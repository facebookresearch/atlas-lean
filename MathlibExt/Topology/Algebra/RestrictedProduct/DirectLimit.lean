/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.DirectLimit
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

@[expose] public section

/-!
# Restricted products as direct limits

This module formalizes ATLAS NumberTheoryI, Proposition 25.5: the
restricted product `∏ (Xᵢ, Uᵢ)` (with the cofinite filter) is the direct
limit of the pieces `X_S` of tuples supported in a finite set `S`,
i.e. the tuples `x` with `x i ∈ U i` for all `i ∉ S`. The direct limit is
the quotient-of-disjoint-union construction in
`MathlibExt/Topology/DirectLimit.lean`.

The topology on the pieces is the subspace topology from the full product;
the topology on the restricted product is Mathlib's
`RestrictedProduct.topologicalSpace`. The maps back and forth are the
obvious ones: a restricted-product element maps to its class in the piece
indexed by its (finite) support, and a class represented in a piece maps to
the restricted-product element carried by that representative.

## Main definitions

* `RestrictedProduct.XS`: the piece of tuples supported in a finite set `S`.
* `RestrictedProduct.DirectLimitXS`: the direct limit of the pieces.
* `RestrictedProduct.toDirectLimit`: the forward map to the direct limit.
* `RestrictedProduct.fromDirectLimit`: the backward map from the direct limit.

## Main results

* `RestrictedProduct.homeomorph_directLimit`: Proposition 25.5 — the
  restricted product is homeomorphic to the direct limit of the pieces.

## References

* ATLAS NumberTheoryI, Proposition 25.5.
-/

open scoped RestrictedProduct
open Filter Set

namespace RestrictedProduct

section XSDefinitions

variable {ι : Type*}
  (X : ι → Type*) (U : (i : ι) → Set (X i))

/-- The piece of the restricted product supported in the finite set `S`:
the tuples `x` with `x i ∈ U i` for all `i ∉ S`. -/
def XS (S : Finset ι) : Set ((i : ι) → X i) :=
  {x | ∀ i, i ∉ S → x i ∈ U i}

/-- The pieces grow with the finite set. -/
theorem XS_mono {S T : Finset ι} (hST : S ⊆ T) : XS X U S ⊆ XS X U T :=
  fun _ hx i hi => hx i (fun hS => hi (hST hS))

/-- Every element of the restricted product is supported in some finite
set. -/
theorem mem_XS_of_restricted (x : Πʳ i, [X i, U i]) :
    ∃ S : Finset ι, (x : (i : ι) → X i) ∈ XS X U S := by
  have hfin := eventually_cofinite.mp x.2
  exact ⟨hfin.toFinset, fun i hi => by
    simp only [Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hi; exact hi⟩

/-- The finite support of an element of the restricted product: the finite
set of indices where it lies outside `U`. -/
noncomputable def supportFinset (x : Πʳ i, [X i, U i]) : Finset ι :=
  (eventually_cofinite.mp x.2).toFinset

/-- Every element of the restricted product lies in the piece indexed by
its own support. -/
theorem mem_XS_support (x : Πʳ i, [X i, U i]) :
    (x : (i : ι) → X i) ∈ XS X U (supportFinset X U x) := by
  intro i hi
  simp only [supportFinset, Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hi; exact hi

/-- A tuple in a piece is eventually in `U`, hence defines an element of
the restricted product. -/
theorem XS_mem_restricted {S : Finset ι} {x : (i : ι) → X i}
    (hx : x ∈ XS X U S) : ∀ᶠ i in cofinite, x i ∈ U i := by
  rw [eventually_cofinite]
  exact S.finite_toSet.subset (fun i hi => by
    simp only [Set.mem_ofPred_eq] at hi
    by_contra h; exact hi (hx i (by simpa using h)))

/-- The support of an element of a piece is contained in the piece's
indexing set. -/
theorem supportFinset_le {T : Finset ι} {x : Πʳ i, [X i, U i]}
    (hx : (x : (i : ι) → X i) ∈ XS X U T) :
    supportFinset X U x ⊆ T := by
  intro i hi
  simp only [supportFinset, Finite.mem_toFinset, Set.mem_ofPred_eq] at hi
  by_contra hiT
  exact hi (hx i hiT)

end XSDefinitions

section DirectLimitConstruction

variable {ι : Type*}
  (X : ι → Type*) [∀ i, TopologicalSpace (X i)]
  (U : (i : ι) → Set (X i))

/-- The inclusion of pieces, as a map between the subtype types. -/
def inclusionMap {S T : Finset ι} (h : S ⊆ T) :
    XS X U S → XS X U T :=
  fun ⟨x, hx⟩ => ⟨x, XS_mono X U h hx⟩

/-- The inclusion of pieces is continuous. -/
theorem continuous_inclusionMap {S T : Finset ι} (h : S ⊆ T) :
    Continuous (inclusionMap X U h) :=
  continuous_subtype_val.subtype_mk _

/-- The transition maps of the direct system of pieces. -/
def transitionMaps :
    ∀ (S T : Finset ι), S ≤ T → XS X U S → XS X U T :=
  fun _ _ h => inclusionMap X U h

/-- The pieces form a directed system under inclusion: the transition maps
satisfy the identity and composition laws definitionally. -/
instance : DirectedSystem (fun S : Finset ι => ↥(XS X U S))
    (fun ⦃S T⦄ (h : S ≤ T) => transitionMaps X U S T h) where
  map_self := fun ⦃_S⦄ _x => rfl
  map_map := fun ⦃_k _j _i⦄ _ _ _x => rfl

/-- The transition maps of the direct system of pieces are continuous. -/
theorem continuous_transitionMaps (S T : Finset ι) (h : S ≤ T) :
    Continuous (transitionMaps X U S T h) :=
  continuous_inclusionMap X U h

/-- The direct limit of the pieces `XS X U S`, indexed by finite sets. -/
abbrev DirectLimitXS :=
  TopologicalSpace.DirectLimit.Space
    (fun S : Finset ι => XS X U S)
    (transitionMaps X U)
    (continuous_transitionMaps X U)

/-- The cofinite filter is below the principal filter on the complement
of any finite set. -/
theorem cofinite_le_principal_compl (S : Finset ι) :
    cofinite ≤ principal ((↑S : Set ι)ᶜ) := by
  rw [le_principal_iff, mem_cofinite, compl_compl]
  exact S.finite_toSet

end DirectLimitConstruction

section PrincipalPieces

variable {ι : Type*}
  (X : ι → Type*) (U : (i : ι) → Set (X i))

/-- The representative of a restricted product with the principal filter
on `S` lies in the piece indexed by the finite set consisting of the
indices outside `S`. -/
theorem inclusion_mem_XS_of_principal {S : Set ι}
    (hS : Filter.cofinite ≤ Filter.principal S)
    (y : Πʳ i, [X i, U i]_[Filter.principal S]) :
    (RestrictedProduct.inclusion X U hS y : (i : ι) → X i) ∈
      XS X U (Set.Finite.toFinset
        (Filter.eventually_cofinite.mp
          (hS (Filter.mem_principal.mpr (Set.Subset.refl S))))) := by
  intro i hi
  have hy := y.2
  rw [Filter.eventually_principal] at hy
  apply hy
  by_contra h
  exact hi ((Set.Finite.mem_toFinset _).mpr h)

end PrincipalPieces

section Homeomorphism

variable {ι : Type*}
  (X : ι → Type*) [∀ i, TopologicalSpace (X i)]
  (U : (i : ι) → Set (X i))

/-- The forward map from the restricted product to the direct limit of
the pieces: send an element to its class in the piece indexed by its
support. -/
noncomputable def toDirectLimit (x : Πʳ i, [X i, U i]) : DirectLimitXS X U :=
  TopologicalSpace.DirectLimit.of (fun S : Finset ι => XS X U S)
    (transitionMaps X U) (continuous_transitionMaps X U)
    (supportFinset X U x)
    ⟨(x : (i : ι) → X i), mem_XS_support X U x⟩

/-- The backward map from the direct limit of the pieces to the
restricted product: send a class to the restricted-product element
carried by any representative. -/
noncomputable def fromDirectLimit : DirectLimitXS X U → Πʳ i, [X i, U i] :=
  TopologicalSpace.DirectLimit.lift (fun S : Finset ι => XS X U S)
    (transitionMaps X U) (continuous_transitionMaps X U)
    (fun S (x : ↥(XS X U S)) => ⟨x.val, XS_mem_restricted X U x.prop⟩)
    (fun _S _T _h _x => rfl)

/-- The two maps are inverse; this direction is definitional: unfolding
both maps, the quotient lift applied to a canonical representative
returns the representative itself. -/
theorem fromDirectLimit_toDirectLimit (x : Πʳ i, [X i, U i]) :
    fromDirectLimit X U (toDirectLimit X U x) = x := rfl

/-- The two maps are inverse in the other direction. -/
theorem toDirectLimit_fromDirectLimit (q : DirectLimitXS X U) :
    toDirectLimit X U (fromDirectLimit X U q) = q := by
  obtain ⟨⟨S, x⟩, rfl⟩ :=
    @Quotient.exists_rep _ (TopologicalSpace.DirectLimit.directLimitSetoid _ _) q
  change toDirectLimit X U
      (fromDirectLimit X U (TopologicalSpace.DirectLimit.of _ _ _ S x)) =
    TopologicalSpace.DirectLimit.of _ _ _ S x
  have key : fromDirectLimit X U (TopologicalSpace.DirectLimit.of _ _ _ S x) =
      ⟨x.val, XS_mem_restricted X U x.prop⟩ := rfl
  rw [key]
  unfold toDirectLimit
  have h_le : supportFinset X U ⟨x.val, XS_mem_restricted X U x.prop⟩ ≤ S :=
    supportFinset_le X U x.prop
  exact (TopologicalSpace.DirectLimit.of_comp (fun S : Finset ι => ↥(XS X U S))
    (transitionMaps X U) (continuous_transitionMaps X U) h_le _).symm

/-- The chunk map from a piece into the restricted product with the
principal filter on the complement of `S`. -/
def toChunk (S : Finset ι) (x : ↥(XS X U S)) :
    Πʳ i, [X i, U i]_[Filter.principal ((↑S : Set ι)ᶜ)] :=
  RestrictedProduct.mk x.val (by
    rw [Filter.eventually_principal]
    intro i hi
    exact x.prop i (by simpa using hi))

/-- The chunk map is continuous. -/
theorem continuous_toChunk (S : Finset ι) : Continuous (toChunk X U S) := by
  rw [RestrictedProduct.topologicalSpace_eq_of_principal]
  exact continuous_induced_rng.mpr continuous_subtype_val

/-- The backward map from the direct limit is continuous, by the
universal property of the direct limit. -/
theorem continuous_fromDirectLimit : Continuous (fromDirectLimit X U) := by
  apply TopologicalSpace.DirectLimit.lift_continuous
  intro S
  have h_filter : Filter.cofinite ≤ Filter.principal ((↑S : Set ι)ᶜ) :=
    cofinite_le_principal_compl S
  rw [show (fun x : ↥(XS X U S) =>
        (⟨(x : (i : ι) → X i), XS_mem_restricted X U x.prop⟩ :
          Πʳ i, [X i, U i])) =
      RestrictedProduct.inclusion X U h_filter ∘ toChunk X U S from by
    ext x i; rfl]
  exact (RestrictedProduct.continuous_inclusion h_filter).comp (continuous_toChunk X U S)

/-- The forward map to the direct limit is continuous, by the universal
property of the restricted product topology (`RestrictedProduct.continuous_dom`). -/
theorem continuous_toDirectLimit : Continuous (toDirectLimit X U) := by
  rw [RestrictedProduct.continuous_dom]
  intro S hS
  have hSc_fin : Set.Finite Sᶜ := by
    rw [← Filter.mem_cofinite]
    exact hS (Filter.mem_principal.mpr (Set.Subset.refl S))
  set T : Finset ι := hSc_fin.toFinset with hT_def
  have key : ∀ y : Πʳ i, [X i, U i]_[Filter.principal S],
      toDirectLimit X U (RestrictedProduct.inclusion X U hS y) =
        TopologicalSpace.DirectLimit.of (fun S : Finset ι => ↥(XS X U S))
          (transitionMaps X U) (continuous_transitionMaps X U) T
          ⟨(RestrictedProduct.inclusion X U hS y : (i : ι) → X i),
           inclusion_mem_XS_of_principal X U hS y⟩ := by
    intro y
    unfold toDirectLimit
    have h_le : supportFinset X U (RestrictedProduct.inclusion X U hS y) ≤ T :=
      supportFinset_le X U (inclusion_mem_XS_of_principal X U hS y)
    exact (TopologicalSpace.DirectLimit.of_comp (fun S : Finset ι => ↥(XS X U S))
      (transitionMaps X U) (continuous_transitionMaps X U) h_le _).symm
  have heq : toDirectLimit X U ∘ RestrictedProduct.inclusion X U hS =
      (fun y => TopologicalSpace.DirectLimit.of (fun S : Finset ι => ↥(XS X U S))
        (transitionMaps X U) (continuous_transitionMaps X U) T
        ⟨(RestrictedProduct.inclusion X U hS y : (i : ι) → X i),
         inclusion_mem_XS_of_principal X U hS y⟩) := by
    ext y; exact key y
  rw [heq]
  apply (TopologicalSpace.DirectLimit.of_continuous _ _ _ T).comp
  apply continuous_induced_rng.mpr
  rw [RestrictedProduct.topologicalSpace_eq_of_principal]
  exact continuous_subtype_val

/-- Proposition 25.5: the restricted product is homeomorphic to the
direct limit of its finite-support pieces. -/
noncomputable def homeomorph_directLimit :
    (Πʳ i, [X i, U i]) ≃ₜ DirectLimitXS X U where
  toFun := toDirectLimit X U
  invFun := fromDirectLimit X U
  left_inv := fromDirectLimit_toDirectLimit X U
  right_inv := toDirectLimit_fromDirectLimit X U
  continuous_toFun := continuous_toDirectLimit X U
  continuous_invFun := continuous_fromDirectLimit X U

end Homeomorphism

end RestrictedProduct
