/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.RepresentationTheory.Homological.Resolution
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# Literal group-bar tuple modules and standard-basis comparison

Normalized degree n is the free representation on tuples of length n
whose entries are all nonidentity. The homogeneous standard presentation
is identified with the full tuple presentation by the native diagonal
action equivalence, followed by native finitely supported domain transport
and currying. Coefficient and group universes are independent.

The raw tuple inclusion is a degree map. The chain inclusion constructed
by normalization must additionally apply the native Dold–Kan projector.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped Simplicial MonoidAlgebra

universe u v

namespace Rep.NormalizedBar

section Tuples

variable (G : Type v) [One G]

/-- A tuple with no identity entry. -/
def IsNondegenerate {n : ℕ} (g : Fin n → G) : Prop := ∀ i, g i ≠ 1

/-- The literal generator type of normalized degree n. -/
abbrev Tuple (n : ℕ) := {g : Fin n → G // IsNondegenerate G g}

end Tuples

variable (k : Type u) [CommRing k] (G : Type v) [Group G]

/-- The literal normalized degree object, free over the group ring. -/
abbrev degree (n : ℕ) : Rep.{max u v} k G := Rep.free k G (Tuple G n)

/-- The full unnormalized tuple degree object. -/
abbrev fullDegree (n : ℕ) : Rep.{max u v} k G := Rep.free k G (Fin n → G)

/-- The actual simplicial linearization of the native universal cover EG. -/
@[reducible]
def standardSimplicial : SimplicialObject (Rep.{max u v} k G) :=
  classifyingSpaceUniversalCover G ⋙ Rep.linearization k G

/-- Its alternating-face standard complex. -/
abbrev standardComplex : ChainComplex (Rep.{max u v} k G) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj (standardSimplicial k G)

/-- The underlying tuple equivalence of the native diagonal action
isomorphism, with the tuple coordinate first. -/
def tupleEquiv (n : ℕ) : (Fin (n + 1) → G) ≃ (Fin n → G) × G :=
  (((forget (Action (Type v) G)).mapIso
    (Action.diagonalSuccIsoTensorTrivial G n)).toEquiv).trans (Equiv.prodComm _ _)

@[simp]
theorem tupleEquiv_apply (n : ℕ) (a : Fin (n + 1) → G) :
    tupleEquiv G n a = ((fun i => (a i.castSucc)⁻¹ * a i.succ), a 0) := by
  change Prod.swap ((Action.diagonalSuccIsoTensorTrivial G n).hom.hom a) = _
  rw [Action.diagonalSuccIsoTensorTrivial_hom_hom_apply]
  rfl

@[simp]
theorem tupleEquiv_symm_apply (n : ℕ) (g : Fin n → G) (h : G) :
    (tupleEquiv G n).symm (g, h) = h • Fin.partialProd g := by
  change (Action.diagonalSuccIsoTensorTrivial G n).inv.hom (h, g) = _
  exact Action.diagonalSuccIsoTensorTrivial_inv_hom_apply h g

/-- Native finitely supported basis transport followed by currying gives
the full inhomogeneous group-ring tuple module. -/
def basisLinearEquiv (n : ℕ) :
    k[Fin (n + 1) → G] ≃ₗ[k] (Fin n → G) →₀ k[G] :=
  (MonoidAlgebra.coeffLinearEquiv k).trans
    ((Finsupp.domLCongr (R := k) (M := k) (tupleEquiv G n)).trans
      ((Finsupp.curryLinearEquiv k).trans
        (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv k).symm)))

@[simp]
theorem basisLinearEquiv_single (n : ℕ) (a : Fin (n + 1) → G) (r : k) :
    basisLinearEquiv k G n (MonoidAlgebra.single a r) =
      Finsupp.single (fun i => (a i.castSucc)⁻¹ * a i.succ)
        (MonoidAlgebra.single (a 0) r) := by
  simp [basisLinearEquiv, Finsupp.curry_single]

@[simp]
theorem basisLinearEquiv_symm_single_single (n : ℕ) (g : Fin n → G) (h : G) (r : k) :
    (basisLinearEquiv k G n).symm (Finsupp.single g (MonoidAlgebra.single h r)) =
      MonoidAlgebra.single (h • Fin.partialProd g) r := by
  simp [basisLinearEquiv, Finsupp.domLCongr_symm, Finsupp.uncurry_single]

/-- Homogeneous basis symbols in the actual simplicial standard degree. -/
@[reducible]
def standardSymbol (n : ℕ) (a : Fin (n + 1) → G) (r : k) :
    ((standardSimplicial k G).obj (Opposite.op ⦋n⦌)).V :=
  MonoidAlgebra.single a r

theorem standardSymbol_action (n : ℕ) (h : G) (a : Fin (n + 1) → G) (r : k) :
    ((standardSimplicial k G).obj (Opposite.op ⦋n⦌)).ρ h (standardSymbol k G n a r) =
      standardSymbol k G n (h • a) r := by
  change MonoidAlgebra.mapDomainLinearMap k k
      (fun b : Fin (n + 1) → G => h • b) (MonoidAlgebra.single a r) =
    MonoidAlgebra.single (h • a) r
  exact MonoidAlgebra.mapDomainLinearMap_single (R := k) (S := k)
    (fun b : Fin (n + 1) → G => h • b) r a

/-- The actual standard degree is isomorphic to the full tuple degree,
with arbitrary independent coefficient and group universes. -/
def basisIso (n : ℕ) :
    (standardSimplicial k G).obj (Opposite.op ⦋n⦌) ≅ fullDegree k G n :=
  Rep.mkIso (Representation.linearizeOfMulActionIso k G (Fin (n + 1) → G)) ≪≫
    Rep.mkIso
    { __ := basisLinearEquiv k G n
      isIntertwining' := fun h => by
        apply MonoidAlgebra.lhom_ext'
        intro a
        apply LinearMap.ext_ring
        simp [basisLinearEquiv_single,
          Representation.ofMulAction_single,
          Pi.smul_apply, mul_inv_rev, mul_assoc] }

theorem basisIso_hom_single (n : ℕ) (a : Fin (n + 1) → G) (r : k) :
    (basisIso k G n).hom.hom (standardSymbol k G n a r) =
      Finsupp.single (fun i => (a i.castSucc)⁻¹ * a i.succ)
        (MonoidAlgebra.single (a 0) r) :=
  basisLinearEquiv_single k G n a r

theorem basisIso_inv_single_single (n : ℕ) (g : Fin n → G) (h : G) (r : k) :
    (basisIso k G n).inv.hom (Finsupp.single g (MonoidAlgebra.single h r)) =
      standardSymbol k G n (h • Fin.partialProd g) r :=
  basisLinearEquiv_symm_single_single k G n g h r

/-- Projection deletes a tuple exactly when one of its entries is identity. -/
def rawProjection (n : ℕ) : fullDegree k G n ⟶ degree k G n := by
  classical
  exact Rep.freeLift k G _ (fun g =>
    if h : IsNondegenerate G g then Finsupp.single ⟨g, h⟩ 1 else 0)

/-- Raw inclusion of the literal nonidentity tuple generators. -/
def rawInclusion (n : ℕ) : degree k G n ⟶ fullDegree k G n :=
  Rep.freeLift k G _ (fun g => Finsupp.single g.val 1)

open scoped Classical in
@[simp]
theorem rawProjection_single_single (n : ℕ) (g : Fin n → G) (h : G) (r : k) :
    (rawProjection k G n).hom (Finsupp.single g (MonoidAlgebra.single h r)) =
      if hg : IsNondegenerate G g then
        Finsupp.single ⟨g, hg⟩ (MonoidAlgebra.single h r) else 0 := by
  classical
  by_cases hg : IsNondegenerate G g <;>
    simp [rawProjection, Representation.freeLift_single_single, hg,
      Representation.free, Representation.finsupp_single,
      Representation.ofMulAction_single, MonoidAlgebra.one_def]

@[simp]
theorem rawInclusion_single_single (n : ℕ) (g : Tuple G n) (h : G) (r : k) :
    (rawInclusion k G n).hom (Finsupp.single g (MonoidAlgebra.single h r)) =
      Finsupp.single g.val (MonoidAlgebra.single h r) := by
  simp [rawInclusion, Representation.freeLift_single_single,
    Representation.free, Representation.finsupp_single,
    Representation.ofMulAction_single, MonoidAlgebra.one_def]

@[reassoc (attr := simp)]
theorem rawInclusion_comp_rawProjection (n : ℕ) :
    rawInclusion k G n ≫ rawProjection k G n = 𝟙 (degree k G n) := by
  classical
  refine Rep.free_ext k G _ _ _ ?_
  intro g
  let ιn : (Tuple G n →₀ k[G]) →ₗ[k] ((Fin n → G) →₀ k[G]) :=
    (rawInclusion k G n).hom.toLinearMap
  let πn : ((Fin n → G) →₀ k[G]) →ₗ[k] (Tuple G n →₀ k[G]) :=
    (rawProjection k G n).hom.toLinearMap
  let z : Tuple G n →₀ k[G] := Finsupp.single g (MonoidAlgebra.single (1 : G) (1 : k))
  let w : (Fin n → G) →₀ k[G] :=
    Finsupp.single g.val (MonoidAlgebra.single (1 : G) (1 : k))
  have hι : ιn z = w := rawInclusion_single_single k G n g 1 1
  have hπ : πn w = z := by
    have h : πn w =
        if hg : IsNondegenerate G g.val then
          Finsupp.single ⟨g.val, hg⟩ (MonoidAlgebra.single (1 : G) (1 : k)) else 0 :=
      rawProjection_single_single k G n g.val 1 1
    exact h.trans (by rw [dite_eq_left g.property])
  change πn (ιn z) = z
  exact (congrArg (fun q : (Fin n → G) →₀ k[G] => πn q) hι).trans hπ

/-- The actual representation projection is the native restriction of
finitely supported functions to the nonidentity tuple subtype. -/
theorem rawProjection_eq_lsubtypeDomain (n : ℕ) :
    (rawProjection k G n).hom.toLinearMap =
      Finsupp.lsubtypeDomain (R := k) (M := k[G]) {g : Fin n → G | IsNondegenerate G g} := by
  classical
  let πn : ((Fin n → G) →₀ k[G]) →ₗ[k] (Tuple G n →₀ k[G]) :=
    (rawProjection k G n).hom.toLinearMap
  change πn = Finsupp.lsubtypeDomain (R := k) (M := k[G])
    {g : Fin n → G | IsNondegenerate G g}
  apply Finsupp.lhom_ext'
  intro g
  apply MonoidAlgebra.lhom_ext'
  intro h
  apply LinearMap.ext_ring
  apply Finsupp.ext
  intro t
  change πn (Finsupp.single g (MonoidAlgebra.single h (1 : k))) t =
    (Finsupp.single g (MonoidAlgebra.single h (1 : k))) t.val
  have hp : πn (Finsupp.single g (MonoidAlgebra.single h (1 : k))) =
      if hg : IsNondegenerate G g then
        Finsupp.single ⟨g, hg⟩ (MonoidAlgebra.single h (1 : k)) else 0 :=
    rawProjection_single_single k G n g h 1
  by_cases hg : IsNondegenerate G g
  · have hpos : πn (Finsupp.single g (MonoidAlgebra.single h (1 : k))) =
        Finsupp.single ⟨g, hg⟩ (MonoidAlgebra.single h (1 : k)) :=
      hp.trans (dite_eq_left hg)
    have heval := congrArg (fun q : Tuple G n →₀ k[G] => q t) hpos
    exact heval.trans (by simp only [Finsupp.single_apply, Subtype.ext_iff])
  · have htg : t.val ≠ g := by
      intro ht
      apply hg
      simpa only [← ht] using t.property
    have hneg : πn (Finsupp.single g (MonoidAlgebra.single h (1 : k))) = 0 :=
      hp.trans (dite_eq_right hg)
    have heval : πn (Finsupp.single g (MonoidAlgebra.single h (1 : k))) t = 0 :=
      congrArg (fun q : Tuple G n →₀ k[G] => q t) hneg
    exact heval.trans (by
      simp only [Finsupp.single_apply, ite_eq_right (Ne.symm htg)])

@[simp]
theorem rawProjection_apply (n : ℕ) (f : (fullDegree k G n).V) (g : Tuple G n) :
    (rawProjection k G n).hom f g = f g.val := by
  rw [← Representation.IntertwiningMap.toLinearMap_apply, rawProjection_eq_lsubtypeDomain]
  rfl

/-- The actual group-ring submodule spanned by degenerate tuple symbols. -/
def degenerateDegree (n : ℕ) : Submodule k[G] ((Fin n → G) →₀ k[G]) :=
  Finsupp.supported k[G] k[G] {g | ¬ IsNondegenerate G g}

/-- Degenerate degree is exactly the span of tuples containing identity. -/
theorem degenerateDegree_eq_span (n : ℕ) :
    degenerateDegree k G n =
      Submodule.span k[G] ((fun g : Fin n → G => Finsupp.single g (1 : k[G])) ''
        {g | ∃ i, g i = 1}) := by
  classical
  simpa only [degenerateDegree, IsNondegenerate, not_forall, not_not] using
    (Finsupp.supported_eq_span_single (R := k[G]) {g : Fin n → G | ¬ IsNondegenerate G g})

/-- Kernel membership is exactly membership in the literal degeneracy span. -/
theorem rawProjection_eq_zero_iff (n : ℕ) (f : (fullDegree k G n).V) :
    (rawProjection k G n).hom f = 0 ↔ f ∈ degenerateDegree k G n := by
  change (rawProjection k G n).hom.toLinearMap f = 0 ↔ _
  rw [rawProjection_eq_lsubtypeDomain]
  change Finsupp.subtypeDomain (IsNondegenerate G) f = 0 ↔ _
  rw [Finsupp.subtypeDomain_eq_zero_iff']
  simp only [degenerateDegree, Finsupp.mem_supported', Set.mem_ofPred_eq, not_not]

/-- Tuple projection in the actual homogeneous standard presentation. -/
def standardProjection (n : ℕ) :
    (standardSimplicial k G).obj (Opposite.op ⦋n⦌) ⟶ degree k G n :=
  (basisIso k G n).hom ≫ rawProjection k G n

/-- Raw nonidentity generators in the homogeneous standard presentation. -/
def standardRawInclusion (n : ℕ) :
    degree k G n ⟶ (standardSimplicial k G).obj (Opposite.op ⦋n⦌) :=
  rawInclusion k G n ≫ (basisIso k G n).inv

@[reassoc (attr := simp)]
theorem standardRawInclusion_comp_standardProjection (n : ℕ) :
    standardRawInclusion k G n ≫ standardProjection k G n = 𝟙 (degree k G n) := by
  simp [standardRawInclusion, standardProjection, Category.assoc]

end Rep.NormalizedBar

end
