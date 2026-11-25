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

/-- **Piece of a restricted product supported in a finite set.** Let $(X_i)_{i \in \iota}$ be a
family of types with subsets $U_i \subseteq X_i$. For a finite set $S$ of indices, the piece
$X_S$ is the set of tuples $x \in \prod_{i \in \iota} X_i$ such that $x_i \in U_i$ for every
$i \notin S$. -/
def XS (S : Finset ι) : Set ((i : ι) → X i) :=
  {x | ∀ i, i ∉ S → x i ∈ U i}

/-- **The pieces grow with the finite set.** Let $(X_i)_{i \in \iota}$ be a family of types with
subsets $U_i \subseteq X_i$, and for a finite set $S$ of indices let $X_S$ be the set of tuples
$x \in \prod_{i \in \iota} X_i$ with $x_i \in U_i$ for every $i \notin S$. If $S \subseteq T$ are
finite sets of indices, then $X_S \subseteq X_T$. -/
theorem XS_mono {S T : Finset ι} (hST : S ⊆ T) : XS X U S ⊆ XS X U T :=
  fun _ hx i hi => hx i (fun hS => hi (hST hS))

/-- **Every element of the restricted product lies in a piece.** Let $(X_i)_{i \in \iota}$ be
sets with subsets $U_i \subseteq X_i$, and let $x$ be an element of the restricted product of
the $X_i$ with respect to the $U_i$, that is, a tuple $x \in \prod_i X_i$ with $x_i \in U_i$ for
all but finitely many $i$. Then there is a finite set $S \subseteq \iota$ such that
$x_i \in U_i$ for all $i \notin S$, that is, $x$ lies in the piece $X_S$. -/
theorem mem_XS_of_restricted (x : Πʳ i, [X i, U i]) :
    ∃ S : Finset ι, (x : (i : ι) → X i) ∈ XS X U S := by
  have hfin := eventually_cofinite.mp x.2
  exact ⟨hfin.toFinset, fun i hi => by
    simp only [Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hi; exact hi⟩

/-- **Support of an element of a restricted product.** Let $(X_i)_{i \in \iota}$ be sets with
subsets $U_i \subseteq X_i$. The support of an element $x$ of the restricted product of the $X_i$
with respect to the $U_i$ (a tuple with $x_i \in U_i$ for all but finitely many $i$) is the
finite set of indices $i$ with $x_i \notin U_i$. -/
noncomputable def supportFinset (x : Πʳ i, [X i, U i]) : Finset ι :=
  (eventually_cofinite.mp x.2).toFinset

/-- **An element lies in the piece indexed by its support.** Let $(X_i)_{i \in \iota}$ be sets
with subsets $U_i \subseteq X_i$, let $x$ be an element of the restricted product of the $X_i$
with respect to the $U_i$ (a tuple with $x_i \in U_i$ for all but finitely many $i$), and let
$\operatorname{supp}(x)$ be the finite set of indices $i$ with $x_i \notin U_i$. Then
$x_i \in U_i$ for every $i \notin \operatorname{supp}(x)$, that is, $x$ lies in the piece
$X_{\operatorname{supp}(x)}$. -/
theorem mem_XS_support (x : Πʳ i, [X i, U i]) :
    (x : (i : ι) → X i) ∈ XS X U (supportFinset X U x) := by
  intro i hi
  simp only [supportFinset, Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hi; exact hi

/-- **Tuples in a piece are eventually in the $U_i$.** Let $(X_i)_{i \in \iota}$ be a family of
types with subsets $U_i \subseteq X_i$, and let $S$ be a finite set of indices. If a tuple
$x \in \prod_{i \in \iota} X_i$ lies in the piece $X_S$, that is, $x_i \in U_i$ for every
$i \notin S$, then $x_i \in U_i$ for all but finitely many indices $i$.

In other words, $x$ defines an element of the restricted product of the $X_i$ with respect to
the $U_i$. -/
theorem XS_mem_restricted {S : Finset ι} {x : (i : ι) → X i}
    (hx : x ∈ XS X U S) : ∀ᶠ i in cofinite, x i ∈ U i := by
  rw [eventually_cofinite]
  exact S.finite_toSet.subset (fun i hi => by
    simp only [Set.mem_ofPred_eq] at hi
    by_contra h; exact hi (hx i (by simpa using h)))

/-- **The support lies in the index set of every piece containing the element.** Let
$(X_i)_{i \in \iota}$ be sets with subsets $U_i \subseteq X_i$, and let $x$ be an element of the
restricted product of the $X_i$ with respect to the $U_i$ (a tuple with $x_i \in U_i$ for all but
finitely many $i$), with support $\operatorname{supp}(x) = \{i : x_i \notin U_i\}$. If
$T \subseteq \iota$ is a finite set with $x_i \in U_i$ for all $i \notin T$, then
$\operatorname{supp}(x) \subseteq T$. -/
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

/-- **Inclusion of pieces.** Let $(X_i)_{i \in \iota}$ be topological spaces with subsets
$U_i \subseteq X_i$, and for a finite set $S \subseteq \iota$ let $X_S$ be the set of tuples
$x \in \prod_i X_i$ with $x_i \in U_i$ for all $i \notin S$. For finite sets $S \subseteq T$, the
inclusion of pieces is the map $X_S \to X_T$ sending each tuple $x$ to itself. -/
def inclusionMap {S T : Finset ι} (h : S ⊆ T) :
    XS X U S → XS X U T :=
  fun ⟨x, hx⟩ => ⟨x, XS_mono X U h hx⟩

/-- **Continuity of the inclusion of pieces.** Let $(X_i)_{i \in \iota}$ be topological spaces with
subsets $U_i \subseteq X_i$, and for a finite set $S \subseteq \iota$ let $X_S$ be the set of
tuples $x \in \prod_i X_i$ with $x_i \in U_i$ for all $i \notin S$, with the subspace topology of
the product topology. For finite sets $S \subseteq T \subseteq \iota$, the inclusion map
$X_S \to X_T$ is continuous. -/
theorem continuous_inclusionMap {S T : Finset ι} (h : S ⊆ T) :
    Continuous (inclusionMap X U h) :=
  continuous_subtype_val.subtype_mk _

/-- **Transition maps of the pieces.** Let $(X_i)_{i \in \iota}$ be topological spaces with
subsets $U_i \subseteq X_i$, and for a finite set $S \subseteq \iota$ let $X_S$ be the set of
tuples $x \in \prod_i X_i$ with $x_i \in U_i$ for all $i \notin S$. For finite sets
$S \subseteq T$, the transition map $X_S \to X_T$ of the direct system of pieces sends each tuple
$x$ to itself. -/
def transitionMaps :
    ∀ (S T : Finset ι), S ≤ T → XS X U S → XS X U T :=
  fun _ _ h => inclusionMap X U h

/-- The pieces form a directed system under inclusion: the transition maps
satisfy the identity and composition laws definitionally. -/
instance : DirectedSystem (fun S : Finset ι => ↥(XS X U S))
    (fun ⦃S T⦄ (h : S ≤ T) => transitionMaps X U S T h) where
  map_self := fun ⦃_S⦄ _x => rfl
  map_map := fun ⦃_k _j _i⦄ _ _ _x => rfl

/-- **Continuity of the transition maps of the pieces.** Let $(X_i)_{i \in \iota}$ be topological
spaces with subsets $U_i \subseteq X_i$, and for a finite set $S \subseteq \iota$ let $X_S$ be the
set of tuples $x \in \prod_i X_i$ with $x_i \in U_i$ for all $i \notin S$, with the subspace
topology of the product topology. For all finite sets $S \subseteq T \subseteq \iota$, the
transition map $X_S \to X_T$ of the direct system of the pieces, which is the inclusion, is
continuous. -/
theorem continuous_transitionMaps (S T : Finset ι) (h : S ≤ T) :
    Continuous (transitionMaps X U S T h) :=
  continuous_inclusionMap X U h

/-- **Direct limit of the finite-support pieces.** Let $(X_i)_{i \in \iota}$ be topological spaces
with subsets $U_i \subseteq X_i$, and for a finite set $S \subseteq \iota$ let $X_S$ be the set of
tuples $x \in \prod_i X_i$ with $x_i \in U_i$ for all $i \notin S$, with the subspace topology of
the product topology. The space $\varinjlim_S X_S$ is the direct limit of the $X_S$ over the
finite subsets $S$ of $\iota$ ordered by inclusion, with the inclusions $X_S \to X_T$ for
$S \subseteq T$ as transition maps: the quotient of the disjoint union of the $X_S$ by the
equivalence relation generated by identifying each $x \in X_S$ with its image in $X_T$, with the
quotient topology. -/
abbrev DirectLimitXS :=
  TopologicalSpace.DirectLimit.Space
    (fun S : Finset ι => XS X U S)
    (transitionMaps X U)
    (continuous_transitionMaps X U)

/-- **The cofinite filter lies below the principal filter of the complement of a finite set.**
For every finite set $S$ of indices in $\iota$, the cofinite filter on $\iota$ is less than or
equal to the principal filter of the complement $\iota \setminus S$; that is, $\iota \setminus S$
belongs to the cofinite filter. -/
theorem cofinite_le_principal_compl (S : Finset ι) :
    cofinite ≤ principal ((↑S : Set ι)ᶜ) := by
  rw [le_principal_iff, mem_cofinite, compl_compl]
  exact S.finite_toSet

end DirectLimitConstruction

section PrincipalPieces

variable {ι : Type*}
  (X : ι → Type*) (U : (i : ι) → Set (X i))

/-- **Tuples restricted on a cofinite set lie in a piece.** Let $(X_i)_{i \in \iota}$ be sets
with subsets $U_i \subseteq X_i$, and for a finite set $F \subseteq \iota$ let $X_F$ be the set
of tuples $x \in \prod_i X_i$ with $x_i \in U_i$ for all $i \notin F$. Let $S \subseteq \iota$
have finite complement. Then every tuple $y \in \prod_i X_i$ with $y_i \in U_i$ for all
$i \in S$ lies in $X_{\iota \setminus S}$. -/
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

/-- **Forward map to the direct limit of the pieces.** Let $(X_i)_{i \in \iota}$ be topological
spaces with subsets $U_i \subseteq X_i$, and let $L$ be the direct limit, over finite sets
$S \subseteq \iota$, of the pieces $X_S$ of tuples with $x_i \in U_i$ for all $i \notin S$. The
forward map sends an element $x$ of the restricted product of the $X_i$ with respect to the
$U_i$ (a tuple with $x_i \in U_i$ for all but finitely many $i$) to the class in $L$ of $x$,
viewed in the piece $X_{\operatorname{supp}(x)}$ indexed by its support
$\operatorname{supp}(x) = \{i : x_i \notin U_i\}$. -/
noncomputable def toDirectLimit (x : Πʳ i, [X i, U i]) : DirectLimitXS X U :=
  TopologicalSpace.DirectLimit.of (fun S : Finset ι => XS X U S)
    (transitionMaps X U) (continuous_transitionMaps X U)
    (supportFinset X U x)
    ⟨(x : (i : ι) → X i), mem_XS_support X U x⟩

/-- **The map from the direct limit of the pieces to the restricted product.** Let
$(X_i)_{i \in \iota}$ be topological spaces with subsets $U_i \subseteq X_i$, and for a finite set
$S \subseteq \iota$ let $X_S$ be the set of tuples $x \in \prod_i X_i$ with $x_i \in U_i$ for all
$i \notin S$, with the subspace topology of the product topology. The backward map sends the class
in the direct limit $\varinjlim_S X_S$ (over the finite subsets of $\iota$) of a tuple
$x \in X_S$ to $x$, regarded as an element of the restricted product $\prod'_i (X_i, U_i)$ with
respect to the cofinite filter; the result does not depend on the representative. -/
noncomputable def fromDirectLimit : DirectLimitXS X U → Πʳ i, [X i, U i] :=
  TopologicalSpace.DirectLimit.lift (fun S : Finset ι => XS X U S)
    (transitionMaps X U) (continuous_transitionMaps X U)
    (fun S (x : ↥(XS X U S)) => ⟨x.val, XS_mem_restricted X U x.prop⟩)
    (fun _S _T _h _x => rfl)

/-- **The backward map undoes the forward map.** Let $(X_i)_{i \in \iota}$ be topological spaces
with subsets $U_i \subseteq X_i$, and for a finite set $S \subseteq \iota$ let $X_S$ be the set of
tuples $x \in \prod_i X_i$ with $x_i \in U_i$ for all $i \notin S$. For every $x$ in the
restricted product $\prod'_i (X_i, U_i)$ with respect to the cofinite filter, let $S(x)$ be the
finite set of indices $i$ with $x_i \notin U_i$. Sending $x$ to its class in $X_{S(x)}$ in the
direct limit $\varinjlim_S X_S$, and then sending that class to the tuple carried by its
representative, returns $x$.

This holds definitionally: unfolding both maps, the quotient lift applied to the canonical
representative returns the representative itself. -/
theorem fromDirectLimit_toDirectLimit (x : Πʳ i, [X i, U i]) :
    fromDirectLimit X U (toDirectLimit X U x) = x := rfl

/-- **The forward map undoes the backward map.** Let $(X_i)_{i \in \iota}$ be topological spaces
with subsets $U_i \subseteq X_i$, let $P$ be their restricted product (the tuples with
$x_i \in U_i$ for all but finitely many $i$), and let $L$ be the direct limit, over finite sets
$S \subseteq \iota$, of the pieces $X_S$ of tuples with $x_i \in U_i$ for all $i \notin S$. Let
$f : P \to L$ be the forward map, sending $x$ to its class in the piece indexed by its support
$\{i : x_i \notin U_i\}$, and let $g : L \to P$ be the backward map, sending a class to the tuple
carried by any of its representatives. Then $f(g(q)) = q$ for every $q \in L$. -/
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

/-- **Chunk map of a piece.** Let $(X_i)_{i \in \iota}$ be topological spaces with subsets
$U_i \subseteq X_i$, let $S \subseteq \iota$ be finite, and let $X_S$ be the set of tuples
$x \in \prod_i X_i$ with $x_i \in U_i$ for all $i \notin S$. The chunk map sends each $x \in X_S$
to the same tuple $x$, viewed as an element of the restricted product of the $X_i$ with respect
to the $U_i$ and the principal filter of $\iota \setminus S$; this restricted product consists
of the tuples whose $i$-th entry lies in $U_i$ for every $i \notin S$. -/
def toChunk (S : Finset ι) (x : ↥(XS X U S)) :
    Πʳ i, [X i, U i]_[Filter.principal ((↑S : Set ι)ᶜ)] :=
  RestrictedProduct.mk x.val (by
    rw [Filter.eventually_principal]
    intro i hi
    exact x.prop i (by simpa using hi))

/-- **Continuity of the chunk map.** Let $(X_i)_{i \in \iota}$ be topological spaces with subsets
$U_i \subseteq X_i$, let $S \subseteq \iota$ be finite, and let $X_S$ be the set of tuples
$x \in \prod_i X_i$ with $x_i \in U_i$ for all $i \notin S$, with the subspace topology of the
product topology. The map that sends $x \in X_S$ to $x$, viewed in the restricted product of the
$(X_i, U_i)$ with respect to the principal filter of $\iota \setminus S$ with its restricted
product topology, is continuous. -/
theorem continuous_toChunk (S : Finset ι) : Continuous (toChunk X U S) := by
  rw [RestrictedProduct.topologicalSpace_eq_of_principal]
  exact continuous_induced_rng.mpr continuous_subtype_val

/-- **Continuity of the map from the direct limit of the pieces.** Let $(X_i)_{i \in \iota}$ be
topological spaces with subsets $U_i \subseteq X_i$, and for a finite set $S \subseteq \iota$ let
$X_S$ be the set of tuples $x \in \prod_i X_i$ with $x_i \in U_i$ for all $i \notin S$, with the
subspace topology of the product topology. The map from the direct limit $\varinjlim_S X_S$ over
the finite subsets of $\iota$ to the restricted product $\prod'_i (X_i, U_i)$ (with respect to the
cofinite filter, with its restricted product topology) that sends the class of $x \in X_S$ to $x$
is continuous.

This follows from the universal property of the direct limit. -/
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

/-- **Continuity of the map to the direct limit of the pieces.** Let $(X_i)_{i \in \iota}$ be
topological spaces with subsets $U_i \subseteq X_i$, and for a finite set $S \subseteq \iota$ let
$X_S$ be the set of tuples $x \in \prod_i X_i$ with $x_i \in U_i$ for all $i \notin S$, with the
subspace topology of the product topology. The map from the restricted product
$\prod'_i (X_i, U_i)$ (with respect to the cofinite filter, with its restricted product topology)
to the direct limit $\varinjlim_S X_S$ over the finite subsets of $\iota$ that sends $x$ to its
class in $X_{S(x)}$, where $S(x)$ is the finite set of indices $i$ with $x_i \notin U_i$, is
continuous.

This follows from the universal property of the restricted product topology. -/
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

/-- **The restricted product is the direct limit of its finite-support pieces.** Let
$(X_i)_{i \in \iota}$ be topological spaces with subsets $U_i \subseteq X_i$, and for a finite set
$S \subseteq \iota$ let $X_S$ be the set of tuples $x \in \prod_i X_i$ with $x_i \in U_i$ for all
$i \notin S$, with the subspace topology of the product topology. Let $\prod'_i (X_i, U_i)$ be
the restricted product with respect to the cofinite filter, with its restricted product
topology, and for $x$ in it let $S(x)$ be the finite set of indices $i$ with $x_i \notin U_i$.
The map sending $x$ to its class in $X_{S(x)}$ is a homeomorphism from $\prod'_i (X_i, U_i)$ to
the direct limit $\varinjlim_S X_S$ over the finite subsets of $\iota$ ordered by inclusion; its
inverse sends the class of $x \in X_S$ to $x$.

Source: ATLAS NumberTheoryI, Proposition 25.5. -/
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
