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
# Free group-bar tuples and homogeneous coordinates

Let k be a commutative ring in universe u and G a group in universe v.
The full degree n representation is free over k[G] on G^n;
the normalized degree is free on tuples with every entry different from 1.
Their carriers have universe max(u,v).

Homogeneous vertices a₀,…,a_n correspond to
(g_i=a_i⁻¹a_(i+1), h=a₀). The inverse vertices are h times the
ordered prefix products of g. This identifies the simplicial linearization
of EG with full inhomogeneous tuple degrees.

The degree projection kills exactly identity-containing tuples;
its raw degree section includes the nonidentity tuples.
The projection kernel is their degeneracy span over k[G].
A chain section is obtained later by correcting the raw section with
the Dold–Kan normalization projector.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped Simplicial MonoidAlgebra

universe u v

namespace Rep.NormalizedBar

section Tuples

variable (G : Type v) [One G]

/-- For a type G with a distinguished element 1, a tuple g:G^n is
nondegenerate when g_i≠1 for every coordinate i.
The empty tuple is included. -/
def IsNondegenerate {n : ℕ} (g : Fin n → G) : Prop := ∀ i, g i ≠ 1

/-- For a type G with distinguished element 1, N_n is the subtype
of length n tuples whose every entry differs from 1. -/
abbrev Tuple (n : ℕ) := {g : Fin n → G // IsNondegenerate G g}

end Tuples

variable (k : Type u) [CommRing k] (G : Type v) [Group G]

/-- Let k be a commutative ring in universe u and G a group in
universe v. Write N_n for tuples G^n with no identity entry,
B_n=⊕_(g∈G^n)k[G] for the full free representation, and
Q_n=⊕_(g∈N_n)k[G] for the normalized degree, with finite support.
The normalized degree Q_n is the free k-linear G-representation
on N_n, with the regular G-action on its k[G] coefficients. -/
abbrev degree (n : ℕ) : Rep.{max u v} k G := Rep.free k G (Tuple G n)

/-- Let k be a commutative ring in universe u and G a group in
universe v. Write N_n for tuples G^n with no identity entry,
B_n=⊕_(g∈G^n)k[G] for the full free representation, and
Q_n=⊕_(g∈N_n)k[G] for the normalized degree, with finite support.
The full degree B_n is the free k-linear G-representation on
all ordered tuples G^n. -/
abbrev fullDegree (n : ℕ) : Rep.{max u v} k G := Rep.free k G (Fin n → G)

/-- Let k be a commutative ring in universe u and G a group in
universe v. Write N_n for tuples G^n with no identity entry,
B_n=⊕_(g∈G^n)k[G] for the full free representation, and
Q_n=⊕_(g∈N_n)k[G] for the normalized degree, with finite support.
Linearizing the diagonal G-action on the universal cover EG
gives the simplicial standard representation.
In degree n its basis is the homogeneous vertex set G^(n+1). -/
@[reducible]
def standardSimplicial : SimplicialObject (Rep.{max u v} k G) :=
  classifyingSpaceUniversalCover G ⋙ Rep.linearization k G

/-- Let k be a commutative ring in universe u and G a group in
universe v. Write N_n for tuples G^n with no identity entry,
B_n=⊕_(g∈G^n)k[G] for the full free representation, and
Q_n=⊕_(g∈N_n)k[G] for the normalized degree, with finite support.
The alternating-face complex of the standard simplicial
representation has boundary ∑_i(-1)^i times vertex deletion. -/
abbrev standardComplex : ChainComplex (Rep.{max u v} k G) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj (standardSimplicial k G)

/-- For a group G, the vertex-to-tuple equivalence sends
(a₀,…,a_n) to ((a_i⁻¹a_(i+1))_i,a₀).
Its inverse sends (g,h) to h times the ordered prefix-product
vertices (1,g₀,g₀g₁,…). -/
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

/-- Let k be a commutative ring in universe u and G a group in
universe v. Write N_n for tuples G^n with no identity entry,
B_n=⊕_(g∈G^n)k[G] for the full free representation, and
Q_n=⊕_(g∈N_n)k[G] for the normalized degree, with finite support.
The k-linear basis equivalence takes a homogeneous symbol
r[a₀,…,a_n] to the tuple symbol indexed by
(a_i⁻¹a_(i+1))_i with group-ring coefficient r[a₀]. -/
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

/-- Let k be a commutative ring in universe u and G a group in
universe v. Write N_n for tuples G^n with no identity entry,
B_n=⊕_(g∈G^n)k[G] for the full free representation, and
Q_n=⊕_(g∈N_n)k[G] for the normalized degree, with finite support.
The standard symbol r[a] is the basis vector at homogeneous
vertices a∈G^(n+1) in the simplicial standard representation. -/
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

/-- Let k be a commutative ring in universe u and G a group in
universe v. Write N_n for tuples G^n with no identity entry,
B_n=⊕_(g∈G^n)k[G] for the full free representation, and
Q_n=⊕_(g∈N_n)k[G] for the normalized degree, with finite support.
The equivariant basis isomorphism from standard degree n to B_n
uses the consecutive-quotient tuple and initial coefficient a₀.
Its inverse has vertices h times the prefix products of g. -/
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

/-- Let k be a commutative ring in universe u and G a group in
universe v. Write N_n for tuples G^n with no identity entry,
B_n=⊕_(g∈G^n)k[G] for the full free representation, and
Q_n=⊕_(g∈N_n)k[G] for the normalized degree, with finite support.
The degree projection B_n→Q_n retains coefficients at tuples
with no identity entries and kills coefficients at all other tuples. -/
def rawProjection (n : ℕ) : fullDegree k G n ⟶ degree k G n := by
  classical
  exact Rep.freeLift k G _ (fun g =>
    if h : IsNondegenerate G g then Finsupp.single ⟨g, h⟩ 1 else 0)

/-- Let k be a commutative ring in universe u and G a group in
universe v. Write N_n for tuples G^n with no identity entry,
B_n=⊕_(g∈G^n)k[G] for the full free representation, and
Q_n=⊕_(g∈N_n)k[G] for the normalized degree, with finite support.
The raw degree inclusion Q_n→B_n extends a nonidentity tuple
symbol to the same full tuple symbol, with zero coefficients elsewhere. -/
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

/-- Let k be a commutative ring in universe u and G a group in
universe v. Write N_n for tuples G^n with no identity entry,
B_n=⊕_(g∈G^n)k[G] for the full free representation, and
Q_n=⊕_(g∈N_n)k[G] for the normalized degree, with finite support.
The underlying linear projection B_n→Q_n is restriction of
a finitely supported coefficient function to the subset N_n. -/
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

/-- Let k be a commutative ring in universe u and G a group in
universe v. Write N_n for tuples G^n with no identity entry,
B_n=⊕_(g∈G^n)k[G] for the full free representation, and
Q_n=⊕_(g∈N_n)k[G] for the normalized degree, with finite support.
The degeneracy submodule D_n⊂B_n consists of coefficient
functions supported on tuples with an identity entry.
It is a submodule over the possibly noncommutative group ring k[G]. -/
def degenerateDegree (n : ℕ) : Submodule k[G] ((Fin n → G) →₀ k[G]) :=
  Finsupp.supported k[G] k[G] {g | ¬ IsNondegenerate G g}

/-- Let k be a commutative ring in universe u and G a group in
universe v. Write N_n for tuples G^n with no identity entry,
B_n=⊕_(g∈G^n)k[G] for the full free representation, and
Q_n=⊕_(g∈N_n)k[G] for the normalized degree, with finite support.
The degeneracy submodule is the k[G]-span of the basis symbols
[g] with some g_i=1. -/
theorem degenerateDegree_eq_span (n : ℕ) :
    degenerateDegree k G n =
      Submodule.span k[G] ((fun g : Fin n → G => Finsupp.single g (1 : k[G])) ''
        {g | ∃ i, g i = 1}) := by
  classical
  simpa only [degenerateDegree, IsNondegenerate, not_forall, not_not] using
    (Finsupp.supported_eq_span_single (R := k[G]) {g : Fin n → G | ¬ IsNondegenerate G g})

/-- Let k be a commutative ring in universe u and G a group in
universe v. Write N_n for tuples G^n with no identity entry,
B_n=⊕_(g∈G^n)k[G] for the full free representation, and
Q_n=⊕_(g∈N_n)k[G] for the normalized degree, with finite support.
For f∈B_n, the degree projection is zero exactly when
f belongs to the degeneracy submodule D_n. -/
theorem rawProjection_eq_zero_iff (n : ℕ) (f : (fullDegree k G n).V) :
    (rawProjection k G n).hom f = 0 ↔ f ∈ degenerateDegree k G n := by
  change (rawProjection k G n).hom.toLinearMap f = 0 ↔ _
  rw [rawProjection_eq_lsubtypeDomain]
  change Finsupp.subtypeDomain (IsNondegenerate G) f = 0 ↔ _
  rw [Finsupp.subtypeDomain_eq_zero_iff']
  simp only [degenerateDegree, Finsupp.mem_supported', Set.mem_ofPred_eq, not_not]

/-- Let k be a commutative ring in universe u and G a group in
universe v. Write N_n for tuples G^n with no identity entry,
B_n=⊕_(g∈G^n)k[G] for the full free representation, and
Q_n=⊕_(g∈N_n)k[G] for the normalized degree, with finite support.
The standard-degree projection is the homogeneous/full tuple
basis isomorphism followed by B_n→Q_n. -/
def standardProjection (n : ℕ) :
    (standardSimplicial k G).obj (Opposite.op ⦋n⦌) ⟶ degree k G n :=
  (basisIso k G n).hom ≫ rawProjection k G n

/-- Let k be a commutative ring in universe u and G a group in
universe v. Write N_n for tuples G^n with no identity entry,
B_n=⊕_(g∈G^n)k[G] for the full free representation, and
Q_n=⊕_(g∈N_n)k[G] for the normalized degree, with finite support.
The raw inclusion into standard degree n is Q_n→B_n followed
by the inverse homogeneous basis isomorphism. -/
def standardRawInclusion (n : ℕ) :
    degree k G n ⟶ (standardSimplicial k G).obj (Opposite.op ⦋n⦌) :=
  rawInclusion k G n ≫ (basisIso k G n).inv

@[reassoc (attr := simp)]
theorem standardRawInclusion_comp_standardProjection (n : ℕ) :
    standardRawInclusion k G n ≫ standardProjection k G n = 𝟙 (degree k G n) := by
  simp [standardRawInclusion, standardProjection, Category.assoc]

end Rep.NormalizedBar

end
