/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicGeometry_HilbertFunctor.lean`,
`Theorems/Thm_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.lean`,
`P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map.lean`,
`Theorems/Thm_AlgebraicGeometry_HilbertFunctor_Point_I_eq_span_of_forall_finrank_piece_succ_le.lean`
and
`P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_Point_I_eq_span_of_forall_finrank_piece_succ_le.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.Rank
import Mathlib.RingTheory.Finiteness.Nakayama
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.LinearAlgebra.Finsupp.SumProd

@[expose] public section

open MvPolynomial
open scoped TensorProduct

namespace AlgebraicGeometry
namespace HilbertFunctor

universe u

/-- The degree-`d` graded piece of the quotient by a homogeneous ideal `I`:
the degree-`d` homogeneous submodule modulo its intersection with `I`. -/
abbrev piece {A : Type*} [CommRing A] {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) A))
    (d : ℕ) : Type _ :=
  ↥(homogeneousSubmodule (Fin (n + 1)) A d) ⧸
    Submodule.comap (homogeneousSubmodule (Fin (n + 1)) A d).subtype (I.restrictScalars A)

/-- A point of the Hilbert functor: a homogeneous ideal whose graded pieces are
finite projective modules of prescribed stalk rank `h d` in every degree. -/
structure Point (A : Type*) [CommRing A] (n : ℕ) (h : ℕ → ℕ) where
  /-- The homogeneous ideal defining the point. -/
  I : Ideal (MvPolynomial (Fin (n + 1)) A)
  /-- The ideal is homogeneous: it contains every homogeneous component of
  each of its elements. -/
  homogeneous : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I
  /-- Every graded piece is finite. -/
  finite_piece : ∀ d : ℕ, Module.Finite A (piece I d)
  /-- Every graded piece is projective. -/
  projective_piece : ∀ d : ℕ, Module.Projective A (piece I d)
  /-- The stalk rank of the degree-`d` piece is `h d` at every prime. -/
  rankAtStalk_piece : ∀ (d : ℕ) (p : PrimeSpectrum A), Module.rankAtStalk (piece I d) p = h d

/-- Two points with the same ideal are equal. -/
@[ext]
theorem Point.ext {A : Type*} [CommRing A] {n : ℕ} {h : ℕ → ℕ} {P Q : Point A n h}
    (e : P.I = Q.I) : P = Q := by
  cases P; cases Q; cases e; rfl

attribute [local instance] MvPolynomial.gradedAlgebra

namespace HilbPieceBC

variable {n : ℕ} {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

omit [Algebra A B] in
private theorem homogeneousComponent_map (φ : A →+* B) (d : ℕ) (p : MvPolynomial (Fin (n + 1)) A) :
    homogeneousComponent d (MvPolynomial.map φ p) = MvPolynomial.map φ (homogeneousComponent d p)
      := by
  ext c
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp

private theorem degree_eq_of_mem_support {R : Type*} [CommRing R] {p : MvPolynomial (Fin (n + 1))
  R} {d : ℕ}
    (hp : p.IsHomogeneous d) {s : Fin (n + 1) →₀ ℕ} (hs : s ∈ p.support) : s.degree = d := by
  have h := hp (mem_support_iff.mp hs)
  have : (Finsupp.degree s : ℕ) = Finsupp.weight (fun _ => 1) s := by
    rw [Finsupp.degree_eq_weight_one]
  rw [this]
  exact h

private theorem decompose_eq (q : MvPolynomial (Fin (n + 1)) B) (d : ℕ) :
    (DirectSum.decompose (homogeneousSubmodule (Fin (n + 1)) B) q d : MvPolynomial (Fin (n + 1)) B)
      =
      homogeneousComponent d q :=
  MvPolynomial.decomposition.decompose'_apply q d

variable (n A B) in
private noncomputable def T (I : Ideal (MvPolynomial (Fin (n + 1)) A)) (j : ℕ) :
    Submodule B (MvPolynomial (Fin (n + 1)) B) :=
  Submodule.span B
    (MvPolynomial.map (algebraMap A B) '' {p | p ∈ I ∧ p.IsHomogeneous j})

private theorem map_mem_T {I : Ideal (MvPolynomial (Fin (n + 1)) A)} {j : ℕ} {p : MvPolynomial (Fin
  (n + 1)) A}
    (hp : p ∈ I) (hpj : p.IsHomogeneous j) : MvPolynomial.map (algebraMap A B) p ∈ T n A B I j :=
  Submodule.subset_span ⟨p, ⟨hp, hpj⟩, rfl⟩

private theorem mul_mem_T (I : Ideal (MvPolynomial (Fin (n + 1)) A)) {i j : ℕ}
    {g : MvPolynomial (Fin (n + 1)) B} (hg : g.IsHomogeneous i)
    {x : MvPolynomial (Fin (n + 1)) B} (hx : x ∈ T n A B I j) : g * x ∈ T n A B I (i + j) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨p, ⟨hpI, hpj⟩, rfl⟩ := hy
    rw [MvPolynomial.as_sum g, Finset.sum_mul]
    refine Submodule.sum_mem _ fun s hs => ?_
    have hsdeg : s.degree = i := degree_eq_of_mem_support hg hs
    have hmono : (monomial s (g.coeff s) : MvPolynomial (Fin (n + 1)) B) =
        g.coeff s • MvPolynomial.map (algebraMap A B) (monomial s (1 : A)) := by
      rw [map_monomial, map_one, smul_monomial, smul_eq_mul, mul_one]
    rw [hmono, smul_mul_assoc, ← map_mul]
    refine Submodule.smul_mem _ _ (map_mem_T (I.mul_mem_left _ hpI) ?_)
    exact (isHomogeneous_monomial (1 : A) hsdeg).mul hpj
  | zero => simp
  | add y z _ _ hy hz => simpa [mul_add] using Submodule.add_mem _ hy hz
  | smul b y _ hy => simpa [mul_smul_comm] using Submodule.smul_mem _ b hy

private theorem homogeneousComponent_mem_T (I : Ideal (MvPolynomial (Fin (n + 1)) A))
    (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I)
    {q : MvPolynomial (Fin (n + 1)) B} (hq : q ∈ I.map (MvPolynomial.map (algebraMap A B))) (d : ℕ)
      :
    homogeneousComponent d q ∈ T n A B I d := by
  revert d
  refine Submodule.span_induction (p := fun q _ => ∀ d : ℕ, homogeneousComponent d q ∈ T n A B I d)
    ?_ ?_ ?_ ?_ (show q ∈ Ideal.span _ from hq)
  · rintro y ⟨p, hpI, rfl⟩ d
    rw [homogeneousComponent_map]
    exact map_mem_T (hI p hpI d) (homogeneousComponent_isHomogeneous d p)
  · intro d
    simp
  · intro y z _ _ hy hz d
    simpa [map_add] using Submodule.add_mem _ (hy d) (hz d)
  · intro g y _ hy d
    rw [smul_eq_mul, ← sum_homogeneousComponent g, Finset.sum_mul, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hgi : homogeneousComponent i g ∈ homogeneousSubmodule (Fin (n + 1)) B i :=
      homogeneousComponent_mem i g
    have key := DirectSum.coe_decompose_mul_of_left_mem (𝒜 := homogeneousSubmodule (Fin (n + 1)) B)
      (b := y) d hgi
    rw [decompose_eq, decompose_eq] at key
    rw [key]
    split_ifs with hid
    · have := mul_mem_T I (homogeneousComponent_isHomogeneous i g) (hy (d - i))
      rwa [Nat.add_sub_cancel' hid] at this
    · exact Submodule.zero_mem _

private theorem T_le (I : Ideal (MvPolynomial (Fin (n + 1)) A)) (d : ℕ) :
    T n A B I d ≤ (I.map (MvPolynomial.map (algebraMap A B))).restrictScalars B := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨p, ⟨hpI, -⟩, rfl⟩
  exact Ideal.mem_map_of_mem _ hpI

private theorem map_homogeneous (I : Ideal (MvPolynomial (Fin (n + 1)) A))
    (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) :
    ∀ q ∈ I.map (MvPolynomial.map (algebraMap A B)), ∀ d : ℕ,
      homogeneousComponent d q ∈ I.map (MvPolynomial.map (algebraMap A B)) :=
  fun _ hq d => T_le I d (homogeneousComponent_mem_T I hI hq d)

section Equiv

variable (I : Ideal (MvPolynomial (Fin (n + 1)) A)) (d : ℕ)

private abbrev SA : Submodule A (MvPolynomial (Fin (n + 1)) A) := homogeneousSubmodule (Fin (n +
  1)) A d

private abbrev SB : Submodule B (MvPolynomial (Fin (n + 1)) B) := homogeneousSubmodule (Fin (n +
  1)) B d

private noncomputable abbrev I' : Ideal (MvPolynomial (Fin (n + 1)) B) := I.map (MvPolynomial.map
  (algebraMap A B))

private noncomputable abbrev KA : Submodule A (SA (n := n) (A := A) d) :=
  Submodule.comap (SA (n := n) (A := A) d).subtype (I.restrictScalars A)

private noncomputable abbrev KB : Submodule B (SB (n := n) (B := B) d) :=
  Submodule.comap (SB (n := n) (B := B) d).subtype ((I' (B := B) I).restrictScalars B)

private noncomputable def gd : SA (n := n) (A := A) d →ₗ[A] SB (n := n) (B := B) d where
  toFun p := ⟨MvPolynomial.map (algebraMap A B) (p : MvPolynomial (Fin (n + 1)) A),
    (show (p : MvPolynomial (Fin (n + 1)) A).IsHomogeneous d from p.2).map (algebraMap A B)⟩
  map_add' p q := by
    ext : 1
    simp
  map_smul' a p := by
    ext : 1
    simp only [RingHom.id_apply, Submodule.coe_smul_of_tower, SetLike.val_smul]
    rw [MvPolynomial.smul_eq_C_mul, map_mul, map_C, Algebra.smul_def, MvPolynomial.algebraMap_apply]

@[scoped simp] private theorem gd_apply_coe (p : SA (n := n) (A := A) d) :
    ((gd (B := B) d p : SB (n := n) (B := B) d) : MvPolynomial (Fin (n + 1)) B) =
      MvPolynomial.map (algebraMap A B) (p : MvPolynomial (Fin (n + 1)) A) := rfl

private noncomputable def gbar : piece I d →ₗ[A] piece (I' (B := B) I) d :=
  (KA I d).liftQ (((KB (B := B) I d).mkQ.restrictScalars A) ∘ₗ gd (B := B) d) (by
    intro p hp
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_restrictScalars, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, Submodule.coe_subtype, Submodule.restrictScalars_mem]
    exact Ideal.mem_map_of_mem _ hp)

private theorem gbar_mk (p : SA (n := n) (A := A) d) :
    gbar (B := B) I d (Submodule.Quotient.mk p) = Submodule.Quotient.mk (gd (B := B) d p) := rfl

private noncomputable def E : B ⊗[A] piece I d →ₗ[B] piece (I' (B := B) I) d :=
  (gbar (B := B) I d).liftBaseChange B

private theorem E_tmul (b : B) (p : SA (n := n) (A := A) d) :
    E (B := B) I d (b ⊗ₜ[A] Submodule.Quotient.mk p) = b • Submodule.Quotient.mk (gd (B := B) d p)
      := by
  simp [E, LinearMap.liftBaseChange_tmul, gbar_mk]

private noncomputable def v : (Fin (n + 1) →₀ ℕ) → B ⊗[A] piece I d := fun s =>
  if hs : s.degree = d then
    (1 : B) ⊗ₜ[A] Submodule.Quotient.mk (⟨monomial s (1 : A), isHomogeneous_monomial (1 : A) hs⟩ :
      SA (n := n) (A := A) d)
  else 0

private noncomputable def Psi' : MvPolynomial (Fin (n + 1)) B →ₗ[B] B ⊗[A] piece I d :=
  (MvPolynomial.basisMonomials (Fin (n + 1)) B).constr B (v (B := B) I d)

private theorem Psi'_monomial (s : Fin (n + 1) →₀ ℕ) (b : B) :
    Psi' (B := B) I d (monomial s b) = b • v (B := B) I d s := by
  have h1 : (monomial s b : MvPolynomial (Fin (n + 1)) B) =
      b • (MvPolynomial.basisMonomials (Fin (n + 1)) B) s := by
    rw [MvPolynomial.coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h1, map_smul, Psi', Module.Basis.constr_basis]

private theorem Psi'_map (p : MvPolynomial (Fin (n + 1)) A) (hp : p.IsHomogeneous d) :
    Psi' (B := B) I d (MvPolynomial.map (algebraMap A B) p) =
      (1 : B) ⊗ₜ[A] Submodule.Quotient.mk (⟨p, hp⟩ : SA (n := n) (A := A) d) := by
  classical
  have hw : ∀ s : Fin (n + 1) →₀ ℕ, (monomial s (p.coeff s) : MvPolynomial (Fin (n + 1))
    A).IsHomogeneous d := by
    intro s
    by_cases hs : p.coeff s = 0
    · rw [hs, monomial_zero]
      exact isHomogeneous_zero _ _ _
    · exact isHomogeneous_monomial _ (degree_eq_of_mem_support hp (mem_support_iff.mpr hs))
  let w : (Fin (n + 1) →₀ ℕ) → SA (n := n) (A := A) d := fun s => ⟨monomial s (p.coeff s), hw s⟩
  have hp_sum : (⟨p, hp⟩ : SA (n := n) (A := A) d) = ∑ s ∈ p.support, w s := by
    apply Subtype.ext
    simp only [w, AddSubmonoidClass.coe_finsetSum]
    exact p.as_sum
  have hmap : MvPolynomial.map (algebraMap A B) p =
      ∑ s ∈ p.support, monomial s (algebraMap A B (p.coeff s)) := by
    conv_lhs => rw [p.as_sum]
    simp only [map_sum, map_monomial]
  have hterm : ∀ s ∈ p.support, Psi' (B := B) I d (monomial s (algebraMap A B (p.coeff s))) =
      (1 : B) ⊗ₜ[A] Submodule.Quotient.mk (w s) := by
    intro s hs
    have hsd : s.degree = d := degree_eq_of_mem_support hp hs
    rw [Psi'_monomial]
    simp only [v, dif_pos hsd]
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      show algebraMap A B (p.coeff s) = p.coeff s • (1 : B) by rw [Algebra.smul_def, mul_one],
      TensorProduct.smul_tmul, ← Submodule.Quotient.mk_smul]
    congr 2
    apply Subtype.ext
    simp [w, smul_monomial]
  rw [hmap, map_sum, Finset.sum_congr rfl hterm, ← TensorProduct.tmul_sum, hp_sum]
  congr 1
  simp only [← Submodule.mkQ_apply, map_sum]

private theorem Psi'_map_eq_zero (p : MvPolynomial (Fin (n + 1)) A) (hpI : p ∈ I) (hp :
  p.IsHomogeneous d) :
    Psi' (B := B) I d (MvPolynomial.map (algebraMap A B) p) = 0 := by
  rw [Psi'_map I d p hp]
  have : (Submodule.Quotient.mk (⟨p, hp⟩ : SA (n := n) (A := A) d) : piece I d) = 0 := by
    rw [Submodule.Quotient.mk_eq_zero]
    simpa using hpI
  rw [this, TensorProduct.tmul_zero]

private theorem T_le_ker : T n A B I d ≤ LinearMap.ker (Psi' (B := B) I d) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨p, ⟨hpI, hpd⟩, rfl⟩
  exact Psi'_map_eq_zero I d p hpI hpd

private noncomputable def Psi (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) :
    piece (I' (B := B) I) d →ₗ[B] B ⊗[A] piece I d :=
  (KB (B := B) I d).liftQ (Psi' (B := B) I d ∘ₗ (SB (n := n) (B := B) d).subtype) (by
    intro q hq
    have hqI : (q : MvPolynomial (Fin (n + 1)) B) ∈ I' (B := B) I := by simpa using hq
    have hqd : (q : MvPolynomial (Fin (n + 1)) B).IsHomogeneous d := q.2
    have hcomp : homogeneousComponent d (q : MvPolynomial (Fin (n + 1)) B) = q :=
      homogeneousComponent_of_mem (m := d) q.2 |>.trans (if_pos rfl)
    rw [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, ← hcomp]
    exact T_le_ker I d (homogeneousComponent_mem_T I hI hqI d))

private theorem Psi_mk (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) (q : SB (n := n) (B :=
  B) d) :
    Psi (B := B) I d hI (Submodule.Quotient.mk q) = Psi' (B := B) I d (q : MvPolynomial (Fin (n +
      1)) B) :=
  rfl

private theorem Psi_E (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) (x : B ⊗[A] piece I d) :
    Psi (B := B) I d hI (E (B := B) I d x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b y =>
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [E_tmul, map_smul, Psi_mk, gd_apply_coe, Psi'_map I d _ p.2, TensorProduct.smul_tmul',
      smul_eq_mul, mul_one]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

private theorem E_Psi (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) (z : piece (I' (B := B)
  I) d) :
    E (B := B) I d (Psi (B := B) I d hI z) = z := by
  classical
  obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [Psi_mk]
  have hq : (q : MvPolynomial (Fin (n + 1)) B).IsHomogeneous d := q.2
  have hw : ∀ s : Fin (n + 1) →₀ ℕ,
      (monomial s ((q : MvPolynomial (Fin (n + 1)) B).coeff s) : MvPolynomial (Fin (n + 1))
        B).IsHomogeneous d := by
    intro s
    by_cases hs : (q : MvPolynomial (Fin (n + 1)) B).coeff s = 0
    · rw [hs, monomial_zero]
      exact isHomogeneous_zero _ _ _
    · exact isHomogeneous_monomial _ (degree_eq_of_mem_support hq (mem_support_iff.mpr hs))
  let w : (Fin (n + 1) →₀ ℕ) → SB (n := n) (B := B) d :=
    fun s => ⟨monomial s ((q : MvPolynomial (Fin (n + 1)) B).coeff s), hw s⟩
  have hq_sum : q = ∑ s ∈ (q : MvPolynomial (Fin (n + 1)) B).support, w s := by
    apply Subtype.ext
    simp only [w, AddSubmonoidClass.coe_finsetSum]
    exact (q : MvPolynomial (Fin (n + 1)) B).as_sum
  have hterm : ∀ s ∈ (q : MvPolynomial (Fin (n + 1)) B).support,
      E (B := B) I d (Psi' (B := B) I d (monomial s ((q : MvPolynomial (Fin (n + 1)) B).coeff s))) =
        Submodule.Quotient.mk (w s) := by
    intro s hs
    have hsd : s.degree = d := degree_eq_of_mem_support hq hs
    rw [Psi'_monomial]
    simp only [v, dif_pos hsd]
    rw [map_smul, E_tmul, one_smul, ← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    simp [w, smul_monomial, map_monomial]
  conv_lhs => rw [(q : MvPolynomial (Fin (n + 1)) B).as_sum, map_sum, map_sum]
  rw [Finset.sum_congr rfl hterm, hq_sum]
  simp only [← Submodule.mkQ_apply, map_sum]
  rw [← hq_sum]

private noncomputable def equiv (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) :
    B ⊗[A] piece I d ≃ₗ[B] piece (I' (B := B) I) d :=
  LinearEquiv.ofLinear (E (B := B) I d) (Psi (B := B) I d hI)
    (LinearMap.ext fun z => E_Psi I d hI z) (LinearMap.ext fun x => Psi_E I d hI x)

private theorem equiv_tmul_mk (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I)
    (p : MvPolynomial (Fin (n + 1)) A) (hp : p.IsHomogeneous d) :
    equiv (B := B) I d hI ((1 : B) ⊗ₜ[A] Submodule.Quotient.mk ⟨p, hp⟩) =
      Submodule.Quotient.mk ⟨MvPolynomial.map (algebraMap A B) p, hp.map (algebraMap A B)⟩ := by
  change E (B := B) I d _ = _
  rw [E_tmul, one_smul]
  rfl

end Equiv

end HilbPieceBC

/-- Base change of a graded piece: tensoring the degree-`d` piece of a
homogeneous ideal with an algebra gives the degree-`d` piece of the mapped
ideal, compatibly with the map on homogeneous polynomials. -/
public theorem exists_linearEquiv_baseChange_piece_map
    (n : ℕ) (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal (MvPolynomial (Fin (n + 1)) A))
    (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) :
    (∀ q ∈ I.map (MvPolynomial.map (algebraMap A B)), ∀ d : ℕ,
        homogeneousComponent d q ∈ I.map (MvPolynomial.map (algebraMap A B))) ∧
    ∀ d : ℕ, ∃ e : B ⊗[A] piece I d ≃ₗ[B] piece (I.map (MvPolynomial.map (algebraMap A B))) d,
      ∀ (p : MvPolynomial (Fin (n + 1)) A) (hp : p.IsHomogeneous d),
        e (1 ⊗ₜ[A] Submodule.Quotient.mk ⟨p, hp⟩) =
          Submodule.Quotient.mk ⟨MvPolynomial.map (algebraMap A B) p, hp.map (algebraMap A B)⟩ :=
  ⟨HilbPieceBC.map_homogeneous I hI, fun d =>
    ⟨HilbPieceBC.equiv I d hI, fun p hp => HilbPieceBC.equiv_tmul_mk I d hI p hp⟩⟩

namespace HilbGenH2c

section Modules

variable {A : Type*} [CommRing A]

private theorem exists_equiv_prod_ker {Q₁ Q₂ : Type*} [AddCommGroup Q₁] [Module A Q₁] [AddCommGroup
  Q₂] [Module A Q₂]
    [Module.Projective A Q₂] (π : Q₁ →ₗ[A] Q₂) (hπ : Function.Surjective π) :
    ∃ e : Q₁ ≃ₗ[A] Q₂ × LinearMap.ker π, ∀ x, (e x).1 = π x := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hs' : ∀ y, π (s y) = y := fun y => by simpa using LinearMap.congr_fun hs y
  refine ⟨{ toFun := fun x => (π x, ⟨x - s (π x), by simp [hs']⟩)
            invFun := fun yk => s yk.1 + yk.2
            map_add' := fun x y => by ext <;> simp [map_add]; abel
            map_smul' := fun a x => by ext <;> simp [map_smul, smul_sub]
            left_inv := fun x => by simp
            right_inv := fun yk => by
              obtain ⟨y, k, hk⟩ := yk
              have hk' : π k = 0 := hk
              ext <;> simp [hs', hk'] }, fun x => rfl⟩

private theorem subsingleton_of_finrank_fiber_eq_zero (K : Type*) [AddCommGroup K] [Module A K]
  [Module.Finite A K]
    (hK : ∀ p : PrimeSpectrum A, Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A]
      K) = 0) :
    Subsingleton K := by

  have hnak : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → ∃ r : A, r - 1 ∈ 𝔪 ∧ ∀ k : K, r • k = 0 := by
    intro 𝔪 h𝔪
    let p : PrimeSpectrum A := ⟨𝔪, h𝔪.isPrime⟩
    let κ := p.asIdeal.ResidueField
    haveI : Module.Finite κ (κ ⊗[A] K) := Module.Finite.base_change A κ K
    have hsub : Subsingleton (κ ⊗[A] K) :=
      (subsingleton_iff_forall_eq 0).mpr (finrank_zero_iff_forall_zero.mp (hK p))

    have hbij := Ideal.bijective_algebraMap_quotient_residueField 𝔪
    let f : (A ⧸ 𝔪) →ₗ[A] κ := (IsScalarTower.toAlgHom A (A ⧸ 𝔪) κ).toLinearMap
    have hf : Function.Bijective f := hbij
    let e : (A ⧸ 𝔪) ≃ₗ[A] κ := LinearEquiv.ofBijective f hf
    have hsub' : Subsingleton ((A ⧸ 𝔪) ⊗[A] K) :=
      (TensorProduct.congr e (LinearEquiv.refl A K)).toEquiv.subsingleton
    have hsub'' : Subsingleton (K ⧸ (𝔪 • (⊤ : Submodule A K))) :=
      (TensorProduct.quotTensorEquivQuotSMul K 𝔪).symm.toEquiv.subsingleton
    have htop : (𝔪 • (⊤ : Submodule A K)) = ⊤ := Submodule.Quotient.subsingleton_iff.mp hsub''
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔪 (⊤ :
      Submodule A K)
      Module.Finite.fg_top (by rw [htop])
    exact ⟨r, hr, fun k => hr0 k Submodule.mem_top⟩

  by_contra hne
  have hann : Module.annihilator A K ≠ ⊤ := by
    intro htop
    apply hne
    refine ⟨fun x y => ?_⟩
    have h1 : (1 : A) ∈ Module.annihilator A K := by rw [htop]; exact Submodule.mem_top
    rw [Module.mem_annihilator] at h1
    have hx := h1 x
    have hy := h1 y
    rw [one_smul] at hx hy
    rw [hx, hy]
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hann
  obtain ⟨r, hr, hr0⟩ := hnak 𝔪 h𝔪
  have hrmem : r ∈ 𝔪 := hle (Module.mem_annihilator.mpr hr0)
  have : (1 : A) ∈ 𝔪 := by
    have := 𝔪.sub_mem hrmem hr
    rwa [sub_sub_cancel] at this
  exact h𝔪.ne_top (𝔪.eq_top_of_isUnit_mem this isUnit_one)

end Modules

variable {n : ℕ}

private theorem finite_homogeneousSubmodule (R : Type*) [CommRing R] (d : ℕ) :
    Module.Finite R ↥(homogeneousSubmodule (Fin (n + 1)) R d) := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  haveI : Finite {x : Fin (n + 1) →₀ ℕ | x.degree = d} :=
    ((Finsupp.finite_of_degree_le d).subset (t := {x | x.degree = d})
      fun x (hx : x.degree = d) => le_of_eq hx).to_subtype
  exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport R {x : Fin (n + 1) →₀ ℕ |
    x.degree = d})

private theorem free_homogeneousSubmodule (R : Type*) [CommRing R] (d : ℕ) :
    Module.Free R ↥(homogeneousSubmodule (Fin (n + 1)) R d) := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  exact Module.Free.of_basis (MvPolynomial.basisRestrictSupport R {x : Fin (n + 1) →₀ ℕ | x.degree
    = d})

private theorem finite_piece_of_quotient (R : Type*) [CommRing R] (J : Ideal (MvPolynomial (Fin (n
  + 1)) R)) (d : ℕ) :
    Module.Finite R (piece J d) := by
  haveI := finite_homogeneousSubmodule (n := n) R d
  exact Module.Finite.quotient R _


private theorem natCard_degree_eq (d : ℕ) : Nat.card {s : Fin (n + 1) →₀ ℕ // s.degree = d} = (n +
  d).choose n := by
  classical
  let e : {s : Fin (n + 1) →₀ ℕ // s.degree = d} ≃ Sym (Fin (n + 1)) d :=
    { toFun := fun s => ⟨Finsupp.toMultiset s.1, by
        have h2 := s.2
        rw [Finsupp.degree_apply] at h2
        rw [Finsupp.card_toMultiset]
        simpa [Finsupp.sum] using h2⟩
      invFun := fun t => ⟨Multiset.toFinsupp (t : Multiset (Fin (n + 1))), by
        have h1 := Finsupp.card_toMultiset (Multiset.toFinsupp (t : Multiset (Fin (n + 1))))
        rw [Multiset.toFinsupp_toMultiset] at h1
        rw [Finsupp.degree_apply]
        have h2 : (t : Multiset (Fin (n + 1))).card = d := t.2
        simpa [Finsupp.sum, h2] using h1.symm⟩
      left_inv := fun s => by
        apply Subtype.ext
        simp
      right_inv := fun t => by
        apply Subtype.ext
        simp }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Sym.card_sym_eq_choose, Fintype.card_fin,
    show n + 1 + d - 1 = n + d by omega, Nat.choose_symm_add]

private theorem finrank_homogeneousSubmodule (A : Type*) [CommRing A] [Nontrivial A] (d : ℕ) :
    Module.finrank A ↥(homogeneousSubmodule (Fin (n + 1)) A d) = (n + d).choose n := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  exact (Module.finrank_eq_nat_card_basis
    (MvPolynomial.basisRestrictSupport A {x : Fin (n + 1) →₀ ℕ | x.degree = d})).trans
      (natCard_degree_eq d)

private theorem span_homogeneous (A : Type*) [CommRing A] (s : Set (MvPolynomial (Fin (n + 1)) A))
  (e : ℕ)
    (hs : ∀ p ∈ s, p.IsHomogeneous e) :
    ∀ p ∈ Ideal.span s, ∀ d : ℕ, homogeneousComponent d p ∈ Ideal.span s := by
  intro p hp d
  have H := Ideal.homogeneous_span (homogeneousSubmodule (Fin (n + 1)) A) s (fun x hx => ⟨e, hs x
    hx⟩)
  have := H d hp
  rwa [show (DirectSum.decompose (homogeneousSubmodule (Fin (n + 1)) A) p d : MvPolynomial (Fin (n
    + 1)) A) =
      homogeneousComponent d p from MvPolynomial.decomposition.decompose'_apply p d] at this

section Step

variable {A : Type u} [CommRing A] (h : ℕ → ℕ) (P : Point A n h) (e : ℕ)

private noncomputable def J' : Ideal (MvPolynomial (Fin (n + 1)) A) := Ideal.span {p | p ∈ P.I ∧
  p.IsHomogeneous e}

private theorem J'_le : J' h P e ≤ P.I := Ideal.span_le.mpr fun _ hp => hp.1

private theorem J'_generated : ∃ s : Set (MvPolynomial (Fin (n + 1)) A), (∀ p ∈ s, p.IsHomogeneous
  e) ∧ J' h P e = Ideal.span s :=
  ⟨{p | p ∈ P.I ∧ p.IsHomogeneous e}, fun _ hp => hp.2, rfl⟩

private theorem J'_homogeneous : ∀ p ∈ J' h P e, ∀ d : ℕ, homogeneousComponent d p ∈ J' h P e :=
  span_homogeneous A _ e fun _ hp => hp.2

private theorem comap_J'_eq :
    Submodule.comap (homogeneousSubmodule (Fin (n + 1)) A e).subtype ((J' h P e).restrictScalars A)
      =
      Submodule.comap (homogeneousSubmodule (Fin (n + 1)) A e).subtype (P.I.restrictScalars A) := by
  ext q
  simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.restrictScalars_mem]
  exact ⟨fun hq => J'_le h P e hq, fun hq => Ideal.subset_span ⟨hq, q.2⟩⟩

private noncomputable def pieceJ'Equiv : piece (J' h P e) e ≃ₗ[A] piece P.I e :=
  Submodule.quotEquivOfEq _ _ (comap_J'_eq h P e)

private noncomputable def π : piece (J' h P e) (e + 1) →ₗ[A] piece P.I (e + 1) :=
  Submodule.mapQ _ _ LinearMap.id fun q hq => by
    simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.restrictScalars_mem,
      LinearMap.id_coe,
      id_eq] at hq ⊢
    exact J'_le h P e hq

private theorem π_mk (q : ↥(homogeneousSubmodule (Fin (n + 1)) A (e + 1))) :
    π h P e (Submodule.Quotient.mk q) = Submodule.Quotient.mk q := rfl

private theorem π_surjective : Function.Surjective (π h P e) := by
  intro y
  obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨Submodule.Quotient.mk q, rfl⟩

variable (hm : ∀ (K : Type u) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) →
      Module.finrank K (piece J e) = h e → Module.finrank K (piece J (e + 1)) ≤ h (e + 1))

include hm in
private theorem finrank_fiber_Q₁_le (p : PrimeSpectrum A) :
    Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] piece (J' h P e) (e + 1)) ≤
      h (e + 1) := by
  let κ := p.asIdeal.ResidueField
  obtain ⟨-, hpiece⟩ := exists_linearEquiv_baseChange_piece_map n A κ (J' h P e)
    (J'_homogeneous h P e)
  obtain ⟨e₁, -⟩ := hpiece (e + 1)
  obtain ⟨e₀, -⟩ := hpiece e
  rw [e₁.finrank_eq]
  refine hm κ _ ⟨MvPolynomial.map (algebraMap A κ) '' {p | p ∈ P.I ∧ p.IsHomogeneous e}, ?_,
    Ideal.map_span _ _⟩ ?_
  · rintro _ ⟨q, hq, rfl⟩
    exact hq.2.map _
  · rw [← e₀.finrank_eq]
    haveI := P.finite_piece e
    haveI := P.projective_piece e
    haveI : Module.Finite A (piece (J' h P e) e) := Module.Finite.equiv (pieceJ'Equiv h P e).symm
    haveI : Module.Projective A (piece (J' h P e) e) := Module.Projective.of_equiv (pieceJ'Equiv h
      P e).symm
    rw [← P.rankAtStalk_piece e p, ← congrFun (Module.rankAtStalk_eq_of_equiv (pieceJ'Equiv h P e))
      p,
      Module.rankAtStalk_eq]

include hm in
private theorem ker_π_eq_bot : LinearMap.ker (π h P e) = ⊥ := by
  haveI := P.projective_piece (e + 1)
  haveI := P.finite_piece (e + 1)
  haveI : Module.Finite A (piece (J' h P e) (e + 1)) := finite_piece_of_quotient A _ _
  obtain ⟨E, hE⟩ := exists_equiv_prod_ker (π h P e) (π_surjective h P e)
  haveI : Module.Finite A (LinearMap.ker (π h P e)) :=
    Module.Finite.of_surjective ((LinearMap.snd A _ _).comp E.toLinearMap) fun k => ⟨E.symm (0, k),
      by simp⟩
  have hfib : ∀ p : PrimeSpectrum A,
      Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] LinearMap.ker (π h P e)) =
        0 := by
    intro p
    haveI : Module.Finite p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] piece (J' h P e) (e +
      1)) :=
      Module.Finite.base_change A _ _
    haveI : Module.Finite p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] piece P.I (e + 1)) :=
      Module.Finite.base_change A _ _
    haveI : Module.Finite p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] LinearMap.ker (π h P
      e)) :=
      Module.Finite.base_change A _ _
    haveI : Module.Free p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] piece P.I (e + 1)) :=
      Module.Free.of_divisionRing _ _
    haveI : Module.Free p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] LinearMap.ker (π h P
      e)) :=
      Module.Free.of_divisionRing _ _
    have hsum : Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] piece (J' h P e)
      (e + 1)) =
        Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] piece P.I (e + 1)) +
          Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] LinearMap.ker (π h P
            e)) := by
      rw [(E.baseChange A p.asIdeal.ResidueField _ _ ≪≫ₗ
        TensorProduct.prodRight A p.asIdeal.ResidueField p.asIdeal.ResidueField _ _).finrank_eq,
          Module.finrank_prod]
    have h1 := finrank_fiber_Q₁_le h P e hm p
    have h2 : Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] piece P.I (e + 1))
      = h (e + 1) := by
      rw [← P.rankAtStalk_piece (e + 1) p, Module.rankAtStalk_eq]
    omega
  have hsub := subsingleton_of_finrank_fiber_eq_zero (LinearMap.ker (π h P e)) hfib
  exact Submodule.eq_bot_iff _ |>.mpr fun x hx => congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩
    : LinearMap.ker _) 0)

include hm in
private theorem mem_J'_of_mem (q : MvPolynomial (Fin (n + 1)) A) (hqI : q ∈ P.I) (hq :
  q.IsHomogeneous (e + 1)) :
    q ∈ J' h P e := by
  have hker := ker_π_eq_bot h P e hm
  have hzero : π h P e (Submodule.Quotient.mk ⟨q, hq⟩) = 0 := by
    rw [π_mk, Submodule.Quotient.mk_eq_zero]
    simpa using hqI
  have hmem : (Submodule.Quotient.mk ⟨q, hq⟩ : piece (J' h P e) (e + 1)) ∈ LinearMap.ker (π h P e)
    := hzero
  rw [hker, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero] at hmem
  simpa using hmem

end Step

section Low

variable {A : Type*} [CommRing A] [Nontrivial A] (h : ℕ → ℕ) (P : Point A n h) (d : ℕ)
  (hd : h d = Nat.choose (n + d) n)

include hd in
private theorem eq_zero_of_mem_of_lt (q : MvPolynomial (Fin (n + 1)) A) (hqI : q ∈ P.I) (hq :
  q.IsHomogeneous d) : q = 0 := by
  haveI := P.projective_piece d
  haveI := P.finite_piece d
  haveI := finite_homogeneousSubmodule (n := n) A d
  haveI := free_homogeneousSubmodule (n := n) A d
  let Kd : Submodule A ↥(homogeneousSubmodule (Fin (n + 1)) A d) :=
    Submodule.comap (homogeneousSubmodule (Fin (n + 1)) A d).subtype (P.I.restrictScalars A)
  obtain ⟨E, hE⟩ := exists_equiv_prod_ker (Kd.mkQ) (Submodule.mkQ_surjective _)

  haveI : Module.Finite A (LinearMap.ker Kd.mkQ) :=
    Module.Finite.of_surjective ((LinearMap.snd A _ _).comp E.toLinearMap) fun k => ⟨E.symm (0, k),
      by simp⟩
  haveI : Module.Projective A (LinearMap.ker Kd.mkQ) :=
    Module.Projective.of_split (E.symm.toLinearMap.comp (LinearMap.inr A _ _))
      ((LinearMap.snd A _ _).comp E.toLinearMap) (by ext x; simp)
  have hrank : Module.rankAtStalk (R := A) (LinearMap.ker Kd.mkQ) = 0 := by
    funext p
    have h1 := congrFun (Module.rankAtStalk_eq_of_equiv
      (N := (↥(homogeneousSubmodule (Fin (n + 1)) A d) ⧸ Kd) × ↥(LinearMap.ker Kd.mkQ)) E) p
    rw [Module.rankAtStalk_prod, Pi.add_apply, Module.rankAtStalk_eq_finrank_of_free,
      finrank_homogeneousSubmodule A d] at h1
    have h2 : Module.rankAtStalk (↥(homogeneousSubmodule (Fin (n + 1)) A d) ⧸ Kd) p = (n +
      d).choose n :=
      (P.rankAtStalk_piece d p).trans hd
    erw [h2] at h1
    simp only [Pi.natCast_apply, Nat.cast_id] at h1
    simp only [Pi.zero_apply]
    omega
  have hsub : Subsingleton (LinearMap.ker Kd.mkQ) := Module.rankAtStalk_eq_zero_iff_subsingleton.mp
    hrank
  have hmem : (⟨q, hq⟩ : ↥(homogeneousSubmodule (Fin (n + 1)) A d)) ∈ LinearMap.ker Kd.mkQ := by
    rw [Submodule.ker_mkQ]
    simpa [Kd] using hqI
  have := congrArg (fun x : LinearMap.ker Kd.mkQ => ((x : ↥(homogeneousSubmodule (Fin (n + 1)) A
    d)) :
    MvPolynomial (Fin (n + 1)) A)) (Subsingleton.elim (⟨_, hmem⟩ : LinearMap.ker Kd.mkQ) 0)
  simpa using this

end Low

end HilbGenH2c

/-- A Hilbert-functor ideal is generated by its degree-`m` homogeneous
elements, provided the Hilbert function agrees with the polynomial-ring
growth `Nat.choose (n + d) n` below `m` and no field-valued homogeneous
ideal generated in degree `e ≥ m` can have its degree-`e + 1` piece grow
past `h (e + 1)` once its degree-`e` piece has size `h e`. -/
public theorem Point.I_eq_span_of_forall_finrank_piece_succ_le
    (n m : ℕ) (h : ℕ → ℕ) (h₁ : ∀ d, d < m → h d = Nat.choose (n + d) n)
    (h₂ : ∀ e, m ≤ e → ∀ (K : Type u) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) →
      Module.finrank K (piece J e) = h e → Module.finrank K (piece J (e + 1)) ≤ h (e + 1))
    (A : Type u) [CommRing A] (P : Point A n h) :
    P.I = Ideal.span {p | p ∈ P.I ∧ p.IsHomogeneous m} := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · haveI : Subsingleton (MvPolynomial (Fin (n + 1)) A) := inferInstance
    exact Subsingleton.elim _ _
  refine le_antisymm ?_ (Ideal.span_le.mpr fun _ hp => hp.1)
  have hgood : ∀ d, ∀ q ∈ P.I, q.IsHomogeneous d →
      q ∈ Ideal.span {p | p ∈ P.I ∧ p.IsHomogeneous m} := by
    intro d
    by_cases hdm : d < m
    · intro q hqI hq
      rw [HilbGenH2c.eq_zero_of_mem_of_lt h P d (h₁ d hdm) q hqI hq]
      exact Ideal.zero_mem _
    · have hmd : m ≤ d := not_lt.mp hdm
      induction d, hmd using Nat.le_induction with
      | base => exact fun q hqI hq => Ideal.subset_span ⟨hqI, hq⟩
      | succ e hme ih =>
        intro q hqI hq
        have hqJ := HilbGenH2c.mem_J'_of_mem h P e (h₂ e hme) q hqI hq
        refine Ideal.span_le.mpr ?_ hqJ
        exact fun p hp => ih (by omega) p hp.1 hp.2
  intro p hp
  rw [← sum_homogeneousComponent p]
  exact Ideal.sum_mem _ fun d _ => hgood d _ (P.homogeneous p hp d)
    (homogeneousComponent_isHomogeneous d p)

end HilbertFunctor
end AlgebraicGeometry
