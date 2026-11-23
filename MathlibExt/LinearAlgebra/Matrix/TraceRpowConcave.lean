/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-!
# Concavity of `A ↦ tr (K* A^q K)`: the one-variable cases of Lieb's concavity theorem

Lieb's concavity theorem (E. A. Carlen, *Trace inequalities and quantum entropy: an introductory
course*, lecture-notes draft of May 3, 2009, Theorem 6.1) asserts that
`(A, B) ↦ tr (K* A^q K B^r)` is jointly concave on pairs of positive-definite matrices when
`q, r ≥ 0` and `q + r ≤ 1`. For square `K` it is proved in
`PhyslibExt.QuantumInfo.LiebConcavity.lieb_concavity_trace_rpow`, from Physlib for `q, r > 0` and
from this file for the boundary cases.

This file proves the two degenerate cases where one exponent vanishes, `r = 0` and `q = 0`.
There the map depends on one matrix only, and its concavity follows from the operator concavity of
`t ↦ t ^ q` for `0 ≤ q ≤ 1` (Carlen, Theorem 2.6; Mathlib's `CFC.concaveOn_rpow`) composed with the
monotone linear functional `X ↦ re tr (K* X K)`. The joint concavity for `q, r > 0` is the real
content of Lieb's theorem; it is not proved here.
-/

@[expose] public section

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace MathlibExt.LinearAlgebra.Matrix.TraceRpowConcave

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
/-- `X ↦ re tr (K* X K)` is monotone for the Loewner order. -/
private lemma re_trace_conj_mono (K : Matrix m n ℂ) {X Y : Matrix m m ℂ} (h : X ≤ Y) :
    RCLike.re (K.conjTranspose * X * K).trace ≤ RCLike.re (K.conjTranspose * Y * K).trace := by
  rw [Matrix.le_iff] at h
  have h' := (h.conjTranspose_mul_mul_same K).trace_nonneg
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub] at h'
  have := (RCLike.nonneg_iff.mp h').1
  rw [map_sub] at this
  linarith

omit [DecidableEq n] in
/-- **Concavity of `A ↦ tr (K* A^q K)`.** For a complex `m × n` matrix `K` and `0 ≤ q ≤ 1`, the map
`A ↦ re tr (K* A^q K)` is concave on positive-semidefinite `m × m` matrices, where
`A^q = cfc (· ^ q) A`. It follows from the operator concavity of `t ↦ t ^ q` (E. A. Carlen,
*Trace inequalities and quantum entropy: an introductory course*, lecture-notes draft of May 3,
2009, Theorem 2.6; Mathlib's `CFC.concaveOn_rpow`) and is the one-variable shadow of Lieb's
concavity theorem (Carlen, Theorem 6.1). -/
theorem concaveOn_re_trace_conj_rpow (K : Matrix m n ℂ) {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ConcaveOn ℝ {A : Matrix m m ℂ | A.PosSemidef}
      (fun A => RCLike.re (K.conjTranspose * cfc (· ^ q : ℝ → ℝ) A * K).trace) := by
  have hset : {A : Matrix m m ℂ | A.PosSemidef} = Set.Ici 0 := by
    ext A; simp [Matrix.nonneg_iff_posSemidef]
  have hc := CFC.concaveOn_rpow (A := Matrix m m ℂ) ⟨hq₀, hq₁⟩
  rw [hset]
  refine ⟨convex_Ici 0, fun A hA B hB a b ha hb hab => ?_⟩
  have hAB : (0 : Matrix m m ℂ) ≤ a • A + b • B :=
    add_nonneg (smul_nonneg ha hA) (smul_nonneg hb hB)
  have key := re_trace_conj_mono K (hc.2 hA hB ha hb hab)
  simp only at key
  rw [CFC.rpow_eq_cfc_real hAB, CFC.rpow_eq_cfc_real hA, CFC.rpow_eq_cfc_real hB] at key
  refine le_trans (le_of_eq ?_) key
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_add,
    Matrix.trace_smul, map_add, smul_eq_mul]
  simp

omit [Fintype m] [DecidableEq m] in
/-- Positive-definite matrices form a convex set. -/
private lemma convex_posDef : Convex ℝ {A : Matrix m m ℂ | A.PosDef} := by
  intro A hA B hB a b ha hb hab
  rcases ha.eq_or_lt with rfl | ha'
  · simp only [zero_add] at hab
    simpa [hab] using hB
  · exact (hA.smul (by exact_mod_cast ha')).add_posSemidef
      (hB.posSemidef.smul (by exact_mod_cast hb))

/-- **Lieb's concavity theorem, case `r = 0`.** For a complex `m × n` matrix `K` and
`0 ≤ q ≤ 1`, the map `(A, B) ↦ re tr (K* A^q K B^0)` is jointly concave on pairs of
positive-definite matrices. This
is the instance `r = 0` of Lieb's concavity theorem (E. A. Carlen, *Trace inequalities and quantum
entropy: an introductory course*, lecture-notes draft of May 3, 2009, Theorem 6.1), stated in the
same form as the joint statement
`PhyslibExt.QuantumInfo.LiebConcavity.lieb_concavity_trace_rpow`; since `B^0 = 1`
it reduces to the concavity of `A ↦ re tr (K* A^q K)`. -/
theorem lieb_concavity_trace_rpow_of_right_eq_zero (K : Matrix m n ℂ) {q : ℝ} (hq₀ : 0 ≤ q)
    (hq₁ : q ≤ 1) :
    ConcaveOn ℝ {p : Matrix m m ℂ × Matrix n n ℂ | p.1.PosDef ∧ p.2.PosDef}
      (fun p => RCLike.re
        (K.conjTranspose * cfc (· ^ q : ℝ → ℝ) p.1 * K * cfc (· ^ (0 : ℝ) : ℝ → ℝ) p.2).trace) := by
  have hc := concaveOn_re_trace_conj_rpow K hq₀ hq₁
  refine ⟨?_, fun x hx y hy a b ha hb hab => ?_⟩
  · intro x hx y hy a b ha hb hab
    exact ⟨convex_posDef hx.1 hy.1 ha hb hab, convex_posDef hx.2 hy.2 ha hb hab⟩
  · have h1 : ∀ B : Matrix n n ℂ, B.PosDef → cfc (· ^ (0 : ℝ) : ℝ → ℝ) B = 1 := fun B hB => by
      simp only [Real.rpow_zero]
      exact cfc_const_one ℝ B (ha := hB.isHermitian)
    have hz : (a • x + b • y).2.PosDef := convex_posDef hx.2 hy.2 ha hb hab
    beta_reduce
    rw [h1 _ hx.2, h1 _ hy.2, h1 _ hz]
    simp only [Matrix.mul_one, Prod.fst_add, Prod.smul_fst]
    exact hc.2 hx.1.posSemidef hy.1.posSemidef ha hb hab

/-- **Lieb's concavity theorem, case `q = 0`.** For a complex `m × n` matrix `K` and
`0 ≤ r ≤ 1`, the map `(A, B) ↦ re tr (K* A^0 K B^r)` is jointly concave on pairs of
positive-definite matrices. This
is the instance `q = 0` of Lieb's concavity theorem (E. A. Carlen, *Trace inequalities and quantum
entropy: an introductory course*, lecture-notes draft of May 3, 2009, Theorem 6.1), in the form of
the joint statement `PhyslibExt.QuantumInfo.LiebConcavity.lieb_concavity_trace_rpow`; since
`A^0 = 1` and `tr (K* K B^r) = tr (K B^r K*)` it reduces to the concavity of
`B ↦ re tr (K B^r K*)`. -/
theorem lieb_concavity_trace_rpow_of_left_eq_zero (K : Matrix m n ℂ) {r : ℝ} (hr₀ : 0 ≤ r)
    (hr₁ : r ≤ 1) :
    ConcaveOn ℝ {p : Matrix m m ℂ × Matrix n n ℂ | p.1.PosDef ∧ p.2.PosDef}
      (fun p => RCLike.re
        (K.conjTranspose * cfc (· ^ (0 : ℝ) : ℝ → ℝ) p.1 * K * cfc (· ^ r : ℝ → ℝ) p.2).trace) := by
  have hc := concaveOn_re_trace_conj_rpow K.conjTranspose hr₀ hr₁
  have hcyc : ∀ B : Matrix n n ℂ, (K.conjTranspose * K * B).trace =
      (K.conjTranspose.conjTranspose * B * K.conjTranspose).trace := fun B => by
    rw [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, Matrix.trace_mul_comm,
      Matrix.mul_assoc]
  refine ⟨?_, fun x hx y hy a b ha hb hab => ?_⟩
  · intro x hx y hy a b ha hb hab
    exact ⟨convex_posDef hx.1 hy.1 ha hb hab, convex_posDef hx.2 hy.2 ha hb hab⟩
  · have h1 : ∀ A : Matrix m m ℂ, A.PosDef → cfc (· ^ (0 : ℝ) : ℝ → ℝ) A = 1 := fun A hA => by
      simp only [Real.rpow_zero]
      exact cfc_const_one ℝ A (ha := hA.isHermitian)
    have hz : (a • x + b • y).1.PosDef := convex_posDef hx.1 hy.1 ha hb hab
    beta_reduce
    rw [h1 _ hx.1, h1 _ hy.1, h1 _ hz]
    simp only [Matrix.mul_one, hcyc, Prod.snd_add, Prod.smul_snd]
    exact hc.2 hx.2.posSemidef hy.2.posSemidef ha hb hab

end MathlibExt.LinearAlgebra.Matrix.TraceRpowConcave
