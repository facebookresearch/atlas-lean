/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`QuantumInfo/ForMathlib/HermitianMat/Rpow.lean` (Physlib), for the compound-matrix
power calculation and the positive-definite approximation in the trace inequality.
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Alex Meiburg
-/

module

public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import QuantumInfo.ForMathlib.HermitianMat.Schatten

/-!
# The Araki–Lieb–Thirring inequality for exponents at most one

`araki_lieb_thirring_of_le_one` compares the traces of two powers of positive matrix
sandwiches. The proof applies Löwner–Heinz to each compound matrix to bound the products
of the largest singular values, then sums their positive powers by weak log-majorization.
-/

public section

namespace MathlibExt.LinearAlgebra.Matrix.ArakiLiebThirringWanted

open scoped ComplexOrder MatrixOrder
open HermitianMat

variable {n : Type*} [Fintype n] [DecidableEq n]

private lemma smul_rpow {A : HermitianMat n ℂ} (hA : 0 ≤ A) {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    (t • A) ^ r = t ^ r • (A ^ r) := by
  rw [← HermitianMat.cfc_const_mul_id (A := A) (r := t), rpow_eq_cfc, ← HermitianMat.cfc_comp,
    rpow_eq_cfc, ← HermitianMat.cfc_const_mul]
  exact cfc_congr_of_nonneg hA fun _ hx => Real.mul_rpow ht hx

private lemma conj_one_power {B : HermitianMat n ℂ} (hB : 0 ≤ B) {p : ℝ} (hp : p ≠ 0) :
    (1 : HermitianMat n ℂ).conj (B ^ p).mat = B ^ (p + p) := by
  ext1
  simp [mat_rpow_add hB (show p + p ≠ 0 by grind)]

/-- Conjugate the bound by the inverse of the outer factor, apply operator monotonicity,
then conjugate back by the powered outer factor. -/
private lemma sandwich_rpow_bound {A B : HermitianMat n ℂ} (hA : 0 ≤ A) (hB : B.mat.PosDef)
    {t r : ℝ} (ht : 0 ≤ t) (hr : 0 < r) (hr' : r ≤ 1) (h : A.conj B.mat ≤ t • 1) :
    (A ^ r).conj (B ^ r).mat ≤ t ^ r • 1 := by
  have hB₀ := zero_le_iff.mpr hB.posSemidef
  have hinv : (B ^ (-1 : ℝ)).mat * B.mat = 1 := by simpa using rpow_neg_mul_rpow_self hB 1
  have hscale (X : HermitianMat n ℂ) (M : Matrix n n ℂ) (c : ℝ) :
      (c • X).conj M = c • X.conj M := (conjLinear ℝ M).map_smul c X
  have hle := conj_mono (M := (B ^ (-1 : ℝ)).mat) h
  rw [conj_conj, hinv, conj_one, hscale, conj_one_power hB₀ (by norm_num)] at hle
  have hp := rpow_le_rpow_of_le hA hle hr hr'
  rw [smul_rpow (rpow_nonneg hB₀) ht, ← rpow_mul hB₀] at hp
  have hback := conj_mono (M := (B ^ r).mat) hp
  rw [hscale, show ((-1 : ℝ) + -1) * r = -r + -r by ring,
    ← conj_one_power hB₀ (neg_ne_zero.mpr hr.ne'), conj_conj,
    mul_eq_one_comm.mp (rpow_neg_mul_rpow_self hB r), conj_one] at hback
  exact hback

private noncomputable def factor (A B : HermitianMat n ℂ) : Matrix n n ℂ :=
  (A ^ (1 / 2 : ℝ)).mat * B.mat

private lemma top_singular_bound {A B : HermitianMat n ℂ} (hA : 0 ≤ A) (hB : B.mat.PosDef)
    {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1) (hn : 0 < Fintype.card n) :
    singularValuesSorted (factor (A ^ r) (B ^ r)) ⟨0, hn⟩ ≤
      singularValuesSorted (factor A B) ⟨0, hn⟩ ^ r := by
  let M := factor A B
  let N := factor (A ^ r) (B ^ r)
  let c := singularValuesSorted M ⟨0, hn⟩
  have hc : 0 ≤ c := singularValuesSorted_nonneg _ _
  have gram (X Y : HermitianMat n ℂ) (hX : 0 ≤ X) :
      (factor X Y).conjTranspose * factor X Y = (X.conj Y.mat).mat :=
    conjTranspose_half_mul_eq_conj hX
  have hM : M.conjTranspose * M ≤ c ^ 2 • (1 : Matrix n n ℂ) := by
    simpa using (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff
      (Matrix.isHermitian_mul_conjTranspose_self M.conjTranspose) (c ^ 2)).mp
        (eigenvalue_le_singularValuesSorted_sq M hn)
  have hconj : A.conj B.mat ≤ c ^ 2 • 1 := by
    change (A.conj B.mat).mat ≤ c ^ 2 • (1 : Matrix n n ℂ)
    rwa [← gram A B hA]
  have hN : N.conjTranspose * N ≤ (c ^ 2) ^ r • (1 : Matrix n n ℂ) := by
    rw [show N.conjTranspose * N = _ from gram (A ^ r) (B ^ r) (rpow_nonneg hA)]
    exact sandwich_rpow_bound hA hB (sq_nonneg c) hr hr' hconj
  change singularValuesSorted N ⟨0, hn⟩ ≤ c ^ r
  rw [singularValuesSorted_zero_eq_sup]
  refine Finset.sup'_le _ _ fun i _ => ?_
  apply (Real.sqrt_le_iff).mpr
  refine ⟨Real.rpow_nonneg hc _, ?_⟩
  have he := (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff
    (Matrix.isHermitian_mul_conjTranspose_self N.conjTranspose) ((c ^ 2) ^ r)).mpr
      (by simpa using hN) i
  convert he using 1
  rw [← Real.rpow_natCast (c ^ r) 2, ← Real.rpow_mul hc, mul_comm,
    Real.rpow_mul hc, Real.rpow_natCast]

open scoped AllOrdered

private lemma compound_rpow (A : HermitianMat n ℂ) (hA : 0 ≤ A) (k : ℕ) (r : ℝ) :
    compoundHermitian (A ^ r) k = (compoundHermitian A k) ^ r := by
  have hdiag (a : n → ℝ) :
      compoundHermitian (diagonal ℂ a) k =
        diagonal ℂ (fun S : {s : Finset n // s.card = k} =>
          ∏ i : Fin k, a (S.1.orderEmbOfFin S.2 i)) := by
    ext1
    simp [compoundHermitian, compoundMatrix_diagonal]
  obtain ⟨U, a, ha, h⟩ : ∃ U : Matrix.unitaryGroup n ℂ, ∃ a : n → ℝ,
      (∀ i, 0 ≤ a i) ∧ A = conj U.val (diagonal ℂ a) :=
    ⟨_, _, (zero_le_iff.mp hA).eigenvalues_nonneg, eq_conj_diagonal A⟩
  rw [h, rpow_conj_unitary, compoundHermitian_conj, compoundHermitian_conj,
    rpow_diagonal, hdiag, hdiag]
  change conj (compoundUnitary U k).val _ = (conj (compoundUnitary U k).val _) ^ r
  rw [rpow_conj_unitary, rpow_diagonal]
  congr 2
  funext S
  exact Real.finsetProd_rpow _ _ (fun _ _ => ha _) _

private lemma compound_posDef {B : HermitianMat n ℂ} (hB : B.mat.PosDef) (k : ℕ) :
    (compoundHermitian B k).mat.PosDef := by
  rw [(compoundHermitian B k).H.posDef_iff_eigenvalues_pos]
  obtain ⟨σ, hσ⟩ := compoundHermitian_eigenvalues B k
  intro S
  obtain ⟨T, rfl⟩ := σ.surjective S
  rw [show (compoundHermitian B k).H.eigenvalues (σ T) = _ from congrFun hσ T]
  exact Finset.prod_pos fun _ _ => hB.eigenvalues_pos _

private lemma compound_factor (A B : HermitianMat n ℂ) (hA : 0 ≤ A) (k : ℕ) :
    compoundMatrix (factor A B) k = factor (compoundHermitian A k) (compoundHermitian B k) := by
  rw [factor, compoundMatrix_mul]
  change (compoundHermitian (A ^ (1 / 2 : ℝ)) k).mat * _ = _
  rw [compound_rpow A hA]
  rfl

/-- The product of the first `k` singular values is the largest singular value
of the `k`th compound matrix. -/
private lemma leading_product_bound {A B : HermitianMat n ℂ} (hA : 0 ≤ A) (hB : B.mat.PosDef)
    {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1) (k : ℕ) (hk : k ≤ Fintype.card n) :
    ∏ i : Fin k, singularValuesSorted (factor (A ^ r) (B ^ r)) ⟨i.val, by omega⟩ ≤
      ∏ i : Fin k, singularValuesSorted (factor A B) ⟨i.val, by omega⟩ ^ r := by
  rw [Real.finsetProd_rpow _ _ (fun _ _ => singularValuesSorted_nonneg _ _),
    prod_singularValuesSorted_eq_compoundSV _ k hk, prod_singularValuesSorted_eq_compoundSV _ k hk,
    compound_factor _ _ (rpow_nonneg hA), compound_factor _ _ hA,
    compound_rpow A hA, compound_rpow B (zero_le_iff.mpr hB.posSemidef)]
  exact top_singular_bound (compoundHermitian_nonneg A hA k) (compound_posDef hB k) hr hr'
    (compound_card_pos k hk)

private lemma trace_power_eq_sum {A B : HermitianMat n ℂ} (hA : 0 ≤ A) {q : ℝ} (hq : 0 < q) :
    ((A.conj B.mat) ^ q).trace = ∑ i, singularValuesSorted (factor A B) i ^ (2 * q) := by
  rw [← schattenNorm_half_mul_rpow_eq_trace_conj hA hq, schattenNorm_rpow_eq_sum_sorted _ (by
    positivity)]
  rfl

private lemma trace_power_le_posDef {A B : HermitianMat n ℂ} (hA : 0 ≤ A) (hB : B.mat.PosDef)
    {r q : ℝ} (hr : 0 < r) (hr' : r ≤ 1) (hq : 0 < q) :
    (((A ^ r).conj (B ^ r).mat) ^ q).trace ≤ ((A.conj B.mat) ^ (r * q)).trace := by
  rw [trace_power_eq_sum (rpow_nonneg hA) hq, trace_power_eq_sum hA (mul_pos hr hq)]
  have hsum := weak_log_maj_sum_rpow_le
    (singularValuesSorted_nonneg (factor (A ^ r) (B ^ r)))
    (fun i => Real.rpow_nonneg (singularValuesSorted_nonneg (factor A B) i) r)
    (singularValuesSorted_antitone _)
    (rpow_antitone_of_nonneg_antitone (singularValuesSorted_antitone _)
      (singularValuesSorted_nonneg _) hr)
    (leading_product_bound hA hB hr hr') (show 0 < 2 * q by positivity)
  simpa only [← Real.rpow_mul (singularValuesSorted_nonneg _ _),
    show r * (2 * q) = 2 * (r * q) by ring] using hsum

open Filter Topology in
private lemma trace_power_le {A B : HermitianMat n ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    {r q : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) (hq : 0 ≤ q) :
    (((A ^ r).conj (B ^ r).mat) ^ q).trace ≤ ((A.conj B.mat) ^ (r * q)).trace := by
  obtain rfl | hr := hr₀.eq_or_lt
  · simp
  obtain rfl | hq' := hq.eq_or_lt
  · simp
  -- Approximate only the outer factor, where the order argument uses an inverse.
  let shift (ε : ℝ) := B + ε • 1
  have hshift : Continuous shift := by dsimp [shift]; fun_prop
  have hleft : Continuous (fun ε => (((A ^ r).conj (shift ε ^ r).mat) ^ q).trace) :=
    continuous_trace.comp ((rpow_const_continuous hq).comp ((continuous_conj _).comp
      (continuous_mat.comp ((rpow_const_continuous hr.le).comp hshift))))
  have hright : Continuous (fun ε => ((A.conj (shift ε).mat) ^ (r * q)).trace) :=
    continuous_trace.comp ((rpow_const_continuous (mul_nonneg hr.le hq)).comp
      ((continuous_conj _).comp (continuous_mat.comp hshift)))
  have hevent : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (((A ^ r).conj (shift ε ^ r).mat) ^ q).trace ≤
        ((A.conj (shift ε).mat) ^ (r * q)).trace := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    apply trace_power_le_posDef hA _ hr hr₁ hq'
    simpa [shift, add_comm] using
      (Matrix.PosDef.one.smul (show 0 < ε from hε)).add_posSemidef (zero_le_iff.mp hB)
  simpa [shift] using le_of_tendsto_of_tendsto hleft.continuousWithinAt.tendsto
    hright.continuousWithinAt.tendsto hevent

/-- **Araki–Lieb–Thirring inequality, reversed range.** For positive-semidefinite complex
matrices `A` and `B` and reals `q ≥ 0`, `0 ≤ r ≤ 1`,
`tr (A^{r/2} B^r A^{r/2})^q ≤ tr (A^{1/2} B A^{1/2})^{rq}`
(H. Araki, Lett. Math. Phys. 19 (1990) 167–170; K. M. R. Audenaert, arXiv:math/0701129,
Theorem 1, the case `0 ≤ r ≤ 1`). -/
theorem araki_lieb_thirring_of_le_one {A B : Matrix n n ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) {q r : ℝ} (hq : 0 ≤ q) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    RCLike.re (cfc (· ^ q : ℝ → ℝ)
        (cfc (· ^ (r / 2) : ℝ → ℝ) A * cfc (· ^ r : ℝ → ℝ) B *
          cfc (· ^ (r / 2) : ℝ → ℝ) A)).trace ≤
      RCLike.re (cfc (· ^ (r * q) : ℝ → ℝ)
        (cfc (· ^ (2⁻¹ : ℝ) : ℝ → ℝ) A * B * cfc (· ^ (2⁻¹ : ℝ) : ℝ → ℝ) A)).trace := by
  let X : HermitianMat n ℂ := ⟨A, hA.isHermitian⟩
  let Y : HermitianMat n ℂ := ⟨B, hB.isHermitian⟩
  have hX : 0 ≤ X := zero_le_iff.mpr hA
  have hY : 0 ≤ Y := zero_le_iff.mpr hB
  have h := trace_power_le hY (rpow_nonneg hX (p := (2⁻¹ : ℝ))) hr₀ hr₁ hq
  rw [← rpow_mul hX, show (2⁻¹ : ℝ) * r = r / 2 by ring] at h
  have power_mat (W : HermitianMat n ℂ) (s : ℝ) :
      (W ^ s).mat = cfc (· ^ s : ℝ → ℝ) W.mat := W.mat_cfc _
  have bridge (U V : HermitianMat n ℂ) (s : ℝ) :
      ((U.conj V.mat) ^ s).trace = RCLike.re (cfc (· ^ s : ℝ → ℝ)
        (V.mat * U.mat * V.mat)).trace := by
    rw [trace_eq_re_trace, power_mat, conj_apply_mat, conjTranspose_mat]
  rw [bridge, bridge] at h
  simpa only [power_mat, show X.mat = A from rfl, show Y.mat = B from rfl] using h

end MathlibExt.LinearAlgebra.Matrix.ArakiLiebThirringWanted
