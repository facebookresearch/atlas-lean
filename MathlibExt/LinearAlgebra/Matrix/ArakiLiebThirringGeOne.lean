/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.ArakiLiebThirring
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# The Araki–Lieb–Thirring inequality

For positive-semidefinite matrices `A`, `B` and real `q ≥ 0`, `r ≥ 1`,
`tr (A^{1/2} B A^{1/2})^{rq} ≤ tr (A^{r/2} B^r A^{r/2})^q`, and the inequality reverses for
`0 ≤ r ≤ 1` (H. Araki, *On an inequality of Lieb and Thirring*, Lett. Math. Phys. 19 (1990)
167–170; stated as Theorem 1 of K. M. R. Audenaert, *On the Araki–Lieb–Thirring inequality*,
arXiv:math/0701129). The case `q = 1` is the Lieb–Thirring trace inequality
`tr (B^{1/2} A B^{1/2})^t ≤ tr (B^{t/2} A^t B^{t/2})` for `t ≥ 1` (E. H. Lieb and W. Thirring, in
*Studies in Mathematical Physics*, Princeton University Press, 1976, 269–303; E. A. Carlen, *Trace
inequalities and quantum entropy: an introductory course*, lecture-notes draft of May 3, 2009,
Theorem 7.4). Matrix powers are the continuous functional calculus `cfc (· ^ p)` of the real
power function. The reversed range is proved in the imported module.
-/

@[expose] public section

open scoped ComplexOrder

namespace MathlibExt.LinearAlgebra.Matrix.ArakiLiebThirringWanted

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Araki–Lieb–Thirring inequality.** For positive-semidefinite complex matrices `A` and `B`
and reals `q ≥ 0`, `r ≥ 1`,
`tr (A^{1/2} B A^{1/2})^{rq} ≤ tr (A^{r/2} B^r A^{r/2})^q`
(H. Araki, Lett. Math. Phys. 19 (1990) 167–170; K. M. R. Audenaert, arXiv:math/0701129,
Theorem 1, the case `r ≥ 1`). Both traces are real because both matrices are positive
semidefinite; the statement compares their real parts. -/
theorem araki_lieb_thirring {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {q r : ℝ} (hq : 0 ≤ q) (hr : 1 ≤ r) :
    RCLike.re (cfc (· ^ (r * q) : ℝ → ℝ)
        (cfc (· ^ (2⁻¹ : ℝ) : ℝ → ℝ) A * B * cfc (· ^ (2⁻¹ : ℝ) : ℝ → ℝ) A)).trace ≤
      RCLike.re (cfc (· ^ q : ℝ → ℝ)
        (cfc (· ^ (r / 2) : ℝ → ℝ) A * cfc (· ^ r : ℝ → ℝ) B *
          cfc (· ^ (r / 2) : ℝ → ℝ) A)).trace := by
  -- The matrix order is needed only by the proof, so the statement is elaborated without it.
  open scoped MatrixOrder in
  have hr₀ : 0 < r := zero_lt_one.trans_le hr
  -- Apply the reversed range to the powered matrices with exponents r⁻¹ and r * q.
  have h := araki_lieb_thirring_of_le_one (A := A ^ r) (B := B ^ r)
    (Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg)
    (Matrix.nonneg_iff_posSemidef.mp CFC.rpow_nonneg)
    (mul_nonneg hr₀.le hq) (inv_nonneg.mpr hr₀.le) (inv_le_one_of_one_le₀ hr)
  have power (M : Matrix n n ℂ) (hM : M.PosSemidef) (s : ℝ) (hs : 0 ≤ s) :
      cfc (· ^ s : ℝ → ℝ) (M ^ r) = M ^ (r * s) := by
    rw [← CFC.rpow_eq_cfc_real CFC.rpow_nonneg,
      CFC.rpow_rpow_of_exponent_nonneg M r s hr₀.le hs hM.nonneg]
  rw [power A hA (r⁻¹ / 2) (by positivity), power B hB r⁻¹ (by positivity),
    power A hA 2⁻¹ (by norm_num), ← mul_div_assoc, mul_inv_cancel₀ hr₀.ne',
    CFC.rpow_one B hB.nonneg, inv_mul_cancel_left₀ hr₀.ne'] at h
  simpa only [one_div, ← div_eq_mul_inv, CFC.rpow_eq_cfc_real hA.nonneg,
    CFC.rpow_eq_cfc_real hB.nonneg] using h

end MathlibExt.LinearAlgebra.Matrix.ArakiLiebThirringWanted
