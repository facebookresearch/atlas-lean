/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import MathlibExt.Analysis.Fourier.FiniteAbelianUncertainty

/-!
# A lower bound for twisted complete exponential sums

The twists are the Fourier coefficients of the unit-modulus function
`x ↦ e_p(f(x))` on `ZMod p`. By Parseval their mean squared norm is `p`.
-/

namespace MetaMathlibExt

open Complex Finset
open MathlibExt.Analysis.Fourier.FiniteAbelianDFTWanted
open MathlibExt.Analysis.Fourier.FiniteAbelianUncertainty

/-- The integers from `1` to `p` form a complete system of representatives modulo `p`. -/
private lemma sum_Icc_one_zmod {p : ℕ} [NeZero p] (F : ZMod p → ℂ) :
    ∑ x ∈ Icc 1 p, F x = ∑ x : ZMod p, F x := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne p)
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, Nat.add_sub_cancel,
    ← Fin.sum_univ_eq_sum_range]
  refine (sum_congr rfl fun (x : Fin (n + 1)) _ => ?_).trans
    (Equiv.sum_comp (Equiv.addLeft (1 : ZMod (n + 1))) F)
  rw [Nat.cast_add, Nat.cast_one]
  exact congrArg (fun z => F (1 + z)) (ZMod.natCast_zmod_val (n := n + 1) x)

/-- **Lower bound for the maximal twisted complete exponential sum.** Let $p$ be a prime, let $f$
be a polynomial with integer coefficients, and write $e_p(t) = e^{2\pi i t / p}$ for integers $t$.
Then
$$\max_{0 \le y \le p - 1} \left| \sum_{x=1}^{p} e_p(f(x) + yx) \right| \ge \sqrt{p}.$$

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Lemma 2.2 (`integers-2025-A48-lem-2-2`). -/
public theorem sqrt_le_sup_norm_completeSum (p : ℕ) (hp : p.Prime) (f : Polynomial ℤ) :
    Real.sqrt p ≤
      (((range p).sup fun y : ℕ =>
        ‖∑ x ∈ Icc 1 p,
          exp (2 * Real.pi * I * ((f.eval (x : ℤ) + y * x : ℤ) : ℂ) / p)‖₊ : NNReal) : ℝ) := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  let g (x : ZMod p) := ZMod.stdAddChar ((f.map (Int.castRingHom (ZMod p))).eval x)
  -- Parseval gives a Fourier coefficient with squared norm at least the mean.
  have hmean : (∑ _ψ : AddChar (ZMod p) ℂ, (p : ℝ)) =
      ∑ ψ : AddChar (ZMod p) ℂ, ‖dftFun g ψ‖ ^ 2 := by
    rw [sum_norm_sq_dftFun]
    simp [g, AddChar.norm_apply, ZMod.card]
  obtain ⟨ψ, _, hψ⟩ := exists_le_of_sum_le univ_nonempty hmean.le
  obtain ⟨y, rfl⟩ := AddChar.zmodAddEquiv.surjective ψ
  -- Express this coefficient using the representatives in the statement.
  let S (y : ℕ) := ∑ x ∈ Icc 1 p,
    exp (2 * Real.pi * I * ((f.eval (x : ℤ) + y * x : ℤ) : ℂ) / p)
  have hsum : dftFun g (AddChar.zmodAddEquiv y) = S y.val := by
    dsimp only [S]
    rw [dftFun, ← sum_Icc_one_zmod]
    apply sum_congr rfl
    intro x _
    change ZMod.stdAddChar (y * (x : ZMod p)) * g x = _
    rw [← ZMod.stdAddChar_coe (N := p), Int.cast_add, AddChar.map_add_eq_mul]
    simp [g, mul_comm]
  rw [hsum] at hψ
  exact (Real.sqrt_le_iff.mpr ⟨norm_nonneg _, hψ⟩).trans
    (NNReal.coe_le_coe.mpr (le_sup (f := fun k => ‖S k‖₊) (mem_range.mpr y.val_lt)))

end MetaMathlibExt
