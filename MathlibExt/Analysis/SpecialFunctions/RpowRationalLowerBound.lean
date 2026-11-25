/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A rational lower bound for a positive real root

`one_add_mul_rpow_inv_gt` bounds the positive `m`th root of `1 + m * x` from below
by showing that the difference of the two logarithms increases from zero.
-/

namespace MetaMathlibExt

/-- **A rational lower bound for $(1 + mx)^{1/m}$.** For every natural number $m \ge 2$ and every
real $x > 0$,

$$\frac{2 + (m + 1)x}{2 + (m - 1)x} < (1 + mx)^{1/m}.$$

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Lemma 3 (`integers-2026-A92-lem-3`). -/
public theorem one_add_mul_rpow_inv_gt {m : ℕ} (hm : 2 ≤ m) {x : ℝ} (hx : 0 < x) :
    (2 + (m + 1) * x) / (2 + (m - 1) * x) < (1 + m * x) ^ (1 / (m : ℝ)) := by
  set a := (m : ℝ)
  have ha : 1 < a := Nat.one_lt_cast.mpr hm
  have ha₀ : 0 < a := lt_trans zero_lt_one ha
  have hsub : 0 < a - 1 := sub_pos.mpr ha
  let F (t : ℝ) := 1 / a * Real.log (1 + a * t) -
    (Real.log (2 + (a + 1) * t) - Real.log (2 + (a - 1) * t))
  have hderiv (t : ℝ) (ht : 0 ≤ t) : HasDerivAt F
      ((a - 1) * (a + 1) * t ^ 2 /
        ((1 + a * t) * (2 + (a + 1) * t) * (2 + (a - 1) * t))) t := by
    have hlog (b c : ℝ) (h : 0 < b + c * t) :
        HasDerivAt (fun s => Real.log (b + c * s)) (c / (b + c * t)) t :=
      ((hasDerivAt_const_mul c).const_add b).log h.ne'
    have h₁ : 0 < 1 + a * t := by positivity
    have h₂ : 0 < 2 + (a + 1) * t := by positivity
    have h₃ : 0 < 2 + (a - 1) * t := by positivity
    apply (((hlog _ _ h₁).const_mul (1 / a)).sub ((hlog _ _ h₂).sub (hlog _ _ h₃))).congr_deriv
    field_simp
    ring
  have hmono : StrictMonoOn F (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · exact fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici, Set.mem_Ioi] at ht
      rw [(hderiv t ht.le).deriv]
      positivity
  have hpos : 0 < F x := by simpa [F] using hmono (Set.mem_Ici.mpr le_rfl) hx.le hx
  apply (Real.log_lt_log_iff (by positivity) (Real.rpow_pos_of_pos (by positivity) _)).mp
  rw [Real.log_div (by positivity) (by positivity), Real.log_rpow (by positivity)]
  exact sub_pos.mp hpos

end MetaMathlibExt
