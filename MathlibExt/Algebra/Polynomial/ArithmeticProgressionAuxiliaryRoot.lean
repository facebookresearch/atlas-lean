/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The positive root of the arithmetic-progression auxiliary equation

On the positive real axis, dividing equation (3) by the power `x ^ (m + 1)` gives a strictly
increasing function with the same zeros.
-/

open Filter Set

namespace MetaMathlibExt

/-- **The auxiliary equation has a unique positive root, which exceeds $1$.** Let $m \ge 2$ and
let $a$, $d$ be integers with $0 < d \le a$. Then the equation
$a x^{m+2} + (a - d) x^{m+1} - (a + (m + 1)d) x - (a + md) = 0$ has exactly one positive real
solution, and every positive real solution $x$ satisfies $x > 1$.

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Proposition 1
(`integers-2026-A92-prop-1`). -/
public theorem arithProgPoly_eq3_existsUnique_pos {m a d : ℕ} (hm : 2 ≤ m) (hd : 0 < d)
    (hda : d ≤ a) :
    (∃! x : ℝ, 0 < x ∧ (a : ℝ) * x ^ (m + 2) + ((a : ℝ) - d) * x ^ (m + 1) -
      ((a : ℝ) + (m + 1) * d) * x - ((a : ℝ) + m * d) = 0) ∧
    ∀ x : ℝ, 0 < x → (a : ℝ) * x ^ (m + 2) + ((a : ℝ) - d) * x ^ (m + 1) -
      ((a : ℝ) + (m + 1) * d) * x - ((a : ℝ) + m * d) = 0 → 1 < x := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have ha : (0 : ℝ) < a := by exact_mod_cast hd.trans_le hda
  let c : ℝ := a + (m + 1) * d
  let b : ℝ := a + m * d
  let f (x : ℝ) := a * x + ((a - d : ℝ) - (c / x ^ m + b / x ^ (m + 1)))
  have hroot (x : ℝ) (hx : 0 < x) :
      (a : ℝ) * x ^ (m + 2) + ((a : ℝ) - d) * x ^ (m + 1) -
        c * x - b = 0 ↔ f x = 0 := by
    have hid : (a : ℝ) * x ^ (m + 2) + ((a : ℝ) - d) * x ^ (m + 1) -
        c * x - b = f x * x ^ (m + 1) := by
      simp only [f, pow_succ]
      field_simp
      ring
    rw [hid, mul_eq_zero]
    simp [hx.ne']
  have hmono : StrictMonoOn f (Ioi 0) := by
    intro x hx y hy hxy
    change 0 < x at hx
    apply add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hxy ha)
    gcongr
  have hcont : ContinuousOn f (Ici 1) := by
    intro x hx
    have hx' : 0 < x := zero_lt_one.trans_le hx
    dsimp [f]
    fun_prop (disch := positivity)
  have htop : Tendsto f atTop atTop :=
    (tendsto_id.const_mul_atTop ha).atTop_add (tendsto_const_nhds.sub
      (((tendsto_pow_atTop (by omega : m ≠ 0)).const_div_atTop c).add
        ((tendsto_pow_atTop (Nat.succ_ne_zero m)).const_div_atTop b)))
  have hone : f 1 < 0 := by
    simp only [f, c, b, one_pow, div_one, mul_one]
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) m) hd'.le]
  obtain ⟨r, hr, hfr⟩ := intermediate_value_Ioi hcont htop hone
  have hrpos : 0 < r := zero_lt_one.trans hr
  have hu (x : ℝ) (hx : 0 < x) (hfx : f x = 0) : x = r :=
    hmono.injOn hx hrpos (hfx.trans hfr.symm)
  exact ⟨⟨r, ⟨hrpos, (hroot r hrpos).2 hfr⟩, fun x ⟨hx, heq⟩ ↦ hu x hx ((hroot x hx).1 heq)⟩,
    fun x hx heq ↦ hu x hx ((hroot x hx).1 heq) ▸ hr⟩

end MetaMathlibExt
