/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Singleton values of the cotangent ceiling sequence

`MetaMathlibExt.ceil_cot_singleton_iff` characterizes the values attained once by the
ceilings of `cot (π / (2 * m))` in terms of the two neighboring values.
-/

namespace MetaMathlibExt

open Real

/-- The chord of sine from zero to `π / 4`, evaluated at `π / (2 * x)`. -/
private theorem sqrt_two_div_le_sin {x : ℝ} (hx : 2 ≤ x) :
    √2 / x ≤ sin (π / (2 * x)) := by
  have hx₀ : 0 < x := by linarith
  have ht : 2 / x ≤ 1 := (div_le_one hx₀).2 hx
  have chord := strictConcaveOn_sin_Icc.concaveOn.2 ⟨le_rfl, pi_pos.le⟩
    (y := π / 4) ⟨by positivity, by linarith [pi_pos]⟩
    (sub_nonneg.mpr ht) (show 0 ≤ 2 / x by positivity) (sub_add_cancel _ _)
  simp only [smul_eq_mul, sin_zero, mul_zero, zero_add, sin_pi_div_four] at chord
  convert chord using 1 <;> ring_nf

/-- From the second index onwards the cotangents increase by at most one. -/
private theorem cot_step_bounds {x : ℝ} (hx : 2 ≤ x) :
    cot (π / (2 * (x + 1))) - cot (π / (2 * x)) ∈ Set.Icc 0 1 := by
  let a := π / (2 * x)
  let b := π / (2 * (x + 1))
  have hx₀ : 0 < x := by linarith
  have hx₁ : 0 < x + 1 := by positivity
  have hdiff : a - b = (π / 2) / (x * (x + 1)) := by
    dsimp [a, b]
    field_simp
    ring
  have hab : 0 ≤ a - b := hdiff ▸ by positivity
  have ha : a ≤ π := (div_le_iff₀ (by positivity : 0 < 2 * x)).2
    (le_mul_of_one_le_right pi_pos.le (by linarith))
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hsa : √2 / x ≤ sin a := sqrt_two_div_le_sin hx
  have hsb : √2 / (x + 1) ≤ sin b := sqrt_two_div_le_sin (by linarith)
  have hsa₀ : 0 < sin a := lt_of_lt_of_le (by positivity) hsa
  have hsb₀ : 0 < sin b := lt_of_lt_of_le (by positivity) hsb
  have hcot : cot b - cot a = sin (a - b) / (sin a * sin b) := by
    rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin, sin_sub]
    field_simp
  change cot b - cot a ∈ Set.Icc 0 1
  rw [hcot]
  refine ⟨div_nonneg (sin_nonneg_of_nonneg_of_le_pi hab (by linarith)) (by positivity), ?_⟩
  apply (div_le_one (mul_pos hsa₀ hsb₀)).2
  calc
    sin (a - b) ≤ a - b := sin_le hab
    _ = (π / 2) / (x * (x + 1)) := hdiff
    _ ≤ 2 / (x * (x + 1)) := by gcongr; linarith [pi_le_four]
    _ = √2 / x * (√2 / (x + 1)) := by
      rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ sin a * sin b := mul_le_mul hsa hsb (by positivity) hsa₀.le

private theorem ceil_cot_step_bounds (n : ℕ) (hn : 1 ≤ n) :
    let g : ℕ → ℤ := fun m => ⌈Real.cot (Real.pi / (2 * m))⌉
    g n ≤ g (n + 1) ∧ g (n + 1) ≤ g n + 1 := by
  dsimp only
  rcases eq_or_lt_of_le hn with rfl | hn
  · norm_num [cot_eq_cos_div_sin, sin_pi_div_two, cos_pi_div_two,
      sin_pi_div_four, cos_pi_div_four]
  · obtain ⟨hlo, hhi⟩ := cot_step_bounds (x := n) (by exact_mod_cast hn)
    rw [Nat.cast_add, Nat.cast_one, ← Int.ceil_add_one]
    exact ⟨Int.ceil_mono (sub_nonneg.mp hlo), Int.ceil_mono (sub_le_iff_le_add'.mp hhi)⟩

set_option linter.unusedVariables false in
/-- **Values taken once by the ceiling of $\cot(\pi/(2m))$.** For $m \ge 1$ let
$g(m) = \lceil \cot(\pi/(2m)) \rceil$. Let $r \ge 1$ and $m \ge 2$ be integers. Then $m$ is the
only integer $m' \ge 1$ with $g(m') = r$ if and only if $g(m-1) = r - 1$, $g(m) = r$ and
$g(m+1) = r + 1$.

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Lemma 11 (`jis-2026-26.1.8-lem-11`). -/
public theorem ceil_cot_singleton_iff (r m : ℕ) (hr : 1 ≤ r) (hm : 2 ≤ m) :
    let g : ℕ → ℤ := fun m => ⌈Real.cot (Real.pi / (2 * m))⌉
    {m' : ℕ | 1 ≤ m' ∧ g m' = r} = {m} ↔
      g (m - 1) = (r : ℤ) - 1 ∧ g m = r ∧ g (m + 1) = (r : ℤ) + 1 := by
  intro g
  have step (n : ℕ) (hn : 1 ≤ n) : g n ≤ g (n + 1) ∧ g (n + 1) ≤ g n + 1 :=
    ceil_cot_step_bounds n hn
  have mono : MonotoneOn g (Set.Ici 1) := monotoneOn_nat_Ici_of_le_succ fun n hn => (step n hn).1
  have hprev : 1 ≤ m - 1 := by omega
  rw [Set.eq_singleton_iff_unique_mem]
  constructor
  · rintro ⟨⟨_, hgm⟩, unique⟩
    have hp := step (m - 1) hprev
    rw [Nat.sub_add_cancel (by omega : 1 ≤ m)] at hp
    have hs := step m (by omega)
    have hpne : g (m - 1) ≠ r := fun h => by
      have := unique (m - 1) ⟨hprev, h⟩
      omega
    have hsne : g (m + 1) ≠ r := fun h => by
      have := unique (m + 1) ⟨by omega, h⟩
      omega
    exact ⟨by omega, hgm, by omega⟩
  · rintro ⟨hp, hgm, hs⟩
    refine ⟨⟨by omega, hgm⟩, ?_⟩
    rintro n ⟨hn, heq⟩
    rcases lt_trichotomy n m with hlt | rfl | hgt
    · have := mono hn hprev (show n ≤ m - 1 by omega)
      omega
    · rfl
    · have := mono (show 1 ≤ m + 1 by omega) hn (show m + 1 ≤ n by omega)
      omega

end MetaMathlibExt
