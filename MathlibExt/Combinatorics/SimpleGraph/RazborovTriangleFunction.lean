/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Razborov's triangle density function

The function `g₃` giving the asymptotically minimal triangle density of a graph with edge
density `a`, conjectured by Lovász and Simonovits and determined by Razborov (2008). For
`a ∈ (1 - 1/t, 1 - 1/(t+1)]` with `t ≥ 1` it is the triangle density of the complete
`(t + 1)`-partite graph whose `t` largest parts have relative size `c` and whose edge density is
`a`:

`c = (t + √(t (t - a (t + 1)))) / (t (t + 1))`, `h(a) = 6 (C(t, 3) c³ + C(t, 2) c² (1 - t c))`

(Pikhurko and Razborov, *Asymptotic structure of graphs with the minimum number of triangles*,
Combin. Probab. Comput. 26 (2017), arXiv:1204.2846v2, equations (1)-(4)). At the endpoints
`a = 1 - 1/(t+1)` the extremal graph is the balanced complete `(t + 1)`-partite graph and
`h(a) = t (t - 1) / (t + 1) ^ 2` (`razborovTriangleDensity_one_sub_inv`).

The lower bound `g₃(a) ≥ h(a)` is Razborov's theorem, recorded in
`WantedExt/GraphTheory/RazborovTriangleDensityWanted`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.RazborovTriangleFunction

/-- **Razborov's triangle density function.** The function `h` on edge densities `a` with
`h(a) = 0` for `a ≤ 1/2`, `h(a) = 1` for `a ≥ 1`, and, for `1 - 1/t < a ≤ 1 - 1/(t+1)` with
`t ≥ 2` (so `t = ⌈1 / (1 - a)⌉ - 1`),
`h(a) = 6 (C(t, 3) c³ + C(t, 2) c² (1 - t c))` where
`c = (t + √(t (t - a (t + 1)))) / (t (t + 1))`. It is the triangle density of the complete
`(t + 1)`-partite graph with edge density `a` whose `t` largest parts have equal size `c`
(Pikhurko and Razborov, Combin. Probab. Comput. 26 (2017), arXiv:1204.2846v2, equations (1)-(4);
A. A. Razborov, *On the minimal density of triangles in graphs*, Combin. Probab. Comput. 17
(2008)). -/
noncomputable def razborovTriangleDensity (a : ℝ) : ℝ :=
  if a ≤ 1 / 2 then 0
  else if 1 ≤ a then 1
  else
    let t : ℕ := ⌈1 / (1 - a)⌉₊ - 1
    let c : ℝ := (t + Real.sqrt (t * (t - a * (t + 1)))) / (t * (t + 1))
    6 * ((t.choose 3 : ℝ) * c ^ 3 + (t.choose 2 : ℝ) * c ^ 2 * (1 - t * c))

/-- **Razborov's function vanishes up to edge density one half.** For `a ≤ 1/2`,
`h(a) = 0`: complete bipartite graphs are triangle-free and realise every edge density up to
`1/2` asymptotically. -/
theorem razborovTriangleDensity_of_le_half {a : ℝ} (ha : a ≤ 1 / 2) :
    razborovTriangleDensity a = 0 := by
  unfold razborovTriangleDensity
  simp only [ha, ↓reduceIte]

/-- **Razborov's function at the Turán densities.** For every natural number `t ≥ 2`, at the
edge density `a = 1 - 1/(t+1)` of the balanced complete `(t + 1)`-partite graph,
`h(a) = t (t - 1) / (t + 1) ^ 2`, the triangle density of that graph. -/
theorem razborovTriangleDensity_one_sub_inv {t : ℕ} (ht : 2 ≤ t) :
    razborovTriangleDensity (1 - 1 / (t + 1)) = t * (t - 1) / (t + 1) ^ 2 := by
  have ht' : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hpos : (0 : ℝ) < t + 1 := by linarith
  have h1 : ¬ (1 - 1 / ((t : ℝ) + 1) ≤ 1 / 2) := by
    rw [not_le, lt_sub_iff_add_lt, ← lt_sub_iff_add_lt', div_lt_iff₀ hpos]
    linarith
  have h2 : ¬ (1 ≤ 1 - 1 / ((t : ℝ) + 1)) := by
    rw [not_le, sub_lt_self_iff]; positivity
  have hceil : ⌈1 / (1 - (1 - 1 / ((t : ℝ) + 1)))⌉₊ - 1 = t := by
    rw [sub_sub_cancel, one_div_one_div]
    exact_mod_cast (show ⌈((t + 1 : ℕ) : ℝ)⌉₊ - 1 = t by rw [Nat.ceil_natCast]; omega)
  unfold razborovTriangleDensity
  simp only [h1, h2, ↓reduceIte]
  simp only [hceil]
  have hsq : (t : ℝ) * (t - (1 - 1 / (t + 1)) * (t + 1)) = 0 := by
    field_simp; ring
  have ht0 : (t : ℝ) ≠ 0 := by positivity
  have hc : ((t : ℝ) + Real.sqrt ((t : ℝ) * (t - (1 - 1 / (t + 1)) * (t + 1)))) / (t * (t + 1)) =
      1 / (t + 1) := by
    rw [hsq, Real.sqrt_zero, add_zero]; field_simp
  rw [hc]
  have hc3 : ((t.choose 3 : ℕ) : ℝ) * 6 = t * (t - 1) * (t - 2) := by
    have h := Nat.descFactorial_eq_factorial_mul_choose t 3
    simp only [Nat.descFactorial, tsub_zero, mul_one, Nat.factorial, Nat.succ_eq_add_one,
      Nat.reduceAdd, zero_add, Nat.reduceMul] at h
    have h' : ((t - 2) * ((t - 1) * t) : ℕ) = 6 * t.choose 3 := by
      simpa [mul_comm, mul_assoc, mul_left_comm] using h
    have := congrArg (fun x : ℕ => (x : ℝ)) h'
    push_cast [Nat.cast_sub (by omega : 1 ≤ t), Nat.cast_sub (by omega : 2 ≤ t)] at this
    linarith
  have hc2 : ((t.choose 2 : ℕ) : ℝ) * 2 = t * (t - 1) := by
    have h := Nat.descFactorial_eq_factorial_mul_choose t 2
    simp only [Nat.descFactorial, tsub_zero, mul_one, Nat.factorial, Nat.succ_eq_add_one,
      Nat.reduceAdd, zero_add] at h
    have := congrArg (fun x : ℕ => (x : ℝ)) h
    push_cast [Nat.cast_sub (by omega : 1 ≤ t)] at this
    linarith
  have e3 : ((t.choose 3 : ℕ) : ℝ) = t * (t - 1) * (t - 2) / 6 := by
    rw [← hc3]; ring
  have e2 : ((t.choose 2 : ℕ) : ℝ) = t * (t - 1) / 2 := by
    rw [← hc2]; ring
  rw [e3, e2]
  field_simp
  ring

end MathlibExt.Combinatorics.SimpleGraph.RazborovTriangleFunction
