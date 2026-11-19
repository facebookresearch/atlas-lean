/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Order.Basic

/-!
# Cobb-Douglas Solow steady state: existence, uniqueness, convergence

For Cobb-Douglas intensive production `f(k) = A * k ^ alpha` with `A > 0`
and `0 < alpha < 1`, the reduced-form Solow map is
`phi(k) = a * k ^ alpha + b * k` with `a = s * A / D`,
`b = (1 - delta) / D`, `D = (1 + n) * (1 + g)`. The steady state solves
`phi(k*) = k*`, giving the closed form
`k* = (a / (1 - b)) ^ (1 / (1 - alpha))`. Convergence is by monotone bounded
convergence on the invariant interval between the starting point and the
steady state, not by a contraction argument: `phi'(k) -> infinity` as
`k -> 0+`, so no global contraction constant exists. The map is the
per-effective-worker law `k' = (s * f(k) + (1 - delta) * k) / D`, written out
explicitly for Cobb-Douglas production (`solowMap_eq_law`, an algebraic
identity).

## Main results

* `MathlibExt.Economics.Macro.SolowSteadyState.solow_fixedPoint`: the
  closed-form point is positive and fixed.
* `MathlibExt.Economics.Macro.SolowSteadyState.solow_unique`: no other
  positive point is fixed.
* `MathlibExt.Economics.Macro.SolowSteadyState.solow_tendsto`: from any
  positive starting capital, the path converges to the steady state.

## References

* D. Acemoglu, *Introduction to Modern Economic Growth*, Princeton University Press (2009),
  Sections 2.2–2.3: the discrete-time Solow model `k(t + 1) = s f(k(t)) + (1 - δ) k(t)`
  (equation (2.17)), Example 2.1 (Cobb-Douglas production), Proposition 2.2 (a unique
  positive steady state) and Proposition 2.5 (from any `k(0) > 0` the path converges
  monotonically to it). These treat the case `D = 1`, without population growth or
  technological progress.
* P. B. Sørensen and H. J. Whitta-Jacobsen, *Introducing Advanced Macroeconomics: Growth
  and Business Cycles*, 2nd ed., McGraw-Hill (2010), Chapter 5 (The Solow Model with
  Technological Progress): the discrete-time Solow model with technological progress,
  written in capital per effective worker.
* Atlas roadmap target MA03.T02.
-/

@[expose] public section

namespace MathlibExt.Economics.Macro.SolowSteadyState

/-- The reduced-form discrete Solow map for Cobb-Douglas technology. -/
noncomputable def solowMap (a b α : ℝ) (k : ℝ) : ℝ :=
  a * k ^ α + b * k

/-- The closed-form positive steady state of the Cobb-Douglas Solow map. -/
noncomputable def solowSteadyState (a b α : ℝ) : ℝ :=
  (a / (1 - b)) ^ ((1 : ℝ) / (1 - α))

/-- The Solow map preserves positivity. -/
theorem solow_phi_pos {a b α : ℝ} (ha : 0 < a) (hb₀ : 0 ≤ b) {k : ℝ}
    (hk : 0 < k) : 0 < solowMap a b α k := by
  unfold solowMap
  have h1 : 0 < a * k ^ α := mul_pos ha (Real.rpow_pos_of_pos hk α)
  have h2 : 0 ≤ b * k := mul_nonneg hb₀ (le_of_lt hk)
  linarith

/-- Every iterate of a positive starting point is positive. -/
theorem solow_path_pos {a b α k₀ : ℝ} (ha : 0 < a) (hb₀ : 0 ≤ b)
    {k : ℕ → ℝ} (hk₀ : 0 < k₀) (h0 : k 0 = k₀)
    (hrec : ∀ t, k (t + 1) = solowMap a b α (k t)) : ∀ t, 0 < k t := by
  intro t
  induction t with
  | zero => rw [h0]; exact hk₀
  | succ t ih => rw [hrec t]; exact solow_phi_pos ha hb₀ ih

/-- The Solow map is strictly monotone on `[0, infinity)`. -/
theorem solow_strictMonoOn {a b α : ℝ} (ha : 0 < a) (hb₀ : 0 ≤ b)
    (hα₀ : 0 < α) : StrictMonoOn (solowMap a b α) (Set.Ici 0) := by
  intro x hx y hy hxy
  rw [Set.mem_Ici] at hx hy
  unfold solowMap
  have hpow : x ^ α < y ^ α := Real.rpow_lt_rpow hx hxy hα₀
  have h1 : a * x ^ α < a * y ^ α := mul_lt_mul_of_pos_left hpow ha
  have h2 : b * x ≤ b * y := mul_le_mul_of_nonneg_left (le_of_lt hxy) hb₀
  exact add_lt_add_of_lt_of_le h1 h2

/-- A positive fixed point satisfies `k ^ (alpha - 1) = (1 - b) / a`. -/
theorem solow_rpow_sub_one_eq {a b α : ℝ} (ha : 0 < a) (_hb₁ : b < 1)
    {k : ℝ} (hk : 0 < k) (hfix : solowMap a b α k = k) :
    k ^ (α - 1) = (1 - b) / a := by
  have h1 : a * k ^ α = (1 - b) * k := by
    have h := hfix
    unfold solowMap at h
    have hsub : a * k ^ α = k - b * k := by linarith
    rw [hsub]
    ring
  have hsplit : k ^ α = k ^ (α - 1) * k := by
    have hexp : (α - 1) + 1 = α := by ring
    calc k ^ α = k ^ ((α - 1) + 1) := by rw [hexp]
      _ = k ^ (α - 1) * k ^ (1:ℝ) := Real.rpow_add hk _ _
      _ = k ^ (α - 1) * k := by rw [Real.rpow_one]
  rw [hsplit] at h1
  have hkne : k ≠ 0 := ne_of_gt hk
  have h2 : a * k ^ (α - 1) = 1 - b := by
    have h1' : (a * k ^ (α - 1)) * k = (1 - b) * k := by linear_combination h1
    exact mul_right_cancel₀ hkne h1'
  rw [eq_div_iff (ne_of_gt ha)]
  linear_combination h2

/-- The reduced-form map agrees with the per-effective-worker law
`k' = (s * f(k) + (1 - δ) * k) / D`, written out for Cobb-Douglas production
`f(k) = A * k ^ α`. This is an algebraic identity in the explicit formula. -/
theorem solowMap_eq_law {s δ D A α k : ℝ} (hD : D ≠ 0) :
    (s * (A * k ^ α) + (1 - δ) * k) / D =
      solowMap (s * A / D) ((1 - δ) / D) α k := by
  unfold solowMap
  field_simp

/-- **Existence:** the closed-form point is positive and fixed by the map. -/
theorem solow_fixedPoint {a b α : ℝ} (ha : 0 < a) (hb₀ : 0 ≤ b) (hb₁ : b < 1)
    (hα₀ : 0 < α) (hα₁ : α < 1) :
    0 < solowSteadyState a b α ∧
      solowMap a b α (solowSteadyState a b α) = solowSteadyState a b α := by
  have _ := hb₀
  have h1b : 0 < 1 - b := by linarith
  have h1a : (0:ℝ) < 1 - α := by linarith
  have h1bne : (1:ℝ) - b ≠ 0 := ne_of_gt h1b
  have h1ane : (1:ℝ) - α ≠ 0 := ne_of_gt h1a
  have hc : 0 < a / (1 - b) := by positivity
  have hpos : 0 < solowSteadyState a b α := by
    unfold solowSteadyState
    exact Real.rpow_pos_of_pos hc _
  refine ⟨hpos, ?_⟩
  have key : a * (solowSteadyState a b α) ^ α
      = (1 - b) * solowSteadyState a b α := by
    have hbase : (1 - b) * (a / (1 - b)) = a := by field_simp
    have hexp1 : (1:ℝ) / (1 - α) * α = α / (1 - α) := by field_simp
    have hexp2 : (1:ℝ) + α / (1 - α) = 1 / (1 - α) := by
      field_simp
      ring
    have hpow : ((a / (1 - b)) ^ ((1:ℝ) / (1 - α))) ^ α
        = (a / (1 - b)) ^ (α / (1 - α)) := by
      rw [← Real.rpow_mul hc.le, hexp1]
    have h2 : (a / (1 - b)) * (a / (1 - b)) ^ (α / (1 - α))
        = (a / (1 - b)) ^ ((1:ℝ) / (1 - α)) := by
      have h3 : (a / (1 - b)) ^ ((1:ℝ) + α / (1 - α))
          = (a / (1 - b)) * (a / (1 - b)) ^ (α / (1 - α)) := by
        rw [Real.rpow_add hc, Real.rpow_one]
      rw [hexp2] at h3
      exact h3.symm
    unfold solowSteadyState
    rw [hpow]
    calc a * (a / (1 - b)) ^ (α / (1 - α))
        = ((1 - b) * (a / (1 - b))) * (a / (1 - b)) ^ (α / (1 - α)) := by
          rw [hbase]
      _ = (1 - b) * ((a / (1 - b)) * (a / (1 - b)) ^ (α / (1 - α))) := by ring
      _ = (1 - b) * (a / (1 - b)) ^ ((1:ℝ) / (1 - α)) := by rw [h2]
  unfold solowMap
  calc a * (solowSteadyState a b α) ^ α + b * solowSteadyState a b α
      = (1 - b) * solowSteadyState a b α + b * solowSteadyState a b α := by
        rw [key]
    _ = solowSteadyState a b α := by ring

/-- Comparison of `a * k ^ (alpha - 1)` with `1 - b` detects `k` above the steady state. -/
theorem solow_key_lt {a b α : ℝ} (ha : 0 < a) (hb₀ : 0 ≤ b) (hb₁ : b < 1)
    (hα₀ : 0 < α) (hα₁ : α < 1) {k : ℝ} (hk : 0 < k) :
    a * k ^ (α - 1) < 1 - b ↔ solowSteadyState a b α < k := by
  have hstar_pos : 0 < solowSteadyState a b α :=
    (solow_fixedPoint ha hb₀ hb₁ hα₀ hα₁).1
  have hstar_fix : solowMap a b α (solowSteadyState a b α)
      = solowSteadyState a b α :=
    (solow_fixedPoint ha hb₀ hb₁ hα₀ hα₁).2
  have hstar_eq : (solowSteadyState a b α) ^ (α - 1) = (1 - b) / a :=
    solow_rpow_sub_one_eq ha hb₁ hstar_pos hstar_fix
  have hexp_neg : α - 1 < 0 := by linarith
  have hiff : k ^ (α - 1) < (solowSteadyState a b α) ^ (α - 1)
      ↔ solowSteadyState a b α < k :=
    Real.rpow_lt_rpow_iff_of_neg hk hstar_pos hexp_neg
  have hdiv : a * k ^ (α - 1) < 1 - b ↔ k ^ (α - 1) < (1 - b) / a := by
    rw [lt_div_iff₀ ha]
    have hcomm : a * k ^ (α - 1) = k ^ (α - 1) * a := by ring
    rw [hcomm]
  rw [hdiv, ← hstar_eq]
  exact hiff

/-- Comparison of `a * k ^ (alpha - 1)` with `1 - b` detects `k` below the steady state. -/
theorem solow_key_gt {a b α : ℝ} (ha : 0 < a) (hb₀ : 0 ≤ b) (hb₁ : b < 1)
    (hα₀ : 0 < α) (hα₁ : α < 1) {k : ℝ} (hk : 0 < k) :
    1 - b < a * k ^ (α - 1) ↔ k < solowSteadyState a b α := by
  have hstar_pos : 0 < solowSteadyState a b α :=
    (solow_fixedPoint ha hb₀ hb₁ hα₀ hα₁).1
  have hstar_fix : solowMap a b α (solowSteadyState a b α)
      = solowSteadyState a b α :=
    (solow_fixedPoint ha hb₀ hb₁ hα₀ hα₁).2
  have hstar_eq : (solowSteadyState a b α) ^ (α - 1) = (1 - b) / a :=
    solow_rpow_sub_one_eq ha hb₁ hstar_pos hstar_fix
  have hexp_neg : α - 1 < 0 := by linarith
  have hiff : (solowSteadyState a b α) ^ (α - 1) < k ^ (α - 1)
      ↔ k < solowSteadyState a b α :=
    Real.rpow_lt_rpow_iff_of_neg hstar_pos hk hexp_neg
  have hdiv : 1 - b < a * k ^ (α - 1) ↔ (1 - b) / a < k ^ (α - 1) := by
    rw [div_lt_iff₀ ha]
    have hcomm : a * k ^ (α - 1) = k ^ (α - 1) * a := by ring
    rw [hcomm]
  rw [hdiv, ← hstar_eq]
  exact hiff

/-- The displacement `phi(k) - k` factors through `a * k ^ (alpha - 1) - (1 - b)`. -/
theorem solow_diff_eq {a b α : ℝ} {k : ℝ} (hk : 0 < k) :
    solowMap a b α k - k = k * (a * k ^ (α - 1) - (1 - b)) := by
  have hsplit : k ^ α = k * k ^ (α - 1) := by
    have hexp : (1:ℝ) + (α - 1) = α := by ring
    calc k ^ α = k ^ ((1:ℝ) + (α - 1)) := by rw [hexp]
      _ = k ^ (1:ℝ) * k ^ (α - 1) := Real.rpow_add hk _ _
      _ = k * k ^ (α - 1) := by rw [Real.rpow_one]
  unfold solowMap
  rw [hsplit]
  ring

/-- The map decreases `k` exactly when `k` is above the steady state. -/
theorem solow_map_lt_self_iff {a b α : ℝ} (ha : 0 < a) (hb₀ : 0 ≤ b)
    (hb₁ : b < 1) (hα₀ : 0 < α) (hα₁ : α < 1) {k : ℝ} (hk : 0 < k) :
    solowMap a b α k < k ↔ solowSteadyState a b α < k := by
  have hdiff : solowMap a b α k - k = k * (a * k ^ (α - 1) - (1 - b)) :=
    solow_diff_eq hk
  have hmul : k * (a * k ^ (α - 1) - (1 - b)) < 0
      ↔ a * k ^ (α - 1) - (1 - b) < 0 := by
    constructor
    · intro h
      by_contra hcon
      push Not at hcon
      have hnn : 0 ≤ k * (a * k ^ (α - 1) - (1 - b)) :=
        mul_nonneg (le_of_lt hk) hcon
      linarith
    · intro h
      exact mul_neg_of_pos_of_neg hk h
  calc (solowMap a b α k < k)
      _ ↔ solowMap a b α k - k < 0 := sub_neg.symm
      _ ↔ k * (a * k ^ (α - 1) - (1 - b)) < 0 := by rw [hdiff]
      _ ↔ a * k ^ (α - 1) - (1 - b) < 0 := hmul
      _ ↔ a * k ^ (α - 1) < 1 - b := sub_neg
      _ ↔ solowSteadyState a b α < k :=
        solow_key_lt ha hb₀ hb₁ hα₀ hα₁ hk

/-- The map increases `k` exactly when `k` is below the steady state. -/
theorem solow_self_lt_map_iff {a b α : ℝ} (ha : 0 < a) (hb₀ : 0 ≤ b)
    (hb₁ : b < 1) (hα₀ : 0 < α) (hα₁ : α < 1) {k : ℝ} (hk : 0 < k) :
    k < solowMap a b α k ↔ k < solowSteadyState a b α := by
  have hdiff : solowMap a b α k - k = k * (a * k ^ (α - 1) - (1 - b)) :=
    solow_diff_eq hk
  have hmul : 0 < k * (a * k ^ (α - 1) - (1 - b))
      ↔ 0 < a * k ^ (α - 1) - (1 - b) :=
    mul_pos_iff_of_pos_left hk
  calc (k < solowMap a b α k)
      _ ↔ 0 < solowMap a b α k - k := sub_pos.symm
      _ ↔ 0 < k * (a * k ^ (α - 1) - (1 - b)) := by rw [hdiff]
      _ ↔ 0 < a * k ^ (α - 1) - (1 - b) := hmul
      _ ↔ 1 - b < a * k ^ (α - 1) := sub_pos
      _ ↔ k < solowSteadyState a b α :=
        solow_key_gt ha hb₀ hb₁ hα₀ hα₁ hk

/-- **Uniqueness:** no other positive point is fixed by the map. -/
theorem solow_unique {a b α : ℝ} (ha : 0 < a) (hb₀ : 0 ≤ b) (hb₁ : b < 1)
    (hα₀ : 0 < α) (hα₁ : α < 1) {k : ℝ} (hk : 0 < k)
    (hfix : solowMap a b α k = k) :
    k = solowSteadyState a b α := by
  have hstar_pos : 0 < solowSteadyState a b α :=
    (solow_fixedPoint ha hb₀ hb₁ hα₀ hα₁).1
  have hstar_fix : solowMap a b α (solowSteadyState a b α)
      = solowSteadyState a b α :=
    (solow_fixedPoint ha hb₀ hb₁ hα₀ hα₁).2
  have hk_eq : k ^ (α - 1) = (1 - b) / a :=
    solow_rpow_sub_one_eq ha hb₁ hk hfix
  have hstar_eq : (solowSteadyState a b α) ^ (α - 1) = (1 - b) / a :=
    solow_rpow_sub_one_eq ha hb₁ hstar_pos hstar_fix
  have heq : k ^ (α - 1) = (solowSteadyState a b α) ^ (α - 1) := by
    rw [hk_eq, hstar_eq]
  have hne : α - 1 ≠ 0 := by
    have hlt : α - 1 < 0 := by linarith
    exact ne_of_lt hlt
  exact (Real.rpow_left_inj hk.le hstar_pos.le hne).mp heq

/-- The map is continuous along convergent sequences (away from zero limits). -/
theorem solow_tendsto_map {a b α : ℝ} {L : ℝ} (hL : L ≠ 0)
    {k : ℕ → ℝ} (hlim : Filter.Tendsto k Filter.atTop (nhds L)) :
    Filter.Tendsto (fun t => solowMap a b α (k t)) Filter.atTop
      (nhds (solowMap a b α L)) := by
  have hpow : Filter.Tendsto (fun t => (k t) ^ α) Filter.atTop (nhds (L ^ α)) :=
    Filter.Tendsto.rpow_const hlim (Or.inl hL)
  have h1 : Filter.Tendsto (fun t => a * (k t) ^ α) Filter.atTop
      (nhds (a * L ^ α)) :=
    Filter.Tendsto.const_mul a hpow
  have h2 : Filter.Tendsto (fun t => b * k t) Filter.atTop (nhds (b * L)) :=
    Filter.Tendsto.const_mul b hlim
  have h3 := h1.add h2
  simp only [solowMap]
  exact h3

/-- A nonzero limit of a Solow path is a fixed point of the map. -/
theorem solow_limit_fixed {a b α : ℝ} {k : ℕ → ℝ} {L : ℝ} (hL : L ≠ 0)
    (hlim : Filter.Tendsto k Filter.atTop (nhds L))
    (hrec : ∀ t, k (t + 1) = solowMap a b α (k t)) :
    solowMap a b α L = L := by
  have hmap : Filter.Tendsto (fun t => solowMap a b α (k t)) Filter.atTop
      (nhds (solowMap a b α L)) :=
    solow_tendsto_map hL hlim
  have hshift : Filter.Tendsto (fun t => k (t + 1)) Filter.atTop (nhds L) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mpr hlim
  have hsame : (fun t => k (t + 1)) = (fun t => solowMap a b α (k t)) :=
    funext hrec
  rw [hsame] at hshift
  exact (tendsto_nhds_unique hshift hmap).symm

/-- **Convergence:** from any positive starting capital, the invariant-domain
path `k(t+1) = φ(k(t))` converges to the unique positive steady state. The
path stays in the closed interval between its starting point and the steady
state, is monotone there, and is bounded; its limit is a fixed point, hence
the steady state by uniqueness. -/
theorem solow_tendsto {a b α k₀ : ℝ} (ha : 0 < a) (hb₀ : 0 ≤ b) (hb₁ : b < 1)
    (hα₀ : 0 < α) (hα₁ : α < 1) {k : ℕ → ℝ} (hk₀ : 0 < k₀) (h0 : k 0 = k₀)
    (hrec : ∀ t, k (t + 1) = solowMap a b α (k t)) :
    Filter.Tendsto k Filter.atTop (nhds (solowSteadyState a b α)) := by
  have hstar_pos : 0 < solowSteadyState a b α :=
    (solow_fixedPoint ha hb₀ hb₁ hα₀ hα₁).1
  have hstar_fix : solowMap a b α (solowSteadyState a b α)
      = solowSteadyState a b α :=
    (solow_fixedPoint ha hb₀ hb₁ hα₀ hα₁).2
  have hpos : ∀ t, 0 < k t := solow_path_pos ha hb₀ hk₀ h0 hrec
  have hmono_phi := solow_strictMonoOn ha hb₀ hα₀
  rcases le_total k₀ (solowSteadyState a b α) with hcase | hcase
  · have hle : ∀ t, k t ≤ solowSteadyState a b α := by
      intro t
      induction t with
      | zero => rw [h0]; exact hcase
      | succ t ih =>
        rw [hrec t]
        calc solowMap a b α (k t)
            ≤ solowMap a b α (solowSteadyState a b α) := by
              rcases eq_or_lt_of_le ih with heq | hlt
              · rw [heq]
              · exact le_of_lt (hmono_phi (Set.mem_Ici.mpr (hpos t).le)
                  (Set.mem_Ici.mpr hstar_pos.le) hlt)
          _ = solowSteadyState a b α := hstar_fix
    have hstep : ∀ t, k t ≤ k (t + 1) := by
      intro t
      rw [hrec t]
      rcases eq_or_lt_of_le (hle t) with heq | hlt
      · rw [heq, hstar_fix]
      · exact le_of_lt
          ((solow_self_lt_map_iff ha hb₀ hb₁ hα₀ hα₁ (hpos t)).mpr hlt)
    have hmon : Monotone k := monotone_nat_of_le_succ hstep
    have hbdd : BddAbove (Set.range k) := by
      refine ⟨solowSteadyState a b α, fun y hy => ?_⟩
      obtain ⟨t, rfl⟩ := hy
      exact hle t
    have hlim : Filter.Tendsto k Filter.atTop (nhds (⨆ i, k i)) :=
      tendsto_atTop_ciSup hmon hbdd
    have hLpos : 0 < ⨆ i, k i := by
      have h := le_ciSup hbdd 0
      rw [h0] at h
      exact lt_of_lt_of_le hk₀ h
    have hfixL : solowMap a b α (⨆ i, k i) = ⨆ i, k i :=
      solow_limit_fixed (ne_of_gt hLpos) hlim hrec
    have hLeq : (⨆ i, k i) = solowSteadyState a b α :=
      solow_unique ha hb₀ hb₁ hα₀ hα₁ hLpos hfixL
    rw [hLeq] at hlim
    exact hlim
  · have hge : ∀ t, solowSteadyState a b α ≤ k t := by
      intro t
      induction t with
      | zero => rw [h0]; exact hcase
      | succ t ih =>
        rw [hrec t]
        calc solowSteadyState a b α
            = solowMap a b α (solowSteadyState a b α) := hstar_fix.symm
          _ ≤ solowMap a b α (k t) := by
              rcases eq_or_lt_of_le ih with heq | hlt
              · rw [heq]
              · exact le_of_lt (hmono_phi (Set.mem_Ici.mpr hstar_pos.le)
                  (Set.mem_Ici.mpr (hpos t).le) hlt)
    have hstep : ∀ t, k (t + 1) ≤ k t := by
      intro t
      rw [hrec t]
      rcases eq_or_lt_of_le (hge t) with heq | hlt
      · rw [← heq, hstar_fix]
      · exact le_of_lt
          ((solow_map_lt_self_iff ha hb₀ hb₁ hα₀ hα₁ (hpos t)).mpr hlt)
    have hanti : Antitone k := antitone_nat_of_succ_le hstep
    have hbdd : BddBelow (Set.range k) := by
      refine ⟨solowSteadyState a b α, fun y hy => ?_⟩
      obtain ⟨t, rfl⟩ := hy
      exact hge t
    have hlim : Filter.Tendsto k Filter.atTop (nhds (⨅ i, k i)) :=
      tendsto_atTop_ciInf hanti hbdd
    have hLpos : 0 < ⨅ i, k i := by
      have h : solowSteadyState a b α ≤ ⨅ i, k i := le_ciInf hge
      exact lt_of_lt_of_le hstar_pos h
    have hfixL : solowMap a b α (⨅ i, k i) = ⨅ i, k i :=
      solow_limit_fixed (ne_of_gt hLpos) hlim hrec
    have hLeq : (⨅ i, k i) = solowSteadyState a b α :=
      solow_unique ha hb₀ hb₁ hα₀ hα₁ hLpos hfixL
    rw [hLeq] at hlim
    exact hlim

end MathlibExt.Economics.Macro.SolowSteadyState
