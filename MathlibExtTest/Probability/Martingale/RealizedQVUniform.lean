/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Martingale.RealizedQVUniform
public import MathlibExt.Probability.Martingale.McLeishCLT
public import MathlibExtTest.Probability.Martingale.RealizedQV

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal
open MathlibExt.Probability.Martingale
open MathlibExtTest.Probability.Martingale.RealizedQV

namespace MathlibExtTest.Probability.Martingale.RealizedQVUniform

noncomputable section

/-! ### Statement faithfulness: the converse output is T82's `hQV`

`tendstoInMeasure_sum_condExp_floor_of_rqv` turns T81's realized-variation hypothesis `hRQV`
into T82's predictable-variation hypothesis `hQV` with no glue, so T82's functional CLT holds
under the realized-variation hypothesis alone. -/

example {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {𝓕 : ℕ → Filtration ℕ m} {ξ : ℕ → ℕ → Ω → ℝ}
    (hξ : ∀ n i, StronglyMeasurable[𝓕 n (i + 1)] (ξ n i))
    (hmds : ∀ n i, μ[ξ n i | 𝓕 n i] =ᵐ[μ] 0) (hL2 : ∀ n i, MemLp (ξ n i) 2 μ)
    (hRQV : ∀ t : Set.Icc (0 : ℝ) 1, TendstoInMeasure μ
      (fun (n : ℕ) ω => ∑ j ∈ Finset.range ⌊(n : ℝ) * t.1⌋₊, ξ n j ω ^ 2) atTop
      (fun _ => t.1))
    (hLind : LindebergConditionTriangular ξ μ)
    (Z : Ω' → C(Set.Icc (0 : ℝ) 1, ℝ)) (hZm : Measurable Z)
    (hZ : ∀ (I : Finset (Set.Icc (0 : ℝ) 1)) (c : I → ℝ),
      P'.map (fun ω => ∑ s : I, c s * Z ω s) = gaussianReal 0
        (∑ s : I, ∑ u : I, c s * c u * (min (s : Set.Icc (0 : ℝ) 1) u).1).toNNReal) :
    TendstoInDistribution (fun n => arrayStepProcess n ξ) atTop
      (fun ω => SkorokhodSpace.ofContinuous (Z ω)) (fun _ => μ) P' :=
  tendstoInDistribution_arrayStepProcess hξ hmds hL2
    (tendstoInMeasure_sum_condExp_floor_of_rqv hξ hL2 hRQV hLind) hLind Z hZm.aemeasurable
    (tendstoInDistribution_fdd_martingaleDifference_floor hξ hmds hL2 hLind hRQV Z hZm hZ)

/-- Under Lindeberg the realized and predictable pointwise hypotheses are equivalent: the
converse composed with T123's forward theorem returns the hypothesis it started from. -/
example {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝓕 : ℕ → Filtration ℕ m} {ξ : ℕ → ℕ → Ω → ℝ}
    (hξ : ∀ n i, StronglyMeasurable[𝓕 n (i + 1)] (ξ n i)) (hL2 : ∀ n i, MemLp (ξ n i) 2 μ)
    (hLind : LindebergConditionTriangular ξ μ) :
    (∀ t ∈ Set.Icc (0 : ℝ) 1, TendstoInMeasure μ
      (fun (n : ℕ) ω => ∑ j ∈ Finset.range ⌊(n : ℝ) * t⌋₊, (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω)
      atTop (fun _ => t)) ↔
    (∀ t : Set.Icc (0 : ℝ) 1, TendstoInMeasure μ
      (fun (n : ℕ) ω => ∑ j ∈ Finset.range ⌊(n : ℝ) * t.1⌋₊, ξ n j ω ^ 2) atTop
      (fun _ => t.1)) :=
  ⟨fun hQV => tendstoInMeasure_sum_sq_floor_of_qv hξ hL2 hQV hLind,
    fun hRQV => tendstoInMeasure_sum_condExp_floor_of_rqv hξ hL2 hRQV hLind⟩

/-! ### Non-vacuity: `flatArray` (every increment `1 / √n`) satisfies the converse's hypotheses

The realized variation of `flatArray` up to `⌊n t⌋` is `⌊n t⌋ / n`, computed from the
definition (`sum_flatArray_sq`); its limit `t` is a deterministic limit. The conditional
variances are the constants `1 / n`. -/

lemma condExp_flatArray_sq {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (𝓕 : ℕ → Filtration ℕ m) (n j : ℕ) :
    μ[fun ω => flatArray n j ω ^ 2 | 𝓕 n j] = fun _ => (n : ℝ)⁻¹ := by
  simp only [flatArray_sq]
  exact condExp_const ((𝓕 n).le j) _

lemma rqv_flatArray {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    ∀ t : Set.Icc (0 : ℝ) 1, TendstoInMeasure μ
      (fun (n : ℕ) ω => ∑ j ∈ Finset.range ⌊(n : ℝ) * t.1⌋₊, flatArray n j ω ^ 2) atTop
      (fun _ => t.1) := by
  intro t
  have heq : (fun (n : ℕ) ω => ∑ j ∈ Finset.range ⌊(n : ℝ) * t.1⌋₊, flatArray n j ω ^ 2) =
      fun (n : ℕ) (_ : Ω) => (⌊(n : ℝ) * t.1⌋₊ : ℝ) / n := by
    funext n ω; exact sum_flatArray_sq n t.1 ω
  rw [heq]
  exact tendstoInMeasure_of_tendsto_ae (fun n => aestronglyMeasurable_const)
    (Eventually.of_forall fun ω => tendsto_floor_mul_div t.1 t.2.1)

/-- The converse applies to `flatArray`: the uniform conclusion for the predictable variation. -/
example {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (𝓕 : ℕ → Filtration ℕ m) :
    TendstoInMeasure μ
      (fun (n : ℕ) ω => ⨆ t : Set.Icc (0 : ℝ) 1,
        |∑ j ∈ Finset.range ⌊(n : ℝ) * t⌋₊, (μ[fun ω => flatArray n j ω ^ 2 | 𝓕 n j]) ω -
          (t : ℝ)|) atTop (fun _ => 0) :=
  tendstoInMeasure_iSup_abs_sum_condExp_floor_sub_of_rqv (𝓕 := 𝓕)
    (fun _ _ => stronglyMeasurable_const) (fun _ _ => memLp_const _) (rqv_flatArray μ)
    (lindeberg_flatArray μ)

/-- The uniform realized-variation theorem applies to `flatArray` (T82's hypotheses checked
from the definitions). -/
example {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (𝓕 : ℕ → Filtration ℕ m) :
    TendstoInMeasure μ
      (fun (n : ℕ) ω => ⨆ t : Set.Icc (0 : ℝ) 1,
        |∑ j ∈ Finset.range ⌊(n : ℝ) * t⌋₊, flatArray n j ω ^ 2 - (t : ℝ)|) atTop
      (fun _ => 0) := by
  have hQV : ∀ s ∈ Set.Icc (0 : ℝ) 1, TendstoInMeasure μ
      (fun (n : ℕ) ω => ∑ j ∈ Finset.range ⌊(n : ℝ) * s⌋₊,
        (μ[fun ω => flatArray n j ω ^ 2 | 𝓕 n j]) ω) atTop (fun _ => s) := by
    intro s hs
    have heq : (fun (n : ℕ) ω => ∑ j ∈ Finset.range ⌊(n : ℝ) * s⌋₊,
        (μ[fun ω => flatArray n j ω ^ 2 | 𝓕 n j]) ω) =
        fun (n : ℕ) (_ : Ω) => (⌊(n : ℝ) * s⌋₊ : ℝ) / n := by
      funext n ω
      rw [Finset.sum_congr rfl fun j _ => congrFun (condExp_flatArray_sq μ 𝓕 n j) ω]
      simp [div_eq_mul_inv]
    rw [heq]
    exact tendstoInMeasure_of_tendsto_ae (fun n => aestronglyMeasurable_const)
      (Eventually.of_forall fun ω => tendsto_floor_mul_div s hs.1)
  exact tendstoInMeasure_iSup_abs_sum_sq_floor_sub_of_qv (𝓕 := 𝓕)
    (fun _ _ => stronglyMeasurable_const) (fun _ _ => memLp_const _) hQV
    (lindeberg_flatArray μ)

/-! ### The uniform value, from the definitions

For `flatArray` the realized variation is `⌊n t⌋ / n`, which is within `1 / n` of `t` for every
`t ∈ [0,1]`: the uniform error is `O(1/n)`, computed without the theorems above. -/

example {Ω : Type*} (n : ℕ) (hn : 0 < n) (t : Set.Icc (0 : ℝ) 1) (ω : Ω) :
    |∑ j ∈ Finset.range ⌊(n : ℝ) * t⌋₊, flatArray n j ω ^ 2 - (t : ℝ)| ≤ 1 / n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := Nat.lt_floor_add_one ((n : ℝ) * t)
  have h2 := Nat.floor_le (mul_nonneg hnpos.le t.2.1)
  rw [sum_flatArray_sq, show (⌊(n : ℝ) * t⌋₊ : ℝ) / n - t = (⌊(n : ℝ) * t⌋₊ - n * t) / n by
    field_simp, abs_div, abs_of_pos hnpos, div_le_div_iff_of_pos_right hnpos, abs_le]
  constructor <;> linarith

/-! ### Boundary values and the grid lemma -/

-- The partial sums are nondecreasing in `t` for nonnegative terms: at `t = 1/2` and `t = 1`
-- on row `4` with unit terms, `2 ≤ 4`.
example : ∑ _j ∈ Finset.range ⌊((4 : ℕ) : ℝ) * (1 / 2)⌋₊, (1 : ℝ) ≤
    ∑ _j ∈ Finset.range ⌊((4 : ℕ) : ℝ) * 1⌋₊, (1 : ℝ) :=
  monotone_sum_range_floor_mul (fun _ => zero_le_one) 4 (by norm_num)

-- The grid lemma at `N = 1` for the identity: grid errors `0 < r` give error `< r + 1`.
example (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |id t - t| < r + 1 / (1 : ℕ) :=
  abs_sub_lt_of_grid monotoneOn_id one_pos (fun i _ => by simpa using hr) ht

-- The supremum includes `t = 0`, where the realized variation is `0` and the error is `0`,
-- so the error at `t = 0` is `|0 - 0| = 0`.
example {Ω : Type*} (ξ : ℕ → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    |∑ j ∈ Finset.range ⌊(n : ℝ) * ((0 : Set.Icc (0 : ℝ) 1) : ℝ)⌋₊, ξ n j ω ^ 2 -
      ((0 : Set.Icc (0 : ℝ) 1) : ℝ)| = 0 := by simp

end

end MathlibExtTest.Probability.Martingale.RealizedQVUniform
