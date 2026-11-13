/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Martingale.RealizedQV
public import MathlibExt.Probability.Martingale.McLeishCLT

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal
open MathlibExt.Probability.Martingale

namespace MathlibExtTest.Probability.Martingale.RealizedQV

noncomputable section

/-! ### Statement faithfulness: the conclusion is T81's `hRQV`, and T82's FCLT follows

Under T82's hypotheses plus the Gaussian finite-dimensional laws of Brownian motion for a
measurable `Z`, `tendstoInMeasure_sum_sq_floor_of_qv` supplies the realized-variation hypothesis
`hRQV` of T81's `tendstoInDistribution_fdd_martingaleDifference_floor` with no glue, and its
output is T82's `hT81`. -/

example {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {𝓕 : ℕ → Filtration ℕ m} {ξ : ℕ → ℕ → Ω → ℝ}
    (hξ : ∀ n i, StronglyMeasurable[𝓕 n (i + 1)] (ξ n i))
    (hmds : ∀ n i, μ[ξ n i | 𝓕 n i] =ᵐ[μ] 0) (hL2 : ∀ n i, MemLp (ξ n i) 2 μ)
    (hQV : ∀ t ∈ Set.Icc (0 : ℝ) 1, TendstoInMeasure μ
      (fun (n : ℕ) ω => ∑ j ∈ Finset.range ⌊(n : ℝ) * t⌋₊, (μ[fun ω => ξ n j ω ^ 2 | 𝓕 n j]) ω)
      atTop (fun _ => t))
    (hLind : LindebergConditionTriangular ξ μ)
    (Z : Ω' → C(Set.Icc (0 : ℝ) 1, ℝ)) (hZm : Measurable Z)
    (hZ : ∀ (I : Finset (Set.Icc (0 : ℝ) 1)) (c : I → ℝ),
      P'.map (fun ω => ∑ s : I, c s * Z ω s) = gaussianReal 0
        (∑ s : I, ∑ u : I, c s * c u * (min (s : Set.Icc (0 : ℝ) 1) u).1).toNNReal) :
    TendstoInDistribution (fun n => arrayStepProcess n ξ) atTop
      (fun ω => SkorokhodSpace.ofContinuous (Z ω)) (fun _ => μ) P' :=
  tendstoInDistribution_arrayStepProcess hξ hmds hL2 hQV hLind Z hZm.aemeasurable
    (tendstoInDistribution_fdd_martingaleDifference_floor hξ hmds hL2 hLind
      (tendstoInMeasure_sum_sq_floor_of_qv hξ hL2 hQV hLind) Z hZm hZ)

/-! ### Non-vacuity: a concrete array satisfying every hypothesis

`flatArray n i ω = 1 / √n` on any probability space with any filtrations. Every hypothesis of
`tendstoInMeasure_sum_sq_floor_of_qv` is checked from the definitions, not through the
theorem. -/

/-- The array with every increment of row `n` equal to `1 / √n`. -/
def flatArray {Ω : Type*} (n _i : ℕ) (_ω : Ω) : ℝ := (Real.sqrt n)⁻¹

lemma flatArray_sq {Ω : Type*} (n i : ℕ) (ω : Ω) : flatArray n i ω ^ 2 = (n : ℝ)⁻¹ := by
  rw [flatArray, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

/-- The realized quadratic variation of `flatArray` up to `⌊n t⌋`, from the definition. -/
lemma sum_flatArray_sq {Ω : Type*} (n : ℕ) (t : ℝ) (ω : Ω) :
    ∑ j ∈ Finset.range ⌊(n : ℝ) * t⌋₊, flatArray n j ω ^ 2 = ⌊(n : ℝ) * t⌋₊ / n := by
  simp [flatArray_sq, div_eq_mul_inv]

lemma tendsto_floor_mul_div (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => (⌊(n : ℝ) * t⌋₊ : ℝ) / n) atTop (𝓝 t) := by
  have := (tendsto_nat_floor_mul_div_atTop (R := ℝ) ht).comp tendsto_natCast_atTop_atTop
  refine this.congr fun n => ?_
  simp [mul_comm]

lemma lindeberg_flatArray {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) :
    LindebergConditionTriangular (flatArray (Ω := Ω)) μ := by
  intro ε hε
  refine tendsto_const_nhds.congr' ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (ε ^ 2)⁻¹
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsmall : (Real.sqrt n)⁻¹ ≤ ε := by
    rw [inv_le_comm₀ (Real.sqrt_pos.2 hnpos) hε, Real.le_sqrt (by positivity)
      (Nat.cast_nonneg n)]
    · have : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn
      rw [inv_pow]; linarith
  symm
  refine Finset.sum_eq_zero fun k _ => ?_
  have hempty : {ω' : Ω | ε < |flatArray n k ω'|} = ∅ := by
    ext ω'
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt, flatArray]
    rwa [abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
  simp [hempty]

/-- All hypotheses hold for `flatArray`, so the theorem applies to a concrete array; its
conclusion agrees with the value `⌊n t⌋ / n → t` computed from the definition. -/
example {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (𝓕 : ℕ → Filtration ℕ m) (t : Set.Icc (0 : ℝ) 1) :
    TendstoInMeasure μ
      (fun (n : ℕ) ω => ∑ j ∈ Finset.range ⌊(n : ℝ) * t.1⌋₊, flatArray n j ω ^ 2) atTop
      (fun _ => t.1) := by
  have hcond : ∀ n j, μ[fun ω => flatArray n j ω ^ 2 | 𝓕 n j] = fun _ => (n : ℝ)⁻¹ := by
    intro n j
    simp only [flatArray_sq]
    exact condExp_const ((𝓕 n).le j) _
  have hQV : ∀ s ∈ Set.Icc (0 : ℝ) 1, TendstoInMeasure μ
      (fun (n : ℕ) ω => ∑ j ∈ Finset.range ⌊(n : ℝ) * s⌋₊,
        (μ[fun ω => flatArray n j ω ^ 2 | 𝓕 n j]) ω) atTop (fun _ => s) := by
    intro s hs
    have heq : (fun (n : ℕ) ω => ∑ j ∈ Finset.range ⌊(n : ℝ) * s⌋₊,
        (μ[fun ω => flatArray n j ω ^ 2 | 𝓕 n j]) ω) =
        fun (n : ℕ) (_ : Ω) => (⌊(n : ℝ) * s⌋₊ : ℝ) / n := by
      funext n ω
      rw [Finset.sum_congr rfl fun j _ => congrFun (hcond n j) ω]
      simp [div_eq_mul_inv]
    rw [heq]
    exact tendstoInMeasure_of_tendsto_ae (fun n => aestronglyMeasurable_const)
      (Eventually.of_forall fun ω => tendsto_floor_mul_div s hs.1)
  exact tendstoInMeasure_sum_sq_floor_of_qv (𝓕 := 𝓕)
    (fun n i => stronglyMeasurable_const) (fun n i => memLp_const _) hQV
    (lindeberg_flatArray μ) t

/-! ### Boundary values, from the definitions -/

-- At `t = 0` no increment is summed: the realized variation is exactly `0`.
example {Ω : Type*} (ξ : ℕ → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ∑ j ∈ Finset.range ⌊(n : ℝ) * 0⌋₊, ξ n j ω ^ 2 = 0 := by simp

-- At `t = 1` row `n` sums all `n` increments.
example {Ω : Type*} (ξ : ℕ → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ∑ j ∈ Finset.range ⌊(n : ℝ) * 1⌋₊, ξ n j ω ^ 2 = ∑ j ∈ Finset.range n, ξ n j ω ^ 2 := by
  simp

-- Row `4` of `flatArray` at `t = 1/2`: two increments of square `1/4`, realized variation `1/2`.
example : ∑ j ∈ Finset.range ⌊((4 : ℕ) : ℝ) * (1 / 2)⌋₊, flatArray 4 j () ^ 2 = 1 / 2 := by
  rw [sum_flatArray_sq]
  norm_num

-- The maximum in the Hall–Heyde form includes the `i = 0` term, which is `|0| = 0`, so the
-- statistic is nonnegative.
example {Ω : Type*} (c ξ : ℕ → ℕ → Ω → ℝ) (K n : ℕ) (ω : Ω) :
    0 ≤ (Finset.range (K + 1)).sup' Finset.nonempty_range_add_one fun i =>
      |∑ j ∈ Finset.range i, (ξ n j ω ^ 2 - c n j ω)| :=
  (abs_nonneg _).trans (Finset.le_sup' (fun i => |∑ j ∈ Finset.range i,
    (ξ n j ω ^ 2 - c n j ω)|) (b := 0) (by simp))

end

end MathlibExtTest.Probability.Martingale.RealizedQV
