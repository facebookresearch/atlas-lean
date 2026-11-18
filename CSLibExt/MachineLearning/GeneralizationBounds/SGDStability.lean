/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GeneralizationBounds.Stability
public import MathlibExt.Analysis.Convex.Cocoercivity
public import Mathlib.Probability.UniformOn
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Uniform stability of stochastic gradient descent

The stochastic gradient method (SGM) on a sample `S = (z₁, …, zₙ)` runs
`w_{t+1} = w_t - α_t ∇_w ℓ(w_t, z_{i_t})`, where each index `i_t` is drawn uniformly from
`{1, …, n}` (the random selection rule). For losses that are convex, `β`-smooth and `L`-Lipschitz
in `w`, with steps `α_t ≤ 2 / β`, SGM run for `T` steps is uniformly stable with
`ε_stab ≤ (2 L² / n) ∑_{t < T} α_t` (M. Hardt, B. Recht and Y. Singer, *Train faster, generalize
better: stability of stochastic gradient descent*, ICML 2016, arXiv:1509.01240, Theorem 3.8).
Combined with `abs_integral_empiricalRisk_sub_risk_le` (their Theorem 2.2), the expected
generalization gap of SGM is at most the same quantity.

The proof couples the runs on two samples that differ in one example through the same index
sequence. When the selected example is shared, the two updates are the same non-expansive map
(`MathlibExt.Analysis.Convex.Cocoercivity.norm_gradientStep_sub_le`); otherwise both updates are
`α_t L`-bounded, and the distance grows by at most `2 α_t L` (the growth recursion, Lemma 2.5).
The second case happens at each step with probability `1 / n`.

## Main definitions

- `sgmIterate ℓ α w₀ S ι t`: the iterate `w_t` along the index sequence `ι`.
- `sgmOutput ℓ α w₀ S T κ`: the output `w_T` for a finite index sequence `κ : Fin T → Fin n`.
- `indexMeasure n T`: the law of `T` independent uniform indices.

## Main results

- `norm_sub_le_min_mul_add_two_mul`: the growth recursion for two different bounded updates.
- `norm_sgmIterate_sub_le`: the coupled distance along a fixed index sequence.
- `integral_abs_sgmOutput_sub_le`: Theorem 3.8 in the form `E_κ |ℓ(w_T, z) - ℓ(w'_T, z)| ≤ ε`.
- `isUniformlyStable_sgm`: SGM is uniformly stable in the sense of `IsUniformlyStable`, for the
  loss averaged over the index sequence.
- `norm_sgmIterate_sub_start_le`: the iterates stay within `L ∑ α_t` of the start.
- `abs_integral_empiricalRisk_sub_risk_sgm_le`: the resulting generalization bound, for a loss
  bounded at the starting point.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CSLibExt.MachineLearning.GeneralizationBounds

section GrowthRecursion

variable {E : Type*} [NormedAddCommGroup E]

/-- **Growth recursion for two bounded updates.** Let `G` be `η`-expansive
(`‖G v - G w‖ ≤ η ‖v - w‖`) and let `G` and `G'` be `σ`-bounded (`‖w - G w‖ ≤ σ` and
`‖w - G' w‖ ≤ σ` for all `w`). Then `‖G v - G' w‖ ≤ min η 1 * ‖v - w‖ + 2 σ`.

Source: M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of
stochastic gradient descent*, ICML 2016, arXiv:1509.01240, Lemma 2.5 (second case; the first case
`G = G'` is the definition of expansiveness). -/
theorem norm_sub_le_min_mul_add_two_mul {G G' : E → E} {η σ : ℝ}
    (hG : ∀ v w, ‖G v - G w‖ ≤ η * ‖v - w‖) (hσ : ∀ w, ‖w - G w‖ ≤ σ)
    (hσ' : ∀ w, ‖w - G' w‖ ≤ σ) (v w : E) :
    ‖G v - G' w‖ ≤ min η 1 * ‖v - w‖ + 2 * σ := by
  have h1 : ‖G v - G' w‖ ≤ ‖v - w‖ + 2 * σ := by
    have : G v - G' w = (v - w) - (v - G v) + (w - G' w) := by abel
    rw [this]
    calc ‖(v - w) - (v - G v) + (w - G' w)‖
        ≤ ‖(v - w) - (v - G v)‖ + ‖w - G' w‖ := norm_add_le _ _
      _ ≤ ‖v - w‖ + ‖v - G v‖ + ‖w - G' w‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ ‖v - w‖ + 2 * σ := by linarith [hσ v, hσ' w]
  have h2 : ‖G v - G' w‖ ≤ η * ‖v - w‖ + 2 * σ := by
    have : G v - G' w = (G v - G w) - (w - G w) + (w - G' w) := by abel
    rw [this]
    calc ‖(G v - G w) - (w - G w) + (w - G' w)‖
        ≤ ‖(G v - G w) - (w - G w)‖ + ‖w - G' w‖ := norm_add_le _ _
      _ ≤ ‖G v - G w‖ + ‖w - G w‖ + ‖w - G' w‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ η * ‖v - w‖ + 2 * σ := by linarith [hG v w, hσ w, hσ' w]
  rw [min_mul_of_nonneg _ _ (norm_nonneg _), one_mul]
  calc ‖G v - G' w‖ ≤ min (η * ‖v - w‖ + 2 * σ) (‖v - w‖ + 2 * σ) := le_min h2 h1
    _ = min (η * ‖v - w‖) ‖v - w‖ + 2 * σ := min_add_add_right _ _ _

end GrowthRecursion

variable {𝒵 E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Iterates of the stochastic gradient method.** Along an index sequence `ι`, `w₀` is given and
`w_{t+1} = w_t - α_t ∇_w ℓ(w_t, z_{ι t})`, where `z = S` is the sample and `ℓ w z` the loss of the
parameter `w` at the example `z`.

Source: M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of
stochastic gradient descent*, ICML 2016, arXiv:1509.01240, Section 3 (the update
`w_{t+1} = w_t - α_t ∇_w f(w_t; z_{i_t})`). -/
noncomputable def sgmIterate {n : ℕ} (ℓ : E → 𝒵 → ℝ) (α : ℕ → ℝ) (w₀ : E) (S : Fin n → 𝒵)
    (ι : ℕ → Fin n) : ℕ → E
  | 0 => w₀
  | t + 1 => sgmIterate ℓ α w₀ S ι t -
      α t • gradient (fun w => ℓ w (S (ι t))) (sgmIterate ℓ α w₀ S ι t)

/-- **Output of the stochastic gradient method.** The iterate `w_T` after `T` steps along the
finite index sequence `κ : Fin T → Fin n` (extended by `0` after step `T`, which does not affect
`w_T`).

Source: M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of
stochastic gradient descent*, ICML 2016, arXiv:1509.01240, Section 3. -/
noncomputable def sgmOutput {n : ℕ} [NeZero n] (ℓ : E → 𝒵 → ℝ) (α : ℕ → ℝ) (w₀ : E)
    (S : Fin n → 𝒵) (T : ℕ) (κ : Fin T → Fin n) : E :=
  sgmIterate ℓ α w₀ S (fun t => if h : t < T then κ ⟨t, h⟩ else 0) T

/-- **Random selection rule.** The law of `T` independent indices, each uniform on `Fin n`.

Source: M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of
stochastic gradient descent*, ICML 2016, arXiv:1509.01240, Section 3 ("pick `i_t ∈ {1, …, n}`
uniformly at random in each step"). -/
noncomputable def indexMeasure (n T : ℕ) : Measure (Fin T → Fin n) :=
  Measure.pi fun _ : Fin T => uniformOn (Set.univ : Set (Fin n))

instance {n T : ℕ} [NeZero n] : IsProbabilityMeasure (indexMeasure n T) := by
  unfold indexMeasure; infer_instance

/-- **Coupled distance of SGM along a fixed index sequence.** Let every loss `ℓ(·, z)` be convex,
differentiable, `L`-Lipschitz, with `β`-Lipschitz gradient, and let `0 ≤ α_t ≤ 2 / β`. Run SGM
from the same `w₀` on `S` and on `S' = Function.update S k z'` along the same index sequence `ι`.
Then after `t` steps `‖w_t - w'_t‖ ≤ ∑_{s < t, ι s = k} 2 α_s L`.

Source: M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of
stochastic gradient descent*, ICML 2016, arXiv:1509.01240, proof of Theorem 3.8 (Lemma 2.5 with
Lemmas 3.3 and 3.7.2, along a fixed realization of the indices). -/
theorem norm_sgmIterate_sub_le {n : ℕ} {ℓ : E → 𝒵 → ℝ} {β : ℝ} (hβ : 0 < β) {L : NNReal}
    (hconv : ∀ z, ConvexOn ℝ Set.univ fun w => ℓ w z)
    (hdiff : ∀ z, Differentiable ℝ fun w => ℓ w z)
    (hsmooth : ∀ z, LipschitzWith ⟨β, hβ.le⟩ (gradient fun w => ℓ w z))
    (hlip : ∀ z, LipschitzWith L fun w => ℓ w z) {α : ℕ → ℝ} (hα0 : ∀ t, 0 ≤ α t)
    (hα : ∀ t, α t ≤ 2 / β) (w₀ : E) (S : Fin n → 𝒵) (k : Fin n) (z' : 𝒵) (ι : ℕ → Fin n)
    (t : ℕ) :
    ‖sgmIterate ℓ α w₀ S ι t - sgmIterate ℓ α w₀ (Function.update S k z') ι t‖ ≤
      ∑ s ∈ Finset.range t, if ι s = k then 2 * α s * L else 0 := by
  induction t with
  | zero => simp [sgmIterate]
  | succ t ih =>
    rw [Finset.sum_range_succ]
    simp only [sgmIterate]
    set w := sgmIterate ℓ α w₀ S ι t
    set w' := sgmIterate ℓ α w₀ (Function.update S k z') ι t
    by_cases hk : ι t = k
    · have hif : (if ι t = k then 2 * α t * (L : ℝ) else 0) = 2 * α t * L := by simp [hk]
      rw [hif]
      have hb : ∀ (z : 𝒵) (u : E),
          ‖u - (u - α t • gradient (fun w => ℓ w z) u)‖ ≤ α t * L := by
        intro z u
        rw [sub_sub_cancel]
        exact MathlibExt.Analysis.Convex.Cocoercivity.norm_smul_gradient_le (hlip z) (hα0 t) u
      have h := norm_sub_le_min_mul_add_two_mul (E := E)
        (G := fun u => u - α t • gradient (fun w => ℓ w (S (ι t))) u)
        (G' := fun u => u - α t • gradient (fun w => ℓ w (Function.update S k z' (ι t))) u)
        (η := 1)
        (fun u v => by
          rw [one_mul]
          exact MathlibExt.Analysis.Convex.Cocoercivity.norm_gradientStep_sub_le hβ
            (hconv _) (hdiff _) (hsmooth _) (hα0 t) (hα t) u v)
        (hb _) (hb _) w w'
      simp only [min_self, one_mul] at h
      calc _ ≤ ‖w - w'‖ + 2 * (α t * L) := h
        _ ≤ _ := by linarith
    · simp only [hk, ↓reduceIte, add_zero]
      have hS : Function.update S k z' (ι t) = S (ι t) := Function.update_of_ne hk _ _
      rw [hS]
      exact (MathlibExt.Analysis.Convex.Cocoercivity.norm_gradientStep_sub_le hβ (hconv _)
        (hdiff _) (hsmooth _) (hα0 t) (hα t) w w').trans ih

/-- **Uniform stability of SGM for convex, smooth, Lipschitz losses.** Let every loss `ℓ(·, z)`
be convex, differentiable and `L`-Lipschitz on a real Hilbert space, with `β`-Lipschitz gradient
(`β > 0`), and let the steps satisfy `0 ≤ α_t ≤ 2 / β`. Let `S` and `S' = Function.update S k z'`
be samples of size `n ≥ 1` differing in one example, and let `w_T`, `w'_T` be the outputs of `T`
steps of SGM from the same `w₀` with the same `T` independent uniform indices. Then for every
test example `z`, `E |ℓ(w_T, z) - ℓ(w'_T, z)| ≤ (2 L² / n) ∑_{t < T} α_t`.

Source: M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of
stochastic gradient descent*, ICML 2016, arXiv:1509.01240, Theorem 3.8 (there with steps
`α_t > 0` indexed from `1` to `T`; the bound is proved in this form, inequality (3.3) with the
unrolled recursion (3.4)). -/
theorem integral_abs_sgmOutput_sub_le {n : ℕ} [NeZero n] {ℓ : E → 𝒵 → ℝ} {β : ℝ} (hβ : 0 < β)
    {L : NNReal} (hconv : ∀ z, ConvexOn ℝ Set.univ fun w => ℓ w z)
    (hdiff : ∀ z, Differentiable ℝ fun w => ℓ w z)
    (hsmooth : ∀ z, LipschitzWith ⟨β, hβ.le⟩ (gradient fun w => ℓ w z))
    (hlip : ∀ z, LipschitzWith L fun w => ℓ w z) {α : ℕ → ℝ} (hα0 : ∀ t, 0 ≤ α t)
    (hα : ∀ t, α t ≤ 2 / β) (w₀ : E) (T : ℕ) (S : Fin n → 𝒵) (k : Fin n) (z' z : 𝒵) :
    ∫ κ, |ℓ (sgmOutput ℓ α w₀ S T κ) z - ℓ (sgmOutput ℓ α w₀ (Function.update S k z') T κ) z|
        ∂(indexMeasure n T) ≤
      2 * (L : ℝ) ^ 2 / n * ∑ t ∈ Finset.range T, α t := by
  set P := indexMeasure n T
  -- pointwise bound along each index sequence
  have hpt : ∀ κ : Fin T → Fin n,
      |ℓ (sgmOutput ℓ α w₀ S T κ) z - ℓ (sgmOutput ℓ α w₀ (Function.update S k z') T κ) z| ≤
        ∑ t : Fin T, if κ t = k then 2 * α t * (L : ℝ) ^ 2 else 0 := by
    intro κ
    have hd := norm_sgmIterate_sub_le hβ hconv hdiff hsmooth hlip hα0 hα w₀ S k z'
      (fun t => if h : t < T then κ ⟨t, h⟩ else 0) T
    have hl := (hlip z).dist_le_mul (sgmOutput ℓ α w₀ S T κ)
      (sgmOutput ℓ α w₀ (Function.update S k z') T κ)
    rw [Real.dist_eq, dist_eq_norm] at hl
    unfold sgmOutput at hl ⊢
    refine hl.trans ?_
    rw [Finset.sum_range (fun s => if (if h : s < T then κ ⟨s, h⟩ else 0) = k
      then 2 * α s * (L : ℝ) else 0)] at hd
    calc (L : ℝ) * ‖_‖ ≤ L * ∑ t : Fin T,
          (if (if h : (t : ℕ) < T then κ ⟨t, h⟩ else 0) = k then 2 * α t * (L : ℝ) else 0) :=
          mul_le_mul_of_nonneg_left hd L.2
      _ = ∑ t : Fin T, if κ t = k then 2 * α t * (L : ℝ) ^ 2 else 0 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          simp only [Fin.is_lt, dite_true, Fin.eta]
          split_ifs <;> ring
  -- the probability that a given step selects index `k`
  have hprob : ∀ t : Fin T, P.real {κ | κ t = k} = 1 / n := by
    intro t
    have hmp := measurePreserving_eval (fun _ : Fin T => uniformOn (Set.univ : Set (Fin n))) t
    have : {κ : Fin T → Fin n | κ t = k} =
        (Function.eval t : (Fin T → Fin n) → Fin n) ⁻¹' ({k} : Set (Fin n)) := rfl
    rw [this, measureReal_def, ← Measure.map_apply (measurable_pi_apply t)
      (measurableSet_singleton k)]
    change ((Measure.pi fun _ : Fin T => uniformOn (Set.univ : Set (Fin n))).map
      (Function.eval t) {k}).toReal = 1 / n
    rw [hmp.map_eq, uniformOn_univ, Measure.count_singleton, Fintype.card_fin]
    simp [ENNReal.toReal_inv]
  calc ∫ κ, |ℓ (sgmOutput ℓ α w₀ S T κ) z - ℓ (sgmOutput ℓ α w₀ (Function.update S k z') T κ) z|
        ∂P ≤ ∫ κ, ∑ t : Fin T, (if κ t = k then 2 * α t * (L : ℝ) ^ 2 else 0) ∂P :=
        integral_mono Integrable.of_finite Integrable.of_finite hpt
    _ = ∑ t : Fin T, 2 * α t * (L : ℝ) ^ 2 * P.real {κ | κ t = k} := by
        rw [integral_finsetSum _ fun t _ => Integrable.of_finite]
        refine Finset.sum_congr rfl fun t _ => ?_
        have : (fun κ : Fin T → Fin n => if κ t = k then 2 * α t * (L : ℝ) ^ 2 else 0) =
            Set.indicator {κ | κ t = k} (fun _ => 2 * α t * (L : ℝ) ^ 2) := by
          ext κ; simp [Set.indicator]
        rw [this, integral_indicator_const _ (MeasurableSet.of_discrete), smul_eq_mul, mul_comm]
    _ = 2 * (L : ℝ) ^ 2 / n * ∑ t ∈ Finset.range T, α t := by
        simp only [hprob]
        rw [Finset.sum_range (fun t => α t), Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        ring

/-- **SGM is uniformly stable.** Under the hypotheses of `integral_abs_sgmOutput_sub_le`, the
algorithm that returns the sample itself, with the loss `L S z = E_κ ℓ(w_T(S, κ), z)` averaged over
the random selection rule, is `ε`-uniformly stable (`IsUniformlyStable`) with
`ε = (2 L² / n) ∑_{t < T} α_t`. This is uniform stability of the randomized algorithm SGM in the
sense of Definition 2.1, where the expectation is over the internal randomness.

Source: M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of
stochastic gradient descent*, ICML 2016, arXiv:1509.01240, Theorem 3.8 with Definition 2.1. -/
theorem isUniformlyStable_sgm {n : ℕ} [NeZero n] {ℓ : E → 𝒵 → ℝ} {β : ℝ} (hβ : 0 < β)
    {L : NNReal} (hconv : ∀ z, ConvexOn ℝ Set.univ fun w => ℓ w z)
    (hdiff : ∀ z, Differentiable ℝ fun w => ℓ w z)
    (hsmooth : ∀ z, LipschitzWith ⟨β, hβ.le⟩ (gradient fun w => ℓ w z))
    (hlip : ∀ z, LipschitzWith L fun w => ℓ w z) {α : ℕ → ℝ} (hα0 : ∀ t, 0 ≤ α t)
    (hα : ∀ t, α t ≤ 2 / β) (w₀ : E) (T : ℕ) :
    IsUniformlyStable (fun (S : Fin n → 𝒵) z => ∫ κ, ℓ (sgmOutput ℓ α w₀ S T κ) z
        ∂(indexMeasure n T)) id (2 * (L : ℝ) ^ 2 / n * ∑ t ∈ Finset.range T, α t) := by
  intro S k z' z
  simp only [id]
  rw [← integral_sub Integrable.of_finite Integrable.of_finite]
  refine le_trans (le_abs_self _) ?_
  refine (abs_integral_le_integral_abs).trans ?_
  have h := integral_abs_sgmOutput_sub_le hβ hconv hdiff hsmooth hlip hα0 hα w₀ T S k z' z
  calc ∫ κ, |ℓ (sgmOutput ℓ α w₀ (Function.update S k z') T κ) z -
          ℓ (sgmOutput ℓ α w₀ S T κ) z| ∂(indexMeasure n T)
      = ∫ κ, |ℓ (sgmOutput ℓ α w₀ S T κ) z -
          ℓ (sgmOutput ℓ α w₀ (Function.update S k z') T κ) z| ∂(indexMeasure n T) := by
        congr 1; ext κ; rw [abs_sub_comm]
    _ ≤ _ := h

/-- **SGM moves at most `L ∑ α_t` from its start.** If every loss `ℓ(·, z)` is `L`-Lipschitz and
the steps are nonnegative, then along every index sequence `‖w_t - w₀‖ ≤ L ∑_{s < t} α_s`, since
each gradient step moves the iterate by at most `α_s L`.

Source: M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of
stochastic gradient descent*, ICML 2016, arXiv:1509.01240, Lemma 3.3 (each gradient update is
`α L`-bounded), summed over the steps. -/
theorem norm_sgmIterate_sub_start_le {n : ℕ} {ℓ : E → 𝒵 → ℝ} {L : NNReal}
    (hlip : ∀ z, LipschitzWith L fun w => ℓ w z) {α : ℕ → ℝ} (hα0 : ∀ t, 0 ≤ α t) (w₀ : E)
    (S : Fin n → 𝒵) (ι : ℕ → Fin n) (t : ℕ) :
    ‖sgmIterate ℓ α w₀ S ι t - w₀‖ ≤ L * ∑ s ∈ Finset.range t, α s := by
  induction t with
  | zero => simp [sgmIterate]
  | succ t ih =>
    rw [Finset.sum_range_succ, mul_add]
    simp only [sgmIterate]
    have hstep := MathlibExt.Analysis.Convex.Cocoercivity.norm_smul_gradient_le
      (hlip (S (ι t))) (hα0 t) (sgmIterate ℓ α w₀ S ι t)
    calc ‖sgmIterate ℓ α w₀ S ι t - α t • gradient (fun w => ℓ w (S (ι t)))
            (sgmIterate ℓ α w₀ S ι t) - w₀‖
        = ‖(sgmIterate ℓ α w₀ S ι t - w₀) - α t • gradient (fun w => ℓ w (S (ι t)))
            (sgmIterate ℓ α w₀ S ι t)‖ := by congr 1; abel
      _ ≤ ‖sgmIterate ℓ α w₀ S ι t - w₀‖ + ‖α t • gradient (fun w => ℓ w (S (ι t)))
            (sgmIterate ℓ α w₀ S ι t)‖ := norm_sub_le _ _
      _ ≤ L * ∑ s ∈ Finset.range t, α s + L * α t := by linarith [mul_comm (α t) (L : ℝ)]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
private theorem abs_le_of_lipschitz_of_start {ℓ : E → 𝒵 → ℝ} {L : NNReal}
    (hlip : ∀ z, LipschitzWith L fun w => ℓ w z) {w₀ : E} {M : ℝ} (hbdd₀ : ∀ z, |ℓ w₀ z| ≤ M)
    {w : E} {D : ℝ} (hw : ‖w - w₀‖ ≤ D) (z : 𝒵) : |ℓ w z| ≤ M + L * D := by
  have h := (hlip z).dist_le_mul w w₀
  rw [Real.dist_eq, dist_eq_norm] at h
  have h1 : |ℓ w z| ≤ |ℓ w₀ z| + |ℓ w z - ℓ w₀ z| := by
    have := abs_add_le (ℓ w₀ z) (ℓ w z - ℓ w₀ z)
    rwa [add_sub_cancel] at this
  have h2 : (L : ℝ) * ‖w - w₀‖ ≤ L * D := mul_le_mul_of_nonneg_left hw L.2
  linarith [hbdd₀ z]

/-- **Generalization of SGM in expectation.** Let `ν` be a probability measure on the example
space and `S ~ ν^{⊗n}` an i.i.d. sample of size `n ≥ 1`. Under the hypotheses of
`integral_abs_sgmOutput_sub_le`, assume moreover that the loss is bounded at the starting point,
`|ℓ(w₀, z)| ≤ M` for every `z`, and that, for every index sequence `κ`, the map
`(S, z) ↦ ℓ(w_T(S, κ), z)` is jointly measurable. Then, with `R̂_S(w) = (1/n) ∑ᵢ ℓ(w, zᵢ)` and
`R(w) = E_z ℓ(w, z)`, `|E_{S, κ}[R̂_S(w_T) - R(w_T)]| ≤ (2 L² / n) ∑_{t < T} α_t`, stated with the
loss averaged over the index sequence as in `isUniformlyStable_sgm`. The bound at `w₀` makes every
loss along the run bounded by `M + L² ∑_{t < T} α_t` (`norm_sgmIterate_sub_start_le`), which is
what the expectations need; a bound on the whole space would force a convex loss to be constant.

Source: M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of
stochastic gradient descent*, ICML 2016, arXiv:1509.01240, Theorem 2.2 applied to Theorem 3.8
(the boundedness at `w₀` and measurability hypotheses are added so that the expectations are
defined). -/
theorem abs_integral_empiricalRisk_sub_risk_sgm_le [MeasurableSpace 𝒵] {ν : Measure 𝒵}
    [IsProbabilityMeasure ν] {n : ℕ} [NeZero n] {ℓ : E → 𝒵 → ℝ} {β : ℝ} (hβ : 0 < β)
    {L : NNReal} (hconv : ∀ z, ConvexOn ℝ Set.univ fun w => ℓ w z)
    (hdiff : ∀ z, Differentiable ℝ fun w => ℓ w z)
    (hsmooth : ∀ z, LipschitzWith ⟨β, hβ.le⟩ (gradient fun w => ℓ w z))
    (hlip : ∀ z, LipschitzWith L fun w => ℓ w z) {α : ℕ → ℝ} (hα0 : ∀ t, 0 ≤ α t)
    (hα : ∀ t, α t ≤ 2 / β) (w₀ : E) (T : ℕ) {M : ℝ} (hbdd₀ : ∀ z, |ℓ w₀ z| ≤ M)
    (hmeas : ∀ κ : Fin T → Fin n,
      Measurable fun p : (Fin n → 𝒵) × 𝒵 => ℓ (sgmOutput ℓ α w₀ p.1 T κ) p.2) :
    |∫ S, (empiricalRisk (fun (S : Fin n → 𝒵) z => ∫ κ, ℓ (sgmOutput ℓ α w₀ S T κ) z
          ∂(indexMeasure n T)) S S -
        risk (fun (S : Fin n → 𝒵) z => ∫ κ, ℓ (sgmOutput ℓ α w₀ S T κ) z
          ∂(indexMeasure n T)) ν S) ∂(Measure.pi fun _ : Fin n => ν)| ≤
      2 * (L : ℝ) ^ 2 / n * ∑ t ∈ Finset.range T, α t := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  refine abs_integral_empiricalRisk_sub_risk_le (A := id) hn ?_
    (M := M + L * (L * ∑ t ∈ Finset.range T, α t)) ?_
    (isUniformlyStable_sgm hβ hconv hdiff hsmooth hlip hα0 hα w₀ T)
  · simp only [id]
    have : (fun p : (Fin n → 𝒵) × 𝒵 => ∫ κ, ℓ (sgmOutput ℓ α w₀ p.1 T κ) p.2
        ∂(indexMeasure n T)) = fun p => ∑ κ : Fin T → Fin n,
          (indexMeasure n T).real {κ} • ℓ (sgmOutput ℓ α w₀ p.1 T κ) p.2 := by
      ext p; exact integral_fintype Integrable.of_finite
    rw [this]
    exact Finset.measurable_sum _ fun κ _ => by
      simp only [smul_eq_mul]; exact (hmeas κ).const_mul _
  · intro S z
    simp only [id]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ κ, |ℓ (sgmOutput ℓ α w₀ S T κ) z| ∂(indexMeasure n T)
        ≤ ∫ _κ, M + L * (L * ∑ t ∈ Finset.range T, α t) ∂(indexMeasure n T) :=
          integral_mono Integrable.of_finite (integrable_const _) fun κ =>
            abs_le_of_lipschitz_of_start hlip hbdd₀
              (norm_sgmIterate_sub_start_le hlip hα0 w₀ S _ T) z
      _ = M + L * (L * ∑ t ∈ Finset.range T, α t) := by simp

end CSLibExt.MachineLearning.GeneralizationBounds
