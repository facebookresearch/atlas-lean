/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# The Fisher–Neyman factorization theorem for discrete families

A statistical model with countable support is a family of probability mass functions
`P : Θ → PMF X` indexed by a parameter set `Θ`. A statistic `T : X → τ` is *sufficient* if
the conditional law of the observation given `T = t` is the same under every parameter that
gives `{T = t}` positive probability. Under `P θ`, the event `{T = T x}` has probability
`(P θ).map T (T x)`, so the conditional probability of `x` given `T = T x` is
`P θ x / (P θ).map T (T x)` (`IsSufficientPMF`). Parameters under which `{T = t}` is null
impose no condition, because the elementary conditional law is undefined there.

The factorization theorem characterizes sufficiency by the shape of the mass functions:
`T` is sufficient if and only if `P θ x = g θ (T x) * h x` for some nonnegative functions
`g` and `h` with `h` free of `θ`.

## Main results

* `IsSufficientPMF.factorization`: a sufficient statistic factorizes the mass functions, with
  `g θ t = P_θ(T = t)` and `h x` the common conditional probability of `x` given `T = T x`.
* `isSufficientPMF_of_factorization`: a factorization makes `T` sufficient.
* `isSufficientPMF_iff_exists_factorization`: the factorization theorem.

## References

* R. A. Fisher, *On the mathematical foundations of theoretical statistics*, Philos. Trans.
  Roy. Soc. London Ser. A 222 (1922), 309–368 (sufficiency).
* J. Neyman, *Su un teorema concernente le cosiddette statistiche sufficienti*, Giorn. Ist.
  Ital. Attuari 6 (1935), 320–334 (factorization).
* G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury (2002),
  Definition 6.2.1 and Theorem 6.2.6.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Sufficiency

open scoped ENNReal NNReal

variable {Θ X τ : Type*}

/-- A statistic `T : X → τ` is *sufficient* for the discrete family `P : Θ → PMF X` if the
conditional probability `P θ x / P_θ(T = T x)` of `x` given `T = T x` is the same under any
two parameters `θ, θ'` for which `{T = T x}` has positive probability. Here
`P_θ(T = t) = (P θ).map T t`. -/
def IsSufficientPMF (P : Θ → PMF X) (T : X → τ) : Prop :=
  ∀ θ θ' x, (P θ).map T (T x) ≠ 0 → (P θ').map T (T x) ≠ 0 →
    P θ x / (P θ).map T (T x) = P θ' x / (P θ').map T (T x)

/-- The probability of `x` is at most that of `{T = T x}`. -/
private theorem apply_le_map_apply (p : PMF X) (T : X → τ) (x : X) : p x ≤ p.map T (T x) := by
  rw [PMF.map_apply]
  refine le_trans (le_of_eq ?_) (ENNReal.le_tsum x)
  simp

/-- **Factorization, necessity.** If `T` is sufficient for `P`, then
`P θ x = g θ (T x) * h x` with `g θ t = P_θ(T = t)` and a parameter-free `h` with values in
`[0, 1]`. -/
theorem IsSufficientPMF.factorization {P : Θ → PMF X} {T : X → τ}
    (hT : IsSufficientPMF P T) :
    ∃ h : X → ℝ≥0, (∀ x, h x ≤ 1) ∧
      ∀ θ x, P θ x = (P θ).map T (T x) * (h x : ℝ≥0∞) := by
  classical
  let h : X → ℝ≥0 := fun x => if hx : ∃ θ, (P θ).map T (T x) ≠ 0 then
      (P hx.choose x / (P hx.choose).map T (T x)).toNNReal else 0
  refine ⟨h, fun x => ?_, fun θ x => ?_⟩
  · simp only [h]
    split_ifs with hx
    · have hle : P hx.choose x / (P hx.choose).map T (T x) ≤ 1 :=
        ENNReal.div_le_of_le_mul (by rw [one_mul]; exact apply_le_map_apply _ T x)
      exact (ENNReal.toNNReal_mono ENNReal.one_ne_top hle).trans_eq (by simp)
    · exact zero_le_one
  · by_cases hθ : (P θ).map T (T x) = 0
    · have h0 : P θ x = 0 := le_zero_iff.mp (hθ ▸ apply_le_map_apply _ T x)
      rw [h0, hθ, zero_mul]
    · have hx : ∃ θ, (P θ).map T (T x) ≠ 0 := ⟨θ, hθ⟩
      simp only [h, hx, ↓reduceDIte]
      rw [ENNReal.coe_toNNReal (ENNReal.div_ne_top (PMF.apply_ne_top _ _) hx.choose_spec),
        ← hT θ hx.choose x hθ hx.choose_spec, ENNReal.mul_div_cancel hθ (PMF.apply_ne_top _ _)]

/-- **Factorization, sufficiency.** If `P θ x = g θ (T x) * h x` for nonnegative real `g`, `h`
with `h` free of `θ`, then `T` is sufficient for `P`. -/
theorem isSufficientPMF_of_factorization {P : Θ → PMF X} {T : X → τ} (g : Θ → τ → ℝ≥0)
    (h : X → ℝ≥0) (hP : ∀ θ x, P θ x = ((g θ (T x) * h x : ℝ≥0) : ℝ≥0∞)) :
    IsSufficientPMF P T := by
  classical
  have hmap : ∀ θ x, (P θ).map T (T x) =
      (g θ (T x) : ℝ≥0∞) * ∑' y, if T x = T y then (h y : ℝ≥0∞) else 0 := by
    intro θ x
    rw [PMF.map_apply, ← ENNReal.tsum_mul_left]
    congr 1
    ext y
    split_ifs with hy
    · rw [hP, hy, ENNReal.coe_mul]
    · rw [mul_zero]
  intro θ θ' x hθ hθ'
  have hg : ∀ θ, (P θ).map T (T x) ≠ 0 → (g θ (T x) : ℝ≥0∞) ≠ 0 := fun θ hne h0 =>
    hne (by rw [hmap, h0, zero_mul])
  rw [hP θ, hP θ', hmap θ, hmap θ', ENNReal.coe_mul, ENNReal.coe_mul,
    ENNReal.mul_div_mul_left _ _ (hg θ hθ) ENNReal.coe_ne_top,
    ENNReal.mul_div_mul_left _ _ (hg θ' hθ') ENNReal.coe_ne_top]

/-- **The Fisher–Neyman factorization theorem** (discrete case). A statistic `T` is sufficient
for the family of mass functions `P` if and only if there are nonnegative functions `g` and
`h`, with `h` free of the parameter, such that `P θ x = g θ (T x) * h x` for every `θ`, `x`.

Source: Neyman (1935); Casella–Berger, Theorem 6.2.6. -/
theorem isSufficientPMF_iff_exists_factorization (P : Θ → PMF X) (T : X → τ) :
    IsSufficientPMF P T ↔ ∃ (g : Θ → τ → ℝ≥0) (h : X → ℝ≥0),
      ∀ θ x, P θ x = ((g θ (T x) * h x : ℝ≥0) : ℝ≥0∞) := by
  refine ⟨fun hT => ?_, fun ⟨g, h, hP⟩ => isSufficientPMF_of_factorization g h hP⟩
  obtain ⟨h, -, hP⟩ := hT.factorization
  refine ⟨fun θ t => ((P θ).map T t).toNNReal, h, fun θ x => ?_⟩
  rw [ENNReal.coe_mul, ENNReal.coe_toNNReal (PMF.apply_ne_top _ _), hP θ x]

end MathlibExt.Probability.Statistics.Sufficiency
