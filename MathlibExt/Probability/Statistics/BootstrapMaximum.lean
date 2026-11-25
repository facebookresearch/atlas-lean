/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.BetaBinomialSampleRank
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Data.Fintype.BigOperators

/-!
# The bootstrap of the sample maximum fails

Bickel and Freedman's Counter-example 2 (P. J. Bickel and D. A. Freedman, "Some asymptotic
theory for the bootstrap", *Ann. Statist.* 9 (1981) 1196–1217, Section 6): for a sample from the
uniform law on `(0, θ)`, the pivot `n (θ - X_(n)) / θ` has a continuous (exponential) limit law,
but its bootstrap analogue `n (X_(n) - X*_(n))` vanishes with conditional probability
`1 - (1 - 1/n)^n → 1 - e⁻¹ ≈ 0.63`: the bootstrap maximum equals the sample maximum exactly when
the largest observation is drawn at least once.

A bootstrap sample of size `n + 1` from data `x : Fin (n + 1) → ℝ` is `x ∘ I` for a uniformly
random map `I : Fin (n + 1) → Fin (n + 1)`, so conditional probabilities are proportions of maps.

## Main results

* `card_resample_sup_eq`: for data with distinct values, exactly
  `(n + 1)^(n + 1) - n^(n + 1)` resampling maps reproduce the maximum.
* `bootstrap_prob_max_eq`: the conditional probability is `1 - (1 - 1/(n + 1))^(n + 1)`.
* `tendsto_bootstrap_prob_max`: it tends to `1 - e⁻¹`.
* `ae_bootstrap_prob_max_eq`: for i.i.d. data from an atomless law the identity holds almost
  surely.
-/

@[expose] public section

open Finset Filter Topology MeasureTheory

namespace MathlibExt.Probability.Statistics.BootstrapMaximum

/-- **Resamples that reproduce the maximum** (P. J. Bickel and D. A. Freedman, *Ann. Statist.* 9
(1981), Section 6, Counter-example 2). If the `n + 1` data values `x i` are distinct, the maps
`I : Fin (n + 1) → Fin (n + 1)` whose bootstrap sample `x ∘ I` has the same maximum as `x` are
exactly those that hit the index of the largest value, and there are
`(n + 1)^(n + 1) - n^(n + 1)` of them. -/
theorem card_resample_sup_eq (n : ℕ) (x : Fin (n + 1) → ℝ) (hx : Function.Injective x) :
    (univ.filter fun I : Fin (n + 1) → Fin (n + 1) =>
        univ.sup' univ_nonempty (fun j => x (I j)) = univ.sup' univ_nonempty x).card =
      (n + 1) ^ (n + 1) - n ^ (n + 1) := by
  obtain ⟨i₀, -, hi₀⟩ := exists_mem_eq_sup' (univ_nonempty (α := Fin (n + 1))) x
  have hiff : ∀ I : Fin (n + 1) → Fin (n + 1),
      univ.sup' univ_nonempty (fun j => x (I j)) = univ.sup' univ_nonempty x ↔
        ∃ j, I j = i₀ := by
    intro I
    rw [hi₀]
    constructor
    · intro h
      obtain ⟨j, -, hj⟩ := exists_mem_eq_sup' (univ_nonempty (α := Fin (n + 1)))
        (fun j => x (I j))
      exact ⟨j, hx (hj.symm.trans h)⟩
    · rintro ⟨j, hj⟩
      refine le_antisymm ?_ ?_
      · refine sup'_le _ _ fun k _ => ?_
        rw [← hi₀]
        exact le_sup' x (mem_univ _)
      · rw [← hj]
        exact le_sup' (fun j => x (I j)) (mem_univ j)
  have hcompl : (univ.filter fun I : Fin (n + 1) → Fin (n + 1) => ¬ ∃ j, I j = i₀) =
      Fintype.piFinset fun _ => univ.erase i₀ := by
    ext I
    simp [Fintype.mem_piFinset]
  have hsplit := card_filter_add_card_filter_not
    (s := (univ : Finset (Fin (n + 1) → Fin (n + 1)))) (fun I => ∃ j, I j = i₀)
  rw [hcompl, Fintype.card_piFinset, card_univ, Fintype.card_fun, Fintype.card_fin] at hsplit
  simp only [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, prod_const,
    Nat.add_sub_cancel] at hsplit
  rw [filter_congr fun I _ => hiff I]
  omega

/-- **Bootstrap probability that the maximum is reproduced** (P. J. Bickel and D. A. Freedman,
*Ann. Statist.* 9 (1981), Section 6, Counter-example 2). For `n + 1` distinct data values, the
proportion of the `(n + 1)^(n + 1)` resampling maps whose bootstrap maximum equals the sample
maximum, that is the conditional probability `P{X*_(n+1) = X_(n+1) | data}`, is
`1 - (1 - 1/(n + 1))^(n + 1)`. -/
theorem bootstrap_prob_max_eq (n : ℕ) (x : Fin (n + 1) → ℝ) (hx : Function.Injective x) :
    (((n + 1 : ℕ) : ℝ) ^ (n + 1))⁻¹ *
        ((univ.filter fun I : Fin (n + 1) → Fin (n + 1) =>
          univ.sup' univ_nonempty (fun j => x (I j)) = univ.sup' univ_nonempty x).card : ℝ) =
      1 - (1 - 1 / ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by
  rw [card_resample_sup_eq n x hx]
  have hle : n ^ (n + 1) ≤ (n + 1) ^ (n + 1) := Nat.pow_le_pow_left (Nat.le_succ n) _
  rw [Nat.cast_sub hle]
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have h1 : (1 - 1 / ((n + 1 : ℕ) : ℝ)) = (n : ℝ) / ((n + 1 : ℕ) : ℝ) := by
    field_simp
    push_cast
    ring
  rw [h1, div_pow]
  field_simp
  push_cast
  ring

/-- **The bootstrap of the maximum has an atom at `0` of mass `1 - e⁻¹`** (P. J. Bickel and
D. A. Freedman, *Ann. Statist.* 9 (1981), Section 6, Counter-example 2:
`P{n (X_(n) - X*_(n)) = 0 | F_n} → 1 - e⁻¹`). The bootstrap probability
`1 - (1 - 1/(n + 1))^(n + 1)` of `bootstrap_prob_max_eq` tends to `1 - e⁻¹`. -/
theorem tendsto_bootstrap_prob_max :
    Tendsto (fun n : ℕ => 1 - (1 - 1 / ((n + 1 : ℕ) : ℝ)) ^ (n + 1)) atTop
      (𝓝 (1 - Real.exp (-1))) := by
  have h := (Real.tendsto_one_add_div_pow_exp (-1)).comp (tendsto_add_atTop_nat 1)
  refine Tendsto.const_sub 1 ?_
  refine h.congr fun n => ?_
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  ring

/-- **Almost sure form for atomless data** (P. J. Bickel and D. A. Freedman, *Ann. Statist.* 9
(1981), Section 6, Counter-example 2, where the data are uniform on `(0, θ)`). For `n + 1`
i.i.d. observations from a law `ν` on `ℝ` without atoms, almost surely the bootstrap maximum
equals the sample maximum with conditional probability `1 - (1 - 1/(n + 1))^(n + 1)`. -/
theorem ae_bootstrap_prob_max_eq (n : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] :
    ∀ᵐ x ∂(Measure.pi fun _ : Fin (n + 1) => ν),
      (((n + 1 : ℕ) : ℝ) ^ (n + 1))⁻¹ *
          ((univ.filter fun I : Fin (n + 1) → Fin (n + 1) =>
            univ.sup' univ_nonempty (fun j => x (I j)) = univ.sup' univ_nonempty x).card : ℝ) =
        1 - (1 - 1 / ((n + 1 : ℕ) : ℝ)) ^ (n + 1) :=
  (MathlibExt.Probability.Distributions.BetaBinomialSampleRank.ae_injective_pi ν).mono
    fun x hx => bootstrap_prob_max_eq n x hx

end MathlibExt.Probability.Statistics.BootstrapMaximum
