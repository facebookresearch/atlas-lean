/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Mathlib
import Code.BeffaraDC.AnimalLLNas
import Code.Foundations.KingmanSigned

open MeasureTheory Filter Topology Finset
open StatMech.Kingman StatMech.KingmanAE StatMech.KingmanFilling StatMech.KingmanSigned

namespace StatMech

namespace BeffaraDC

variable {ρ : Measure ℝ}








noncomputable def signedAnimalValue (ω : ℤ → ℝ) (c : ℝ) (n : ℕ) : ℝ :=
  animalValue ω n - c * n


@[simp] theorem signedAnimalValue_zero (ω : ℤ → ℝ) (c : ℝ) : signedAnimalValue ω c 0 = 0 := by
  simp [signedAnimalValue, animalValue]




theorem signedAnimalValue_subadditive (ω : ℤ → ℝ) (c : ℝ) (m n : ℕ) :
    signedAnimalValue ω c (m + n)
      ≤ signedAnimalValue ω c m + signedAnimalValue (shiftEnv^[m] ω) c n := by
  have hsub := animalValue_subadditive ω m n
  simp only [signedAnimalValue, Nat.cast_add]
  linarith [hsub]


theorem measurable_signedAnimalValue (c : ℝ) (n : ℕ) :
    Measurable (fun ω : ℤ → ℝ => signedAnimalValue ω c n) := by
  simpa [signedAnimalValue] using (measurable_animalValue n).sub measurable_const



theorem integrable_signedAnimalValue [IsProbabilityMeasure ρ] (hρ : Integrable (id : ℝ → ℝ) ρ)
    (c : ℝ) (n : ℕ) :
    Integrable (fun ω : ℤ → ℝ => signedAnimalValue ω c n)
      (Measure.infinitePi (fun _ : ℤ => ρ)) := by
  simpa [signedAnimalValue] using (integrable_animalValue hρ n).sub (integrable_const (c * n))





theorem signedAnimalCocycle [IsProbabilityMeasure ρ] (hρ : Integrable (id : ℝ → ℝ) ρ) (c : ℝ) :
    SubadditiveCocycle shiftEnv (Measure.infinitePi (fun _ : ℤ => ρ))
      (fun n ω => signedAnimalValue ω c n) where
  measurePreserving := shiftEnv_measurePreserving ρ
  integrable := integrable_signedAnimalValue hρ c
  subadditive := fun m n =>
    Filter.Eventually.of_forall (fun ω => signedAnimalValue_subadditive ω c m n)




theorem expSeq_signedAnimalValue [IsProbabilityMeasure ρ] (hρ : Integrable (id : ℝ → ℝ) ρ)
    (c : ℝ) (n : ℕ) :
    SubadditiveCocycle.expSeq (fun n ω => signedAnimalValue ω c n)
        (Measure.infinitePi (fun _ : ℤ => ρ)) n
      = SubadditiveCocycle.expSeq (fun n ω => animalValue ω n)
          (Measure.infinitePi (fun _ : ℤ => ρ)) n - c * n := by
  unfold SubadditiveCocycle.expSeq
  simp only [signedAnimalValue]
  rw [integral_sub (integrable_animalValue hρ n) (integrable_const (c * n)), integral_const,
    probReal_univ, smul_eq_mul, one_mul]





theorem bddBelow_expSeq_signedAnimalValue [IsProbabilityMeasure ρ] (hρ : Integrable (id : ℝ → ℝ) ρ)
    (c : ℝ) :
    BddBelow (Set.range fun n => SubadditiveCocycle.expSeq
      (fun n ω => signedAnimalValue ω c n) (Measure.infinitePi (fun _ : ℤ => ρ)) n / n) := by
  refine ⟨min (-c) 0, ?_⟩
  rintro _ ⟨n, rfl⟩
  simp only []
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp only [Nat.cast_zero, div_zero]; exact min_le_right _ _
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [expSeq_signedAnimalValue hρ c n, sub_div, mul_div_assoc,
      div_self (ne_of_gt hn0), mul_one]
    have hanon : (0 : ℝ) ≤ SubadditiveCocycle.expSeq (fun n ω => animalValue ω n)
        (Measure.infinitePi (fun _ : ℤ => ρ)) n :=
      integral_nonneg_of_ae (animalValue_nonneg_ae n)
    have : (0 : ℝ) ≤ SubadditiveCocycle.expSeq (fun n ω => animalValue ω n)
        (Measure.infinitePi (fun _ : ℤ => ρ)) n / n := div_nonneg hanon (le_of_lt hn0)
    calc min (-c) 0 ≤ -c := min_le_left _ _
      _ ≤ SubadditiveCocycle.expSeq (fun n ω => animalValue ω n)
          (Measure.infinitePi (fun _ : ℤ => ρ)) n / n - c := by linarith














theorem signedAnimalValue_lln_ae [IsProbabilityMeasure ρ] (hρ : Integrable (id : ℝ → ℝ) ρ)
    (c : ℝ) :
    ∀ᵐ ω ∂(Measure.infinitePi (fun _ : ℤ => ρ)),
      Tendsto (fun n => signedAnimalValue ω c n / n) atTop
        (𝓝 (kingmanLimit shiftEnv (fun n ω => signedAnimalValue ω c n) ω)) :=
  kingman_ae_general (signedAnimalCocycle hρ c) (bddBelow_expSeq_signedAnimalValue hρ c)


theorem signedAnimalValue_div_eq (ω : ℤ → ℝ) (c : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    signedAnimalValue ω c n / n = animalValue ω n / n - c := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  simp only [signedAnimalValue, sub_div, mul_div_assoc, div_self hn0, mul_one]



theorem tendsto_signedAnimalValue_div_animalLimit [IsProbabilityMeasure ρ]
    (hρ : Integrable (id : ℝ → ℝ) ρ) (c : ℝ) :
    ∀ᵐ ω ∂(Measure.infinitePi (fun _ : ℤ => ρ)),
      Tendsto (fun n => signedAnimalValue ω c n / n) atTop (𝓝 (animalLimit ρ ω - c)) := by
  filter_upwards [animalValue_lln_ae hρ] with ω hω
  have heq : ∀ᶠ n in atTop, signedAnimalValue ω c n / n = animalValue ω n / n - c := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact signedAnimalValue_div_eq ω c hn
  rw [tendsto_congr' heq]
  exact (show animalLimit ρ ω = kingmanLimit shiftEnv (fun n ω => animalValue ω n) ω from rfl) ▸
    hω.sub_const c








theorem signedAnimalLimit_eq [IsProbabilityMeasure ρ] (hρ : Integrable (id : ℝ → ℝ) ρ) (c : ℝ) :
    ∀ᵐ ω ∂(Measure.infinitePi (fun _ : ℤ => ρ)),
      kingmanLimit shiftEnv (fun n ω => signedAnimalValue ω c n) ω = animalLimit ρ ω - c := by
  filter_upwards [signedAnimalValue_lln_ae hρ c, tendsto_signedAnimalValue_div_animalLimit hρ c]
    with ω h1 h2
  exact tendsto_nhds_unique h1 h2






theorem animalValue_lln_ae_via_signed [IsProbabilityMeasure ρ] (hρ : Integrable (id : ℝ → ℝ) ρ) :
    ∀ᵐ ω ∂(Measure.infinitePi (fun _ : ℤ => ρ)),
      Tendsto (fun n => animalValue ω n / n) atTop (𝓝 (animalLimit ρ ω)) := by
  filter_upwards [signedAnimalValue_lln_ae hρ 0, signedAnimalLimit_eq hρ 0] with ω h1 h2
  have heq : ∀ n, signedAnimalValue ω 0 n / n = animalValue ω n / n := by
    intro n; simp [signedAnimalValue]
  rw [h2, sub_zero] at h1
  simpa only [heq] using h1














theorem signedAnimalValue_eventually_pos_ae [IsProbabilityMeasure ρ]
    (hρ : Integrable (id : ℝ → ℝ) ρ) (c : ℝ) :
    ∀ᵐ ω ∂(Measure.infinitePi (fun _ : ℤ => ρ)),
      c < animalLimit ρ ω →
        ∀ᶠ n in atTop, 0 < signedAnimalValue ω c n := by
  filter_upwards [tendsto_signedAnimalValue_div_animalLimit hρ c] with ω hω hlt
  have hpos : (0 : ℝ) < animalLimit ρ ω - c := by linarith
  have hev : ∀ᶠ n in atTop, 0 < signedAnimalValue ω c n / n :=
    hω.eventually (eventually_gt_nhds hpos)
  filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
  have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [div_pos_iff] at hn
  rcases hn with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact h1
  · linarith






theorem signedAnimalValue_eventually_neg_ae [IsProbabilityMeasure ρ]
    (hρ : Integrable (id : ℝ → ℝ) ρ) (c : ℝ) :
    ∀ᵐ ω ∂(Measure.infinitePi (fun _ : ℤ => ρ)),
      animalLimit ρ ω < c →
        ∀ᶠ n in atTop, signedAnimalValue ω c n < 0 := by
  filter_upwards [tendsto_signedAnimalValue_div_animalLimit hρ c] with ω hω hlt
  have hneg : animalLimit ρ ω - c < 0 := by linarith
  have hev : ∀ᶠ n in atTop, signedAnimalValue ω c n / n < 0 :=
    hω.eventually (eventually_lt_nhds hneg)
  filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
  have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [div_neg_iff] at hn
  rcases hn with ⟨_, h2⟩ | ⟨h1, _⟩
  · linarith
  · exact h1

end BeffaraDC

end StatMech
