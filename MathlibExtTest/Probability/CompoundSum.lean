/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.CompoundSum
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Independence.InfinitePi

/-! A count of zero or two and an independent sequence of signed, non-centred severities. -/

open MeasureTheory ProbabilityTheory MathlibExt.Probability

namespace MathlibExtTest.Probability.CompoundSum

private abbrev Ω := ℕ × (ℕ → ℝ)
private noncomputable abbrev half : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
private noncomputable abbrev counts := bernoulliMeasure (0 : ℕ) 2 half
private noncomputable abbrev sizes := bernoulliMeasure (-1 : ℝ) 3 half
private noncomputable abbrev seqLaw := Measure.infinitePi (fun _ : ℕ ↦ sizes)
private noncomputable abbrev P := counts.prod seqLaw
private abbrev X (i : ℕ) (ω : Ω) := ω.2 i
private noncomputable abbrev S (ω : Ω) := ∑ i ∈ Finset.range ω.1, X i ω

private theorem emptyPrefix (x : ℕ → ℝ) : S (0, x) = 0 := by simp [S]

-- Both summands matter: E[N] Var(X₀) = 4, while Var(N) E[X₀]² = 1.
private theorem signedTwoPoint_moments : MemLp S 2 P ∧ P[S] = 1 ∧ variance S P = 5 := by
  have hn : HasLaw (Prod.fst : Ω → ℕ) counts P := measurePreserving_fst.hasLaw
  have hs : HasLaw (Prod.snd : Ω → ℕ → ℝ) seqLaw P := measurePreserving_snd.hasLaw
  have hx (i : ℕ) : HasLaw (X i) sizes P :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ sizes) i).hasLaw.comp hs
  have hi : iIndepFun X P := (iIndepFun_iff_hasLaw_Pi_infinitePi hx hs.aemeasurable).2 hs
  have hnx : IndepFun (Prod.fst : Ω → ℕ) Prod.snd P := indepFun_prod measurable_id measurable_id
  let C (n : ℕ) := (n : ℝ)
  have mC : Measurable C := measurable_of_countable C
  have hn₂ : MemLp (fun ω : Ω ↦ C ω.1) 2 P := hn.memLp_comp <|
    (memLp_two_iff_integrable_sq mC.aestronglyMeasurable).2 (integrable_bernoulliMeasure ..)
  have hx₂ : MemLp (X 0) 2 P := (hx 0).memLp <|
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 (integrable_bernoulliMeasure ..)
  have hen : P[fun ω : Ω ↦ C ω.1] = 1 := by
    change P[C ∘ Prod.fst] = 1
    rw [hn.integral_comp mC.aestronglyMeasurable, integral_bernoulliMeasure]
    norm_num [half, C]
  have hex : P[X 0] = 1 := by rw [(hx 0).integral_eq, integral_bernoulliMeasure]; norm_num [half]
  have hvn : variance (fun ω : Ω ↦ C ω.1) P = 1 := by
    rw [variance_eq_sub hn₂, hen]
    change P[(fun n ↦ C n ^ 2) ∘ Prod.fst] - 1 ^ 2 = 1
    rw [hn.integral_comp (mC.pow_const 2).aestronglyMeasurable, integral_bernoulliMeasure]
    norm_num [half, C]
  have hvx : variance (X 0) P = 4 := by
    rw [variance_eq_sub hx₂, hex]
    change P[(fun x : ℝ ↦ x ^ 2) ∘ X 0] - 1 ^ 2 = 4
    rw [(hx 0).integral_comp (f := fun x : ℝ ↦ x ^ 2) (by fun_prop), integral_bernoulliMeasure]
    norm_num [half]
  have h := compoundSum_moments hn.aemeasurable hn₂ hx₂ hi (fun i ↦ (hx i).identDistrib (hx 0)) hnx
  refine ⟨h.1, h.2.1.trans ?_, h.2.2.trans ?_⟩
  · rw [hen, hex, mul_one]
  · rw [hen, hvx, hvn, hex]
    norm_num

end MathlibExtTest.Probability.CompoundSum
