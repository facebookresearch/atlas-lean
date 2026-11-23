/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Sufficiency.Ancillary

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.Sufficiency.Ancillary

open MeasureTheory

/-- Fixture A (use): a constant statistic is ancillary for the Bernoulli family. -/
example (P : Bool → ProbabilityMeasure Bool) :
    MathlibExt.Probability.Statistics.Sufficiency.IsAncillary P (fun _ : Bool => ()) := by
  exact MathlibExt.Probability.Statistics.Sufficiency.isAncillary_of_ae_const
    (c := ()) (fun θ => Filter.Eventually.of_forall fun _ => rfl) measurable_const

/-- Fixture B (use through preservation): a measurable function of a constant statistic is
ancillary. -/
example (P : Bool → ProbabilityMeasure Bool) (W : Unit → ℕ) (hW : Measurable W) :
    MathlibExt.Probability.Statistics.Sufficiency.IsAncillary P (W ∘ fun _ : Bool => ()) := by
  have hA : MathlibExt.Probability.Statistics.Sufficiency.IsAncillary P (fun _ : Bool => ()) :=
    MathlibExt.Probability.Statistics.Sufficiency.isAncillary_of_ae_const
      (c := ()) (fun θ => Filter.Eventually.of_forall fun _ => rfl) measurable_const
  exact hA.comp hW

/-- Fixture C (boundary): the identity statistic on the Bernoulli family is not ancillary —
the pushforwards at distinct parameters differ. -/
example (P : ℝ → ProbabilityMeasure Bool)
    (hP : ∀ p : Set.Ioo (0 : ℝ) 1, ((P p.val) : Measure Bool) {true} =
      ENNReal.ofReal p.val)
    (a b : Set.Ioo (0 : ℝ) 1) (hab : a.val ≠ b.val) :
    ¬ MathlibExt.Probability.Statistics.Sufficiency.IsAncillary P id := by
  intro hAnc
  obtain ⟨hm, heq⟩ := hAnc
  have h := heq a.val b.val
  simp only [Measure.map_id] at h
  have htrue := congrArg (fun μ : Measure Bool => μ {true}) h
  rw [hP a, hP b] at htrue
  have ha : (0 : ℝ) ≤ a.val := le_of_lt (Set.mem_Ioo.mp a.property).1
  have hb : (0 : ℝ) ≤ b.val := le_of_lt (Set.mem_Ioo.mp b.property).1
  rw [ENNReal.ofReal_eq_ofReal_iff ha hb] at htrue
  exact hab htrue

end MathlibExtTest.Probability.Statistics.Sufficiency.Ancillary
