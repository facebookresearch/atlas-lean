/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.MachineLearning.PACLearning.Defs
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.MinMax
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Topology.UnitInterval

/-!
# The 1-nearest-neighbor rule

The rule predicts the label of the closest sample point, with ties broken by sample index alone.
See Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory to Algorithms*
(2014), §19.1 for the rule and §19.2.1 for the binary Bayes threshold.
-/

@[expose] public section

namespace Cslib.MachineLearning.PACLearning

open MeasureTheory

variable {X Y : Type*} {m : ℕ}

/-- The least index of a sample point minimizing the distance to `x` in a nonempty finite
sequence of points in a pseudometric space. -/
noncomputable def nearestNeighborIndex [PseudoMetricSpace X] [NeZero m]
    (points : Fin m → X) (x : X) : Fin m :=
  ((List.finRange m).argmin (fun i => dist x (points i))).getD 0

/-- An index is selected exactly when, for every index `j`, it is closer than `j`, or is at
the same distance and no later than `j`. The sample is a nonempty sequence in a pseudometric
space. -/
theorem nearestNeighborIndex_eq_iff [PseudoMetricSpace X] [NeZero m]
    (points : Fin m → X) (x : X) (i : Fin m) :
    nearestNeighborIndex points x = i ↔
      ∀ j, dist x (points i) < dist x (points j) ∨
        dist x (points i) = dist x (points j) ∧ i ≤ j := by
  let f (j : Fin m) := dist x (points j)
  have hne : (List.finRange m).argmin f ≠ none :=
    fun h => List.ne_nil_of_mem (List.mem_finRange (0 : Fin m)) (List.argmin_eq_none.mp h)
  have hget : ((List.finRange m).argmin f).getD 0 = i ↔
      (List.finRange m).argmin f = some i := by
    cases h : (List.finRange m).argmin f with
    | none => exact (hne h).elim
    | some j => simp
  change ((List.finRange m).argmin f).getD 0 = i ↔ _
  rw [hget, List.argmin_eq_some_iff]
  simp only [List.mem_finRange, List.idxOf_finRange, true_and, true_implies, Fin.val_fin_le]
  constructor
  · rintro ⟨hmin, hfirst⟩ j
    exact (hmin j).lt_or_eq.imp_right fun heq => ⟨heq, hfirst j heq.ge⟩
  · intro h
    refine ⟨fun j => (h j).elim le_of_lt fun hej => hej.1.le, fun j hj => ?_⟩
    exact (h j).elim (fun hlt => (not_lt_of_ge hj hlt).elim) And.right

/-- Selecting the least-index nearest neighbor among finitely many measurable points is
measurable as a function of a measurable query and those points. The space of points is a
second-countable pseudometric space with measurable open sets, and the sample is nonempty. -/
theorem measurable_nearestNeighborIndex {A : Type*} [MeasurableSpace A] [PseudoMetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [SecondCountableTopology X] [NeZero m]
    {points : Fin m → A → X}
    {query : A → X} (hp : ∀ i, Measurable (points i)) (hq : Measurable query) :
    Measurable fun a => nearestNeighborIndex (fun i => points i a) (query a) := by
  refine measurable_to_countable' fun i => ?_
  simp only [Set.preimage, Set.mem_singleton_iff, nearestNeighborIndex_eq_iff, Set.ofPred_forall,
    Set.ofPred_or, Set.ofPred_and]
  exact MeasurableSet.iInter fun j =>
    (measurableSet_lt (hq.dist (hp i)) (hq.dist (hp j))).union
      ((measurableSet_eq_fun (hq.dist (hp i)) (hq.dist (hp j))).inter
        (MeasurableSet.const (i ≤ j)))

/-- The 1-nearest-neighbor classifier returns the label at the least index whose sample point
is closest to the query. The sample is a nonempty sequence of point-label pairs. -/
noncomputable def oneNearestNeighbor [PseudoMetricSpace X] [NeZero m]
    (S : LabeledSample X Y m) (x : X) : Y :=
  (S (nearestNeighborIndex (fun i => (S i).1) x)).2

/-- The 1-nearest-neighbor prediction is jointly measurable in the nonempty sample and query.
The space of points is a second-countable pseudometric space with measurable open sets. -/
theorem measurable_oneNearestNeighbor [PseudoMetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [SecondCountableTopology X] [MeasurableSpace Y] [NeZero m] :
    Measurable (Function.uncurry (oneNearestNeighbor (X := X) (Y := Y) (m := m))) := by
  let idx (p : LabeledSample X Y m × X) := nearestNeighborIndex (fun i => (p.1 i).1) p.2
  have hidx : Measurable idx :=
    measurable_nearestNeighborIndex
      (fun i => measurable_fst.comp ((measurable_pi_apply i).comp measurable_fst)) measurable_snd
  intro s hs
  have heq : (Function.uncurry oneNearestNeighbor : LabeledSample X Y m × X → Y) ⁻¹' s =
      ⋃ i : Fin m, {p | idx p = i} ∩ {p | (p.1 i).2 ∈ s} := by
    ext p
    simp [Function.uncurry, oneNearestNeighbor, idx]
  rw [heq]
  exact MeasurableSet.iUnion fun i => (hidx (measurableSet_singleton i)).inter
    ((measurable_snd.comp ((measurable_pi_apply i).comp measurable_fst)) hs)

/-- For a probability law on examples with countable labels and measurable singletons, the real
0-1 risk of the 1-nearest-neighbor classifier is integrable over the nonempty i.i.d. sample.
The space of points is a second-countable pseudometric space with measurable open sets. -/
theorem integrable_oneNearestNeighbor_error [PseudoMetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [SecondCountableTopology X] [MeasurableSpace Y] [Countable Y]
    [MeasurableSingletonClass Y]
    [NeZero m] (D : Measure (X × Y)) [IsProbabilityMeasure D] :
    Integrable (fun S : LabeledSample X Y m => (error D (oneNearestNeighbor S)).toReal)
      (Measure.pi fun _ : Fin m => D) := by
  have hpred : Measurable (fun p : LabeledSample X Y m × (X × Y) =>
      oneNearestNeighbor p.1 p.2.1) :=
    measurable_oneNearestNeighbor.comp (measurable_fst.prodMk measurable_snd.fst)
  have hbad : MeasurableSet {p : LabeledSample X Y m × (X × Y) |
      oneNearestNeighbor p.1 p.2.1 ≠ p.2.2} :=
    (measurableSet_eq_fun hpred measurable_snd.snd).compl
  have hrisk : Measurable (fun S : LabeledSample X Y m =>
      (error D (oneNearestNeighbor S)).toReal) :=
    ENNReal.measurable_toReal.comp (measurable_measure_prodMk_left_finite (ν := D) hbad)
  refine Integrable.of_bound hrisk.aestronglyMeasurable 1 (.of_forall fun S => ?_)
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono (by simp) (prob_le_one : error D (oneNearestNeighbor S) ≤ 1)

/-- The binary Bayes threshold for a function `η : X → [0, 1]`: predict `true` (label 1) when
`η x > 1/2`, and `false` (label 0) otherwise, including at equality. -/
noncomputable def binaryBayesClassifier (η : X → unitInterval) (x : X) : Bool :=
  if 1 / 2 < (η x : ℝ) then true else false

/-- The binary Bayes threshold of a measurable function into `[0, 1]` is measurable. -/
theorem measurable_binaryBayesClassifier [MeasurableSpace X] {η : X → unitInterval}
    (hη : Measurable η) : Measurable (binaryBayesClassifier η) :=
  Measurable.ite (measurableSet_lt measurable_const (measurable_subtype_coe.comp hη))
    measurable_const measurable_const

end Cslib.MachineLearning.PACLearning
