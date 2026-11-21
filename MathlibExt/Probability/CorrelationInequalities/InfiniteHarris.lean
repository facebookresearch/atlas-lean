/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Configuration.CylinderDeriv
public import MathlibExt.Probability.CorrelationInequalities.Harris
public import MathlibExt.Probability.CorrelationInequalities.ReimerCompression

@[expose] public section

/-!
# Harris inequality on countable configuration spaces

For a countable set `E`, the Harris inequality for the product Bernoulli measure on
`ConfigSpace E = E → Bool` is reduced to the finite case: an event that depends only on the
coordinates in a finite set `F` is a cylinder over its section on `F`, and its probability is the
finite-dimensional probability of that section. Events that are decreasing limits of such events
are handled by continuity of measure.

## Main definitions

* `StatMech.ih_fill F η`: the configuration equal to `η` on `F` and closed (`false`) off `F`.
* `StatMech.ih_section A F`: the section of `A` on `F`, `{η | ih_fill F η ∈ A}`.

## Main results

* `StatMech.ih_eq_cylinder_of_dependsOn`: an event depending only on `F` is the cylinder over its
  section on `F`.
* `StatMech.ih_harris_of_finite_dependsOn`: the **Harris inequality** for increasing events that
  depend on finitely many coordinates.
* `StatMech.ih_harris_iInter_of_antitone`: positive correlation passes to decreasing limits.

See also `StatMech.eq_cylinder_restrict_image` in
`MathlibExt.Probability.Configuration.CylinderDeriv`,
which gives the same cylinder representation in terms of `Finset.restrict`.

## References

* T. E. Harris, *A lower bound for the critical probability in a certain percolation process*,
  Proc. Cambridge Philos. Soc. 56 (1960).
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace StatMech

variable {E : Type*} [Countable E] [DecidableEq E]

omit [Countable E] [DecidableEq E] in
/-- If the indicator of `A` depends only on the coordinates in `S` (Mathlib's `DependsOn`), so
does the event `A` (`StatMech.DependsOn`). -/
theorem ih_event_dependsOn_of_indicator {A : Set (ConfigSpace E)} {S : Set E}
    (h : _root_.DependsOn (A.indicator (fun _ => (1 : ℝ))) S) :
    StatMech.DependsOn A S := by
  intro omega omega' hagree
  have hi := h (x := omega) (y := omega') (fun e he => (hagree e he).symm)
  constructor
  · intro hw
    by_contra hw'
    rw [Set.indicator_of_mem hw, Set.indicator_of_notMem hw'] at hi
    norm_num at hi
  · intro hw'
    by_contra hw
    rw [Set.indicator_of_notMem hw, Set.indicator_of_mem hw'] at hi
    norm_num at hi

omit [Countable E] [DecidableEq E] in
/-- If the event `A` depends only on `S`, so does its indicator function. -/
theorem ih_indicator_dependsOn_of_event {A : Set (ConfigSpace E)} {S : Set E}
    (h : StatMech.DependsOn A S) :
    _root_.DependsOn (A.indicator (fun _ => (1 : ℝ))) S := by
  intro omega omega' hagree
  have hiff := h omega omega' (fun e he => (hagree e he).symm)
  by_cases hw : omega ∈ A
  · rw [Set.indicator_of_mem hw, Set.indicator_of_mem (hiff.mp hw)]
  · rw [Set.indicator_of_notMem hw,
      Set.indicator_of_notMem (fun hw' => hw (hiff.mpr hw'))]

omit [Countable E] [DecidableEq E] in
/-- Events depending only on `S` are closed under intersection. -/
theorem ih_dependsOn_inter {A B : Set (ConfigSpace E)} {S : Set E}
    (hA : StatMech.DependsOn A S) (hB : StatMech.DependsOn B S) :
    StatMech.DependsOn (A ∩ B) S := by
  intro omega omega' hagree
  simp only [Set.mem_inter_iff, hA omega omega' hagree, hB omega omega' hagree]

omit [Countable E] [DecidableEq E] in
/-- Events depending only on `S` are closed under arbitrary unions. -/
theorem ih_dependsOn_iUnion {ι : Sort*} {S : Set E} {A : ι → Set (ConfigSpace E)}
    (hA : ∀ i, StatMech.DependsOn (A i) S) :
    StatMech.DependsOn (⋃ i, A i) S := by
  intro omega omega' hagree
  simp only [Set.mem_iUnion]
  exact exists_congr (fun i => hA i omega omega' hagree)

/-- The configuration on `E` equal to `η` on the finite set `F` and closed (`false`) off `F`. -/
def ih_fill (F : Finset E) (eta : ConfigSpace F) : ConfigSpace E :=
  fun e => if h : e ∈ F then eta ⟨e, h⟩ else false

omit [Countable E] in
/-- `ih_fill F` is monotone. -/
theorem ih_fill_mono (F : Finset E) : Monotone (ih_fill F) := by
  intro eta eta' h e
  simp only [ih_fill]
  split
  · exact h _
  · exact le_rfl

/-- The section of an event `A` on `F`: the configurations `η` on `F` with `ih_fill F η ∈ A`. -/
def ih_section (A : Set (ConfigSpace E)) (F : Finset E) : Set (ConfigSpace F) :=
  {eta | ih_fill F eta ∈ A}

omit [Countable E] in
/-- The section of an increasing event is increasing. -/
theorem ih_section_isIncreasing {A : Set (ConfigSpace E)} (hA : IsIncreasing A)
    (F : Finset E) : IsIncreasing (ih_section A F) := by
  intro eta eta' h hmem
  exact hA (ih_fill_mono F h) hmem

omit [Countable E] in
/-- An event depending only on the coordinates in `F` is the cylinder over its section on `F`. -/
theorem ih_eq_cylinder_of_dependsOn {A : Set (ConfigSpace E)} (F : Finset E)
    (hA : DependsOn A (F : Set E)) :
    A = MeasureTheory.cylinder F (ih_section A F) := by
  ext omega
  change omega ∈ A ↔ ih_fill F (F.restrict omega) ∈ A
  exact hA omega (ih_fill F (F.restrict omega)) (by
    intro e he
    have heF : e ∈ F := he
    rw [ih_fill, dite_eq_left heF]
    rfl)

omit [DecidableEq E] in
/-- The **Harris inequality** on a countable configuration space for increasing events that
depend on finitely many coordinates: `P_p(A) * P_p(B) ≤ P_p(A ∩ B)`. -/
theorem ih_harris_of_finite_dependsOn {p : ℝ≥0} (hp : p ≤ 1)
    {A B : Set (ConfigSpace E)} (F : Finset E)
    (hAdep : DependsOn A (F : Set E)) (hBdep : DependsOn B (F : Set E))
    (hAinc : IsIncreasing A) (hBinc : IsIncreasing B) :
    (bernoulliProductMeasure (E := E) p hp).real A *
        (bernoulliProductMeasure (E := E) p hp).real B ≤
      (bernoulliProductMeasure (E := E) p hp).real (A ∩ B) := by
  classical
  let SA := ih_section A F
  let SB := ih_section B F
  have hAcyl : A = MeasureTheory.cylinder F SA :=
    ih_eq_cylinder_of_dependsOn F hAdep
  have hBcyl : B = MeasureTheory.cylinder F SB :=
    ih_eq_cylinder_of_dependsOn F hBdep
  rw [hAcyl, hBcyl]
  change (bernoulliProductMeasure (E := E) p hp).real
      (MeasureTheory.cylinder F SA) *
      (bernoulliProductMeasure (E := E) p hp).real
        (MeasureTheory.cylinder F SB) ≤
    (bernoulliProductMeasure (E := E) p hp).real
      (MeasureTheory.cylinder F (SA ∩ SB))
  rw [realProb_cylinder, realProb_cylinder, realProb_cylinder]
  exact harris_inequality hp (ih_section_isIncreasing hAinc F)
    (ih_section_isIncreasing hBinc F)

omit [Countable E] [DecidableEq E] in
/-- Positive correlation passes to limits of decreasing sequences of measurable events: if
`μ(A n) μ(B n) ≤ μ(A n ∩ B n)` for all `n`, the same holds for `⋂ n, A n` and `⋂ n, B n`. -/
theorem ih_harris_iInter_of_antitone
    (mu : Measure (ConfigSpace E)) [IsProbabilityMeasure mu]
    (A B : ℕ → Set (ConfigSpace E))
    (hAanti : Antitone A) (hBanti : Antitone B)
    (hAmeas : ∀ n, MeasurableSet (A n)) (hBmeas : ∀ n, MeasurableSet (B n))
    (hstage : ∀ n, mu.real (A n) * mu.real (B n) ≤ mu.real (A n ∩ B n)) :
    mu.real (⋂ n, A n) * mu.real (⋂ n, B n) ≤
      mu.real ((⋂ n, A n) ∩ (⋂ n, B n)) := by
  have hAt : Tendsto (fun n => mu.real (A n)) atTop (nhds (mu.real (⋂ n, A n))) := by
    have h := tendsto_measure_iInter_atTop (μ := mu)
      (fun n => (hAmeas n).nullMeasurableSet) hAanti ⟨0, measure_ne_top _ _⟩
    exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp h
  have hBt : Tendsto (fun n => mu.real (B n)) atTop (nhds (mu.real (⋂ n, B n))) := by
    have h := tendsto_measure_iInter_atTop (μ := mu)
      (fun n => (hBmeas n).nullMeasurableSet) hBanti ⟨0, measure_ne_top _ _⟩
    exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp h
  have hIanti : Antitone (fun n => A n ∩ B n) := fun n m hnm =>
    inter_subset_inter (hAanti hnm) (hBanti hnm)
  have hIt : Tendsto (fun n => mu.real (A n ∩ B n)) atTop
      (nhds (mu.real (⋂ n, A n ∩ B n))) := by
    have h := tendsto_measure_iInter_atTop (μ := mu)
      (fun n => ((hAmeas n).inter (hBmeas n)).nullMeasurableSet)
      hIanti ⟨0, measure_ne_top _ _⟩
    exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp h
  have hlim := le_of_tendsto_of_tendsto (hAt.mul hBt) hIt
    (Filter.Eventually.of_forall hstage)
  rw [iInter_inter_distrib] at hlim
  exact hlim

/-- Continuity from above of a finite measure, real-valued form: `μ.real (A n)` tends to
`μ.real (⋂ n, A n)` for a decreasing sequence of measurable sets. -/
theorem ih_tendsto_measureReal_iInter {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsFiniteMeasure mu]
    (A : ℕ → Set Ω) (hanti : Antitone A)
    (hmeas : ∀ n, MeasurableSet (A n)) :
    Tendsto (fun n => mu.real (A n)) atTop (nhds (mu.real (⋂ n, A n))) := by
  have h := tendsto_measure_iInter_atTop (μ := mu)
    (fun n => (hmeas n).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp h

end StatMech
