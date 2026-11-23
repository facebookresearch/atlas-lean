/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.MarkedCompensator

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
open MathlibExt.Probability.Statistics.CountingProcess.ContinuousTime

namespace MathlibExtTest.Probability.Statistics.MarkedCompensator

/-! ### T56's history is a single-jump history -/

section Censoring

variable {Ω : Type*} [MeasurableSpace Ω] {T C : Ω → ℝ}

omit [MeasurableSpace Ω] in
/-- The observed process `(N, Nᶜ)` sits at `(0, 0)` exactly before exit, from the definitions. -/
theorem observedProcess_eq_zero_iff (u : ℝ) (ω : Ω) :
    observedProcess T C u ω = (0, 0) ↔ u < obsTime T C ω := by
  unfold observedProcess countingProcess censoringProcess obsTime
  rcases le_or_gt (T ω) (C ω) with h | h
  · rw [min_eq_left h]
    by_cases hu : T ω ≤ u
    · simp [h, hu, not_lt.2 h, not_lt.2 hu]
    · simp [h, hu, not_lt.2 h, not_le.1 hu]
  · rw [min_eq_right h.le]
    by_cases hu : C ω ≤ u
    · simp [h, hu, not_le.2 h, not_lt.2 hu]
    · simp [h, hu, not_le.2 h, not_le.1 hu]

/-- `singleJumpHistory` of the observed process is T56's `historyFiltration`. -/
example (hT : Measurable T) (hC : Measurable C) :
    singleJumpHistory (fun u => (stronglyMeasurable_observedProcess hT hC u).measurable) =
      historyFiltration hT hC :=
  Filtration.ext rfl

/-- Hence T56's history satisfies all three filtration hypotheses through the single-jump
lemmas. -/
example (hT : Measurable T) (hC : Measurable C) (s t : ℝ) (B : Set Ω)
    (hB : MeasurableSet[historyFiltration hT hC t] B) :
    MeasurableSet[historyFiltration hT hC s] {ω | s < obsTime T C ω} ∧
      MeasurableSet[historyFiltration hT hC s] (B ∩ {ω | obsTime T C ω ≤ s}) := by
  have hZ := fun u => (stronglyMeasurable_observedProcess hT hC u).measurable
  have hX := measurableSet_lt_singleJumpHistory hZ observedProcess_eq_zero_iff
  refine ⟨hX s, ?_⟩
  refine measurableSet_inter_le_singleJumpHistory hZ
    (fun _ _ _ h1 h2 => observedProcess_of_obsTime_le h1 h2) (fun s => ?_) hB
  simpa only [compl_ofPred, not_lt] using (hX s).compl

end Censoring

/-! ### A marked filtration: failure time and a binary cause -/

/-- On `Ω = ℝ × Bool` (failure time, cause), `Z u = 0` before the failure and `1` or `2` (the
cause) from the failure on. -/
noncomputable def Zm (u : ℝ) (ω : ℝ × Bool) : ℕ := if ω.1 ≤ u then (if ω.2 then 2 else 1) else 0

theorem measurable_Zm (u : ℝ) : Measurable (Zm u) :=
  Measurable.ite (measurableSet_le measurable_fst measurable_const)
    ((measurable_from_top (f := fun b : Bool => if b then 2 else 1)).comp measurable_snd)
    measurable_const

theorem Zm_eq_zero_iff (u : ℝ) (ω : ℝ × Bool) : Zm u ω = 0 ↔ u < ω.1 := by
  by_cases h : ω.1 ≤ u
  · cases hb : ω.2 <;> simp [Zm, h, hb, not_lt.2 h]
  · simp [Zm, h, not_le.1 h]

theorem Zm_freeze (ω : ℝ × Bool) (s u : ℝ) (hs : ω.1 ≤ s) (hsu : s ≤ u) : Zm u ω = Zm s ω := by
  simp [Zm, hs, hs.trans hsu]

/-- The marked history `σ(Z u : u ≤ t)`. -/
local notation "ℱm" => singleJumpHistory (m0 := inferInstance) measurable_Zm

/-- The cause is learned at the failure: `{X ≤ s, J = true} = {Z s = 2}` is observed at `s`. -/
example (s : ℝ) : MeasurableSet[ℱm s] {ω : ℝ × Bool | ω.1 ≤ s ∧ ω.2 = true} := by
  have : {ω : ℝ × Bool | ω.1 ≤ s ∧ ω.2 = true} = Zm s ⁻¹' {2} := by
    ext ω
    by_cases h : ω.1 ≤ s
    · cases hb : ω.2 <;> simp [Zm, h, hb]
    · simp [Zm, h]
  rw [this]
  exact comap_le_singleJumpHistory measurable_Zm le_rfl _ ⟨{2}, trivial, rfl⟩

/-- **Boundary**: the cause is not observed before the failure. At time `0`, `{J = true}` is not
an event of the marked history: it meets `{X > 0}` (at `(1, true)`) without containing it
(`(1, false)`), so the "nothing learned before exit" lemma excludes it. -/
example : ¬ MeasurableSet[ℱm 0] {ω : ℝ × Bool | ω.2 = true} := by
  intro h
  rcases singleJumpHistory_inter_or_subset measurable_Zm (fun u ω => (Zm_eq_zero_iff u ω).2) h
    with h' | h'
  · have : ((1 : ℝ), true) ∈ {ω : ℝ × Bool | ω.2 = true} ∩ {ω | (0 : ℝ) < ω.1} := by simp
    rw [h'] at this
    exact this
  · have := h' (show ((1 : ℝ), false) ∈ {ω : ℝ × Bool | (0 : ℝ) < ω.1} by simp)
    simp at this

/-- The marked history satisfies `hX`, `hpast` and `hfut`. -/
example (s t : ℝ) (B : Set (ℝ × Bool)) (hB : MeasurableSet[ℱm t] B) :
    MeasurableSet[ℱm s] {ω : ℝ × Bool | s < ω.1} ∧
      (B ∩ {ω | t < ω.1} = ∅ ∨ {ω | t < ω.1} ⊆ B) ∧
      MeasurableSet[ℱm s] (B ∩ {ω | ω.1 ≤ s}) := by
  have hX := measurableSet_lt_singleJumpHistory measurable_Zm (X := Prod.fst) Zm_eq_zero_iff
  refine ⟨hX s, singleJumpHistory_inter_or_subset measurable_Zm
    (fun u ω => (Zm_eq_zero_iff u ω).2) hB, ?_⟩
  refine measurableSet_inter_le_singleJumpHistory measurable_Zm Zm_freeze (fun s => ?_) hB
  simpa only [compl_ofPred, not_lt] using (hX s).compl

/-! ### A deterministic marked jump: every hypothesis, from the definitions -/

/-- Exit at time `0`. -/
def Xd (_ : Unit) : ℝ := 0

/-- The history process: `0` before time `0`, `1` from time `0` on. -/
noncomputable def Zd (u : ℝ) (_ : Unit) : ℕ := if 0 ≤ u then 1 else 0

open Classical in
/-- The marked counting process with mark `true` at time `0`: `N(t, B) = 1{0 ≤ t, true ∈ B}`. -/
noncomputable def Nd (B : Set Bool) (t : ℝ) (_ : Unit) : ℝ := if 0 ≤ t ∧ true ∈ B then 1 else 0

/-- Its compensating random measure: `A(t) = δ_true` for `t ≥ 0`, `0` before. -/
noncomputable def Ad (t : ℝ) (_ : Unit) : Measure Bool := if 0 ≤ t then Measure.dirac true else 0

theorem measurable_Zd (u : ℝ) : Measurable (Zd u) := measurable_const' fun _ _ => rfl

theorem Zd_eq_zero_iff (u : ℝ) (ω : Unit) : Zd u ω = 0 ↔ u < Xd ω := by
  by_cases h : 0 ≤ u
  · simp [Zd, Xd, h, not_lt.2 h]
  · simp [Zd, Xd, h, not_le.1 h]

theorem Zd_freeze (ω : Unit) (s u : ℝ) (hs : Xd ω ≤ s) (hsu : s ≤ u) : Zd u ω = Zd s ω := by
  simp only [Xd] at hs
  simp [Zd, hs, hs.trans hsu]

local notation "ℱd" => singleJumpHistory (m0 := inferInstance) measurable_Zd

instance isFiniteMeasure_Ad (t : ℝ) (ω : Unit) : IsFiniteMeasure (Ad t ω) := by
  unfold Ad; split_ifs <;> infer_instance

/-- `A(t, B) = N(t, B)`, computed from the definitions. -/
theorem Ad_apply (B : Set Bool) (t : ℝ) (ω : Unit) : (Ad t ω B).toReal = Nd B t ω := by
  by_cases ht : 0 ≤ t
  · by_cases hB : true ∈ B <;> simp [Ad, Nd, ht, hB]
  · simp [Ad, Nd, ht]

theorem monotone_Nd (B : Set Bool) (ω : Unit) : Monotone fun t => Nd B t ω := by
  intro s s' h
  simp only [Nd]
  split_ifs with h1 h2 <;> first | exact absurd ⟨h1.1.trans h, h1.2⟩ h2 | norm_num

theorem continuousWithinAt_Nd (B : Set Bool) (ω : Unit) (t : ℝ) :
    ContinuousWithinAt (fun s => Nd B s ω) (Ici t) t := by
  have key : ∀ᶠ s in 𝓝[≥] t, Nd B s ω = Nd B t ω := by
    by_cases ht : 0 ≤ t
    · filter_upwards [self_mem_nhdsWithin] with s (hs : t ≤ s)
      simp only [Nd]
      by_cases hB : true ∈ B
      · rw [ite_eq_left ⟨ht.trans hs, hB⟩, ite_eq_left ⟨ht, hB⟩]
      · rw [ite_eq_right fun h => hB h.2, ite_eq_right fun h => hB h.2]
    · filter_upwards [Ico_mem_nhdsGE (not_le.1 ht)] with s hs
      simp only [Nd]
      rw [ite_eq_right fun h => not_le.2 hs.2 h.1, ite_eq_right fun h => ht h.1]
  exact continuousWithinAt_const.congr_of_eventuallyEq key rfl

theorem tendsto_Nd_atBot (B : Set Bool) (ω : Unit) :
    Tendsto (fun t => Nd B t ω) atBot (𝓝 0) :=
  (tendsto_const_nhds (x := (0 : ℝ))).congr'
    ((eventually_lt_atBot 0).mono fun s hs => by simp [Nd, not_le.2 hs])

theorem measurable_unit {m : MeasurableSpace Unit} (f : Unit → ℝ) : Measurable[m] f :=
  measurable_const' fun _ _ => rfl

/-- **Non-vacuity**: every hypothesis of `ae_forall_eq_of_isMarkedCompensator_singleJump` holds
for the deterministic marked jump, with `A = A' = Ad`. -/
example : ∀ᵐ ω ∂(Measure.dirac ()), ∀ t, Ad t ω = Ad t ω := by
  have hmart : ∀ B : Set Bool, MeasurableSet B →
      Martingale (fun t ω => Nd B t ω - (Ad t ω B).toReal) ℱd (Measure.dirac ()) := fun B _ => by
    have : (fun t ω => Nd B t ω - (Ad t ω B).toReal) = 0 := by
      funext t ω; simp [Ad_apply]
    rw [this]; exact martingale_zero _ _ _
  exact ae_forall_eq_of_isMarkedCompensator_singleJump measurable_Zd Zd_eq_zero_iff Zd_freeze
    (N := Nd) (fun t ω => inferInstance) (fun t ω => inferInstance) hmart hmart
    (fun _ _ _ => measurable_unit _) (fun _ _ _ => measurable_unit _)
    (fun B _ ω t => by simpa only [Ad_apply] using continuousWithinAt_Nd B ω t)
    (fun B _ ω t => by simpa only [Ad_apply] using continuousWithinAt_Nd B ω t)
    (fun B _ => ae_of_all _ fun ω => by
      simpa only [Ad_apply] using ((monotone_Nd B ω).monotoneOn univ).locallyBoundedVariationOn)
    (fun B _ => ae_of_all _ fun ω => by
      simpa only [Ad_apply] using ((monotone_Nd B ω).monotoneOn univ).locallyBoundedVariationOn)
    (fun B _ => ae_of_all _ fun ω => by simpa only [Ad_apply] using tendsto_Nd_atBot B ω)
    (fun B _ => ae_of_all _ fun ω => by simpa only [Ad_apply] using tendsto_Nd_atBot B ω)

/-- `2 • A` differs from `A` at time `0`, from the definitions. -/
theorem two_smul_Ad_ne : (2 : ℝ≥0∞) • Ad 0 () ≠ Ad 0 () := by
  intro h
  have := congrArg (fun μ : Measure Bool => μ univ) h
  simp [Ad] at this

/-- **The theorem has content.** `2 • A` is predictable, càdlàg, of finite variation and
normalized for every mark set, so if it compensated `N(·, B)` for every `B`, the theorem would
force `2 • A = A`, contradicting `two_smul_Ad_ne`. -/
example : ¬ ∀ B : Set Bool, MeasurableSet B →
    Martingale (fun t ω => Nd B t ω - (((2 : ℝ≥0∞) • Ad t ω) B).toReal) ℱd
      (Measure.dirac ()) := by
  intro hM
  have h2 : ∀ B t ω, (((2 : ℝ≥0∞) • Ad t ω) B).toReal = 2 * Nd B t ω := fun B t ω => by
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, Ad_apply]; norm_num
  have hmart : ∀ B : Set Bool, MeasurableSet B →
      Martingale (fun t ω => Nd B t ω - (Ad t ω B).toReal) ℱd (Measure.dirac ()) := fun B _ => by
    have : (fun t ω => Nd B t ω - (Ad t ω B).toReal) = 0 := by
      funext t ω; simp [Ad_apply]
    rw [this]; exact martingale_zero _ _ _
  have h := ae_forall_eq_of_isMarkedCompensator_singleJump measurable_Zd Zd_eq_zero_iff Zd_freeze
    (N := Nd) (A := Ad) (A' := fun t ω => (2 : ℝ≥0∞) • Ad t ω)
    (fun t ω => inferInstance)
    (fun t ω => ⟨by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top (by simp) (measure_lt_top _ _)⟩)
    hmart hM
    (fun _ _ _ => measurable_unit _) (fun _ _ _ => measurable_unit _)
    (fun B _ ω t => by simpa only [Ad_apply] using continuousWithinAt_Nd B ω t)
    (fun B _ ω t => by
      simp only [h2]
      exact ((continuous_const (y := (2 : ℝ))).mul continuous_id).continuousAt
        |>.comp_continuousWithinAt (continuousWithinAt_Nd B ω t))
    (fun B _ => ae_of_all _ fun ω => by
      simpa only [Ad_apply] using ((monotone_Nd B ω).monotoneOn univ).locallyBoundedVariationOn)
    (fun B _ => ae_of_all _ fun ω => by
      simpa only [h2] using (((monotone_Nd B ω).const_mul (by norm_num : (0 : ℝ) ≤ 2)).monotoneOn
        univ).locallyBoundedVariationOn)
    (fun B _ => ae_of_all _ fun ω => by simpa only [Ad_apply] using tendsto_Nd_atBot B ω)
    (fun B _ => ae_of_all _ fun ω => by
      simpa only [h2, mul_zero] using (tendsto_Nd_atBot B ω).const_mul 2)
  have h0 : ∀ t, Ad t () = (2 : ℝ≥0∞) • Ad t () := by
    by_contra hne
    have hnull := ae_iff.1 h
    have huniv : {ω : Unit | ¬ ∀ t, Ad t ω = (2 : ℝ≥0∞) • Ad t ω} = univ :=
      eq_univ_of_forall fun ω => by cases ω; exact hne
    rw [huniv, measure_univ] at hnull
    exact one_ne_zero hnull
  exact two_smul_Ad_ne (h0 0).symm

end MathlibExtTest.Probability.Statistics.MarkedCompensator
