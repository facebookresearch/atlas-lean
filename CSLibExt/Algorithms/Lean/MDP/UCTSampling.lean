/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.UCT
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# UCT with fresh innovations

A sampler computes a joint successor/reward pair from the current state, action and one
innovation. Its noise law can be atomless. `Sampler.runLaw` uses the finite product law over
steps and episodes. The rollout reads one new coordinate on each descent, and backs up the
local discounted return on ascent, using the same `select` and `record` as the PMF model.

For measurability, a table produced by the algorithm can be queried at a *random* state:
this holds initially, and recording at one random key preserves it by measurable equality.
This does not require joint evaluation on the product space of all possible tables to be
measurable. States need not be countable. The ambient action type is finite with measurable
singletons, and availability of each action is measurable.

## Reference

Kocsis and Szepesvári, *Bandit based Monte-Carlo Planning*, ECML 2006, §§2.1–2.3 and Figure 1.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.MarkovDecision.UCT

open MeasureTheory
open scoped NNReal

variable {S A E X : Type*} [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace E]
  [MeasurableSpace X]

/-- A joint simulator driven by a fresh innovation. The two output coordinates need not be
independent. The distribution on innovations is supplied to `rolloutLaw` or `runLaw`. -/
structure Sampler (S A E : Type*) [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace E]
    extends Menu S A where
  sample : S → A → E → S × ℝ
  measurable_sample : Measurable (fun z : S × A × E => sample z.1 z.2.1 z.2.2)
  measurable_available (a : A) : MeasurableSet {s | a ∈ actions s}

instance : MeasurableSpace Stats :=
  MeasurableSpace.comap (fun u => (u.count, u.total)) inferInstance

theorem Stats.measurable_iff {f : X → Stats} : Measurable f ↔
    Measurable (fun x => (f x).count) ∧ Measurable (fun x => (f x).total) := by
  rw [show Measurable f ↔ Measurable (fun x => ((f x).count, (f x).total)) from
    measurable_comap_iff]
  exact ⟨fun h => ⟨h.fst, h.snd⟩, fun ⟨h, h'⟩ => h.prodMk h'⟩

/-- Measurability of lookup at a varying state and action, on a given sample space. This is
stronger than measurability of each fixed coordinate of a table. -/
def QueryMeasurable (T : X → Table S A) : Prop :=
  ∀ (d : ℕ) {s : X → S} {a : X → A}, Measurable s → Measurable a →
    Measurable fun x => T x d (s x) (a x)

namespace QueryMeasurable

theorem empty_table : QueryMeasurable (fun _ : X => (empty : Table S A)) :=
  fun _ _ _ _ _ => measurable_const

theorem measurable {T : X → Table S A} (hT : QueryMeasurable T) : Measurable T :=
  measurable_pi_iff.2 fun d => measurable_pi_iff.2 fun _ => measurable_pi_iff.2 fun _ =>
    hT d measurable_const measurable_const

theorem record [MeasurableEq S] [MeasurableEq A] {T : X → Table S A} (hT : QueryMeasurable T)
    (d : ℕ) {s : X → S} {a : X → A} {q : X → ℝ} (hs : Measurable s) (ha : Measurable a)
    (hq : Measurable q) : QueryMeasurable (fun x => UCT.record (T x) d (s x) (a x) (q x)) := by
  classical
  intro e t b ht hb
  have he : MeasurableSet {x | (e, t x, b x) = (d, s x, a x)} := by
    simp only [Prod.mk.injEq]
    exact (MeasurableSet.const _).inter ((measurableSet_eq_fun ht hs).inter
      (measurableSet_eq_fun hb ha))
  apply Measurable.ite he _ (hT e ht hb)
  obtain ⟨hc, hr⟩ := Stats.measurable_iff.mp (hT d hs ha)
  exact Stats.measurable_iff.mpr ⟨hc.add measurable_const, hr.add hq⟩

end QueryMeasurable

namespace Sampler

variable (P : Sampler S A E) [LinearOrder A]

/-- One path on a tape of `k` innovations. The first draw determines both the immediate
reward and the state passed to the tail of the tape. -/
noncomputable def rollout (c : ℝ≥0) (γ : ℝ) (T : Table S A) :
    (k : ℕ) → ℕ → S → (Fin k → E) → ℝ × Table S A
  | 0, _, _, _ => (0, T)
  | k + 1, d, s, w =>
      let a := select P.toMenu c T d s
      let z := P.sample s a (w 0)
      let child := rollout c γ T k (d + 1) z.1 (fun i => w i.succ)
      let q := z.2 + γ * child.1
      (q, record child.2 d s a q)

/-- The learned table after `n` episodes. Row `j` of the tape is used only for episode `j`;
all rows start at the same root and update the table learned from preceding rows. -/
noncomputable def run (c : ℝ≥0) (γ : ℝ) (H : ℕ) (root : S) :
    (n : ℕ) → (Fin n → Fin H → E) → Table S A
  | 0, _ => empty
  | n + 1, w => (P.rollout c γ (run c γ H root n (fun j => w j.castSucc)) H 0 root
      (w (Fin.last n))).2

variable {P} {c : ℝ≥0} {γ : ℝ} {T : Table S A}

private theorem preserves_before {k e d : ℕ} (h : e < d) (s x : S) (b : A) (w : Fin k → E) :
    (P.rollout c γ T k d s w).2 e x b = T e x b := by
  induction k generalizing d s with
  | zero => rfl
  | succ k ih =>
    exact (record_other _ _ (fun he => h.ne (congrArg Prod.fst he))).trans (ih (by omega) _ _)

/-- Every tape gives exactly `n` visits at the root after `n` positive-horizon episodes. -/
theorem run_visits_root {H n : ℕ} (root : S) (w : Fin n → Fin (H + 1) → E) :
    visits P.toMenu (P.run c γ (H + 1) root n w) 0 root = n := by
  induction n with
  | zero => simp [run, visits, empty]
  | succ n ih =>
    rw [run, rollout, visits_record (select_spec ..).1]
    congr 1
    unfold visits
    simp only [preserves_before (by decide : 0 < 0 + 1)]
    exact ih _

/-- A pathwise unit-scale hypothesis on all feasible suffix returns implies bounded totals
on every tape. `outcomes` here is the range of the joint simulator, not a set of positive-mass
singletons, which might be empty for a continuous reward. -/
theorem run_boundedTotals {H n : ℕ} (root : S) (w : Fin n → Fin H → E)
    (hs : ScaledReturns P.toMenu (fun s a => Set.range (P.sample s a)) γ H) :
    BoundedTotals (P.run c γ H root n w) := by
  have aux {T : Table S A} (ht : BoundedTotals T) {k : ℕ} (hk : k ≤ H) (d : ℕ) (s : S)
      (v : Fin k → E) : let r := P.rollout c γ T k d s v
        PossibleReturn P.toMenu (fun x a => Set.range (P.sample x a)) γ k s r.1 ∧
        BoundedTotals r.2 := by
    induction k generalizing d s with
    | zero => exact ⟨.zero _, ht⟩
    | succ k ih =>
      let a := select P.toMenu c T d s
      obtain ⟨hq, hu⟩ := ih (by omega) (d + 1) (P.sample s a (v 0)).1 (fun i => v i.succ)
      have hp := PossibleReturn.step (select_spec P.toMenu c T d s).1
        (Set.mem_range_self (v 0) : P.sample s a (v 0) ∈ Set.range (P.sample s a)) hq
      exact ⟨hp, hu.record _ (hs hk hp)⟩
  induction n with
  | zero => intro d s a; simp [run, empty]
  | succ n ih => exact (aux (ih _) le_rfl 0 root _).2

variable [Finite A]

private theorem measurable_select {U : X → Table S A} (hU : QueryMeasurable U) (d : ℕ)
    {s : X → S} (hs : Measurable s) : Measurable fun x => select P.toMenu c (U x) d (s x) := by
  classical
  let _ := Fintype.ofFinite A
  let clock x := visits P.toMenu (U x) d (s x)
  let f a x := priority c (clock x) (U x d (s x) a)
  have hav a : MeasurableSet {x | a ∈ P.actions (s x)} := hs (P.measurable_available a)
  have hstat a := Stats.measurable_iff.mp (hU d hs (measurable_const (a := a)))
  have ht : Measurable clock := by
    have h := Finset.measurable_sum (f := fun a x =>
      if a ∈ P.actions (s x) then (U x d (s x) a).count else 0) Finset.univ
      (fun a _ => Measurable.ite (hav a) (hstat a).1 measurable_const)
    simpa [clock, visits, Finset.sum_ite_mem] using h
  have hf a : Measurable (f a) := by
    have ⟨hc, hr⟩ := hstat a
    apply Measurable.ite (measurableSet_eq_fun hc measurable_const) measurable_const
    unfold Stats.mean
    fun_prop
  apply measurable_to_countable'
  intro a
  let wins (x : X) (a : A) := a ∈ P.actions (s x) ∧ ∀ b ∈ P.actions (s x),
    f b x ≤ f a x ∧ (f b x = f a x → a ≤ b)
  have hw x : wins x (select P.toMenu c (U x) d (s x)) := select_spec ..
  have he : (fun x => select P.toMenu c (U x) d (s x)) ⁻¹' {a} = {x | wins x a} := by
    ext x
    change select P.toMenu c (U x) d (s x) = a ↔ _
    constructor
    · rintro rfl; exact hw x
    · intro h
      have h₁ := (hw x).2 a h.1
      have h₂ := h.2 _ (hw x).1
      exact le_antisymm (h₁.2 (le_antisymm h₁.1 h₂.1)) (h₂.2 (le_antisymm h₂.1 h₁.1))
  rw [he]
  change MeasurableSet ({x | a ∈ P.actions (s x)} ∩ {x | ∀ b ∈ P.actions (s x),
    f b x ≤ f a x ∧ (f b x = f a x → a ≤ b)})
  apply (hav a).inter
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter fun b => (hav b).imp ((measurableSet_le (hf b) (hf a)).inter
    ((measurableSet_eq_fun (hf b) (hf a)).imp (MeasurableSet.const _)))

variable [MeasurableSingletonClass A] [MeasurableEq S]

/-- A rollout on measurable input has a measurable return and preserves measurable adaptive
lookup. The starting table is allowed to depend on earlier innovations. -/
theorem rollout_measurable {U : X → Table S A} (hU : QueryMeasurable U) (k d : ℕ)
    {s : X → S} (hs : Measurable s) {w : X → Fin k → E} (hw : Measurable w) :
    Measurable (fun x => (P.rollout c γ (U x) k d (s x) (w x)).1) ∧
      QueryMeasurable (fun x => (P.rollout c γ (U x) k d (s x) (w x)).2) := by
  induction k generalizing d s with
  | zero => exact ⟨measurable_const, hU⟩
  | succ k ih =>
    let a x := select P.toMenu c (U x) d (s x)
    let z x := P.sample (s x) (a x) (w x 0)
    have ha : Measurable a := measurable_select hU d hs
    have hz : Measurable z := P.measurable_sample.comp (hs.prodMk (ha.prodMk
      ((measurable_pi_iff.mp hw) 0)))
    obtain ⟨hq, hT⟩ := ih (d + 1) hz.fst (measurable_pi_iff.mpr
      (fun i : Fin k => measurable_pi_iff.mp hw i.succ))
    have hq' := hz.snd.add ((measurable_const (a := γ)).mul hq)
    exact ⟨hq', hT.record d hs ha hq'⟩

/-- After any number of episodes the learned table can be queried measurably even at a random
state, not just at deterministic coordinates. -/
theorem run_queryMeasurable (H n : ℕ) (root : S) {w : X → Fin n → Fin H → E} (hw : Measurable w) :
    QueryMeasurable fun x => P.run c γ H root n (w x) := by
  induction n with
  | zero => exact QueryMeasurable.empty_table
  | succ n ih =>
    have hu := ih (measurable_pi_iff.mpr (fun i : Fin n => measurable_pi_iff.mp hw i.castSucc))
    exact (rollout_measurable hu H 0 (measurable_const (a := root))
      (measurable_pi_iff.mp hw (Fin.last n))).2

variable (P c γ)

/-- Joint law of the return and updated statistics of one episode from the empty table. -/
noncomputable def rolloutLaw (μ : Measure E) [IsProbabilityMeasure μ] (H : ℕ) (root : S) :
    ProbabilityMeasure (ℝ × Table S A) := by
  have h := P.rollout_measurable (c := c) (γ := γ) QueryMeasurable.empty_table H 0
    (measurable_const (a := root)) (measurable_id (α := Fin H → E))
  refine ⟨(Measure.pi fun _ : Fin H => μ).map (P.rollout c γ empty H 0 root), ?_⟩
  exact (Measure.isProbabilityMeasure_map_iff (h.1.prodMk h.2.measurable).aemeasurable).2
    inferInstance

/-- The UCT table law: independent rows of independent innovations, pushed forward by the
adaptive sequence of root episodes. Only the innovations, not the learned tables, are iid. -/
noncomputable def runLaw (μ : Measure E) [IsProbabilityMeasure μ] (H n : ℕ) (root : S) :
    ProbabilityMeasure (Table S A) :=
  ⟨(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin H => μ).map (P.run c γ H root n),
    (Measure.isProbabilityMeasure_map_iff (P.run_queryMeasurable (c := c) (γ := γ) H n root
      measurable_id).measurable.aemeasurable).2 inferInstance⟩

/-- Under the general simulation law the root clock is almost surely the episode count. -/
theorem runLaw_visits_root (μ : Measure E) [IsProbabilityMeasure μ] (H n : ℕ) (root : S) :
    ∀ᵐ T ∂(P.runLaw c γ μ (H + 1) n root : Measure _), visits P.toMenu T 0 root = n := by
  have hf := (P.run_queryMeasurable (c := c) (γ := γ) (H + 1) n root measurable_id).measurable
  apply (ae_map_iff hf.aemeasurable (measurableSet_eq_fun _ measurable_const)).2
  · exact Filter.Eventually.of_forall (P.run_visits_root (c := c) (γ := γ) root)
  · exact Finset.measurable_sum _ fun a _ => (Stats.measurable_iff.mp
      ((measurable_pi_apply a).comp ((measurable_pi_apply root).comp (measurable_pi_apply 0)))).1

/-- With scaled suffix returns the empirical mean at any fixed key lies almost surely in `[0,1]`.
The stronger simultaneous, pathwise statement follows from `run_boundedTotals`. -/
theorem runLaw_mean_mem (μ : Measure E) [IsProbabilityMeasure μ] (H n : ℕ) (root : S)
    (hs : ScaledReturns P.toMenu (fun s a => Set.range (P.sample s a)) γ H)
    (d : ℕ) (s : S) (a : A) :
    ∀ᵐ T ∂(P.runLaw c γ μ H n root : Measure (Table S A)), (T d s a).mean ∈ Set.Icc (0 : ℝ) 1 := by
  have hf := (P.run_queryMeasurable (c := c) (γ := γ) H n root measurable_id).measurable
  have hm : Measurable (fun T : Table S A => (T d s a).mean) := by
    obtain ⟨hc, hr⟩ := Stats.measurable_iff.mp ((measurable_pi_apply a).comp
      ((measurable_pi_apply s).comp (measurable_pi_apply d)) :
      Measurable (fun T : Table S A => T d s a))
    apply hr.div
    fun_prop
  exact (ae_map_iff hf.aemeasurable (hm measurableSet_Icc)).2
    (Filter.Eventually.of_forall fun w => (P.run_boundedTotals (c := c) root w hs).mean_mem d s a)

end Sampler

end Cslib.Algorithms.Lean.MarkovDecision.UCT
