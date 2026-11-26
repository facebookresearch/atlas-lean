/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.ValueIteration
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Finite-horizon UCT rollouts

`UCT.episode` samples a path, not the entire expectimax tree. Each recursive call binds a
fresh sample from the joint law of successor and reward at the selected state and action.
Thus these two outputs can be correlated, and later states can depend on earlier draws.
The boundary is a fixed horizon with zero terminal value. On return, each call records its
own immediate reward plus `γ` times its continuation return (`γ = 1` is undiscounted).
`UCT.episodes` restarts at the root with the resulting table, whose keys are depth, state
and action rather than the history leading to the state. The linear order of the actions
resolves ties, including among untried actions. No probability or convergence bound is implied.

## References

L. Kocsis and Cs. Szepesvári, *Bandit based Monte-Carlo Planning*, ECML 2006, pp. 282–293,
§§2.1–2.3. Figure 1 gives the rollout and backup; (1)–(2) give the UCB1 index, and the end of
§2.2 gives the exploration term used at each state and depth in §2.3.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.MarkovDecision.UCT

open scoped NNReal

variable {S A : Type*}

/-- The nonempty finite menu at each state, shared by stochastic and pathwise rollouts. -/
structure Menu (S A : Type*) where
  actions : S → Finset A
  nonempty (s : S) : (actions s).Nonempty

/-- A discrete generative interface: a joint probability mass function for one draw.
Only the laws at available actions are used. -/
structure Simulator (S A : Type*) extends Menu S A where
  draw : S → A → PMF (S × ℝ)

instance : Coe (Simulator S A) (Menu S A) := ⟨Simulator.toMenu⟩

/-- A finite stochastic MDP gives a simulator with its transition row as successor law and
its deterministic `reward s a` on every outcome. A general `Simulator` need not factor this way. -/
noncomputable def Simulator.ofMDP [Fintype S] [Fintype A] [Nonempty A]
    (M : MDP S A ℝ) (hM : M.Stochastic) : Simulator S A where
  actions _ := Finset.univ
  nonempty _ := Finset.univ_nonempty
  draw s a := (PMF.ofFintype (fun x => ENNReal.ofReal (M.prob s a x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun x _ => hM.1 s a x, hM.2, ENNReal.ofReal_one])).map
      fun x => (x, M.reward s a)

/-- Sufficient statistics of the suffix returns observed for one action at one node. -/
structure Stats where
  count : ℕ
  total : ℝ

/-- The empirical mean, totalized to zero at zero visits. -/
noncomputable def Stats.mean (u : Stats) : ℝ := u.total / u.count

/-- Incorporate one observed return. -/
def Stats.observe (u : Stats) (q : ℝ) : Stats := ⟨u.count + 1, u.total + q⟩

theorem Stats.mean_observe {u : Stats} (hu : u.count ≠ 0) (q : ℝ) :
    (u.observe q).mean = (u.count * u.mean + q) / (u.count + 1) := by
  simp [Stats.mean, Stats.observe, mul_div_cancel₀, hu]

/-- Statistics shared by all paths reaching the same depth and state. -/
abbrev Table (S A : Type*) := ℕ → S → A → Stats

/-- No visits and no accumulated return. -/
def empty : Table S A := fun _ _ _ => ⟨0, 0⟩

open Classical in
/-- Record an observation at exactly one key. -/
noncomputable def record (T : Table S A) (d : ℕ) (s : S) (a : A) (q : ℝ) : Table S A :=
  fun e x b => if (e, x, b) = (d, s, a) then (T d s a).observe q else T e x b

@[simp] theorem record_same (T : Table S A) (d : ℕ) (s : S) (a : A) (q : ℝ) :
    record T d s a q d s a = (T d s a).observe q := by classical simp [record]

theorem record_other (T : Table S A) {d e : ℕ} {s x : S} {a b : A} (q : ℝ)
    (h : (e, x, b) ≠ (d, s, a)) : record T d s a q e x b = T e x b := by
  classical simp [record, h]

variable (P : Menu S A)

/-- Node visits are the sum of action counts at this state and this depth. -/
def visits (T : Table S A) (d : ℕ) (s : S) : ℕ := ∑ a ∈ P.actions s, (T d s a).count

/-- Untried actions have priority over every real index. For a positive count the index is
empirical mean plus the UCT exploration term with local visit count `t`. -/
noncomputable def priority (c : ℝ≥0) (t : ℕ) (u : Stats) : WithTop ℝ :=
  if u.count = 0 then ⊤ else ↑(u.mean + 2 * (c : ℝ) * Real.sqrt (Real.log t / u.count))

variable [LinearOrder A]

/-- The least available action attaining maximal priority. The order is fixed across episodes. -/
noncomputable def select (c : ℝ≥0) (T : Table S A) (d : ℕ) (s : S) : A :=
  let f a := priority c (visits P T d s) (T d s a)
  ((P.actions s).filter (fun a => f a = (P.actions s).sup' (P.nonempty s) f)).min' (by
    obtain ⟨a, ha, he⟩ := Finset.exists_mem_eq_sup' (P.nonempty s) f
    exact ⟨a, Finset.mem_filter.mpr ⟨ha, he.symm⟩⟩)

/-- The chosen action is available, maximizes the index, and precedes every other maximizer. -/
theorem select_spec (c : ℝ≥0) (T : Table S A) (d : ℕ) (s : S) :
    let f a := priority c (visits P T d s) (T d s a)
    let a := select P c T d s
    a ∈ P.actions s ∧ ∀ b ∈ P.actions s, f b ≤ f a ∧ (f b = f a → a ≤ b) := by
  let f a := priority c (visits P T d s) (T d s a)
  let winners := (P.actions s).filter (fun a => f a = (P.actions s).sup' (P.nonempty s) f)
  have h : winners.Nonempty := by
    obtain ⟨a, ha, he⟩ := Finset.exists_mem_eq_sup' (P.nonempty s) f
    exact ⟨a, Finset.mem_filter.mpr ⟨ha, he.symm⟩⟩
  have hm := Finset.mem_filter.mp (Finset.min'_mem winners h)
  refine ⟨hm.1, fun b hb => ⟨(Finset.le_sup' f hb).trans_eq hm.2.symm, fun hba => ?_⟩⟩
  exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hb, hba.trans hm.2⟩)

variable (P : Simulator S A)

/-- One UCT episode with `k` steps left at depth `d`, returning its discounted reward and updated
statistics. The table is updated on unwinding, so the return observed at the child does not
include the incoming edge reward. -/
noncomputable def episode (c : ℝ≥0) (γ : ℝ) (T : Table S A) :
    ℕ → ℕ → S → PMF (ℝ × Table S A)
  | 0, _, _ => PMF.pure (0, T)
  | k + 1, d, s =>
      let a := select P c T d s
      (P.draw s a).bind fun z => (episode c γ T k (d + 1) z.1).map fun child =>
        let q := z.2 + γ * child.1
        (q, record child.2 d s a q)

/-- Law of the learned table after `n` episodes of horizon `H`. Each starts at depth zero in
`root`. Only the table, not a random seed or a previously drawn outcome, passes between episodes. -/
noncomputable def episodes (c : ℝ≥0) (γ : ℝ) (H : ℕ) (root : S) : ℕ → PMF (Table S A)
  | 0 => PMF.pure empty
  | n + 1 => (episodes c γ H root n).bind fun T => (episode P c γ T H 0 root).map Prod.snd

variable {P} {c : ℝ≥0} {γ : ℝ} {T : Table S A} {k d : ℕ} {s : S}

/-- In one supported step the very same joint draw supplies the child state and the incoming
reward. The backpropagated table differs from the child's at just the selected key. -/
theorem mem_support_episode_succ {out : ℝ × Table S A} :
    out ∈ (episode P c γ T (k + 1) d s).support ↔
      let a := select P c T d s
      ∃ z ∈ (P.draw s a).support, ∃ child ∈ (episode P c γ T k (d + 1) z.1).support,
        let q := z.2 + γ * child.1
        (q, record child.2 d s a q) = out := by
  simp only [episode, PMF.mem_support_bind_iff, PMF.mem_support_map_iff]

/-- Deeper recursive calls cannot modify an ancestor's statistics, even on a self-loop. -/
theorem episode_preserves_before {out : ℝ × Table S A} (ho : out ∈ (episode P c γ T k d s).support)
    {e : ℕ} (he : e < d) (x : S) (b : A) : out.2 e x b = T e x b := by
  induction k generalizing d s out with
  | zero => obtain rfl := (PMF.mem_support_pure_iff ..).mp ho; rfl
  | succ k ih =>
    obtain ⟨z, _, child, hc, rfl⟩ := mem_support_episode_succ.mp ho
    exact (record_other _ _ (fun h => he.ne (congrArg Prod.fst h))).trans
      (ih hc (by omega))

omit [LinearOrder A] in
theorem visits_record {P : Menu S A} {a : A} (ha : a ∈ P.actions s) (q : ℝ) :
    visits P (record T d s a q) d s = visits P T d s + 1 := by
  classical
  unfold visits
  have h b : (record T d s a q d s b).count = (T d s b).count + if b = a then 1 else 0 := by
    by_cases hb : b = a
    · subst b; simp [Stats.observe]
    · simp [record, hb]
  simp [h, Finset.sum_add_distrib, ha]

/-- A run of `n` nonempty episodes visits its designated root exactly `n` times. -/
theorem visits_root {H n : ℕ} {root : S} (hT : T ∈ (episodes P c γ (H + 1) root n).support) :
    visits P T 0 root = n := by
  induction n generalizing T with
  | zero => obtain rfl := (PMF.mem_support_pure_iff ..).mp hT; simp [visits, empty]
  | succ n ih =>
    obtain ⟨U, hU, hm⟩ := (PMF.mem_support_bind_iff ..).mp hT
    obtain ⟨out, ho, rfl⟩ := (PMF.mem_support_map_iff ..).mp hm
    obtain ⟨z, _, child, hc, rfl⟩ := mem_support_episode_succ.mp ho
    rw [visits_record (select_spec P c U 0 root).1]
    have he : child.2 0 root = U 0 root := funext (episode_preserves_before hc (by decide) root)
    simpa only [visits, he] using congrArg (· + 1) (ih hU)

/-- A possible discounted return under *any* sequence of available choices and supported draws.
This depends on the simulator and horizon, not on the UCT statistics or selection rule. -/
inductive PossibleReturn (P : Menu S A) (outcomes : S → A → Set (S × ℝ)) (γ : ℝ) :
    ℕ → S → ℝ → Prop where
  | zero (s : S) : PossibleReturn P outcomes γ 0 s 0
  | step {k s a z q} (ha : a ∈ P.actions s) (hz : z ∈ outcomes s a)
      (hq : PossibleReturn P outcomes γ k z.1 q) :
      PossibleReturn P outcomes γ (k + 1) s (z.2 + γ * q)

/-- The unit-range convention is on whole returns at each remaining horizon up to `H`,
not just on immediate rewards. -/
def ScaledReturns (P : Menu S A) (outcomes : S → A → Set (S × ℝ)) (γ : ℝ) (H : ℕ) : Prop :=
  ∀ ⦃k s q⦄, k ≤ H → PossibleReturn P outcomes γ k s q → q ∈ Set.Icc (0 : ℝ) 1

/-- The possible outputs of one discrete draw. -/
def Simulator.outcomes (P : Simulator S A) (s : S) (a : A) := (P.draw s a).support

/-- The sum of the returns at every key lies between zero and its number of visits. -/
def BoundedTotals (T : Table S A) : Prop :=
  ∀ d s a, (T d s a).total ∈ Set.Icc (0 : ℝ) (T d s a).count

omit [LinearOrder A] in
/-- Bounded totals put empirical means on the unit scale as well. -/
theorem BoundedTotals.mean_mem (hT : BoundedTotals T) (d : ℕ) (s : S) (a : A) :
    (T d s a).mean ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨hl, hu⟩ := hT d s a
  by_cases hz : (T d s a).count = 0
  · simp [Stats.mean, hz]
  · have hc : (0 : ℝ) < (T d s a).count := by exact_mod_cast Nat.pos_of_ne_zero hz
    exact ⟨div_nonneg hl hc.le, (div_le_one hc).2 hu⟩

omit [LinearOrder A] in
theorem BoundedTotals.record (hT : BoundedTotals T) (a : A) {q : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1) : BoundedTotals (record T d s a q) := by
  intro e x b
  by_cases h : (e, x, b) = (d, s, a)
  · obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj h |>.imp_right Prod.mk.inj
    simp only [record_same, Stats.observe, Nat.cast_add, Nat.cast_one]
    exact ⟨add_nonneg (hT _ _ _).1 hq.1, add_le_add (hT _ _ _).2 hq.2⟩
  · rw [record_other _ _ h]; exact hT _ _ _

private theorem episode_bounds {H : ℕ} (hscale : ScaledReturns P P.outcomes γ H) (hk : k ≤ H)
    (hT : BoundedTotals T) {out : ℝ × Table S A} (ho : out ∈ (episode P c γ T k d s).support) :
    PossibleReturn P P.outcomes γ k s out.1 ∧ BoundedTotals out.2 := by
  induction k generalizing d s out with
  | zero => obtain rfl := (PMF.mem_support_pure_iff ..).mp ho; exact ⟨.zero _, hT⟩
  | succ k ih =>
    obtain ⟨z, hz, child, hc, rfl⟩ := mem_support_episode_succ.mp ho
    obtain ⟨hq, ht⟩ := ih (by omega) hc
    have hp := PossibleReturn.step (select_spec P c T d s).1 hz hq
    exact ⟨hp, ht.record _ (hscale hk hp)⟩

/-- Under return scaling, every table in the law after any number of episodes has bounded totals. -/
theorem episodes_boundedTotals {H n : ℕ} {root : S} (hscale : ScaledReturns P P.outcomes γ H)
    (hT : T ∈ (episodes P c γ H root n).support) : BoundedTotals T := by
  induction n generalizing T with
  | zero => obtain rfl := (PMF.mem_support_pure_iff ..).mp hT; intro d s a; simp [empty]
  | succ n ih =>
    obtain ⟨U, hU, hm⟩ := (PMF.mem_support_bind_iff ..).mp hT
    obtain ⟨out, ho, rfl⟩ := (PMF.mem_support_map_iff ..).mp hm
    exact (episode_bounds hscale le_rfl (ih hU) ho).2

end Cslib.Algorithms.Lean.MarkovDecision.UCT
