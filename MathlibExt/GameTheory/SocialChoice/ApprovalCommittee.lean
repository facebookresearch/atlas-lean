/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.List.MinMax
public import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Approval-based committee elections and justified representation

An approval-based committee election has a finite set of voters, a finite set `C` of
candidates, an approval ballot `A i ⊆ C` for each voter `i`, and a committee size `k`; a
committee is a set of `k` candidates. This file defines the rules AV, SAV, PAV, MAV and GreedyAV
and the axiom of justified representation (JR), and proves the JR results of Aziz et al. for
GreedyAV, AV, SAV and MAV.

## Main definitions

* `ProvidesJR A k W`: the committee `W` provides justified representation for `(A, k)`
  (Definition 1).
* `IsAVCommittee`, `IsSAVCommittee`, `IsPAVCommittee`, `IsMAVCommittee`: `W` is a winning
  committee of AV, SAV, PAV or MAV before tie-breaking (Section 2.1).
* `IsGreedyAVRun A j W`: some run of GreedyAV reaches `W` after `j` rounds (Section 2.1);
  `greedyAV` is GreedyAV with ties broken toward the least candidate.
* `uncoveredSupport A W c` and `checkJR`: the number `s(c)` and the JR check from the paragraph
  before Theorem 2.

## Main results

* `providesJR_iff_forall_mul_uncoveredSupport_lt` and `checkJR_eq_true_iff`: the criterion
  `k * s(c) < n` for JR (the source's `s(c) < n / k`, for positive `k`) and the correctness
  of the check.
* `IsGreedyAVRun.providesJR`: with at least one voter, GreedyAV satisfies JR (Theorem 1).
* `exists_isAVCommittee_two_providesJR`, `isAVCommittee_avTieProfile_not_providesJR` and
  `isAVCommittee_avProfile_iff_and_not_providesJR`: with at least one voter and `k = 2`, AV
  satisfies JR when ties are
  broken in favor of committees that provide JR and can fail it otherwise; for every `k ≥ 3`,
  AV fails JR (Theorem 3).
* `isSAVCommittee_savProfile_iff_and_not_providesJR` and
  `mavProfile_isMAVCommittee_not_providesJR`: SAV and MAV fail JR for every `k ≥ 2`
  (Theorem 4).

## Conventions

Voters form a finite type `V`, so `n = Fintype.card V`. A ballot is any `Finset` of candidates,
possibly empty; a committee is a `Finset C`, and the rule predicates require cardinality `k`.
The JR threshold is the product form `n ≤ k * |N|`, which for positive `k` is the source's
rational comparison `|N| ≥ n / k`; natural-number division would make Theorem 1 false.
Where the source's formulas are undefined,
an empty ballot contributes `0` to the SAV score, and the MAV score with no voters is `0`.

## References

* H. Aziz, M. Brill, V. Conitzer, E. Elkind, R. Freeman and T. Walsh, *Justified representation
  in approval-based committee voting*, Social Choice and Welfare 48 (2017); arXiv:1407.8269.
  Section 2.1, Definition 1, Theorems 1, 3 and 4, and the paragraph before Theorem 2.
-/

@[expose] public section

namespace MathlibExt.GameTheory.SocialChoice.ApprovalCommittee

variable {V C : Type*} [Fintype V]

/-! ### Justified representation (Definition 1) -/

/-- `W` provides justified representation for `(A, k)` (Definition 1): there is no group `N` of
voters with `n ≤ k * |N|` (the source's `|N| ≥ n / k`, for positive `k`) whose ballots have a
common candidate while no
member of `N` approves a member of `W`. Definition 1 is stated for voters `N = {1, …, n}` and a
committee with `|W| = k ≥ 1`, where this predicate agrees with it; the predicate is defined for
every `W` and `k`. The empty group is not excluded: it violates the condition exactly when there
are no voters and at least one candidate. -/
def ProvidesJR (A : V → Finset C) (k : ℕ) (W : Finset C) : Prop :=
  ¬ ∃ N : Finset V, Fintype.card V ≤ k * N.card ∧ (∃ c, ∀ i ∈ N, c ∈ A i) ∧
      ∀ i ∈ N, Disjoint (A i) W

section Rules

variable [DecidableEq C]

/-! ### Approval-based rules (Section 2.1) -/

/-- The approval score `|{i ∈ N | c ∈ A i}|` of the candidate `c`. -/
def approvalScore (A : V → Finset C) (c : C) : ℕ :=
  (Finset.univ.filter fun i => c ∈ A i).card

/-- The AV score `∑_{c ∈ W} |{i ∈ N | c ∈ A i}|` of the candidate set `W`. -/
def avScore (A : V → Finset C) (W : Finset C) : ℕ :=
  ∑ c ∈ W, approvalScore A c

/-- The AV score counts approvals voter by voter: it is `∑_i |A i ∩ W|`. -/
theorem avScore_eq_sum_card_inter (A : V → Finset C) (W : Finset C) :
    avScore A W = ∑ i, (A i ∩ W).card := by
  unfold avScore approvalScore
  simp only [Finset.card_filter]
  conv_rhs => arg 2; ext i; rw [Finset.inter_comm (A i) W, ← Finset.filter_mem_eq_inter,
    Finset.card_filter]
  exact Finset.sum_comm

/-- `W` is an AV committee for `(A, k)`: `|W| = k` and no `k`-subset of the candidates has a
larger AV score. Ties are not broken: a tie-breaking rule chooses one of the AV committees. -/
def IsAVCommittee (A : V → Finset C) (k : ℕ) (W : Finset C) : Prop :=
  W.card = k ∧ ∀ W' : Finset C, W'.card = k → avScore A W' ≤ avScore A W

/-- The SAV score `∑_i |W ∩ A i| / |A i|` of `W`. Because `x / 0 = 0` in `ℚ`, a voter with an
empty ballot contributes `0`; the source's formula is undefined for such a voter. -/
def savScore (A : V → Finset C) (W : Finset C) : ℚ :=
  ∑ i, ((W ∩ A i).card : ℚ) / (A i).card

/-- `W` is an SAV committee for `(A, k)`: `|W| = k` and no `k`-subset has a larger SAV score. -/
def IsSAVCommittee (A : V → Finset C) (k : ℕ) (W : Finset C) : Prop :=
  W.card = k ∧ ∀ W' : Finset C, W'.card = k → savScore A W' ≤ savScore A W

/-- The PAV score `∑_i r(|W ∩ A i|)` of `W`, where `r(p) = 1 + 1/2 + ⋯ + 1/p` is the harmonic
number `harmonic p`. -/
def pavScore (A : V → Finset C) (W : Finset C) : ℚ :=
  ∑ i, harmonic (W ∩ A i).card

/-- `W` is a PAV committee for `(A, k)`: `|W| = k` and no `k`-subset has a larger PAV score. -/
def IsPAVCommittee (A : V → Finset C) (k : ℕ) (W : Finset C) : Prop :=
  W.card = k ∧ ∀ W' : Finset C, W'.card = k → pavScore A W' ≤ pavScore A W

/-- The MAV score of `W`: the largest Hamming distance `d(W, A i) = |W \ A i| + |A i \ W|` from
`W` to a ballot. It is `0` when there are no voters. -/
def mavScore (A : V → Finset C) (W : Finset C) : ℕ :=
  Finset.univ.sup fun i => (W \ A i).card + (A i \ W).card

/-- `W` is an MAV committee for `(A, k)`: `|W| = k` and no `k`-subset has a smaller MAV
score. -/
def IsMAVCommittee (A : V → Finset C) (k : ℕ) (W : Finset C) : Prop :=
  W.card = k ∧ ∀ W' : Finset C, W'.card = k → mavScore A W ≤ mavScore A W'

/-! ### Checking justified representation (the paragraph before Theorem 2) -/

/-- `s_W(c) = |{i ∈ N | c ∈ A i, A i ∩ W = ∅}|`: the number of voters who approve `c` and
approve no member of `W`. -/
def uncoveredSupport (A : V → Finset C) (W : Finset C) (c : C) : ℕ :=
  (Finset.univ.filter fun i => c ∈ A i ∧ Disjoint (A i) W).card

/-- The JR check: accept `W` iff `k * s_W(c) < n` for every candidate `c`, where `n` is the
number of voters and `s_W(c)` the number of voters approving `c` but no member of `W`. For
positive `k` this is the source's `s_W(c) < n / k`. -/
def checkJR [Fintype C] (A : V → Finset C) (k : ℕ) (W : Finset C) : Bool :=
  decide (∀ c, k * uncoveredSupport A W c < Fintype.card V)

/-- **The JR criterion.** For every natural `k`, `W` provides justified representation for
`(A, k)` if and only if `k * s_W(c) < n` for every candidate `c`, where `n` is the number of
voters. For positive `k` this is the source's `s_W(c) < n / k`. -/
theorem providesJR_iff_forall_mul_uncoveredSupport_lt (A : V → Finset C) (k : ℕ)
    (W : Finset C) :
    ProvidesJR A k W ↔ ∀ c, k * uncoveredSupport A W c < Fintype.card V := by
  unfold ProvidesJR uncoveredSupport
  constructor
  · intro h c
    by_contra hc
    have hle : Fintype.card V ≤
        k * (Finset.univ.filter fun i => c ∈ A i ∧ Disjoint (A i) W).card :=
      Nat.le_of_not_gt hc
    apply h
    refine ⟨_, hle, ⟨c, fun i hi => (Finset.mem_filter.mp hi).2.1⟩,
      fun i hi => (Finset.mem_filter.mp hi).2.2⟩
  · intro h ⟨N, hNcard, ⟨c, hc⟩, hdisj⟩
    have hsub : N ⊆ Finset.univ.filter fun i => c ∈ A i ∧ Disjoint (A i) W := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hc i hi, hdisj i hi⟩
    have hle : N.card ≤
        (Finset.univ.filter fun i => c ∈ A i ∧ Disjoint (A i) W).card :=
      Finset.card_le_card hsub
    have hmul : k * N.card ≤
        k * (Finset.univ.filter fun i => c ∈ A i ∧ Disjoint (A i) W).card :=
      Nat.mul_le_mul_left k hle
    have h1 : Fintype.card V ≤
        k * (Finset.univ.filter fun i => c ∈ A i ∧ Disjoint (A i) W).card :=
      le_trans hNcard hmul
    exact (Nat.not_lt_of_ge h1) (h c)

/-- **Correctness of the JR check.** For a finite electorate and candidate set,
`checkJR A k W` returns `true` if and only if `W` provides justified representation
for `(A, k)`. -/
theorem checkJR_eq_true_iff [Fintype C] (A : V → Finset C) (k : ℕ) (W : Finset C) :
    checkJR A k W = true ↔ ProvidesJR A k W := by
  unfold checkJR
  rw [decide_eq_true_iff]
  exact (providesJR_iff_forall_mul_uncoveredSupport_lt A k W).symm

/-! ### GreedyAV (Section 2.1) and Theorem 1 -/

/-- One GreedyAV round from the committee `W`: the chosen candidate `c ∉ W` maximizes `s_W` over
the candidates outside `W`. The ballots still in the source's `A'` are those disjoint from `W`,
so a candidate's approval score with respect to `A'` is `s_W`. Once no remaining ballot approves
a candidate outside `W`, every such candidate has `s_W = 0`, so this round also covers the
source's arbitrary completion. -/
def IsGreedyAVStep (A : V → Finset C) (W : Finset C) (c : C) : Prop :=
  c ∉ W ∧ ∀ d, d ∉ W → uncoveredSupport A W d ≤ uncoveredSupport A W c

/-- `IsGreedyAVRun A j W`: some run of GreedyAV reaches the committee `W` after `j` rounds.
Every tie-breaking procedure is allowed, history-dependent ones included. -/
inductive IsGreedyAVRun (A : V → Finset C) : ℕ → Finset C → Prop
  /-- GreedyAV starts from the empty committee. -/
  | nil : IsGreedyAVRun A 0 ∅
  /-- A round adds a candidate allowed by `IsGreedyAVStep`. -/
  | step {j : ℕ} {W : Finset C} {c : C} :
      IsGreedyAVRun A j W → IsGreedyAVStep A W c → IsGreedyAVRun A (j + 1) (insert c W)

/-- A GreedyAV run of `k` rounds outputs a committee of size `k`. -/
theorem IsGreedyAVRun.card_eq {A : V → Finset C} {k : ℕ} {W : Finset C}
    (h : IsGreedyAVRun A k W) : W.card = k := by
  induction h with
  | nil => simp
  | step _ hstep ih =>
    unfold IsGreedyAVStep at hstep
    rw [Finset.card_insert_of_notMem hstep.1, ih]

/-- GreedyAV can run `k` rounds whenever `k ≤ |C|`. -/
theorem exists_isGreedyAVRun [Fintype C] (A : V → Finset C) {k : ℕ}
    (hk : k ≤ Fintype.card C) : ∃ W, IsGreedyAVRun A k W := by
  induction k with
  | zero => exact ⟨∅, .nil⟩
  | succ k ih =>
    have hk' : k ≤ Fintype.card C := Nat.le_of_succ_le hk
    obtain ⟨W, hW⟩ := ih hk'
    have hcard : W.card = k := hW.card_eq
    have hlt : W.card < (Finset.univ : Finset C).card := by
      rw [Finset.card_univ, hcard]
      omega
    obtain ⟨c, -, hcW⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have hne : (Finset.univ \ W).Nonempty :=
      ⟨c, Finset.mem_sdiff.mpr ⟨Finset.mem_univ c, hcW⟩⟩
    obtain ⟨c', hc'mem, hc'max⟩ :=
      Finset.exists_max_image (Finset.univ \ W) (uncoveredSupport A W) hne
    have hc'nmem : c' ∉ W := (Finset.mem_sdiff.mp hc'mem).2
    refine ⟨insert c' W, .step hW ⟨hc'nmem, fun d hdW => ?_⟩⟩
    have hdmem : d ∈ Finset.univ \ W :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ d, hdW⟩
    exact hc'max d hdmem

private theorem coveredFilter_insert_card (A : V → Finset C) (W : Finset C) (c : C) :
    (Finset.univ.filter fun i => ¬ Disjoint (A i) (insert c W)).card =
    (Finset.univ.filter fun i => ¬ Disjoint (A i) W).card +
    (Finset.univ.filter fun i => c ∈ A i ∧ Disjoint (A i) W).card := by
  simp only [Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.disjoint_insert_right]
  by_cases hD : Disjoint (A i) W <;> by_cases hc : c ∈ A i <;> simp [hD, hc]

private theorem mul_card_le_coveredFilter_card_of_run {A : V → Finset C} {j : ℕ} {W : Finset C}
    (h : IsGreedyAVRun A j W) :
    ∀ (N : Finset V) (c₀ : C), (∀ i ∈ N, c₀ ∈ A i) → (∀ i ∈ N, Disjoint (A i) W) →
    j * N.card ≤ (Finset.univ.filter fun i => ¬ Disjoint (A i) W).card := by
  induction h with
  | nil =>
    intro N c₀ _ _
    simp
  | @step j W c _ hstep ih =>
    intro N c₀ hcommon hdisj
    unfold IsGreedyAVStep at hstep
    obtain ⟨_, hmax⟩ := hstep
    have hdisjW : ∀ i ∈ N, Disjoint (A i) W :=
      fun i hi => (Finset.disjoint_insert_right.mp (hdisj i hi)).2
    have ih' := ih N c₀ hcommon hdisjW
    by_cases hNe : N.Nonempty
    · obtain ⟨i₀, hi₀⟩ := hNe
      have hc₀W : c₀ ∉ W :=
        Finset.disjoint_left.mp (hdisjW i₀ hi₀) (hcommon i₀ hi₀)
      have hsub : N ⊆ Finset.univ.filter fun i => c₀ ∈ A i ∧ Disjoint (A i) W := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hcommon i hi, hdisjW i hi⟩
      have hNle : N.card ≤ uncoveredSupport A W c₀ := Finset.card_le_card hsub
      have hNlec : N.card ≤ uncoveredSupport A W c := le_trans hNle (hmax c₀ hc₀W)
      unfold uncoveredSupport at hNlec
      have hcov := coveredFilter_insert_card A W c
      calc (j + 1) * N.card = j * N.card + N.card := by rw [add_mul, one_mul]
        _ ≤ (Finset.univ.filter fun i => ¬ Disjoint (A i) W).card +
            (Finset.univ.filter fun i => c ∈ A i ∧ Disjoint (A i) W).card :=
          Nat.add_le_add ih' hNlec
        _ = (Finset.univ.filter fun i => ¬ Disjoint (A i) (insert c W)).card := hcov.symm
    · have hcard0 : N.card = 0 :=
        Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hNe)
      simp [hcard0]

/-- **GreedyAV satisfies justified representation** (Theorem 1 of Aziz et al.): with at least
one voter, every committee that GreedyAV outputs, under every tie-breaking, provides justified
representation. -/
theorem IsGreedyAVRun.providesJR [Nonempty V] {A : V → Finset C} {k : ℕ} {W : Finset C}
    (h : IsGreedyAVRun A k W) : ProvidesJR A k W := by
  unfold ProvidesJR
  rintro ⟨N, hNcard, ⟨c₀, hcommon⟩, hdisj⟩
  have hinv := mul_card_le_coveredFilter_card_of_run h N c₀ hcommon hdisj
  have hNsub : N ⊆ Finset.univ.filter fun i => Disjoint (A i) W := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hdisj i hi
  have hNle : N.card ≤ (Finset.univ.filter fun i => Disjoint (A i) W).card :=
    Finset.card_le_card hNsub
  have hsplit : (Finset.univ.filter fun i => Disjoint (A i) W).card +
      (Finset.univ.filter fun i => ¬ Disjoint (A i) W).card = Fintype.card V := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V))
      (p := fun i => Disjoint (A i) W)
    rwa [Finset.card_univ] at h
  have hn_le_cov : Fintype.card V ≤ (Finset.univ.filter fun i => ¬ Disjoint (A i) W).card :=
    le_trans hNcard hinv
  have hN0 : N.card = 0 := by omega
  rw [hN0, mul_zero] at hNcard
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  omega

/-! ### AV (Theorem 3) -/

private theorem exists_avTwo_of_not_providesJR [Nonempty V] {A : V → Finset C}
    {W : Finset C} (hW : IsAVCommittee A 2 W) (hJR : ¬ ProvidesJR A 2 W) :
    ∃ a c, a ∈ W ∧ c ∉ W ∧ IsAVCommittee A 2 {a, c} ∧ ProvidesJR A 2 {a, c} := by
  classical
  unfold IsAVCommittee at hW
  obtain ⟨hWcard, hWopt⟩ := hW
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hWcard
  unfold ProvidesJR at hJR
  obtain ⟨N, hNcard, ⟨c, hcommon⟩, hdisj⟩ := Classical.byContradiction hJR
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  have hNe : N.Nonempty := by
    by_contra hcon
    have h0 : N.card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hcon)
    rw [h0, mul_zero] at hNcard
    omega
  obtain ⟨i₀, hi₀⟩ := hNe
  have hcW : c ∉ ({a, b} : Finset C) :=
    Finset.disjoint_left.mp (hdisj i₀ hi₀) (hcommon i₀ hi₀)
  have hca : a ≠ c := by
    intro h
    apply hcW
    rw [← h]
    exact Finset.mem_insert_self a {b}
  have hcb : b ≠ c := by
    intro h
    apply hcW
    rw [← h]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  have hsub_a : Finset.univ.filter (fun i => a ∈ A i) ⊆
      Finset.univ.filter (fun i => i ∉ N) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    intro hiN
    have hdis := hdisj i hiN
    have hna : a ∉ A i := Finset.disjoint_right.mp hdis (Finset.mem_insert_self a {b})
    exact hna hi
  have hsub_b : Finset.univ.filter (fun i => b ∈ A i) ⊆
      Finset.univ.filter (fun i => i ∉ N) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    intro hiN
    have hdis := hdisj i hiN
    have hnb : b ∉ A i := Finset.disjoint_right.mp hdis
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
    exact hnb hi
  have hsub_c : N ⊆ Finset.univ.filter (fun i => c ∈ A i) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hcommon i hi
  have hfilterN : Finset.univ.filter (fun i => i ∈ N) = N := by
    ext i
    simp
  have hsplit : N.card + (Finset.univ.filter fun i => i ∉ N).card = Fintype.card V := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V))
      (p := fun i => i ∈ N)
    rw [Finset.card_univ, hfilterN] at h
    exact h
  have hout_eq : (Finset.univ.filter fun i => i ∉ N).card =
      Fintype.card V - N.card := by omega
  have hle_a : (Finset.univ.filter fun i => a ∈ A i).card ≤ Fintype.card V - N.card := by
    rw [← hout_eq]
    exact Finset.card_le_card hsub_a
  have hle_b : (Finset.univ.filter fun i => b ∈ A i).card ≤ Fintype.card V - N.card := by
    rw [← hout_eq]
    exact Finset.card_le_card hsub_b
  have hnN : Fintype.card V - N.card ≤ N.card := by omega
  have hNc : N.card ≤ (Finset.univ.filter fun i => c ∈ A i).card :=
    Finset.card_le_card hsub_c
  have hav_ab : avScore A {a, b} = (Finset.univ.filter fun i => a ∈ A i).card +
      (Finset.univ.filter fun i => b ∈ A i).card := by
    unfold avScore approvalScore
    rw [Finset.sum_insert (by simp [hab]), Finset.sum_singleton]
  have hav_ac : avScore A {a, c} = (Finset.univ.filter fun i => a ∈ A i).card +
      (Finset.univ.filter fun i => c ∈ A i).card := by
    unfold avScore approvalScore
    rw [Finset.sum_insert (by simp [hca]), Finset.sum_singleton]
  have hav_bc : avScore A {b, c} = (Finset.univ.filter fun i => b ∈ A i).card +
      (Finset.univ.filter fun i => c ∈ A i).card := by
    unfold avScore approvalScore
    rw [Finset.sum_insert (by simp [hcb]), Finset.sum_singleton]
  have hopt_cb : (Finset.univ.filter fun i => c ∈ A i).card ≤
      (Finset.univ.filter fun i => b ∈ A i).card := by
    have h := hWopt {a, c} (Finset.card_pair hca)
    rw [hav_ac, hav_ab] at h
    omega
  have hopt_ca : (Finset.univ.filter fun i => c ∈ A i).card ≤
      (Finset.univ.filter fun i => a ∈ A i).card := by
    have h := hWopt {b, c} (Finset.card_pair hcb)
    rw [hav_bc, hav_ab] at h
    omega
  have heq_a : (Finset.univ.filter fun i => a ∈ A i).card = N.card := by omega
  have heq_b : (Finset.univ.filter fun i => b ∈ A i).card = N.card := by omega
  have heq_c : (Finset.univ.filter fun i => c ∈ A i).card = N.card := by omega
  have hnN_eq : Fintype.card V - N.card = N.card := by omega
  have hAVac : IsAVCommittee A 2 {a, c} := by
    unfold IsAVCommittee
    refine ⟨Finset.card_pair hca, fun W' hW' => ?_⟩
    have hle := hWopt W' hW'
    rw [hav_ab] at hle
    rw [hav_ac]
    omega
  have heq_filt : Finset.univ.filter (fun i => a ∈ A i) =
      Finset.univ.filter (fun i => i ∉ N) :=
    Finset.eq_of_subset_of_card_le hsub_a (by omega)
  have hac : ∀ i, a ∈ A i ∨ c ∈ A i := by
    intro i
    by_cases hiN : i ∈ N
    · exact Or.inr (hcommon i hiN)
    · left
      have hmem : i ∈ Finset.univ.filter (fun j => j ∉ N) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hiN
      rw [← heq_filt] at hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      exact hmem
  have hs0 : ∀ d, uncoveredSupport A {a, c} d = 0 := by
    intro d
    unfold uncoveredSupport
    have hempty : Finset.univ.filter (fun i => d ∈ A i ∧ Disjoint (A i) {a, c}) = ∅ := by
      apply Finset.filter_false_of_mem
      intro i _
      rintro ⟨-, hdis⟩
      have ha : a ∉ A i :=
        Finset.disjoint_right.mp hdis (Finset.mem_insert_self a {c})
      have hc : c ∉ A i := Finset.disjoint_right.mp hdis
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self c))
      rcases hac i with h | h
      · exact ha h
      · exact hc h
    rw [hempty, Finset.card_empty]
  have hJRac : ProvidesJR A 2 {a, c} := by
    rw [providesJR_iff_forall_mul_uncoveredSupport_lt]
    intro d
    rw [hs0 d, mul_zero]
    exact hpos
  exact ⟨a, c, Finset.mem_insert_self a {b}, hcW, hAVac, hJRac⟩

/-- **Theorem 3, `k = 2`.** With at least one voter and at least two candidates, some AV
committee of size `2` provides justified representation: AV satisfies JR for `k = 2` when ties
are broken in favor of committees that provide it. -/
theorem exists_isAVCommittee_two_providesJR [Fintype C] [Nonempty V] (A : V → Finset C)
    (hC : 2 ≤ Fintype.card C) : ∃ W, IsAVCommittee A 2 W ∧ ProvidesJR A 2 W := by
  have hne : (Finset.powersetCard 2 (Finset.univ : Finset C)).Nonempty :=
    Finset.powersetCard_nonempty.mpr (by rwa [Finset.card_univ])
  obtain ⟨W, hWmem, hWmax⟩ :=
    Finset.exists_max_image (Finset.powersetCard 2 (Finset.univ : Finset C)) (avScore A) hne
  have hWcard : W.card = 2 := (Finset.mem_powersetCard.mp hWmem).2
  have hAV : IsAVCommittee A 2 W :=
    ⟨hWcard, fun W' hW' => hWmax W' (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ W', hW'⟩)⟩
  by_cases hJR : ProvidesJR A 2 W
  · exact ⟨W, hAV, hJR⟩
  · obtain ⟨a, c, -, -, hAVac, hJRac⟩ := exists_avTwo_of_not_providesJR hAV hJR
    exact ⟨{a, c}, hAVac, hJRac⟩

/-- With at least one voter, a unique two-seat AV winner provides JR: for `k = 2` a
failure of AV needs a tie. -/
theorem providesJR_of_isAVCommittee_two_unique [Nonempty V] {A : V → Finset C} {W : Finset C}
    (hW : IsAVCommittee A 2 W) (huniq : ∀ W', IsAVCommittee A 2 W' → W' = W) :
    ProvidesJR A 2 W := by
  by_contra hJR
  obtain ⟨a, c, _, hcW, hAVac, -⟩ := exists_avTwo_of_not_providesJR hW hJR
  have heq := huniq {a, c} hAVac
  have hcmem : c ∈ ({a, c} : Finset C) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self c)
  rw [heq] at hcmem
  exact hcW hcmem

/-- The tie in the proof of Theorem 3, with `n' = 1`: voter `0` approves `{0, 2}` and voter `1`
approves `{1}`. -/
def avTieProfile : Fin 2 → Finset (Fin 3) := ![{0, 2}, {1}]

/-- **Theorem 3 needs its tie rule.** `{0, 2}` is an AV committee for `(avTieProfile, 2)` and
does not provide justified representation: voter `1` alone is a group of size
`1 ≥ n / k = 1`. -/
theorem isAVCommittee_avTieProfile_not_providesJR :
    IsAVCommittee avTieProfile 2 {0, 2} ∧ ¬ ProvidesJR avTieProfile 2 {0, 2} := by
  unfold IsAVCommittee ProvidesJR avTieProfile
  decide

/-- The profile in the proof of Theorem 3 for `k ≥ 3`: `n = k` voters and the candidates
`0, …, k`; voter `0` approves `{0}` and every other voter approves `{1, …, k}`. -/
def avProfile (k : ℕ) : Fin k → Finset (Fin (k + 1)) :=
  fun i => if (i : ℕ) = 0 then {0} else Finset.univ.erase 0

/-- **Theorem 3, `k ≥ 3`.** The unique AV committee for `(avProfile k, k)` is `{1, …, k}`, and
it does not provide justified representation. -/
theorem isAVCommittee_avProfile_iff_and_not_providesJR {k : ℕ} (hk : 3 ≤ k) :
    (∀ W, IsAVCommittee (avProfile k) k W ↔ W = Finset.univ.erase 0) ∧
      ¬ ProvidesJR (avProfile k) k (Finset.univ.erase 0) := by
  have hkpos : 0 < k := by omega
  have h0 : approvalScore (avProfile k) 0 = 1 := by
    have hfilter : Finset.univ.filter (fun i : Fin k => (0 : Fin (k+1)) ∈
        (if (i:ℕ)=0 then ({0} : Finset (Fin (k+1))) else Finset.univ.erase 0)) =
        ({⟨0, hkpos⟩} : Finset (Fin k)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      by_cases hi : (i : ℕ) = 0
      · rw [ite_eq_left hi]
        have hi0 : i = ⟨0, hkpos⟩ := Fin.ext hi
        simp [hi0]
      · rw [ite_eq_right hi]
        have hi0 : i ≠ ⟨0, hkpos⟩ := by
          rintro rfl
          exact hi rfl
        simp [Finset.mem_erase, hi0]
    unfold approvalScore avProfile
    rw [hfilter, Finset.card_singleton]
  have hj : ∀ j : Fin (k+1), j ≠ 0 → approvalScore (avProfile k) j = k - 1 := by
    intro j hj0
    have hfilter : Finset.univ.filter (fun i : Fin k => j ∈
        (if (i:ℕ)=0 then ({0} : Finset (Fin (k+1))) else Finset.univ.erase 0)) =
        Finset.univ.erase (⟨0, hkpos⟩ : Fin k) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      by_cases hi : (i : ℕ) = 0
      · rw [ite_eq_left hi]
        have hi0 : i = ⟨0, hkpos⟩ := Fin.ext hi
        simp [hi0, hj0]
      · rw [ite_eq_right hi]
        have hi0 : i ≠ ⟨0, hkpos⟩ := by
          rintro rfl
          exact hi rfl
        simp [Finset.mem_erase, hi0, hj0]
    unfold approvalScore avProfile
    rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
  have hcard_erase0 : (Finset.univ.erase (0 : Fin (k+1))).card = k := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, Fintype.card_fin,
      Nat.add_sub_cancel]
  have hWerase : ∀ W : Finset (Fin (k+1)), W.card = k → ∃ j, W = Finset.univ.erase j := by
    intro W hWcard
    have hsub : W ⊆ Finset.univ := Finset.subset_univ W
    have hne : W ≠ Finset.univ := by
      intro hcon
      have hcc := congrArg Finset.card hcon
      rw [hWcard, Finset.card_univ, Fintype.card_fin] at hcc
      omega
    have hss : W ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
    obtain ⟨j, -, hjnmem⟩ := Finset.exists_of_ssubset hss
    refine ⟨j, ?_⟩
    have hsub2 : W ⊆ Finset.univ.erase j := by
      intro x hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro hcon
      apply hjnmem
      rw [← hcon]
      exact hx
    have hcard_erase : (Finset.univ.erase j).card = k := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin,
        Nat.add_sub_cancel]
    have hle : (Finset.univ.erase j).card ≤ W.card := by omega
    exact Finset.eq_of_subset_of_card_le hsub2 hle
  have hadd_erase : ∀ j : Fin (k+1), approvalScore (avProfile k) j +
      avScore (avProfile k) (Finset.univ.erase j) =
      (∑ x ∈ (Finset.univ : Finset (Fin (k+1))), approvalScore (avProfile k) x) := by
    intro j
    unfold avScore
    exact Finset.add_sum_erase _ _ (Finset.mem_univ j)
  constructor
  · intro W
    constructor
    · intro hWc
      unfold IsAVCommittee at hWc
      obtain ⟨hWcard, hWopt⟩ := hWc
      obtain ⟨j, rfl⟩ := hWerase W hWcard
      by_cases hj0 : j = 0
      · rw [hj0]
      · exfalso
        have hle := hWopt (Finset.univ.erase 0) hcard_erase0
        have e0 := hadd_erase 0
        have ej := hadd_erase j
        rw [h0] at e0
        rw [hj j hj0] at ej
        omega
    · intro hWeq
      rw [hWeq]
      unfold IsAVCommittee
      refine ⟨hcard_erase0, fun W' hW' => ?_⟩
      obtain ⟨j, rfl⟩ := hWerase W' hW'
      have e0 := hadd_erase 0
      have ej := hadd_erase j
      rw [h0] at e0
      by_cases hj0 : j = 0
      · subst hj0
        omega
      · rw [hj j hj0] at ej
        omega
  · unfold ProvidesJR
    apply not_not_intro
    have hcond : ((⟨0, hkpos⟩ : Fin k) : ℕ) = 0 := rfl
    refine ⟨{⟨0, hkpos⟩}, by simp [Fintype.card_fin], ⟨0, ?_⟩, ?_⟩
    · intro i hi
      simp only [Finset.mem_singleton] at hi
      subst hi
      unfold avProfile
      rw [ite_eq_left hcond]
      exact Finset.mem_singleton_self 0
    · intro i hi
      simp only [Finset.mem_singleton] at hi
      subst hi
      unfold avProfile
      rw [ite_eq_left hcond, Finset.disjoint_singleton_left]
      simp

/-! ### SAV and MAV (Theorem 4) -/

/-- The SAV profile in the proof of Theorem 4: candidates `X = Fin (k + 1)` (left) and
`Y = Fin k` (right) and `n = k` voters. In the construction for `k ≥ 2`, voter `0` approves
`X`, voter `1` approves `{y₀, y₁}` and voter `i ≥ 2` approves `{yᵢ}`. -/
def savProfile (k : ℕ) : Fin k → Finset (Fin (k + 1) ⊕ Fin k) := fun i =>
  if (i : ℕ) = 0 then Finset.univ.map Function.Embedding.inl
  else (Finset.univ.filter fun j : Fin k =>
      ((i : ℕ) = 1 ∧ (j : ℕ) ≤ 1) ∨ (2 ≤ (i : ℕ) ∧ j = i)).map Function.Embedding.inr

private def savX (k : ℕ) : Finset (Fin (k + 1) ⊕ Fin k) :=
  Finset.univ.map Function.Embedding.inl
private def savY (k : ℕ) : Finset (Fin (k + 1) ⊕ Fin k) :=
  Finset.univ.map Function.Embedding.inr

private theorem savX_card {k : ℕ} : (savX k).card = k + 1 := by
  unfold savX
  rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]

private theorem savY_card {k : ℕ} : (savY k).card = k := by
  unfold savY
  rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]

private theorem savXY_disj {k : ℕ} : Disjoint (savX k) (savY k) := by
  rw [Finset.disjoint_left]
  intro c hc
  simp only [savX, savY, Finset.mem_map, Finset.mem_univ, true_and] at hc ⊢
  obtain ⟨x, hex⟩ := hc
  subst hex
  rintro ⟨j, heq⟩
  have hcontra : (Sum.inl x : Fin (k+1) ⊕ Fin k) = Sum.inr j := heq.symm
  exact absurd hcontra Sum.inl_ne_inr

private theorem savX_union_Y {k : ℕ} : savX k ∪ savY k = Finset.univ := by
  ext c
  simp only [savX, savY, Finset.mem_union, Finset.mem_map, Finset.mem_univ, true_and,
    Finset.mem_univ, iff_true]
  cases c with
  | inl x => exact Or.inl ⟨x, rfl⟩
  | inr j => exact Or.inr ⟨j, rfl⟩

private theorem savW_split {k : ℕ} (W : Finset (Fin (k + 1) ⊕ Fin k)) :
    (W ∩ savX k).card + (W ∩ savY k).card = W.card := by
  have hunion : (W ∩ savX k) ∪ (W ∩ savY k) = W := by
    rw [← Finset.inter_union_distrib_left, savX_union_Y, Finset.inter_univ]
  have hdisj : Disjoint (W ∩ savX k) (W ∩ savY k) :=
    Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right savXY_disj
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion] at hcard
  exact hcard.symm

private theorem savA0 {k : ℕ} (hkpos : 0 < k) :
    savProfile k ⟨0, hkpos⟩ = savX k := by
  unfold savProfile savX
  have hcond0 : ((⟨0, hkpos⟩ : Fin k) : ℕ) = 0 := rfl
  rw [ite_eq_left hcond0]

private theorem savFilter1 {k : ℕ} (hkpos : 0 < k) (hk1 : 1 < k) :
    Finset.univ.filter (fun j : Fin k =>
      (((⟨1, hk1⟩ : Fin k) : ℕ) = 1 ∧ (j : ℕ) ≤ 1) ∨
        (2 ≤ (((⟨1, hk1⟩ : Fin k) : ℕ)) ∧ j = ⟨1, hk1⟩)) =
      ({⟨0, hkpos⟩, ⟨1, hk1⟩} : Finset (Fin k)) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro hj
    have hle : (j : ℕ) ≤ 1 := by
      rcases hj with hle | ⟨h2, -⟩
      · exact hle
      · omega
    have hval : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by omega
    rcases hval with h0 | h1
    · exact Or.inl (Fin.ext h0)
    · exact Or.inr (Fin.ext h1)
  · rintro (rfl | rfl) <;> simp

private theorem savA1_eq {k : ℕ} (hkpos : 0 < k) (hk1 : 1 < k) :
    savProfile k ⟨1, hk1⟩ =
      {Sum.inr (⟨0, hkpos⟩ : Fin k), Sum.inr (⟨1, hk1⟩ : Fin k)} := by
  unfold savProfile
  have h1ne : ((⟨1, hk1⟩ : Fin k) : ℕ) ≠ 0 := one_ne_zero
  rw [ite_eq_right h1ne, savFilter1 hkpos hk1, Finset.map_insert, Finset.map_singleton]
  rfl

private theorem savA1_card {k : ℕ} (hkpos : 0 < k) (hk1 : 1 < k) :
    (savProfile k ⟨1, hk1⟩).card = 2 := by
  rw [savA1_eq hkpos hk1]
  apply Finset.card_pair
  intro hcon
  have h2 : (⟨0, hkpos⟩ : Fin k) = ⟨1, hk1⟩ := Sum.inr.inj hcon
  have h3 := congrArg Fin.val h2
  exact zero_ne_one h3

private theorem savA1_sub_Y {k : ℕ} (hkpos : 0 < k) (hk1 : 1 < k) :
    savProfile k ⟨1, hk1⟩ ⊆ savY k := by
  rw [savA1_eq hkpos hk1]
  intro c hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  simp only [savY, Finset.mem_map, Finset.mem_univ, true_and]
  rcases hc with rfl | rfl
  · exact ⟨⟨0, hkpos⟩, rfl⟩
  · exact ⟨⟨1, hk1⟩, rfl⟩

private theorem savAi {k : ℕ} (i : Fin k) (hi2 : 2 ≤ (i : ℕ)) :
    savProfile k i = {Sum.inr i} := by
  unfold savProfile
  have hi0 : (i : ℕ) ≠ 0 := by omega
  rw [ite_eq_right hi0]
  have hi1 : (i : ℕ) ≠ 1 := by omega
  have hfilter : Finset.univ.filter (fun j : Fin k =>
      ((i : ℕ) = 1 ∧ (j : ℕ) ≤ 1) ∨ (2 ≤ (i : ℕ) ∧ j = i)) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro (⟨h1, -⟩ | ⟨-, hji⟩)
      · exact absurd h1 hi1
      · exact hji
    · intro hji
      subst hji
      exact Or.inr ⟨hi2, rfl⟩
  rw [hfilter, Finset.map_singleton]
  rfl

private theorem savAi_card {k : ℕ} (i : Fin k) (hi2 : 2 ≤ (i : ℕ)) :
    (savProfile k i).card = 1 := by
  rw [savAi i hi2, Finset.card_singleton]

private theorem mem_erase_erase_ge_two {k : ℕ} (hkpos : 0 < k) (hk1 : 1 < k)
    (i : Fin k) (hi : i ∈ (Finset.univ.erase (⟨0, hkpos⟩ : Fin k)).erase (⟨1, hk1⟩ : Fin k)) :
    2 ≤ (i : ℕ) := by
  simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq] at hi
  obtain ⟨hi1, hi0⟩ := hi
  have h0 : (i : ℕ) ≠ 0 := by
    intro hcon
    apply hi0
    exact Fin.ext hcon
  have h1 : (i : ℕ) ≠ 1 := by
    intro hcon
    apply hi1
    exact Fin.ext hcon
  omega

private theorem inter_singleton_card {k : ℕ} (W : Finset (Fin (k + 1) ⊕ Fin k))
    (i : Fin k) :
    (W ∩ {Sum.inr i}).card = (if Sum.inr i ∈ W then 1 else 0) := by
  by_cases h : Sum.inr i ∈ W
  · have hsub : ({Sum.inr i} : Finset (Fin (k + 1) ⊕ Fin k)) ⊆ W :=
      Finset.singleton_subset_iff.mpr h
    have hinter : W ∩ {Sum.inr i} = {Sum.inr i} :=
      Finset.inter_eq_right.mpr hsub
    rw [hinter, Finset.card_singleton]
    simp [h]
  · have hempty : W ∩ ({Sum.inr i} : Finset (Fin (k + 1) ⊕ Fin k)) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro c
      simp only [Finset.mem_inter, Finset.mem_singleton]
      rintro ⟨hcW, rfl⟩
      exact h hcW
    rw [hempty, Finset.card_empty]
    simp [h]

private theorem savScore_split {k : ℕ} (hkpos : 0 < k) (hk1 : 1 < k)
    (W : Finset (Fin (k + 1) ⊕ Fin k)) :
    savScore (savProfile k) W =
      ((W ∩ savX k).card : ℚ) / (k + 1) + ((W ∩ savProfile k ⟨1, hk1⟩).card : ℚ) / 2 +
      ((((Finset.univ.erase (⟨0, hkpos⟩ : Fin k)).erase (⟨1, hk1⟩ : Fin k)).filter
        (fun i => Sum.inr i ∈ W)).card : ℚ) := by
  have hne10 : (⟨1, hk1⟩ : Fin k) ≠ ⟨0, hkpos⟩ := by
    intro hcon
    have h3 := congrArg Fin.val hcon
    exact one_ne_zero h3
  have h1mem : (⟨1, hk1⟩ : Fin k) ∈ Finset.univ.erase (⟨0, hkpos⟩ : Fin k) :=
    Finset.mem_erase.mpr ⟨hne10, Finset.mem_univ _⟩
  have hadd0 := Finset.add_sum_erase (Finset.univ : Finset (Fin k))
    (fun i => ((W ∩ savProfile k i).card : ℚ) / (savProfile k i).card)
    (Finset.mem_univ (⟨0, hkpos⟩ : Fin k))
  have hadd1 := Finset.add_sum_erase ((Finset.univ : Finset (Fin k)).erase (⟨0, hkpos⟩ : Fin k))
    (fun i => ((W ∩ savProfile k i).card : ℚ) / (savProfile k i).card) h1mem
  have hf0 : ((W ∩ savProfile k (⟨0, hkpos⟩ : Fin k)).card : ℚ) /
        (savProfile k (⟨0, hkpos⟩ : Fin k)).card =
      ((W ∩ savX k).card : ℚ) / (k + 1) := by
    rw [savA0 hkpos, savX_card]
    simp only [Nat.cast_add, Nat.cast_one]
  have hf1 : ((W ∩ savProfile k (⟨1, hk1⟩ : Fin k)).card : ℚ) /
        (savProfile k (⟨1, hk1⟩ : Fin k)).card =
      ((W ∩ savProfile k (⟨1, hk1⟩ : Fin k)).card : ℚ) / 2 := by
    rw [savA1_card hkpos hk1]
    norm_num
  have hfS : ∑ i ∈ ((Finset.univ.erase (⟨0, hkpos⟩ : Fin k)).erase (⟨1, hk1⟩ : Fin k)),
      ((W ∩ savProfile k i).card : ℚ) / (savProfile k i).card =
      ((((Finset.univ.erase (⟨0, hkpos⟩ : Fin k)).erase (⟨1, hk1⟩ : Fin k)).filter
        (fun i => Sum.inr i ∈ W)).card : ℚ) := by
    have hterm : ∀ i ∈ ((Finset.univ.erase (⟨0, hkpos⟩ : Fin k)).erase (⟨1, hk1⟩ : Fin k)),
        ((W ∩ savProfile k i).card : ℚ) / (savProfile k i).card =
        (if Sum.inr i ∈ W then (1 : ℚ) else 0) := by
      intro i hi
      have hi2 := mem_erase_erase_ge_two hkpos hk1 i hi
      rw [savAi_card i hi2, savAi i hi2, inter_singleton_card W i]
      by_cases h : Sum.inr i ∈ W <;> simp [h]
    rw [Finset.sum_congr rfl hterm]
    exact Finset.sum_boole _ _
  unfold savScore at hadd0 hadd1 ⊢
  linarith [hadd0, hadd1, hf0, hf1, hfS]

private theorem savY_mem {k : ℕ} (c : Fin (k + 1) ⊕ Fin k) :
    c ∈ savY k ↔ ∃ j, Sum.inr j = c := by
  constructor
  · intro hc
    rw [savY, Finset.mem_map] at hc
    obtain ⟨j, -, heq⟩ := hc
    exact ⟨j, heq⟩
  · rintro ⟨j, rfl⟩
    rw [savY, Finset.mem_map]
    exact ⟨j, Finset.mem_univ j, rfl⟩

private theorem filter_card_eq {k : ℕ} (hkpos : 0 < k) (hk1 : 1 < k)
    (W : Finset (Fin (k + 1) ⊕ Fin k)) :
    (((Finset.univ.erase (⟨0, hkpos⟩ : Fin k)).erase (⟨1, hk1⟩ : Fin k)).filter
      (fun i => Sum.inr i ∈ W)).card =
    (W ∩ savY k).card - (W ∩ savProfile k (⟨1, hk1⟩ : Fin k)).card := by
  have hB1sub := savA1_sub_Y hkpos hk1
  have hinter : savProfile k (⟨1, hk1⟩ : Fin k) ∩ (W ∩ savY k) =
      W ∩ savProfile k (⟨1, hk1⟩ : Fin k) := by
    ext c
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨hcB, hcW, -⟩
      exact ⟨hcW, hcB⟩
    · rintro ⟨hcW, hcB⟩
      exact ⟨hcB, hcW, hB1sub hcB⟩
  have hsdiff : ((W ∩ savY k) \ savProfile k (⟨1, hk1⟩ : Fin k)).card =
      (W ∩ savY k).card - (W ∩ savProfile k (⟨1, hk1⟩ : Fin k)).card := by
    rw [Finset.card_sdiff, hinter]
  have himage : (W ∩ savY k) \ savProfile k (⟨1, hk1⟩ : Fin k) =
      Finset.image Sum.inr (((Finset.univ.erase (⟨0, hkpos⟩ : Fin k)).erase
        (⟨1, hk1⟩ : Fin k)).filter (fun i => Sum.inr i ∈ W)) := by
    ext c
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_image, Finset.mem_filter,
      Finset.mem_erase, Finset.mem_univ, and_true, ne_eq]
    constructor
    · rintro ⟨⟨hcW, hcY⟩, hcB⟩
      obtain ⟨j, heq⟩ := (savY_mem c).mp hcY
      subst heq
      have hBne : (Sum.inr j : Fin (k + 1) ⊕ Fin k) ≠ Sum.inr (⟨0, hkpos⟩ : Fin k) ∧
          (Sum.inr j : Fin (k + 1) ⊕ Fin k) ≠ Sum.inr (⟨1, hk1⟩ : Fin k) := by
        rw [savA1_eq hkpos hk1] at hcB
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcB
        exact hcB
      have hne0 : j ≠ (⟨0, hkpos⟩ : Fin k) := by
        intro hcon
        exact hBne.1 (congrArg Sum.inr hcon)
      have hne1 : j ≠ (⟨1, hk1⟩ : Fin k) := by
        intro hcon
        exact hBne.2 (congrArg Sum.inr hcon)
      exact ⟨j, ⟨⟨hne1, hne0⟩, hcW⟩, rfl⟩
    · rintro ⟨j, ⟨⟨hne1, hne0⟩, hcW⟩, rfl⟩
      have hY : (Sum.inr j : Fin (k + 1) ⊕ Fin k) ∈ savY k :=
        (savY_mem _).mpr ⟨j, rfl⟩
      have hB : (Sum.inr j : Fin (k + 1) ⊕ Fin k) ∉ savProfile k (⟨1, hk1⟩ : Fin k) := by
        rw [savA1_eq hkpos hk1]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        constructor
        · intro hcon
          apply hne0
          exact Sum.inr.inj hcon
        · intro hcon
          apply hne1
          exact Sum.inr.inj hcon
      exact ⟨⟨hcW, hY⟩, hB⟩
  have hcard := Finset.card_image_of_injective
    (f := (Sum.inr : Fin k → Fin (k + 1) ⊕ Fin k))
    (((Finset.univ.erase (⟨0, hkpos⟩ : Fin k)).erase (⟨1, hk1⟩ : Fin k)).filter
      (fun i => Sum.inr i ∈ W)) (fun _ _ h => Sum.inr.inj h)
  rw [← himage, hsdiff] at hcard
  exact hcard.symm

private theorem savA_le_U {k : ℕ} (hkpos : 0 < k) (hk1 : 1 < k)
    (W : Finset (Fin (k + 1) ⊕ Fin k)) :
    (W ∩ savProfile k (⟨1, hk1⟩ : Fin k)).card ≤ (W ∩ savY k).card := by
  apply Finset.card_le_card
  exact Finset.inter_subset_inter le_rfl (savA1_sub_Y hkpos hk1)

private theorem savErase_card {k : ℕ} (hkpos : 0 < k) (hk1 : 1 < k) :
    (((Finset.univ.erase (⟨0, hkpos⟩ : Fin k)).erase (⟨1, hk1⟩ : Fin k))).card = k - 2 := by
  have hne10 : (⟨1, hk1⟩ : Fin k) ≠ ⟨0, hkpos⟩ := by
    intro hcon
    have h3 := congrArg Fin.val hcon
    exact one_ne_zero h3
  have h1mem : (⟨1, hk1⟩ : Fin k) ∈ Finset.univ.erase (⟨0, hkpos⟩ : Fin k) :=
    Finset.mem_erase.mpr ⟨hne10, Finset.mem_univ _⟩
  rw [Finset.card_erase_of_mem h1mem, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin]
  omega

private theorem savScore_eq_form {k : ℕ} (hkpos : 0 < k) (hk1 : 1 < k)
    (W : Finset (Fin (k + 1) ⊕ Fin k)) :
    savScore (savProfile k) W =
      (((W ∩ savX k).card : ℚ) / (k + 1) + ((W ∩ savProfile k (⟨1, hk1⟩ : Fin k)).card : ℚ) / 2 +
      ((((W ∩ savY k).card - (W ∩ savProfile k (⟨1, hk1⟩ : Fin k)).card : ℕ)) : ℚ)) := by
  rw [savScore_split hkpos hk1 W, filter_card_eq hkpos hk1 W]

private theorem savScore_Y {k : ℕ} (hk : 2 ≤ k) :
    savScore (savProfile k) (savY k) = (k : ℚ) - 1 := by
  have hkpos : 0 < k := by omega
  have hk1 : 1 < k := by omega
  have hform := savScore_eq_form hkpos hk1 (savY k)
  have ht0 : (savY k ∩ savX k).card = 0 := by
    have hempty : savY k ∩ savX k = ∅ := by
      rw [Finset.inter_comm]
      exact Finset.disjoint_iff_inter_eq_empty.mp savXY_disj
    rw [hempty, Finset.card_empty]
  have haY : (savY k ∩ savProfile k (⟨1, hk1⟩ : Fin k)).card = 2 := by
    have heq : savY k ∩ savProfile k (⟨1, hk1⟩ : Fin k) =
        savProfile k (⟨1, hk1⟩ : Fin k) :=
      Finset.inter_eq_right.mpr (savA1_sub_Y hkpos hk1)
    rw [heq, savA1_card hkpos hk1]
  have huY : (savY k ∩ savY k).card = k := by
    rw [Finset.inter_eq_left.mpr le_rfl, savY_card]
  rw [ht0, haY, huY, Nat.cast_sub hk] at hform
  norm_num at hform
  linarith

private theorem savScore_lt {k : ℕ} (hk : 2 ≤ k)
    (W : Finset (Fin (k + 1) ⊕ Fin k)) (hWcard : W.card = k) (hne : W ≠ savY k) :
    savScore (savProfile k) W < (k : ℚ) - 1 := by
  have hkpos : 0 < k := by omega
  have hk1 : 1 < k := by omega
  have hform := savScore_eq_form hkpos hk1 W
  have htu : (W ∩ savX k).card + (W ∩ savY k).card = k := by
    have h := savW_split W
    omega
  have haU := savA_le_U hkpos hk1 W
  have hTU : ((W ∩ savX k).card : ℚ) + ((W ∩ savY k).card : ℚ) = (k : ℚ) := by
    exact_mod_cast htu
  have hA0 : (0 : ℚ) ≤ ((W ∩ savProfile k (⟨1, hk1⟩ : Fin k)).card : ℚ) :=
    Nat.cast_nonneg _
  have hsub : ((((W ∩ savY k).card - (W ∩ savProfile k (⟨1, hk1⟩ : Fin k)).card : ℕ)) : ℚ) =
      ((W ∩ savY k).card : ℚ) - ((W ∩ savProfile k (⟨1, hk1⟩ : Fin k)).card : ℚ) :=
    Nat.cast_sub haU
  rw [hsub] at hform
  by_cases h0 : (W ∩ savX k).card = 0
  · have hempty : W ∩ savX k = ∅ := Finset.card_eq_zero.mp h0
    have hWYsub : W ⊆ savY k := by
      intro c hcW
      have huniv : c ∈ savX k ∪ savY k := by
        rw [savX_union_Y]
        exact Finset.mem_univ c
      rw [Finset.mem_union] at huniv
      rcases huniv with hcX | hcY
      · exfalso
        have hmem : c ∈ W ∩ savX k := Finset.mem_inter.mpr ⟨hcW, hcX⟩
        rw [hempty] at hmem
        exact Finset.notMem_empty c hmem
      · exact hcY
    have hYc : (savY k).card = k := savY_card
    have hWeq : W = savY k := Finset.eq_of_subset_of_card_le hWYsub (by omega)
    exact (hne hWeq).elim
  · have ht1 : 1 ≤ (W ∩ savX k).card := by omega
    by_cases h1 : (W ∩ savX k).card = 1
    · have ha1 : 1 ≤ (W ∩ savProfile k (⟨1, hk1⟩ : Fin k)).card := by
        have hflt := filter_card_eq hkpos hk1 W
        have hle : ((((Finset.univ.erase (⟨0, hkpos⟩ : Fin k)).erase (⟨1, hk1⟩ : Fin k)).filter
            (fun i => Sum.inr i ∈ W))).card ≤ k - 2 := by
          have hsub2 : ((((Finset.univ.erase (⟨0, hkpos⟩ : Fin k)).erase (⟨1, hk1⟩ : Fin k)).filter
              (fun i => Sum.inr i ∈ W))) ⊆
              ((Finset.univ.erase (⟨0, hkpos⟩ : Fin k)).erase (⟨1, hk1⟩ : Fin k)) :=
            Finset.filter_subset _ _
          have hcc := Finset.card_le_card hsub2
          rw [savErase_card hkpos hk1] at hcc
          exact hcc
        omega
      have ha1Q : (1 : ℚ) ≤ ((W ∩ savProfile k (⟨1, hk1⟩ : Fin k)).card : ℚ) := by
        exact_mod_cast ha1
      have hK2 : (2 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
      have hposK : (0 : ℚ) < (k : ℚ) + 1 := by
        have hnn := Nat.cast_nonneg (α := ℚ) k
        linarith
      have hdiv1 : (1 : ℚ) / ((k : ℚ) + 1) < 1 / 2 := by
        rw [div_lt_iff₀ hposK]
        linarith
      rw [h1, Nat.cast_one] at hform hTU
      linarith [hform, hTU, hdiv1, ha1Q]
    · have ht2 : 2 ≤ (W ∩ savX k).card := by omega
      have hprod : ((W ∩ savX k).card - 1) * 2 ≤ ((W ∩ savX k).card - 1) * k :=
        Nat.mul_le_mul_left _ hk
      have hexpand : ((W ∩ savX k).card - 1) * (k + 1) =
          ((W ∩ savX k).card - 1) * k + ((W ∩ savX k).card - 1) := by
        rw [mul_add, mul_one]
      have hNat : (W ∩ savX k).card < ((W ∩ savX k).card - 1) * (k + 1) := by omega
      have hQ : (((W ∩ savX k).card - 1) * (k + 1) : ℚ) >
          ((W ∩ savX k).card : ℚ) := by
        exact_mod_cast hNat
      have hposK : (0 : ℚ) < (k : ℚ) + 1 := by
        have hnn := Nat.cast_nonneg (α := ℚ) k
        linarith
      have hdiv : ((W ∩ savX k).card : ℚ) / ((k : ℚ) + 1) <
          ((W ∩ savX k).card : ℚ) - 1 := by
        rw [div_lt_iff₀ hposK]
        linarith [hQ]
      linarith [hform, hdiv, hTU, hA0]

/-- **Theorem 4, SAV.** For `k ≥ 2` the unique SAV committee for `(savProfile k, k)` is `Y`,
and it does not provide justified representation: voter `0` is unrepresented. -/
theorem isSAVCommittee_savProfile_iff_and_not_providesJR {k : ℕ} (hk : 2 ≤ k) :
    (∀ W, IsSAVCommittee (savProfile k) k W ↔ W = Finset.univ.map Function.Embedding.inr) ∧
      ¬ ProvidesJR (savProfile k) k (Finset.univ.map Function.Embedding.inr) := by
  change (∀ W, IsSAVCommittee (savProfile k) k W ↔ W = savY k) ∧
    ¬ ProvidesJR (savProfile k) k (savY k)
  constructor
  · intro W
    constructor
    · intro hWc
      obtain ⟨hWcard, hWopt⟩ := hWc
      by_cases hWY : W = savY k
      · exact hWY
      · exfalso
        have hlt := savScore_lt hk W hWcard hWY
        have hY : savScore (savProfile k) (savY k) = (k : ℚ) - 1 := savScore_Y hk
        have hle := hWopt (savY k) savY_card
        linarith
    · intro hWeq
      rw [hWeq]
      refine ⟨savY_card, fun W' hW' => ?_⟩
      by_cases hWY : W' = savY k
      · subst hWY
        exact le_rfl
      · have hlt := savScore_lt hk W' hW' hWY
        have hY : savScore (savProfile k) (savY k) = (k : ℚ) - 1 := savScore_Y hk
        linarith
  · have hkpos : 0 < k := by omega
    have hk1pos : 0 < k + 1 := by omega
    intro hJR
    unfold ProvidesJR at hJR
    apply hJR
    refine ⟨{⟨0, hkpos⟩}, by simp [Fintype.card_fin],
      ⟨Sum.inl (⟨0, hk1pos⟩ : Fin (k + 1)), ?_⟩, ?_⟩
    · intro i hi
      simp only [Finset.mem_singleton] at hi
      subst hi
      rw [savA0 hkpos]
      unfold savX
      rw [Finset.mem_map]
      exact ⟨⟨0, hk1pos⟩, Finset.mem_univ _, rfl⟩
    · intro i hi
      simp only [Finset.mem_singleton] at hi
      subst hi
      rw [savA0 hkpos]
      exact savXY_disj

/-- The MAV profile in the proof of Theorem 4: candidates `some (inl i) = xᵢ`,
`some (inr i) = yᵢ` and `none = z`; voter `inl i` approves `{xᵢ, yᵢ}` and voter `inr i`
approves `{z}`, so `n = 2k`. -/
def mavProfile (k : ℕ) : Fin k ⊕ Fin k → Finset (Option (Fin k ⊕ Fin k))
  | .inl i => {some (.inl i), some (.inr i)}
  | .inr _ => {none}

private def inlSomeEmb (k : ℕ) : Fin k ↪ Option (Fin k ⊕ Fin k) :=
  ⟨fun i => some (.inl i), fun i j h => by simpa using h⟩

private def mavX (k : ℕ) : Finset (Option (Fin k ⊕ Fin k)) :=
  Finset.univ.map (inlSomeEmb k)

private theorem mavX_card {k : ℕ} : (mavX k).card = k := by
  unfold mavX
  rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]

private theorem mavX_notMem_none {k : ℕ} : (none : Option (Fin k ⊕ Fin k)) ∉ mavX k := by
  intro hcon
  rw [mavX, Finset.mem_map] at hcon
  obtain ⟨i, -, hcon⟩ := hcon
  have h2 : (some (Sum.inl i) : Option (Fin k ⊕ Fin k)) = none := hcon
  exact absurd h2 (Option.some_ne_none _)

private theorem mavX_mem_inl {k : ℕ} (i : Fin k) :
    (some (.inl i) : Option (Fin k ⊕ Fin k)) ∈ mavX k := by
  rw [mavX, Finset.mem_map]
  exact ⟨i, Finset.mem_univ i, rfl⟩

private theorem mavX_notMem_inr {k : ℕ} (j : Fin k) :
    (some (.inr j) : Option (Fin k ⊕ Fin k)) ∉ mavX k := by
  intro hcon
  rw [mavX, Finset.mem_map] at hcon
  obtain ⟨i, -, hcon⟩ := hcon
  have h2 : (some (Sum.inl i) : Option (Fin k ⊕ Fin k)) = some (Sum.inr j) := hcon
  have h3 : (Sum.inl i : Fin k ⊕ Fin k) = Sum.inr j := Option.some_inj.mp h2
  exact absurd h3 Sum.inl_ne_inr

private theorem mavX_dist_inl {k : ℕ} (hk : 2 ≤ k) (i : Fin k) :
    ((mavX k \ mavProfile k (.inl i)).card + (mavProfile k (.inl i) \ mavX k).card) = k := by
  have haX : (some (.inl i) : Option (Fin k ⊕ Fin k)) ∈ mavX k := mavX_mem_inl i
  have hbX : (some (.inr i) : Option (Fin k ⊕ Fin k)) ∉ mavX k := mavX_notMem_inr i
  have hA : mavProfile k (.inl i) = {some (.inl i), some (.inr i)} := rfl
  have hsdiff1 : mavX k \ mavProfile k (.inl i) = (mavX k).erase (some (.inl i)) := by
    rw [hA]
    ext c
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_erase, not_or]
    constructor
    · rintro ⟨hcX, hne1, hne2⟩
      exact ⟨hne1, hcX⟩
    · rintro ⟨hne1, hcX⟩
      refine ⟨hcX, hne1, ?_⟩
      intro hcon
      rw [hcon] at hcX
      exact hbX hcX
  have hsdiff2 : mavProfile k (.inl i) \ mavX k = {some (.inr i)} := by
    rw [hA]
    ext c
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h_or, h_not⟩
      rcases h_or with rfl | rfl
      · exact (h_not haX).elim
      · rfl
    · intro hc
      rw [hc]
      exact ⟨Or.inr rfl, hbX⟩
  rw [hsdiff1, hsdiff2, Finset.card_erase_of_mem haX, mavX_card, Finset.card_singleton]
  omega

private theorem mavX_dist_inr {k : ℕ} (j : Fin k) :
    ((mavX k \ mavProfile k (.inr j)).card + (mavProfile k (.inr j) \ mavX k).card) = k + 1 := by
  have hnone : (none : Option (Fin k ⊕ Fin k)) ∉ mavX k := mavX_notMem_none
  have hA : mavProfile k (.inr j) = {none} := rfl
  have hsdiff1 : mavX k \ mavProfile k (.inr j) = mavX k := by
    rw [hA, Finset.sdiff_singleton_eq_erase, Finset.erase_eq_of_notMem hnone]
  have hsdiff2 : mavProfile k (.inr j) \ mavX k = {none} := by
    rw [hA]
    ext c
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl, -⟩
      rfl
    · intro hc
      rw [hc]
      exact ⟨rfl, hnone⟩
  rw [hsdiff1, hsdiff2, mavX_card, Finset.card_singleton]

private theorem mavScore_X {k : ℕ} (hk : 2 ≤ k) :
    mavScore (mavProfile k) (mavX k) = k + 1 := by
  have hkpos : 0 < k := by omega
  unfold mavScore
  apply le_antisymm
  · apply Finset.sup_le
    intro v _
    cases v with
    | inl i =>
      rw [mavX_dist_inl hk i]
      omega
    | inr j =>
      rw [mavX_dist_inr j]
  · have hle := Finset.le_sup (s := (Finset.univ : Finset (Fin k ⊕ Fin k)))
      (f := fun i => ((mavX k \ mavProfile k i).card + (mavProfile k i \ mavX k).card))
      (Finset.mem_univ (.inr (⟨0, hkpos⟩ : Fin k)))
    rw [mavX_dist_inr] at hle
    exact hle

private def mavPairIdx {k : ℕ} (hkpos : 0 < k) : Option (Fin k ⊕ Fin k) → Fin k
  | some (.inl i) => i
  | some (.inr i) => i
  | none => ⟨0, hkpos⟩

private theorem exists_dist_ge_of_mem_none {k : ℕ} (hk : 2 ≤ k)
    (W : Finset (Option (Fin k ⊕ Fin k)))
    (hWcard : W.card = k) (hnone : (none : Option (Fin k ⊕ Fin k)) ∈ W) :
    ∃ i : Fin k, ((W \ mavProfile k (.inl i)).card + (mavProfile k (.inl i) \ W).card) = k + 2 := by
  have hkpos : 0 < k := by omega
  have herase_card : (W.erase none).card = k - 1 := by
    rw [Finset.card_erase_of_mem hnone, hWcard]
  have himg_le : ((W.erase none).image (mavPairIdx hkpos)).card ≤ k - 1 := by
    rw [← herase_card]
    exact Finset.card_image_le
  have hlt : ((W.erase none).image (mavPairIdx hkpos)).card <
      (Finset.univ : Finset (Fin k)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨i₀, _, hi₀S⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have haW : (some (.inl i₀) : Option (Fin k ⊕ Fin k)) ∉ W := by
    intro hcon
    have hmem_erase : (some (.inl i₀) : Option (Fin k ⊕ Fin k)) ∈ W.erase none := by
      rw [Finset.mem_erase]
      exact ⟨Option.some_ne_none _, hcon⟩
    have hi₀mem : i₀ ∈ (W.erase none).image (mavPairIdx hkpos) := by
      rw [Finset.mem_image]
      exact ⟨_, hmem_erase, rfl⟩
    exact hi₀S hi₀mem
  have hbW : (some (.inr i₀) : Option (Fin k ⊕ Fin k)) ∉ W := by
    intro hcon
    have hmem_erase : (some (.inr i₀) : Option (Fin k ⊕ Fin k)) ∈ W.erase none := by
      rw [Finset.mem_erase]
      exact ⟨Option.some_ne_none _, hcon⟩
    have hi₀mem : i₀ ∈ (W.erase none).image (mavPairIdx hkpos) := by
      rw [Finset.mem_image]
      exact ⟨_, hmem_erase, rfl⟩
    exact hi₀S hi₀mem
  have hA : mavProfile k (.inl i₀) = {some (.inl i₀), some (.inr i₀)} := rfl
  have hdisj : Disjoint W (mavProfile k (.inl i₀)) := by
    rw [hA, Finset.disjoint_left]
    intro c hcW hcA
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcA
    rcases hcA with rfl | rfl
    · exact haW hcW
    · exact hbW hcW
  have hsdiff1 : W \ mavProfile k (.inl i₀) = W :=
    Finset.sdiff_eq_self_iff_disjoint.mpr hdisj
  have hsdiff2 : mavProfile k (.inl i₀) \ W = mavProfile k (.inl i₀) :=
    Finset.sdiff_eq_self_iff_disjoint.mpr (Disjoint.symm hdisj)
  have hAcard : (mavProfile k (.inl i₀)).card = 2 := by
    rw [hA]
    apply Finset.card_pair
    intro hcon
    have h3 : (Sum.inl i₀ : Fin k ⊕ Fin k) = Sum.inr i₀ := Option.some_inj.mp hcon
    exact absurd h3 Sum.inl_ne_inr
  exact ⟨i₀, by rw [hsdiff1, hsdiff2, hWcard, hAcard]⟩

/-- **Theorem 4, MAV.** For `k ≥ 2` there is an MAV committee for `(mavProfile k, k)`, and no
MAV committee provides justified representation. -/
theorem mavProfile_isMAVCommittee_not_providesJR {k : ℕ} (hk : 2 ≤ k) :
    (∃ W, IsMAVCommittee (mavProfile k) k W) ∧
      ∀ W, IsMAVCommittee (mavProfile k) k W → ¬ ProvidesJR (mavProfile k) k W := by
  have hkpos : 0 < k := by omega
  have hC : k ≤ Fintype.card (Option (Fin k ⊕ Fin k)) := by
    rw [Fintype.card_option, Fintype.card_sum, Fintype.card_fin]
    omega
  have hne : (Finset.powersetCard k
      (Finset.univ : Finset (Option (Fin k ⊕ Fin k)))).Nonempty :=
    Finset.powersetCard_nonempty.mpr (by rwa [Finset.card_univ])
  obtain ⟨W0, hW0mem, hW0min⟩ :=
    Finset.exists_min_image (Finset.powersetCard k
      (Finset.univ : Finset (Option (Fin k ⊕ Fin k))))
      (mavScore (mavProfile k)) hne
  have hW0card : W0.card = k := (Finset.mem_powersetCard.mp hW0mem).2
  have hMAV0 : IsMAVCommittee (mavProfile k) k W0 :=
    ⟨hW0card, fun W' hW' => hW0min W' (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ W', hW'⟩)⟩
  have hXcard : (mavX k).card = k := mavX_card
  have hXscore : mavScore (mavProfile k) (mavX k) = k + 1 := mavScore_X hk
  refine ⟨⟨W0, hMAV0⟩, fun W hW => ?_⟩
  obtain ⟨hWcard, hWopt⟩ := hW
  have hWle : mavScore (mavProfile k) W ≤ k + 1 := by
    have h := hWopt (mavX k) hXcard
    rw [hXscore] at h
    exact h
  have hnone_nmem : (none : Option (Fin k ⊕ Fin k)) ∉ W := by
    intro hcon
    obtain ⟨i₀, hi₀⟩ := exists_dist_ge_of_mem_none hk W hWcard hcon
    have hle := Finset.le_sup (s := (Finset.univ : Finset (Fin k ⊕ Fin k)))
      (f := fun i => ((W \ mavProfile k i).card + (mavProfile k i \ W).card))
      (Finset.mem_univ (.inl i₀))
    unfold mavScore at hWle hle
    omega
  have hn : Fintype.card (Fin k ⊕ Fin k) = k + k := by
    rw [Fintype.card_sum, Fintype.card_fin]
  have hNcard : (Finset.univ.map Function.Embedding.inr :
      Finset (Fin k ⊕ Fin k)).card = k := by
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hthresh : Fintype.card (Fin k ⊕ Fin k) ≤
      k * (Finset.univ.map Function.Embedding.inr : Finset (Fin k ⊕ Fin k)).card := by
    rw [hn, hNcard]
    have h : 2 * k ≤ k * k := Nat.mul_le_mul_right k hk
    omega
  intro hJR
  unfold ProvidesJR at hJR
  apply hJR
  refine ⟨Finset.univ.map Function.Embedding.inr, hthresh, ⟨none, ?_⟩, ?_⟩
  · intro i hi
    rw [Finset.mem_map] at hi
    obtain ⟨j, -, rfl⟩ := hi
    exact Finset.mem_singleton_self none
  · intro i hi
    rw [Finset.mem_map] at hi
    obtain ⟨j, -, rfl⟩ := hi
    change Disjoint ({none} : Finset (Option (Fin k ⊕ Fin k))) W
    rw [Finset.disjoint_singleton_left]
    exact hnone_nmem

end Rules

/-! ### GreedyAV with ties broken toward the least candidate -/

section Deterministic

variable [Fintype C] [LinearOrder C]

/-- One GreedyAV round from `W`, breaking ties toward the least candidate: the first maximizer
of `s_W` in the increasing list of the candidates outside `W`, or `none` iff `W` contains every
candidate. -/
def greedyAVPick (A : V → Finset C) (W : Finset C) : Option C :=
  ((Finset.univ \ W).sort (· ≤ ·)).argmax (uncoveredSupport A W)

/-- GreedyAV with ties broken toward the least candidate, run for `j` iterations; once
every candidate is seated, further iterations leave the committee unchanged. -/
def greedyAV (A : V → Finset C) : ℕ → Finset C
  | 0 => ∅
  | j + 1 =>
    match greedyAVPick A (greedyAV A j) with
    | some c => insert c (greedyAV A j)
    | none => greedyAV A j

/-- For `k ≤ |C|`, least-candidate GreedyAV yields a `k`-round GreedyAV run. With
`IsGreedyAVRun.card_eq` and `IsGreedyAVRun.providesJR`, it outputs a committee of size `k`
that provides justified representation whenever there is at least one voter. -/
theorem isGreedyAVRun_greedyAV (A : V → Finset C) {k : ℕ} (hk : k ≤ Fintype.card C) :
    IsGreedyAVRun A k (greedyAV A k) := by
  induction k with
  | zero => exact .nil
  | succ k ih =>
    have hk' : k ≤ Fintype.card C := Nat.le_of_succ_le hk
    have hrun := ih hk'
    have hcard : (greedyAV A k).card = k := hrun.card_eq
    have hlt : (greedyAV A k).card < (Finset.univ : Finset C).card := by
      rw [Finset.card_univ, hcard]
      omega
    obtain ⟨c0, -, hc0W⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have hne : (Finset.univ \ greedyAV A k).Nonempty :=
      ⟨c0, Finset.mem_sdiff.mpr ⟨Finset.mem_univ c0, hc0W⟩⟩
    have hsort_ne : ((Finset.univ \ greedyAV A k).sort (· ≤ ·)) ≠ [] := by
      intro hcon
      have hlen := Finset.length_sort (· ≤ ·) (s := Finset.univ \ greedyAV A k)
      rw [hcon] at hlen
      simp at hlen
      have hcard0 : (Finset.univ \ greedyAV A k).card = 0 := hlen.symm
      have hempty := Finset.card_eq_zero.mp hcard0
      obtain ⟨x, hx⟩ := hne
      rw [hempty] at hx
      exact Finset.notMem_empty x hx
    have harg_ne : ((Finset.univ \ greedyAV A k).sort (· ≤ ·)).argmax
        (uncoveredSupport A (greedyAV A k)) ≠ none := by
      intro hcon
      rw [List.argmax_eq_none] at hcon
      exact hsort_ne hcon
    obtain ⟨c, hceq⟩ := Option.ne_none_iff_exists.mp harg_ne
    have harg : c ∈ ((Finset.univ \ greedyAV A k).sort (· ≤ ·)).argmax
        (uncoveredSupport A (greedyAV A k)) := by
      rw [← hceq]
      exact rfl
    have hmem_sort : c ∈ ((Finset.univ \ greedyAV A k).sort (· ≤ ·)) :=
      List.argmax_mem harg
    have hmem_sdiff : c ∈ (Finset.univ \ greedyAV A k) := by
      rwa [Finset.mem_sort] at hmem_sort
    have hcW : c ∉ greedyAV A k := (Finset.mem_sdiff.mp hmem_sdiff).2
    have hmax : ∀ d, d ∉ greedyAV A k →
        uncoveredSupport A (greedyAV A k) d ≤ uncoveredSupport A (greedyAV A k) c := by
      intro d hdW
      have hd_sdiff : d ∈ (Finset.univ \ greedyAV A k) :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ d, hdW⟩
      have hd_sort : d ∈ ((Finset.univ \ greedyAV A k).sort (· ≤ ·)) := by
        rwa [Finset.mem_sort]
      exact List.le_of_mem_argmax hd_sort harg
    have hpick : greedyAVPick A (greedyAV A k) = some c := by
      unfold greedyAVPick
      exact hceq.symm
    have hgreedy : greedyAV A (k + 1) = insert c (greedyAV A k) := by
      simp only [greedyAV, hpick]
    rw [hgreedy]
    exact .step hrun ⟨hcW, hmax⟩

end Deterministic

end MathlibExt.GameTheory.SocialChoice.ApprovalCommittee

end
