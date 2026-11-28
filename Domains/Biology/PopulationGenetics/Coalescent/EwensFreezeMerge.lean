/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ChineseRestaurant
public import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto

/-!
# Neutral freeze-and-merge jumps

`State` records a partition of the labeled sample and its active blocks. `Event` uses
two-element subsets for unordered mergers. For a mutation parameter `θ > 0`, `eventLaw` assigns
the specified neutral jump probabilities; `step` applies those events, and `run` iterates them
from active singletons. The process stutters after all blocks freeze. These are embedded discrete
jumps; no continuous-time genealogy coupling is asserted.

This is the embedded jump chain of the coalescent of Donnelly and Tavaré (1986, §2), with the
age order of the new classes forgotten as in Watterson (1984). Active blocks are their old
equivalence classes, frozen blocks are their new classes, and a freeze is a mutation. For
`θ > 0` and `k ≥ 1` active blocks, given that a jump occurs, a specified pair merges with
probability `2 / (k (θ + k - 1))` and a specified block freezes with probability
`θ / (k (θ + k - 1))`:
Donnelly and Tavaré (1986), (2.9)–(2.11) and cases (a′), (b′), pp. 4–5. The terminal formula
`terminalLaw_apply` is their Theorem 2.2 (p. 6) at `k = 0`, the labeled Ewens sampling formula
(Ewens 1972).

## Main results

* `step_applyEvent`: each legal event has its neutral probability.
* `run_all_frozen`: after `n` jumps every block is frozen.
* `terminalLaw_eq_crp`: the terminal partition law is the Chinese restaurant process.
* `terminalLaw_apply`: the labeled Ewens sampling formula for the terminal partition.

## References

* P. Donnelly and S. Tavaré, *The ages of alleles and a coalescent*, Adv. Appl. Probab. 18
  (1986), 1–19, §2: the jump probabilities (2.9)–(2.11) and the embedded chain, pp. 4–5;
  Theorem 2.2, p. 6.
* G. A. Watterson, *Lines of descent and the coalescent*, Theor. Popul. Biol. 26 (1984),
  77–92.
* W. J. Ewens, *The sampling theory of selectively neutral alleles*, Theor. Popul. Biol. 3
  (1972), 87–112.
-/

@[expose] public section

noncomputable section

open Finset

namespace Domains.Biology.PopulationGenetics.Coalescent.EwensFreezeMerge

/-- **Freeze-and-merge state.** A partition of the labeled sample, with a subset of its blocks
marked active. Native `Finpartition` ensures nonempty, disjoint blocks covering the sample. -/
@[ext] structure State (n : ℕ) where
  partition : Finpartition (univ : Finset (Fin n))
  active : Finset (Finset (Fin n))
  active_subset : active ⊆ partition.parts
  deriving DecidableEq

instance (n : ℕ) : Fintype (State n) :=
  Fintype.ofInjective (fun s : State n ↦ (s.partition, s.active)) (by
    intro s t h
    exact State.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

/-- **Frozen blocks.** The frozen blocks are precisely the blocks outside the active subset. -/
def frozen (n : ℕ) (s : State n) : Finset (Finset (Fin n)) :=
  s.partition.parts \ s.active

private lemma union_notMem_rest (n : ℕ)
    (π : Finpartition (univ : Finset (Fin n))) (p : Finset (Finset (Fin n)))
    (hp : p ⊆ π.parts) (hne : p.Nonempty) :
    p.biUnion id ∉ π.parts \ p := by
  intro h
  obtain ⟨B, hB⟩ := hne
  obtain ⟨x, hx⟩ := π.nonempty_of_mem_parts (hp hB)
  have hu : x ∈ p.biUnion id := mem_biUnion.mpr ⟨B, hB, hx⟩
  have heq := π.eq_of_mem_parts (mem_sdiff.mp h).1 (hp hB) hu hx
  exact (mem_sdiff.mp h).2 (heq ▸ hB)

private lemma existsUnique_mem_merge (n : ℕ)
    (π : Finpartition (univ : Finset (Fin n))) (p : Finset (Finset (Fin n)))
    (hp : p ⊆ π.parts) :
    ∀ x ∈ (univ : Finset (Fin n)), ∃! B ∈ insert (p.biUnion id) (π.parts \ p), x ∈ B := by
  intro x hx
  obtain ⟨B, ⟨hB, hxB⟩, huniq⟩ := π.existsUnique_mem hx
  by_cases hBp : B ∈ p
  · refine ⟨p.biUnion id, ⟨mem_insert_self _ _, mem_biUnion.mpr ⟨B, hBp, hxB⟩⟩, ?_⟩
    rintro C ⟨hC, hxC⟩
    rcases mem_insert.mp hC with rfl | hC
    · rfl
    · have heq := huniq C ⟨(mem_sdiff.mp hC).1, hxC⟩
      exact False.elim ((mem_sdiff.mp hC).2 (heq ▸ hBp))
  · refine ⟨B, ⟨mem_insert_of_mem (mem_sdiff.mpr ⟨hB, hBp⟩), hxB⟩, ?_⟩
    rintro C ⟨hC, hxC⟩
    rcases mem_insert.mp hC with rfl | hC
    · obtain ⟨D, hD, hxD⟩ := mem_biUnion.mp hxC
      have heq := huniq D ⟨hp hD, hxD⟩
      exact False.elim (hBp (heq ▸ hD))
    · exact huniq C ⟨(mem_sdiff.mp hC).1, hxC⟩

private lemma empty_notMem_merge (n : ℕ)
    (π : Finpartition (univ : Finset (Fin n))) (p : Finset (Finset (Fin n)))
    (hp : p ⊆ π.parts) (hne : p.Nonempty) :
    ∅ ∉ insert (p.biUnion id) (π.parts \ p) := by
  simp only [mem_insert, mem_sdiff, not_or]
  constructor
  · obtain ⟨B, hB⟩ := hne
    obtain ⟨x, hx⟩ := π.nonempty_of_mem_parts (hp hB)
    intro heq
    have : x ∈ p.biUnion id := mem_biUnion.mpr ⟨B, hB, hx⟩
    simp [← heq] at this
  · exact fun h ↦ π.bot_notMem h.1

/-- **Freezing an active block.** Freeze one specified active block without changing the
partition or any other mark. -/
def freeze (n : ℕ) (s : State n) (B : s.active) : State n where
  partition := s.partition
  active := s.active.erase B.1
  active_subset := (erase_subset _ _).trans s.active_subset

/-- **Merging active blocks.** Merge a nonempty collection of active blocks into its union; all
other blocks keep their marks. The jump law only calls this with a two-element collection. -/
def merge (n : ℕ) (s : State n) (p : Finset (Finset (Fin n)))
    (hp : p ⊆ s.active) (hne : p.Nonempty) : State n where
  partition := Finpartition.ofExistsUnique (insert (p.biUnion id) (s.partition.parts \ p))
    (fun _ _ ↦ subset_univ _)
    (by exact existsUnique_mem_merge n s.partition p (hp.trans s.active_subset))
    (by exact empty_notMem_merge n s.partition p (hp.trans s.active_subset) hne)
  active := insert (p.biUnion id) (s.active \ p)
  active_subset := by
    intro B hB
    rcases mem_insert.mp hB with rfl | hB
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_sdiff.mpr
        ⟨s.active_subset (mem_sdiff.mp hB).1, (mem_sdiff.mp hB).2⟩)

/-- **Freeze-and-merge events.** Legal nonabsorbing events: a specified active block freezes,
or an unordered pair of distinct active blocks merges. -/
abbrev Event (n : ℕ) (s : State n) :=
  s.active ⊕ {p : Finset (Finset (Fin n)) // p ∈ s.active.powersetCard 2}

private lemma pair_subset (n : ℕ) (s : State n)
    (p : {p : Finset (Finset (Fin n)) // p ∈ s.active.powersetCard 2}) :
    p.1 ⊆ s.active := (mem_powersetCard.mp p.2).1

private lemma pair_nonempty (n : ℕ) (s : State n)
    (p : {p : Finset (Finset (Fin n)) // p ∈ s.active.powersetCard 2}) :
    p.1.Nonempty := by
  rw [← card_pos, (mem_powersetCard.mp p.2).2]
  decide

/-- **Applying an event.** Apply a legal event, preserving the native partition and marking
invariants. -/
def applyEvent (n : ℕ) (s : State n) : Event n s → State n
  | Sum.inl B => freeze n s B
  | Sum.inr p => merge n s p.1 (by exact pair_subset n s p) (by exact pair_nonempty n s p)

/-- **Each jump removes one active block.** Every nonabsorbing event reduces the number of
active blocks by exactly one. -/
theorem applyEvent_active_card (n : ℕ) (s : State n) (e : Event n s) :
    (applyEvent n s e).active.card + 1 = s.active.card := by
  classical
  cases e with
  | inl B =>
    change (s.active.erase B.1).card + 1 = s.active.card
    rw [card_erase_of_mem B.2]
    have := card_pos.mpr (show s.active.Nonempty from ⟨B.1, B.2⟩)
    omega
  | inr p =>
    have hp := pair_subset n s p
    have hcard := (mem_powersetCard.mp p.2).2
    have hne := pair_nonempty n s p
    have hrest : p.1.biUnion id ∉ s.active \ p.1 := by
      intro h
      exact union_notMem_rest n s.partition p.1 (hp.trans s.active_subset) hne
        (mem_sdiff.mpr ⟨s.active_subset (mem_sdiff.mp h).1, (mem_sdiff.mp h).2⟩)
    change (insert (p.1.biUnion id) (s.active \ p.1)).card + 1 = _
    rw [card_insert_of_notMem hrest, card_sdiff_of_subset hp, hcard]
    have := card_le_card hp
    omega

/-- **Freezing keeps the partition.** Freezing leaves the partition unchanged. -/
theorem freeze_partition (n : ℕ) (s : State n) (B : s.active) :
    (freeze n s B).partition = s.partition := rfl

/-- **Freezing adds one frozen block.** A freeze adds precisely the selected block to the
frozen set. -/
theorem freeze_frozen (n : ℕ) (s : State n) (B : s.active) :
    frozen n (freeze n s B) = insert B.1 (frozen n s) := by
  classical
  ext C
  simp only [frozen, freeze, mem_sdiff, mem_erase, mem_insert]
  have hB := s.active_subset B.2
  by_cases hCB : C = B.1
  · subst C
    simp [hB]
  · simp [hCB]

/-- **Merging keeps the frozen blocks.** A merger preserves every frozen block, and creates no
new frozen block. -/
theorem merge_frozen (n : ℕ) (s : State n) (p : Finset (Finset (Fin n)))
    (hp : p ⊆ s.active) (hne : p.Nonempty) :
    frozen n (merge n s p hp hne) = frozen n s := by
  classical
  have hU := union_notMem_rest n s.partition p (hp.trans s.active_subset) hne
  ext B
  simp only [frozen, merge, Finpartition.ofExistsUnique_parts,
    mem_sdiff, mem_insert]
  constructor
  · rintro ⟨hB, hBa⟩
    rcases hB with hB | ⟨hB, hBp⟩
    · exact False.elim (hBa (Or.inl hB))
    · refine ⟨hB, ?_⟩
      intro hactive
      exact hBa (Or.inr ⟨hactive, hBp⟩)
  · rintro ⟨hB, hBa⟩
    have hBp : B ∉ p := fun h ↦ hBa (hp h)
    refine ⟨Or.inr ⟨hB, hBp⟩, ?_⟩
    rintro (hBU | ⟨hactive, -⟩)
    · subst B
      exact hU (mem_sdiff.mpr ⟨hB, hBp⟩)
    · exact hBa hactive

/-- **Jump denominator.** The denominator of a nonabsorbing jump at active count `k`. -/
def denominator (θ : ℝ) (k : ℕ) : ℝ := k * (θ + k - 1)

/-- **The last-jump denominator vanishes without mutation.** The last-jump denominator vanishes
at `θ = 0`, which is why that parameter is excluded from the nonabsorbing neutral transition
law. -/
theorem denominator_zero_last : denominator 0 1 = 0 := by
  norm_num [denominator]

private lemma denominator_pos (θ : ℝ) (hθ : 0 < θ) (k : ℕ) (hk : 0 < k) :
    0 < denominator θ k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  exact mul_pos hk0 (by linarith)

private lemma union_notMem_parts_pair (n : ℕ)
    (π : Finpartition (univ : Finset (Fin n))) (p : Finset (Finset (Fin n)))
    (hp : p ⊆ π.parts) (hc : p.card = 2) : p.biUnion id ∉ π.parts := by
  intro hU
  have hsub : p ⊆ {p.biUnion id} := by
    intro B hB
    obtain ⟨x, hx⟩ := π.nonempty_of_mem_parts (hp hB)
    exact mem_singleton.mpr (π.eq_of_mem_parts (hp hB) hU hx
      (mem_biUnion.mpr ⟨B, hB, hx⟩))
  have := card_le_card hsub
  simp only [card_singleton, hc] at this
  omega

private lemma union_notMem_active_pair (n : ℕ) (s : State n) (p : Finset (Finset (Fin n)))
    (hp : p ⊆ s.active) (hc : p.card = 2) : p.biUnion id ∉ s.active := fun hu ↦
  union_notMem_parts_pair n s.partition p (hp.trans s.active_subset) hc (s.active_subset hu)

private lemma merge_pair_partition_card (n : ℕ) (s : State n)
    (p : {p : Finset (Finset (Fin n)) // p ∈ s.active.powersetCard 2}) :
    (applyEvent n s (Sum.inr p)).partition.parts.card + 1 = s.partition.parts.card := by
  have hp := (pair_subset n s p).trans s.active_subset
  have hc := (mem_powersetCard.mp p.2).2
  change (insert (p.1.biUnion id) (s.partition.parts \ p.1)).card + 1 = _
  rw [card_insert_of_notMem (union_notMem_rest n s.partition p.1 hp
    (pair_nonempty n s p)), card_sdiff_of_subset hp, hc]
  have := card_le_card hp
  omega

private lemma removed_merge_pair (n : ℕ) (s : State n)
    (p : {p : Finset (Finset (Fin n)) // p ∈ s.active.powersetCard 2}) :
    s.active \ (applyEvent n s (Sum.inr p)).active = p.1 := by
  classical
  have hp := pair_subset n s p
  have hU := union_notMem_active_pair n s p.1 hp (mem_powersetCard.mp p.2).2
  ext B
  change B ∈ s.active \ insert (p.1.biUnion id) (s.active \ p.1) ↔ B ∈ p.1
  simp only [mem_sdiff, mem_insert]
  constructor
  · rintro ⟨ha, hn⟩
    by_contra hnp
    exact hn (Or.inr ⟨ha, hnp⟩)
  · intro hB
    refine ⟨hp hB, ?_⟩
    rintro (hBU | ⟨-, hnp⟩)
    · exact hU (hBU ▸ hp hB)
    · exact hnp hB

private lemma freeze_injective (n : ℕ) (s : State n) :
    Function.Injective (freeze n s) := by
  intro B C h
  apply Subtype.ext
  by_contra hBC
  have heq := congrArg State.active h
  change s.active.erase B.1 = s.active.erase C.1 at heq
  have hmem : B.1 ∈ s.active.erase C.1 := mem_erase.mpr ⟨hBC, B.2⟩
  rw [← heq] at hmem
  exact notMem_erase _ _ hmem

/-- **Distinct events give distinct states.** Distinct legal freeze or unordered-merger events
have distinct successor states. -/
theorem applyEvent_injective (n : ℕ) (s : State n) :
    Function.Injective (applyEvent n s) := by
  intro e f h
  cases e with
  | inl B =>
    cases f with
    | inl C => exact congrArg Sum.inl (freeze_injective n s h)
    | inr p =>
      have heq := congrArg (fun t : State n ↦ t.partition.parts.card) h
      have hc := merge_pair_partition_card n s p
      change s.partition.parts.card = _ at heq
      omega
  | inr p =>
    cases f with
    | inl B =>
      have heq := congrArg (fun t : State n ↦ t.partition.parts.card) h
      have hc := merge_pair_partition_card n s p
      change _ = s.partition.parts.card at heq
      omega
    | inr q =>
      have heq := congrArg (fun t : State n ↦ s.active \ t.active) h
      rw [removed_merge_pair, removed_merge_pair] at heq
      exact congrArg Sum.inr (Subtype.ext heq)

/-- **Neutral jump weights.** The raw weight of an event at active count `k`: `θ / [k(θ+k-1)]`
for each freeze and `2 / [k(θ+k-1)]` for each specified unordered merger, matching pair rate one
and mutation rate `θ/2`. For `θ > 0` and `k ≥ 1` they are probabilities: they sum to one
(`sum_eventWeight`) and are the embedded jump probabilities of Donnelly and Tavaré (1986), p. 5,
cases (a′) and (b′). In general they are raw values: at `θ = 0` and `k = 1` the only event, a
freeze, has weight `0 / 0 = 0`. -/
def eventWeight (θ : ℝ) (n : ℕ) (s : State n) : Event n s → ℝ
  | Sum.inl _ => θ / denominator θ s.active.card
  | Sum.inr _ => 2 / denominator θ s.active.card

private lemma eventWeight_nonneg (θ : ℝ) (hθ : 0 < θ) (n : ℕ)
    (s : State n) (hk : 0 < s.active.card) (e : Event n s) :
    0 ≤ eventWeight θ n s e := by
  have hd := (denominator_pos θ hθ s.active.card hk).le
  cases e <;> exact div_nonneg (by positivity) hd

private lemma twice_choose_two (k : ℕ) : (2 : ℝ) * k.choose 2 = k * (k - 1 : ℕ) := by
  cases k with
  | zero => norm_num
  | succ k =>
    have h : (k + 1) * k = (k + 1).choose 2 * 2 := by
      simpa using Nat.add_one_mul_choose_eq k 1
    have hr : ((k + 1 : ℕ) : ℝ) * (k : ℝ) = ((k + 1).choose 2 : ℝ) * 2 := by
      exact_mod_cast h
    simpa [mul_comm] using hr.symm

/-- **The jump weights sum to one.** For `θ > 0` and positive active count, the actual finite
collection of event weights sums to one. -/
theorem sum_eventWeight (θ : ℝ) (hθ : 0 < θ) (n : ℕ)
    (s : State n) (hk : 0 < s.active.card) : ∑ e : Event n s, eventWeight θ n s e = 1 := by
  classical
  have hd := (denominator_pos θ hθ s.active.card hk).ne'
  have hk1 : (1 : ℝ) ≤ s.active.card := by exact_mod_cast hk
  have hsub : ((s.active.card - 1 : ℕ) : ℝ) = s.active.card - 1 :=
    by simpa using (Nat.cast_sub (R := ℝ) (show 1 ≤ s.active.card by omega))
  rw [Fintype.sum_sum_type]
  simp only [eventWeight, sum_const, nsmul_eq_mul, card_univ, Fintype.card_coe, card_powersetCard]
  have hc := twice_choose_two s.active.card
  rw [hsub] at hc
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
  have hnum : (s.active.card : ℝ) * θ + (s.active.card.choose 2 : ℝ) * 2 =
      denominator θ s.active.card := by
    unfold denominator
    nlinarith
  rw [hnum, div_self hd]

/-- **Neutral jump law.** For `θ > 0` and positive active count, the neutral event PMF,
constructed from the nonnegative normalized finite weights. -/
def eventLaw (θ : ℝ) (hθ : 0 < θ) (n : ℕ) (s : State n)
    (hk : 0 < s.active.card) : PMF (Event n s) := by
  classical
  exact PMF.ofFintype (fun e ↦ ENNReal.ofReal (eventWeight θ n s e)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun e _ ↦ eventWeight_nonneg θ hθ n s hk e),
      sum_eventWeight θ hθ n s hk, ENNReal.ofReal_one])

/-- **Values of the jump law.** For `θ > 0` and positive active count, the event PMF evaluates
to the specified finite real weight converted to `ENNReal`. -/
theorem eventLaw_apply (θ : ℝ) (hθ : 0 < θ) (n : ℕ) (s : State n)
    (hk : 0 < s.active.card) (e : Event n s) :
    eventLaw θ hθ n s hk e = ENNReal.ofReal (eventWeight θ n s e) := rfl

/-- **Freeze-and-merge transition law.** For `θ > 0`, the actual finite transition PMF: apply
the event law while active, and stutter when every block is frozen. -/
def step (θ : ℝ) (hθ : 0 < θ) (n : ℕ) (s : State n) : PMF (State n) :=
  if hk : 0 < s.active.card then (eventLaw θ hθ n s hk).map (applyEvent n s)
  else PMF.pure s

/-- **Transition probability of a jump.** For `θ > 0` and positive active count, the transition
probability of each specified legal event is exactly its neutral weight; injectivity ensures no
other event contributes to this successor. -/
theorem step_applyEvent (θ : ℝ) (hθ : 0 < θ) (n : ℕ) (s : State n)
    (hk : 0 < s.active.card) (e : Event n s) :
    step θ hθ n s (applyEvent n s e) = ENNReal.ofReal (eventWeight θ n s e) := by
  classical
  rw [step, dite_eq_left hk, PMF.map_apply, tsum_fintype, sum_eq_single e]
  · simp [eventLaw]
  · intro f _ hfe
    have hne : applyEvent n s e ≠ applyEvent n s f := by
      intro h
      exact hfe ((applyEvent_injective n s h).symm)
    simp [hne]
  · simp

/-- **The last jump keeps the partition.** For `θ > 0`, with one active block, the last jump
freezes it and leaves the partition fixed. -/
theorem step_partition_one (θ : ℝ) (hθ : 0 < θ) (n : ℕ) (s : State n)
    (hk : s.active.card = 1) :
    (step θ hθ n s).map State.partition = PMF.pure s.partition := by
  have hpos : 0 < s.active.card := by omega
  rw [step, dite_eq_left hpos, PMF.map_comp]
  have hf : State.partition ∘ applyEvent n s = Function.const (Event n s) s.partition := by
    funext e
    cases e with
    | inl B => rfl
    | inr p =>
      have hp := pair_subset n s p
      have hc := (mem_powersetCard.mp p.2).2
      have := card_le_card hp
      omega
  rw [hf, PMF.map_const]

/-- **Initial freeze-and-merge state.** Initially the partition consists of singletons, all
marked active. -/
def initial (n : ℕ) : State n where
  partition := ⊥
  active := (⊥ : Finpartition (univ : Finset (Fin n))).parts
  active_subset := Subset.refl _

/-- **Freeze-and-merge chain.** For `θ > 0`, iterate the transition PMF independently of any
terminal formula. -/
def run (θ : ℝ) (hθ : 0 < θ) (n : ℕ) : ℕ → PMF (State n)
  | 0 => PMF.pure (initial n)
  | t + 1 => (run θ hθ n t).bind (step θ hθ n)

/-- **Terminal partition law.** For `θ > 0`, project the result after `n` jumps to the native
labeled partition type. -/
def terminalLaw (θ : ℝ) (hθ : 0 < θ) (n : ℕ) :
    PMF (Finpartition (univ : Finset (Fin n))) :=
  (run θ hθ n n).map State.partition

/-- **The chain stutters once absorbed.** For `θ > 0`, at zero active count the chain
stutters. -/
theorem step_stutter (θ : ℝ) (hθ : 0 < θ) (n : ℕ) (s : State n)
    (hk : s.active.card = 0) : step θ hθ n s = PMF.pure s := by
  simp [step, hk]

private lemma step_active_card (θ : ℝ) (hθ : 0 < θ) (n : ℕ)
    (s t : State n) (ht : t ∈ (step θ hθ n s).support) :
    t.active.card = s.active.card - 1 := by
  classical
  by_cases hk : 0 < s.active.card
  · rw [step, dite_eq_left hk, PMF.mem_support_map_iff] at ht
    obtain ⟨e, -, rfl⟩ := ht
    have := applyEvent_active_card n s e
    omega
  · have hz : s.active.card = 0 := by omega
    rw [step_stutter θ hθ n s hz, PMF.mem_support_pure_iff] at ht
    subst t
    simp [hz]

/-- **Initial active count.** Initially there are exactly `n` active singleton blocks. -/
theorem initial_active_card (n : ℕ) : (initial n).active.card = n := by
  simp [initial]

/-- **Active count after `t` jumps.** For `θ > 0`, the support after `t` jumps has exactly
`n-t` active blocks, using truncated subtraction to include stuttering after absorption. -/
theorem run_active_card (θ : ℝ) (hθ : 0 < θ) (n t : ℕ) (s : State n)
    (hs : s ∈ (run θ hθ n t).support) : s.active.card = n - t := by
  induction t generalizing s with
  | zero =>
    rw [run, PMF.mem_support_pure_iff] at hs
    subst s
    simpa using initial_active_card n
  | succ t ih =>
    rw [run, PMF.mem_support_bind_iff] at hs
    obtain ⟨r, hr, hs⟩ := hs
    rw [step_active_card θ hθ n r s hs, ih r hr]
    omega

/-- **Absorption after `n` jumps.** For `θ > 0`, after `n` jumps all blocks are frozen; this
follows from the actual chain's support and is independent of the terminal partition formula. -/
theorem run_all_frozen (θ : ℝ) (hθ : 0 < θ) (n : ℕ) (s : State n)
    (hs : s ∈ (run θ hθ n n).support) : s.active = ∅ := by
  apply card_eq_zero.mp
  simpa using run_active_card θ hθ n n s hs

private def compatible (n : ℕ) (s : State n)
    (π : Finpartition (univ : Finset (Fin n))) : Prop :=
  s.partition ≤ π ∧ frozen n s ⊆ π.parts

private def activeGroup (n : ℕ) (s : State n) (B : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  s.active.filter (fun A => A ⊆ B)

private lemma part_subset_eq (n : ℕ) (π : Finpartition (univ : Finset (Fin n)))
    (A B : Finset (Fin n)) (hA : A ∈ π.parts) (hB : B ∈ π.parts) (hAB : A ⊆ B) :
    A = B := by
  obtain ⟨x,hx⟩ := π.nonempty_of_mem_parts hA
  exact π.eq_of_mem_parts hA hB hx (hAB hx)

private lemma active_target_unique (n : ℕ) (s : State n)
    (π : Finpartition (univ : Finset (Fin n))) (h : compatible n s π)
    (A : Finset (Fin n)) (hA : A ∈ s.active) :
    ∃! B, B ∈ π.parts ∧ A ⊆ B := by
  obtain ⟨B,hB,hAB⟩ := h.1 (s.active_subset hA)
  refine ⟨B, ⟨hB,hAB⟩, ?_⟩
  rintro C ⟨hC,hAC⟩
  obtain ⟨x,hx⟩ := s.partition.nonempty_of_mem_parts (s.active_subset hA)
  exact π.eq_of_mem_parts hC hB (hAC hx) (hAB hx)

private lemma sum_activeGroup_card (n : ℕ) (s : State n)
    (π : Finpartition (univ : Finset (Fin n))) (h : compatible n s π) :
    ∑ B ∈ π.parts, (activeGroup n s B).card = s.active.card := by
  classical
  simp only [activeGroup, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  have hi : ∀ A ∈ s.active, (∑ B ∈ π.parts, if A ⊆ B then 1 else 0) = (1 : ℕ) := by
    intro A hA
    obtain ⟨B, ⟨hB,hAB⟩, hu⟩ := active_target_unique n s π h A hA
    rw [sum_eq_single B]
    · simp [hAB]
    · intro C hC hCB
      have hn : ¬ A ⊆ C := fun hAC => hCB (hu C ⟨hC,hAC⟩)
      simp [hn]
    · exact fun hn => False.elim (hn hB)
  simp only [sum_congr rfl hi, sum_const, nsmul_eq_mul, mul_one]

private lemma group_nonempty_iff (n : ℕ) (s : State n)
    (π : Finpartition (univ : Finset (Fin n))) (h : compatible n s π)
    (B : Finset (Fin n)) (hB : B ∈ π.parts) :
    (activeGroup n s B).Nonempty ↔ B ∉ frozen n s := by
  classical
  constructor
  · rintro ⟨A,hA⟩ hBF
    obtain ⟨hAa,hAB⟩ := mem_filter.mp hA
    obtain ⟨hBp,hBa⟩ := mem_sdiff.mp hBF
    have heq := part_subset_eq n s.partition A B (s.active_subset hAa) hBp hAB
    exact hBa (heq ▸ hAa)
  · intro hn
    obtain ⟨A,hA,hAB⟩ := Finpartition.exists_le_of_le h.1 hB
    have hAa : A ∈ s.active := by
      by_contra hAa
      have hAf : A ∈ frozen n s := mem_sdiff.mpr ⟨hA,hAa⟩
      have heq := part_subset_eq n π A B (h.2 hAf) hB hAB
      exact hn (heq ▸ hAf)
    exact ⟨A,mem_filter.mpr ⟨hAa,hAB⟩⟩

private lemma freeze_compatible_iff (n : ℕ) (s : State n)
    (π : Finpartition (univ : Finset (Fin n))) (h : compatible n s π) (A : s.active) :
    compatible n (freeze n s A) π ↔ A.1 ∈ π.parts := by
  rw [compatible, freeze_partition, freeze_frozen]
  constructor
  · exact fun hh => hh.2 (mem_insert_self _ _)
  · exact fun hA => ⟨h.1, insert_subset_iff.mpr ⟨hA,h.2⟩⟩

private lemma freeze_compatible_back (n : ℕ) (s : State n)
    (π : Finpartition (univ : Finset (Fin n))) (A : s.active)
    (h : compatible n (freeze n s A) π) : compatible n s π := by
  rw [compatible, freeze_partition, freeze_frozen] at h
  exact ⟨h.1,(subset_insert _ _).trans h.2⟩

private lemma activeGroup_eq_singleton (n : ℕ) (s : State n) (A : s.active) :
    activeGroup n s A.1 = {A.1} := by
  classical
  ext B
  simp only [activeGroup, mem_filter, mem_singleton]
  constructor
  · rintro ⟨hB,hBA⟩
    exact part_subset_eq n s.partition B A.1 (s.active_subset hB) (s.active_subset A.2) hBA
  · rintro rfl
    exact ⟨A.2,Subset.refl _⟩

private lemma freeze_activeGroup (n : ℕ) (s : State n) (A : s.active) (B : Finset (Fin n)) :
    activeGroup n (freeze n s A) B = (activeGroup n s B).erase A.1 := by
  classical
  ext C
  simp only [activeGroup, freeze, mem_filter, mem_erase]
  tauto

private lemma freeze_activeGroup_other (n : ℕ) (s : State n)
    (π : Finpartition (univ : Finset (Fin n))) (A : s.active)
    (hA : A.1 ∈ π.parts) (B : Finset (Fin n)) (hB : B ∈ π.parts) (hne : B ≠ A.1) :
    activeGroup n (freeze n s A) B = activeGroup n s B := by
  classical
  rw [freeze_activeGroup]
  apply erase_eq_of_notMem
  intro hh
  have hAB := (mem_filter.mp hh).2
  exact hne (part_subset_eq n π A.1 B hA hB hAB).symm

private lemma merge_refines (n : ℕ) (s : State n) (p : Finset (Finset (Fin n)))
    (hp : p ⊆ s.active) (hne : p.Nonempty) :
    s.partition ≤ (merge n s p hp hne).partition := by
  intro A hA
  by_cases hAp : A ∈ p
  · exact ⟨p.biUnion id,mem_insert_self _ _,fun x hx => mem_biUnion.mpr ⟨A,hAp,hx⟩⟩
  · exact ⟨A,mem_insert_of_mem (mem_sdiff.mpr ⟨hA,hAp⟩),Subset.refl _⟩

private lemma merge_compatible_back (n : ℕ) (s : State n)
    (π : Finpartition (univ : Finset (Fin n))) (p : Finset (Finset (Fin n)))
    (hp : p ⊆ s.active) (hne : p.Nonempty)
    (h : compatible n (merge n s p hp hne) π) : compatible n s π := by
  refine ⟨(merge_refines n s p hp hne).trans h.1, ?_⟩
  have hf := h.2
  rw [merge_frozen] at hf
  exact hf

private lemma merge_compatible_iff (n : ℕ) (s : State n)
    (π : Finpartition (univ : Finset (Fin n))) (h : compatible n s π)
    (p : Finset (Finset (Fin n))) (hp : p ⊆ s.active) (hne : p.Nonempty) :
    compatible n (merge n s p hp hne) π ↔
      ∃ B ∈ π.parts, p ⊆ activeGroup n s B := by
  classical
  constructor
  · intro hh
    obtain ⟨B,hB,huB⟩ := hh.1 (show p.biUnion id ∈ (merge n s p hp hne).partition.parts from
      mem_insert_self _ _)
    refine ⟨B,hB,?_⟩
    intro A hA
    exact mem_filter.mpr ⟨hp hA,fun x hx => huB (mem_biUnion.mpr ⟨A,hA,hx⟩)⟩
  · rintro ⟨B,hB,hpB⟩
    refine ⟨?_,?_⟩
    · intro A hA
      change A ∈ insert (p.biUnion id) (s.partition.parts \ p) at hA
      rcases mem_insert.mp hA with rfl | hA
      · refine ⟨B,hB,?_⟩
        intro x hx
        obtain ⟨C,hC,hxC⟩ := mem_biUnion.mp hx
        exact (mem_filter.mp (hpB hC)).2 hxC
      · exact h.1 (mem_sdiff.mp hA).1
    · rw [merge_frozen]
      exact h.2

private lemma biUnion_activeGroup_eq (n : ℕ) (s : State n)
    (π : Finpartition (univ : Finset (Fin n))) (h : compatible n s π)
    (B : Finset (Fin n)) (hB : B ∈ π.parts) (hn : B ∉ frozen n s) :
    (activeGroup n s B).biUnion id = B := by
  classical
  apply Subset.antisymm
  · intro x hx
    obtain ⟨A,hA,hxA⟩ := mem_biUnion.mp hx
    exact (mem_filter.mp hA).2 hxA
  · intro x hxB
    obtain ⟨A,hA,hxA⟩ := s.partition.exists_mem (mem_univ x)
    obtain ⟨C,hC,hAC⟩ := h.1 hA
    have heq : C = B := π.eq_of_mem_parts hC hB (hAC hxA) hxB
    subst C
    have hAa : A ∈ s.active := by
      by_contra hAa
      have hAf : A ∈ frozen n s := mem_sdiff.mpr ⟨hA,hAa⟩
      have hAB : A = B := part_subset_eq n π A B (h.2 hAf) hB hAC
      exact hn (hAB ▸ hAf)
    exact mem_biUnion.mpr ⟨A,mem_filter.mpr ⟨hAa,hAC⟩,hxA⟩

private lemma group_card_one_iff (n : ℕ) (s : State n)
    (π : Finpartition (univ : Finset (Fin n))) (h : compatible n s π)
    (B : Finset (Fin n)) (hB : B ∈ π.parts) :
    (activeGroup n s B).card = 1 ↔ B ∈ s.active := by
  classical
  constructor
  · intro hc
    obtain ⟨A,hA⟩ := card_eq_one.mp hc
    have hg : (activeGroup n s B).Nonempty := by rw [hA]; exact singleton_nonempty _
    have heq := biUnion_activeGroup_eq n s π h B hB ((group_nonempty_iff n s π h B hB).mp hg)
    rw [hA] at heq
    simp only [singleton_biUnion,id_eq] at heq
    have ha : A ∈ activeGroup n s B := by rw [hA]; exact mem_singleton_self _
    exact heq ▸ (mem_filter.mp ha).1
  · intro hBa
    rw [activeGroup_eq_singleton n s ⟨B,hBa⟩,card_singleton]

private lemma pair_target_unique (n : ℕ) (s : State n)
    (π : Finpartition (univ : Finset (Fin n))) (p : Finset (Finset (Fin n)))
    (hne : p.Nonempty) (B C : Finset (Fin n)) (hB : B ∈ π.parts) (hC : C ∈ π.parts)
    (hpB : p ⊆ activeGroup n s B) (hpC : p ⊆ activeGroup n s C) : B = C := by
  obtain ⟨A,hA⟩ := hne
  have haB := mem_filter.mp (hpB hA)
  have haC := mem_filter.mp (hpC hA)
  obtain ⟨x,hx⟩ := s.partition.nonempty_of_mem_parts (s.active_subset haB.1)
  exact π.eq_of_mem_parts hB hC (haB.2 hx) (haC.2 hx)

private lemma merge_activeGroup_internal (n : ℕ) (s : State n)
    (p : Finset (Finset (Fin n))) (hp : p ⊆ s.active) (hne : p.Nonempty)
    (B : Finset (Fin n)) (hpB : p ⊆ activeGroup n s B) :
    activeGroup n (merge n s p hp hne) B =
      insert (p.biUnion id) (activeGroup n s B \ p) := by
  classical
  have huB : p.biUnion id ⊆ B := by
    intro x hx
    obtain ⟨A,hA,hxA⟩ := mem_biUnion.mp hx
    exact (mem_filter.mp (hpB hA)).2 hxA
  ext A
  simp only [activeGroup, merge, mem_filter, mem_insert, mem_sdiff]
  constructor
  · rintro ⟨hA,hAB⟩
    rcases hA with rfl | hA
    · exact Or.inl rfl
    · exact Or.inr ⟨⟨hA.1,hAB⟩,hA.2⟩
  · rintro (rfl | ⟨hA,hAp⟩)
    · exact ⟨Or.inl rfl,huB⟩
    · exact ⟨Or.inr ⟨hA.1,hAp⟩,hA.2⟩

private lemma merge_activeGroup_card (n : ℕ) (s : State n)
    (p : Finset (Finset (Fin n))) (hp : p ⊆ s.active) (hne : p.Nonempty) (hc : p.card = 2)
    (B : Finset (Fin n)) (hpB : p ⊆ activeGroup n s B) :
    (activeGroup n (merge n s p hp hne) B).card + 1 = (activeGroup n s B).card := by
  classical
  rw [merge_activeGroup_internal n s p hp hne B hpB]
  have hn : p.biUnion id ∉ activeGroup n s B \ p := by
    intro hu
    exact union_notMem_active_pair n s p hp hc (mem_filter.mp (mem_sdiff.mp hu).1).1
  rw [card_insert_of_notMem hn,card_sdiff_of_subset hpB,hc]
  have hle := card_le_card hpB
  rw [hc] at hle
  omega

private lemma merge_activeGroup_other (n : ℕ) (s : State n)
    (π : Finpartition (univ : Finset (Fin n)))
    (p : Finset (Finset (Fin n))) (hp : p ⊆ s.active) (hne : p.Nonempty)
    (B C : Finset (Fin n)) (hB : B ∈ π.parts) (hC : C ∈ π.parts) (hneBC : C ≠ B)
    (hpB : p ⊆ activeGroup n s B) :
    activeGroup n (merge n s p hp hne) C = activeGroup n s C := by
  classical
  have hbad : ∀ A ∈ p, ¬ A ⊆ C := by
    intro A hA hAC
    have haB := mem_filter.mp (hpB hA)
    obtain ⟨x,hx⟩ := s.partition.nonempty_of_mem_parts (s.active_subset haB.1)
    exact hneBC (π.eq_of_mem_parts hC hB (hAC hx) (haB.2 hx))
  have hbadU : ¬ p.biUnion id ⊆ C := by
    intro huC
    obtain ⟨A,hA⟩ := hne
    exact hbad A hA (fun x hx => huC (mem_biUnion.mpr ⟨A,hA,hx⟩))
  ext A
  simp only [activeGroup, merge, mem_filter, mem_insert, mem_sdiff]
  constructor
  · rintro ⟨hA,hAC⟩
    rcases hA with rfl | ⟨ha,hAp⟩
    · exact False.elim (hbadU hAC)
    · exact ⟨ha,hAC⟩
  · rintro ⟨ha,hAC⟩
    exact ⟨Or.inr ⟨ha,fun hAp => hbad A hAp hAC⟩,hAC⟩

private lemma powersetCard_activeGroup (n : ℕ) (s : State n) (B : Finset (Fin n)) :
    (activeGroup n s B).powersetCard 2 =
      (s.active.powersetCard 2).filter (fun p => p ⊆ activeGroup n s B) := by
  classical
  ext p
  simp only [mem_filter,mem_powersetCard]
  constructor
  · rintro ⟨hp,hc⟩
    exact ⟨⟨hp.trans (filter_subset _ _),hc⟩,hp⟩
  · rintro ⟨⟨hp,hc⟩,hpB⟩
    exact ⟨hpB,hc⟩

private lemma sum_freeze_groups (n : ℕ) (s : State n)
    (π : Finpartition (univ : Finset (Fin n))) (h : compatible n s π)
    (f : Finset (Fin n) → ℝ) :
    (∑ A ∈ s.active, if A ∈ π.parts then f A else 0) =
      ∑ B ∈ π.parts, if (activeGroup n s B).card = 1 then f B else 0 := by
  classical
  trans ∑ B ∈ π.parts, if B ∈ s.active then f B else 0
  · rw [←sum_filter,←sum_filter]
    congr 1
    ext A
    simp only [mem_filter]
    tauto
  · apply sum_congr rfl
    intro B hB
    simp only [group_card_one_iff n s π h B hB]

private lemma sum_merge_groups (n : ℕ) (s : State n)
    (π : Finpartition (univ : Finset (Fin n)))
    (f : Finset (Finset (Fin n)) → ℝ) :
    (∑ p ∈ s.active.powersetCard 2,
      if ∃ B ∈ π.parts, p ⊆ activeGroup n s B then f p else 0) =
      ∑ B ∈ π.parts, ∑ p ∈ (activeGroup n s B).powersetCard 2, f p := by
  classical
  have hsum : ∀ B ∈ π.parts,
      (∑ p ∈ (activeGroup n s B).powersetCard 2, f p) =
      ∑ p ∈ s.active.powersetCard 2, if p ⊆ activeGroup n s B then f p else 0 := by
    intro B hB
    rw [powersetCard_activeGroup,sum_filter]
  rw [sum_congr rfl hsum,sum_comm]
  apply sum_congr rfl
  intro p hp
  have hne : p.Nonempty := pair_nonempty n s ⟨p, hp⟩
  by_cases hg : ∃ B ∈ π.parts, p ⊆ activeGroup n s B
  · obtain ⟨B,hB,hpB⟩ := hg
    rw [ite_eq_left ⟨B,hB,hpB⟩,sum_eq_single B]
    · simp [hpB]
    · intro C hC hCB
      have hn : ¬ p ⊆ activeGroup n s C := by
        intro hpC
        exact hCB (pair_target_unique n s π p hne C B hC hB hpC hpB)
      simp [hn]
    · exact fun hn => False.elim (hn hB)
  · rw [ite_eq_right hg]
    symm
    apply sum_eq_zero
    intro B hB
    have hn : ¬ p ⊆ activeGroup n s B := fun hpB => hg ⟨B,hB,hpB⟩
    simp [hn]

private lemma freeze_nonfrozen_card (n : ℕ) (s : State n)
    (π : Finpartition (univ : Finset (Fin n))) (A : s.active) (hA : A.1 ∈ π.parts) :
    (π.parts \ frozen n (freeze n s A)).card + 1 = (π.parts \ frozen n s).card := by
  classical
  have hf : A.1 ∉ frozen n s := by
    intro hh
    exact (mem_sdiff.mp hh).2 A.2
  have hm : A.1 ∈ π.parts \ frozen n s := mem_sdiff.mpr ⟨hA,hf⟩
  have heq : π.parts \ frozen n (freeze n s A) = (π.parts \ frozen n s).erase A.1 := by
    rw [freeze_frozen]
    ext B
    simp only [mem_sdiff,mem_insert,mem_erase]
    tauto
  rw [heq,card_erase_of_mem hm]
  have hc := card_pos.mpr (show (π.parts \ frozen n s).Nonempty from ⟨A.1,hm⟩)
  omega

private lemma harmonic_product_freeze {ι : Type*}
    (T : Finset ι) (a b : ι → ℕ) (i : ι)
    (ha : a i = 1) (hb : b i = 0) (h : ∀ j ∈ T, j ≠ i → a j = b j) :
    (∏ j ∈ T, ((a j - 1).factorial : ℝ)) =
      ∏ j ∈ T, ((b j - 1).factorial : ℝ) := by
  classical
  apply prod_congr rfl
  intro j hj
  by_cases hji : j = i
  · subst j
    simp [ha, hb]
  · rw [h j hj hji]

private lemma harmonic_product_merge {ι : Type*}
    (T : Finset ι) (a b : ι → ℕ) (i : ι) (hi : i ∈ T)
    (ha : 2 ≤ a i) (hb : b i + 1 = a i)
    (h : ∀ j ∈ T, j ≠ i → a j = b j) :
    (∏ j ∈ T, ((a j - 1).factorial : ℝ)) =
      (a i - 1 : ℕ) * ∏ j ∈ T, ((b j - 1).factorial : ℝ) := by
  classical
  have hpred : b i - 1 + 1 = a i - 1 := by omega
  have he : (a i - 1).factorial = (a i - 1) * (b i - 1).factorial := by
    rw [← hpred, Nat.factorial_succ]
  rw [← mul_prod_erase T _ hi, ← mul_prod_erase T _ hi, he, Nat.cast_mul]
  have hrest : (∏ j ∈ T.erase i, ((a j - 1).factorial : ℝ)) =
      ∏ j ∈ T.erase i, ((b j - 1).factorial : ℝ) := by
    apply prod_congr rfl
    intro j hj
    rw [h j (mem_of_mem_erase hj) (mem_erase.mp hj).1]
  rw [hrest]
  ring

private lemma harmonic_rising_pred (θ : ℝ) (k : ℕ) (hk : 0 < k) :
    (ascPochhammer ℝ k).eval θ =
      (ascPochhammer ℝ (k - 1)).eval θ * (θ + k - 1) := by
  have he : k - 1 + 1 = k := by omega
  have hc : ((k - 1 : ℕ) : ℝ) = k - 1 := by
    exact_mod_cast Nat.cast_sub (R := ℝ) (show 1 ≤ k by omega)
  calc
    (ascPochhammer ℝ k).eval θ = (ascPochhammer ℝ (k - 1 + 1)).eval θ :=
      congrArg (fun m ↦ (ascPochhammer ℝ m).eval θ) he.symm
    _ = _ := by rw [ascPochhammer_succ_eval, hc]; ring

private lemma harmonic_freeze_weight (θ : ℝ) (hθ : 0 < θ)
    (k u : ℕ) (hk : 0 < k) (hu : 0 < u) (P : ℝ) :
    θ / ((k : ℝ) * (θ + k - 1)) *
        (θ ^ (u - 1) * P / (ascPochhammer ℝ (k - 1)).eval θ) =
      (θ ^ u * P / (ascPochhammer ℝ k).eval θ) / k := by
  have hp := (ascPochhammer_pos (k - 1) θ hθ).ne'
  have hrk : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hd : θ + k - 1 ≠ 0 := by linarith
  have heu : u - 1 + 1 = u := by omega
  have hpow : θ ^ u = θ ^ (u - 1) * θ := by
    calc
      θ ^ u = θ ^ (u - 1 + 1) := congrArg (fun m ↦ θ ^ m) heu.symm
      _ = _ := pow_succ θ (u - 1)
  rw [harmonic_rising_pred θ k hk, hpow]
  field_simp [hp, hrk, hd]

private lemma harmonic_merge_weight_each (θ : ℝ) (hθ : 0 < θ)
    (k u a : ℕ) (hk : 0 < k) (ha : 1 < a) (P Q : ℝ)
    (hP : P = (a - 1 : ℕ) * Q) :
    2 / ((k : ℝ) * (θ + k - 1)) *
        (θ ^ u * Q / (ascPochhammer ℝ (k - 1)).eval θ) =
      (2 / (a - 1 : ℕ)) * (θ ^ u * P / (ascPochhammer ℝ k).eval θ) / k := by
  have hp := (ascPochhammer_pos (k - 1) θ hθ).ne'
  have hrk : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hd : θ + k - 1 ≠ 0 := by linarith
  have ha1 : ((a - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show a - 1 ≠ 0 by omega)
  rw [harmonic_rising_pred θ k hk, hP]
  field_simp [hp, hrk, hd, ha1]

private lemma harmonic_group_sum {ι : Type*} (T : Finset ι) (a : ι → ℕ)
    (k : ℕ) (hk : 0 < k) (h : ∑ i ∈ T, a i = k) (H : ℝ) :
    (∑ i ∈ T, (a i : ℝ) * H / k) = H := by
  have hrk : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [← sum_div, ← sum_mul, ← Nat.cast_sum, h]
  field_simp

private def potential (θ : ℝ) (n : ℕ) (s : State n)
    (π : Finpartition (univ : Finset (Fin n))) : ℝ := by
  classical
  exact if compatible n s π then
    θ ^ (π.parts \ frozen n s).card *
      (∏ B ∈ π.parts, (((activeGroup n s B).card - 1).factorial : ℝ)) /
      (ascPochhammer ℝ s.active.card).eval θ
  else 0

private lemma potential_nonneg (θ : ℝ) (hθ : 0 < θ) (n : ℕ) (s : State n)
    (π : Finpartition (univ : Finset (Fin n))) : 0 ≤ potential θ n s π := by
  classical
  unfold potential
  split_ifs
  · have hp := (ascPochhammer_pos s.active.card θ hθ).le
    exact div_nonneg (mul_nonneg (pow_nonneg hθ.le _)
      (prod_nonneg (fun B _ => Nat.cast_nonneg _))) hp
  · exact le_refl 0

private lemma compatible_event_back (n : ℕ) (s : State n)
    (π : Finpartition (univ : Finset (Fin n))) (e : Event n s)
    (h : compatible n (applyEvent n s e) π) : compatible n s π := by
  cases e with
  | inl A => exact freeze_compatible_back n s π A h
  | inr p => exact merge_compatible_back n s π p.1 (pair_subset n s p) (pair_nonempty n s p) h

private lemma potential_event_of_incompatible (θ : ℝ) (n : ℕ) (s : State n)
    (π : Finpartition (univ : Finset (Fin n))) (h : ¬ compatible n s π)
    (e : Event n s) : potential θ n (applyEvent n s e) π = 0 := by
  classical
  have hn : ¬ compatible n (applyEvent n s e) π :=
    fun hh => h (compatible_event_back n s π e hh)
  simp [potential, hn]

private lemma potential_freeze_weight (θ : ℝ) (hθ : 0 < θ) (n : ℕ)
    (s : State n) (π : Finpartition (univ : Finset (Fin n)))
    (h : compatible n s π) (A : s.active) :
    θ / denominator θ s.active.card * potential θ n (freeze n s A) π =
      if A.1 ∈ π.parts then potential θ n s π / s.active.card else 0 := by
  classical
  have hk : 0 < s.active.card := card_pos.mpr ⟨A.1,A.2⟩
  by_cases hA : A.1 ∈ π.parts
  · have hs := (freeze_compatible_iff n s π h A).mpr hA
    have hAf : A.1 ∉ frozen n s := fun hh => (mem_sdiff.mp hh).2 A.2
    have hAu : A.1 ∈ π.parts \ frozen n s := mem_sdiff.mpr ⟨hA,hAf⟩
    have hu : 0 < (π.parts \ frozen n s).card := card_pos.mpr ⟨A.1,hAu⟩
    have huc : (π.parts \ frozen n (freeze n s A)).card =
        (π.parts \ frozen n s).card - 1 := by
      have := freeze_nonfrozen_card n s π A hA
      omega
    have hak : (activeGroup n s A.1).card = 1 := by
      rw [activeGroup_eq_singleton,card_singleton]
    have hbk : (activeGroup n (freeze n s A) A.1).card = 0 := by
      rw [freeze_activeGroup,activeGroup_eq_singleton]
      simp
    have hp := harmonic_product_freeze π.parts
      (fun B => (activeGroup n s B).card)
      (fun B => (activeGroup n (freeze n s A) B).card) A.1 hak hbk
      (fun B hB hBA => congrArg card (freeze_activeGroup_other n s π A hA B hB hBA).symm)
    have hc : (freeze n s A).active.card = s.active.card - 1 := by
      change (s.active.erase A.1).card = _
      rw [card_erase_of_mem A.2]
    simp only [potential,h,hs,ite_true,hA]
    rw [huc,hc,← hp]
    exact harmonic_freeze_weight θ hθ s.active.card (π.parts \ frozen n s).card hk hu _
  · have hs : ¬ compatible n (freeze n s A) π :=
      fun hs => hA ((freeze_compatible_iff n s π h A).mp hs)
    simp [potential,hs,hA]

private lemma potential_merge_weight (θ : ℝ) (hθ : 0 < θ) (n : ℕ)
    (s : State n) (π : Finpartition (univ : Finset (Fin n))) (h : compatible n s π)
    (p : Finset (Finset (Fin n))) (hp : p ⊆ s.active) (hne : p.Nonempty) (hc : p.card = 2)
    (B : Finset (Fin n)) (hB : B ∈ π.parts) (hpB : p ⊆ activeGroup n s B) :
    2 / denominator θ s.active.card * potential θ n (merge n s p hp hne) π =
      (2 / ((activeGroup n s B).card - 1 : ℕ)) * potential θ n s π / s.active.card := by
  classical
  have hk : 0 < s.active.card := card_pos.mpr (hne.mono hp)
  have hs := (merge_compatible_iff n s π h p hp hne).mpr ⟨B,hB,hpB⟩
  have ha : 2 ≤ (activeGroup n s B).card := by
    have he := card_le_card hpB
    rwa [hc] at he
  have hcount := merge_activeGroup_card n s p hp hne hc B hpB
  have hprod := harmonic_product_merge π.parts
    (fun C => (activeGroup n s C).card)
    (fun C => (activeGroup n (merge n s p hp hne) C).card) B hB ha hcount
    (fun C hC hCB => congrArg card (merge_activeGroup_other n s π p hp hne B C hB hC hCB hpB).symm)
  have hactive : (merge n s p hp hne).active.card = s.active.card - 1 := by
    have hpc : p ∈ s.active.powersetCard 2 := mem_powersetCard.mpr ⟨hp,hc⟩
    have he := applyEvent_active_card n s (Sum.inr ⟨p,hpc⟩)
    change (merge n s p hp hne).active.card + 1 = s.active.card at he
    omega
  simp only [potential,h,hs,ite_true]
  rw [merge_frozen,hactive]
  exact harmonic_merge_weight_each θ hθ s.active.card (π.parts \ frozen n s).card
    (activeGroup n s B).card hk (by omega) _ _ hprod


private lemma potential_freeze_sum (θ : ℝ) (hθ : 0 < θ) (n : ℕ)
    (s : State n) (π : Finpartition (univ : Finset (Fin n))) (h : compatible n s π) :
    (∑ A : s.active, eventWeight θ n s (Sum.inl A) * potential θ n (freeze n s A) π) =
      ∑ B ∈ π.parts, if (activeGroup n s B).card = 1 then
        potential θ n s π / s.active.card else 0 := by
  classical
  have hf : ∀ A : s.active,
      eventWeight θ n s (Sum.inl A) * potential θ n (freeze n s A) π =
        if A.1 ∈ π.parts then potential θ n s π / s.active.card else 0 := by
    intro A
    exact potential_freeze_weight θ hθ n s π h A
  simp_rw [hf]
  rw [sum_coe_sort s.active (fun A =>
    if A ∈ π.parts then potential θ n s π / s.active.card else 0), ← sum_filter]
  have he : s.active.filter (fun A => A ∈ π.parts) =
      π.parts.filter (fun A => A ∈ s.active) := by
    ext A
    simp [and_comm]
  rw [he,sum_filter]
  apply sum_congr rfl
  intro B hB
  simp only [group_card_one_iff n s π h B hB]

private lemma harmonic_group_contribution (a k : ℕ) (H : ℝ) :
    (if a = 1 then H / k else 0) +
        (a.choose 2 : ℝ) * ((2 / (a - 1 : ℕ)) * H / k) = a * H / k := by
  by_cases ha0 : a = 0
  · subst a
    simp
  by_cases ha1 : a = 1
  · subst a
    simp
  have hd : ((a - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show a - 1 ≠ 0 by omega)
  have hc := twice_choose_two a
  by_cases hk : (k : ℝ) = 0
  · simp [hk]
  simp only [ha1,ite_false,zero_add]
  field_simp [hd,hk]
  linear_combination H * hc

private lemma potential_merge_sum (θ : ℝ) (hθ : 0 < θ) (n : ℕ)
    (s : State n) (π : Finpartition (univ : Finset (Fin n))) (h : compatible n s π) :
    (∑ p : {p : Finset (Finset (Fin n)) // p ∈ s.active.powersetCard 2},
      eventWeight θ n s (Sum.inr p) * potential θ n (applyEvent n s (Sum.inr p)) π) =
      ∑ B ∈ π.parts, ((activeGroup n s B).card.choose 2 : ℝ) *
        ((2 / ((activeGroup n s B).card - 1 : ℕ)) * potential θ n s π / s.active.card) := by
  classical
  let f : Finset (Finset (Fin n)) → ℝ := fun p =>
    if hp : p ∈ s.active.powersetCard 2 then
      eventWeight θ n s (Sum.inr ⟨p,hp⟩) *
        potential θ n (applyEvent n s (Sum.inr ⟨p,hp⟩)) π
    else 0
  have hf : (∑ p : {p : Finset (Finset (Fin n)) // p ∈ s.active.powersetCard 2},
      eventWeight θ n s (Sum.inr p) * potential θ n (applyEvent n s (Sum.inr p)) π) =
      ∑ p ∈ s.active.powersetCard 2, f p := by
    calc
      _ = ∑ p : {p : Finset (Finset (Fin n)) // p ∈ s.active.powersetCard 2}, f p := by
        apply sum_congr rfl
        intro p hp
        simp only [f,dite_eq_left p.2]
      _ = _ := sum_coe_sort _ f
  rw [hf]
  have hz : ∀ p ∈ s.active.powersetCard 2,
      ¬ (∃ B ∈ π.parts, p ⊆ activeGroup n s B) → f p = 0 := by
    intro p hp hn
    have hpA : p ⊆ s.active := pair_subset n s ⟨p, hp⟩
    have hne : p.Nonempty := pair_nonempty n s ⟨p, hp⟩
    have hbad : ¬ compatible n (merge n s p hpA hne) π :=
      fun hh => hn ((merge_compatible_iff n s π h p hpA hne).mp hh)
    simp only [f,dite_eq_left hp,eventWeight,applyEvent]
    change 2 / denominator θ s.active.card * potential θ n (merge n s p hpA hne) π = 0
    rw [potential,ite_eq_right hbad,mul_zero]
  have hg : (∑ p ∈ s.active.powersetCard 2, f p) =
      ∑ p ∈ s.active.powersetCard 2,
        if ∃ B ∈ π.parts, p ⊆ activeGroup n s B then f p else 0 := by
    apply sum_congr rfl
    intro p hp
    by_cases hb : ∃ B ∈ π.parts, p ⊆ activeGroup n s B
    · simp only [hb,ite_true]
    · simp only [hb,ite_false,hz p hp hb]
  rw [hg,sum_merge_groups]
  apply sum_congr rfl
  intro B hB
  have hval : ∀ p ∈ (activeGroup n s B).powersetCard 2,
      f p = (2 / ((activeGroup n s B).card - 1 : ℕ)) *
        potential θ n s π / s.active.card := by
    intro p hp
    obtain ⟨hpB,hc⟩ := mem_powersetCard.mp hp
    have hpA : p ⊆ s.active := hpB.trans (filter_subset _ _)
    have hpLegal : p ∈ s.active.powersetCard 2 := mem_powersetCard.mpr ⟨hpA,hc⟩
    have hne : p.Nonempty := pair_nonempty n s ⟨p, hpLegal⟩
    simp only [f,dite_eq_left hpLegal,eventWeight,applyEvent]
    exact potential_merge_weight θ hθ n s π h p hpA hne hc B hB hpB
  rw [sum_congr rfl hval]
  simp only [sum_const,nsmul_eq_mul,card_powersetCard]

private lemma potential_harmonic (θ : ℝ) (hθ : 0 < θ) (n : ℕ) (s : State n)
    (π : Finpartition (univ : Finset (Fin n))) (hk : 0 < s.active.card) :
    (∑ e : Event n s, eventWeight θ n s e * potential θ n (applyEvent n s e) π) =
      potential θ n s π := by
  classical
  by_cases h : compatible n s π
  · rw [Fintype.sum_sum_type]
    change (∑ A : s.active, eventWeight θ n s (Sum.inl A) * potential θ n (freeze n s A) π) +
      (∑ p : {p : Finset (Finset (Fin n)) // p ∈ s.active.powersetCard 2},
        eventWeight θ n s (Sum.inr p) * potential θ n (applyEvent n s (Sum.inr p)) π) = _
    rw [potential_freeze_sum θ hθ n s π h,potential_merge_sum θ hθ n s π h,← sum_add_distrib]
    calc
      _ = ∑ B ∈ π.parts, (activeGroup n s B).card * potential θ n s π / s.active.card := by
        apply sum_congr rfl
        intro B hB
        exact harmonic_group_contribution (activeGroup n s B).card s.active.card (potential θ n s π)
      _ = _ := harmonic_group_sum π.parts (fun B => (activeGroup n s B).card) s.active.card hk
        (sum_activeGroup_card n s π h) _
  · have hz : ∀ e : Event n s, eventWeight θ n s e * potential θ n (applyEvent n s e) π = 0 := by
      intro e
      rw [potential_event_of_incompatible θ n s π h e,mul_zero]
    rw [sum_congr rfl (fun e _ => hz e)]
    simp [potential,h]

private lemma initial_compatible (n : ℕ) (π : Finpartition (univ : Finset (Fin n))) :
    compatible n (initial n) π := by
  refine ⟨bot_le, ?_⟩
  simp [frozen, initial]

private lemma initial_group_card (n : ℕ) (B : Finset (Fin n)) :
    (activeGroup n (initial n) B).card = B.card := by
  classical
  simp [activeGroup, initial, Finpartition.parts_bot, filter_map]

private lemma potential_initial (θ : ℝ) (n : ℕ)
    (π : Finpartition (univ : Finset (Fin n))) :
    potential θ n (initial n) π =
      MathlibExt.Biology.PopulationGenetics.ChineseRestaurant.crpProb θ π := by
  classical
  rw [potential, ite_eq_left (initial_compatible n π)]
  have hf : frozen n (initial n) = ∅ := by simp [frozen, initial]
  rw [hf, sdiff_empty, initial_active_card]
  simp_rw [initial_group_card]
  rfl

private lemma compatible_absorbed (n : ℕ) (s : State n)
    (π : Finpartition (univ : Finset (Fin n))) (ha : s.active = ∅) :
    compatible n s π ↔ s.partition = π := by
  constructor
  · intro h
    have hp : s.partition.parts ⊆ π.parts := by simpa [frozen,ha] using h.2
    apply le_antisymm h.1
    intro B hB
    obtain ⟨A,hA,hAB⟩ := Finpartition.exists_le_of_le h.1 hB
    have he := part_subset_eq n π A B (hp hA) hB hAB
    refine ⟨A,hA,?_⟩
    rw [he]
  · intro h
    refine ⟨le_of_eq h, ?_⟩
    simp [frozen,h,ha]

private lemma potential_absorbed (θ : ℝ) (n : ℕ) (s : State n)
    (π : Finpartition (univ : Finset (Fin n))) (ha : s.active = ∅) :
    potential θ n s π = if s.partition = π then 1 else 0 := by
  classical
  unfold potential
  rw [compatible_absorbed n s π ha]
  split_ifs with h
  · simp [frozen,ha,h,activeGroup]
  · rfl

private def expectation {α : Type*} [Fintype α] (p : PMF α) (f : α → ENNReal) : ENNReal :=
  ∑ x, p x * f x

private lemma expectation_pure {α : Type*} [Fintype α] (x : α) (f : α → ENNReal) :
    expectation (PMF.pure x) f = f x := by
  classical
  simp [expectation, PMF.pure_apply]

private lemma expectation_map {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (f : α → β) (g : β → ENNReal) :
    expectation (p.map f) g = expectation p (fun x ↦ g (f x)) := by
  classical
  simp only [expectation, PMF.map_apply, tsum_fintype, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro x hx
  simp [ite_mul]

private lemma expectation_bind {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (f : α → PMF β) (g : β → ENNReal) :
    expectation (p.bind f) g = expectation p (fun x ↦ expectation (f x) g) := by
  classical
  simp only [expectation, PMF.bind_apply, tsum_fintype, sum_mul, mul_sum, mul_assoc]
  rw [sum_comm]

private lemma run_expectation (θ : ℝ) (hθ : 0 < θ) (n : ℕ)
    (f : State n → ENNReal)
    (hf : ∀ s, expectation (step θ hθ n s) f = f s) (t : ℕ) :
    expectation (run θ hθ n t) f = f (initial n) := by
  induction t with
  | zero => exact expectation_pure _ _
  | succ t ih =>
    rw [run, expectation_bind]
    simp_rw [hf]
    exact ih

private lemma potential_step (θ : ℝ) (hθ : 0 < θ) (n : ℕ)
    (π : Finpartition (univ : Finset (Fin n)))
    (hh : ∀ (s : State n) (_hk : 0 < s.active.card),
      (∑ e : Event n s, eventWeight θ n s e * potential θ n (applyEvent n s e) π) =
        potential θ n s π) (s : State n) :
    expectation (step θ hθ n s) (fun r ↦ ENNReal.ofReal (potential θ n r π)) =
      ENNReal.ofReal (potential θ n s π) := by
  classical
  by_cases hk : 0 < s.active.card
  · rw [step, dite_eq_left hk, expectation_map]
    unfold expectation
    simp only [eventLaw_apply]
    have hn : ∀ e : Event n s, 0 ≤ eventWeight θ n s e :=
      eventWeight_nonneg θ hθ n s hk
    simp_rw [← ENNReal.ofReal_mul (hn _)]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun e _ ↦
      mul_nonneg (hn e) (potential_nonneg θ hθ n (applyEvent n s e) π)), hh s hk]
  · have hz : s.active.card = 0 := by omega
    rw [step_stutter θ hθ n s hz, expectation_pure]

private lemma terminal_of_harmonic (θ : ℝ) (hθ : 0 < θ) (n : ℕ)
    (hh : ∀ (s : State n) (π : Finpartition (univ : Finset (Fin n)))
      (_hk : 0 < s.active.card),
      (∑ e : Event n s, eventWeight θ n s e * potential θ n (applyEvent n s e) π) =
        potential θ n s π) :
    terminalLaw θ hθ n =
      MathlibExt.Biology.PopulationGenetics.ChineseRestaurant.crp θ hθ n := by
  classical
  ext π
  rw [MathlibExt.Biology.PopulationGenetics.ChineseRestaurant.crp_apply]
  have he := run_expectation θ hθ n (fun s ↦ ENNReal.ofReal (potential θ n s π))
    (potential_step θ hθ n π (fun s hk ↦ hh s π hk)) n
  rw [potential_initial] at he
  rw [← he]
  change ((run θ hθ n n).map State.partition) π = _
  simp only [PMF.map_apply, tsum_fintype, expectation]
  apply sum_congr rfl
  intro s hs
  by_cases hz : (run θ hθ n n) s = 0
  · simp [hz]
  · have ha := run_all_frozen θ hθ n s ((PMF.mem_support_iff _ _).mpr hz)
    rw [potential_absorbed θ n s π ha]
    by_cases hp : s.partition = π
    · simp [hp]
    · simp [hp,Ne.symm hp]

/-- **The terminal law is the Chinese restaurant process.** For `θ > 0`, the terminal law of
the neutral embedded jumps equals the native Chinese restaurant partition law. -/
theorem terminalLaw_eq_crp (θ : ℝ) (hθ : 0 < θ) (n : ℕ) :
    terminalLaw θ hθ n =
      MathlibExt.Biology.PopulationGenetics.ChineseRestaurant.crp θ hθ n := by
  exact terminal_of_harmonic θ hθ n (potential_harmonic θ hθ n)

/-- **Ewens sampling formula for the freeze-and-merge chain.** For `θ > 0`, each particular
labeled partition has the full Ewens probability, obtained from the terminal-law equality and the
native `crp_apply` and `crpProb` declarations. This is Theorem 2.2 of Donnelly and Tavaré (1986),
p. 6, at `k = 0`. -/
theorem terminalLaw_apply (θ : ℝ) (hθ : 0 < θ) (n : ℕ)
    (π : Finpartition (univ : Finset (Fin n))) :
    terminalLaw θ hθ n π = ENNReal.ofReal
      (θ ^ π.parts.card * π.cardProd (fun k => ((k-1).factorial : ℝ)) /
        (ascPochhammer ℝ n).eval θ) := by
  rw [terminalLaw_eq_crp]
  exact MathlibExt.Biology.PopulationGenetics.ChineseRestaurant.crp_apply hθ π

end Domains.Biology.PopulationGenetics.Coalescent.EwensFreezeMerge
