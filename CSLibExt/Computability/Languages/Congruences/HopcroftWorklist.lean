/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.Congruences.HopcroftCost

/-!
# Pending-splitter accounting for Hopcroft's algorithm

The accounting uses the existing partition and waiting list, not a new
machine model. A pending entry can be replaced repeatedly without being
popped. Replacement preserves its credit; adding a smaller half spends
one unit of the logarithmic block-size potential.
-/

@[expose] public section

namespace DFA.Hopcroft

variable {α σ : Type*} [DecidableEq α] [DecidableEq σ]

/-- **Splitter count of a state and letter.**
Number of splitters with letter `b` containing `q`, with multiplicity.
This applies both to the waiting list and to the actual popped trace. -/
def splitterCount (q : σ) (b : α) (W : List (Finset σ × α)) : ℕ :=
  W.countP fun cb => decide (cb.2 = b ∧ q ∈ cb.1)

@[simp]
theorem splitterCount_nil (q : σ) (b : α) :
    splitterCount q b [] = 0 := rfl

@[simp]
theorem splitterCount_cons (q : σ) (b : α) (cb : Finset σ × α)
    (W : List (Finset σ × α)) :
    splitterCount q b (cb :: W) =
      splitterCount q b W + if cb.2 = b ∧ q ∈ cb.1 then 1 else 0 := by
  simp [splitterCount, List.countP_cons]

@[simp]
theorem splitterCount_append (q : σ) (b : α)
    (W V : List (Finset σ × α)) :
    splitterCount q b (W ++ V) =
      splitterCount q b W + splitterCount q b V := by
  exact List.countP_append

private theorem splitterCount_flatMap {β : Type*} (q : σ) (b : α)
    (L : List β) (f : β → List (Finset σ × α)) :
    splitterCount q b (L.flatMap f) =
      (L.map fun x => splitterCount q b (f x)).sum :=
  List.countP_flatMap

variable [FinEnum α]

/-- **Splitter count of newly added splitters.**
Replacement contributes one token at a state in the parent block;
otherwise only membership in the smaller half contributes a token. -/
theorem splitterCount_newSplitters (q : σ) (b : α)
    (W : List (Finset σ × α)) (pre D : Finset σ) :
    splitterCount q b (newSplitters W pre D) =
      if (D, b) ∈ W then (if q ∈ D then 1 else 0)
      else if q ∈ smaller (D.filter (· ∈ pre))
          (D.filter (· ∉ pre)) then 1 else 0 := by
  unfold newSplitters
  rw [splitterCount_flatMap,
    ← List.sum_toFinset _ FinEnum.nodup_toList]
  rw [Finset.sum_eq_single b]
  · by_cases hw : (D, b) ∈ W
    · by_cases hq : q ∈ D <;> by_cases hp : q ∈ pre <;>
        simp [hw, splitterCount_cons, hq, hp]
    · simp [hw, splitterCount_cons]
  · intro c _ hcb
    by_cases hw : (D, c) ∈ W <;> simp [hw, splitterCount_cons, hcb]
  · simp [FinEnum.mem_toList]

private theorem splitterCount_newSplitters_of_not_mem (q : σ) (b : α)
    (W : List (Finset σ × α)) (pre D : Finset σ) (hq : q ∉ D) :
    splitterCount q b (newSplitters W pre D) = 0 := by
  apply List.countP_eq_zero.mpr
  intro cb hcb hh
  have hh' : cb.2 = b ∧ q ∈ cb.1 := by simpa using hh
  exact hq ((mem_newSplitters hcb).1 hh'.2)

variable [Fintype σ]

omit [FinEnum α] [Fintype σ] in
private theorem splitterCount_retained {P : List (Finset σ)}
    (hP : IsPartition P) (W : List (Finset σ × α))
    (hW : ∀ cb ∈ W, cb.1 ∈ P) (q : σ) (b : α)
    (pre D : Finset σ) (hD : D ∈ P) (hq : q ∈ D) :
    splitterCount q b (W.filter fun cb => !decide (Splits pre cb.1)) =
      if Splits pre D then 0 else splitterCount q b W := by
  unfold splitterCount
  rw [List.countP_filter]
  have heq : ∀ cb ∈ W, q ∈ cb.1 → cb.1 = D :=
    fun cb hcb hq' => hP.eq_of_mem (hW cb hcb) hD hq' hq
  by_cases hs : Splits pre D
  · rw [ite_eq_left hs]
    apply List.countP_eq_zero.mpr
    intro cb hcb hh
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      decide_eq_false_iff_not] at hh
    exact hh.2 ((heq cb hcb hh.1.2).symm ▸ hs)
  · rw [ite_eq_right hs]
    apply List.countP_congr
    intro cb hcb
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      decide_eq_false_iff_not]
    exact ⟨And.left, fun hh => ⟨hh, (heq cb hcb hh.2).symm ▸ hs⟩⟩

omit [Fintype σ] in
private theorem splitterCount_generated {P : List (Finset σ)}
    (hP : IsPartition P) (W : List (Finset σ × α)) (q : σ) (b : α)
    (pre D : Finset σ) (hD : D ∈ P) (hq : q ∈ D) :
    splitterCount q b ((P.filter fun E => decide (Splits pre E)).flatMap
        (newSplitters W pre)) =
      if Splits pre D then splitterCount q b (newSplitters W pre D)
      else 0 := by
  rw [splitterCount_flatMap,
    ← List.sum_toFinset _ (hP.nodup.filter _)]
  have hz : ∀ E ∈ P, E ≠ D →
      splitterCount q b (newSplitters W pre E) = 0 := by
    intro E hE hne
    apply splitterCount_newSplitters_of_not_mem
    exact fun hqE => hne (hP.eq_of_mem hE hD hqE hq)
  by_cases hs : Splits pre D
  · rw [ite_eq_left hs]
    apply Finset.sum_eq_single D
    · intro E hE hne
      exact hz E (List.mem_filter.mp (List.mem_toFinset.mp hE)).1 hne
    · simp [hD, hs]
  · rw [ite_eq_right hs]
    apply Finset.sum_eq_zero
    intro E hE
    obtain ⟨hEP, hEs⟩ := List.mem_filter.mp (List.mem_toFinset.mp hE)
    apply hz E hEP
    intro heq
    subst E
    exact hs (of_decide_eq_true hEs)

/-- **Splitter count update after one Hopcroft round.**
The exact token update at a state. Only its unique parent block can
contribute a new token, even when other blocks split in the same round. -/
theorem splitterCount_roundW (M : DFA α σ) {P : List (Finset σ)}
    (hP : IsPartition P) (W : List (Finset σ × α))
    (hW : ∀ cb ∈ W, cb.1 ∈ P) (q : σ) (b : α)
    (C D : Finset σ) (a : α) (hD : D ∈ P) (hq : q ∈ D) :
    splitterCount q b (roundW M P W C a) =
      if Splits (preimage M C a) D then
        if (D, b) ∈ W then 1
        else if q ∈ smaller (D.filter (· ∈ preimage M C a))
            (D.filter (· ∉ preimage M C a)) then 1 else 0
      else splitterCount q b W := by
  rw [roundW, splitterCount_append,
    splitterCount_retained hP W hW q b _ D hD hq,
    splitterCount_generated hP W q b _ D hD hq,
    splitterCount_newSplitters]
  by_cases hs : Splits (preimage M C a) D <;> simp [hs, hq]

omit [FinEnum α] [Fintype σ] in
/-- **Waiting entries give positive splitter count.**
A waiting entry supplies a token; duplicate entries remain counted. -/
theorem splitterCount_pos_of_mem (q : σ) (b : α)
    {W : List (Finset σ × α)} {D : Finset σ}
    (hW : (D, b) ∈ W) (hq : q ∈ D) : 0 < splitterCount q b W := by
  by_contra h
  have hz : splitterCount q b W = 0 := by omega
  have hn := List.countP_eq_zero.mp hz (D, b) hW
  simp [hq] at hn

omit [DecidableEq α] [FinEnum α] in
/-- **Refined Hopcroft blocks lie inside their old blocks.**
A refined block containing `q` is a subset of the old block
containing `q`. Both partitions are the canonical Hopcroft partitions. -/
theorem IsPartition.subset_of_mem_roundP (M : DFA α σ)
    {P : List (Finset σ)} (hP : IsPartition P)
    {C D E : Finset σ} {a : α} {q : σ}
    (hD : D ∈ P) (hqD : q ∈ D)
    (hE : E ∈ Hopcroft.roundP M P C a) (hqE : q ∈ E) : E ⊆ D := by
  obtain ⟨B, hB, hEB⟩ := List.mem_flatMap.mp hE
  have hsub := subset_of_mem_splitBlock hEB
  obtain rfl := hP.eq_of_mem hB hD (hsub hqE) hqD
  exact hsub

omit [DecidableEq α] [FinEnum α] in
private theorem log_child_lt_of_mem_smaller (M : DFA α σ)
    {P : List (Finset σ)} (hP : IsPartition P)
    {C D E : Finset σ} {a : α} {q : σ} (hD : D ∈ P)
    (hE : E ∈ roundP M P C a) (hqE : q ∈ E)
    (hs : Splits (preimage M C a) D)
    (hqS : q ∈ smaller (D.filter (· ∈ preimage M C a))
      (D.filter (· ∉ preimage M C a))) :
    Nat.log 2 E.card + 1 ≤ Nat.log 2 D.card := by
  let S := smaller (D.filter (· ∈ preimage M C a))
    (D.filter (· ∉ preimage M C a))
  have hS : S ∈ roundP M P C a := by
    apply List.mem_flatMap.mpr
    refine ⟨D, hD, ?_⟩
    dsimp [S, smaller]
    split_ifs <;> simp [splitBlock, hs]
  have heq : E = S := (hP.roundP C a).eq_of_mem hE hS hqE hqS
  have hhalf : 2 * E.card ≤ D.card := by
    rw [heq]
    exact two_mul_smaller_card_le_of_split
      (Finset.filter_union_filter_not_eq _ D)
      (Finset.disjoint_filter_filter_not D D _)
  calc
    Nat.log 2 E.card + 1 = Nat.log 2 (E.card * 2) :=
      (Nat.log_mul_base (by decide)
        (Finset.card_ne_zero.mpr ⟨q, hqE⟩)).symm
    _ ≤ Nat.log 2 D.card := Nat.log_mono_right (by omega)

/-- **Potential inequality for one Hopcroft refinement round.**
One refinement cannot increase logarithmic block-size credit plus
pending-token credit. Replacing a pending splitter spends no new credit;
adding a nonpending smaller half spends one logarithmic unit. -/
theorem splitterCount_round_potential (M : DFA α σ)
    {P : List (Finset σ)} (hP : IsPartition P)
    (W : List (Finset σ × α)) (hW : ∀ cb ∈ W, cb.1 ∈ P)
    (q : σ) (b : α) {C D E : Finset σ} {a : α}
    (hD : D ∈ P) (hqD : q ∈ D)
    (hE : E ∈ roundP M P C a) (hqE : q ∈ E) :
    splitterCount q b (roundW M P W C a) + Nat.log 2 E.card ≤
      splitterCount q b W + Nat.log 2 D.card := by
  have hlog : Nat.log 2 E.card ≤ Nat.log 2 D.card :=
    Nat.log_mono_right (Finset.card_le_card
      (hP.subset_of_mem_roundP M hD hqD hE hqE))
  rw [splitterCount_roundW M hP W hW q b C D a hD hqD]
  split_ifs with hs hw hqS
  · have hpos := splitterCount_pos_of_mem q b hw hqD
    omega
  · have hdrop := log_child_lt_of_mem_smaller M hP hD hE hqE hs hqS
    omega
  · omega
  · omega

/-- **Splitter count bound along a Hopcroft execution.**
Total state/letter charging along the actual execution. The bound
includes initial tokens and tokens still pending through replacements.
No amortized bound is assumed in the execution invariant. -/
theorem splitterCount_hopcroftSplitters_le (M : DFA α σ) (k : ℕ)
    {P : List (Finset σ)} {W : List (Finset σ × α)} (hI : Inv M P W)
    (q : σ) (b : α) {D : Finset σ} (hD : D ∈ P) (hqD : q ∈ D) :
    splitterCount q b (hopcroftSplitters M k P W) ≤
      splitterCount q b W + Nat.log 2 D.card := by
  induction k generalizing P W D with
  | zero => simp [hopcroftSplitters]
  | succ k ih =>
    cases W with
    | nil => simp [hopcroftSplitters]
    | cons cb W =>
      obtain ⟨C, a⟩ := cb
      obtain ⟨E, hE, hqE⟩ := hI.round.part.cover q
      have ht := ih hI.round hE hqE
      have hw : ∀ cb ∈ W, cb.1 ∈ P :=
        fun cb hcb => hI.mem cb (List.mem_cons_of_mem _ hcb)
      have hp := splitterCount_round_potential M hI.part W hw
        q b hD hqD hE hqE
      simp only [hopcroftSplitters, splitterCount_cons]
      omega

/-- **Initial splitter count is at most one.**
Initially there is at most one token for each state and letter. -/
theorem splitterCount_initW_le (M : DFA α σ)
    [DecidablePred (· ∈ M.accept)] (q : σ) (b : α) :
    splitterCount q b (initW M) ≤ 1 := by
  unfold initW
  split_ifs
  · by_cases hq : q ∈ smaller (accBlock M) (rejBlock M)
    · have hc : splitterCount q b ((FinEnum.toList α).map fun c =>
          (smaller (accBlock M) (rejBlock M), c)) =
          (FinEnum.toList α).count b := by
        unfold splitterCount List.count
        rw [List.countP_map]
        apply List.countP_congr
        intro c _
        simp [hq]
      rw [hc, List.count_eq_one_of_mem FinEnum.nodup_toList
        (FinEnum.mem_toList b)]
    · simp [splitterCount, List.countP_map, Function.comp_def, hq]
  · simp

/-- **Hopcroft visits each of $n$ states at most $\log_2 n + 1$ times per letter.**
Each state is processed with a fixed letter at most `log₂ n + 1`
times during any prefix of the actual initialized Hopcroft execution. -/
theorem splitterCount_init_trace_le (M : DFA α σ)
    [DecidablePred (· ∈ M.accept)] (k : ℕ) (q : σ) (b : α) :
    splitterCount q b (hopcroftSplitters M k (initP M) (initW M)) ≤
      Nat.log 2 (Fintype.card σ) + 1 := by
  obtain ⟨D, hD, hqD⟩ := (inv_init M).part.cover q
  have ht := splitterCount_hopcroftSplitters_le M k (inv_init M) q b hD hqD
  have hi := splitterCount_initW_le M q b
  have hl : Nat.log 2 D.card ≤ Nat.log 2 (Fintype.card σ) :=
    Nat.log_mono_right (Finset.card_le_univ D)
  omega

omit [DecidableEq α] in
/-- **Popped Hopcroft splitters are nonempty.**
Every popped splitter has a nonempty block, including splitters whose
predecessor set is empty. -/
theorem nonempty_of_mem_hopcroftSplitters (M : DFA α σ) (k : ℕ)
    {P : List (Finset σ)} {W : List (Finset σ × α)} (hI : Inv M P W)
    {cb : Finset σ × α} (hcb : cb ∈ hopcroftSplitters M k P W) :
    cb.1.Nonempty := by
  induction k generalizing P W with
  | zero => simp [hopcroftSplitters] at hcb
  | succ k ih =>
    cases W with
    | nil => simp [hopcroftSplitters] at hcb
    | cons da W =>
      obtain ⟨D, a⟩ := da
      rcases List.mem_cons.mp hcb with rfl | hcb
      · exact hI.part.nonempty D (hI.mem (D, a) List.mem_cons_self)
      · exact ih hI.round hcb

end DFA.Hopcroft
