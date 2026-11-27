/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.CyclicPatternAvoidingStacks
import all MathlibExt.Combinatorics.Enumerative.CyclicPatternAvoidingStacks

/-!
# Strict reduction after a pass of the cyclic sorting machine for `123`

If the input has no increasing consecutive pair, we track its first entry and its successor
at the bottom of the cyclic stack. When the first entry is maximal, we instead track the two
largest entries through West's stack.

## References

* Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
  Article A15, Section 3.1, Lemmas 1 and 2 (pp. 5–6).
* Katalin Berlow, *Restricted Stacks as Functions*, Discrete Mathematics 344 (11) (2021),
  Article 112571 (the restricted-stack map).
* Julian West, *Permutations with restricted subsequences and stack-sortable permutations*,
  Ph.D. thesis, Massachusetts Institute of Technology (1990) (the deterministic sorting map).
-/

namespace MetaMathlibExt

namespace length_reductionSeq_cyclicSortingMachine_123_lt

open cyclicSortingMachine_123_iterate_eq_id_iff_reductionSeq

-- Processing a prefix leaves the protected bottom of the stack in place. Any continuation
-- then runs from that stack, and the entries above the bottom came only from the prefix or stack.
private theorem run_prefix (d : Bool) (s st bottom : List ℕ)
    (hsafe : ∀ x ∈ s, ¬bad d (x :: bottom)) :
    ∃ out above : List ℕ, (∀ x ∈ above, x ∈ s ++ st) ∧
      ∀ t, run d (s ++ t) (st ++ bottom) = out ++ run d t (above ++ bottom) := by
  cases s with
  | nil => exact ⟨[], st, by simp, by simp⟩
  | cons x xs =>
    by_cases hb : bad d (x :: (st ++ bottom))
    · cases st with
      | nil => exact (hsafe x (by simp) hb).elim
      | cons y ys =>
        obtain ⟨out, above, hm, he⟩ := run_prefix d (x :: xs) ys bottom hsafe
        refine ⟨y :: out, above, ?_, fun t => ?_⟩
        · intro z hz
          have := hm z hz
          simp only [List.mem_append, List.mem_cons] at this ⊢
          tauto
        · simp only [List.cons_append] at hb ⊢
          rw [run_pop hb, ← List.cons_append, he]
    · obtain ⟨out, above, hm, he⟩ := run_prefix d xs (x :: st) bottom
        (fun y hy => hsafe y (by simp [hy]))
      refine ⟨out, above, ?_, fun t => ?_⟩
      · intro z hz
        have := hm z hz
        simp only [List.mem_append, List.mem_cons] at this ⊢
        tauto
      · rw [List.cons_append, run_push hb]
        exact he t
termination_by 2 * s.length + st.length
decreasing_by
  all_goals subst_vars; simp
  omega

private theorem cyclic_not_bad_short {w : List ℕ} (hw : w.length < 3) : ¬bad true w := by
  rw [bad_iff]
  rintro ⟨s, hs, hf⟩
  have hl := hs.length_le
  simp [forbidden, rotations_123, SameRelativeOrder] at hf
  omega

private theorem cyclic_succ_forbidden (a y : ℕ) (h₁ : y ≠ a) (h₂ : y ≠ a + 1) :
    forbidden true [a + 1, y, a] := by
  simp [forbidden, rotations_123, SameRelativeOrder, Nat.forall_lt_succ_right]
  omega

-- The next entry `a + 1` forces every intervening entry out of the cyclic stack.
private theorem cyclic_push_succ (a : ℕ) (st rest : List ℕ)
    (hn : ∀ y ∈ st, y ≠ a ∧ y ≠ a + 1) :
    run true ((a + 1) :: rest) (st ++ [a]) = st ++ run true rest [a + 1, a] := by
  induction st with
  | nil => exact run_push (cyclic_not_bad_short (by simp))
  | cons y ys ih =>
    obtain ⟨h₁, h₂⟩ := hn y (by simp)
    have hsub : [a + 1, y, a].Sublist ((a + 1) :: y :: (ys ++ [a])) :=
      ((List.sublist_append_right _ _).cons_cons _).cons_cons _
    have hb : bad true ((a + 1) :: y :: (ys ++ [a])) :=
      (bad_iff ..).mpr ⟨_, hsub, cyclic_succ_forbidden a y h₁ h₂⟩
    simp only [List.cons_append]
    rw [run_pop hb, ih (fun z hz => hn z (by simp [hz]))]

private theorem cyclic_ends_first (a : ℕ) (s : List ℕ) :
    ∃ out, run true (a :: s) [] = out ++ [a] := by
  rw [run_push (bad_singleton true a)]
  obtain ⟨out, st, _, he⟩ := run_prefix true s [] [a]
    (fun _ _ => cyclic_not_bad_short (by simp))
  exact ⟨out ++ st, by simpa [List.append_assoc, restrictedStackSortAux] using he []⟩

private theorem cyclic_ends_pair (a : ℕ) (s : List ℕ) (hn : (a :: s).Nodup)
    (hm : a + 1 ∈ s) : ∃ out, run true (a :: s) [] = out ++ [a + 1, a] := by
  obtain ⟨u, v, rfl⟩ := List.append_of_mem hm
  have ha : a ∉ u := fun h => hn.notMem (List.mem_append_left _ h)
  have hs : a + 1 ∉ u := fun h => (List.nodup_append.mp hn.of_cons).2.2 _ h _ (by simp) rfl
  rw [run_push (bad_singleton true a)]
  obtain ⟨out, st, hst, he⟩ := run_prefix true u [] [a]
    (fun _ _ => cyclic_not_bad_short (by simp))
  rw [show [a] = [] ++ [a] by rfl, he, cyclic_push_succ a st v]
  · have hsafe (x : ℕ) : ¬bad true [x, a + 1, a] := by
      have h := bad_pair a true [x] []
      simp [liftEntry] at h
      exact h.not.mpr (not_or.mpr ⟨cyclic_not_bad_short (by simp),
        cyclic_not_bad_short (by simp)⟩)
    obtain ⟨out', st', _, he'⟩ := run_prefix true v [] [a + 1, a] (fun x _ => hsafe x)
    refine ⟨out ++ st ++ out' ++ st', ?_⟩
    have hv : run true v [a + 1, a] = out' ++ (st' ++ [a + 1, a]) := by
      simpa [restrictedStackSortAux] using he' []
    simp [hv, List.append_assoc]
  · intro y hy
    have hyu : y ∈ u := by simpa using hst y hy
    exact ⟨fun e => ha (e ▸ hyu), fun e => hs (e ▸ hyu)⟩

-- West's only obstruction to pushing onto a good stack is a smaller entry already there.
private theorem west_bad_cons (x : ℕ) (st : List ℕ) :
    bad false (x :: st) ↔ (∃ y ∈ st, y < x) ∨ bad false st := by
  have hpair (a b : ℕ) : forbidden false [a, b] ↔ b < a := by
    simp [forbidden, SameRelativeOrder, Nat.forall_lt_succ_right]
    omega
  constructor
  · intro hb
    obtain ⟨s, hsub, hf⟩ := (bad_iff ..).mp hb
    rcases List.sublist_cons_iff.mp hsub with ht | ⟨t, rfl, ht⟩
    · exact Or.inr ((bad_iff ..).mpr ⟨s, ht, hf⟩)
    · have hlen : (x :: t).length = 2 := hf.1
      cases t with
      | nil => simp at hlen
      | cons y t =>
        have ht' : t = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
        subst t
        exact Or.inl ⟨y, List.singleton_sublist.mp ht, (hpair x y).mp hf⟩
  · rintro (⟨y, hy, hyx⟩ | hb)
    · exact (bad_iff ..).mpr ⟨_, (List.singleton_sublist.mpr hy).cons_cons _, (hpair x y).mpr hyx⟩
    · exact bad_mono (List.sublist_cons_self ..) false hb

private theorem west_last_pair (a : ℕ) (st : List ℕ) :
    ∃ u v, run false [a + 1, a] st = u ++ a :: (a + 1) :: v := by
  induction st with
  | nil =>
    have h : ¬bad false [a, a + 1] := by simp [west_bad_cons, bad_singleton]
    exact ⟨[], [], by rw [run_push (bad_singleton false (a + 1)), run_push h]; rfl⟩
  | cons y ys ih =>
    by_cases hb : bad false ((a + 1) :: y :: ys)
    · obtain ⟨u, v, he⟩ := ih
      exact ⟨y :: u, v, by rw [run_pop hb, he]; rfl⟩
    · have hg : ¬bad false (a :: (a + 1) :: y :: ys) := by
        refine (west_bad_cons ..).not.mpr (not_or.mpr ⟨?_, hb⟩)
        rintro ⟨z, hz, hza⟩
        rcases List.mem_cons.mp hz with rfl | hz
        · omega
        · exact hb ((west_bad_cons ..).mpr (Or.inl ⟨z, hz, by omega⟩))
      exact ⟨[], y :: ys, by rw [run_push hb, run_push hg]; rfl⟩

private theorem west_flush (m : ℕ) (s st : List ℕ) (h : ∀ y ∈ st, y < m) :
    run false (m :: s) st = st ++ run false s [m] := by
  induction st with
  | nil => exact run_push (bad_singleton false m)
  | cons y ys ih =>
    have hb := (west_bad_cons m (y :: ys)).mpr (Or.inl ⟨y, by simp, h y (by simp)⟩)
    rw [run_pop hb, ih (fun z hz => h z (by simp [hz])), List.cons_append]

private theorem west_ends_max (m : ℕ) (s : List ℕ) (hn : s.Nodup)
    (hm : m ∈ s) (hbound : ∀ x ∈ s, x ≤ m) : ∃ u, run false s [] = u ++ [m] := by
  obtain ⟨u, v, rfl⟩ := List.append_of_mem hm
  obtain ⟨out, st, hst, he⟩ := run_prefix false u [] [] (fun x _ => bad_singleton false x)
  have hu : m ∉ u := fun h => (List.nodup_append.mp hn).2.2 _ h _ (by simp) rfl
  have hlt : ∀ x ∈ st ++ [], x < m := by
    intro x hx
    have hxu := hst x (by simpa using hx)
    simp only [List.append_nil] at hxu
    exact lt_of_le_of_ne (hbound x (List.mem_append_left _ hxu)) (fun h => hu (h ▸ hxu))
  simp only [List.nil_append] at he
  rw [he (m :: v), west_flush m v _ hlt]
  have hsafe (x : ℕ) (hx : x ∈ v) : ¬bad false [x, m] := by
    simp [west_bad_cons, bad_singleton, Nat.not_lt.mpr (hbound x (by simp [hx]))]
  obtain ⟨out', st', _, hv⟩ := run_prefix false v [] [m] hsafe
  have hv' : run false v [m] = out' ++ (st' ++ [m]) := by
    simpa [restrictedStackSortAux] using hv []
  exact ⟨out ++ st ++ out' ++ st', by simp [hv', List.append_assoc]⟩

private theorem west_append_max (m : ℕ) (s : List ℕ) (hbound : ∀ x ∈ s, x < m) :
    run false (s ++ [m]) [] = run false s [] ++ [m] := by
  obtain ⟨out, st, hst, he⟩ := run_prefix false s [] [] (fun x _ => bad_singleton false x)
  have hlt : ∀ x ∈ st ++ [], x < m := fun x hx =>
    hbound x (by simpa using hst x (by simpa using hx))
  simp only [List.nil_append] at he
  have hz : run false s [] = out ++ st := by simpa [restrictedStackSortAux] using he []
  rw [he [m], hz, west_flush m [] _ hlt]
  simp [List.append_assoc, restrictedStackSortAux]

private theorem machine_has_pair {n : ℕ} (hn : 2 ≤ n) {π : List ℕ}
    (hπ : π.Perm (List.range' 1 n)) : ∃ u a v, machine π = u ++ a :: (a + 1) :: v := by
  cases π with
  | nil =>
    have h := hπ.length_eq
    simp at h
    omega
  | cons a s =>
    have ha := List.mem_range'_1.mp (hπ.mem_iff.mp (List.mem_cons_self ..))
    have hnodup := hπ.nodup_iff.mpr (List.nodup_range' 1)
    change ∃ u b v, run false (run true (a :: s) []) [] = u ++ b :: (b + 1) :: v
    by_cases h : a = n
    · subst a
      obtain ⟨p, hp⟩ := cyclic_ends_first n s
      have hperm : (p ++ [n]).Perm (List.range' 1 n) := by
        rw [← hp]
        exact (run_perm true (n :: s) []).trans (by simpa using hπ)
      have hnp := hperm.nodup_iff.mpr (List.nodup_range' 1)
      have hlt (x : ℕ) (hx : x ∈ p) : x < n := by
        have hb := List.mem_range'_1.mp (hperm.mem_iff.mp (List.mem_append_left _ hx))
        have hne : x ≠ n := fun h => (List.nodup_append.mp hnp).2.2 _ hx _ (by simp) h
        omega
      have hm : n - 1 ∈ p := by
        have hm := hperm.mem_iff.mpr (List.mem_range'_1.mpr
          (by omega : 1 ≤ n - 1 ∧ n - 1 < 1 + n))
        simpa [show n - 1 ≠ n by omega] using hm
      obtain ⟨u, hu⟩ := west_ends_max (n - 1) p (List.nodup_append.mp hnp).1 hm
        (fun x hx => by have := hlt x hx; omega)
      refine ⟨u, n - 1, [], ?_⟩
      rw [hp, west_append_max n p hlt, hu]
      simp [List.append_assoc, show n - 1 + 1 = n by omega]
    · have hm : a + 1 ∈ s := by
        have hm := hπ.mem_iff.mpr (List.mem_range'_1.mpr
          (by omega : 1 ≤ a + 1 ∧ a + 1 < 1 + n))
        simpa using hm
      obtain ⟨p, hp⟩ := cyclic_ends_pair a s hnodup hm
      obtain ⟨out, st, _, he⟩ := run_prefix false p [] [] (fun x _ => bad_singleton false x)
      obtain ⟨u, v, hw⟩ := west_last_pair a (st ++ [])
      simp only [List.nil_append] at he
      exact ⟨out ++ u, a, v, by rw [hp, he [a + 1, a], hw, List.append_assoc]⟩

private theorem reduction_length_le (s : List ℕ) : (reductionSeq s).length ≤ s.length := by
  have h (p : Option ℕ) (t : List ℕ) : (consecutiveRunHeads p t).length ≤ t.length := by
    induction t generalizing p with
    | nil => cases p <;> simp [consecutiveRunHeads]
    | cons x xs ih =>
      cases p with
      | none => simpa [consecutiveRunHeads] using ih (some x)
      | some y =>
        have ht := ih (some x)
        simp only [consecutiveRunHeads, List.length_cons]
        split <;> simp only [List.length_append, List.length_nil, List.length_cons] <;> omega
  simpa [reductionSeq, standardizeSeq] using h none s

private theorem reduction_length_lt_of_pair (u v : List ℕ) (a : ℕ)
    (hn : (u ++ a :: (a + 1) :: v).Nodup) :
    (reductionSeq (u ++ a :: (a + 1) :: v)).length < (u ++ a :: (a + 1) :: v).length := by
  have he := congrArg reductionSeq (expand_contract_pair a u v hn)
  rw [reduction_expand] at he
  rw [← he]
  refine (reduction_length_le _).trans_lt ?_
  have hu := (List.filter_sublist (p := fun x : ℕ => !decide (x = a + 1)) (l := u)).length_le
  have hv := (List.filter_sublist (p := fun x : ℕ => !decide (x = a + 1)) (l := v)).length_le
  simp [contract, List.filter_append]
  omega

end length_reductionSeq_cyclicSortingMachine_123_lt

open cyclicSortingMachine_123_iterate_eq_id_iff_reductionSeq
  length_reductionSeq_cyclicSortingMachine_123_lt in
/-- **After one pass of the $123$ cyclic sorting machine, the reduction is shorter.** For every
$n \ge 2$ and every permutation $\pi$ of $[n] = \{1, \ldots, n\}$, the reduction
$\operatorname{red}(\mathrm{SC}_{[123]}(\pi))$ of the image of $\pi$ under the cyclic sorting
machine $\mathrm{SC}_{[123]}$ has fewer than $n$ entries.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Lemma 2 (`integers-2026-A15-lem-2`). -/
public theorem length_reductionSeq_cyclicSortingMachine_123_lt {n : ℕ} (hn : 2 ≤ n)
    {π : List ℕ} (hπ : π.Perm (List.range' 1 n)) :
    (reductionSeq (cyclicSortingMachine [1, 2, 3] π)).length < n := by
  by_cases h₂ : n = 2
  · subst n
    have hl : π.length = 2 := by simpa using hπ.length_eq
    obtain ⟨x, y, rfl⟩ : ∃ x y, π = [x, y] := ⟨_, _, List.eq_getElem_of_length_eq_two π hl⟩
    have hx : x = 1 ∨ x = 2 := by
      have := List.mem_range'_1.mp (hπ.mem_iff.mp (by simp : x ∈ [x, y]))
      omega
    have hy : y = 1 ∨ y = 2 := by
      have := List.mem_range'_1.mp (hπ.mem_iff.mp (by simp : y ∈ [x, y]))
      omega
    have hne : x ≠ y := by
      simpa using hπ.nodup_iff.mpr (List.nodup_range' 1)
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> first | contradiction | decide
  by_cases h : ∃ u a v, π = u ++ a :: (a + 1) :: v
  · obtain ⟨u, a, v, rfl⟩ := h
    have hred := reduction_length_lt_of_pair u v a (hπ.nodup_iff.mpr (List.nodup_range' 1))
    rw [← reductionSeq_cyclicSortingMachine_123_reductionSeq hπ]
    calc
      _ ≤ (machine (reductionSeq (u ++ a :: (a + 1) :: v))).length := reduction_length_le _
      _ = (reductionSeq (u ++ a :: (a + 1) :: v)).length := (machine_perm _).length_eq
      _ < n := by simpa using hred.trans_le (by simpa using hπ.length_eq.le)
  · obtain ⟨u, a, v, he⟩ := machine_has_pair hn hπ
    have hperm := (machine_perm π).trans hπ
    have hlen : (machine π).length = n := by simpa using hperm.length_eq
    have hnodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
    change (reductionSeq (machine π)).length < n
    rw [he] at hlen hnodup ⊢
    rw [← hlen]
    exact reduction_length_lt_of_pair u v a hnodup

end MetaMathlibExt
