/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.CyclicPatternAvoidingStacks
import Mathlib.Data.List.Sublists

/-!
# One pass of the cyclic sorting machine for `321` on superimposed runs

For `n ≥ 4` and `1 ≤ m < ⌊(2n + 1) / 3⌋`, the cyclic sorting machine `SC_[321] = s ∘ s_[321]`
sends the superimposition `si((1, …, m), (m + 1, …, n))` to `si((1, …, m + 1), (m + 2, …, n))`.

The superimposition grows at its right end by blocks `u, u + 1, w` of two small entries and a
large one, after an initial run of large entries starting with `m + 1`. We follow both passes
block by block. The first pass keeps `m + 1` at the bottom of its stack, with at most one small
and one large entry above it. West's pass then holds at most one small entry above one large
entry.
-/

namespace MetaMathlibExt
namespace cyclicSortingMachine_321_superimpose

-- The number of entries popped before pushing `x`, as computed by `restrictedStackSortAux`.
private def popCount (bad : List ℕ → Prop) [DecidablePred bad] (x : ℕ) (st : List ℕ) : ℕ :=
  ((List.range (st.length + 1)).find? fun k => !decide (bad (x :: st.drop k))).getD st.length

private theorem popCount_cons (bad : List ℕ → Prop) [DecidablePred bad] (x y : ℕ)
    (st : List ℕ) :
    popCount bad x (y :: st) = if bad (x :: y :: st) then popCount bad x st + 1 else 0 := by
  unfold popCount
  rw [List.length_cons, List.range_succ_eq_map, List.find?_cons, List.find?_map]
  simp only [List.drop_zero, List.drop_succ_cons, Function.comp_def]
  split_ifs <;> simp_all

private theorem run_pop {bad : List ℕ → Prop} [DecidablePred bad] {x y : ℕ} {xs st : List ℕ}
    (hb : bad (x :: y :: st)) :
    restrictedStackSortAux bad (x :: xs) (y :: st) =
      y :: restrictedStackSortAux bad (x :: xs) st := by
  change (y :: st).take (popCount bad x (y :: st)) ++
      restrictedStackSortAux bad xs (x :: (y :: st).drop (popCount bad x (y :: st))) =
    y :: (st.take (popCount bad x st) ++
      restrictedStackSortAux bad xs (x :: st.drop (popCount bad x st)))
  simp [popCount_cons, hb]

private theorem run_push {bad : List ℕ → Prop} [DecidablePred bad] {x : ℕ} {xs st : List ℕ}
    (hg : ¬bad (x :: st)) :
    restrictedStackSortAux bad (x :: xs) st = restrictedStackSortAux bad xs (x :: st) := by
  have hz : popCount bad x st = 0 := by
    cases st with
    | nil => simp [popCount, List.range_succ_eq_map, hg]
    | cons y st => simp [popCount_cons, hg]
  change st.take (popCount bad x st) ++
    restrictedStackSortAux bad xs (x :: st.drop (popCount bad x st)) = _
  simp [hz]

private theorem run_nil {bad : List ℕ → Prop} [DecidablePred bad] (st : List ℕ) :
    restrictedStackSortAux bad [] st = st := rfl

-- The stack of `s_[321]`, read from top to bottom, contains a rotation of `321` as a pattern.
private def cbad (st : List ℕ) : Prop :=
  ∃ p ∈ ([3, 2, 1] : List ℕ).cyclicPermutations, ContainsPatternSeq st p

private instance decidableCbad : DecidablePred cbad := fun st => by
  unfold cbad
  infer_instance

-- The stack of West's map, read from top to bottom, contains the pattern `21`.
private def wbad (st : List ℕ) : Prop :=
  ContainsPatternSeq st [2, 1]

private instance decidableWbad : DecidablePred wbad := fun st => by
  unfold wbad
  infer_instance

local notation "runC" => restrictedStackSortAux cbad
local notation "runW" => restrictedStackSortAux wbad

-- The rotations of `321` are `321`, `213` and `132`.
private theorem rotations :
    ([3, 2, 1] : List ℕ).cyclicPermutations = [[3, 2, 1], [2, 1, 3], [1, 3, 2]] := by decide

private theorem cbad_of_sublist {s w : List ℕ} (h : s.Sublist w) (hs : cbad s) : cbad w := by
  obtain ⟨p, hp, t, ht, ho⟩ := hs
  exact ⟨p, hp, t, List.mem_sublists.mpr ((List.mem_sublists.mp ht).trans h), ho⟩

private theorem not_cbad_of_length_le {st : List ℕ} (h : st.length ≤ 2) : ¬cbad st := by
  rintro ⟨p, hp, s, hs, ho⟩
  have hlen := (List.mem_sublists.mp hs).length_le
  have hl := ho.1
  rw [rotations] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> simp at hl <;> omega

-- A list of length three is its only sublist of length three.
private theorem contains_three_iff (a b c : ℕ) {p : List ℕ} (hp : p.length = 3) :
    ContainsPatternSeq [a, b, c] p ↔ SameRelativeOrder [a, b, c] p := by
  constructor
  · rintro ⟨s, hs, ho⟩
    have hlen : s.length = [a, b, c].length := by rw [ho.1, hp]; rfl
    rwa [(List.mem_sublists.mp hs).eq_of_length hlen] at ho
  · exact fun ho => ⟨_, List.mem_sublists.mpr (List.Sublist.refl _), ho⟩

-- A list of three entries contains a rotation of `321` exactly when it is one.
private theorem cbad_three (a b c : ℕ) :
    cbad [a, b, c] ↔ (b < a ∧ c < b) ∨ (b < a ∧ a < c) ∨ (a < c ∧ c < b) := by
  simp only [cbad, rotations, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left]
  rw [contains_three_iff _ _ _ rfl, contains_three_iff _ _ _ rfl, contains_three_iff _ _ _ rfl]
  simp [SameRelativeOrder, Nat.forall_lt_succ_right]
  omega

private theorem contains_two_iff (a b : ℕ) {p : List ℕ} (hp : p.length = 2) :
    ContainsPatternSeq [a, b] p ↔ SameRelativeOrder [a, b] p := by
  constructor
  · rintro ⟨s, hs, ho⟩
    have hlen : s.length = [a, b].length := by rw [ho.1, hp]; rfl
    rwa [(List.mem_sublists.mp hs).eq_of_length hlen] at ho
  · exact fun ho => ⟨_, List.mem_sublists.mpr (List.Sublist.refl _), ho⟩

private theorem wbad_pair (a b : ℕ) : wbad [a, b] ↔ b < a := by
  rw [wbad, contains_two_iff _ _ rfl]
  simp [SameRelativeOrder, Nat.forall_lt_succ_right]
  omega

private theorem not_wbad_single (a : ℕ) : ¬wbad [a] := by
  rintro ⟨s, hs, ho⟩
  have := (List.mem_sublists.mp hs).length_le
  have := ho.1
  simp_all

private theorem wbad_cons_cons {a b : ℕ} (st : List ℕ) (h : b < a) : wbad (a :: b :: st) := by
  obtain ⟨s, hs, ho⟩ := (wbad_pair a b).mpr h
  refine ⟨s, List.mem_sublists.mpr ((List.mem_sublists.mp hs).trans ?_), ho⟩
  exact ((List.nil_sublist st).cons_cons b).cons_cons a

-- An increasing run above the bottom entry: each new entry pops the previous one.
private theorem runC_run {b c : ℕ} (hbc : b < c) (l : ℕ) (ys : List ℕ) :
    runC (List.range' (c + 1) l ++ ys) [c, b] = List.range' c l ++ runC ys [c + l, b] := by
  induction l generalizing c with
  | zero => simp
  | succ l ih =>
    rw [List.range'_succ, List.cons_append,
      run_pop ((cbad_three _ _ _).mpr (Or.inl ⟨by omega, hbc⟩)),
      run_push (not_cbad_of_length_le (by simp)), ih (by omega), List.range'_succ]
    simp [Nat.add_right_comm, Nat.add_assoc]

-- A small entry pushed on a large one and the bottom entry pops the large one.
private theorem runC_small_large {u ℓ b : ℕ} (hub : u < b) (hbℓ : b < ℓ) (ys : List ℕ) :
    runC (u :: ys) [ℓ, b] = ℓ :: runC ys [u, b] := by
  rw [run_pop ((cbad_three _ _ _).mpr (Or.inr (Or.inr ⟨hub, hbℓ⟩))),
    run_push (not_cbad_of_length_le (by simp))]

-- A larger small entry pops a smaller one sitting on the bottom entry.
private theorem runC_small_small {t u b : ℕ} (htu : t < u) (hub : u < b) (ys : List ℕ) :
    runC (u :: ys) [t, b] = t :: runC ys [u, b] := by
  rw [run_pop ((cbad_three _ _ _).mpr (Or.inr (Or.inl ⟨htu, hub⟩))),
    run_push (not_cbad_of_length_le (by simp))]

-- A large entry goes on top of a small entry and the bottom entry.
private theorem runC_large {s b w : ℕ} (hsb : s < b) (hbw : b < w) (ys : List ℕ) :
    runC (w :: ys) [s, b] = runC ys [w, s, b] := by
  refine run_push ?_
  rw [cbad_three]
  omega

-- One block `u, u + 1, w` of the superimposition.
private theorem runC_block {ℓ t u w b : ℕ} (htu : t < u) (hub : u + 1 < b) (hbℓ : b < ℓ)
    (hbw : b < w) (ys : List ℕ) :
    runC ([u, u + 1, w] ++ ys) [ℓ, t, b] = [ℓ, t, u] ++ runC ys [w, u + 1, b] := by
  have h₁ : cbad [u, ℓ, t, b] :=
    cbad_of_sublist (s := [u, ℓ, b]) (((List.Sublist.refl [b]).cons t).cons_cons ℓ |>.cons_cons u)
      ((cbad_three _ _ _).mpr (Or.inr (Or.inr ⟨by omega, hbℓ⟩)))
  rw [List.cons_append, run_pop h₁, runC_small_small htu (by omega), List.cons_append,
    runC_small_small (by omega) hub, List.cons_append, List.nil_append, runC_large hub hbw]
  rfl

-- Pushing an entry larger than the whole stack pops the whole stack.
private theorem runW_pop_all {w : ℕ} (zs : List ℕ) :
    ∀ {W : List ℕ}, (∀ x ∈ W, x < w) → runW (w :: zs) W = W ++ runW zs [w]
  | [], _ => run_push (not_wbad_single w)
  | x :: W, h => by
    rw [run_pop (wbad_cons_cons _ (h x (by simp))),
      runW_pop_all zs (fun y hy => h y (by simp [hy]))]
    rfl

-- An increasing run: each new entry pops the previous one.
private theorem runW_run (c l : ℕ) (zs : List ℕ) :
    runW (List.range' (c + 1) l ++ zs) [c] = List.range' c l ++ runW zs [c + l] := by
  induction l generalizing c with
  | zero => simp
  | succ l ih =>
    rw [List.range'_succ, List.cons_append, runW_pop_all _ (by simp), ih, List.range'_succ]
    simp [Nat.add_right_comm, Nat.add_assoc]

-- One block `w, k, k + 1` of the output of the first pass.
private theorem runW_block {w k : ℕ} {W : List ℕ} (hW : ∀ x ∈ W, x < w) (hk : k + 1 < w)
    (zs : List ℕ) : runW ([w, k, k + 1] ++ zs) W = W ++ [k] ++ runW zs [k + 1, w] := by
  rw [List.cons_append, runW_pop_all _ hW, List.cons_append,
    run_push (by rw [wbad_pair]; omega), List.cons_append,
    run_pop (wbad_cons_cons _ (by omega)), run_push (by rw [wbad_pair]; omega)]
  simp

private theorem superimposePush_nil_left (b : List ℕ) : superimposePush [] b = b := by
  cases b <;> simp [superimposePush]

private theorem superimpose_nil_left (σ : List ℕ) : superimpose [] σ = σ := by
  simp [superimpose, superimposePush_nil_left]

private theorem superimpose_nil_right (σ : List ℕ) : superimpose σ [] = σ := by
  simp [superimpose, superimposePush]

-- The superimposition grows at its right end by two entries of the first run and one of the second.
private theorem superimpose_snoc (σ₁ σ₂ : List ℕ) (u v w : ℕ) :
    superimpose (σ₁ ++ [u, v]) (σ₂ ++ [w]) = superimpose σ₁ σ₂ ++ [u, v, w] := by
  simp [superimpose, superimposePush]

private theorem superimpose_single (u : ℕ) (σ : List ℕ) (w : ℕ) :
    superimpose [u] (σ ++ [w]) = σ ++ [u, w] := by
  simp [superimpose, superimposePush, superimposePush_nil_left]

-- The first entries of the output of the first pass form an increasing run.
private theorem runW_initial (c r : ℕ) (zs : List ℕ) :
    runW (List.range' c r ++ (c + r) :: zs) [] = List.range' c r ++ runW zs [c + r] := by
  rw [← List.singleton_append, ← List.append_assoc, ← List.range'_1_concat, List.range'_succ,
    List.cons_append, run_push (not_wbad_single c), runW_run]

-- After the prefix `si((1, …, k), (m + 1, …, m + j))` of the input, the first pass has the stack
-- `m + j, k, m + 1`; the second pass has emitted `O` and holds `W`, all below the next large entry.
private def Stage (m k j : ℕ) : Prop :=
  ∃ O W : List ℕ,
    (∀ ys, runW (runC (superimpose (List.range' 1 k) (List.range' (m + 1) j) ++ ys) []) [] =
      O ++ runW (runC ys [m + j, k, m + 1]) W) ∧
    (∀ x ∈ W, x < m + j) ∧
    superimpose (List.range' 1 (k + 1)) (List.range' (m + 2) (j - 1)) = O ++ W ++ [k, k + 1, m + j]

private theorem stage_step {m k j : ℕ} (hkm : k + 2 ≤ m) (hj : 2 ≤ j)
    (h : Stage m k j) : Stage m (k + 2) (j + 1) := by
  obtain ⟨O, W, hrun, hW, hT⟩ := h
  refine ⟨O ++ W ++ [k], [k + 1, m + j], fun ys => ?_, ?_, ?_⟩
  · have hI : superimpose (List.range' 1 (k + 2)) (List.range' (m + 1) (j + 1)) =
        superimpose (List.range' 1 k) (List.range' (m + 1) j) ++ [k + 1, k + 2, m + j + 1] := by
      rw [List.range'_1_concat, List.range'_1_concat, List.range'_1_concat (s := m + 1),
        List.append_assoc, List.singleton_append, superimpose_snoc]
      simp only [List.append_cancel_left_eq, List.cons.injEq, and_true]
      omega
    rw [hI, List.append_assoc, hrun, runC_block (by omega) (by omega) (by omega) (by omega),
      runW_block hW (by omega)]
    simp [Nat.add_assoc]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    omega
  · have hT' : superimpose (List.range' 1 (k + 2 + 1)) (List.range' (m + 2) (j + 1 - 1)) =
        superimpose (List.range' 1 (k + 1)) (List.range' (m + 2) (j - 1)) ++
          [k + 2, k + 3, m + j + 1] := by
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [List.range'_1_concat, List.range'_1_concat, Nat.add_sub_cancel,
        List.range'_1_concat (s := m + 2), List.append_assoc, List.singleton_append,
        superimpose_snoc]
      simp [Nat.add_assoc]
      omega
    rw [hT', hT]
    simp [Nat.add_assoc]

-- An initial run `m + 1, …, m + r + 2` of large entries leaves its last entry above `m + 1`.
private theorem runC_initial (m r : ℕ) (ys : List ℕ) :
    runC (List.range' (m + 1) (r + 2) ++ ys) [] =
      List.range' (m + 2) r ++ runC ys [m + 2 + r, m + 1] := by
  rw [List.range'_succ, List.cons_append, run_push (not_cbad_of_length_le (by simp)),
    List.range'_succ, List.cons_append, run_push (not_cbad_of_length_le (by simp))]
  exact runC_run (by omega) r ys

-- For odd `m`, the input starts with `r` large entries, then `1` and a large entry.
private theorem stage_odd {m r : ℕ} (hm : 1 ≤ m) (hr : 1 ≤ r) : Stage m 1 (r + 1) := by
  have hI : superimpose (List.range' 1 1) (List.range' (m + 1) (r + 1)) =
      List.range' (m + 1) r ++ [1, m + 1 + r] := by
    rw [List.range'_1_concat (s := m + 1)]
    exact superimpose_single 1 _ _
  obtain rfl | ⟨r, rfl⟩ : r = 1 ∨ ∃ r', r = r' + 2 :=
    (by rcases r with _ | _ | r <;> simp_all)
  · refine ⟨[], [], fun ys => ?_, by simp, ?_⟩
    · rw [hI]
      simp only [List.range'_succ, List.range'_zero, List.cons_append, List.nil_append]
      rw [run_push (not_cbad_of_length_le (by simp)), run_push (not_cbad_of_length_le (by simp)),
        runC_large (by omega) (by omega)]
    · simp [superimpose, superimposePush, List.range'_succ]
  · refine ⟨List.range' (m + 2) r, [m + 2 + r], fun ys => ?_, ?_, ?_⟩
    · rw [hI, List.append_assoc, runC_initial, List.cons_append,
        runC_small_large (by omega) (by omega), List.cons_append, List.nil_append,
        runC_large (by omega) (by omega), runW_initial,
        show m + (r + 2 + 1) = m + 1 + (r + 2) by omega]
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      omega
    · rw [show r + 2 + 1 - 1 = r + 1 + 1 by omega, List.range'_1_concat (s := m + 2) (n := r + 1),
        show List.range' 1 (1 + 1) = [] ++ [1, 2] from rfl, superimpose_snoc,
        superimpose_nil_left, List.range'_1_concat]
      simp only [List.append_cancel_left_eq, List.cons.injEq, and_true, true_and]
      omega

-- For even `m`, the input starts with `r` large entries, then `1, 2` and a large entry.
private theorem stage_even {m r : ℕ} (hm : 2 ≤ m) (hr : 1 ≤ r) : Stage m 2 (r + 1) := by
  have hI : superimpose (List.range' 1 2) (List.range' (m + 1) (r + 1)) =
      List.range' (m + 1) r ++ [1, 2, m + 1 + r] := by
    rw [List.range'_1_concat (s := m + 1), show List.range' 1 2 = [] ++ [1, 2] from rfl,
      superimpose_snoc, superimpose_nil_left]
  obtain rfl | ⟨r, rfl⟩ : r = 1 ∨ ∃ r', r = r' + 2 :=
    (by rcases r with _ | _ | r <;> simp_all)
  · refine ⟨[], [1], fun ys => ?_, ?_, ?_⟩
    · rw [hI]
      simp only [List.range'_succ, List.range'_zero, List.cons_append, List.nil_append]
      rw [run_push (not_cbad_of_length_le (by simp)), run_push (not_cbad_of_length_le (by simp)),
        runC_small_small (by omega) (by omega), runC_large (by omega) (by omega),
        run_push (not_wbad_single _)]
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      omega
    · rw [show List.range' 1 (2 + 1) = [1] ++ [2, 3] from rfl,
        show List.range' (m + 2) (1 + 1 - 1) = [] ++ [m + 2] from rfl, superimpose_snoc,
        superimpose_nil_right]
      simp only [List.cons_append, List.nil_append]
  · refine ⟨List.range' (m + 2) r, [1, m + 2 + r], fun ys => ?_, ?_, ?_⟩
    · rw [hI, List.append_assoc, runC_initial, List.cons_append,
        runC_small_large (by omega) (by omega), List.cons_append,
        runC_small_small (by omega) (by omega), List.cons_append, List.nil_append,
        runC_large (by omega) (by omega), runW_initial, run_push (by rw [wbad_pair]; omega),
        show m + (r + 2 + 1) = m + 1 + (r + 2) by omega]
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      omega
    · rw [show r + 2 + 1 - 1 = r + 1 + 1 by omega, List.range'_1_concat (s := m + 2) (n := r + 1),
        show List.range' 1 (2 + 1) = [1] ++ [2, 3] from rfl, superimpose_snoc,
        List.range'_1_concat, superimpose_single]
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_cancel_left_eq,
        List.cons.injEq, and_true, true_and]
      omega

-- Iterating the block step reaches every later stage of the same parity.
private theorem stage_iter {m k j : ℕ} (h : Stage m k j) (hj : 2 ≤ j) :
    ∀ i, k + 2 * i ≤ m → Stage m (k + 2 * i) (j + i)
  | 0, _ => h
  | i + 1, hi => by
    have := stage_step (by omega) (by omega) (stage_iter h hj i (by omega))
    rwa [show k + 2 * i + 2 = k + 2 * (i + 1) by omega, Nat.add_assoc] at this

end cyclicSortingMachine_321_superimpose

-- The hypothesis `4 ≤ n` is kept from the source statement; the proof does not use it.
set_option linter.unusedVariables false in
open cyclicSortingMachine_321_superimpose in
/-- **One pass of $SC_{[321]}$ on superimposed increasing runs.** Let $n \ge 4$ and
$1 \le m < \lceil (2n-1)/3 \rceil = \lfloor (2n+1)/3 \rfloor$. Then the cyclic avoidance machine
$SC_{[321]}$ maps the superimposition $\mathrm{si}((1, \dots, m), (m+1, \dots, n))$ to
$\mathrm{si}((1, \dots, m+1), (m+2, \dots, n))$.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Lemma 3 (`integers-2026-A15-lem-3`). -/
public theorem cyclicSortingMachine_321_superimpose {n m : ℕ} (hn : 4 ≤ n) (hm : 1 ≤ m)
    (hmn : m < (2 * n + 1) / 3) :
    cyclicSortingMachine [3, 2, 1] (superimpose (List.range' 1 m) (List.range' (m + 1) (n - m))) =
      superimpose (List.range' 1 (m + 1)) (List.range' (m + 2) (n - m - 1)) := by
  have hstage : Stage m m (n - m) := by
    obtain ⟨q, rfl | rfl⟩ : ∃ q, m = 2 * q ∨ m = 2 * q + 1 := ⟨m / 2, by omega⟩
    · -- For even `m`, the input starts with `n - 3q` large entries, then `1, 2` and a large entry.
      have h := stage_iter (stage_even (m := 2 * q) (r := n - 3 * q) (by omega) (by omega))
        (by omega) (q - 1) (by omega)
      rwa [show 2 + 2 * (q - 1) = 2 * q by omega,
        show n - 3 * q + 1 + (q - 1) = n - 2 * q by omega] at h
    · -- For odd `m`, the input starts with `n - 3q - 2` large entries, then `1` and a large entry.
      have h := stage_iter (stage_odd (m := 2 * q + 1) (r := n - 3 * q - 2) (by omega) (by omega))
        (by omega) q (by omega)
      rwa [show 1 + 2 * q = 2 * q + 1 by omega,
        show n - 3 * q - 2 + 1 + q = n - (2 * q + 1) by omega] at h
  obtain ⟨O, W, hrun, hW, hT⟩ := hstage
  have hn' : m + (n - m) = n := by omega
  have h := hrun []
  rw [List.append_nil, run_nil, hn'] at h
  rw [hn'] at hW hT
  have hlast := runW_block hW (show m + 1 < n by omega) []
  rw [List.append_nil, run_nil] at hlast
  change restrictedStackSortAux wbad (restrictedStackSortAux cbad _ []) [] = _
  rw [h, hT, hlast]
  simp

end MetaMathlibExt
