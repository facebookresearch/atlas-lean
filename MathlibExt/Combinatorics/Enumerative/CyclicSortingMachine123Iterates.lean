/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.CyclicSortingMachineReductionLength
import Mathlib.Data.List.Permutation
import all MathlibExt.Combinatorics.Enumerative.CyclicPatternAvoidingStacks
import all MathlibExt.Combinatorics.Enumerative.CyclicSortingMachineReductionLength
import all MathlibExt.Combinatorics.Enumerative.CyclicSortingMachineSuperimpose

/-!
# Sharp iteration bound for the cyclic sorting machine for `123`

For `n ≥ 3`, the machine sorts every permutation of `1, …, n` in `n - 2` passes, but does not sort
`xiPermutation n` in `n - 3` passes. The upper bound uses the strict decrease in reduced length.
For sharpness, we trace both stacks on the parity blocks and express the output as an expansion
of the preceding witness.

## References

* Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
  Article A15, Theorem 1 (p. 3), proof in Section 3.1 (pp. 6–7).
* Katalin Berlow, *Restricted Stacks as Functions*, Discrete Mathematics 344 (11) (2021),
  Article 112571 (the restricted-stack map).
* Julian West, *Permutations with forbidden subsequences and stack-sortable permutations*,
  Ph.D. thesis, Massachusetts Institute of Technology (1990) (the deterministic sorting map).
* `CyclicPatternAvoidingStacks` supplies the stack transitions, consecutive-pair expansion and
  `cyclicSortingMachine_123_iterate_eq_id_iff_reductionSeq`. We also use `cyclic_push_succ` and
  `west_bad_cons` from `CyclicSortingMachineReductionLength` and `runW_pop_all` from
  `CyclicSortingMachineSuperimpose`.
-/

namespace MetaMathlibExt

namespace CyclicSortingMachine123Iterates

open cyclicSortingMachine_123_iterate_eq_id_iff_reductionSeq
open reductionSeq_cyclicSortingMachine_123_reductionSeq (expansion_induction)
open length_reductionSeq_cyclicSortingMachine_123_lt (cyclic_push_succ west_bad_cons)
open cyclicSortingMachine_321_superimpose (runW_pop_all)

private theorem reduction_perm {n : ℕ} {s : List ℕ} (hs : s.Perm (List.range' 1 n)) :
    (reductionSeq s).Perm (List.range' 1 (reductionSeq s).length) := by
  apply expansion_induction (P := fun _ t =>
    (reductionSeq t).Perm (List.range' 1 (reductionSeq t).length)) _ _ hs
  · intro n t ht he
    simpa only [he, ht.length_eq, List.length_range'] using ht
  · intro n t a _ _ _ ih
    simpa only [reduction_expand] using ih

private theorem sorts_small {n : ℕ} (hn : n ≤ 3) {s : List ℕ}
    (hs : s.Perm (List.range' 1 n)) : machine s = List.range' 1 n := by
  have hmem := List.mem_permutations'.mpr hs
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  all_goals
    exact (by decide +kernel : ∀ t ∈ (List.range' 1 _).permutations',
      machine t = List.range' 1 _) s hmem

private theorem sorts_at_least {n j : ℕ} (hj : max 1 (n - 2) ≤ j) {s : List ℕ}
    (hs : s.Perm (List.range' 1 n)) : machine^[j] s = List.range' 1 n := by
  induction n using Nat.strong_induction_on generalizing j s with
  | ind n ih =>
    by_cases hn : n ≤ 3
    · have hfix := sorts_small hn (List.Perm.refl (List.range' 1 n))
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      rw [Function.iterate_succ_apply, sorts_small hn hs]
      exact Function.iterate_fixed hfix k
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      rw [Function.iterate_succ_apply]
      have hp := (machine_perm s).trans hs
      refine (cyclicSortingMachine_123_iterate_eq_id_iff_reductionSeq hp).mpr ?_
      have hlt := length_reductionSeq_cyclicSortingMachine_123_lt (by omega : 2 ≤ n) hs
      exact ih _ hlt (by omega) (reduction_perm hp)

-- Write each parity block as an arithmetic progression of step two.
private abbrev stride (a m : ℕ) := List.range' a m 2

private theorem filter_parity_range (s m b : ℕ) (hs : s % 2 = b) :
    ((List.range' s (2 * m)).filter fun x => x % 2 = b) = stride s m ∧
    ((List.range' s (2 * m)).filter fun x => x % 2 ≠ b) = stride (s + 1) m := by
  induction m generalizing s with
  | zero => simp
  | succ m ih =>
    have hstep : List.range' s (2 * (m + 1)) = s :: (s + 1) :: List.range' (s + 2) (2 * m) := by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega]
      rfl
    have he : (s + 1) % 2 ≠ b := by omega
    obtain ⟨heq, hne⟩ := ih (s + 2) (by omega)
    have hne' : ((List.range' (s + 2) (2 * m)).filter fun x => !decide (x % 2 = b)) =
        stride (s + 1 + 2) m := by
      simpa [Nat.add_right_comm] using hne
    simp [hstep, hs, he, heq, hne', List.range'_succ]

private theorem xi_even (m : ℕ) : xiPermutation (2 * m) = stride 1 m ++ stride 2 m := by
  obtain ⟨ho, he⟩ := filter_parity_range 1 m 1 rfl
  have hp (x : ℕ) : (x % 2 ≠ 0) = (x % 2 = 1) := propext (by omega)
  have hq (x : ℕ) : (x % 2 = 0) = (x % 2 ≠ 1) := propext (by omega)
  simp only [xiPermutation, show 2 * m % 2 = 0 by omega, hp, hq, ho, he]

private theorem xi_odd (m : ℕ) : xiPermutation (2 * m + 1) = stride 2 m ++ stride 1 (m + 1) := by
  obtain ⟨ho, he⟩ := filter_parity_range 1 m 1 rfl
  simp only [xiPermutation, show (2 * m + 1) % 2 = 1 by omega, List.range'_1_concat,
    List.filter_append, ho, he, List.filter_cons, List.filter_nil]
  rw [show stride 1 (m + 1) = stride 1 m ++ [1 + 2 * m] from List.range'_concat]
  simp [show (1 + 2 * m) % 2 = 1 by omega]

private theorem xi_perm (n : ℕ) : (xiPermutation n).Perm (List.range' 1 n) := by
  simpa only [xiPermutation, decide_not, Bool.not_not] using
    List.filter_append_perm (fun x : ℕ => decide (x % 2 ≠ n % 2)) (List.range' 1 n)

-- A forbidden triple with a descent at the end must start between the two other entries.
private theorem not_forbidden_of_extreme {x y z : ℕ} (hzy : z < y) (hx : x < z ∨ y < x) :
    ¬forbidden true [x, y, z] := by
  intro h
  simp only [forbidden, ite_true, rotations_123, List.mem_cons, List.not_mem_nil, or_false,
    exists_eq_or_imp, exists_eq_left] at h
  rcases h with h | h | h
  · have hyz : y < z := (h.2 1 (by decide) 2 (by decide)).mpr (by decide)
    omega
  · have hxy : x < y := (h.2 0 (by decide) 1 (by decide)).mpr (by decide)
    have hzx : z < x := (h.2 2 (by decide) 0 (by decide)).mpr (by decide)
    omega
  · have hyz : y < z := (h.2 1 (by decide) 2 (by decide)).mpr (by decide)
    omega

-- A decreasing cyclic stack is valid, and so is one with a new minimum above it.
private theorem cyclic_good {st : List ℕ} (hst : st.Pairwise (· > ·)) : ¬bad true st := by
  rw [bad_iff]
  rintro ⟨t, ht, hf⟩
  have hl : t.length = 3 := by
    simp only [forbidden, ite_true, rotations_123, List.mem_cons, List.not_mem_nil, or_false,
      exists_eq_or_imp, exists_eq_left] at hf
    rcases hf with hf | hf | hf <;> exact hf.1
  have hs := hst.sublist ht
  rcases t with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, es⟩⟩⟩⟩ <;> simp at hl
  have hba := List.rel_of_pairwise_cons hs (by simp : b ∈ [b, c])
  have hcb := List.rel_of_pairwise_cons hs.of_cons (by simp : c ∈ [c])
  exact not_forbidden_of_extreme hcb (.inr hba) hf

private theorem cyclic_push_min {x : ℕ} {st xs : List ℕ} (hst : st.Pairwise (· > ·))
    (hx : ∀ y ∈ st, x < y) : run true (x :: xs) st = run true xs (x :: st) := by
  apply run_push
  rw [bad_iff]
  rintro ⟨t, ht, hf⟩
  rcases List.sublist_cons_iff.mp ht with ht | ⟨u, rfl, hu⟩
  · exact cyclic_good hst ((bad_iff ..).mpr ⟨_, ht, hf⟩)
  · have hl : (x :: u).length = 3 := by
      simp only [forbidden, ite_true, rotations_123, List.mem_cons, List.not_mem_nil, or_false,
      exists_eq_or_imp, exists_eq_left] at hf
      rcases hf with hf | hf | hf <;> exact hf.1
    have hs := hst.sublist hu
    rcases u with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩ <;> simp at hl
    exact not_forbidden_of_extreme (List.rel_of_pairwise_cons hs (by simp : b ∈ [b]))
      (.inl (hx b (hu.subset (by simp)))) hf

private theorem west_good {st : List ℕ} (hst : st.Pairwise (· < ·)) : ¬bad false st := by
  induction st with
  | nil => exact fun h => bad_singleton false 0 (bad_mono (List.nil_sublist [0]) false h)
  | cons x st ih =>
    rw [west_bad_cons, not_or]
    exact ⟨fun ⟨y, hy, hyx⟩ => (List.rel_of_pairwise_cons hst hy).not_gt hyx, ih hst.of_cons⟩

-- If the whole resulting stack is ordered, processing the prefix only pushes entries.
private theorem push_prefix {d : Bool} {r : ℕ → ℕ → Prop}
    (good : ∀ {st : List ℕ}, st.Pairwise r → ¬bad d st) (s t st : List ℕ)
    (hs : (s.reverse ++ st).Pairwise r) : run d (s ++ t) st = run d t (s.reverse ++ st) := by
  induction s generalizing st with
  | nil => simp
  | cons x s ih =>
    simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] at hs ⊢
    have hp : (x :: st).Pairwise r := hs.sublist (List.sublist_append_right _ _)
    rw [run_push (good hp), ih _ hs]

private theorem cycle_even (k : ℕ) :
    run true (xiPermutation (2 * (k + 2))) [] =
      (stride 3 (k + 1)).reverse ++ (stride 2 (k + 2)).reverse ++ [1] := by
  rw [xi_even]
  have hfirst : run true (stride 1 (k + 2) ++ stride 2 (k + 2)) [] =
      run true (stride 2 (k + 2)) ((stride 1 (k + 2)).reverse ++ []) :=
    push_prefix cyclic_good _ _ [] (by
      simpa only [List.append_nil, List.pairwise_reverse] using List.pairwise_lt_range' 2)
  rw [hfirst, List.append_nil]
  have h1 : stride 1 (k + 2) = 1 :: stride 3 (k + 1) := rfl
  have h2 : stride 2 (k + 2) = 2 :: stride 4 (k + 1) := rfl
  rw [h1, h2, List.reverse_cons]
  have hpop : run true (2 :: stride 4 (k + 1)) ((stride 3 (k + 1)).reverse ++ [1]) =
      (stride 3 (k + 1)).reverse ++ run true (stride 4 (k + 1)) [2, 1] :=
    cyclic_push_succ 1 _ _ (by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp (List.mem_reverse.mp hy)
      omega)
  rw [hpop]
  have hlast : run true (stride 4 (k + 1)) [2, 1] =
      (stride 4 (k + 1)).reverse ++ [2, 1] := by
    have h := push_prefix cyclic_good (stride 4 (k + 1)) [] [2, 1] (by
      simp only [List.pairwise_append, List.pairwise_reverse, List.mem_reverse]
      refine ⟨List.pairwise_lt_range' 2, by decide, ?_⟩
      intro y hy z hz
      obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hy
      simp at hz
      omega)
    simpa only [List.append_nil, restrictedStackSortAux] using h
  rw [hlast]
  simp [List.reverse_cons, List.append_assoc]

-- For odd length, `1` goes on top of the even block before `3` forces the pops.
private theorem cycle_odd (k : ℕ) :
    run true (xiPermutation (2 * (k + 2) + 1)) [] =
      1 :: ((stride 4 (k + 1)).reverse ++ ((stride 3 (k + 2)).reverse ++ [2])) := by
  rw [xi_odd]
  have hfirst : run true (stride 2 (k + 2) ++ stride 1 (k + 3)) [] =
      run true (stride 1 (k + 3)) ((stride 2 (k + 2)).reverse ++ []) :=
    push_prefix cyclic_good _ _ [] (by
      simpa only [List.append_nil, List.pairwise_reverse] using List.pairwise_lt_range' 2)
  rw [hfirst, List.append_nil]
  change run true (1 :: 3 :: stride 5 (k + 1)) (stride 2 (k + 2)).reverse = _
  have hmin : run true (1 :: 3 :: stride 5 (k + 1)) (stride 2 (k + 2)).reverse =
      run true (3 :: stride 5 (k + 1)) (1 :: (stride 2 (k + 2)).reverse) :=
    cyclic_push_min (by simpa only [List.pairwise_reverse] using List.pairwise_lt_range' 2) (by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp (List.mem_reverse.mp hy)
      omega)
  rw [hmin]
  have h2 : stride 2 (k + 2) = 2 :: stride 4 (k + 1) := rfl
  rw [h2, List.reverse_cons, ← List.cons_append]
  have hpop : run true (3 :: stride 5 (k + 1)) ((1 :: (stride 4 (k + 1)).reverse) ++ [2]) =
      (1 :: (stride 4 (k + 1)).reverse) ++ run true (stride 5 (k + 1)) [3, 2] :=
    cyclic_push_succ 2 _ _ (by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · decide
      · obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp (List.mem_reverse.mp hy)
        omega)
  rw [hpop]
  have hlast : run true (stride 5 (k + 1)) [3, 2] =
      (stride 5 (k + 1)).reverse ++ [3, 2] := by
    have h := push_prefix cyclic_good (stride 5 (k + 1)) [] [3, 2] (by
      simp only [List.pairwise_append, List.pairwise_reverse, List.mem_reverse]
      refine ⟨List.pairwise_lt_range' 2, by decide, ?_⟩
      intro y hy z hz
      obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hy
      simp at hz
      omega)
    simpa only [List.append_nil, restrictedStackSortAux] using h
  rw [hlast]
  have h3 : stride 3 (k + 2) = 3 :: stride 5 (k + 1) := rfl
  simp [h3, List.reverse_cons, List.append_assoc]

-- The maximum at the start of the second block releases the first block in increasing order.
private theorem west_blocks {a b : List ℕ} {m : ℕ} (ha : a.Pairwise (· < ·))
    (hb : (b ++ [m]).Pairwise (· < ·)) (hm : ∀ x ∈ a, x < m) :
    run false (a.reverse ++ (b ++ [m]).reverse) [] = a ++ b ++ [m] := by
  rw [push_prefix west_good _ _ [] (by simpa using ha), List.reverse_reverse, List.append_nil]
  rw [List.reverse_append]
  change run false (m :: b.reverse) a = _
  have hpop : run false (m :: b.reverse) a = a ++ run false b.reverse [m] :=
    runW_pop_all _ hm
  have hpush := push_prefix west_good b.reverse [] [m]
    (by simpa only [List.reverse_reverse] using hb)
  rw [hpop]
  simpa only [List.append_nil, List.reverse_reverse, restrictedStackSortAux, List.append_assoc]
    using congrArg (a ++ ·) hpush

private theorem expand_stride_above {a b : ℕ} (h : a < b) (m : ℕ) :
    expand a false (stride b m) = stride (b + 1) m := by
  calc
    expand a false (stride b m) = (stride b m).map (· + 1) := by
      rw [expand, List.map_eq_flatMap]
      apply List.flatMap_congr
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hx
      have hp : a < b + 2 * i := by omega
      simp [block, liftEntry, hp.ne', hp.not_gt]
    _ = _ := List.range'_succ_left.symm

private theorem machine_xi_even (k : ℕ) :
    machine (xiPermutation (2 * (k + 2))) = expand 1 false (xiPermutation (2 * (k + 1) + 1)) := by
  change run false (run true _ []) [] = _
  rw [cycle_even]
  have hb : (1 :: stride 2 (k + 2)).Pairwise (· < ·) := by
    refine List.pairwise_cons.mpr ⟨?_, List.pairwise_lt_range' 2⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hx
    omega
  have hs : stride 2 (k + 2) = stride 2 (k + 1) ++ [2 + 2 * (k + 1)] := List.range'_concat
  have hw := west_blocks (b := 1 :: stride 2 (k + 1)) (m := 2 + 2 * (k + 1))
    (List.pairwise_lt_range' (s := 3) (n := k + 1) 2) (by simpa only [List.cons_append, ← hs]
      using hb) (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hx
      omega)
  simp only [List.append_assoc, List.cons_append, ← hs, List.reverse_cons] at hw
  rw [List.append_assoc, hw, xi_odd]
  change _ = (stride 2 (k + 1) ++ 1 :: stride 3 (k + 1)).flatMap (block 1 false)
  rw [List.flatMap_append, List.flatMap_cons]
  change _ = expand 1 false (stride 2 (k + 1)) ++
    (block 1 false 1 ++ expand 1 false (stride 3 (k + 1)))
  rw [expand_stride_above (by decide : 1 < 2), expand_stride_above (by decide : 1 < 3)]
  rfl

private theorem machine_xi_odd (k : ℕ) :
    machine (xiPermutation (2 * (k + 2) + 1)) = expand 2 false (xiPermutation (2 * (k + 2))) := by
  change run false (run true _ []) [] = _
  rw [cycle_odd]
  have hb : (2 :: stride 3 (k + 2)).Pairwise (· < ·) := by
    refine List.pairwise_cons.mpr ⟨?_, List.pairwise_lt_range' 2⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hx
    omega
  have hs : stride 3 (k + 2) = stride 3 (k + 1) ++ [3 + 2 * (k + 1)] := List.range'_concat
  have hw := west_blocks (b := 2 :: stride 3 (k + 1)) (m := 3 + 2 * (k + 1))
    (List.pairwise_lt_range' (s := 4) (n := k + 1) 2) (by simpa only [List.cons_append, ← hs]
      using hb) (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hx
      omega)
  simp only [List.append_assoc, List.cons_append, ← hs, List.reverse_cons] at hw
  have hfirst : (stride 4 (k + 1)).reverse = (4 + 2 * k) :: (stride 4 k).reverse := by
    rw [show stride 4 (k + 1) = stride 4 k ++ [4 + 2 * k] from List.range'_concat,
      List.reverse_append]
    rfl
  rw [run_push (bad_singleton false 1), hfirst, List.cons_append]
  let rest := (stride 4 k).reverse ++ ((stride 3 (k + 2)).reverse ++ [2])
  have hpop : run false ((4 + 2 * k) :: rest) [1] =
      [1] ++ run false rest [4 + 2 * k] := runW_pop_all _ (by simp; omega)
  rw [hpop]
  change 1 :: run false rest [4 + 2 * k] = _
  rw [← run_push (bad_singleton false (4 + 2 * k))]
  dsimp only [rest]
  rw [← List.cons_append, ← hfirst, hw, xi_even]
  change _ = ((1 :: stride 3 (k + 1)) ++ 2 :: stride 4 (k + 1)).flatMap (block 2 false)
  rw [List.flatMap_append, List.flatMap_cons, List.flatMap_cons]
  change _ = (block 2 false 1 ++ expand 2 false (stride 3 (k + 1))) ++
    (block 2 false 2 ++ expand 2 false (stride 4 (k + 1)))
  rw [expand_stride_above (by decide : 2 < 3), expand_stride_above (by decide : 2 < 4)]
  rfl

private theorem machine_xi_expand {n : ℕ} (hn : 4 ≤ n) :
    ∃ a, 1 ≤ a ∧ a < n ∧ machine (xiPermutation n) = expand a false (xiPermutation (n - 1)) := by
  let k := n / 2 - 2
  rcases (show n = 2 * (k + 2) ∨ n = 2 * (k + 2) + 1 by dsimp [k]; omega) with he | ho
  · refine ⟨1, by omega, by omega, ?_⟩
    rw [he, show 2 * (k + 2) - 1 = 2 * (k + 1) + 1 by omega, machine_xi_even]
  · refine ⟨2, by omega, by omega, ?_⟩
    rw [ho, show 2 * (k + 2) + 1 - 1 = 2 * (k + 2) by omega, machine_xi_odd]

private theorem xi_not_sorted {n : ℕ} (hn : 3 ≤ n) :
    machine^[n - 3] (xiPermutation n) ≠ List.range' 1 n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : n = 2
    · subst n
      decide
    · have hn' : 3 ≤ n := by omega
      obtain ⟨a, ha, han, he⟩ := machine_xi_expand (by omega : 4 ≤ n + 1)
      simp only [Nat.add_sub_cancel] at he
      have hnodup := (xi_perm n).nodup_iff.mpr (List.nodup_range' 1)
      rw [show n + 1 - 3 = (n - 3) + 1 by omega, Function.iterate_succ_apply, he,
        iterate_expand _ _ _ hnodup, ← expand_range (b := 1) ha (by omega)]
      exact fun hsort => ih hn' ((Function.LeftInverse.injective (contract_expand a)) hsort)

end CyclicSortingMachine123Iterates

open CyclicSortingMachine123Iterates in
/-- **$n - 2$ passes of $SC_{[123]}$ sort every permutation, and $n - 3$ do not.** Let $n \ge 3$
and let $SC_{[123]}^k$ be the $k$-fold iterate of the cyclic avoidance machine $SC_{[123]}$.
For every permutation $\pi$ of $[n] = \{1, \dots, n\}$, $SC_{[123]}^{n-2}(\pi) = 12 \cdots n$, and
the bound is tight: $SC_{[123]}^{n-3}(\xi_n) \ne 12 \cdots n$, where $\xi_n$ lists the elements of
$[n]$ of parity different from $n$ in increasing order, followed by those of the parity of $n$
in increasing order.

Source: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026),
Article A15, Theorem 1 (`integers-2026-A15-thm-1`). -/
public theorem cyclicSortingMachine_123_iterate_sorts {n : ℕ} (hn : 3 ≤ n) :
    (∀ π : List ℕ, π.Perm (List.range' 1 n) →
      (cyclicSortingMachine [1, 2, 3])^[n - 2] π = List.range' 1 n) ∧
    (cyclicSortingMachine [1, 2, 3])^[n - 3] (xiPermutation n) ≠ List.range' 1 n := by
  exact ⟨fun _ hπ => sorts_at_least (by omega) hπ, xi_not_sorted hn⟩

end MetaMathlibExt
