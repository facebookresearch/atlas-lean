/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Dedup
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Int

/-!
# Valid orderings of finite sets of nonzero integers

An ordering `a₁, …, aₘ` of a finite set is *valid* if its partial sums
`a₁, a₁ + a₂, …, a₁ + ⋯ + aₘ` are pairwise distinct; the empty partial sum `0` is not counted.
The main result, `exists_distinct_partial_sums_ordering`, says that every finite set of nonzero
integers has a valid ordering.

The proof is that of Theorem 1.3 in Noah Kravitz, "Rearranging Small Sets for Distinct Partial
Sums", arXiv:2407.01835 (published in INTEGERS 24 (2024), Article A113). Write the set as
`P ∪ (-N)` with `P` and `N` sets of positive integers. By induction on `|P| + |N|`, there are
orderings `p₁, …, p_{|P|}` of `P` and `n₁, …, n_{|N|}` of `N` such that
`p₁ + ⋯ + pᵢ ≠ n₁ + ⋯ + nⱼ` unless `(i, j)` is `(0, 0)` or `(|P|, |N|)`. By symmetry, let the
sum of `P` be at least that of `N`. If `N` is empty, any ordering of `P` works. Otherwise remove
an element `p*` of `P` whose removal leaves a sum different from that of `N`, order the rest by
induction and put `p*` last. The ordering `p_{|P|}, …, p₁, -n₁, …, -n_{|N|}` is then valid.
-/

namespace MathlibExt.Combinatorics.ValidOrderingWanted

open List

/-- Kravitz's condition on an ordering `lp` of the positive elements and an ordering `ln` of the
absolute values of the negative elements: a prefix sum of `lp` equals a prefix sum of `ln` only
for the two empty prefixes and for the two whole lists. -/
private def PrefixSumsSeparated (lp ln : List ℤ) : Prop :=
  ∀ u, u <+: lp → ∀ v, v <+: ln → u.sum = v.sum → (u = [] ∧ v = []) ∨ (u = lp ∧ v = ln)

private theorem prefixSumsSeparated_symm {lp ln : List ℤ} (h : PrefixSumsSeparated lp ln) :
    PrefixSumsSeparated ln lp := by
  intro u hu v hv huv
  rcases h v hv u hu huv.symm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h2, h1⟩
  · exact Or.inr ⟨h2, h1⟩

/-- A proper prefix of a list of positive integers has a smaller sum. -/
private theorem sum_lt_of_prefix {l u : List ℤ} (hl : ∀ x ∈ l, 0 < x) (hu : u <+: l)
    (hne : u ≠ l) : u.sum < l.sum := by
  obtain ⟨t, rfl⟩ := hu
  have ht : t ≠ [] := by
    rintro rfl
    simp at hne
  have := List.sum_pos t (fun x hx => hl x (mem_append_right u hx)) ht
  rw [sum_append]
  omega

/-- Prefixes of a list of positive integers with the same sum are equal. -/
private theorem prefix_eq_of_sum_eq {l u w : List ℤ} (hl : ∀ x ∈ l, 0 < x) (hu : u <+: l)
    (hw : w <+: l) (huw : u.sum = w.sum) : u = w := by
  rcases prefix_or_prefix_of_prefix hu hw with h | h
  · by_contra hne
    have := sum_lt_of_prefix (fun x hx => hl x (hw.subset hx)) h hne
    omega
  · by_contra hne
    have := sum_lt_of_prefix (fun x hx => hl x (hu.subset hx)) h (Ne.symm hne)
    omega

/-- With no negative elements, any ordering of the positive elements will do. -/
private theorem prefixSumsSeparated_nil_right {lp : List ℤ} (hp : ∀ x ∈ lp, 0 < x) :
    PrefixSumsSeparated lp [] := by
  intro u hu v hv huv
  rw [prefix_nil] at hv
  subst hv
  refine Or.inl ⟨?_, rfl⟩
  by_contra hne
  have := List.sum_pos u (fun x hx => hp x (hu.subset hx)) hne
  simp only [sum_nil] at huv
  omega

/-- In a nonempty list of distinct integers, some element can be removed so that the sum of the
remaining elements avoids a given nonzero value. -/
private theorem exists_sum_erase_ne {s : ℤ} (hs : s ≠ 0) :
    ∀ {l : List ℤ}, l.Nodup → l ≠ [] → ∃ a ∈ l, (l.erase a).sum ≠ s
  | [], _, h => absurd rfl h
  | [b], _, _ => ⟨b, by simp, by simpa using hs.symm⟩
  | b :: c :: l, hnd, _ => by
    have hbc : b ≠ c := by
      rintro rfl
      simp at hnd
    by_contra! H
    have e1 := List.sum_erase (l := b :: c :: l) (a := b) (by simp)
    have e2 := List.sum_erase (l := b :: c :: l) (a := c) (by simp)
    have h1 := H b (by simp)
    have h2 := H c (by simp)
    omega

/-- The inductive step of Kravitz's proof, when the sum of `lp` is at least that of `ln`: put last
an element of `lp` whose removal leaves a sum different from that of `ln`. -/
private theorem exists_prefixSumsSeparated_step (lp ln : List ℤ) (hp : ∀ x ∈ lp, 0 < x)
    (hn : ∀ x ∈ ln, 0 < x) (hnd : lp.Nodup) (hsum : ln.sum ≤ lp.sum)
    (ih : ∀ a ∈ lp, ∃ lp' ln', lp' ~ lp.erase a ∧ ln' ~ ln ∧ PrefixSumsSeparated lp' ln') :
    ∃ lp' ln', lp' ~ lp ∧ ln' ~ ln ∧ PrefixSumsSeparated lp' ln' := by
  rcases eq_or_ne ln [] with rfl | hln
  · exact ⟨lp, [], Perm.refl _, Perm.refl _, prefixSumsSeparated_nil_right hp⟩
  have hlnpos : 0 < ln.sum := List.sum_pos ln hn hln
  have hlp : lp ≠ [] := by
    rintro rfl
    simp only [sum_nil] at hsum
    omega
  obtain ⟨a, ha, hne⟩ := exists_sum_erase_ne hlnpos.ne' hnd hlp
  obtain ⟨lp', ln', hlp', hln', hg⟩ := ih a ha
  refine ⟨lp' ++ [a], ln', ?_, hln', ?_⟩
  · exact (perm_append_singleton a lp').trans ((hlp'.cons a).trans (perm_cons_erase ha).symm)
  have hsa : (lp' ++ [a]).sum = lp.sum := by
    rw [sum_append, hlp'.sum_eq, ← List.sum_erase ha]
    simp only [sum_cons, sum_nil]
    omega
  have hn' : ∀ x ∈ ln', 0 < x := fun x hx => hn x (hln'.subset hx)
  intro u hu v hv huv
  rcases prefix_concat_iff.mp hu with rfl | hu
  · refine Or.inr ⟨rfl, ?_⟩
    by_contra hvne
    have := sum_lt_of_prefix hn' hv hvne
    rw [hln'.sum_eq] at this
    omega
  · rcases hg u hu v hv huv with h | ⟨rfl, rfl⟩
    · exact Or.inl h
    · exact absurd (hlp'.sum_eq.symm.trans (huv.trans hln'.sum_eq)) hne

/-- Kravitz's induction: two lists of distinct positive integers can be reordered so that their
prefix sums agree only for the two empty prefixes and for the two whole lists. -/
private theorem exists_prefixSumsSeparated (n : ℕ) : ∀ (lp ln : List ℤ), lp.length + ln.length ≤ n →
    lp.Nodup → ln.Nodup → (∀ x ∈ lp, 0 < x) → (∀ x ∈ ln, 0 < x) →
    ∃ lp' ln', lp' ~ lp ∧ ln' ~ ln ∧ PrefixSumsSeparated lp' ln' := by
  induction n with
  | zero =>
    intro lp ln hlen _ _ hp _
    obtain rfl : lp = [] := List.eq_nil_of_length_eq_zero (by omega)
    obtain rfl : ln = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact ⟨[], [], Perm.refl _, Perm.refl _, prefixSumsSeparated_nil_right hp⟩
  | succ n ih =>
    intro lp ln hlen hndp hndn hp hn
    rcases le_total ln.sum lp.sum with h | h
    · refine exists_prefixSumsSeparated_step lp ln hp hn hndp h fun a ha => ?_
      have h1 := List.length_erase_of_mem ha
      have h2 := List.length_pos_of_mem ha
      exact ih (lp.erase a) ln (by omega) (hndp.erase a) hndn
        (fun x hx => hp x (List.mem_of_mem_erase hx)) hn
    · obtain ⟨ln', lp', h1, h2, h3⟩ :=
        exists_prefixSumsSeparated_step ln lp hn hp hndn h fun a ha => by
          have h1 := List.length_erase_of_mem ha
          have h2 := List.length_pos_of_mem ha
          obtain ⟨lp', ln', h1, h2, h3⟩ := ih lp (ln.erase a) (by omega) hndp (hndn.erase a) hp
            (fun x hx => hn x (List.mem_of_mem_erase hx))
          exact ⟨ln', lp', h2, h1, prefixSumsSeparated_symm h3⟩
      exact ⟨lp', ln', h2, h1, prefixSumsSeparated_symm h3⟩

private theorem scanl_eq_cons_tail (l : List ℤ) (c : ℤ) :
    l.scanl (· + ·) c = c :: (l.scanl (· + ·) c).tail := by
  cases l <;> simp

private theorem foldl_add_eq (l : List ℤ) (a : ℤ) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    simp only [foldl_cons, sum_cons, ih]
    omega

/-- Every element of the tail of `l.scanl (· + ·) a` is `a` plus the sum of a nonempty prefix
of `l`. -/
private theorem exists_prefix_of_mem_tail_scanl :
    ∀ {l : List ℤ} {a x : ℤ}, x ∈ (l.scanl (· + ·) a).tail →
      ∃ u, u <+: l ∧ u ≠ [] ∧ x = a + u.sum
  | [], a, x, h => by simp at h
  | b :: l, a, x, h => by
    simp only [scanl_cons, tail_cons] at h
    rw [scanl_eq_cons_tail, mem_cons] at h
    rcases h with rfl | h
    · exact ⟨[b], by simp, by simp, by simp⟩
    · obtain ⟨u, hu, hne, rfl⟩ := exists_prefix_of_mem_tail_scanl h
      refine ⟨b :: u, by simpa using hu, by simp, ?_⟩
      simp only [sum_cons]
      omega

/-- If no two distinct nonempty prefixes of `l` have the same sum, then the partial sums of `l`
are pairwise distinct. -/
private theorem nodup_tail_scanl :
    ∀ {l : List ℤ} (a : ℤ),
      (∀ u w, u <+: l → w <+: l → u ≠ [] → w ≠ [] → u.sum = w.sum → u = w) →
      (l.scanl (· + ·) a).tail.Nodup
  | [], a, _ => by simp
  | b :: l, a, h => by
    simp only [scanl_cons, tail_cons]
    rw [scanl_eq_cons_tail, nodup_cons]
    refine ⟨fun hmem => ?_, nodup_tail_scanl (a + b) fun u w hu hw _ _ huw => ?_⟩
    · obtain ⟨u, hu, hne, hu0⟩ := exists_prefix_of_mem_tail_scanl hmem
      have := h [b] (b :: u) (by simp) (by simpa using hu) (by simp) (by simp)
        (by simp only [sum_cons, sum_nil]; omega)
      simp only [cons.injEq, true_and] at this
      exact hne this.symm
    · have := h (b :: u) (b :: w) (by simpa using hu) (by simpa using hw) (by simp) (by simp)
        (by simp [huw])
      simpa using this

/-- Kravitz's ordering, the positive elements in reverse order followed by the negative elements,
has pairwise distinct partial sums. -/
private theorem nodup_tail_scanl_of_separated {lp ln : List ℤ} (hp : ∀ x ∈ lp, 0 < x)
    (hn : ∀ x ∈ ln, 0 < x) (hg : PrefixSumsSeparated lp ln) :
    ((lp.reverse ++ ln.map (- ·)).scanl (· + ·) 0).tail.Nodup := by
  rw [scanl_append, tail_append_of_ne_nil scanl_ne_nil, nodup_append, foldl_add_eq]
  refine ⟨nodup_tail_scanl 0 fun u w hu hw _ _ huw =>
      prefix_eq_of_sum_eq (fun x hx => hp x (mem_reverse.mp hx)) hu hw huw,
    nodup_tail_scanl _ fun u w hu hw _ _ huw => ?_, ?_⟩
  · obtain ⟨u', hu', rfl⟩ := prefix_map_iff.mp hu
    obtain ⟨w', hw', rfl⟩ := prefix_map_iff.mp hw
    rw [prefix_eq_of_sum_eq hn hu' hw' (by simpa [← sum_neg] using huw)]
  · intro x hx y hy hxy
    subst hxy
    obtain ⟨u, hu, hu0, hxu⟩ := exists_prefix_of_mem_tail_scanl hx
    obtain ⟨w, hw, hw0, hxw⟩ := exists_prefix_of_mem_tail_scanl hy
    obtain ⟨w', hw', rfl⟩ := prefix_map_iff.mp hw
    obtain ⟨r, hr⟩ := hu
    have hlp : lp = r.reverse ++ u.reverse := by
      rw [← reverse_append, hr, reverse_reverse]
    have hsum : r.reverse.sum = w'.sum := by
      have h1 : lp.sum = r.sum + u.sum := by
        rw [hlp, sum_append, sum_reverse, sum_reverse]
      have h2 := sum_neg w'
      rw [sum_reverse] at hxw ⊢
      omega
    rcases hg r.reverse ⟨u.reverse, hlp.symm⟩ w' hw' hsum with ⟨_, rfl⟩ | ⟨h1, _⟩
    · exact hw0 rfl
    · have := congrArg length h1
      have := congrArg length hr
      simp only [length_reverse, length_append] at *
      exact hu0 (List.eq_nil_of_length_eq_zero (by omega))

/-- **Valid orderings of finite sets of nonzero integers.** Every finite set $A$ of nonzero
integers has a valid ordering: its elements can be listed as $a_1, \dots, a_m$, each exactly
once, so that the partial sums $a_1, a_1 + a_2, \dots, a_1 + \cdots + a_m$ are pairwise
distinct. The empty sum $0$ is not counted among the partial sums.

Source: Noah Kravitz, "Rearranging Small Sets for
Distinct Partial Sums", Theorem 2. -/
public theorem exists_distinct_partial_sums_ordering
    (A : Finset ℤ) (h0 : 0 ∉ A) :
    ∃ l : List ℤ, List.Perm l A.toList ∧
      ((l.scanl (· + ·) 0).tail).Nodup := by
  set l0 := A.toList
  have hnd : l0.Nodup := A.nodup_toList
  have hl0 : (0 : ℤ) ∉ l0 := by simpa [l0] using h0
  obtain ⟨lp, ln, hp, hn, hg⟩ := exists_prefixSumsSeparated _ (l0.filter (0 < ·))
    ((l0.filter (· < 0)).map (- ·)) le_rfl (hnd.filter _)
    ((hnd.filter _).map neg_injective)
    (fun x hx => by simpa using (mem_filter.mp hx).2)
    (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
      simpa using (mem_filter.mp hy).2)
  refine ⟨lp.reverse ++ ln.map (- ·), ?_, ?_⟩
  · have h1 : lp.reverse ~ l0.filter (0 < ·) := (reverse_perm lp).trans hp
    have h2 : ln.map (- ·) ~ l0.filter (· < 0) := by
      simpa [map_map, Function.comp_def] using hn.map (- ·)
    have h3 : l0.filter (· < 0) = l0.filter (fun x => !decide (0 < x)) := by
      apply filter_congr
      intro x hx
      have : x ≠ 0 := fun h => hl0 (h ▸ hx)
      by_cases hx' : 0 < x <;> simp [hx'] <;> omega
    exact (h1.append h2).trans (h3 ▸ filter_append_perm _ l0)
  · exact nodup_tail_scanl_of_separated
      (fun x hx => (mem_filter.mp (hp.subset hx)).2 |> of_decide_eq_true)
      (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := mem_map.mp (hn.subset hx)
        simpa using of_decide_eq_true (mem_filter.mp hy).2) hg

end MathlibExt.Combinatorics.ValidOrderingWanted
