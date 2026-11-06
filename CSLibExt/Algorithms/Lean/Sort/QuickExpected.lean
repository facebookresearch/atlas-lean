/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Sort.Quick
public import CSLibExt.Algorithms.Lean.Random.ExpectedCost
public import MathlibExt.Probability.ProbabilityMassFunction.Expectation

/-!
# Expected comparison count of deterministic quicksort

The expected number of comparisons made by the deterministic head-pivot
`quickSort` on a uniformly random permutation of a duplicate-free input
(Cormen, Leiserson, Rivest, and Stein, *Introduction to Algorithms*, 4th
ed., Section 7.4). The proof is the indicator analysis of CLRS: the
comparison count on any ordering is the sum, over unordered pairs
`a < b` of values, of the indicator that `a` and `b` are ever compared.
Two values are compared exactly when the first element of the ordering
(in list order) whose value lies in the closed interval `[a, b]` is `a`
or `b` itself; for a random ordering this happens for exactly
`2 / (d + 2)` of all permutations, where `d` is the number of input
values strictly between `a` and `b`, because each of the `d + 2`
interval values is equally likely to appear first.

"First element in the interval" is represented by
`List.find? (fun x => decide (a ≤ x ∧ x ≤ b))`, which makes the
functionality (uniqueness) of the first element automatic and interacts
well with both the stable filter form of `partition3` and with swapping
two values in a permuted list (the counting bijection).
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

open scoped ENNReal

universe u

variable {α : Type u} [LinearOrder α]

/-- **Number of list entries strictly between two values.** For a list $\ell$ over a linear order
and elements $a$ and $b$, this is the number of entries $x$ of $\ell$, counted with multiplicity,
such that $a < x < b$. -/
public def betweenCount (xs : List α) (a b : α) : ℕ :=
  (xs.filter (fun x => a < x ∧ x < b)).length

/-- The Boolean predicate of lying in the closed interval `[a, b]`. -/
private abbrev inAB (a b : α) : α → Bool :=
  fun x => decide (a ≤ x ∧ x ≤ b)

private theorem inAB_iff {a b x : α} : inAB a b x ↔ a ≤ x ∧ x ≤ b := by
  simp [inAB]

/-- The first entry of `ys` in `[a, b]` (list order) is `a` or `b`. -/
private abbrev comparedProp (ys : List α) (a b : α) : Prop :=
  ys.find? (inAB a b) = some a ∨ ys.find? (inAB a b) = some b

/-- The comparison indicator of the pair `(a, b)` on the ordering `ys`. -/
private def cmpInd (ys : List α) (a b : α) : ℕ :=
  if comparedProp ys a b then 1 else 0

/-- The unordered pairs `a < b` of values occurring in `ys`. -/
private def pairSet (ys : List α) : Finset (α × α) :=
  (ys.toFinset ×ˢ ys.toFinset).filter (fun p => p.1 < p.2)

private theorem mem_pairSet {ys : List α} {p : α × α} :
    p ∈ pairSet ys ↔ p.1 ∈ ys ∧ p.2 ∈ ys ∧ p.1 < p.2 := by
  simp [pairSet, List.mem_toFinset, and_assoc]

/-- The total indicator count over all unordered pairs of `ys`. -/
private def pairSum (ys : List α) : ℕ :=
  ∑ p ∈ pairSet ys, cmpInd ys p.1 p.2

/-- Filtering out only entries rejected by `p` does not change the
first entry satisfying `p`. -/
private theorem find?_filter_eq {β : Type*} {p q : β → Bool}
    (h : ∀ x, p x → q x) (l : List β) :
    (l.filter q).find? p = l.find? p := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      by_cases hq : q x
      · by_cases hp : p x <;> simp [hq, hp, ih]
      · have hp : ¬ p x := fun hp => hq (h x hp)
        simp [hq, hp, ih]

/-- Mapping by a function preserving `p` maps the first entry
satisfying `p` accordingly. -/
private theorem find?_map_eq {β : Type*} {p : β → Bool} {f : β → β}
    (h : ∀ x, p (f x) = p x) (l : List β) :
    (l.map f).find? p = (l.find? p).map f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      by_cases hp : p x
      · have hfp : p (f x) := by rw [h x]; exact hp
        simp [hp, hfp]
      · have hfp : ¬ p (f x) := by rw [h x]; exact hp
        simp [hp, hfp, ih]

private theorem find?_cons_pivot {pivot a b : α} {tail : List α}
    (h : a ≤ pivot ∧ pivot ≤ b) :
    (pivot :: tail).find? (inAB a b) = some pivot := by
  apply List.find?_cons_of_pos
  exact inAB_iff.mpr h

private theorem find?_cons_pivot_not {pivot a b : α} {tail : List α}
    (h : ¬ (a ≤ pivot ∧ pivot ≤ b)) :
    (pivot :: tail).find? (inAB a b) = tail.find? (inAB a b) := by
  apply List.find?_cons_of_neg
  exact fun hh => h (inAB_iff.mp hh)

/-- On `pivot :: tail`, a pair whose interval contains `pivot` is
compared exactly when `pivot` is one of its endpoints. -/
private theorem cmpInd_cons_pivot {pivot a b : α} {tail : List α}
    (h : a ≤ pivot ∧ pivot ≤ b) :
    cmpInd (pivot :: tail) a b = if pivot = a ∨ pivot = b then 1 else 0 := by
  unfold cmpInd comparedProp
  rw [find?_cons_pivot h]
  by_cases hp : pivot = a ∨ pivot = b
  · rcases hp with rfl | rfl <;> simp
  · simp [hp]

/-- For a pair entirely below the pivot, the indicator on
`pivot :: tail` agrees with the indicator on the below-filter. -/
private theorem cmpInd_cons_below {pivot a b : α} {tail : List α}
    (hb : b < pivot) :
    cmpInd (pivot :: tail) a b =
      cmpInd (tail.filter (fun x => x < pivot)) a b := by
  unfold cmpInd comparedProp
  have hfind : (tail.filter (fun x => x < pivot)).find? (inAB a b) =
      tail.find? (inAB a b) := by
    apply find?_filter_eq
    intro x hx
    have hxx : a ≤ x ∧ x ≤ b := inAB_iff.mp hx
    have hxp : x < pivot := hxx.2.trans_lt hb
    simp [hxp]
  rw [find?_cons_pivot_not (fun h => not_le_of_gt hb h.2), hfind]

/-- For a pair entirely above the pivot, the indicator on
`pivot :: tail` agrees with the indicator on the above-filter. -/
private theorem cmpInd_cons_above {pivot a b : α} {tail : List α}
    (ha : pivot < a) :
    cmpInd (pivot :: tail) a b =
      cmpInd (tail.filter (fun x => pivot < x)) a b := by
  unfold cmpInd comparedProp
  have hfind : (tail.filter (fun x => pivot < x)).find? (inAB a b) =
      tail.find? (inAB a b) := by
    apply find?_filter_eq
    intro x hx
    have hxx : a ≤ x ∧ x ≤ b := inAB_iff.mp hx
    have hxp : pivot < x := ha.trans_le hxx.1
    simp [hxp]
  rw [find?_cons_pivot_not (fun h => not_le_of_gt ha h.1), hfind]

/-- Classification of a pair by the position of the pivot relative to
it: `0` below-below, `1` above-above, `2` below-pivot, `3`
pivot-above, `4` below-above (cross). -/
private def pairTag (pivot : α) (p : α × α) : ℕ :=
  if p.2 < pivot then 0
  else if pivot < p.1 then 1
  else if p.2 = pivot then 2
  else if p.1 = pivot then 3
  else 4

private theorem pairTag_lt (pivot : α) (p : α × α) : pairTag pivot p < 5 := by
  unfold pairTag
  split_ifs <;> omega

private theorem pairTag_eq_zero {pivot : α} {p : α × α} :
    pairTag pivot p = 0 ↔ p.2 < pivot := by
  unfold pairTag
  split_ifs <;> simp_all

private theorem pairTag_eq_one {pivot : α} {p : α × α} (hlt : p.1 < p.2) :
    pairTag pivot p = 1 ↔ pivot < p.1 := by
  have hnot : pivot < p.1 → ¬ p.2 < pivot :=
    fun h hh => lt_asymm hh (h.trans hlt)
  unfold pairTag
  split_ifs <;> simp_all

private theorem pairTag_eq_two {pivot : α} {p : α × α} (hlt : p.1 < p.2) :
    pairTag pivot p = 2 ↔ p.2 = pivot := by
  constructor
  · intro h
    unfold pairTag at h
    split_ifs at h <;> simp_all
  · intro h
    have h2 : ¬ pivot < p.1 := by
      rw [← h]; exact fun hh => lt_asymm hh hlt
    simp [pairTag, h2, h]

private theorem pairTag_eq_three {pivot : α} {p : α × α} (hlt : p.1 < p.2) :
    pairTag pivot p = 3 ↔ p.1 = pivot := by
  constructor
  · intro h
    unfold pairTag at h
    split_ifs at h <;> simp_all
  · intro h
    have h1 : ¬ p.2 < pivot := by
      rw [← h]; exact fun hh => lt_asymm hh hlt
    have h3 : ¬ p.2 = pivot := by rw [← h]; exact ne_of_gt hlt
    simp [pairTag, h1, h3, h]

private theorem pairTag_eq_four {pivot : α} {p : α × α} (hlt : p.1 < p.2) :
    pairTag pivot p = 4 ↔ p.1 < pivot ∧ pivot < p.2 := by
  constructor
  · intro h
    have h1 : ¬ p.2 < pivot := by
      rw [← pairTag_eq_zero]; omega
    have h2 : ¬ pivot < p.1 := by
      rw [← pairTag_eq_one hlt]; omega
    have h3 : ¬ p.2 = pivot := by
      rw [← pairTag_eq_two hlt]; omega
    have h4 : ¬ p.1 = pivot := by
      rw [← pairTag_eq_three hlt]; omega
    exact ⟨lt_of_le_of_ne (le_of_not_gt h2) h4,
      lt_of_le_of_ne (le_of_not_gt h1) (fun hh => h3 hh.symm)⟩
  · rintro ⟨hlo, hhi⟩
    have h0 : pairTag pivot p ≠ 0 :=
      fun hh => not_lt_of_gt hhi (pairTag_eq_zero.mp hh)
    have h1 : pairTag pivot p ≠ 1 :=
      fun hh => not_lt_of_gt hlo ((pairTag_eq_one hlt).mp hh)
    have h2 : pairTag pivot p ≠ 2 :=
      fun hh => ne_of_gt hhi ((pairTag_eq_two hlt).mp hh)
    have h3 : pairTag pivot p ≠ 3 :=
      fun hh => ne_of_lt hlo ((pairTag_eq_three hlt).mp hh)
    have h5 := pairTag_lt pivot p
    omega

private theorem mem_belowFilter {pivot x : α} {tail : List α} :
    x ∈ tail.filter (fun x => x < pivot) ↔ x ∈ tail ∧ x < pivot := by
  simp [List.mem_filter]

private theorem mem_aboveFilter {pivot x : α} {tail : List α} :
    x ∈ tail.filter (fun x => pivot < x) ↔ x ∈ tail ∧ pivot < x := by
  simp [List.mem_filter]

omit [LinearOrder α] in
private theorem mem_tail_of_mem_cons_ne {pivot x : α} {tail : List α}
    (hx : x ∈ pivot :: tail) (hne : x ≠ pivot) : x ∈ tail := by
  rcases List.mem_cons.mp hx with h | h
  · exact absurd h hne
  · exact h

private theorem filter_pairTag_zero (pivot : α) (tail : List α) :
    (pairSet (pivot :: tail)).filter (fun p => pairTag pivot p = 0) =
      pairSet (tail.filter (fun x => x < pivot)) := by
  ext ⟨x, y⟩
  simp only [Finset.mem_filter, mem_pairSet]
  constructor
  · rintro ⟨⟨hx, hy, hlt⟩, htag⟩
    have hylt : y < pivot := pairTag_eq_zero.mp htag
    have hxlt : x < pivot := hlt.trans hylt
    exact ⟨mem_belowFilter.mpr
        ⟨mem_tail_of_mem_cons_ne hx (ne_of_lt hxlt), hxlt⟩,
      mem_belowFilter.mpr
        ⟨mem_tail_of_mem_cons_ne hy (ne_of_lt hylt), hylt⟩, hlt⟩
  · rintro ⟨hx, hy, hlt⟩
    obtain ⟨hxt, hxlt⟩ := mem_belowFilter.mp hx
    obtain ⟨hyt, hylt⟩ := mem_belowFilter.mp hy
    exact ⟨⟨List.mem_cons_of_mem _ hxt, List.mem_cons_of_mem _ hyt, hlt⟩,
      pairTag_eq_zero.mpr hylt⟩

private theorem filter_pairTag_one (pivot : α) (tail : List α) :
    (pairSet (pivot :: tail)).filter (fun p => pairTag pivot p = 1) =
      pairSet (tail.filter (fun x => pivot < x)) := by
  ext ⟨x, y⟩
  simp only [Finset.mem_filter, mem_pairSet]
  constructor
  · rintro ⟨⟨hx, hy, hlt⟩, htag⟩
    have hxgt : pivot < x := (pairTag_eq_one hlt).mp htag
    have hygt : pivot < y := hxgt.trans hlt
    exact ⟨mem_aboveFilter.mpr
        ⟨mem_tail_of_mem_cons_ne hx (ne_of_gt hxgt), hxgt⟩,
      mem_aboveFilter.mpr
        ⟨mem_tail_of_mem_cons_ne hy (ne_of_gt hygt), hygt⟩, hlt⟩
  · rintro ⟨hx, hy, hlt⟩
    obtain ⟨hxt, hxgt⟩ := mem_aboveFilter.mp hx
    obtain ⟨hyt, -⟩ := mem_aboveFilter.mp hy
    exact ⟨⟨List.mem_cons_of_mem _ hxt, List.mem_cons_of_mem _ hyt, hlt⟩,
      (pairTag_eq_one hlt).mpr hxgt⟩

private theorem filter_pairTag_two (pivot : α) (tail : List α) :
    (pairSet (pivot :: tail)).filter (fun p => pairTag pivot p = 2) =
      (tail.filter (fun x => x < pivot)).toFinset.image
        (fun a => (a, pivot)) := by
  ext ⟨x, y⟩
  simp only [Finset.mem_filter, mem_pairSet, Finset.mem_image,
    List.mem_toFinset]
  constructor
  · rintro ⟨⟨hx, -, hlt⟩, htag⟩
    have hyEq : y = pivot := (pairTag_eq_two hlt).mp htag
    have hxlt : x < pivot := hyEq ▸ hlt
    exact ⟨x, mem_belowFilter.mpr
      ⟨mem_tail_of_mem_cons_ne hx (ne_of_lt hxlt), hxlt⟩,
      Prod.ext rfl hyEq.symm⟩
  · rintro ⟨a, ha, hEq⟩
    have hax : a = x := congrArg Prod.fst hEq
    have hpy : pivot = y := congrArg Prod.snd hEq
    subst hax
    subst hpy
    obtain ⟨hat, hlt⟩ := mem_belowFilter.mp ha
    exact ⟨⟨List.mem_cons_of_mem _ hat, List.mem_cons_self, hlt⟩,
      (pairTag_eq_two hlt).mpr rfl⟩

private theorem filter_pairTag_three (pivot : α) (tail : List α) :
    (pairSet (pivot :: tail)).filter (fun p => pairTag pivot p = 3) =
      (tail.filter (fun x => pivot < x)).toFinset.image
        (fun b => (pivot, b)) := by
  ext ⟨x, y⟩
  simp only [Finset.mem_filter, mem_pairSet, Finset.mem_image,
    List.mem_toFinset]
  constructor
  · rintro ⟨⟨-, hy, hlt⟩, htag⟩
    have hxEq : x = pivot := (pairTag_eq_three hlt).mp htag
    have hygt : pivot < y := hxEq ▸ hlt
    exact ⟨y, mem_aboveFilter.mpr
      ⟨mem_tail_of_mem_cons_ne hy (ne_of_gt hygt), hygt⟩,
      Prod.ext hxEq.symm rfl⟩
  · rintro ⟨b, hb, hEq⟩
    have hpx : pivot = x := congrArg Prod.fst hEq
    have hby : b = y := congrArg Prod.snd hEq
    subst hby
    subst hpx
    obtain ⟨hbt, hlt⟩ := mem_aboveFilter.mp hb
    exact ⟨⟨List.mem_cons_self, List.mem_cons_of_mem _ hbt, hlt⟩,
      (pairTag_eq_three hlt).mpr rfl⟩

/-- One unfolding step of the pair-sum: pairs with the pivot contribute
`tail.length`, pairs inside each side recurse on that side's filter,
and cross pairs contribute `0`. -/
private theorem pairSum_cons {pivot : α} {tail : List α}
    (hnd : (pivot :: tail).Nodup) :
    pairSum (pivot :: tail) = tail.length +
      pairSum (tail.filter (fun x => x < pivot)) +
      pairSum (tail.filter (fun x => pivot < x)) := by
  obtain ⟨hpivotNot, htailNd⟩ := List.nodup_cons.mp hnd
  have hBnd : (tail.filter (fun x => x < pivot)).Nodup :=
    htailNd.filter _
  have hAnd : (tail.filter (fun x => pivot < x)).Nodup :=
    htailNd.filter _
  have hlen : (tail.filter (fun x => x < pivot)).length +
      (tail.filter (fun x => pivot < x)).length = tail.length := by
    have hparts := partition3_length pivot tail
    rw [partition3_below_eq_filter, partition3_equal_eq_filter,
      partition3_above_eq_filter] at hparts
    have heqNil : tail.filter (fun x => x = pivot) = [] := by
      refine List.filter_eq_nil_iff.mpr fun x hx => ?_
      have hne : x ≠ pivot := fun hh => hpivotNot (hh ▸ hx)
      simp [hne]
    rw [heqNil] at hparts
    simp at hparts
    omega
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := pairSet (pivot :: tail)) (t := Finset.range 5)
    (g := pairTag pivot)
    (fun p _ => Finset.mem_range.mpr (pairTag_lt pivot p))
    (fun p => cmpInd (pivot :: tail) p.1 p.2)
  have h0 : (∑ p ∈ (pairSet (pivot :: tail)).filter
        (fun p => pairTag pivot p = 0),
        cmpInd (pivot :: tail) p.1 p.2) =
      pairSum (tail.filter (fun x => x < pivot)) := by
    rw [filter_pairTag_zero]
    unfold pairSum
    refine Finset.sum_congr rfl fun ⟨x, y⟩ hp => ?_
    have hylt : y < pivot :=
      (mem_belowFilter.mp (mem_pairSet.mp hp).2.1).2
    exact cmpInd_cons_below hylt
  have h1 : (∑ p ∈ (pairSet (pivot :: tail)).filter
        (fun p => pairTag pivot p = 1),
        cmpInd (pivot :: tail) p.1 p.2) =
      pairSum (tail.filter (fun x => pivot < x)) := by
    rw [filter_pairTag_one]
    unfold pairSum
    refine Finset.sum_congr rfl fun ⟨x, y⟩ hp => ?_
    have hxgt : pivot < x :=
      (mem_aboveFilter.mp (mem_pairSet.mp hp).1).2
    exact cmpInd_cons_above hxgt
  have h2 : (∑ p ∈ (pairSet (pivot :: tail)).filter
        (fun p => pairTag pivot p = 2),
        cmpInd (pivot :: tail) p.1 p.2) =
      (tail.filter (fun x => x < pivot)).length := by
    rw [filter_pairTag_two, Finset.sum_image
      (fun x _ y _ hxy => congrArg Prod.fst hxy)]
    have hterm : ∀ a ∈ (tail.filter (fun x => x < pivot)).toFinset,
        cmpInd (pivot :: tail) a pivot = 1 := by
      intro a ha
      have halt : a < pivot :=
        (mem_belowFilter.mp (List.mem_toFinset.mp ha)).2
      rw [cmpInd_cons_pivot ⟨halt.le, le_rfl⟩]
      simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_const,
      List.toFinset_card_of_nodup hBnd]
    simp
  have h3 : (∑ p ∈ (pairSet (pivot :: tail)).filter
        (fun p => pairTag pivot p = 3),
        cmpInd (pivot :: tail) p.1 p.2) =
      (tail.filter (fun x => pivot < x)).length := by
    rw [filter_pairTag_three, Finset.sum_image
      (fun x _ y _ hxy => congrArg Prod.snd hxy)]
    have hterm : ∀ b ∈ (tail.filter (fun x => pivot < x)).toFinset,
        cmpInd (pivot :: tail) pivot b = 1 := by
      intro b hb
      have hbgt : pivot < b :=
        (mem_aboveFilter.mp (List.mem_toFinset.mp hb)).2
      rw [cmpInd_cons_pivot ⟨le_rfl, hbgt.le⟩]
      simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_const,
      List.toFinset_card_of_nodup hAnd]
    simp
  have h4 : (∑ p ∈ (pairSet (pivot :: tail)).filter
        (fun p => pairTag pivot p = 4),
        cmpInd (pivot :: tail) p.1 p.2) = 0 := by
    refine Finset.sum_eq_zero fun ⟨x, y⟩ hp => ?_
    rw [Finset.mem_filter] at hp
    have hlt : x < y := (mem_pairSet.mp hp.1).2.2
    obtain ⟨hlo, hhi⟩ := (pairTag_eq_four hlt).mp hp.2
    rw [cmpInd_cons_pivot ⟨hlo.le, hhi.le⟩]
    simp [(ne_of_lt hlo).symm, ne_of_lt hhi]
  have hgoal : pairSum (pivot :: tail) =
      ∑ k ∈ Finset.range 5, ∑ p ∈ (pairSet (pivot :: tail)).filter
        (fun p => pairTag pivot p = k),
        cmpInd (pivot :: tail) p.1 p.2 := hfib.symm
  rw [hgoal]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [h0, h1, h2, h3, h4]
  omega

/-- Deterministic decomposition: on a duplicate-free ordering, the
comparison count of `quickSort` is the sum of the pair indicators. -/
private theorem quickSort_time_eq_pairSum {ys : List α}
    (hnd : ys.Nodup) : (quickSort ys).time = pairSum ys := by
  unfold quickSort
  have loop_eq : ∀ (fuel : ℕ) (ys : List α), ys.length ≤ fuel →
      ys.Nodup → (quickSort.loop fuel ys).time = pairSum ys := by
    intro fuel
    induction fuel with
    | zero =>
        intro ys hlen _hnd
        cases ys with
        | nil => simp [quickSort.loop, pairSum, pairSet]
        | cons y ys => simp at hlen
    | succ fuel ih =>
        intro ys hlen hnd
        cases ys with
        | nil => simp [quickSort.loop, pairSum, pairSet]
        | cons pivot tail =>
            obtain ⟨hpivotNot, htailNd⟩ := List.nodup_cons.mp hnd
            have htail : tail.length ≤ fuel := by
              simpa only [List.length_cons, Nat.succ_le_succ_iff] using hlen
            generalize hparts : (partition3 pivot tail).ret = parts
            have hbelowEq : parts.below =
                tail.filter (fun x => x < pivot) := by
              have h := partition3_below_eq_filter pivot tail
              rw [hparts] at h
              exact h
            have haboveEq : parts.above =
                tail.filter (fun x => pivot < x) := by
              have h := partition3_above_eq_filter pivot tail
              rw [hparts] at h
              exact h
            have hpartsLength := partition3_length pivot tail
            rw [hparts] at hpartsLength
            have hbelowFuel : parts.below.length ≤ fuel := by omega
            have haboveFuel : parts.above.length ≤ fuel := by omega
            have ihB := ih parts.below hbelowFuel
              (hbelowEq ▸ htailNd.filter _)
            have ihA := ih parts.above haboveFuel
              (haboveEq ▸ htailNd.filter _)
            simp only [quickSort.loop, time_bind, time_pure, hparts,
              partition3_time]
            rw [ihB, ihA, hbelowEq, haboveEq, pairSum_cons hnd]
            omega
  exact loop_eq ys.length ys (Nat.le_refl _) hnd

omit [LinearOrder α] in
private theorem mem_permuted {xs : List α}
    (σ : Equiv.Perm (Fin xs.length)) {v : α} :
    v ∈ List.ofFn (fun p => xs.get (σ p)) ↔ v ∈ xs := by
  constructor
  · intro h
    rw [List.mem_ofFn] at h
    obtain ⟨i, hi⟩ := h
    exact List.mem_iff_get.mpr ⟨σ i, hi⟩
  · intro h
    rw [List.mem_ofFn]
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp h
    exact ⟨σ.symm i, by rw [Equiv.apply_symm_apply]; exact hi⟩

omit [LinearOrder α] in
private theorem nodup_permuted {xs : List α} (hxs : xs.Nodup)
    (σ : Equiv.Perm (Fin xs.length)) :
    (List.ofFn (fun p => xs.get (σ p))).Nodup := by
  refine List.nodup_ofFn.mpr fun i j h => ?_
  exact σ.injective ((List.Nodup.get_inj_iff hxs).mp h)

private theorem pairSet_permuted {xs : List α}
    (σ : Equiv.Perm (Fin xs.length)) :
    pairSet (List.ofFn (fun p => xs.get (σ p))) = pairSet xs := by
  have htoFinset :
      (List.ofFn (fun p => xs.get (σ p))).toFinset = xs.toFinset := by
    ext v
    simp only [List.mem_toFinset]
    exact mem_permuted σ
  unfold pairSet
  rw [htoFinset]

private theorem quickSort_time_permuted {xs : List α} (hxs : xs.Nodup)
    (σ : Equiv.Perm (Fin xs.length)) :
    (quickSort (List.ofFn (fun p => xs.get (σ p)))).time =
      ∑ p ∈ pairSet xs,
        cmpInd (List.ofFn (fun q => xs.get (σ q))) p.1 p.2 := by
  rw [quickSort_time_eq_pairSum (nodup_permuted hxs σ), pairSum,
    pairSet_permuted]

/-- The values of `xs` lying in the closed interval `[a, b]`. -/
private def intervalFinset (xs : List α) (a b : α) : Finset α :=
  xs.toFinset.filter (fun x => a ≤ x ∧ x ≤ b)

private theorem mem_intervalFinset {xs : List α} {a b x : α} :
    x ∈ intervalFinset xs a b ↔ x ∈ xs ∧ a ≤ x ∧ x ≤ b := by
  simp [intervalFinset, List.mem_toFinset]

/-- The permutations whose first interval entry (for `[a, b]`) is a
given value `x₀`. -/
private def firstFiber (xs : List α) (a b x₀ : α) :
    Finset (Equiv.Perm (Fin xs.length)) :=
  Finset.univ.filter (fun σ =>
    (List.ofFn (fun p => xs.get (σ p))).find? (inAB a b) = some x₀)

private theorem mem_firstFiber {xs : List α} {a b x₀ : α}
    {σ : Equiv.Perm (Fin xs.length)} :
    σ ∈ firstFiber xs a b x₀ ↔
      (List.ofFn (fun p => xs.get (σ p))).find? (inAB a b) = some x₀ := by
  simp [firstFiber]

/-- The interval `[a, b]` contains exactly `betweenCount xs a b + 2`
values of a duplicate-free `xs` when `a < b` both occur in `xs`. -/
private theorem card_intervalFinset {xs : List α} (hxs : xs.Nodup)
    {a b : α} (ha : a ∈ xs) (hb : b ∈ xs) (hab : a < b) :
    (intervalFinset xs a b).card = betweenCount xs a b + 2 := by
  have hBcard :
      (xs.toFinset.filter (fun x => a < x ∧ x < b)).card =
        betweenCount xs a b := by
    rw [List.filter_toFinset, List.toFinset_card_of_nodup (hxs.filter _)]
    rfl
  have hSetEq : intervalFinset xs a b =
      insert a (insert b
        (xs.toFinset.filter (fun x => a < x ∧ x < b))) := by
    ext x
    simp only [mem_intervalFinset, Finset.mem_insert, Finset.mem_filter,
      List.mem_toFinset]
    constructor
    · rintro ⟨hx, h1, h2⟩
      by_cases hxa : x = a
      · exact Or.inl hxa
      · by_cases hxb : x = b
        · exact Or.inr (Or.inl hxb)
        · exact Or.inr (Or.inr ⟨hx,
            lt_of_le_of_ne h1 (fun hh => hxa hh.symm),
            lt_of_le_of_ne h2 hxb⟩)
    · rintro (rfl | rfl | ⟨hx, h1, h2⟩)
      · exact ⟨ha, le_rfl, hab.le⟩
      · exact ⟨hb, hab.le, le_rfl⟩
      · exact ⟨hx, h1.le, h2.le⟩
  have hbNot : b ∉ xs.toFinset.filter (fun x => a < x ∧ x < b) := by
    simp only [Finset.mem_filter, List.mem_toFinset]
    rintro ⟨-, -, hlt⟩
    exact lt_irrefl _ hlt
  have haNot : a ∉ insert b
      (xs.toFinset.filter (fun x => a < x ∧ x < b)) := by
    simp only [Finset.mem_insert, Finset.mem_filter, List.mem_toFinset]
    rintro (h | ⟨-, hlt, -⟩)
    · exact hab.ne h
    · exact lt_irrefl _ hlt
  rw [hSetEq, Finset.card_insert_of_notMem haNot,
    Finset.card_insert_of_notMem hbNot, hBcard]

/-- All first-entry fibers over interval values have the same
cardinality: swapping the values `x` and `y` (both in the interval) in
every ordering bijects the fiber over `x` with the fiber over `y`. -/
private theorem firstFiber_card_eq {xs : List α} (hxs : xs.Nodup)
    {a b x y : α} (hx : x ∈ intervalFinset xs a b)
    (hy : y ∈ intervalFinset xs a b) :
    (firstFiber xs a b x).card = (firstFiber xs a b y).card := by
  obtain ⟨hxmem, hx1, hx2⟩ := mem_intervalFinset.mp hx
  obtain ⟨hymem, hy1, hy2⟩ := mem_intervalFinset.mp hy
  obtain ⟨ix, hix⟩ := List.mem_iff_get.mp hxmem
  obtain ⟨iy, hiy⟩ := List.mem_iff_get.mp hymem
  have hswapGet : ∀ k : Fin xs.length,
      xs.get (Equiv.swap ix iy k) = Equiv.swap x y (xs.get k) := by
    intro k
    by_cases hk : k = ix
    · subst hk
      rw [Equiv.swap_apply_left, hix, hiy, Equiv.swap_apply_left]
    · by_cases hk2 : k = iy
      · subst hk2
        rw [Equiv.swap_apply_right, hiy, hix, Equiv.swap_apply_right]
      · have hkx : xs.get k ≠ x := by
          intro hh
          exact hk ((List.Nodup.get_inj_iff hxs).mp (by rw [hh, hix]))
        have hky : xs.get k ≠ y := by
          intro hh
          exact hk2 ((List.Nodup.get_inj_iff hxs).mp (by rw [hh, hiy]))
        rw [Equiv.swap_apply_of_ne_of_ne hk hk2,
          Equiv.swap_apply_of_ne_of_ne hkx hky]
  have hlist : ∀ σ : Equiv.Perm (Fin xs.length),
      List.ofFn (fun p => xs.get ((Equiv.swap ix iy * σ) p)) =
        (List.ofFn (fun p => xs.get (σ p))).map (Equiv.swap x y) := by
    intro σ
    rw [List.map_ofFn]
    congr 1
    funext p
    simp only [Function.comp_apply, Equiv.Perm.mul_apply]
    exact hswapGet (σ p)
  have hIx : inAB a b x = true := inAB_iff.mpr ⟨hx1, hx2⟩
  have hIy : inAB a b y = true := inAB_iff.mpr ⟨hy1, hy2⟩
  have hpres : ∀ v : α, inAB a b (Equiv.swap x y v) = inAB a b v := by
    intro v
    by_cases hvx : v = x
    · subst hvx
      rw [Equiv.swap_apply_left, hIy, hIx]
    · by_cases hvy : v = y
      · subst hvy
        rw [Equiv.swap_apply_right, hIx, hIy]
      · rw [Equiv.swap_apply_of_ne_of_ne hvx hvy]
  have hfind : ∀ σ : Equiv.Perm (Fin xs.length),
      (List.ofFn (fun p => xs.get ((Equiv.swap ix iy * σ) p))).find?
          (inAB a b) =
        ((List.ofFn (fun p => xs.get (σ p))).find? (inAB a b)).map
          (Equiv.swap x y) := by
    intro σ
    rw [hlist]
    exact find?_map_eq hpres _
  refine Finset.card_bij' (fun σ _ => Equiv.swap ix iy * σ)
    (fun σ _ => Equiv.swap ix iy * σ) ?_ ?_ ?_ ?_
  · intro σ hσ
    rw [mem_firstFiber] at hσ ⊢
    rw [hfind, hσ]
    simp [Equiv.swap_apply_left]
  · intro σ hσ
    rw [mem_firstFiber] at hσ ⊢
    rw [hfind, hσ]
    simp [Equiv.swap_apply_right]
  · intro σ _
    exact Equiv.swap_mul_self_mul ix iy σ
  · intro σ _
    exact Equiv.swap_mul_self_mul ix iy σ

/-- The first-entry fibers partition all permutations, so the number
of interval values times the size of one fiber is `n !`. -/
private theorem card_firstFiber_mul {xs : List α} (hxs : xs.Nodup)
    {a b : α} (ha : a ∈ xs) (hb : b ∈ xs) (hab : a < b) :
    (intervalFinset xs a b).card * (firstFiber xs a b a).card =
      xs.length.factorial := by
  have haInt : a ∈ intervalFinset xs a b :=
    mem_intervalFinset.mpr ⟨ha, le_rfl, hab.le⟩
  have hdisj : ((intervalFinset xs a b : Set α)).PairwiseDisjoint
      (firstFiber xs a b) := by
    intro x _ y _ hne
    show Disjoint (firstFiber xs a b x) (firstFiber xs a b y)
    rw [Finset.disjoint_left]
    intro σ hσ hσ'
    rw [mem_firstFiber] at hσ hσ'
    exact hne (Option.some.inj (hσ.symm.trans hσ'))
  have hcover : (intervalFinset xs a b).biUnion (firstFiber xs a b) =
      Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro σ
    have hex : ∃ x, x ∈ List.ofFn (fun p => xs.get (σ p)) ∧
        inAB a b x :=
      ⟨b, (mem_permuted σ).mpr hb, inAB_iff.mpr ⟨hab.le, le_rfl⟩⟩
    have hsome := List.find?_isSome.mpr hex
    obtain ⟨x₀, hx₀⟩ := Option.isSome_iff_exists.mp hsome
    have hx₀mem : x₀ ∈ List.ofFn (fun p => xs.get (σ p)) :=
      List.mem_of_find?_eq_some hx₀
    have hx₀int : a ≤ x₀ ∧ x₀ ≤ b :=
      inAB_iff.mp (List.find?_some hx₀)
    rw [Finset.mem_biUnion]
    exact ⟨x₀,
      mem_intervalFinset.mpr
        ⟨(mem_permuted σ).mp hx₀mem, hx₀int.1, hx₀int.2⟩,
      mem_firstFiber.mpr hx₀⟩
  have hcard : ∀ x ∈ intervalFinset xs a b,
      (firstFiber xs a b x).card = (firstFiber xs a b a).card :=
    fun x hx => firstFiber_card_eq hxs hx haInt
  have hsum : (Finset.univ :
      Finset (Equiv.Perm (Fin xs.length))).card =
      ∑ x ∈ intervalFinset xs a b, (firstFiber xs a b x).card := by
    rw [← hcover, Finset.card_biUnion hdisj]
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hsum
  rw [hsum, Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul]

/-- Per-pair expectation: the average of the `(a, b)` indicator over
all permutations is `2 / (betweenCount xs a b + 2)` in `ℝ≥0∞`. -/
private theorem inv_factorial_mul_sum_cmpInd {xs : List α}
    (hxs : xs.Nodup) {a b : α} (ha : a ∈ xs) (hb : b ∈ xs)
    (hab : a < b) :
    (xs.length.factorial : ℝ≥0∞)⁻¹ *
        ∑ σ : Equiv.Perm (Fin xs.length),
          (cmpInd (List.ofFn (fun p => xs.get (σ p))) a b : ℝ≥0∞) =
      2 * ((betweenCount xs a b + 2 : ℕ) : ℝ≥0∞)⁻¹ := by
  have haInt : a ∈ intervalFinset xs a b :=
    mem_intervalFinset.mpr ⟨ha, le_rfl, hab.le⟩
  have hbInt : b ∈ intervalFinset xs a b :=
    mem_intervalFinset.mpr ⟨hb, hab.le, le_rfl⟩
  have hsumCard :
      (∑ σ : Equiv.Perm (Fin xs.length),
          (cmpInd (List.ofFn (fun p => xs.get (σ p))) a b : ℝ≥0∞)) =
        ((Finset.univ.filter (fun σ : Equiv.Perm (Fin xs.length) =>
          comparedProp (List.ofFn (fun p => xs.get (σ p))) a b)).card :
          ℝ≥0∞) := by
    have hcongr : (∑ σ : Equiv.Perm (Fin xs.length),
          (cmpInd (List.ofFn (fun p => xs.get (σ p))) a b : ℝ≥0∞)) =
        ∑ σ : Equiv.Perm (Fin xs.length),
          (if comparedProp (List.ofFn (fun p => xs.get (σ p))) a b
            then (1 : ℝ≥0∞) else 0) := by
      refine Finset.sum_congr rfl fun σ _ => ?_
      unfold cmpInd
      split_ifs <;> simp
    rw [hcongr, Finset.sum_boole]
  have hfilterEq : Finset.univ.filter (fun σ : Equiv.Perm (Fin xs.length) =>
        comparedProp (List.ofFn (fun p => xs.get (σ p))) a b) =
      firstFiber xs a b a ∪ firstFiber xs a b b := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, mem_firstFiber]
  have hdisj : Disjoint (firstFiber xs a b a) (firstFiber xs a b b) := by
    rw [Finset.disjoint_left]
    intro σ hσ hσ'
    rw [mem_firstFiber] at hσ hσ'
    exact hab.ne (Option.some.inj (hσ.symm.trans hσ'))
  have hcardCmp :
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin xs.length) =>
        comparedProp (List.ofFn (fun p => xs.get (σ p))) a b)).card =
        (firstFiber xs a b a).card + (firstFiber xs a b b).card := by
    rw [hfilterEq, Finset.card_union_of_disjoint hdisj]
  have hfiberB : (firstFiber xs a b b).card =
      (firstFiber xs a b a).card :=
    firstFiber_card_eq hxs hbInt haInt
  have hmul := card_firstFiber_mul hxs ha hb hab
  have hcardInt := card_intervalFinset hxs ha hb hab
  have hNat : (betweenCount xs a b + 2) *
        (Finset.univ.filter (fun σ : Equiv.Perm (Fin xs.length) =>
          comparedProp (List.ofFn (fun p => xs.get (σ p))) a b)).card =
      2 * xs.length.factorial := by
    rw [hcardCmp, hfiberB]
    have hring : (betweenCount xs a b + 2) *
          ((firstFiber xs a b a).card + (firstFiber xs a b a).card) =
        2 * ((betweenCount xs a b + 2) * (firstFiber xs a b a).card) := by
      ring
    rw [hring, ← hcardInt, hmul]
  have hENN : ((betweenCount xs a b + 2 : ℕ) : ℝ≥0∞) *
        ((Finset.univ.filter (fun σ : Equiv.Perm (Fin xs.length) =>
          comparedProp (List.ofFn (fun p => xs.get (σ p))) a b)).card :
          ℝ≥0∞) =
      2 * (xs.length.factorial : ℝ≥0∞) := by
    exact_mod_cast hNat
  have hfact0 : (xs.length.factorial : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  have hfactT : (xs.length.factorial : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hd0 : ((betweenCount xs a b + 2 : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (by omega : betweenCount xs a b + 2 ≠ 0)
  have hdT : ((betweenCount xs a b + 2 : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hkey : (xs.length.factorial : ℝ≥0∞)⁻¹ *
        ((Finset.univ.filter (fun σ : Equiv.Perm (Fin xs.length) =>
          comparedProp (List.ofFn (fun p => xs.get (σ p))) a b)).card :
          ℝ≥0∞) *
        ((betweenCount xs a b + 2 : ℕ) : ℝ≥0∞) = 2 := by
    calc (xs.length.factorial : ℝ≥0∞)⁻¹ *
          ((Finset.univ.filter (fun σ : Equiv.Perm (Fin xs.length) =>
            comparedProp (List.ofFn (fun p => xs.get (σ p))) a b)).card :
            ℝ≥0∞) *
          ((betweenCount xs a b + 2 : ℕ) : ℝ≥0∞)
        = (xs.length.factorial : ℝ≥0∞)⁻¹ *
            (((betweenCount xs a b + 2 : ℕ) : ℝ≥0∞) *
              ((Finset.univ.filter (fun σ : Equiv.Perm (Fin xs.length) =>
                comparedProp (List.ofFn (fun p => xs.get (σ p)))
                  a b)).card : ℝ≥0∞)) := by ring
      _ = (xs.length.factorial : ℝ≥0∞)⁻¹ *
            (2 * (xs.length.factorial : ℝ≥0∞)) := by rw [hENN]
      _ = 2 * ((xs.length.factorial : ℝ≥0∞)⁻¹ *
            (xs.length.factorial : ℝ≥0∞)) := by ring
      _ = 2 := by
          rw [ENNReal.inv_mul_cancel hfact0 hfactT, mul_one]
  rw [hsumCard]
  calc (xs.length.factorial : ℝ≥0∞)⁻¹ *
        ((Finset.univ.filter (fun σ : Equiv.Perm (Fin xs.length) =>
          comparedProp (List.ofFn (fun p => xs.get (σ p))) a b)).card :
          ℝ≥0∞)
      = ((xs.length.factorial : ℝ≥0∞)⁻¹ *
          ((Finset.univ.filter (fun σ : Equiv.Perm (Fin xs.length) =>
            comparedProp (List.ofFn (fun p => xs.get (σ p))) a b)).card :
            ℝ≥0∞) *
          ((betweenCount xs a b + 2 : ℕ) : ℝ≥0∞)) *
          ((betweenCount xs a b + 2 : ℕ) : ℝ≥0∞)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hd0 hdT, mul_one]
    _ = 2 * ((betweenCount xs a b + 2 : ℕ) : ℝ≥0∞)⁻¹ := by rw [hkey]

/-- **Expected comparisons of quicksort on a random permutation.** Let $\ell$ be a list without
repeated entries over a linear order. The expected number of comparisons made by quicksort on the
list obtained by rearranging the entries of $\ell$ by a uniformly random permutation of their
positions, computed in the extended nonnegative reals $[0, \infty]$, equals

$$\sum_{a < b} \frac{2}{d(a, b) + 2},$$

where the sum runs over pairs of entries $a < b$ of $\ell$ and $d(a, b)$ is the number of entries
of $\ell$ strictly between $a$ and $b$ (CLRS Section 7.4). -/
public theorem quickSort_expectedTime_uniformPermutation
    (xs : List α) (hxs : xs.Nodup) :
    expectedTime quickSort (uniformPermutation xs) =
      ∑ p ∈ (xs.toFinset ×ˢ xs.toFinset).filter (fun p => p.1 < p.2),
        (2 : ℝ≥0∞) * ((betweenCount xs p.1 p.2 + 2 : ℝ≥0∞))⁻¹ := by
  rw [expectedTime_uniformPermutation]
  show (xs.length.factorial : ℝ≥0∞)⁻¹ *
        ∑ σ : Equiv.Perm (Fin xs.length),
          ((quickSort (List.ofFn (fun p => xs.get (σ p)))).time :
            ℝ≥0∞) =
      ∑ p ∈ pairSet xs,
        (2 : ℝ≥0∞) * ((betweenCount xs p.1 p.2 + 2 : ℝ≥0∞))⁻¹
  have hcast : ∀ σ : Equiv.Perm (Fin xs.length),
      ((quickSort (List.ofFn (fun p => xs.get (σ p)))).time : ℝ≥0∞) =
        ∑ p ∈ pairSet xs,
          (cmpInd (List.ofFn (fun q => xs.get (σ q))) p.1 p.2 :
            ℝ≥0∞) := by
    intro σ
    rw [quickSort_time_permuted hxs σ, Nat.cast_sum]
  have hsumEq :
      (∑ σ : Equiv.Perm (Fin xs.length),
          ((quickSort (List.ofFn (fun p => xs.get (σ p)))).time :
            ℝ≥0∞)) =
        ∑ σ : Equiv.Perm (Fin xs.length),
          ∑ p ∈ pairSet xs,
            (cmpInd (List.ofFn (fun q => xs.get (σ q))) p.1 p.2 :
              ℝ≥0∞) :=
    Finset.sum_congr rfl fun σ _ => hcast σ
  rw [hsumEq, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨ha, hb, hab⟩ := mem_pairSet.mp hp
  have h := inv_factorial_mul_sum_cmpInd hxs ha hb hab
  have hcast2 : ((betweenCount xs p.1 p.2 : ℝ≥0∞) + 2) =
      ((betweenCount xs p.1 p.2 + 2 : ℕ) : ℝ≥0∞) := by
    push_cast
    ring
  rw [hcast2]
  exact h

/-- **Expected comparisons of quicksort on a random permutation, as a real number.** Let $\ell$
be a list without repeated entries over a linear order. Take the expected number of comparisons
made by quicksort on the list obtained by rearranging the entries of $\ell$ by a uniformly random
permutation of their positions, which is an element of $[0, \infty]$, and convert it to a real
number. The result equals the real sum

$$\sum_{a < b} \frac{2}{d(a, b) + 2},$$

where the sum runs over pairs of entries $a < b$ of $\ell$ and $d(a, b)$ is the number of entries
of $\ell$ strictly between $a$ and $b$. -/
public theorem quickSort_expectedTime_uniformPermutation_toReal
    (xs : List α) (hxs : xs.Nodup) :
    (expectedTime quickSort (uniformPermutation xs)).toReal =
      ∑ p ∈ (xs.toFinset ×ˢ xs.toFinset).filter (fun p => p.1 < p.2),
        (2 : ℝ) / (betweenCount xs p.1 p.2 + 2) := by
  rw [quickSort_expectedTime_uniformPermutation xs hxs,
    ENNReal.toReal_sum (fun p _ =>
      ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (ENNReal.inv_ne_top.mpr (by positivity)))]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_add (ENNReal.natCast_ne_top _) ENNReal.ofNat_ne_top,
    ENNReal.toReal_natCast, div_eq_mul_inv]
  norm_num

end Cslib.Algorithms.Lean.TimeM
