/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Multiset.Powerset
import Mathlib.Data.Nat.BitIndices
import Mathlib.Order.Interval.Finset.Nat

/-!
# Colored partitions with restricted colors

A colored part and its simultaneous doubles form a chain based at a pair that is not
both even. Splitting a part down its chain gives a power-of-two multiplicity at the base;
binary expansion reverses the splitting. Swapping adjacent colors on even sizes gives the
other parity restriction.
-/

namespace MetaMathlibExt

namespace coloredPartitions_differentParts_eq_restrictedColors

open Finset Multiset

private def digits (k : ℕ) : Finset ℕ := k.bitIndices.toFinset

private lemma sum_digits (k : ℕ) : (∑ i ∈ digits k, 2 ^ i) = k := by
  rw [digits, List.sum_toFinset _ Nat.bitIndices_nodup, Nat.sum_map_two_pow_bitIndices]

private lemma digits_sum (s : Finset ℕ) : digits (∑ i ∈ s, 2 ^ i) = s := by
  rw [← s.sort_toFinset (· ≤ ·), List.sum_toFinset _ s.sortedLT_sort.nodup,
    digits, Nat.bitIndices_sum_map_two_pow s.sortedLT_sort]

-- At base `a`, retain just the indices of the powers of two present in `s`.
private def fiberDigits {α : Type*} [DecidableEq α] (s : Finset (α × ℕ)) (a : α) : Finset ℕ :=
  (s.filter fun x => x.1 = a).image Prod.snd

private lemma mem_fiberDigits {α : Type*} [DecidableEq α]
    {s : Finset (α × ℕ)} {a : α} {i : ℕ} : i ∈ fiberDigits s a ↔ (a, i) ∈ s := by
  simp only [fiberDigits, Finset.mem_image, Finset.mem_filter, Prod.exists]
  constructor
  · rintro ⟨b, j, ⟨h, rfl⟩, rfl⟩
    exact h
  · exact fun h => ⟨a, i, ⟨h, rfl⟩, rfl⟩

private def pack {α : Type*} (s : Finset (α × ℕ)) : Multiset α :=
  ∑ x ∈ s, (2 ^ x.2) • ({x.1} : Multiset α)

private lemma count_pack {α : Type*} [DecidableEq α] (s : Finset (α × ℕ)) (a : α) :
    (pack s).count a = ∑ i ∈ fiberDigits s a, 2 ^ i := by
  rw [pack, Multiset.count_sum', fiberDigits, Finset.sum_image, Finset.sum_filter]
  · apply Finset.sum_congr rfl
    intro x _
    by_cases h : x.1 = a
    · simp [h]
    · simp [h, Ne.symm h]
  · intro x hx y hy h
    exact Prod.ext ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) h

-- Only bases in the support of `M` can contribute any binary digits.
private def unpack {α : Type*} [DecidableEq α] (M : Multiset α) : Finset (α × ℕ) :=
  M.toFinset.biUnion fun a => (digits (M.count a)).map ⟨(a, ·), fun _ _ h => congrArg Prod.snd h⟩

private lemma mem_unpack {α : Type*} [DecidableEq α] {M : Multiset α} {a : α} {i : ℕ} :
    (a, i) ∈ unpack M ↔ i ∈ digits (M.count a) := by
  simp only [unpack, Finset.mem_biUnion, Multiset.mem_toFinset, Finset.mem_map]
  constructor
  · rintro ⟨b, _, j, hj, he⟩
    change (b, j) = (a, i) at he
    cases he
    exact hj
  · intro hi
    refine ⟨a, ?_, i, hi, rfl⟩
    by_contra h
    simp [Multiset.count_eq_zero_of_notMem h, digits] at hi

private lemma pack_unpack {α : Type*} [DecidableEq α] (M : Multiset α) : pack (unpack M) = M := by
  apply Multiset.ext.mpr
  intro a
  rw [count_pack, show fiberDigits (unpack M) a = digits (M.count a) by
    ext i
    rw [mem_fiberDigits, mem_unpack], sum_digits]

private lemma unpack_pack {α : Type*} [DecidableEq α] (s : Finset (α × ℕ)) :
    unpack (pack s) = s := by
  ext ⟨a, i⟩
  rw [mem_unpack, count_pack, digits_sum, mem_fiberDigits]

private def weight {α : Type*} (w : α → ℕ) (M : Multiset α) : ℕ := (M.map w).sum

private lemma weight_pack {α : Type*} (w : α → ℕ) (s : Finset (α × ℕ)) :
    weight w (pack s) = ∑ x ∈ s, 2 ^ x.2 * w x.1 := by
  let φ := Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom w)
  change φ (∑ x ∈ s, (2 ^ x.2) • ({x.1} : Multiset α)) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun x _ => by
    rw [AddMonoidHom.map_nsmul]
    simp [φ, nsmul_eq_mul]

private abbrev Part := ℕ × ℕ
private abbrev Valid (x : Part) : Prop := 1 ≤ x.2 ∧ x.2 ≤ x.1
private abbrev Primitive := {x : Part // Valid x ∧ (Even x.1 → ¬Even x.2)}

private def scale (x : Primitive × ℕ) : Part := (2 ^ x.2 * x.1.val.1, 2 ^ x.2 * x.1.val.2)

private lemma scale_valid (x : Primitive × ℕ) : Valid (scale x) := by
  refine ⟨?_, Nat.mul_le_mul_left _ x.1.property.1.2⟩
  exact Nat.mul_pos (Nat.two_pow_pos _) x.1.property.1.1

private lemma scale_succ (a : Primitive) (k : ℕ) :
    scale (a, k + 1) = (2 * (scale (a, k)).1, 2 * (scale (a, k)).2) := by
  simp only [scale, pow_succ', Nat.mul_assoc]

private lemma scale_zero (a : Primitive) : scale (a, 0) = a.val := by
  simp [scale]

private lemma scale_succ_even (a : Primitive) (k : ℕ) :
    Even (scale (a, k + 1)).1 ∧ Even (scale (a, k + 1)).2 := by
  rw [scale_succ]
  exact ⟨Nat.even_mul.mpr (Or.inl even_two), Nat.even_mul.mpr (Or.inl even_two)⟩

private lemma scale_injective : Function.Injective scale := by
  rintro ⟨a, k⟩ ⟨b, l⟩
  induction k generalizing l with
  | zero =>
    cases l with
    | zero =>
      intro h
      rw [scale_zero, scale_zero] at h
      exact congrArg (·, 0) (Subtype.ext h)
    | succ l =>
      intro h
      have he := scale_succ_even b l
      rw [← h, scale_zero] at he
      exact (a.property.2 he.1 he.2).elim
  | succ k ih =>
    cases l with
    | zero =>
      intro h
      have he := scale_succ_even a k
      rw [h, scale_zero] at he
      exact (b.property.2 he.1 he.2).elim
    | succ l =>
      intro h
      rw [scale_succ, scale_succ] at h
      have e := ih (l := l) (Prod.ext (Nat.mul_left_cancel (by decide) (congrArg Prod.fst h))
        (Nat.mul_left_cancel (by decide) (congrArg Prod.snd h)))
      exact congrArg (fun p : Primitive × ℕ => (p.1, p.2 + 1)) e

private lemma exists_scale (x : Part) (hx : Valid x) : x ∈ Set.range scale := by
  obtain ⟨m, j⟩ := x
  induction m using Nat.strong_induction_on generalizing j with
  | ind m ih =>
    rcases hx with ⟨hj, hjm⟩
    change 1 ≤ j at hj
    change j ≤ m at hjm
    by_cases h : Even m ∧ Even j
    · obtain ⟨hm, hj'⟩ := h
      rw [Nat.even_iff] at hm hj'
      obtain ⟨⟨a, k⟩, hk⟩ := ih (m / 2) (by omega) (j := j / 2) ⟨by omega, by omega⟩
      refine ⟨(a, k + 1), ?_⟩
      rw [scale_succ, hk]
      exact Prod.ext (by omega) (by omega)
    · exact ⟨(⟨(m, j), ⟨hj, hjm⟩, fun hm hj => h ⟨hm, hj⟩⟩, 0), scale_zero _⟩

private def scaleEmbedding : (Primitive × ℕ) ↪ Part := ⟨scale, scale_injective⟩

private lemma lift_parts {α β : Type*} (f : α → β) (M : Multiset β)
    (h : ∀ p ∈ M, p ∈ Set.range f) : ∃ T : Multiset α, T.map f = M := by
  choose g hg using fun p : {p // p ∈ M} => h p.val p.property
  refine ⟨M.attach.map g, ?_⟩
  rw [Multiset.map_map]
  exact (Multiset.map_congr rfl fun p _ => hg p).trans M.attach_map_val

private def distinct (n : ℕ) : Set (Multiset Part) :=
  {M | M.Nodup ∧ (∀ x ∈ M, Valid x) ∧ weight Prod.fst M = n}

private def oddColors (n : ℕ) : Set (Multiset Part) :=
  {M | (∀ x ∈ M, 1 ≤ x.2 ∧ x.2 ≤ x.1 ∧ (Even x.1 → ¬Even x.2)) ∧ weight Prod.fst M = n}

private def evenColors (n : ℕ) : Set (Multiset Part) :=
  {M | (∀ x ∈ M, 1 ≤ x.2 ∧ x.2 ≤ x.1 ∧ (Even x.1 → Even x.2)) ∧ weight Prod.fst M = n}

-- Each part has size and color at most `n`, and each multiplicity is at most `n`.
private lemma finite_colored (n : ℕ) :
    {M : Multiset Part | (∀ x ∈ M, Valid x) ∧ weight Prod.fst M = n}.Finite := by
  let U : Finset Part := Finset.Icc 1 n ×ˢ Finset.Icc 1 n
  refine ((n • U.val).powerset.toFinset.finite_toSet).subset ?_
  intro M hM
  apply Multiset.mem_toFinset.mpr (Multiset.mem_powerset.mpr (Multiset.le_iff_count.mpr ?_))
  have hcard : M.card ≤ n := by
    have h := Multiset.sum_map_le_sum_map (Function.const Part 1) Prod.fst
      (s := M) (fun x hx => (hM.1 x hx).1.trans (hM.1 x hx).2)
    simpa [Multiset.map_const, Multiset.sum_replicate, ← hM.2, weight] using h
  intro x
  by_cases hx : x ∈ M
  · obtain ⟨hj, hjm⟩ := hM.1 x hx
    have hm : x.1 ≤ n := hM.2 ▸ Multiset.le_sum_of_mem (Multiset.mem_map_of_mem Prod.fst hx)
    have hU : x ∈ U := Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hj.trans hjm, hm⟩, Finset.mem_Icc.mpr ⟨hj, hjm.trans hm⟩⟩
    rw [Multiset.count_nsmul, Multiset.count_eq_one_of_mem U.nodup (Finset.mem_def.mp hU), mul_one]
    exact (Multiset.count_le_card x M).trans hcard
  · rw [Multiset.count_eq_zero_of_notMem hx]
    exact Nat.zero_le _

private def expand (M : Multiset Primitive) : Multiset Part :=
  ((unpack M).map scaleEmbedding).val

private lemma expand_weight (M : Multiset Primitive) :
    weight Prod.fst (expand M) = weight (fun x => x.val.1) M := by
  conv_rhs => rw [← pack_unpack M]
  rw [weight_pack]
  rw [expand, weight, Finset.map_val, Multiset.map_map]
  rfl

private lemma distinct_eq_oddColors (n : ℕ) : (distinct n).ncard = (oddColors n).ncard := by
  classical
  symm
  have hex (M : Multiset Part) (hM : M ∈ oddColors n) :
      ∃ T : Multiset Primitive, T.map Subtype.val = M :=
    lift_parts _ M fun p hp =>
      let h := hM.1 p hp
      ⟨⟨p, ⟨h.1, h.2.1⟩, h.2.2⟩, rfl⟩
  choose lift hlift using hex
  have hs : (oddColors n).Finite := (finite_colored n).subset fun _ h =>
    ⟨fun p hp => ⟨(h.1 p hp).1, (h.1 p hp).2.1⟩, h.2⟩
  have ht : (distinct n).Finite := (finite_colored n).subset fun _ h => h.2
  rw [Set.ncard_eq_toFinset_card _ hs, Set.ncard_eq_toFinset_card _ ht]
  refine Finset.card_bij (fun M hM => expand (lift M (hs.mem_toFinset.mp hM))) ?_ ?_ ?_
  · intro M hM
    apply ht.mem_toFinset.mpr
    have hM := hs.mem_toFinset.mp hM
    refine ⟨(Finset.map scaleEmbedding (unpack (lift M hM))).nodup, ?_, ?_⟩
    · intro p hp
      obtain ⟨q, _, rfl⟩ := Finset.mem_map.mp (Finset.mem_def.mpr hp)
      exact scale_valid q
    · rw [expand_weight]
      have h := hM.2
      rw [← hlift M hM] at h
      simpa only [weight, Multiset.map_map, Function.comp_def] using h
  · intro M hM N hN h
    have hM := hs.mem_toFinset.mp hM
    have hN := hs.mem_toFinset.mp hN
    have eq := Finset.map_injective scaleEmbedding (Finset.val_injective h)
    have eq' := congrArg pack eq
    rw [pack_unpack, pack_unpack] at eq'
    exact (hlift M hM).symm.trans ((congrArg (Multiset.map Subtype.val) eq').trans (hlift N hN))
  · intro D hD
    have hD := ht.mem_toFinset.mp hD
    obtain ⟨T, hT⟩ := lift_parts scale D fun p hp => exists_scale p (hD.2.1 p hp)
    have hn : T.Nodup := (Multiset.nodup_map_iff_of_injective scale_injective).mp (hT ▸ hD.1)
    let s : Finset (Primitive × ℕ) := ⟨T, hn⟩
    have he : expand (pack s) = D := by
      simpa only [expand, unpack_pack, Finset.map_val, scaleEmbedding,
        Function.Embedding.coeFn_mk, s] using hT
    let M := (pack s).map Subtype.val
    have hM : M ∈ oddColors n := by
      refine ⟨fun p hp => ?_, ?_⟩
      · obtain ⟨q, _, rfl⟩ := Multiset.mem_map.mp hp
        exact ⟨q.property.1.1, q.property.1.2, q.property.2⟩
      · change weight Prod.fst ((pack s).map Subtype.val) = n
        simpa only [weight, Multiset.map_map, Function.comp_def] using
          (expand_weight (pack s)).symm.trans (he ▸ hD.2.2)
    refine ⟨M, hs.mem_toFinset.mpr hM, ?_⟩
    have e : lift M hM = pack s := Multiset.map_injective Subtype.val_injective (hlift M hM)
    exact (congrArg expand e).trans he

private def swapColor (x : Part) : Part :=
  (x.1, if Even x.1 then if Even x.2 then x.2 - 1 else x.2 + 1 else x.2)

private lemma swapColor_swapColor (x : Part) : swapColor (swapColor x) = x := by
  obtain ⟨m, j⟩ := x
  by_cases hm : Even m
  · by_cases hj : Even j
    · by_cases hj0 : j = 0
      · subst j
        simp [swapColor, hm]
      · have h : ¬Even (j - 1) := by simp only [Nat.even_iff] at hj ⊢; omega
        simp [swapColor, hm, hj, h, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0)]
    · have h : Even (j + 1) := by simp only [Nat.even_iff] at hj ⊢; omega
      simp [swapColor, hm, hj, h]
  · simp [swapColor, hm]

private lemma swapColor_valid (x : Part) (hx : Valid x) : Valid (swapColor x) := by
  obtain ⟨m, j⟩ := x
  obtain ⟨hj, hjm⟩ := hx
  change 1 ≤ j at hj
  change j ≤ m at hjm
  change 1 ≤ (swapColor (m, j)).2 ∧ (swapColor (m, j)).2 ≤ m
  simp only [swapColor]
  split_ifs <;> simp only [Nat.even_iff] at * <;> omega

private lemma swapColor_even (x : Part) (hx : Valid x) (hm : Even x.1) :
    Even (swapColor x).2 ↔ ¬Even x.2 := by
  rcases x with ⟨m, j⟩
  obtain ⟨hj, _⟩ := hx
  change 1 ≤ j at hj
  change Even m at hm
  simp only [swapColor, hm, ite_true]
  split_ifs <;> simp only [Nat.even_iff] at * <;> omega

private lemma weight_swapColor (M : Multiset Part) :
    weight Prod.fst (M.map swapColor) = weight Prod.fst M := by
  simp [weight, Multiset.map_map, Function.comp_def, swapColor]

private lemma oddColors_eq_evenColors (n : ℕ) : (oddColors n).ncard = (evenColors n).ncard := by
  refine Set.ncard_congr (fun M _ => M.map swapColor) ?_ ?_ ?_
  · intro M hM
    refine ⟨fun p hp => ?_, (weight_swapColor M).trans hM.2⟩
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hp
    obtain ⟨h₁, h₂, hparity⟩ := hM.1 x hx
    obtain ⟨h₃, h₄⟩ := swapColor_valid x ⟨h₁, h₂⟩
    exact ⟨h₃, h₄, fun hm => (swapColor_even x ⟨h₁, h₂⟩ hm).mpr (hparity hm)⟩
  · intro M N _ _ h
    exact Multiset.map_injective (Function.LeftInverse.injective swapColor_swapColor) h
  · intro M hM
    refine ⟨M.map swapColor, ⟨fun p hp => ?_, (weight_swapColor M).trans hM.2⟩, ?_⟩
    · obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hp
      obtain ⟨h₁, h₂, hparity⟩ := hM.1 x hx
      obtain ⟨h₃, h₄⟩ := swapColor_valid x ⟨h₁, h₂⟩
      exact ⟨h₃, h₄, fun hm he => (swapColor_even x ⟨h₁, h₂⟩ hm).mp he (hparity hm)⟩
    · simp only [Multiset.map_map, Function.comp_def, swapColor_swapColor, Multiset.map_id']

end coloredPartitions_differentParts_eq_restrictedColors

open coloredPartitions_differentParts_eq_restrictedColors

/-- **Colored partitions with different parts.** A colored part is a pair $(m, j)$ of integers
with $1 \le j \le m$, read as the part $m$ in color $j$, and a colored partition of $n$ is a
finite multiset of colored parts whose sizes $m$ sum to $n$. For every $n \ge 0$, the number of
colored partitions of $n$ in which no colored part is repeated equals the number of colored
partitions of $n$ in which no even part has an even color, and it also equals the number of
colored partitions of $n$ in which no even part has an odd color.

Source: Beimar J. Naranjo and José L. Ramírez, *On Colored Partitions and Euler-Type
Identities*, INTEGERS 26 (2026), Article A20, Corollary 4 (`integers-2026-A20-cor-4`). -/
public theorem coloredPartitions_differentParts_eq_restrictedColors (n : ℕ) :
    {M : Multiset (ℕ × ℕ) | M.Nodup ∧ (∀ x ∈ M, 1 ≤ x.2 ∧ x.2 ≤ x.1) ∧
        (M.map Prod.fst).sum = n}.ncard =
      {M : Multiset (ℕ × ℕ) | (∀ x ∈ M, 1 ≤ x.2 ∧ x.2 ≤ x.1 ∧ (Even x.1 → ¬ Even x.2)) ∧
        (M.map Prod.fst).sum = n}.ncard ∧
    {M : Multiset (ℕ × ℕ) | M.Nodup ∧ (∀ x ∈ M, 1 ≤ x.2 ∧ x.2 ≤ x.1) ∧
        (M.map Prod.fst).sum = n}.ncard =
      {M : Multiset (ℕ × ℕ) | (∀ x ∈ M, 1 ≤ x.2 ∧ x.2 ≤ x.1 ∧ (Even x.1 → Even x.2)) ∧
        (M.map Prod.fst).sum = n}.ncard := by
  have h := distinct_eq_oddColors n
  exact ⟨h, h.trans (oddColors_eq_evenColors n)⟩

end MetaMathlibExt
