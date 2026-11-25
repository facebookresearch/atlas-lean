/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fintype.BigOperators

/-!
# Constant-block partitions

The number of partitions into constant blocks with support an initial interval equals the
number of double compositions. Requiring distinct blocks restricts each color to a partition
into distinct parts.
-/

namespace MetaMathlibExt

open Multiset

namespace ConstantBlockPartitions

private def IsConstant (b : Multiset ℕ) : Prop :=
  ∃ x c : ℕ, 0 < c ∧ b = replicate c x

private def blockPartitions (distinct : Bool) (n : ℕ) : Set (Multiset (Multiset ℕ)) :=
  {P | (distinct = true → P.Nodup) ∧ (∀ b ∈ P, IsConstant b) ∧ P.join.card = n ∧
    ∃ k : ℕ, P.join.toFinset = Finset.Icc 1 k}

private def partitionColors (distinct : Bool) (m : ℕ) : Finset (Nat.Partition m) :=
  if distinct then Nat.Partition.distincts m else Finset.univ

private lemma mem_partitionColors {distinct : Bool} {m : ℕ} {p : Nat.Partition m} :
    p ∈ partitionColors distinct m ↔ (distinct = true → p.parts.Nodup) := by
  cases distinct <;> simp [partitionColors, Nat.Partition.distincts]

private abbrev ColoredComposition (distinct : Bool) (n : ℕ) :=
  Σ c : Composition n, (i : Fin c.length) → ↥(partitionColors distinct (c.blocksFun i))

private lemma replicate_eq_iff {m l x y : ℕ} (hm : 0 < m) :
    replicate m x = replicate l y ↔ m = l ∧ x = y := by
  constructor
  · intro h
    have hx : x ∈ replicate l y := h ▸ mem_replicate.mpr ⟨hm.ne', rfl⟩
    exact ⟨by simpa only [card_replicate] using congrArg Multiset.card h, eq_of_mem_replicate hx⟩
  · rintro ⟨rfl, rfl⟩
    rfl

-- Read the sizes of the blocks whose common value is x.
private def group (P : Multiset (Multiset ℕ)) (x : ℕ) : Multiset ℕ :=
  (P.filter (x ∈ ·)).map card

private lemma mem_group {P : Multiset (Multiset ℕ)} {x m : ℕ}
    (hP : ∀ b ∈ P, IsConstant b) : m ∈ group P x ↔ 0 < m ∧ replicate m x ∈ P := by
  constructor
  · intro hm
    obtain ⟨b, hb, rfl⟩ := mem_map.mp hm
    obtain ⟨hb, hx⟩ := mem_filter.mp hb
    obtain ⟨y, l, hl, rfl⟩ := hP b hb
    obtain rfl := eq_of_mem_replicate hx
    simpa only [card_replicate] using And.intro hl hb
  · rintro ⟨hm, hb⟩
    exact mem_map.mpr ⟨_, mem_filter.mpr ⟨hb, mem_replicate.mpr ⟨hm.ne', rfl⟩⟩,
      card_replicate _ _⟩

private lemma group_nodup {P : Multiset (Multiset ℕ)} (hP : P.Nodup)
    (hconst : ∀ b ∈ P, IsConstant b) (x : ℕ) : (group P x).Nodup := by
  refine (hP.filter _).map_on ?_
  intro a ha b hb heq
  obtain ⟨ha, hxa⟩ := mem_filter.mp ha
  obtain ⟨hb, hxb⟩ := mem_filter.mp hb
  obtain ⟨y, m, _, rfl⟩ := hconst a ha
  obtain ⟨z, l, _, rfl⟩ := hconst b hb
  obtain rfl := eq_of_mem_replicate hxa
  obtain rfl := eq_of_mem_replicate hxb
  simp only [card_replicate] at heq
  rw [heq]

-- At position i, rebuild each block using the common value i + 1.
private def gather {k : ℕ} (sizes : Fin k → Multiset ℕ) : Multiset (Multiset ℕ) :=
  (↑(List.finRange k) : Multiset (Fin k)).bind fun i =>
    (sizes i).map fun m => replicate m (i.val + 1)

private lemma mem_gather {k : ℕ} {sizes : Fin k → Multiset ℕ} {b : Multiset ℕ} :
    b ∈ gather sizes ↔ ∃ i, ∃ m ∈ sizes i, replicate m (i.val + 1) = b := by
  simp [gather]

private lemma gather_constant {k : ℕ} {sizes : Fin k → Multiset ℕ}
    (hpos : ∀ i m, m ∈ sizes i → 0 < m) : ∀ b ∈ gather sizes, IsConstant b := by
  intro b hb
  obtain ⟨i, m, hm, rfl⟩ := mem_gather.mp hb
  exact ⟨_, _, hpos i m hm, rfl⟩

private lemma gather_nodup {k : ℕ} {sizes : Fin k → Multiset ℕ}
    (hpos : ∀ i m, m ∈ sizes i → 0 < m) (hnd : ∀ i, (sizes i).Nodup) :
    (gather sizes).Nodup := by
  unfold gather
  refine nodup_bind.mpr ⟨fun i _ => (hnd i).map ?_, ?_⟩
  · intro a b h
    simpa only [card_replicate] using congrArg card h
  · refine ⟨_, rfl, (List.nodup_finRange k).imp ?_⟩
    intro i j hij
    apply Multiset.disjoint_left.mpr
    intro b hi hj
    obtain ⟨m, hm, rfl⟩ := mem_map.mp hi
    obtain ⟨l, _, heq⟩ := mem_map.mp hj
    have h := ((replicate_eq_iff (hpos i m hm)).mp heq.symm).2
    exact hij (Fin.ext (Nat.add_right_cancel h))

private lemma card_join_gather {k : ℕ} (sizes : Fin k → Multiset ℕ) :
    (gather sizes).join.card = (List.ofFn fun i => (sizes i).sum).sum := by
  simp only [gather, card_join, map_bind, sum_bind, map_map, Function.comp_apply,
    card_replicate, map_id', map_coe, sum_coe, List.ofFn_eq_map]

private lemma support_gather {k : ℕ} {sizes : Fin k → Multiset ℕ}
    (hpos : ∀ i m, m ∈ sizes i → 0 < m) (hne : ∀ i, sizes i ≠ 0) :
    (gather sizes).join.toFinset = Finset.Icc 1 k := by
  ext x
  rw [mem_toFinset, mem_join, Finset.mem_Icc]
  constructor
  · rintro ⟨b, hb, hx⟩
    obtain ⟨i, m, _, rfl⟩ := mem_gather.mp hb
    obtain rfl := eq_of_mem_replicate hx
    have := i.isLt
    omega
  · intro hx
    let i : Fin k := ⟨x - 1, by omega⟩
    have hi : i.val + 1 = x := by dsimp [i]; omega
    obtain ⟨m, hm⟩ := Multiset.exists_mem_of_ne_zero (hne i)
    exact ⟨_, mem_gather.mpr ⟨i, m, hm, rfl⟩, mem_replicate.mpr ⟨(hpos i m hm).ne', hi.symm⟩⟩

private lemma bind_finRange_eq_single {α : Type*} {k : ℕ} (i : Fin k) (f : Fin k → Multiset α) :
    (↑(List.finRange k) : Multiset (Fin k)).bind (fun j => if j = i then f j else 0) = f i := by
  rw [← bind_filter, Multiset.filter_eq', coe_count, List.count_finRange]
  simp

-- Filtering by a value selects exactly one group, keeping all its multiplicities.
private lemma group_gather {k : ℕ} {sizes : Fin k → Multiset ℕ}
    (hpos : ∀ i m, m ∈ sizes i → 0 < m) (i : Fin k) :
    group (gather sizes) (i.val + 1) = sizes i := by
  simp only [group, gather, filter_bind, map_bind, filter_map, map_map, Function.comp_def,
    card_replicate, map_id']
  rw [← bind_finRange_eq_single i sizes]
  apply Multiset.bind_congr
  intro j _
  by_cases h : j = i
  · subst j
    rw [ite_eq_left rfl, filter_eq_self]
    exact fun m hm => mem_replicate.mpr ⟨(hpos i m hm).ne', rfl⟩
  · rw [ite_eq_right h, filter_eq_nil]
    intro m _ hm
    exact h (Fin.ext (Nat.add_right_cancel (eq_of_mem_replicate hm).symm))

-- Interchange the bind over indices with the bind over blocks. Each occurrence of a block
-- lands at exactly one index, where taking its size and replicating recovers that block.
private lemma gather_group {P : Multiset (Multiset ℕ)} {k : ℕ}
    (hconst : ∀ b ∈ P, IsConstant b) (hsupp : P.join.toFinset = Finset.Icc 1 k) :
    gather (fun i : Fin k => group P (i.val + 1)) = P := by
  simp only [gather, group, map_map, Function.comp_def]
  simp_rw [← bind_singleton, bind_filter]
  rw [bind_bind]
  calc
    _ = P.bind (fun b => {b}) := by
      apply Multiset.bind_congr
      intro b hb
      obtain ⟨x, m, hm, rfl⟩ := hconst b hb
      have hx : x ∈ P.join.toFinset :=
        mem_toFinset.mpr (mem_join.mpr ⟨_, hb, mem_replicate.mpr ⟨hm.ne', rfl⟩⟩)
      rw [hsupp, Finset.mem_Icc] at hx
      let i : Fin k := ⟨x - 1, by omega⟩
      have hi : i.val + 1 = x := by dsimp [i]; omega
      rw [← bind_finRange_eq_single i (fun _ => {replicate m x})]
      apply Multiset.bind_congr
      intro j _
      have hmem : j.val + 1 ∈ replicate m x ↔ j = i := by
        rw [mem_replicate, and_iff_right hm.ne', ← hi]
        exact ⟨fun h => Fin.ext (Nat.add_right_cancel h), fun h => congrArg (·.val + 1) h⟩
      simp only [hmem, card_replicate]
      split_ifs with h
      · rw [h, hi]
      · rfl
    _ = P := by rw [bind_singleton, map_id']

private variable {distinct : Bool} {n : ℕ}

private def parts (c : ColoredComposition distinct n) (i : Fin c.1.length) : Multiset ℕ :=
  (c.2 i).1.parts

private lemma parts_pos (c : ColoredComposition distinct n) (i : Fin c.1.length)
    (m : ℕ) (hm : m ∈ parts c i) : 0 < m :=
  (c.2 i).1.parts_pos hm

private lemma parts_sum (c : ColoredComposition distinct n) (i : Fin c.1.length) :
    (parts c i).sum = c.1.blocksFun i :=
  (c.2 i).1.parts_sum

private lemma parts_ne_zero (c : ColoredComposition distinct n) (i : Fin c.1.length) :
    parts c i ≠ 0 := by
  intro hi
  have h := parts_sum c i
  rw [hi, sum_zero] at h
  exact (c.1.blocks_pos (c.1.blocksFun_mem_blocks i)).ne' h.symm

private def assemble (c : ColoredComposition distinct n) : blockPartitions distinct n :=
  ⟨gather (parts c), by
    refine ⟨fun h => gather_nodup (parts_pos c) (fun i => (mem_partitionColors.mp (c.2 i).2) h),
      gather_constant (parts_pos c), ?_, c.1.length, support_gather (parts_pos c) (parts_ne_zero c)⟩
    rw [card_join_gather]
    simp only [parts_sum, Composition.ofFn_blocksFun, Composition.blocks_sum]⟩

private lemma assemble_injective : Function.Injective (@assemble distinct n) := by
  rintro ⟨c, f⟩ ⟨d, g⟩ h
  have hP : gather (parts ⟨c, f⟩) = gather (parts ⟨d, g⟩) := congrArg Subtype.val h
  have hsupp : Finset.Icc 1 c.length = Finset.Icc 1 d.length := by
    rw [← support_gather (parts_pos ⟨c, f⟩) (parts_ne_zero ⟨c, f⟩),
      hP, support_gather (parts_pos ⟨d, g⟩) (parts_ne_zero ⟨d, g⟩)]
  have hlen : c.length = d.length := by
    simpa using congrArg Finset.card hsupp
  have hparts (i : Fin c.length) (j : Fin d.length) (hij : i.val = j.val) :
      parts ⟨c, f⟩ i = parts ⟨d, g⟩ j := by
    rw [← group_gather (parts_pos ⟨c, f⟩) i, ← group_gather (parts_pos ⟨d, g⟩) j, hP, hij]
  have hcd : c = d := by
    apply Composition.ext
    refine List.ext_getElem hlen fun i hi hj => ?_
    exact ((parts_sum ⟨c, f⟩ ⟨i, hi⟩).symm.trans
      (congrArg Multiset.sum (hparts ⟨i, hi⟩ ⟨i, hj⟩ rfl))).trans (parts_sum ⟨d, g⟩ ⟨i, hj⟩)
  subst d
  have hfg : f = g := funext fun i => Subtype.ext (Nat.Partition.ext (hparts i i rfl))
  cases hfg
  rfl

private lemma assemble_surjective : Function.Surjective (@assemble distinct n) := by
  rintro ⟨P, hnd, hconst, hcard, k, hsupp⟩
  let sizes (x : ℕ) := group P (x + 1)
  have hsum (i : Fin k) : 0 < (sizes i.val).sum := by
    have hx : i.val + 1 ∈ P.join := by
      rw [← mem_toFinset, hsupp, Finset.mem_Icc]
      have := i.isLt
      omega
    obtain ⟨b, hb, hx⟩ := mem_join.mp hx
    obtain ⟨x, m, hm, rfl⟩ := hconst b hb
    have heq := eq_of_mem_replicate hx
    have hmem : m ∈ sizes i.val :=
      (mem_group hconst).mpr ⟨hm, by simpa only [heq] using hb⟩
    exact hm.trans_le (le_sum_of_mem hmem)
  let c : Composition n :=
    ⟨List.ofFn fun i : Fin k => (sizes i.val).sum,
      fun hm => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hm
        exact hsum i,
      by rw [← card_join_gather, gather_group hconst hsupp, hcard]⟩
  have hlen : c.length = k := List.length_ofFn
  have hsize (i : Fin c.length) : (sizes i.val).sum = c.blocksFun i := by
    change (sizes i.val).sum = (List.ofFn fun j : Fin k => (sizes j.val).sum)[i.val]'i.isLt
    rw [List.getElem_ofFn]
  let f (i : Fin c.length) : ↥(partitionColors distinct (c.blocksFun i)) :=
    ⟨⟨sizes i.val, fun hm => ((mem_group hconst).mp hm).1, hsize i⟩,
      mem_partitionColors.mpr fun h => group_nodup (hnd h) hconst _⟩
  refine ⟨⟨c, f⟩, Subtype.ext ?_⟩
  change gather (fun i : Fin c.length => sizes i.val) = P
  exact gather_group hconst (by rw [hlen]; exact hsupp)

private lemma ncard_blockPartitions (distinct : Bool) (n : ℕ) :
    (blockPartitions distinct n).ncard =
      ∑ c : Composition n, (c.blocks.map fun m => (partitionColors distinct m).card).prod := by
  let e := Equiv.ofBijective (assemble (distinct := distinct) (n := n))
    ⟨assemble_injective, assemble_surjective⟩
  change Nat.card (blockPartitions distinct n) = _
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Fintype.card_pi]
  calc
    _ = ∏ i : Fin c.length, (partitionColors distinct (c.blocksFun i)).card :=
      Finset.prod_congr rfl fun i _ => Fintype.card_coe _
    _ = _ := by
      rw [← List.prod_ofFn]
      congr 1
      exact List.ofFn_getElem_eq_map c.blocks fun m => (partitionColors distinct m).card

end ConstantBlockPartitions

open ConstantBlockPartitions

/-- **Distinct constant-block partitions and colored compositions.** For $n \ge 0$, count the
pairs $(A, P)$ where $A$ is a multiset of $n$ positive integers whose distinct elements are
exactly $1, \dots, k$ for some $k \ge 0$, and $P$ is a partition of $A$ into pairwise distinct
constant blocks, that is, a multiset of pairwise distinct nonempty multisets, each with all its
elements equal, whose sum is $A$. The number of such pairs equals the number of compositions of
$n$ in which each summand $m$ is colored by a partition of $m$ into distinct parts:
$$\sum_{(c_1, \dots, c_r)} q(c_1) \cdots q(c_r),$$
where the sum runs over all compositions $(c_1, \dots, c_r)$ of $n$ and $q(m)$ is the number of
partitions of $m$ into distinct parts.

Source: Beimar J. Naranjo and José L. Ramírez, *On Colored Partitions and Euler-Type
Identities*, INTEGERS 26 (2026), Article A20, Corollary 1 (`integers-2026-A20-cor-1`). -/
public theorem ncard_distinctConstantBlockPartitions_eq_coloredCompositions (n : ℕ) :
    {P : Multiset (Multiset ℕ) |
        P.Nodup ∧ (∀ b ∈ P, ∃ x c : ℕ, 0 < c ∧ b = Multiset.replicate c x) ∧
          P.join.card = n ∧ ∃ k : ℕ, P.join.toFinset = Finset.Icc 1 k}.ncard =
      ∑ c : Composition n, (c.blocks.map fun m => (Nat.Partition.distincts m).card).prod := by
  simpa [blockPartitions, IsConstant, partitionColors] using ncard_blockPartitions true n

/-- **Constant-block partitions and double compositions.** For $n \ge 0$, count the pairs
$(A, P)$ where $A$ is a multiset of $n$ positive integers whose distinct elements are exactly
$1, \dots, k$ for some $k \ge 0$, and $P$ is a partition of $A$ into constant blocks, that is,
a multiset of nonempty multisets, each with all its elements equal, whose sum is $A$. The number
of such pairs equals the number $d_c(n)$ of double compositions of $n$, that is, compositions of
$n$ in which each summand $m$ is colored by a partition of $m$:
$$d_c(n) = \sum_{(c_1, \dots, c_r)} p(c_1) \cdots p(c_r),$$
where the sum runs over all compositions $(c_1, \dots, c_r)$ of $n$ and $p(m)$ is the number of
partitions of $m$.

Source: Beimar J. Naranjo and José L. Ramírez, *On Colored Partitions and Euler-Type
Identities*, INTEGERS 26 (2026), Article A20, Theorem 4 (`integers-2026-A20-thm-4`). -/
public theorem ncard_constantBlockPartitions_eq_doubleCompositions (n : ℕ) :
    {P : Multiset (Multiset ℕ) |
        (∀ b ∈ P, ∃ x c : ℕ, 0 < c ∧ b = Multiset.replicate c x) ∧ P.join.card = n ∧
          ∃ k : ℕ, P.join.toFinset = Finset.Icc 1 k}.ncard =
      ∑ c : Composition n, (c.blocks.map fun m => Fintype.card (Nat.Partition m)).prod := by
  simpa [blockPartitions, IsConstant, partitionColors] using ncard_blockPartitions false n

end MetaMathlibExt
