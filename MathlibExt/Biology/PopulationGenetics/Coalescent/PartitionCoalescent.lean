/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Normed.Algebra.MatrixExponentialIntertwining
public import MathlibExt.Biology.PopulationGenetics.Coalescent.BlockCounting
public import MathlibExt.Combinatorics.Finpartition.Comap
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.LinearAlgebra.Matrix.Stochastic

/-!
# Kingman's coalescent as a partition-valued process

Kingman's `n`-coalescent is a continuous-time Markov chain on the set partitions of the sample
`{0, …, n - 1}` (here `Fin n`; a partition is a `Finpartition` of `Finset.univ`). While the
partition has `k` blocks, each of the `k.choose 2` pairs of blocks merges at rate `1` (time in
units of `2N` generations), so the number of blocks is the block-counting process of
`BlockCounting.lean`. Its **jump chain** merges a uniformly random pair of blocks at each
step. We encode "`π'` arises from `π` by merging two blocks" as `IsMerge π π'`: `π` refines
`π'` and has exactly one more block; there are `(#π.parts).choose 2` such `π'`
(`card_isMerge`), one per pair of blocks.

* `jumpMatrix n` is the transition matrix of the jump chain (uniform over the
  `(#π.parts).choose 2` mergers; a partition with at most one block is absorbing) and
  `jumpLaw n m π` is the probability that the chain started from the partition into
  singletons is at `π` after `m` jumps.
* `partitionRate n` is the rate matrix of the continuous-time chain and
  `timeLaw n t π = exp (t • partitionRate n) ⊥ π` the probability that the coalescent of a
  sample of `n` started from singletons is at `π` at time `t ≥ 0`.

The processes are given by their transition matrices on the finite type of set partitions; no
path space is constructed. Relabeling the sample by a permutation `σ` is `π.comap σ`, and
restricting a partition of `Fin (n + 1)` to the first `n` genes is `π.comap Fin.castSucc`
(`Finpartition.comap`).

**Kingman's formula** (Kingman 1982): for `m < n`, the partition reached after `m = n - k`
jumps has law `P(π) = (n - k)! k! (k - 1)! / (n! (n - 1)!) · ∏_{B ∈ π} |B|!` on the partitions
with `k` blocks (`kingmanProb`). The proof is by induction on `m` from the splitting identity
`2 ∑_{π ↦ π'} ∏_{B ∈ π} |B|! = (n - #π') ∏_{B ∈ π'} |B|!` over the partitions `π` that merge to
`π'`. The law is exchangeable: invariant under relabeling the sample. At time `t` the law
factorizes as `P(Π_t = π) = P(N_t = k) · P(π)`, where `P(N_t = k)` is the block-counting
transition probability `exp (t • blockCountingGenerator n) n k` (Tavaré's formula); the proof
shows that Kingman's formula intertwines the two rate matrices and passes the intertwining to
the matrix exponentials (`Matrix.exp_mul_eq_mul_exp_of_mul_eq`). Restricting the sample of
`n + 1` to its first `n` genes maps the time-`t` law of the `(n + 1)`-coalescent to that of the
`n`-coalescent (Kingman's consistency), by the same argument applied to the restriction map.

The consistency of the jump chains themselves (as laws of the sequences of distinct
restricted partitions) is stated, not proved, in
`WantedExt/Biology/PopulationGenetics/Coalescent/PartitionCoalescentWanted.lean`.

## Main results

* `card_isMerge`: a partition with `k` blocks has `k.choose 2` one-step mergers.
* `jumpMatrix_mem_rowStochastic`, `sum_jumpLaw`: the jump chain is a Markov chain.
* `two_mul_sum_prod_factorial_isMerge`: the splitting identity.
* `jumpLaw_eq`: **Kingman's formula** for the jump chain; `sum_kingmanProb`: it is a
  probability distribution on the partitions with `k` blocks.
* `jumpLaw_comap_perm`, `timeLaw_comap_perm`: exchangeability.
* `blockCountingGenerator_mul_kingmanMatrix`, `timeLaw_eq`, `timeLaw_eq_tavareProb`: the time-`t`
  marginal is the block-counting probability times Kingman's formula; `sum_timeLaw`.
* `partitionRate_mul_restrictMatrix`, `sum_timeLaw_restrict`: consistency of the time-`t`
  marginals under restriction.

## References

* J. F. C. Kingman, "The coalescent", Stochastic Process. Appl. 13 (1982) 235–248.
* R. Durrett, *Probability Models for DNA Sequence Evolution*, 2nd ed. (2008), ch. 1.
* S. Tavaré, "Line-of-descent and genealogical processes, and their applications in population
  genetics models", Theor. Popul. Biol. 26 (1984) 119–164.
-/

@[expose] public section

open Finset Matrix

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.PartitionCoalescent

open KingmanBlockCounting

/-- The set partitions of a sample of `n` labeled genes `{0, …, n - 1}`. -/
abbrev SamplePartition (n : ℕ) : Type := Finpartition (univ : Finset (Fin n))

variable {n : ℕ}

/-- `π'` arises from `π` by merging two blocks: `π` refines `π'` and has exactly one more
block (so exactly two blocks of `π` lie in one block of `π'`, and the others are blocks of
`π'`). -/
def IsMerge (π π' : SamplePartition n) : Prop :=
  π ≤ π' ∧ #π'.parts + 1 = #π.parts

open scoped Classical in
/-- The transition matrix of the jump chain of Kingman's coalescent: from a partition with
`k ≥ 2` blocks, move to each of the `k.choose 2` partitions obtained by merging two blocks with
probability `1 / k.choose 2`; a partition with at most one block is absorbing. -/
noncomputable def jumpMatrix (n : ℕ) : Matrix (SamplePartition n) (SamplePartition n) ℝ :=
  Matrix.of fun π π' =>
    if 2 ≤ #π.parts then (if IsMerge π π' then (((#π.parts).choose 2 : ℕ) : ℝ)⁻¹ else 0)
    else if π = π' then 1 else 0

/-- The law of the jump chain after `m` jumps, started from the partition into singletons:
`jumpLaw n m π` is the probability that the partition after `m` coalescences is `π`. -/
noncomputable def jumpLaw (n m : ℕ) (π : SamplePartition n) : ℝ :=
  (jumpMatrix n ^ m) ⊥ π

/-- **Kingman's formula**: the probability `(n - k)! k! (k - 1)! ∏_{B ∈ π} |B|! / (n! (n - 1)!)`
of a partition `π` with `k` blocks of a sample of size `n` (meaningful for `1 ≤ k ≤ n`; for
the empty sample it gives `1` to the empty partition). -/
noncomputable def kingmanProb (n : ℕ) (π : SamplePartition n) : ℝ :=
  (((n - #π.parts).factorial * (#π.parts).factorial * (#π.parts - 1).factorial *
      π.cardProd Nat.factorial : ℕ) : ℝ) /
    ((n.factorial * (n - 1).factorial : ℕ) : ℝ)

open scoped Classical in
/-- The rate matrix of Kingman's partition-valued coalescent: each pair of blocks merges at
rate `1`, so a partition with `k` blocks is left at total rate `k.choose 2` (time in units of
`2N` generations). -/
noncomputable def partitionRate (n : ℕ) : Matrix (SamplePartition n) (SamplePartition n) ℝ :=
  Matrix.of fun π π' =>
    if IsMerge π π' then 1 else if π = π' then -(((#π.parts).choose 2 : ℕ) : ℝ) else 0

/-- The time-`t` marginal of Kingman's `n`-coalescent started from singletons:
`timeLaw n t π = exp (t • partitionRate n) ⊥ π` is the probability that the ancestral partition
of the sample at time `t ≥ 0` (in units of `2N` generations) is `π`. The matrix exponential is
defined for every real `t`; the identities below hold for every real `t`. -/
noncomputable def timeLaw (n : ℕ) (t : ℝ) (π : SamplePartition n) : ℝ :=
  NormedSpace.exp (t • partitionRate n) ⊥ π

/-! ### Restriction -/

open scoped Classical in
/-- The restriction map as a `0/1` matrix: entry `(π, ρ)` is `1` iff `π.comap Fin.castSucc = ρ`. -/
noncomputable def restrictMatrix (n : ℕ) :
    Matrix (SamplePartition (n + 1)) (SamplePartition n) ℝ :=
  Matrix.of fun π ρ => if π.comap Fin.castSucc = ρ then 1 else 0

/-! ### Combinatorics of mergers -/

/-- Merge the blocks in `s ⊆ π.parts` (nonempty) into one block. -/
private def mergeOf (π : SamplePartition n) (s : Finset (Finset (Fin n))) (hs : s ⊆ π.parts)
    (hne : s.Nonempty) : SamplePartition n where
  parts := insert (s.sup id) (π.parts \ s)
  supIndep := by
    rw [Finset.supIndep_iff_pairwiseDisjoint, coe_insert]
    refine (π.disjoint.subset (by simp)).insert ?_
    intro C hC _
    simp only [mem_coe, mem_sdiff] at hC
    rw [id, id, Finset.disjoint_sup_left]
    intro A hA
    exact π.disjoint (hs hA) hC.1 (fun h => hC.2 (h ▸ hA))
  sup_parts := by
    rw [sup_insert, id, ← Finset.sup_union, union_sdiff_of_subset hs, π.sup_parts]
  bot_notMem := by
    intro h
    rcases mem_insert.1 h with h | h
    · obtain ⟨A, hA⟩ := hne
      have hle : A ≤ s.sup id := le_sup (f := id) hA
      rw [← h] at hle
      exact π.ne_bot (hs hA) (le_bot_iff.1 hle)
    · exact π.bot_notMem (mem_sdiff.1 h).1

private theorem parts_mergeOf (π : SamplePartition n) (s : Finset (Finset (Fin n)))
    (hs : s ⊆ π.parts)
    (hne : s.Nonempty) : (mergeOf π s hs hne).parts = insert (s.sup id) (π.parts \ s) := rfl

/-- If `s` has at least two blocks, its union is not a block of `π`. -/
private theorem sup_notMem_parts (π : SamplePartition n) {s : Finset (Finset (Fin n))}
    (hs : s ⊆ π.parts) (h2 : 2 ≤ #s) : s.sup id ∉ π.parts := by
  intro hmem
  obtain ⟨A, hA, B, hB, hAB⟩ := one_lt_card.1 h2
  have hAle : A ≤ s.sup id := le_sup (f := id) hA
  have hBle : B ≤ s.sup id := le_sup (f := id) hB
  -- A ⊆ sup and A, sup ∈ parts, A nonempty ⇒ A = sup; same for B
  have eA : A = s.sup id := by
    obtain ⟨x, hx⟩ := π.nonempty_of_mem_parts (hs hA)
    exact π.eq_of_mem_parts (hs hA) hmem hx (hAle hx)
  have eB : B = s.sup id := by
    obtain ⟨x, hx⟩ := π.nonempty_of_mem_parts (hs hB)
    exact π.eq_of_mem_parts (hs hB) hmem hx (hBle hx)
  exact hAB (eA.trans eB.symm)

private theorem isMerge_mergeOf (π : SamplePartition n) {s : Finset (Finset (Fin n))}
    (hs : s ⊆ π.parts) (h2 : #s = 2) :
    IsMerge π (mergeOf π s hs (card_pos.1 (by omega))) := by
  refine ⟨fun B hB => ?_, ?_⟩
  · by_cases hBs : B ∈ s
    · exact ⟨s.sup id, mem_insert_self _ _, le_sup (f := id) hBs⟩
    · exact ⟨B, mem_insert_of_mem (mem_sdiff.2 ⟨hB, hBs⟩), le_rfl⟩
  · rw [parts_mergeOf, card_insert_of_notMem (fun h => sup_notMem_parts π hs (by omega)
      (mem_sdiff.1 h).1), card_sdiff_of_subset hs, h2]
    have : 2 ≤ #π.parts := h2 ▸ card_le_card hs
    omega

private theorem inter_parts_mergeOf (π : SamplePartition n) {s : Finset (Finset (Fin n))}
    (hs : s ⊆ π.parts) (h2 : 2 ≤ #s) (hne : s.Nonempty) :
    π.parts ∩ (mergeOf π s hs hne).parts = π.parts \ s := by
  ext B
  simp only [mem_inter, parts_mergeOf, mem_insert, mem_sdiff]
  constructor
  · rintro ⟨hB, h | h⟩
    · exact absurd (h ▸ hB) (sup_notMem_parts π hs h2)
    · exact h
  · rintro ⟨hB, hBs⟩
    exact ⟨hB, Or.inr ⟨hB, hBs⟩⟩

open scoped Classical in
private theorem exists_mergeOf_eq {π π' : SamplePartition n} (h : IsMerge π π') :
    ∃ s, ∃ hs : s ⊆ π.parts, ∃ h2 : #s = 2,
      mergeOf π s hs (card_pos.1 (by omega)) = π' := by
  set P := π.parts
  let f : Finset (Fin n) → Finset (Fin n) := fun B =>
    if hB : B.Nonempty then π'.part hB.choose else ∅
  have hf : ∀ B ∈ P, f B ∈ π'.parts ∧ B ⊆ f B := by
    intro B hB
    have hne := π.nonempty_of_mem_parts hB
    obtain ⟨C, hC, hBC⟩ := h.1 hB
    have : f B = C := by
      simp only [f, dite_eq_left hne]
      exact π'.part_eq_of_mem hC (hBC hne.choose_spec)
    rw [this]
    exact ⟨hC, hBC⟩
  have huniq : ∀ B ∈ P, ∀ C ∈ π'.parts, B ⊆ C → C = f B := by
    intro B hB C hC hBC
    obtain ⟨x, hx⟩ := π.nonempty_of_mem_parts hB
    exact π'.eq_of_mem_parts hC (hf B hB).1 (hBC hx) ((hf B hB).2 hx)
  let fib : Finset (Fin n) → Finset (Finset (Fin n)) := fun C => P.filter (f · = C)
  have hsum : #P = ∑ C ∈ π'.parts, #(fib C) :=
    card_eq_sum_card_fiberwise fun B hB => (hf B hB).1
  have hfib_pos : ∀ C ∈ π'.parts, 1 ≤ #(fib C) := by
    intro C hC
    obtain ⟨B, hB, hBC⟩ := Finpartition.exists_le_of_le h.1 hC
    exact card_pos.2 ⟨B, mem_filter.2 ⟨hB, (huniq B hB C hC hBC).symm⟩⟩
  have hsup : ∀ C ∈ π'.parts, (fib C).sup id = C := by
    intro C hC
    apply le_antisymm
    · refine Finset.sup_le fun B hB => ?_
      have hB' := mem_filter.1 hB
      simpa [hB'.2] using (hf B hB'.1).2
    · intro x hx
      have hxP : π.part x ∈ P := π.part_mem.2 (mem_univ x)
      have hxB : x ∈ π.part x := π.mem_part_self.2 (mem_univ x)
      have hfx : f (π.part x) = C :=
        (π'.eq_of_mem_parts hC (hf _ hxP).1 hx ((hf _ hxP).2 hxB)).symm
      exact mem_sup.2 ⟨π.part x, mem_filter.2 ⟨hxP, hfx⟩, hxB⟩
  -- the fiber sizes sum to `#π'.parts + 1`
  have htot : ∑ C ∈ π'.parts, #(fib C) = ∑ C ∈ π'.parts, 1 + 1 := by
    rw [← hsum, sum_const, smul_eq_mul, mul_one, h.2]
  obtain ⟨C₀, hC₀, hC₀2⟩ : ∃ C₀ ∈ π'.parts, 2 ≤ #(fib C₀) := by
    by_contra hcon
    push Not at hcon
    have : ∑ C ∈ π'.parts, #(fib C) ≤ ∑ C ∈ π'.parts, 1 :=
      sum_le_sum fun C hC => by have := hcon C hC; omega
    omega
  have hsplit := add_sum_erase π'.parts (fun C => #(fib C)) hC₀
  have hsplit1 := add_sum_erase π'.parts (fun _ => 1) hC₀
  have hrest : ∑ C ∈ π'.parts.erase C₀, 1 ≤ ∑ C ∈ π'.parts.erase C₀, #(fib C) :=
    sum_le_sum fun C hC => hfib_pos C (mem_of_mem_erase hC)
  have hC₀eq : #(fib C₀) = 2 := by omega
  have hone : ∀ C ∈ π'.parts, C ≠ C₀ → #(fib C) = 1 := by
    intro C hC hne
    have hle := hfib_pos C hC
    by_contra hcon
    have h2 : 2 ≤ #(fib C) := by omega
    have := add_sum_erase (π'.parts.erase C₀) (fun C => #(fib C)) (mem_erase.2 ⟨hne, hC⟩)
    have := add_sum_erase (π'.parts.erase C₀) (fun _ => 1) (mem_erase.2 ⟨hne, hC⟩)
    have : ∑ C ∈ (π'.parts.erase C₀).erase C, 1 ≤
        ∑ C ∈ (π'.parts.erase C₀).erase C, #(fib C) :=
      sum_le_sum fun D hD => hfib_pos D (mem_of_mem_erase (mem_of_mem_erase hD))
    omega
  -- a singleton fiber is a block of both partitions
  have hsingle : ∀ C ∈ π'.parts, C ≠ C₀ → C ∈ P ∧ f C = C := by
    intro C hC hne
    obtain ⟨B, hB⟩ := card_eq_one.1 (hone C hC hne)
    have hBC : B = C := by
      have := hsup C hC
      rw [hB, sup_singleton, id] at this
      exact this
    have hBm : B ∈ fib C := by rw [hB]; exact mem_singleton_self B
    have hBm' := mem_filter.1 hBm
    rw [hBC] at hBm'
    exact hBm'
  refine ⟨fib C₀, filter_subset _ _, hC₀eq, Finpartition.ext ?_⟩
  rw [parts_mergeOf, hsup C₀ hC₀]
  ext X
  simp only [mem_insert, mem_sdiff]
  constructor
  · rintro (rfl | ⟨hX, hXs⟩)
    · exact hC₀
    · have hfX : f X ≠ C₀ := fun he => hXs (mem_filter.2 ⟨hX, he⟩)
      obtain ⟨hfXP, hffX⟩ := hsingle (f X) (hf X hX).1 hfX
      have : X = f X := by
        obtain ⟨x, hx⟩ := π.nonempty_of_mem_parts hX
        exact π.eq_of_mem_parts hX hfXP hx ((hf X hX).2 hx)
      rw [this]
      exact (hf X hX).1
  · intro hX
    by_cases hXC : X = C₀
    · exact Or.inl hXC
    · obtain ⟨hXP, hfX⟩ := hsingle X hX hXC
      refine Or.inr ⟨hXP, fun hm => hXC ?_⟩
      have := (mem_filter.1 hm).2
      rw [hfX] at this
      exact this

open scoped Classical in
/-- **Mergers.** A partition with `k` blocks has exactly `k.choose 2` partitions that arise
from it by merging two blocks. -/
theorem card_isMerge (π : SamplePartition n) :
    #{π' | IsMerge π π'} = (#π.parts).choose 2 := by
  rw [← card_powersetCard 2 π.parts]
  symm
  refine card_bij (fun s hs => mergeOf π s (mem_powersetCard.1 hs).1
      (card_pos.1 (by rw [(mem_powersetCard.1 hs).2]; omega))) (fun s hs => ?_) ?_ ?_
  · exact mem_filter.2 ⟨mem_univ _, isMerge_mergeOf π _ (mem_powersetCard.1 hs).2⟩
  · intro s hs t ht hst
    have hs' := mem_powersetCard.1 hs
    have ht' := mem_powersetCard.1 ht
    have e := congrArg (fun ρ : SamplePartition n => π.parts ∩ ρ.parts) hst
    rw [inter_parts_mergeOf π hs'.1 (by omega), inter_parts_mergeOf π ht'.1 (by omega)] at e
    rw [← Finset.sdiff_sdiff_eq_self hs'.1, ← Finset.sdiff_sdiff_eq_self ht'.1, e]
  · intro π' hπ'
    obtain ⟨s, hs, h2, he⟩ := exists_mergeOf_eq (mem_filter.1 hπ').2
    exact ⟨s, mem_powersetCard.2 ⟨hs, h2⟩, he⟩

open scoped Classical in
/-- `mergeOf` extended by `π` outside its domain. -/
private noncomputable def mergeOf' (π : SamplePartition n) (s : Finset (Finset (Fin n))) :
    SamplePartition n :=
  if h : s ⊆ π.parts ∧ s.Nonempty then mergeOf π s h.1 h.2 else π

open scoped Classical in
/-- Mergers of `π` with a property `Q` correspond to pairs of blocks whose merger has `Q`. -/
private theorem card_filter_isMerge (π : SamplePartition n) (Q : SamplePartition n → Prop) :
    #{π' | IsMerge π π' ∧ Q π'} = #{s ∈ π.parts.powersetCard 2 | Q (mergeOf' π s)} := by
  have hm : ∀ s ∈ π.parts.powersetCard 2, ∃ h : s ⊆ π.parts ∧ s.Nonempty,
      mergeOf' π s = mergeOf π s h.1 h.2 := by
    intro s hs
    have hs' := mem_powersetCard.1 hs
    have h : s ⊆ π.parts ∧ s.Nonempty := ⟨hs'.1, card_pos.1 (by omega)⟩
    exact ⟨h, dite_eq_left h⟩
  symm
  refine card_bij (fun s _ => mergeOf' π s) (fun s hs => ?_) ?_ ?_
  · obtain ⟨hsP, hQ⟩ := mem_filter.1 hs
    obtain ⟨h, he⟩ := hm s hsP
    refine mem_filter.2 ⟨mem_univ _, ?_, hQ⟩
    rw [he]
    exact isMerge_mergeOf π _ (mem_powersetCard.1 hsP).2
  · intro s hs t ht hst
    have hs' := mem_powersetCard.1 (mem_filter.1 hs).1
    have ht' := mem_powersetCard.1 (mem_filter.1 ht).1
    obtain ⟨h1, he1⟩ := hm s (mem_filter.1 hs).1
    obtain ⟨h2, he2⟩ := hm t (mem_filter.1 ht).1
    rw [he1, he2] at hst
    have e := congrArg (fun ρ : SamplePartition n => π.parts ∩ ρ.parts) hst
    rw [inter_parts_mergeOf π hs'.1 (by omega), inter_parts_mergeOf π ht'.1 (by omega)] at e
    rw [← Finset.sdiff_sdiff_eq_self hs'.1, ← Finset.sdiff_sdiff_eq_self ht'.1, e]
  · intro π' hπ'
    obtain ⟨-, hM, hQ⟩ := mem_filter.1 hπ'
    obtain ⟨s, hs, h2, he⟩ := exists_mergeOf_eq hM
    have hsP : s ∈ π.parts.powersetCard 2 := mem_powersetCard.2 ⟨hs, h2⟩
    obtain ⟨h, he'⟩ := hm s hsP
    refine ⟨s, mem_filter.2 ⟨hsP, ?_⟩, ?_⟩
    · rw [he', he]
      exact hQ
    · rw [he', he]

/-- The trace of a set of genes of a sample of `n + 1` on the first `n` genes. -/
private def trace (B : Finset (Fin (n + 1))) : Finset (Fin n) :=
  univ.filter fun a => a.castSucc ∈ B

private theorem mem_parts_comap_castSucc (π : SamplePartition (n + 1)) (X : Finset (Fin n)) :
    X ∈ (π.comap Fin.castSucc).parts ↔ ∃ B ∈ π.parts, trace B = X ∧ X.Nonempty := by
  rw [Finpartition.mem_comap_parts]
  constructor
  · rintro ⟨hX, B, hB, rfl⟩
    exact ⟨B, hB, rfl, hX⟩
  · rintro ⟨B, hB, rfl, hX⟩
    exact ⟨hX, B, hB, rfl⟩

/-- A block of a partition of `Fin (n + 1)` has empty trace iff it is `{n}`. -/
private theorem trace_eq_empty_iff (π : SamplePartition (n + 1)) {B : Finset (Fin (n + 1))}
    (hB : B ∈ π.parts) : trace B = ∅ ↔ B = {Fin.last n} := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := π.nonempty_of_mem_parts hB
    have hsub : ∀ y ∈ B, y = Fin.last n := by
      intro y hy
      by_contra hne
      have hmem : y.castPred hne ∈ trace B := mem_filter.2 ⟨mem_univ _, by simpa using hy⟩
      rw [h] at hmem
      exact notMem_empty _ hmem
    exact eq_singleton_iff_unique_mem.2 ⟨hsub x hx ▸ hx, hsub⟩
  · rintro rfl
    ext a
    simp [trace, Fin.castSucc_ne_last]

private theorem trace_sup (s : Finset (Finset (Fin (n + 1)))) :
    trace (s.sup id) = (s.image trace).sup id := by
  classical
  ext a
  simp only [trace, mem_filter, mem_univ, true_and, sup_image, mem_sup, Function.comp_apply,
    id]

private theorem trace_injOn (π : SamplePartition (n + 1)) :
    Set.InjOn trace (π.parts.erase {Fin.last n} : Set (Finset (Fin (n + 1)))) := by
  intro A hA B hB h
  simp only [coe_erase, Set.mem_sdiff, mem_coe, Set.mem_singleton_iff] at hA hB
  obtain ⟨a, ha⟩ := nonempty_iff_ne_empty.2 (fun he => hA.2 ((trace_eq_empty_iff π hA.1).1 he))
  have hb : a ∈ trace B := h ▸ ha
  exact π.eq_of_mem_parts hA.1 hB.1 (mem_filter.1 ha).2 (mem_filter.1 hb).2

private theorem parts_comap_castSucc (π : SamplePartition (n + 1)) :
    (π.comap Fin.castSucc).parts = (π.parts.erase {Fin.last n}).image trace := by
  classical
  ext X
  rw [mem_parts_comap_castSucc, mem_image]
  constructor
  · rintro ⟨B, hB, rfl, hne⟩
    exact ⟨B, mem_erase.2 ⟨fun he => hne.ne_empty ((trace_eq_empty_iff π hB).2 he), hB⟩, rfl⟩
  · rintro ⟨B, hB, rfl⟩
    obtain ⟨hBL, hB⟩ := mem_erase.1 hB
    exact ⟨B, hB, rfl, nonempty_iff_ne_empty.2 fun he => hBL ((trace_eq_empty_iff π hB).1 he)⟩

private theorem card_parts_comap_castSucc (π : SamplePartition (n + 1)) :
    #(π.comap Fin.castSucc).parts = #(π.parts.erase {Fin.last n}) := by
  classical
  rw [parts_comap_castSucc, card_image_of_injOn (trace_injOn π)]

/-- The union of a set `s` of blocks containing a block other than `{n}` is not `{n}`. -/
private theorem sup_ne_last (π : SamplePartition (n + 1)) {s : Finset (Finset (Fin (n + 1)))}
    (hs : s ⊆ π.parts) {B : Finset (Fin (n + 1))} (hB : B ∈ s) (hBL : B ≠ {Fin.last n}) :
    s.sup id ≠ {Fin.last n} := by
  intro h
  have hle : B ⊆ s.sup id := le_sup (f := id) hB
  rw [h] at hle
  obtain ⟨x, hx⟩ := π.nonempty_of_mem_parts (hs hB)
  exact hBL (eq_singleton_iff_unique_mem.2 ⟨mem_singleton.1 (hle hx) ▸ hx,
    fun y hy => mem_singleton.1 (hle hy)⟩)

/-- Merging the block `{n}` into another block does not change the restriction. -/
private theorem comap_castSucc_mergeOf_of_mem (π : SamplePartition (n + 1))
    {s : Finset (Finset (Fin (n + 1)))} (hs : s ⊆ π.parts) (h2 : #s = 2) (hne : s.Nonempty)
    (hL : {Fin.last n} ∈ s) : (mergeOf π s hs hne).comap Fin.castSucc = π.comap Fin.castSucc := by
  classical
  obtain ⟨B, hBs, hBL⟩ : ∃ B ∈ s, B ≠ {Fin.last n} := by
    obtain ⟨A, hA, B, hB, hAB⟩ := one_lt_card.1 (by omega : 1 < #s)
    by_cases hA' : A = {Fin.last n}
    · exact ⟨B, hB, fun h => hAB (hA'.trans h.symm)⟩
    · exact ⟨A, hA, hA'⟩
  have hsB : s = {{Fin.last n}, B} := by
    rw [card_eq_two] at h2
    obtain ⟨x, y, hxy, rfl⟩ := h2
    simp only [mem_insert, mem_singleton] at hL hBs
    rcases hL with rfl | rfl <;> rcases hBs with rfl | rfl <;> simp_all [pair_comm]
  have hsup := sup_ne_last π hs hBs hBL
  have htr : trace (s.sup id) = trace B := by
    rw [trace_sup, hsB, image_insert, image_singleton, sup_insert, sup_singleton, id, id,
      (trace_eq_empty_iff π (hs hL)).2 rfl]
    simp
  refine Finpartition.ext ?_
  rw [parts_comap_castSucc, parts_comap_castSucc, parts_mergeOf, erase_insert_of_ne hsup]
  ext X
  simp only [mem_image, mem_insert, mem_erase, mem_sdiff]
  constructor
  · rintro ⟨D, hD | ⟨hDL, hDP, hDs⟩, rfl⟩
    · exact ⟨B, ⟨hBL, hs hBs⟩, by rw [hD, htr]⟩
    · exact ⟨D, ⟨hDL, hDP⟩, rfl⟩
  · rintro ⟨D, ⟨hDL, hDP⟩, rfl⟩
    by_cases hDB : D = B
    · exact ⟨s.sup id, Or.inl rfl, by rw [htr, hDB]⟩
    · refine ⟨D, Or.inr ⟨hDL, hDP, ?_⟩, rfl⟩
      rw [hsB]
      simp [hDL, hDB]

/-- Merging two blocks other than `{n}` merges their traces in the restriction. -/
private theorem comap_castSucc_mergeOf_of_notMem (π : SamplePartition (n + 1))
    {s : Finset (Finset (Fin (n + 1)))} (hs : s ⊆ π.parts) (hne : s.Nonempty)
    (hL : {Fin.last n} ∉ s) :
    (mergeOf π s hs hne).comap Fin.castSucc = mergeOf' (π.comap Fin.castSucc) (s.image trace) := by
  classical
  have hsE : s ⊆ π.parts.erase {Fin.last n} := fun B hB =>
    mem_erase.2 ⟨fun h => hL (h ▸ hB), hs hB⟩
  have ht : s.image trace ⊆ (π.comap Fin.castSucc).parts := by
    rw [parts_comap_castSucc]
    exact image_subset_image hsE
  have htne : (s.image trace).Nonempty := hne.image _
  obtain ⟨B, hB⟩ := id hne
  have hsup := sup_ne_last π hs hB (fun h => hL (h ▸ hB))
  rw [mergeOf', dite_eq_left ⟨ht, htne⟩]
  refine Finpartition.ext ?_
  rw [parts_comap_castSucc, parts_mergeOf, parts_mergeOf, parts_comap_castSucc,
    erase_insert_of_ne hsup, image_insert, trace_sup, ← image_sdiff_of_injOn (trace_injOn π) hsE]
  congr 2
  ext D
  simp only [mem_erase, mem_sdiff]
  tauto

open scoped Classical in
/-- Pairs of blocks containing a given block `x ∈ P`: there are `#P - 1` of them. -/
private theorem card_powersetCard_two_filter_mem {α : Type*} [DecidableEq α] (P : Finset α)
    {x : α} (hx : x ∈ P) : #{s ∈ P.powersetCard 2 | x ∈ s} = #P - 1 := by
  rw [← card_erase_of_mem hx]
  symm
  refine card_bij (fun y _ => {x, y}) (fun y hy => ?_) (fun y hy z hz h => ?_) (fun s hs => ?_)
  · obtain ⟨hyx, hyP⟩ := mem_erase.1 hy
    refine mem_filter.2 ⟨mem_powersetCard.2 ⟨?_, card_pair (Ne.symm hyx)⟩, mem_insert_self _ _⟩
    exact insert_subset hx (singleton_subset_iff.2 hyP)
  · have hyx := (mem_erase.1 hy).1
    have hzx := (mem_erase.1 hz).1
    have : y ∈ ({x, z} : Finset α) := h ▸ mem_insert_of_mem (mem_singleton_self y)
    simp only [mem_insert, mem_singleton] at this
    exact this.resolve_left hyx
  · obtain ⟨hs2, hxs⟩ := mem_filter.1 hs
    obtain ⟨hsP, hcard⟩ := mem_powersetCard.1 hs2
    obtain ⟨a, b, hab, rfl⟩ := card_eq_two.1 hcard
    simp only [mem_insert, mem_singleton] at hxs
    rcases hxs with rfl | rfl
    · exact ⟨b, mem_erase.2 ⟨Ne.symm hab, hsP (mem_insert_of_mem (mem_singleton_self b))⟩, rfl⟩
    · exact ⟨a, mem_erase.2 ⟨hab, hsP (mem_insert_self a _)⟩, pair_comm _ _⟩

open scoped Classical in
/-- **Mergers and restriction.** Among the mergers `π'` of `π`, those restricting to `ρ` are
the merger realizing `ρ` (if `ρ` is a merger of the restriction of `π`) and, when `ρ` is the
restriction of `π` and `{n}` is a block of `π`, the `#π.parts - 1` mergers of `{n}`. -/
private theorem card_isMerge_comap_castSucc (π : SamplePartition (n + 1)) (ρ : SamplePartition n) :
    #{π' | IsMerge π π' ∧ π'.comap Fin.castSucc = ρ} =
      (if IsMerge (π.comap Fin.castSucc) ρ then 1 else 0) +
        (if π.comap Fin.castSucc = ρ ∧ {Fin.last n} ∈ π.parts then #π.parts - 1 else 0) := by
  trans #{s ∈ π.parts.powersetCard 2 | (mergeOf' π s).comap Fin.castSucc = ρ}
  · convert card_filter_isMerge π (fun π' => π'.comap Fin.castSucc = ρ)
  rw [← card_filter_add_card_filter_not (fun s => {Fin.last n} ∈ s), filter_filter,
    filter_filter, add_comm]
  have hunf : ∀ s ∈ π.parts.powersetCard 2, ∃ (hs : s ⊆ π.parts) (hne : s.Nonempty),
      mergeOf' π s = mergeOf π s hs hne ∧ #s = 2 := by
    intro s hs
    have hs' := mem_powersetCard.1 hs
    have hne : s.Nonempty := card_pos.1 (by omega)
    exact ⟨hs'.1, hne, dite_eq_left ⟨hs'.1, hne⟩, hs'.2⟩
  congr 1
  · -- pairs avoiding `{n}` correspond to pairs of blocks of the restriction
    trans #{t ∈ (π.comap Fin.castSucc).parts.powersetCard 2 | mergeOf' (π.comap Fin.castSucc) t = ρ}
    swap
    · have h := card_filter_isMerge (π.comap Fin.castSucc) (fun π' => π' = ρ)
      have h2 : #{π' | IsMerge (π.comap Fin.castSucc) π' ∧ π' = ρ} =
          if IsMerge (π.comap Fin.castSucc) ρ then 1 else 0 := by
        split_ifs with hM
        · rw [card_eq_one]
          refine ⟨ρ, ?_⟩
          ext x
          simp only [mem_filter, mem_univ, true_and, mem_singleton]
          constructor
          · exact And.right
          · rintro rfl
            exact ⟨hM, rfl⟩
        · rw [card_eq_zero, filter_eq_empty_iff]
          rintro x - ⟨hx, rfl⟩
          exact hM hx
      rw [← h2]
      convert h.symm using 3
    have hsub := parts_comap_castSucc π
    refine card_bij (fun s _ => s.image trace) (fun s hs => ?_) (fun s hs t ht h => ?_)
      (fun t ht => ?_)
    · obtain ⟨hsP, hρ, hL⟩ := mem_filter.1 hs
      obtain ⟨hsP', hne, he, h2⟩ := hunf s hsP
      have hsE : s ⊆ π.parts.erase {Fin.last n} := fun B hB =>
        mem_erase.2 ⟨fun h => hL (h ▸ hB), hsP' hB⟩
      refine mem_filter.2 ⟨mem_powersetCard.2 ⟨?_, ?_⟩, ?_⟩
      · rw [hsub]
        exact image_subset_image hsE
      · rw [card_image_of_injOn ((trace_injOn π).mono (coe_subset.2 hsE)), h2]
      · rw [← comap_castSucc_mergeOf_of_notMem π hsP' hne hL, ← he]
        exact hρ
    · have hsE : s ⊆ π.parts.erase {Fin.last n} := fun B hB =>
        mem_erase.2 ⟨fun h => (mem_filter.1 hs).2.2 (h ▸ hB),
          (mem_powersetCard.1 (mem_filter.1 hs).1).1 hB⟩
      have htE : t ⊆ π.parts.erase {Fin.last n} := fun B hB =>
        mem_erase.2 ⟨fun h => (mem_filter.1 ht).2.2 (h ▸ hB),
          (mem_powersetCard.1 (mem_filter.1 ht).1).1 hB⟩
      have key : ∀ {u v : Finset (Finset (Fin (n + 1)))}, u ⊆ π.parts.erase {Fin.last n} →
          v ⊆ π.parts.erase {Fin.last n} → u.image trace = v.image trace → u ⊆ v := by
        intro u v hu hv huv A hA
        obtain ⟨B, hB, hBA⟩ := mem_image.1 (huv ▸ mem_image_of_mem trace hA)
        rwa [(trace_injOn π) (hv hB) (hu hA) hBA] at hB
      exact subset_antisymm (key hsE htE h) (key htE hsE h.symm)
    · obtain ⟨htP, hρ⟩ := mem_filter.1 ht
      obtain ⟨htsub, ht2⟩ := mem_powersetCard.1 htP
      rw [hsub] at htsub
      set s := (π.parts.erase {Fin.last n}).filter fun B => trace B ∈ t with hs_def
      have hsE : s ⊆ π.parts.erase {Fin.last n} := filter_subset _ _
      have himg : s.image trace = t := by
        ext X
        simp only [hs_def, mem_image, mem_filter]
        constructor
        · rintro ⟨B, ⟨-, hB⟩, rfl⟩
          exact hB
        · intro hX
          obtain ⟨B, hB, rfl⟩ := mem_image.1 (htsub hX)
          exact ⟨B, ⟨hB, hX⟩, rfl⟩
      have hs2 : #s = 2 := by
        rw [← ht2, ← himg, card_image_of_injOn ((trace_injOn π).mono (coe_subset.2 hsE))]
      have hsP : s ⊆ π.parts := hsE.trans (erase_subset _ _)
      have hL : {Fin.last n} ∉ s := fun h => (mem_erase.1 (hsE h)).1 rfl
      have hne : s.Nonempty := card_pos.1 (by omega)
      refine ⟨s, mem_filter.2 ⟨mem_powersetCard.2 ⟨hsP, hs2⟩, ?_, hL⟩, himg⟩
      rw [mergeOf', dite_eq_left ⟨hsP, hne⟩, comap_castSucc_mergeOf_of_notMem π hsP hne hL, himg]
      exact hρ
  · -- pairs containing `{n}` do not change the restriction
    have hfilt : (π.parts.powersetCard 2).filter
        (fun s => (mergeOf' π s).comap Fin.castSucc = ρ ∧ {Fin.last n} ∈ s) =
        if π.comap Fin.castSucc = ρ then (π.parts.powersetCard 2).filter (fun s => {Fin.last n} ∈ s)
        else ∅ := by
      ext s
      simp only [mem_filter]
      constructor
      · rintro ⟨hs, hρ, hL⟩
        obtain ⟨hsP, hne, he, h2⟩ := hunf s hs
        rw [he, comap_castSucc_mergeOf_of_mem π hsP h2 hne hL] at hρ
        rw [ite_eq_left hρ]
        exact mem_filter.2 ⟨hs, hL⟩
      · intro h
        by_cases hρ : π.comap Fin.castSucc = ρ
        · rw [ite_eq_left hρ] at h
          obtain ⟨hs, hL⟩ := mem_filter.1 h
          obtain ⟨hsP, hne, he, h2⟩ := hunf s hs
          exact ⟨hs, by rw [he, comap_castSucc_mergeOf_of_mem π hsP h2 hne hL, hρ], hL⟩
        · rw [ite_eq_right hρ] at h
          exact absurd h (notMem_empty s)
    rw [hfilt]
    by_cases hρ : π.comap Fin.castSucc = ρ
    · rw [ite_eq_left hρ]
      by_cases hL : {Fin.last n} ∈ π.parts
      · rw [card_powersetCard_two_filter_mem π.parts hL, ite_eq_left ⟨hρ, hL⟩]
      · rw [ite_eq_right (fun h => hL h.2), card_eq_zero, filter_eq_empty_iff]
        intro s hs hLs
        exact hL ((mem_powersetCard.1 hs).1 hLs)
    · rw [ite_eq_right hρ, ite_eq_right (fun h => hρ h.1), card_empty]

/-- Split the block `C` of `π'` into `A` and `C \ A`. -/
private def splitOf (π' : SamplePartition n) {C A : Finset (Fin n)} (hC : C ∈ π'.parts)
    (hAC : A ⊆ C)
    (hA : A.Nonempty) (hA' : (C \ A).Nonempty) : SamplePartition n where
  parts := insert A (insert (C \ A) (π'.parts.erase C))
  supIndep := by
    have hdisj : ∀ D ∈ π'.parts.erase C, Disjoint C D := fun D hD =>
      π'.disjoint hC (mem_of_mem_erase hD) (ne_of_mem_erase hD).symm
    rw [Finset.supIndep_iff_pairwiseDisjoint, coe_insert, coe_insert]
    refine ((π'.disjoint.subset (by simp)).insert ?_).insert ?_
    · intro D hD _
      exact (hdisj D hD).mono_left sdiff_le
    · intro D hD hne
      simp only [Set.mem_insert_iff, mem_coe] at hD
      rcases hD with rfl | hD
      · exact disjoint_sdiff_self_right
      · exact (hdisj D hD).mono_left hAC
  sup_parts := by
    have h := π'.sup_parts
    rw [← insert_erase hC, sup_insert] at h
    rw [sup_insert, sup_insert, id, id, ← sup_assoc,
      show A ⊔ C \ A = C from union_sdiff_of_subset hAC]
    exact h
  bot_notMem := by
    intro h
    simp only [mem_insert] at h
    rcases h with h | h | h
    · exact hA.ne_empty h.symm
    · exact hA'.ne_empty h.symm
    · exact π'.bot_notMem (mem_of_mem_erase h)

private theorem parts_splitOf (π' : SamplePartition n) {C A : Finset (Fin n)} (hC : C ∈ π'.parts)
    (hAC : A ⊆ C) (hA : A.Nonempty) (hA' : (C \ A).Nonempty) :
    (splitOf π' hC hAC hA hA').parts = insert A (insert (C \ A) (π'.parts.erase C)) := rfl

/-- A nonempty proper part of a block of `π'` is not a block of `π'`. -/
private theorem notMem_parts_of_ssubset (π' : SamplePartition n) {C A : Finset (Fin n)}
    (hC : C ∈ π'.parts) (hAC : A ⊆ C) (hA : A.Nonempty) (hA' : (C \ A).Nonempty) :
    A ∉ π'.parts := by
  intro hmem
  obtain ⟨x, hx⟩ := hA
  have : A = C := π'.eq_of_mem_parts hmem hC hx (hAC hx)
  rw [this, sdiff_self] at hA'
  exact not_nonempty_empty hA'

private theorem sdiff_parts_splitOf (π' : SamplePartition n) {C A : Finset (Fin n)}
    (hC : C ∈ π'.parts)
    (hAC : A ⊆ C) (hA : A.Nonempty) (hA' : (C \ A).Nonempty) :
    (splitOf π' hC hAC hA hA').parts \ π'.parts = {A, C \ A} := by
  have h1 := notMem_parts_of_ssubset π' hC hAC hA hA'
  have h2 : C \ A ∉ π'.parts := by
    refine notMem_parts_of_ssubset π' hC sdiff_subset hA' ?_
    rwa [Finset.sdiff_sdiff_eq_self hAC]
  ext B
  simp only [parts_splitOf, mem_sdiff, mem_insert, mem_singleton]
  constructor
  · rintro ⟨h | h | h, hB⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (mem_of_mem_erase h) hB
  · rintro (rfl | rfl)
    · exact ⟨Or.inl rfl, h1⟩
    · exact ⟨Or.inr (Or.inl rfl), h2⟩

private theorem isMerge_splitOf (π' : SamplePartition n) {C A : Finset (Fin n)} (hC : C ∈ π'.parts)
    (hAC : A ⊆ C) (hA : A.Nonempty) (hA' : (C \ A).Nonempty) :
    IsMerge (splitOf π' hC hAC hA hA') π' := by
  have h1 := notMem_parts_of_ssubset π' hC hAC hA hA'
  have hne : A ≠ C \ A := by
    intro h
    obtain ⟨x, hx⟩ := hA
    have hx' := hx
    rw [h] at hx'
    exact (mem_sdiff.1 hx').2 hx
  refine ⟨fun B hB => ?_, ?_⟩
  · simp only [parts_splitOf, mem_insert] at hB
    rcases hB with rfl | rfl | hB
    · exact ⟨C, hC, hAC⟩
    · exact ⟨C, hC, sdiff_subset⟩
    · exact ⟨B, mem_of_mem_erase hB, le_rfl⟩
  · rw [parts_splitOf, card_insert_of_notMem, card_insert_of_notMem, card_erase_of_mem hC]
    · have := card_pos.2 ⟨C, hC⟩
      omega
    · intro h
      exact notMem_parts_of_ssubset π' hC sdiff_subset hA' (by rwa [Finset.sdiff_sdiff_eq_self hAC])
        (mem_of_mem_erase h)
    · intro h
      rcases mem_insert.1 h with h | h
      · exact hne h
      · exact h1 (mem_of_mem_erase h)

private theorem prod_splitOf (π' : SamplePartition n) {C A : Finset (Fin n)} (hC : C ∈ π'.parts)
    (hAC : A ⊆ C) (hA : A.Nonempty) (hA' : (C \ A).Nonempty) :
    ∏ B ∈ (splitOf π' hC hAC hA hA').parts, (#B).factorial =
      (#A).factorial * (#C - #A).factorial * ∏ B ∈ π'.parts.erase C, (#B).factorial := by
  have h1 := notMem_parts_of_ssubset π' hC hAC hA hA'
  have hne : A ≠ C \ A := by
    intro h
    obtain ⟨x, hx⟩ := hA
    have hx' := hx
    rw [h] at hx'
    exact (mem_sdiff.1 hx').2 hx
  rw [parts_splitOf, prod_insert, prod_insert, card_sdiff_of_subset hAC, mul_assoc]
  · intro h
    exact notMem_parts_of_ssubset π' hC sdiff_subset hA' (by rwa [Finset.sdiff_sdiff_eq_self hAC])
      (mem_of_mem_erase h)
  · intro h
    rcases mem_insert.1 h with h | h
    · exact hne h
    · exact h1 (mem_of_mem_erase h)

/-- `∑_{∅ ≠ A ⊊ C} |A|! |C \ A|! = (|C| - 1) |C|!`. -/
private theorem sum_split_factorial (C : Finset (Fin n)) (hC : C.Nonempty) :
    ∑ A ∈ C.powerset with A.Nonempty ∧ (C \ A).Nonempty, (#A).factorial * (#C - #A).factorial =
      (#C - 1) * (#C).factorial := by
  classical
  have hall : ∑ A ∈ C.powerset, (#A).factorial * (#C - #A).factorial =
      (#C + 1) * (#C).factorial := by
    rw [sum_powerset_apply_card (fun a => a.factorial * (#C - a).factorial)]
    rw [sum_congr rfl fun a ha => by
      rw [smul_eq_mul, ← mul_assoc, Nat.choose_mul_factorial_mul_factorial
        (Nat.lt_succ_iff.1 (mem_range.1 ha))]]
    rw [sum_const, card_range, smul_eq_mul]
  have hnot : C.powerset.filter (fun A => ¬ (A.Nonempty ∧ (C \ A).Nonempty)) = {∅, C} := by
    ext A
    simp only [mem_filter, mem_powerset, mem_insert, mem_singleton, not_and_or,
      not_nonempty_iff_eq_empty, sdiff_eq_empty_iff_subset]
    constructor
    · rintro ⟨hAC, h | h⟩
      · exact Or.inl h
      · exact Or.inr (subset_antisymm hAC h)
    · rintro (rfl | rfl)
      · exact ⟨empty_subset _, Or.inl rfl⟩
      · exact ⟨subset_rfl, Or.inr subset_rfl⟩
  have hsplit := sum_filter_add_sum_filter_not C.powerset (fun A => A.Nonempty ∧ (C \ A).Nonempty)
    (fun A => (#A).factorial * (#C - #A).factorial)
  rw [hnot, sum_pair hC.ne_empty.symm, hall] at hsplit
  simp only [card_empty, Nat.factorial_zero, Nat.sub_zero, one_mul, Nat.sub_self,
    mul_one] at hsplit
  have hc := card_pos.2 hC
  obtain ⟨c, hc'⟩ : ∃ c, #C = c + 1 := ⟨#C - 1, by omega⟩
  rw [hc'] at hsplit ⊢
  simp only [Nat.add_sub_cancel]
  nlinarith [hsplit]

/-- The blocks of a predecessor `π` of `π' = mergeOf π s` that are not blocks of `π'` are the
merged blocks `s`. -/
private theorem sdiff_parts_mergeOf (π : SamplePartition n) {s : Finset (Finset (Fin n))}
    (hs : s ⊆ π.parts) (h2 : 2 ≤ #s) (hne : s.Nonempty) :
    π.parts \ (mergeOf π s hs hne).parts = s := by
  have hsup := sup_notMem_parts π hs h2
  ext B
  simp only [mem_sdiff, parts_mergeOf, mem_insert, not_or, not_and, not_not]
  constructor
  · rintro ⟨hB, -, h⟩
    exact h hB
  · intro hB
    exact ⟨hs hB, fun h => hsup (h ▸ hs hB), fun _ => hB⟩

/-- A predecessor `π` of `π'` in which the blocks `A, B` merge is the split of `A ∪ B`. -/
private theorem splitOf_eq_of_mergeOf {π π' : SamplePartition n} {A B : Finset (Fin n)}
    (hAB : A ≠ B) (hs : {A, B} ⊆ π.parts) (he : mergeOf π {A, B} hs (insert_nonempty _ _) = π')
    (hC : A ∪ B ∈ π'.parts) (hAC : A ⊆ A ∪ B) (hA : A.Nonempty)
    (hA' : ((A ∪ B) \ A).Nonempty) :
    splitOf π' hC hAC hA hA' = π := by
  have hApart : A ∈ π.parts := hs (mem_insert_self _ _)
  have hBpart : B ∈ π.parts := hs (mem_insert_of_mem (mem_singleton_self _))
  have hdisj : Disjoint A B := π.disjoint hApart hBpart hAB
  have hsdiff : (A ∪ B) \ A = B := by
    rw [union_sdiff_left]
    exact sdiff_eq_self_of_disjoint hdisj.symm
  have hsup : ({A, B} : Finset (Finset (Fin n))).sup id = A ∪ B := by
    rw [sup_insert, sup_singleton, id, id, sup_eq_union]
  have hnot : A ∪ B ∉ π.parts := by
    rw [← hsup]
    exact sup_notMem_parts π hs (by rw [card_pair hAB])
  refine Finpartition.ext ?_
  rw [parts_splitOf, hsdiff, ← he, parts_mergeOf, hsup, erase_insert (fun h => hnot
    (mem_sdiff.1 h).1)]
  ext X
  simp only [mem_insert, mem_sdiff, mem_singleton]
  constructor
  · rintro (rfl | rfl | ⟨hX, -⟩)
    · exact hApart
    · exact hBpart
    · exact hX
  · intro hX
    by_cases h1 : X = A
    · exact Or.inl h1
    · by_cases h2 : X = B
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ⟨hX, by tauto⟩)

open scoped Classical in
/-- **Splitting identity.** Summing `∏_{B ∈ π} |B|!` over the partitions `π` that merge to
`π'` gives `(n - #π'.parts) / 2 · ∏_{B ∈ π'} |B|!`: a block of size `b` has
`(2^b - 2) / 2` splits into two blocks, and `∑_{∅ ≠ A ⊊ B} |A|! |B \ A|! = (b - 1) b!`. -/
theorem two_mul_sum_prod_factorial_isMerge (π' : SamplePartition n) :
    2 * ∑ π with IsMerge π π', π.cardProd Nat.factorial =
      (n - #π'.parts) * π'.cardProd Nat.factorial := by
  simp only [Finpartition.cardProd]
  set F : SamplePartition n → ℕ := fun π => ∏ B ∈ π.parts, (#B).factorial with hF
  let Cond : (Σ _ : Finset (Fin n), Finset (Fin n)) → Prop := fun x =>
    x.1 ∈ π'.parts ∧ x.2 ⊆ x.1 ∧ x.2.Nonempty ∧ (x.1 \ x.2).Nonempty
  let T : Finset (Σ _ : Finset (Fin n), Finset (Fin n)) :=
    π'.parts.sigma fun C => C.powerset.filter fun A => A.Nonempty ∧ (C \ A).Nonempty
  have hmemT : ∀ x, x ∈ T ↔ Cond x := by
    rintro ⟨C, A⟩
    simp only [T, Cond, mem_sigma, mem_filter, mem_powerset]
  let Φ : (Σ _ : Finset (Fin n), Finset (Fin n)) → SamplePartition n := fun x =>
    if h : Cond x then splitOf π' h.1 h.2.1 h.2.2.1 h.2.2.2 else π'
  have hΦ : ∀ x (h : Cond x), Φ x = splitOf π' h.1 h.2.1 h.2.2.1 h.2.2.2 := fun x h =>
    dite_eq_left h
  -- Step A: the sum over ordered splits
  have hA : ∑ x ∈ T, F (Φ x) = (n - #π'.parts) * F π' := by
    rw [sum_sigma]
    have hinner : ∀ C ∈ π'.parts,
        ∑ A ∈ C.powerset.filter (fun A => A.Nonempty ∧ (C \ A).Nonempty), F (Φ ⟨C, A⟩) =
          (#C - 1) * F π' := by
      intro C hC
      have hstep : ∀ A ∈ C.powerset.filter (fun A => A.Nonempty ∧ (C \ A).Nonempty),
          F (Φ ⟨C, A⟩) = (#A).factorial * (#C - #A).factorial *
            ∏ B ∈ π'.parts.erase C, (#B).factorial := by
        intro A hA
        have hc : Cond ⟨C, A⟩ := (hmemT ⟨C, A⟩).1 (mem_sigma.2 ⟨hC, hA⟩)
        rw [hΦ _ hc]
        exact prod_splitOf π' hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
      rw [sum_congr rfl hstep, ← sum_mul, sum_split_factorial C (π'.nonempty_of_mem_parts hC)]
      change _ = (#C - 1) * ∏ B ∈ π'.parts, (#B).factorial
      rw [← mul_prod_erase π'.parts (fun B => (#B).factorial) hC]
      ring
    rw [sum_congr rfl hinner, ← sum_mul]
    congr 1
    have h1 : ∀ C ∈ π'.parts, #C - 1 + 1 = #C := fun C hC => by
      have := card_pos.2 (π'.nonempty_of_mem_parts hC)
      omega
    have h2 : ∑ C ∈ π'.parts, (#C - 1) + #π'.parts = n := by
      have hs := π'.sum_card_parts
      rw [card_univ, Fintype.card_fin] at hs
      have h3 : ∑ C ∈ π'.parts, (#C - 1 + 1) = ∑ C ∈ π'.parts, (#C - 1) + #π'.parts := by
        rw [sum_add_distrib, sum_const, smul_eq_mul, mul_one]
      rw [sum_congr rfl h1, hs] at h3
      omega
    omega
  -- Step B: each predecessor is hit by exactly two ordered splits
  have hB : ∑ x ∈ T, F (Φ x) = 2 * ∑ π with IsMerge π π', F π := by
    rw [sum_comp, mul_sum]
    have himage : T.image Φ = univ.filter fun π => IsMerge π π' := by
      ext π
      simp only [mem_image, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hc := (hmemT x).1 hx
        rw [hΦ x hc]
        exact isMerge_splitOf π' _ _ _ _
      · intro hπ
        obtain ⟨s, hs, h2, he⟩ := exists_mergeOf_eq hπ
        obtain ⟨A, B, hAB, rfl⟩ := card_eq_two.1 h2
        have hC : A ∪ B ∈ π'.parts := by
          rw [← he, parts_mergeOf]
          refine mem_insert.2 (Or.inl ?_)
          rw [sup_insert, sup_singleton, id, id, sup_eq_union]
        have hApart : A ∈ π.parts := hs (mem_insert_self _ _)
        have hBpart : B ∈ π.parts := hs (mem_insert_of_mem (mem_singleton_self _))
        have hsdiff : (A ∪ B) \ A = B := by
          rw [union_sdiff_left]
          exact sdiff_eq_self_of_disjoint (π.disjoint hApart hBpart hAB).symm
        have hc : Cond ⟨A ∪ B, A⟩ := ⟨hC, subset_union_left, π.nonempty_of_mem_parts hApart,
          by change ((A ∪ B) \ A).Nonempty; rw [hsdiff]; exact π.nonempty_of_mem_parts hBpart⟩
        exact ⟨⟨A ∪ B, A⟩, (hmemT _).2 hc, by
          rw [hΦ _ hc]
          exact splitOf_eq_of_mergeOf hAB hs he _ _ _ _⟩
    rw [himage]
    refine sum_congr rfl fun π hπ => ?_
    rw [smul_eq_mul]
    congr 1
    -- the fiber over `π` has two elements
    obtain ⟨s, hs, h2, he⟩ := exists_mergeOf_eq (mem_filter.1 hπ).2
    have hne : s.Nonempty := card_pos.1 (by omega)
    have hsd := sdiff_parts_mergeOf π hs (by omega) hne
    rw [← h2]
    symm
    refine card_bij (fun A _ => (⟨s.sup id, A⟩ : Σ _ : Finset (Fin n), Finset (Fin n)))
      (fun A hA => ?_) (fun A _ B _ h => by simpa using h) (fun x hx => ?_)
    · obtain ⟨A₁, B₁, hAB, rfl⟩ := card_eq_two.1 h2
      have hsup : ({A₁, B₁} : Finset (Finset (Fin n))).sup id = A₁ ∪ B₁ := by
        rw [sup_insert, sup_singleton, id, id, sup_eq_union]
      have hC : A₁ ∪ B₁ ∈ π'.parts := by
        rw [← he, parts_mergeOf, hsup]
        exact mem_insert_self _ _
      have hA₁ : A₁ ∈ π.parts := hs (mem_insert_self _ _)
      have hB₁ : B₁ ∈ π.parts := hs (mem_insert_of_mem (mem_singleton_self _))
      have hdisj := π.disjoint hA₁ hB₁ hAB
      rw [hsup, mem_filter]
      rcases mem_insert.1 hA with rfl | hA
      · have hsdiff : (A ∪ B₁) \ A = B₁ := by
          rw [union_sdiff_left]
          exact sdiff_eq_self_of_disjoint hdisj.symm
        have hc : Cond ⟨A ∪ B₁, A⟩ := ⟨hC, subset_union_left, π.nonempty_of_mem_parts hA₁,
          by change ((A ∪ B₁) \ A).Nonempty; rw [hsdiff]; exact π.nonempty_of_mem_parts hB₁⟩
        refine ⟨(hmemT _).2 hc, ?_⟩
        rw [hΦ _ hc]
        exact splitOf_eq_of_mergeOf hAB hs he _ _ _ _
      · rw [mem_singleton] at hA
        subst hA
        have hs' : ({A, A₁} : Finset (Finset (Fin n))) ⊆ π.parts := by
          rw [pair_comm]; exact hs
        have he' : mergeOf π {A, A₁} hs' (insert_nonempty _ _) = π' := by
          rw [← he]
          congr 1
          exact pair_comm _ _
        have hC' : A ∪ A₁ ∈ π'.parts := by rw [union_comm]; exact hC
        have hsdiff : (A ∪ A₁) \ A = A₁ := by
          rw [union_sdiff_left]
          exact sdiff_eq_self_of_disjoint hdisj
        have hc : Cond ⟨A ∪ A₁, A⟩ := ⟨hC', subset_union_left, π.nonempty_of_mem_parts hB₁,
          by change ((A ∪ A₁) \ A).Nonempty; rw [hsdiff]; exact π.nonempty_of_mem_parts hA₁⟩
        have heq : A₁ ∪ A = A ∪ A₁ := union_comm _ _
        rw [heq]
        refine ⟨(hmemT _).2 hc, ?_⟩
        rw [hΦ _ hc]
        exact splitOf_eq_of_mergeOf (Ne.symm hAB) hs' he' _ _ _ _
    · obtain ⟨hxT, hxπ⟩ := mem_filter.1 hx
      have hc := (hmemT x).1 hxT
      have hpair := sdiff_parts_splitOf π' hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
      rw [← hΦ x hc, hxπ, ← he, hsd] at hpair
      refine ⟨x.2, by rw [hpair]; exact mem_insert_self _ _, ?_⟩
      obtain ⟨C, A⟩ := x
      simp only at hpair ⊢
      have : C = ({A, C \ A} : Finset (Finset (Fin n))).sup id := by
        rw [sup_insert, sup_singleton, id, id, sup_eq_union, union_sdiff_of_subset hc.2.1]
      rw [this, ← hpair]
  rw [← hB, hA]


/-- The partition into singletons has `n` blocks. -/
private theorem card_parts_bot : #(⊥ : SamplePartition n).parts = n := by
  rw [Finpartition.card_bot, card_univ, Fintype.card_fin]

/-- The only partition of a sample of `n` with `n` blocks is the partition into singletons. -/
private theorem eq_bot_of_card_parts (π : SamplePartition n) (h : #π.parts = n) : π = ⊥ :=
  (Finpartition.eq_bot_iff_card_parts_eq_card π).2 (by rw [h, card_univ, Fintype.card_fin])

/-- Kingman's formula gives probability `1` to the partition into singletons. -/
theorem kingmanProb_bot : kingmanProb n ⊥ = 1 := by
  rw [kingmanProb, Finpartition.cardProd_bot, Nat.factorial_one, one_pow, card_parts_bot,
    Nat.sub_self, Nat.factorial_zero, one_mul, mul_one]
  exact div_self (by positivity)

/-- Kingman's formula for a partition with `k` blocks. -/
theorem kingmanProb_of_card {π : SamplePartition n} {k : ℕ} (h : #π.parts = k) :
    kingmanProb n π = ((n - k).factorial * k.factorial * (k - 1).factorial : ℝ) *
      ((π.cardProd Nat.factorial : ℕ) : ℝ) / (n.factorial * (n - 1).factorial : ℝ) := by
  subst h
  simp only [kingmanProb]
  push_cast
  ring

open scoped Classical in
/-- **Backward equation of Kingman's formula.** For a partition `π'` with `k` blocks,
`1 ≤ k < n`, the Kingman probabilities of the partitions merging to `π'` sum to
`(k + 1).choose 2` times the Kingman probability of `π'`. -/
theorem sum_kingmanProb_isMerge (π' : SamplePartition n) (h1 : 1 ≤ #π'.parts)
    (hn : #π'.parts < n) :
    ∑ π with IsMerge π π', kingmanProb n π =
      (((#π'.parts + 1).choose 2 : ℕ) : ℝ) * kingmanProb n π' := by
  set k := #π'.parts with hk
  have hsum : ∑ π with IsMerge π π', kingmanProb n π =
      ((n - (k + 1)).factorial * (k + 1).factorial * k.factorial : ℝ) /
        (n.factorial * (n - 1).factorial : ℝ) *
        ∑ π with IsMerge π π', ((π.cardProd Nat.factorial : ℕ) : ℝ) := by
    rw [mul_sum]
    refine sum_congr rfl fun π hπ => ?_
    rw [kingmanProb_of_card (mem_filter.1 hπ).2.2.symm, Nat.add_sub_cancel]
    ring
  have hG : (2 : ℝ) * ∑ π with IsMerge π π', ((π.cardProd Nat.factorial : ℕ) : ℝ) =
      ((n - k : ℕ) : ℝ) * ((π'.cardProd Nat.factorial : ℕ) : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast two_mul_sum_prod_factorial_isMerge π'
  have hc : (((k + 1).choose 2 : ℕ) : ℝ) * 2 = (k + 1) * k := by
    have : (k + 1).choose 2 * 2 = (k + 1) * k := by
      rw [Nat.choose_two_right, Nat.add_sub_cancel]
      exact Nat.div_mul_cancel (by rw [mul_comm]; exact (Nat.even_mul_succ_self k).two_dvd)
    exact_mod_cast this
  have f1 : ((n - k).factorial : ℝ) = ((n - k : ℕ) : ℝ) * (n - (k + 1)).factorial := by
    rw [show n - k = n - (k + 1) + 1 by omega, Nat.factorial_succ, Nat.cast_mul]
  have f2 : (k.factorial : ℝ) = k * (k - 1).factorial := by
    conv_lhs => rw [show k = k - 1 + 1 by omega, Nat.factorial_succ]
    rw [Nat.sub_add_cancel h1, Nat.cast_mul]
  have f3 : ((k + 1).factorial : ℝ) = (k + 1) * k.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hD : (n.factorial * (n - 1).factorial : ℝ) ≠ 0 := by positivity
  rw [hsum, kingmanProb_of_card hk.symm, f1, f3, f2, div_mul_eq_mul_div, mul_div_assoc',
    div_left_inj' hD]
  set S := ∑ π with IsMerge π π', ((π.cardProd Nat.factorial : ℕ) : ℝ)
  set a : ℝ := ((n - (k + 1)).factorial : ℝ)
  set b : ℝ := ((k - 1).factorial : ℝ)
  set C : ℝ := (((k + 1).choose 2 : ℕ) : ℝ)
  linear_combination (a * k * b ^ 2 * C) * hG - (a * k * b ^ 2 * S) * hc

/-- The jump-chain transition matrix is row-stochastic. -/
theorem jumpMatrix_mem_rowStochastic : jumpMatrix n ∈ rowStochastic ℝ (SamplePartition n) := by
  classical
  refine mem_rowStochastic_iff_sum.2 ⟨fun π π' => ?_, fun π => ?_⟩
  · simp only [jumpMatrix, Matrix.of_apply]
    split_ifs <;> positivity
  · simp only [jumpMatrix, Matrix.of_apply]
    split_ifs with h
    · rw [← sum_filter, sum_const, card_isMerge, nsmul_eq_mul]
      have : ((#π.parts).choose 2 : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos h).ne'
      exact mul_inv_cancel₀ this
    · simp

/-- **Kingman's formula** (Kingman 1982; Durrett 2008, ch. 1). For `m < n`, after `m`
coalescences the jump chain started from singletons is at a partition `π` with probability
`kingmanProb n π = (n - k)! k! (k - 1)! ∏_{B ∈ π} |B|! / (n! (n - 1)!)` if `π` has `k = n - m`
blocks, and `0` otherwise. (For `m ≥ n - 1` the chain has been absorbed at the one-block
partition.) -/
theorem jumpLaw_eq {m : ℕ} (hm : m < n) (π : SamplePartition n) :
    jumpLaw n m π = if #π.parts + m = n then kingmanProb n π else 0 := by
  classical
  induction m generalizing π with
  | zero =>
    simp only [jumpLaw, pow_zero, Matrix.one_apply, add_zero]
    by_cases h : #π.parts = n
    · have hb := eq_bot_of_card_parts π h
      rw [ite_eq_left hb.symm, ite_eq_left h, hb, kingmanProb_bot]
    · rw [ite_eq_right h, ite_eq_right]
      rintro rfl
      exact h card_parts_bot
  | succ m ih =>
    have hm' : m < n := by omega
    have key : ∀ π₀ : SamplePartition n,
        jumpLaw n m π₀ * jumpMatrix n π₀ π =
          if IsMerge π₀ π then
            (if #π.parts + (m + 1) = n then
              kingmanProb n π₀ / (((#π.parts + 1).choose 2 : ℕ) : ℝ) else 0)
          else 0 := by
      intro π₀
      rw [ih hm' π₀]
      by_cases h0 : #π₀.parts + m = n
      · have h2 : 2 ≤ #π₀.parts := by omega
        simp only [jumpMatrix, Matrix.of_apply, ite_eq_left h0, ite_eq_left h2]
        by_cases hM : IsMerge π₀ π
        · have hc : #π₀.parts = #π.parts + 1 := hM.2.symm
          rw [ite_eq_left hM, ite_eq_left hM, ite_eq_left (by omega), hc, div_eq_mul_inv]
        · rw [ite_eq_right hM, ite_eq_right hM, mul_zero]
      · rw [ite_eq_right h0, zero_mul]
        by_cases hM : IsMerge π₀ π
        · have hc : #π₀.parts = #π.parts + 1 := hM.2.symm
          rw [ite_eq_left hM, ite_eq_right (by omega)]
        · rw [ite_eq_right hM]
    simp only [jumpLaw, pow_succ, Matrix.mul_apply] at *
    simp_rw [key]
    rw [← sum_filter]
    split_ifs with h
    · rw [← sum_div, sum_kingmanProb_isMerge π (by omega) (by omega)]
      have : (((#π.parts + 1).choose 2 : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos (by omega)).ne'
      field_simp
    · simp

/-- The jump chain's law after `m` jumps sums to one (its entries are nonnegative by
`jumpMatrix_mem_rowStochastic`). -/
theorem sum_jumpLaw (m : ℕ) : ∑ π, jumpLaw n m π = 1 :=
  sum_row_of_mem_rowStochastic (pow_mem jumpMatrix_mem_rowStochastic m) ⊥

open scoped Classical in
/-- **Kingman's formula is a probability distribution** on the partitions with `k` blocks, for
`1 ≤ k ≤ n`. Equivalently, `∑_{π, k blocks} ∏_{B ∈ π} |B|! = n! (n - 1)! / ((n - k)! k! (k - 1)!)`,
the Lah number `L(n, k)`. -/
theorem sum_kingmanProb {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∑ π with #π.parts = k, kingmanProb n π = 1 := by
  rw [← sum_jumpLaw (n := n) (n - k), sum_filter]
  refine sum_congr rfl fun π _ => ?_
  rw [jumpLaw_eq (by omega)]
  congr 1
  apply propext
  omega

/-- Relabeling the sample by a permutation (`Finpartition.comap`) preserves Kingman's
formula. -/
theorem kingmanProb_comap_perm (σ : Equiv.Perm (Fin n)) (π : SamplePartition n) :
    kingmanProb n (π.comap σ) = kingmanProb n π := by
  rw [kingmanProb, kingmanProb, Finpartition.cardProd_comap_equiv,
    Finpartition.card_parts_comap_equiv]

/-- **Exchangeability** of the jump chain: for `m < n`, relabeling the sample does not change
the probability of a partition after `m` coalescences. -/
theorem jumpLaw_comap_perm {m : ℕ} (hm : m < n) (σ : Equiv.Perm (Fin n))
    (π : SamplePartition n) : jumpLaw n m (π.comap σ) = jumpLaw n m π := by
  rw [jumpLaw_eq hm, jumpLaw_eq hm, Finpartition.card_parts_comap_equiv, kingmanProb_comap_perm]

/-! ### The time-`t` marginal -/

/-- The number of blocks of a partition of a sample of `n`, as an element of `Fin (n + 1)` (a
state of the block-counting process). -/
def numBlocks (π : SamplePartition n) : Fin (n + 1) :=
  ⟨#π.parts, Nat.lt_succ_of_le (by simpa using π.card_parts_le_card)⟩

/-- Kingman's formula arranged by number of blocks: entry `(k, π)` is `kingmanProb n π` if `π`
has `k` blocks and `0` otherwise. For `1 ≤ k ≤ n`, row `k` is the law of the jump chain after
`n - k` jumps (`jumpLaw_eq`). -/
noncomputable def kingmanMatrix (n : ℕ) : Matrix (Fin (n + 1)) (SamplePartition n) ℝ :=
  Matrix.of fun k π => if #π.parts = (k : ℕ) then kingmanProb n π else 0

/-- Row `n` of `kingmanMatrix n` is the point mass at the partition into singletons. -/
theorem kingmanMatrix_last (π : SamplePartition n) :
    kingmanMatrix n (Fin.last n) π = if π = ⊥ then 1 else 0 := by
  simp only [kingmanMatrix, Matrix.of_apply, Fin.val_last]
  by_cases h : #π.parts = n
  · rw [ite_eq_left h, ite_eq_left (eq_bot_of_card_parts π h), eq_bot_of_card_parts π h,
      kingmanProb_bot]
  · rw [ite_eq_right h, ite_eq_right]
    rintro rfl
    exact h card_parts_bot

/-- A partition of a nonempty sample has at least one block. -/
private theorem one_le_card_parts (hn : 1 ≤ n) (π : SamplePartition n) : 1 ≤ #π.parts :=
  π.one_le_card_parts_of_nonempty (univ_nonempty_iff.2 ⟨⟨0, hn⟩⟩)

/-- **Kingman's formula intertwines the block-counting generator with the partition rate
matrix**: `G * Λ = Λ * Q`. This is the backward equation `sum_kingmanProb_isMerge` in matrix
form. -/
theorem blockCountingGenerator_mul_kingmanMatrix :
    blockCountingGenerator n * kingmanMatrix n = kingmanMatrix n * partitionRate n := by
  classical
  ext k π'
  have hlt : #π'.parts < n + 1 := Nat.lt_succ_of_le (by simpa using π'.card_parts_le_card)
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_eq_single ⟨#π'.parts, hlt⟩]
  swap
  · intro j hj
    simp only [kingmanMatrix, Matrix.of_apply]
    rw [ite_eq_right (fun hc => hj (Fin.ext hc.symm)), mul_zero]
  have hsplit : ∀ π : SamplePartition n, kingmanMatrix n k π * partitionRate n π π' =
      (if IsMerge π π' ∧ #π.parts = (k : ℕ) then kingmanProb n π else 0) +
      (if π = π' then (if #π'.parts = (k : ℕ) then
        -(((#π'.parts).choose 2 : ℕ) : ℝ) * kingmanProb n π' else 0) else 0) := by
    intro π
    simp only [kingmanMatrix, partitionRate, Matrix.of_apply]
    by_cases hM : IsMerge π π'
    · have hne : π ≠ π' := by
        rintro rfl
        have := hM.2
        omega
      simp [hM, hne]
    · by_cases he : π = π'
      · subst he
        by_cases hk : #π.parts = (k : ℕ) <;> simp [hM, hk, mul_comm]
      · simp [hM, he]
  simp_rw [hsplit]
  rw [sum_add_distrib, sum_ite_eq' univ π', ← sum_filter]
  simp only [blockCountingGenerator, kingmanMatrix, Matrix.of_apply]
  by_cases h1 : #π'.parts + 1 = (k : ℕ)
  · have hfilter : univ.filter (fun π : SamplePartition n => IsMerge π π' ∧ #π.parts = (k : ℕ))
        = univ.filter (fun π => IsMerge π π') := by
      refine filter_congr fun π _ => ?_
      refine ⟨And.left, fun hM => ⟨hM, ?_⟩⟩
      have := hM.2
      omega
    have hk : (k : ℕ) ≤ n := Nat.lt_succ_iff.1 k.isLt
    have hpos : 1 ≤ #π'.parts := one_le_card_parts (by omega) π'
    have hne : ¬#π'.parts = (k : ℕ) := by omega
    rw [hfilter, sum_kingmanProb_isMerge π' hpos (by omega), ite_eq_left h1, ite_eq_right hne,
      ← h1]
    simp
  · by_cases h2 : #π'.parts = (k : ℕ)
    · have hfilter :
          univ.filter (fun π : SamplePartition n => IsMerge π π' ∧ #π.parts = (k : ℕ)) = ∅ := by
        refine filter_eq_empty_iff.2 fun π _ hM => ?_
        have := hM.1.2
        omega
      rw [hfilter, sum_empty, ite_eq_right h1, ite_eq_left (Fin.ext h2), ite_eq_left h2, h2]
      simp
    · have hfilter :
          univ.filter (fun π : SamplePartition n => IsMerge π π' ∧ #π.parts = (k : ℕ)) = ∅ := by
        refine filter_eq_empty_iff.2 fun π _ hM => ?_
        have := hM.1.2
        omega
      rw [hfilter, sum_empty, ite_eq_right h1, ite_eq_right (fun h => h2 (congrArg Fin.val h)),
        ite_eq_right h2]
      simp

/-- **The time-`t` marginal of the partition-valued coalescent** (Kingman 1982): for
every real `t`, the probability of a partition `π` with `k` blocks is the probability that the
block-counting process goes from `n` to `k` lineages in time `t`, times Kingman's formula. -/
theorem timeLaw_eq (t : ℝ) (π : SamplePartition n) :
    timeLaw n t π =
      NormedSpace.exp (t • blockCountingGenerator n) (Fin.last n) (numBlocks π) *
        kingmanProb n π := by
  have hX : (t • blockCountingGenerator n) * kingmanMatrix n =
      kingmanMatrix n * (t • partitionRate n) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, blockCountingGenerator_mul_kingmanMatrix]
  have h := congrFun (congrFun (exp_mul_eq_mul_exp_of_mul_eq hX) (Fin.last n)) π
  rw [Matrix.mul_apply, Matrix.mul_apply] at h
  simp only [kingmanMatrix_last, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ,
    ite_true] at h
  rw [timeLaw, ← h, Fintype.sum_eq_single (numBlocks π)]
  · simp [kingmanMatrix, numBlocks]
  · intro j hj
    simp only [kingmanMatrix, Matrix.of_apply]
    rw [ite_eq_right (fun hc => hj (Fin.ext hc.symm)), mul_zero]

/-- The time-`t` marginal with Tavaré's closed form for the block-counting factor: for a
partition `π` of a sample of `n` (so `π` has at least one block when `n ≥ 1`),
`P(Π_t = π) = tavareProb n k t · kingmanProb n π` with `k = #π.parts`. -/
theorem timeLaw_eq_tavareProb (hn : 1 ≤ n) (t : ℝ) (π : SamplePartition n) :
    timeLaw n t π = tavareProb n #π.parts t * kingmanProb n π := by
  rw [timeLaw_eq, exp_blockCountingGenerator_apply n t _ _ (one_le_card_parts hn π)
    (Fin.le_last _)]
  rfl

/-- **Exchangeability** of the time-`t` marginal. -/
theorem timeLaw_comap_perm (t : ℝ) (σ : Equiv.Perm (Fin n)) (π : SamplePartition n) :
    timeLaw n t (π.comap σ) = timeLaw n t π := by
  rw [timeLaw_eq, timeLaw_eq, kingmanProb_comap_perm,
    show numBlocks (π.comap σ) = numBlocks π from
      Fin.ext (Finpartition.card_parts_comap_equiv σ π)]

/-- Each row of the partition rate matrix sums to `0`: a partition with `k` blocks has
`k.choose 2` mergers (`card_isMerge`), each at rate `1`. -/
theorem sum_partitionRate (π : SamplePartition n) : ∑ π', partitionRate n π π' = 0 := by
  classical
  have h : ∀ π', partitionRate n π π' = (if IsMerge π π' then 1 else 0) +
      (if π = π' then -(((#π.parts).choose 2 : ℕ) : ℝ) else 0) := by
    intro π'
    simp only [partitionRate, Matrix.of_apply]
    by_cases hM : IsMerge π π'
    · have hne : π ≠ π' := by
        rintro rfl
        have := hM.2
        omega
      simp [hM, hne]
    · simp [hM]
  simp_rw [h]
  rw [sum_add_distrib, sum_ite_eq, ← sum_filter, sum_const, card_isMerge]
  simp

/-- The time-`t` marginal sums to one over all partitions: `∑_π timeLaw n t π = 1` (for every
real `t`, since the rows of the rate matrix sum to `0`). -/
theorem sum_timeLaw (t : ℝ) : ∑ π, timeLaw n t π = 1 := by
  let X : Matrix (SamplePartition n) (Fin 1) ℝ := Matrix.of fun _ _ => 1
  have hX : (t • partitionRate n) * X = X * (0 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext π j
    simp only [Matrix.smul_apply, Matrix.mul_apply, X, Matrix.of_apply, mul_one, smul_eq_mul,
      mul_zero, Matrix.zero_apply, sum_const_zero]
    rw [← mul_sum, sum_partitionRate, mul_zero]
  have h := congrFun (congrFun (exp_mul_eq_mul_exp_of_mul_eq hX) ⊥) 0
  rw [NormedSpace.exp_zero, Matrix.mul_one] at h
  simpa [Matrix.mul_apply, X, timeLaw] using h

/-- Restricting the partition into singletons gives the partition into singletons. -/
private theorem comap_castSucc_bot :
    (⊥ : SamplePartition (n + 1)).comap Fin.castSucc = ⊥ := by
  refine Finpartition.ext ?_
  ext B
  simp only [Finpartition.mem_comap_parts, Finpartition.parts_bot, mem_map, mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨⟨a, ha⟩, C, ⟨x, rfl⟩, rfl⟩
    have hx : a.castSucc = x := mem_singleton.1 (mem_filter.1 ha).2
    subst hx
    exact ⟨a, by ext b; simp [eq_comm]⟩
  · rintro ⟨a, rfl⟩
    exact ⟨singleton_nonempty a, {a.castSucc}, ⟨a.castSucc, rfl⟩, by ext b; simp⟩

/-- **Lumpability of restriction** (Kingman 1982): restricting to the first `n` genes
intertwines the rate matrices of the `(n + 1)`- and `n`-coalescents. -/
theorem partitionRate_mul_restrictMatrix :
    partitionRate (n + 1) * restrictMatrix n = restrictMatrix n * partitionRate n := by
  classical
  ext π ρ
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_eq_single (π.comap Fin.castSucc)]
  swap
  · intro ρ' hρ'
    simp only [restrictMatrix, Matrix.of_apply]
    rw [ite_eq_right (Ne.symm hρ'), zero_mul]
  have hsplit : ∀ π' : SamplePartition (n + 1), partitionRate (n + 1) π π' * restrictMatrix n π' ρ =
      (if IsMerge π π' ∧ π'.comap Fin.castSucc = ρ then 1 else 0) +
      (if π = π' then (if π.comap Fin.castSucc = ρ then -(((#π.parts).choose 2 : ℕ) : ℝ) else 0)
        else 0) := by
    intro π'
    simp only [partitionRate, restrictMatrix, Matrix.of_apply]
    by_cases hM : IsMerge π π'
    · have hne : π ≠ π' := by
        rintro rfl
        have := hM.2
        omega
      by_cases hr : π'.comap Fin.castSucc = ρ <;> simp [hM, hne, hr]
    · by_cases he : π = π'
      · subst he
        by_cases hr : π.comap Fin.castSucc = ρ <;> simp [hM, hr]
      · simp [hM, he]
  simp_rw [hsplit]
  rw [sum_add_distrib, sum_ite_eq univ π, ← sum_filter, sum_const, nsmul_eq_mul, mul_one,
    card_isMerge_comap_castSucc]
  simp only [mem_univ, ite_true, restrictMatrix, partitionRate, Matrix.of_apply, one_mul]
  have hcard := card_parts_comap_castSucc π
  by_cases hM : IsMerge (π.comap Fin.castSucc) ρ
  · have hne : π.comap Fin.castSucc ≠ ρ := by
      rintro rfl
      have := hM.2
      omega
    simp [hM, hne]
  · by_cases hρ : π.comap Fin.castSucc = ρ
    · subst hρ
      simp only [hM, ite_false, ite_true, true_and, zero_add]
      by_cases hL : {Fin.last n} ∈ π.parts
      · rw [card_erase_of_mem hL] at hcard
        rw [ite_eq_left hL, hcard]
        have hk : 1 ≤ #π.parts := card_pos.2 ⟨_, hL⟩
        obtain ⟨k, hk'⟩ : ∃ k, #π.parts = k + 1 := ⟨#π.parts - 1, by omega⟩
        rw [hk', Nat.add_sub_cancel, Nat.choose_succ_succ, Nat.choose_one_right]
        push_cast
        ring
      · rw [erase_eq_of_notMem hL] at hcard
        rw [ite_eq_right hL, hcard]
        simp
    · simp [hM, hρ]

/-- **Consistency** (Kingman 1982): the time-`t` law of the restriction of the
`(n + 1)`-coalescent to the first `n` genes is the time-`t` law of the `n`-coalescent. -/
theorem sum_timeLaw_restrict (t : ℝ) (ρ : SamplePartition n) :
    ∑ π with π.comap Fin.castSucc = ρ, timeLaw (n + 1) t π = timeLaw n t ρ := by
  classical
  have hX : (t • partitionRate (n + 1)) * restrictMatrix n =
      restrictMatrix n * (t • partitionRate n) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, partitionRate_mul_restrictMatrix]
  have h := congrFun (congrFun (exp_mul_eq_mul_exp_of_mul_eq hX) ⊥) ρ
  rw [Matrix.mul_apply, Matrix.mul_apply] at h
  simp only [restrictMatrix, Matrix.of_apply, comap_castSucc_bot, mul_ite, mul_one, mul_zero,
    ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true] at h
  rw [sum_filter]
  exact h

end MathlibExt.Biology.PopulationGenetics.Coalescent.PartitionCoalescent
