/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import MathlibExt.Combinatorics.Enumerative.Stirling

/-!
# Genus of set partitions

Increasing-cycle permutations encode set partitions. For partitions into two blocks,
`twoBlock_oneFace_and_genus` counts the nontrivial face cycles and determines the genus, and
`partitionGenusCount_twoBlocks` counts the partitions into two blocks of given sizes and genus.

## Implementation notes

For `partitionGenusCount_twoBlocks`: a nonempty proper subset of `Fin n` and its complement
are the cycles of exactly one increasing-cycle permutation, and by `twoBlock_oneFace_and_genus`
its genus is one less than the number of runs of the subset, a run being a maximal set of
cyclically consecutive elements. The subsets with `p` elements and `r` runs are counted by
marking the first element of a run, rotating it to `0` and counting compositions.
-/

namespace MetaMathlibExt

@[expose] public section

open Equiv Finset

/-- **Increasing-cycle permutation.** A permutation $\tau$ of $\{0, \dots, n-1\}$ is an
increasing-cycle permutation when, for all $x$ and $y$ in $\{0, \dots, n-1\}$ such that
$\tau(x) \le x$ and $y$ lies in the same cycle of $\tau$ as $x$, we have $\tau(x) \le y$. That
is, whenever $\tau(x) \le x$, the value $\tau(x)$ is the least element of the cycle of $x$;
equivalently, each cycle of $\tau$ runs through its elements in increasing order and returns from
the largest to the least.

Set partitions of $\{0, \dots, n-1\}$ correspond bijectively to increasing-cycle permutations,
the blocks being the cycles (fixed points give singleton blocks), and partitions are counted
through this encoding.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Section 2.4 (the permutation `τ`
whose cycles are the parts, with their elements in increasing order). -/
def IsIncreasingCyclePerm {n : ℕ} (τ : Perm (Fin n)) : Prop :=
  ∀ x y, τ x ≤ x → τ.SameCycle x y → τ x ≤ y

instance {n : ℕ} : DecidablePred (IsIncreasingCyclePerm (n := n)) := fun τ => by
  unfold IsIncreasingCyclePerm
  infer_instance

/-- **Genus of a set partition.** Let $\sigma$ be the cyclic permutation $i \mapsto i + 1 \pmod n$
of $\{0, \dots, n-1\}$. For a permutation $\tau$ of $\{0, \dots, n-1\}$, thought of as encoding the
set partition whose blocks are its cycles, let $|\alpha|$ be the number of cycles of $\tau$ and $c$
the number of cycles of $\sigma \circ \tau^{-1}$, fixed points counted as cycles in both. The genus
of $\tau$ is the integer part of $\frac{1}{2} \max(0,\ n + 1 - |\alpha| - c)$.

For $n \ge 1$ the number $n + 1 - |\alpha| - c$ is nonnegative and even, so the genus is the
number $g$ with $-2g = |\alpha| - 1 - n + c$; for $n = 0$ the genus is $0$.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Section 2.4, equation (genus). -/
def setPartitionGenus {n : ℕ} (τ : Perm (Fin n)) : ℕ :=
  (n + 1 - τ.partition.parts.card - (finRotate n * τ⁻¹).partition.parts.card) / 2

/-- **Number of set partitions of given type and genus.** For natural numbers $n$ and $g$ and a
multiset $\alpha$ of natural numbers, $C_{n,[\alpha]}^{(g)}$ is the number of increasing-cycle
permutations $\tau$ of $\{0, \dots, n-1\}$ whose multiset of cycle lengths, fixed points counted
as cycles of length $1$, is $\alpha$ and whose genus is $g$.

Through the encoding of set partitions by increasing-cycle permutations, this is the number of
set partitions of $\{0, \dots, n-1\}$ of type $[\alpha]$ (multiset of block sizes $\alpha$) and
genus $g$.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Section 2.4 (the numbers
`C_{n,[α]}^{(g)}`). -/
def partitionGenusCount (n : ℕ) (α : Multiset ℕ) (g : ℕ) : ℕ :=
  #{τ : Perm (Fin n) | IsIncreasingCyclePerm τ ∧ τ.partition.parts = α ∧
    setPartitionGenus τ = g}

/-- **The identity is an increasing-cycle permutation.** For every natural number $n$, the
identity permutation of $\{0, \dots, n-1\}$ is an increasing-cycle permutation.

Its cycles are the singletons, so it encodes the partition of $\{0, \dots, n-1\}$ into
singletons.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Section 2.4. -/
theorem isIncreasingCyclePerm_one (n : ℕ) : IsIncreasingCyclePerm (1 : Perm (Fin n)) := by
  intro x y _ h
  rw [Perm.sameCycle_one] at h
  simp [h]

/-- **The partition into singletons has genus zero.** For every natural number $n$, the genus of
the identity permutation of $\{0, \dots, n-1\}$ is $0$; the identity encodes the partition of
$\{0, \dots, n-1\}$ into singletons.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Section 2.4. -/
theorem setPartitionGenus_one (n : ℕ) : setPartitionGenus (1 : Perm (Fin n)) = 0 := by
  have h : (1 : Perm (Fin n)).partition.parts.card = n := by
    simp [Perm.parts_partition]
  unfold setPartitionGenus
  rw [h]
  omega

/-- **The cyclic rotation is an increasing-cycle permutation.** For every natural number $n$,
the cyclic permutation $i \mapsto i + 1 \pmod n$ of $\{0, \dots, n-1\}$ is an increasing-cycle
permutation.

For $n \ge 1$ its only cycle is all of $\{0, \dots, n-1\}$, so it encodes the set partition with a
single block.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Section 2.4. -/
theorem isIncreasingCyclePerm_finRotate (n : ℕ) : IsIncreasingCyclePerm (finRotate n) := by
  cases n with
  | zero => intro x; exact x.elim0
  | succ m =>
    intro x y hx _
    by_cases hl : x = Fin.last m
    · subst hl
      rw [finRotate_last]
      exact Fin.zero_le y
    · exfalso
      have h1 := coe_finRotate_of_ne_last hl
      rw [Fin.le_def, h1] at hx
      omega

/-- **The one-block partition has genus zero.** For every natural number $n$, the genus of the
cyclic permutation $i \mapsto i + 1 \pmod n$ of $\{0, \dots, n-1\}$ is $0$.

For $n \ge 1$ its only cycle is all of $\{0, \dots, n-1\}$, so this says that the partition with a
single block has genus $0$.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Section 2.4 ("one-part partitions
(`k = 1`) necessarily have genus 0"). -/
theorem setPartitionGenus_finRotate (n : ℕ) : setPartitionGenus (finRotate n) = 0 := by
  have h : (finRotate n * (finRotate n)⁻¹).partition.parts.card = n := by
    simp [Perm.parts_partition]
  unfold setPartitionGenus
  rw [h]
  omega

namespace twoBlock_oneFace_and_genus

variable {n : ℕ}

/-- The first point of a block at or after the cut, wrapping to its minimum if necessary. -/
private def nextPoint (s : Finset (Fin n)) (hs : s.Nonempty) (k : ℕ) : Fin n :=
  if h : (s.filter (k ≤ ·.val)).Nonempty then (s.filter (k ≤ ·.val)).min' h else s.min' hs

private theorem nextPoint_self {s : Finset (Fin n)} {x : Fin n} (hx : x ∈ s) :
    nextPoint s ⟨x, hx⟩ x.val = x := by
  have hmem : x ∈ s.filter (x.val ≤ ·.val) := mem_filter.mpr ⟨hx, le_rfl⟩
  unfold nextPoint
  rw [dite_eq_left ⟨x, hmem⟩]
  exact le_antisymm (min'_le _ _ hmem) (mem_filter.mp (min'_mem _ _)).2

private theorem nextPoint_skip {s : Finset (Fin n)} (hs : s.Nonempty) {x : Fin n}
    (hx : x ∉ s) : nextPoint s hs (x.val + 1) = nextPoint s hs x.val := by
  have he : s.filter (x.val + 1 ≤ ·.val) = s.filter (x.val ≤ ·.val) := by
    apply filter_congr
    intro y hy
    have hne : x.val ≠ y.val := fun h => hx (Fin.ext h ▸ hy)
    omega
  simp only [nextPoint, he]

private theorem nextPoint_rotate (s : Finset (Fin n)) (hs : s.Nonempty) (x : Fin n) :
    nextPoint s hs (finRotate n x).val = nextPoint s hs (x.val + 1) := by
  cases n with
  | zero => exact x.elim0
  | succ m =>
    rw [coe_finRotate]
    split
    · rename_i h
      subst x
      have he : s.filter ((m + 1) ≤ ·.val) = ∅ := by
        apply filter_eq_empty_iff.mpr
        intro y _
        exact Nat.not_le_of_lt y.isLt
      change nextPoint s hs 0 = nextPoint s hs (m + 1)
      simp only [nextPoint, he, Finset.not_nonempty_empty, dite_false, Nat.zero_le, filter_true,
        hs, dite_true]
    · rfl

-- Within a block the successor of x is its first point strictly after x, cyclically.
private theorem nextPoint_succ {τ : Perm (Fin n)} (hτ : IsIncreasingCyclePerm τ)
    {s : Finset (Fin n)} (hs : s.Nonempty)
    (hcycle : ∀ x ∈ s, ∀ y, y ∈ s ↔ τ.SameCycle x y) (x : Fin n) (hx : x ∈ s) :
    nextPoint s hs (x.val + 1) = τ x := by
  induction x using WellFoundedLT.induction with
  | ind x ih =>
    have hmem (y : Fin n) (hy : y ∈ s) : τ y ∈ s :=
      (hcycle y hy _).2 (Perm.SameCycle.rfl.apply_right)
    unfold nextPoint
    split
    · rename_i hn
      let y := (s.filter (x.val + 1 ≤ ·.val)).min' hn
      have hy := mem_filter.mp ((s.filter (x.val + 1 ≤ ·.val)).min'_mem hn)
      change y ∈ s ∧ x.val + 1 ≤ y.val at hy
      let z := τ.symm y
      have hz : τ z = y := τ.apply_symm_apply y
      have hzs : z ∈ s := (hcycle y hy.1 _).2 Perm.SameCycle.rfl.symm_apply_right
      have hzy : z < y := by
        by_contra! h
        have hle := hτ z x (hz.symm ▸ h) ((hcycle z hzs x).mp hx)
        rw [hz] at hle
        exact (Nat.not_le_of_lt hy.2) hle
      have hzx : z ≤ x := by
        by_contra! h
        exact hzy.not_ge (min'_le _ z (mem_filter.mpr ⟨hzs, h⟩))
      obtain he | hlt := hzx.eq_or_lt
      · exact hz.symm.trans (congrArg τ he)
      · have hi := ih z hlt hzs
        have hxf : x ∈ s.filter (z.val + 1 ≤ ·.val) := mem_filter.mpr ⟨hx, hlt⟩
        unfold nextPoint at hi
        rw [dite_eq_left ⟨x, hxf⟩, hz] at hi
        have hle := min'_le _ x hxf
        rw [hi] at hle
        exact (Nat.not_le_of_lt hy.2 hle).elim
    · rename_i hn
      have hle : τ x ≤ x := by
        by_contra! h
        exact hn ⟨τ x, mem_filter.mpr ⟨hmem _ hx, h⟩⟩
      exact le_antisymm (min'_le _ _ (hmem _ hx))
        (hτ _ _ hle ((hcycle x hx _).mp (min'_mem _ _)))

-- Label the two cycle classes by the two Booleans.
private theorem exists_coloring {τ : Perm (Fin n)} (h2 : τ.partition.parts.card = 2) :
    ∃ c : Fin n → Bool, Function.Surjective c ∧ ∀ x y, τ.SameCycle x y ↔ c x = c y := by
  classical
  have hcard : Fintype.card (Quotient (Perm.SameCycle.setoid τ)) = 2 := by
    rw [← Nat.card_eq_fintype_card]
    change cycleQuotientCount τ = 2
    simpa only [cycleQuotientCount_eq, Perm.card_fixedPoints, Perm.sum_cycleType,
      Perm.parts_partition, Multiset.card_add, Multiset.card_replicate] using h2
  let e := (Fintype.equivFinOfCardEq hcard).trans finTwoEquiv
  exact ⟨e ∘ Quotient.mk _, e.surjective.comp Quotient.mk_surjective,
    fun _ _ => Quotient.eq.symm.trans e.injective.eq_iff.symm⟩

private theorem rotate_induction [NeZero n] {P : Fin n → Prop} (h0 : P 0)
    (h : ∀ i, P i → P (finRotate n i)) (i : Fin n) : P i := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
    induction i using Fin.induction with
    | zero => exact h0
    | succ i ih =>
      have he : finRotate (m + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
      exact he ▸ h i.castSucc ih

private theorem face_orbit [NeZero n] {τ : Perm (Fin n)} (hτ : IsIncreasingCyclePerm τ)
    (c : Fin n → Bool) (hc : Function.Surjective c) (hclass : ∀ x y, τ.SameCycle x y ↔ c x = c y) :
    let φ := finRotate n * τ⁻¹
    φ.IsCycle ∧ ∀ x ∈ φ.support, c (φ x) = !c x := by
  let σ := finRotate n
  let φ := σ * τ⁻¹
  have hφ (i) : φ (τ i) = σ i := by simp [φ]
  have hcolor (i) : c (τ i) = c i := ((hclass i _).mp Perm.SameCycle.rfl.apply_right).symm
  let block (b : Bool) : Finset (Fin n) := univ.filter (fun i => c i = b)
  have mem_block (b i) : i ∈ block b ↔ c i = b := by simp [block]
  have inhabited (b) : (block b).Nonempty := by
    obtain ⟨i, hi⟩ := hc b
    exact ⟨i, (mem_block b i).2 hi⟩
  let nextIn (b : Bool) (i : Fin n) := nextPoint (block b) (inhabited b) i.val
  have self (i) : nextIn (c i) i = i := nextPoint_self ((mem_block _ _).2 rfl)
  have step (b i) : nextIn b (σ i) = if c i = b then τ i else nextIn b i := by
    dsimp only [nextIn, σ]
    rw [nextPoint_rotate]
    split
    · rename_i hi
      apply nextPoint_succ hτ _ _ _ ((mem_block _ _).2 hi)
      intro x hx y
      rw [mem_block, hclass, (mem_block _ _).mp hx, eq_comm]
    · rename_i hi
      exact nextPoint_skip _ (fun h => hi ((mem_block _ _).mp h))
  -- The first point of the opposite block stays put until the cut changes blocks.
  -- At such a change the face permutation takes the new point back to the old one.
  let other (i : Fin n) := nextIn (!c i) i
  have adjacent (i) : φ.SameCycle (other i) (other (σ i)) ∧
      (φ (τ i) ≠ τ i → other i = σ i ∧ c (σ i) = !c i) := by
    by_cases hi : c (σ i) = c i
    · have he : nextIn (c i) (σ i) = σ i := hi ▸ self (σ i)
      rw [step, ite_eq_left rfl] at he
      have ho : other (σ i) = other i := by simp [other, hi, step]
      exact ⟨ho.symm.sameCycle φ, fun h => (h ((hφ i).trans he.symm)).elim⟩
    · have hnot := Bool.eq_not_of_ne hi
      have he : nextIn (!c i) (σ i) = σ i := hnot ▸ self (σ i)
      have hold : other i = σ i := by simpa [step] using he
      have hnew : other (σ i) = τ i := by simp [other, hnot, step]
      refine ⟨?_, fun _ => ⟨hold, hnot⟩⟩
      rw [hold, hnew, ← hφ]
      exact Perm.SameCycle.rfl.apply_left
  have connected (i) : φ.SameCycle (other 0) (other i) :=
    rotate_induction (P := fun j => φ.SameCycle (other 0) (other j)) Perm.SameCycle.rfl
      (fun j h => h.trans (adjacent j).1) i
  have moved (x) (hx : φ x ≠ x) : φ.SameCycle (other 0) x ∧ c (φ x) = !c x := by
    obtain ⟨i, rfl⟩ := τ.surjective x
    obtain ⟨hold, hnot⟩ := (adjacent i).2 hx
    have he := connected i
    rw [hold, ← hφ] at he
    exact ⟨he.of_apply_right, by rw [hφ, hnot, hcolor]⟩
  have boundary : ∃ i, c (σ i) ≠ c i := by
    by_contra! he
    obtain ⟨j, hj⟩ := hc (!c 0)
    have : c j = c 0 :=
      rotate_induction (P := fun k => c k = c 0) rfl (fun i hi => (he i).trans hi) j
    simp [this] at hj
  obtain ⟨i, hi⟩ := boundary
  have hmove : φ (τ i) ≠ τ i := by
    intro he
    exact hi ((congrArg c ((hφ i).symm.trans he)).trans (hcolor i))
  refine ⟨⟨τ i, hmove, fun {y} hy => (moved _ hmove).1.symm.trans (moved _ hy).1⟩, ?_⟩
  exact fun x hx => (moved x (Perm.mem_support.mp hx)).2

end twoBlock_oneFace_and_genus

open twoBlock_oneFace_and_genus

/-- **Genus of two-block partitions.** Let $\sigma$ be the cyclic permutation
$i \mapsto i + 1 \pmod n$ of $\{0, \dots, n-1\}$, and let $\tau$ be an increasing-cycle permutation
of $\{0, \dots, n-1\}$ with exactly two cycles, fixed points counted as cycles (so $\tau$ encodes a
set partition into two blocks). Then $\sigma \circ \tau^{-1}$ has exactly one cycle of length at
least $2$. Moreover, for every $x_0$ in $\{0, \dots, n-1\}$, if $B$ is the cycle of $\tau$
containing $x_0$ and $s$ is the number of elements of $B$ fixed by $\sigma \circ \tau^{-1}$, then
the genus $g$ of $\tau$ satisfies $g + 1 + s = |B|$.

Taking $x_0$ in each of the two blocks, of sizes $p$ and $n - p$, and writing $s_1$ and $s_2$ for
the corresponding values of $s$, gives $g = p - s_1 - 1 = (n - p) - s_2 - 1$.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Lemma 13
(`jis-2024-24.2.6-lem-13`). -/
theorem twoBlock_oneFace_and_genus {n : ℕ} (τ : Perm (Fin n))
    (hτ : IsIncreasingCyclePerm τ) (h2 : τ.partition.parts.card = 2) (x₀ : Fin n) :
    (finRotate n * τ⁻¹).cycleType.card = 1 ∧
      setPartitionGenus τ + 1 + #{x | τ.SameCycle x₀ x ∧ (finRotate n * τ⁻¹) x = x} =
        #{x | τ.SameCycle x₀ x} := by
  let := x₀.neZero
  obtain ⟨c, hc, hclass⟩ := exists_coloring h2
  let φ := finRotate n * τ⁻¹
  obtain ⟨hcycle, hflip⟩ := face_orbit hτ c hc hclass
  change φ.IsCycle at hcycle
  change ∀ x ∈ φ.support, c (φ x) = !c x at hflip
  have hone : φ.cycleType.card = 1 := Perm.card_cycleType_eq_one.mpr hcycle
  refine ⟨hone, ?_⟩
  let B := fun x => c x = c x₀
  have hequal : #(φ.support.filter B) = #(φ.support.filter fun x => ¬ B x) := by
    apply card_bijective φ φ.bijective
    intro x
    simp only [mem_filter, Perm.apply_mem_support]
    refine and_congr_right fun hx => ?_
    simp [B, hflip x hx]
  have hdouble := card_filter_add_card_filter_not (s := φ.support) B
  rw [← hequal] at hdouble
  have hblock := card_filter_add_card_filter_not (s := univ.filter B) (fun x => φ x ≠ x)
  have hmoved : (univ.filter B).filter (fun x => φ x ≠ x) = φ.support.filter B := by
    ext x
    simp [and_comm]
  rw [hmoved] at hblock
  simp only [filter_filter, not_not] at hblock
  have hpos := hcycle.nonempty_support.card_pos
  have hle : #φ.support ≤ n := by simpa using card_le_univ φ.support
  change setPartitionGenus τ + 1 + #{x | τ.SameCycle x₀ x ∧ φ x = x} =
    #{x | τ.SameCycle x₀ x}
  have hB (x) : τ.SameCycle x₀ x ↔ B x := (hclass _ _).trans eq_comm
  simp_rw [hB]
  change (n + 1 - τ.partition.parts.card - φ.partition.parts.card) / 2 +
    1 + #{x | B x ∧ φ x = x} = #(univ.filter B)
  rw [h2, Perm.parts_partition, Multiset.card_add, Multiset.card_replicate, Fintype.card_fin, hone]
  omega

namespace partitionGenusCount_twoBlocks

/-! ### Subsets of a cycle counted by their runs -/

/-- The number of compositions of `m` into `k` positive parts. -/
private def compCount : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | m + 1, k + 1 => m.choose k

private theorem compCount_succ_succ (m k : ℕ) :
    compCount (m + 1) (k + 1) = compCount m (k + 1) + compCount m k := by
  rcases m with _ | m <;> rcases k with _ | k <;>
    simp [compCount, Nat.choose_succ_succ', add_comm]

/-- The number of maximal runs of consecutive numbers in a finite set of natural numbers. -/
private def linRuns (C : Finset ℕ) : ℕ := #{x ∈ C | x = 0 ∨ x - 1 ∉ C}

private theorem linRuns_insert {n : ℕ} {C : Finset ℕ} (hC : C ⊆ range (n + 1)) :
    linRuns (insert (n + 1) C) = linRuns C + if n ∈ C then 0 else 1 := by
  have hn : n + 1 ∉ C := fun h => by simpa using hC h
  have hfilter : {x ∈ C | x = 0 ∨ x - 1 ∉ insert (n + 1) C} = {x ∈ C | x = 0 ∨ x - 1 ∉ C} := by
    refine filter_congr fun x hx => ?_
    have hx' := mem_range.mp (hC hx)
    have : x - 1 ≠ n + 1 := by omega
    simp [this]
  unfold linRuns
  rw [filter_insert, hfilter]
  by_cases h : n ∈ C
  · simp [h]
  · simp [h, card_insert_of_notMem (show n + 1 ∉ {x ∈ C | x = 0 ∨ x - 1 ∉ C} by simp [hn])]

/-- The number of subsets of `{0, …, n}` that contain `0`, have `p` elements and `r` runs, and
contain `n` exactly when `b` holds. -/
private def linCount (n p r : ℕ) (b : Bool) : ℕ :=
  #{C ∈ (range (n + 1)).powerset | 0 ∈ C ∧ (n ∈ C ↔ b = true) ∧ #C = p ∧ linRuns C = r}

private theorem linCount_succ_false (n p r : ℕ) :
    linCount (n + 1) p r false = linCount n p r true + linCount n p r false := by
  simp only [linCount, card_filter]
  rw [range_add_one (n := n + 1), sum_powerset_insert (by simp), ← sum_add_distrib,
    ← sum_add_distrib]
  refine sum_congr rfl fun t ht => ?_
  have hn : n + 1 ∉ t := fun h => by simpa using mem_powerset.1 ht h
  by_cases h : n ∈ t <;> simp [h, hn]

private theorem linCount_succ_true (n p r : ℕ) :
    linCount (n + 1) (p + 1) (r + 1) true = linCount n p (r + 1) true + linCount n p r false := by
  simp only [linCount, card_filter]
  rw [range_add_one (n := n + 1), sum_powerset_insert (by simp), ← sum_add_distrib,
    ← sum_add_distrib]
  refine sum_congr rfl fun t ht => ?_
  have ht' := mem_powerset.1 ht
  have hn : n + 1 ∉ t := fun h => by simpa using ht' h
  by_cases h : n ∈ t <;> simp [linRuns_insert ht', card_insert_of_notMem hn, h, hn]

private theorem linCount_zero_runs (n p : ℕ) (b : Bool) : linCount n p 0 b = 0 := by
  refine card_eq_zero.mpr (filter_eq_empty_iff.mpr fun C _ h => ?_)
  have h0 : 0 ∈ {x ∈ C | x = 0 ∨ x - 1 ∉ C} := mem_filter.mpr ⟨h.1, Or.inl rfl⟩
  exact (card_pos.mpr ⟨0, h0⟩).ne' h.2.2.2

private theorem linCount_zero_left (n r : ℕ) (b : Bool) : linCount n 0 r b = 0 := by
  refine card_eq_zero.mpr (filter_eq_empty_iff.mpr fun C _ h => ?_)
  exact (card_pos.mpr ⟨0, h.1⟩).ne' h.2.2.1

private theorem linCount_eq_zero_of_lt {n p : ℕ} (h : n + 1 < p) (r : ℕ) (b : Bool) :
    linCount n p r b = 0 := by
  refine card_eq_zero.mpr (filter_eq_empty_iff.mpr fun C hC hP => ?_)
  have hle := card_le_card (mem_powerset.1 hC)
  rw [card_range] at hle
  have := hP.2.2.1
  omega

private theorem linCount_eq (n : ℕ) : ∀ a ≤ n, ∀ k : ℕ,
    linCount n (a + 1) (k + 1) false = a.choose k * compCount (n - a) (k + 1) ∧
      linCount n (a + 1) (k + 1) true = a.choose k * compCount (n - a) k := by
  induction n with
  | zero =>
    intro a ha k
    obtain rfl : a = 0 := by omega
    refine ⟨?_, ?_⟩
    · refine (card_eq_zero.mpr (filter_eq_empty_iff.mpr fun C _ h => ?_)).trans
        (by simp [compCount])
      exact Bool.false_ne_true (h.2.1.mp h.1)
    · rcases k with _ | k
      · decide
      · refine (card_eq_zero.mpr (filter_eq_empty_iff.mpr fun C hC h => ?_)).trans (by simp)
        have h1 : linRuns C ≤ 1 :=
          (card_filter_le _ _).trans (h.2.2.1.le)
        have := h.2.2.2
        omega
  | succ n ih =>
    intro a ha k
    refine ⟨?_, ?_⟩
    · rw [linCount_succ_false]
      rcases Nat.lt_or_ge n a with h | h
      · obtain rfl : a = n + 1 := by omega
        rw [linCount_eq_zero_of_lt (by omega), linCount_eq_zero_of_lt (by omega)]
        simp [compCount]
      · rw [(ih a h k).1, (ih a h k).2, ← mul_add, show n + 1 - a = n - a + 1 by omega,
          compCount_succ_succ, add_comm (compCount (n - a) k)]
    · rcases a with _ | a
      · rw [linCount_succ_true, linCount_zero_left, linCount_zero_left]
        rcases k with _ | k <;> simp [compCount]
      · rw [linCount_succ_true, show n + 1 - (a + 1) = n - a by omega]
        rcases k with _ | k
        · rw [linCount_zero_runs, add_zero, (ih a (by omega) 0).2]
          simp
        · rw [(ih a (by omega) (k + 1)).2, (ih a (by omega) k).1, Nat.choose_succ_succ' a k]
          ring

/-- Translating a subset of `Fin (m + 1)` preserves its number of cyclic runs. -/
private theorem card_runs_map {m : ℕ} (e : Fin (m + 1) ≃ Fin (m + 1))
    (he : ∀ x, e (x - 1) = e x - 1) (A : Finset (Fin (m + 1))) :
    #{x ∈ A.map e.toEmbedding | x - 1 ∉ A.map e.toEmbedding} = #{x ∈ A | x - 1 ∉ A} := by
  rw [filter_map, card_map]
  congr 1
  refine filter_congr fun x _ => ?_
  simp [← he]

private theorem card_runs_start {m : ℕ} (p r : ℕ) (j : Fin (m + 1)) :
    #{A : Finset (Fin (m + 1)) | (#A = p ∧ #{x ∈ A | x - 1 ∉ A} = r) ∧ j ∈ A ∧ j - 1 ∉ A} =
      #{A : Finset (Fin (m + 1)) | (#A = p ∧ #{x ∈ A | x - 1 ∉ A} = r) ∧ 0 ∈ A ∧ -1 ∉ A} := by
  let e : Fin (m + 1) ≃ Fin (m + 1) := Equiv.addRight j
  symm
  rw [← card_map e.finsetCongr.toEmbedding]
  congr 1
  ext B
  have he (x : Fin (m + 1)) : e.symm (x - 1) = e.symm x - 1 := by
    simp only [e, Equiv.addRight_symm, Equiv.coe_addRight]
    exact (add_sub_right_comm _ _ _).symm
  rw [mem_map_equiv, mem_filter, mem_filter, Equiv.finsetCongr_symm, Equiv.finsetCongr_apply,
    card_map, card_runs_map e.symm he]
  simp [e, neg_add_eq_sub]

private theorem card_runs_linear (m p r : ℕ) :
    #{A : Finset (Fin (m + 1)) | (#A = p ∧ #{x ∈ A | x - 1 ∉ A} = r) ∧ 0 ∈ A ∧ -1 ∉ A} =
      linCount m p r false := by
  have hmem (A : Finset (Fin (m + 1))) (y : Fin (m + 1)) :
      (y : ℕ) ∈ A.map Fin.valEmbedding ↔ y ∈ A := mem_map' Fin.valEmbedding
  have key (A : Finset (Fin (m + 1))) :
      ((#A = p ∧ #{x ∈ A | x - 1 ∉ A} = r) ∧ 0 ∈ A ∧ -1 ∉ A) ↔
        (0 ∈ A.map Fin.valEmbedding ∧ (m ∈ A.map Fin.valEmbedding ↔ false = true) ∧
          #(A.map Fin.valEmbedding) = p ∧ linRuns (A.map Fin.valEmbedding) = r) := by
    have h0 : 0 ∈ A.map Fin.valEmbedding ↔ (0 : Fin (m + 1)) ∈ A := hmem A 0
    have hm : m ∈ A.map Fin.valEmbedding ↔ (-1 : Fin (m + 1)) ∈ A := by
      rw [← hmem A (-1), Fin.coe_neg_one]
    have hruns (h0A : (0 : Fin (m + 1)) ∈ A) (h1A : (-1 : Fin (m + 1)) ∉ A) :
        linRuns (A.map Fin.valEmbedding) = #{x ∈ A | x - 1 ∉ A} := by
      unfold linRuns
      rw [filter_map, card_map]
      congr 1
      refine filter_congr fun x _ => ?_
      simp only [Function.comp_apply, Fin.valEmbedding_apply]
      by_cases hx0 : x = 0
      · subst hx0
        simp [h1A]
      · rw [← Fin.val_sub_one_of_ne_zero hx0, hmem]
        simp [Fin.val_eq_zero_iff, hx0]
    rw [h0, hm, card_map]
    constructor
    · rintro ⟨⟨hp, hr⟩, h0A, h1A⟩
      exact ⟨h0A, by simpa using h1A, hp, (hruns h0A h1A).trans hr⟩
    · rintro ⟨h0A, h1A, hp, hr⟩
      have h1A' : (-1 : Fin (m + 1)) ∉ A := by simpa using h1A
      exact ⟨⟨hp, (hruns h0A h1A').symm.trans hr⟩, h0A, h1A'⟩
  unfold linCount
  refine card_bij (fun A _ => A.map Fin.valEmbedding) (fun A hA => ?_)
    (fun A _ B _ h => map_injective _ h) (fun C hC => ?_)
  · rw [mem_filter] at hA ⊢
    refine ⟨mem_powerset.2 fun y hy => ?_, (key A).1 hA.2⟩
    obtain ⟨x, _, rfl⟩ := mem_map.1 hy
    exact mem_range.2 x.isLt
  · rw [mem_filter, mem_powerset] at hC
    have hAC : (univ.filter fun x : Fin (m + 1) => (x : ℕ) ∈ C).map Fin.valEmbedding = C := by
      ext y
      simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hy
        exact ⟨⟨y, mem_range.1 (hC.1 hy)⟩, hy, rfl⟩
    refine ⟨univ.filter fun x : Fin (m + 1) => (x : ℕ) ∈ C,
      mem_filter.2 ⟨mem_univ _, (key _).2 ?_⟩, hAC⟩
    rw [hAC]
    exact hC.2

private theorem card_cyclicRuns (m p r : ℕ) (hp : 0 < p) (hpm : p ≤ m) (hr : 0 < r) :
    r * #{A : Finset (Fin (m + 1)) | #A = p ∧ #{x ∈ A | x - 1 ∉ A} = r} =
      (m + 1) * ((p - 1).choose (r - 1) * (m - p).choose (r - 1)) := by
  obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  set S : Finset (Finset (Fin (m + 1))) := {A | #A = a + 1 ∧ #{x ∈ A | x - 1 ∉ A} = k + 1}
    with hS
  have h1 (A : Finset (Fin (m + 1))) : #{x ∈ A | x - 1 ∉ A} = #{x | x ∈ A ∧ x - 1 ∉ A} := by
    congr 1
    ext x
    simp
  have hdouble : ∑ A ∈ S, #{x | x ∈ A ∧ x - 1 ∉ A} =
      ∑ x : Fin (m + 1), #{A ∈ S | x ∈ A ∧ x - 1 ∉ A} := by
    simp only [card_filter]
    exact sum_comm
  have hsum1 : ∑ A ∈ S, #{x | x ∈ A ∧ x - 1 ∉ A} = #S * (k + 1) :=
    sum_const_nat fun A hA => by
      rw [← h1]
      exact (mem_filter.1 hA).2.2
  have hsum2 : ∑ x : Fin (m + 1), #{A ∈ S | x ∈ A ∧ x - 1 ∉ A} =
      (m + 1) * linCount m (a + 1) (k + 1) false := by
    rw [sum_congr rfl fun x _ => by rw [hS, filter_filter, card_runs_start, card_runs_linear],
      sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  rw [mul_comm, ← hsum1, hdouble, hsum2, (linCount_eq m a (by omega) k).1,
    show m - a = m - (a + 1) + 1 by omega]
  simp [compCount]

/-! ### Two-block partitions as subsets -/

variable {n : ℕ}

private theorem nextPoint_mem (s : Finset (Fin n)) (hs : s.Nonempty) (k : ℕ) :
    nextPoint s hs k ∈ s := by
  unfold nextPoint
  split
  · exact (mem_filter.mp (min'_mem _ _)).1
  · exact min'_mem _ _

private theorem nextPoint_of_nonempty {s : Finset (Fin n)} (hs : s.Nonempty) {k : ℕ}
    (h : (s.filter (k ≤ ·.val)).Nonempty) :
    nextPoint s hs k = (s.filter (k ≤ ·.val)).min' h := by
  unfold nextPoint
  rw [dite_eq_left h]

private theorem nextPoint_of_not_nonempty {s : Finset (Fin n)} (hs : s.Nonempty) {k : ℕ}
    (h : ¬(s.filter (k ≤ ·.val)).Nonempty) : nextPoint s hs k = s.min' hs := by
  unfold nextPoint
  rw [dite_eq_right h]

private theorem nextPoint_congr {s t : Finset (Fin n)} (h : s = t) (hs : s.Nonempty)
    (ht : t.Nonempty) (k : ℕ) : nextPoint s hs k = nextPoint t ht k := by
  subst h
  rfl

-- Two increasing-cycle permutations with the same cycles are equal.
private theorem eq_of_sameCycle_iff {τ τ' : Perm (Fin n)} (hτ : IsIncreasingCyclePerm τ)
    (hτ' : IsIncreasingCyclePerm τ') (h : ∀ x y, τ.SameCycle x y ↔ τ'.SameCycle x y) :
    τ = τ' := by
  ext x : 1
  let s : Finset (Fin n) := {y | τ.SameCycle x y}
  have hx : x ∈ s := mem_filter.mpr ⟨mem_univ _, Perm.SameCycle.refl τ x⟩
  have hcycle (z : Fin n) (hz : z ∈ s) (y : Fin n) : y ∈ s ↔ τ.SameCycle z y := by
    simp only [s, mem_filter, mem_univ, true_and] at hz ⊢
    exact ⟨hz.symm.trans, hz.trans⟩
  rw [← nextPoint_succ hτ ⟨x, hx⟩ hcycle x hx,
    ← nextPoint_succ hτ' ⟨x, hx⟩ (fun z hz y => (hcycle z hz y).trans (h z y)) x hx]

/-- The block of `x` in the partition of `Fin n` into `A` and its complement. -/
private def block (A : Finset (Fin n)) (x : Fin n) : Finset (Fin n) := {y | y ∈ A ↔ x ∈ A}

private theorem mem_block {A : Finset (Fin n)} {x y : Fin n} :
    y ∈ block A x ↔ (y ∈ A ↔ x ∈ A) := by
  simp [block]

private theorem mem_block_self (A : Finset (Fin n)) (x : Fin n) : x ∈ block A x :=
  mem_block.mpr Iff.rfl

private theorem block_nonempty (A : Finset (Fin n)) (x : Fin n) : (block A x).Nonempty :=
  ⟨x, mem_block_self A x⟩

private theorem block_eq {A : Finset (Fin n)} {x y : Fin n} (h : y ∈ block A x) :
    block A y = block A x := by
  ext z
  rw [mem_block, mem_block, mem_block.mp h]

/-- The successor of `x` in its block: the next point of the block, cyclically. -/
private def succFun (A : Finset (Fin n)) (x : Fin n) : Fin n :=
  nextPoint (block A x) (block_nonempty A x) (x.val + 1)

private theorem succFun_mem (A : Finset (Fin n)) (x : Fin n) : succFun A x ∈ block A x :=
  nextPoint_mem _ _ _

private theorem succFun_eq (A : Finset (Fin n)) (x : Fin n) {s : Finset (Fin n)}
    (hs : s.Nonempty) (h : block A x = s) : succFun A x = nextPoint s hs (x.val + 1) := by
  unfold succFun
  subst h
  rfl

private theorem nextPoint_succ_ne {s : Finset (Fin n)} (hs : s.Nonempty) {x y : Fin n}
    (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y) :
    nextPoint s hs (x.val + 1) ≠ nextPoint s hs (y.val + 1) := by
  have hyf : y ∈ s.filter (x.val + 1 ≤ ·.val) := mem_filter.mpr ⟨hy, hxy⟩
  rw [nextPoint_of_nonempty hs ⟨y, hyf⟩]
  have hle := Fin.le_def.mp (min'_le _ _ hyf)
  have hge := (mem_filter.mp (min'_mem _ ⟨y, hyf⟩)).2
  intro he
  by_cases hn : (s.filter (y.val + 1 ≤ ·.val)).Nonempty
  · have h1 := (mem_filter.mp (min'_mem _ hn)).2
    rw [nextPoint_of_nonempty hs hn] at he
    rw [← he] at h1
    omega
  · rw [nextPoint_of_not_nonempty hs hn] at he
    have h1 := Fin.le_def.mp (min'_le s x hx)
    rw [← he] at h1
    omega

private theorem succFun_injective (A : Finset (Fin n)) : Function.Injective (succFun A) := by
  have key (x y : Fin n) (hxy : x < y) (he : succFun A x = succFun A y) : False := by
    have h1 := succFun_mem A x
    rw [he] at h1
    have hb : block A y = block A x := (block_eq (succFun_mem A y)).symm.trans (block_eq h1)
    have hy : y ∈ block A x := hb ▸ mem_block_self A y
    refine nextPoint_succ_ne (block_nonempty A x) (mem_block_self A x) hy hxy ?_
    exact he.trans (succFun_eq A y _ hb)
  intro x y he
  rcases lt_trichotomy x y with h | h | h
  · exact (key x y h he).elim
  · exact h
  · exact (key y x h he.symm).elim

/-- The increasing-cycle permutation whose cycles are `A` and its complement. -/
private noncomputable def twoBlockPerm (A : Finset (Fin n)) : Perm (Fin n) :=
  Equiv.ofBijective (succFun A) (Finite.injective_iff_bijective.mp (succFun_injective A))

private theorem twoBlockPerm_apply (A : Finset (Fin n)) (x : Fin n) :
    twoBlockPerm A x = succFun A x := rfl

private theorem twoBlockPerm_mem_iff (A : Finset (Fin n)) (x : Fin n) :
    twoBlockPerm A x ∈ A ↔ x ∈ A :=
  mem_block.mp (succFun_mem A x)

private theorem pow_apply_mem_iff (A : Finset (Fin n)) (x : Fin n) (i : ℕ) :
    (twoBlockPerm A ^ i) x ∈ A ↔ x ∈ A := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', Perm.mul_apply, twoBlockPerm_mem_iff, ih]

private theorem mem_iff_of_sameCycle {A : Finset (Fin n)} {x y : Fin n}
    (h : (twoBlockPerm A).SameCycle x y) : x ∈ A ↔ y ∈ A := by
  obtain ⟨i, rfl⟩ := h.exists_nat_pow_eq
  exact (pow_apply_mem_iff A x i).symm

private theorem sameCycle_min' (A : Finset (Fin n)) (x y : Fin n) (hy : y ∈ block A x) :
    (twoBlockPerm A).SameCycle ((block A x).min' (block_nonempty A x)) y := by
  induction y using WellFoundedLT.induction with
  | ind y ih =>
    obtain hmin | hlt := (min'_le (block A x) y hy).eq_or_lt
    · rw [hmin]
    · let t := (block A x).filter (· < y)
      have ht : t.Nonempty :=
        ⟨_, mem_filter.mpr ⟨min'_mem (block A x) (block_nonempty A x), hlt⟩⟩
      have hw := mem_filter.mp (max'_mem t ht)
      have hstep : twoBlockPerm A (t.max' ht) = y := by
        rw [twoBlockPerm_apply, succFun_eq A _ (block_nonempty A x) (block_eq hw.1)]
        have hyf : y ∈ (block A x).filter ((t.max' ht).val + 1 ≤ ·.val) :=
          mem_filter.mpr ⟨hy, hw.2⟩
        rw [nextPoint_of_nonempty _ ⟨y, hyf⟩]
        refine le_antisymm (min'_le _ _ hyf) (le_min' _ _ _ fun z hz => ?_)
        obtain ⟨hzs, hzw⟩ := mem_filter.mp hz
        by_contra! hzy
        have h1 := Fin.le_def.mp (le_max' t z (mem_filter.mpr ⟨hzs, hzy⟩))
        omega
      rw [← hstep]
      exact (ih _ hw.2 hw.1).apply_right

private theorem twoBlockPerm_sameCycle_iff (A : Finset (Fin n)) (x y : Fin n) :
    (twoBlockPerm A).SameCycle x y ↔ (x ∈ A ↔ y ∈ A) := by
  refine ⟨mem_iff_of_sameCycle, fun h => ?_⟩
  exact (sameCycle_min' A x x (mem_block_self A x)).symm.trans
    (sameCycle_min' A x y (mem_block.mpr h.symm))

private theorem isIncreasingCyclePerm_twoBlockPerm (A : Finset (Fin n)) :
    IsIncreasingCyclePerm (twoBlockPerm A) := by
  intro x y hle hxy
  have hy : y ∈ block A x := mem_block.mpr (mem_iff_of_sameCycle hxy).symm
  rw [twoBlockPerm_apply, succFun_eq A x (block_nonempty A x) rfl] at hle ⊢
  by_cases hn : ((block A x).filter (x.val + 1 ≤ ·.val)).Nonempty
  · rw [nextPoint_of_nonempty _ hn] at hle
    have h1 := (mem_filter.mp (min'_mem _ hn)).2
    have h2 := Fin.le_def.mp hle
    omega
  · rw [nextPoint_of_not_nonempty _ hn]
    exact min'_le _ _ hy

private theorem card_parts_eq_cycleQuotientCount (τ : Perm (Fin n)) :
    τ.partition.parts.card = cycleQuotientCount τ := by
  simp only [cycleQuotientCount_eq, Perm.card_fixedPoints, Perm.sum_cycleType,
    Perm.parts_partition, Multiset.card_add, Multiset.card_replicate]

private theorem card_parts_eq_two_of_blocks {τ : Perm (Fin n)} {A : Finset (Fin n)}
    (hR : ∀ x y, τ.SameCycle x y ↔ (x ∈ A ↔ y ∈ A)) {a b : Fin n} (ha : a ∈ A) (hb : b ∉ A) :
    τ.partition.parts.card = 2 := by
  rw [card_parts_eq_cycleQuotientCount, cycleQuotientCount]
  let f : Quotient (Perm.SameCycle.setoid τ) → Bool :=
    Quotient.lift (fun x => decide (x ∈ A)) fun x y h => by
      simpa using (hR x y).mp h
  have hf : Function.Bijective f := by
    constructor
    · intro u v huv
      induction u using Quotient.inductionOn
      induction v using Quotient.inductionOn
      exact Quotient.sound ((hR _ _).mpr (by simpa [f] using huv))
    · intro c
      cases c
      · exact ⟨Quotient.mk _ b, by simp [f, hb]⟩
      · exact ⟨Quotient.mk _ a, by simp [f, ha]⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_bool]

private theorem card_sameCycle_mem_parts (τ : Perm (Fin n)) (x : Fin n) :
    #{y | τ.SameCycle x y} ∈ τ.partition.parts := by
  rw [Perm.parts_partition, Multiset.mem_add]
  by_cases hx : τ x = x
  · right
    have he : ({y | τ.SameCycle x y} : Finset (Fin n)) = {x} := by
      ext y
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      exact ⟨fun h => (h.eq_of_left hx).symm, fun h => h ▸ Perm.SameCycle.refl τ x⟩
    have hlt : #τ.support < Fintype.card (Fin n) :=
      card_lt_univ_of_notMem (Perm.notMem_support.mpr hx)
    rw [he, card_singleton, Multiset.mem_replicate]
    exact ⟨by omega, rfl⟩
  · left
    have hs : x ∈ τ.support := Perm.mem_support.mpr hx
    have he : ({y | τ.SameCycle x y} : Finset (Fin n)) = (τ.cycleOf x).support := by
      ext y
      rw [Perm.mem_support_cycleOf_iff]
      simp [hs]
    rw [he, Perm.cycleType_def]
    exact Multiset.mem_map_of_mem (card ∘ Perm.support)
      (Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hs)

private theorem parts_eq_of_blocks {τ : Perm (Fin n)} {A : Finset (Fin n)}
    (hR : ∀ x y, τ.SameCycle x y ↔ (x ∈ A ↔ y ∈ A)) {a b : Fin n} (ha : a ∈ A) (hb : b ∉ A) :
    τ.partition.parts = {#A, n - #A} := by
  have hmem : #A ∈ τ.partition.parts := by
    have he : ({y | τ.SameCycle a y} : Finset (Fin n)) = A := by
      ext y
      simp [hR, ha]
    exact he ▸ card_sameCycle_mem_parts τ a
  have hsum : τ.partition.parts.sum = n := τ.partition.parts_sum.trans (Fintype.card_fin n)
  obtain ⟨u, v, huv⟩ := Multiset.card_eq_two.mp (card_parts_eq_two_of_blocks hR ha hb)
  rw [huv] at hmem hsum ⊢
  simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton,
    Multiset.mem_cons, Multiset.mem_singleton] at hmem hsum
  rcases hmem with h | h
  · rw [h, show n - u = v by omega]
  · rw [h, show n - v = u by omega, Multiset.pair_comm]

-- The genus of a two-block partition is one less than the number of runs of either block.
private theorem genus_add_one_eq_runs {τ : Perm (Fin n)} (hτ : IsIncreasingCyclePerm τ)
    (h2 : τ.partition.parts.card = 2) {A : Finset (Fin n)}
    (hR : ∀ x y, τ.SameCycle x y ↔ (x ∈ A ↔ y ∈ A)) {x₀ : Fin n} (hx₀ : x₀ ∈ A) :
    setPartitionGenus τ + 1 = #{x ∈ A | (finRotate n).symm x ∉ A} := by
  have key := (twoBlock_oneFace_and_genus τ hτ h2 x₀).2
  have hcycle (z : Fin n) (hz : z ∈ A) (y : Fin n) : y ∈ A ↔ τ.SameCycle z y := by
    rw [hR]
    exact ⟨fun hy => iff_of_true hz hy, fun h => h.mp hz⟩
  have hA : ({x | τ.SameCycle x₀ x} : Finset (Fin n)) = A := by
    ext x
    simp only [mem_filter, mem_univ, true_and]
    exact (hcycle x₀ hx₀ x).symm
  have hfix : ({x | τ.SameCycle x₀ x ∧ (finRotate n * τ⁻¹) x = x} : Finset (Fin n)) =
      {x ∈ A | (finRotate n).symm x ∈ A} := by
    ext x
    simp only [mem_filter, mem_univ, true_and, ← hcycle x₀ hx₀ x]
    refine and_congr_right fun hx => ?_
    rw [Perm.mul_apply, ← Equiv.eq_symm_apply, Perm.inv_def, Equiv.symm_apply_eq]
    constructor
    · intro h
      have h1 := (hR _ _).mp (Perm.SameCycle.refl τ ((finRotate n).symm x)).apply_right
      rw [← h] at h1
      exact h1.mpr hx
    · intro hy
      calc x = nextPoint A ⟨x, hx⟩ x.val := (nextPoint_self hx).symm
        _ = nextPoint A ⟨x₀, hx₀⟩ (finRotate n ((finRotate n).symm x)).val := by
          rw [Equiv.apply_symm_apply]
        _ = nextPoint A ⟨x₀, hx₀⟩ (((finRotate n).symm x).val + 1) := nextPoint_rotate _ _ _
        _ = τ ((finRotate n).symm x) := nextPoint_succ hτ _ hcycle _ hy
  rw [hA, hfix] at key
  have := card_filter_add_card_filter_not (s := A) (fun x => (finRotate n).symm x ∈ A)
  omega

private theorem eq_or_eq_compl_of_blocks {τ : Perm (Fin n)} {A B : Finset (Fin n)}
    (hA : ∀ x y, τ.SameCycle x y ↔ (x ∈ A ↔ y ∈ A))
    (hB : ∀ x y, τ.SameCycle x y ↔ (x ∈ B ↔ y ∈ B)) {a : Fin n} (ha : a ∈ A) :
    B = A ∨ B = Aᶜ := by
  by_cases haB : a ∈ B
  · left
    ext x
    have h1 := hB a x
    have h2 := hA a x
    rw [iff_true_left haB] at h1
    rw [iff_true_left ha] at h2
    exact h1.symm.trans h2
  · right
    ext x
    have h1 := hB a x
    have h2 := hA a x
    rw [iff_false_left haB] at h1
    rw [iff_true_left ha] at h2
    rw [mem_compl]
    tauto

end partitionGenusCount_twoBlocks

open partitionGenusCount_twoBlocks

/-- **Genus count of two-block partitions.** Let $n$, $p$ and $g$ be natural numbers with
$2 \le p < n$. The number $C_{n,[p,\,n-p]}^{(g)}$ of genus-$g$ set partitions of
$\{0, \dots, n-1\}$ into two blocks of sizes $p$ and $n - p$ equals
$$\frac{n}{g+1} \binom{p-1}{g} \binom{n-p-1}{g}$$
when $n \ne 2p$, and half of this number when $n = 2p$.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Proposition 14
(`jis-2024-24.2.6-prop-14`). -/
theorem partitionGenusCount_twoBlocks (n p g : ℕ) (hp : 2 ≤ p) (hpn : p < n) :
    (partitionGenusCount n {p, n - p} g : ℚ) =
      (if n = 2 * p then 1 / 2 else 1) *
        ((n : ℚ) / (g + 1) * ((p - 1).choose g : ℚ) * ((n - p - 1).choose g : ℚ)) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- Both blocks of a partition counted on the left have size `p` or `m + 1 - p` and `g + 1`
  -- runs.
  have hblock {τ : Perm (Fin (m + 1))}
      (hτ : IsIncreasingCyclePerm τ ∧ τ.partition.parts = {p, m + 1 - p} ∧
        setPartitionGenus τ = g)
      {B : Finset (Fin (m + 1))} (hR : ∀ x y, τ.SameCycle x y ↔ (x ∈ B ↔ y ∈ B))
      {a b : Fin (m + 1)} (ha : a ∈ B) (hb : b ∉ B) :
      (#B = p ∨ #B = m + 1 - p) ∧ #{x ∈ B | x - 1 ∉ B} = g + 1 := by
    obtain ⟨hinc, hparts, hgenus⟩ := hτ
    constructor
    · have h := parts_eq_of_blocks hR ha hb
      rw [hparts] at h
      have hmem : #B ∈ ({p, m + 1 - p} : Multiset ℕ) := by
        rw [h]
        simp
      simpa using hmem
    · have h := genus_add_one_eq_runs hinc (card_parts_eq_two_of_blocks hR ha hb) hR ha
      simp only [finRotate_symm_apply] at h
      omega
  -- Double count the pairs `(τ, B)` where `B` is a block of `τ`.
  have hdouble : partitionGenusCount (m + 1) {p, m + 1 - p} g * 2 =
      #{A : Finset (Fin (m + 1)) |
        (#A = p ∨ #A = m + 1 - p) ∧ #{x ∈ A | x - 1 ∉ A} = g + 1} * 1 := by
    unfold partitionGenusCount
    refine card_mul_eq_card_mul (fun τ A => ∀ x y, τ.SameCycle x y ↔ (x ∈ A ↔ y ∈ A)) ?_ ?_
    · intro τ hτ
      replace hτ := (mem_filter.mp hτ).2
      have h2 : τ.partition.parts.card = 2 := by
        rw [hτ.2.1]
        simp
      obtain ⟨c, hc, hclass⟩ := exists_coloring h2
      let A₀ : Finset (Fin (m + 1)) := {x | c x = true}
      have hR₀ (x y : Fin (m + 1)) : τ.SameCycle x y ↔ (x ∈ A₀ ↔ y ∈ A₀) := by
        rw [hclass]
        simp only [A₀, mem_filter, mem_univ, true_and]
        cases c x <;> cases c y <;> simp
      have hR₁ (x y : Fin (m + 1)) : τ.SameCycle x y ↔ (x ∈ A₀ᶜ ↔ y ∈ A₀ᶜ) := by
        rw [hR₀, mem_compl, mem_compl, not_iff_not]
      obtain ⟨a, ha⟩ := hc true
      obtain ⟨b, hb⟩ := hc false
      have ha' : a ∈ A₀ := by simp [A₀, ha]
      have hb' : b ∉ A₀ := by simp [A₀, hb]
      rw [card_eq_two]
      refine ⟨A₀, A₀ᶜ, fun h => (mem_compl.mp (h ▸ ha')) ha', ?_⟩
      ext B
      simp only [bipartiteAbove, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      constructor
      · rintro ⟨-, hRB⟩
        exact eq_or_eq_compl_of_blocks hR₀ hRB ha'
      · rintro (rfl | rfl)
        · exact ⟨hblock hτ hR₀ ha' hb', hR₀⟩
        · exact ⟨hblock hτ hR₁ (mem_compl.mpr hb') (not_not.mpr ha' ∘ mem_compl.mp), hR₁⟩
    · intro A hA
      obtain ⟨hsize, hruns⟩ := (mem_filter.mp hA).2
      have hpos : 0 < #A := by omega
      have hlt : #A < m + 1 := by omega
      obtain ⟨a, ha⟩ := card_pos.mp hpos
      obtain ⟨b, hb⟩ : ∃ b, b ∉ A := by
        by_contra! h
        rw [eq_univ_of_forall h, card_univ, Fintype.card_fin] at hlt
        omega
      have hR := twoBlockPerm_sameCycle_iff A
      have hinc := isIncreasingCyclePerm_twoBlockPerm A
      rw [card_eq_one]
      refine ⟨twoBlockPerm A, ?_⟩
      ext τ
      simp only [bipartiteBelow, mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · rintro ⟨⟨hτ, -, -⟩, hRτ⟩
        exact eq_of_sameCycle_iff hτ hinc fun x y => (hRτ x y).trans (hR x y).symm
      · rintro rfl
        refine ⟨⟨hinc, ?_, ?_⟩, hR⟩
        · rw [parts_eq_of_blocks hR ha hb]
          rcases hsize with h | h
          · rw [h]
          · rw [h, show m + 1 - (m + 1 - p) = p by omega, Multiset.pair_comm]
        · have h := genus_add_one_eq_runs hinc (card_parts_eq_two_of_blocks hR ha hb) hR ha
          simp only [finRotate_symm_apply] at h
          omega
  have h1 := card_cyclicRuns m p (g + 1) (by omega) (by omega) (by omega)
  have h2 := card_cyclicRuns m (m + 1 - p) (g + 1) (by omega) (by omega) (by omega)
  rw [show m + 1 - p - 1 = m - p by omega, show m - (m + 1 - p) = p - 1 by omega,
    Nat.add_sub_cancel] at h2
  rw [Nat.add_sub_cancel] at h1
  rw [show m + 1 - p - 1 = m - p by omega]
  by_cases hn : m + 1 = 2 * p
  · rw [ite_eq_left hn]
    have hq : m + 1 - p = p := by omega
    have hS : #{A : Finset (Fin (m + 1)) |
          (#A = p ∨ #A = m + 1 - p) ∧ #{x ∈ A | x - 1 ∉ A} = g + 1} =
        #{A : Finset (Fin (m + 1)) | #A = p ∧ #{x ∈ A | x - 1 ∉ A} = g + 1} := by
      rw [hq]
      simp only [or_self]
    rw [hS] at hdouble
    have e1 : (partitionGenusCount (m + 1) {p, m + 1 - p} g : ℚ) * 2 =
        #{A : Finset (Fin (m + 1)) | #A = p ∧ #{x ∈ A | x - 1 ∉ A} = g + 1} := by
      exact_mod_cast hdouble.trans (mul_one _)
    have e2 : ((g : ℚ) + 1) *
        #{A : Finset (Fin (m + 1)) | #A = p ∧ #{x ∈ A | x - 1 ∉ A} = g + 1} =
        ((m : ℚ) + 1) * ((p - 1).choose g * (m - p).choose g) := by
      exact_mod_cast h1
    have hg : (g : ℚ) + 1 ≠ 0 := by positivity
    have hS : (#{A : Finset (Fin (m + 1)) | #A = p ∧ #{x ∈ A | x - 1 ∉ A} = g + 1} : ℚ) =
        ((m : ℚ) + 1) * ((p - 1).choose g * (m - p).choose g) / ((g : ℚ) + 1) := by
      rw [eq_div_iff hg, mul_comm]
      exact e2
    push_cast
    calc (partitionGenusCount (m + 1) {p, m + 1 - p} g : ℚ)
        = (partitionGenusCount (m + 1) {p, m + 1 - p} g : ℚ) * 2 / 2 := by ring
      _ = _ := by rw [e1, hS]; ring
  · rw [ite_eq_right hn]
    have hS : #{A : Finset (Fin (m + 1)) |
          (#A = p ∨ #A = m + 1 - p) ∧ #{x ∈ A | x - 1 ∉ A} = g + 1} =
        #{A : Finset (Fin (m + 1)) | #A = p ∧ #{x ∈ A | x - 1 ∉ A} = g + 1} +
          #{A : Finset (Fin (m + 1)) | #A = m + 1 - p ∧ #{x ∈ A | x - 1 ∉ A} = g + 1} := by
      rw [← card_union_of_disjoint]
      · congr 1
        ext A
        simp only [mem_filter, mem_univ, true_and, mem_union]
        tauto
      · rw [disjoint_filter]
        intro A _ h h'
        omega
    rw [hS] at hdouble
    have e1 : (partitionGenusCount (m + 1) {p, m + 1 - p} g : ℚ) * 2 =
        #{A : Finset (Fin (m + 1)) | #A = p ∧ #{x ∈ A | x - 1 ∉ A} = g + 1} +
          #{A : Finset (Fin (m + 1)) | #A = m + 1 - p ∧ #{x ∈ A | x - 1 ∉ A} = g + 1} := by
      exact_mod_cast hdouble.trans (mul_one _)
    have e2 : ((g : ℚ) + 1) *
        #{A : Finset (Fin (m + 1)) | #A = p ∧ #{x ∈ A | x - 1 ∉ A} = g + 1} =
        ((m : ℚ) + 1) * ((p - 1).choose g * (m - p).choose g) := by
      exact_mod_cast h1
    have e3 : ((g : ℚ) + 1) *
        #{A : Finset (Fin (m + 1)) | #A = m + 1 - p ∧ #{x ∈ A | x - 1 ∉ A} = g + 1} =
        ((m : ℚ) + 1) * ((m - p).choose g * (p - 1).choose g) := by
      exact_mod_cast h2
    have hg : (g : ℚ) + 1 ≠ 0 := by positivity
    have hS : (#{A : Finset (Fin (m + 1)) | #A = p ∧ #{x ∈ A | x - 1 ∉ A} = g + 1} : ℚ) =
        ((m : ℚ) + 1) * ((p - 1).choose g * (m - p).choose g) / ((g : ℚ) + 1) := by
      rw [eq_div_iff hg, mul_comm]
      exact e2
    have hS' :
        (#{A : Finset (Fin (m + 1)) | #A = m + 1 - p ∧ #{x ∈ A | x - 1 ∉ A} = g + 1} : ℚ) =
          ((m : ℚ) + 1) * ((m - p).choose g * (p - 1).choose g) / ((g : ℚ) + 1) := by
      rw [eq_div_iff hg, mul_comm]
      exact e3
    push_cast
    calc (partitionGenusCount (m + 1) {p, m + 1 - p} g : ℚ)
        = (partitionGenusCount (m + 1) {p, m + 1 - p} g : ℚ) * 2 / 2 := by ring
      _ = _ := by rw [e1, hS, hS']; ring

end

end MetaMathlibExt
