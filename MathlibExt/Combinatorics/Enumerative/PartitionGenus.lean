/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Logic.Equiv.Fin.Rotate
import MathlibExt.Combinatorics.Enumerative.Stirling

/-!
# Genus of set partitions

Increasing-cycle permutations encode set partitions. For partitions into two blocks,
`twoBlock_oneFace_and_genus` counts the nontrivial face cycles and determines the genus.
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

end

end MetaMathlibExt
