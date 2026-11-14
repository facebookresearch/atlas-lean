/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Odd-indexed Fibonacci numbers via pattern-avoiding permutations

Statements from Juan B. Gil, Felix H. Xu, and William
Y. Zhu, "Odd-Indexed Fibonacci Numbers via
Pattern-Avoiding Permutations", *INTEGERS* 25 (2025),
Article A79 (<https://math.colgate.edu/~integers/vol25.html>).

Pattern containment is classical: `HasPattern σ π` says
some subsequence of `σ` is order-isomorphic to `π`
(patterns are given as `0`-based value functions, so
`pat321 = ![2, 1, 0]`, etc.). Stated here are the counts
`|Sₙ(321, 4123)| = |Sₙ(321, 3412)| = |Sₙ(231, 3124)| =
F_{2n-1}` (Propositions 1, 7, 10), the position-of-`1`
refinements for the first and third classes
(Propositions 2, 11, counts only: the bivariate
generating-function clauses reach the extraction in
garbled form and are not stated), and the first clause of
Proposition 8 (positions `1` and `2` of the entry `1` in
the `(321, 3412)` class). All were verified by brute force
for `n ≤ 7`.

With the journal text (revisit): Propositions 4, 5, 6 for
the vincular pattern `2143` (`HasVincular2143`; the
extraction lost the underline, and the classical-pattern
counts `1, 2, 5, 13, 33, 80, 185` are not `F_{2n-1}`), and
the bijection statements (Corollary 1, Propositions 3, 6, 9,
12) as `Nonempty (A ≃ B)` over Mathlib `DyckWord`s,
block fountains, noncrossing/nonnesting set partitions and
directed column-convex polyominoes, each brute-forced for
`n ≤ 7`.

Not stated (see the source audit table): Proposition 8's
clause for positions `≥ 3`, whose extracted form
`|Sₙ^{k→1}| = |S_{n-1}|` is numerically false (the values
are `F_{2n-2k+1}`).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import MathlibExt.Combinatorics.NoncrossingPartition.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Polynomial.Basic

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted

/-- Classical pattern containment: `σ` contains the
pattern `π` if some strictly increasing choice of
positions gives entries order-isomorphic to `π`. -/
def HasPattern {n k : ℕ} (σ : Equiv.Perm (Fin n))
    (π : Fin k → Fin k) : Prop :=
  ∃ e : Fin k → Fin n, (∀ i j : Fin k, i < j → e i < e j) ∧
    ∀ i j : Fin k, σ (e i) < σ (e j) ↔ π i < π j


/-- The pattern `321` (0-based). -/
def pat321 : Fin 3 → Fin 3 := ![2, 1, 0]

/-- The pattern `231` (0-based). -/
def pat231 : Fin 3 → Fin 3 := ![1, 2, 0]

/-- The pattern `4123` (0-based). -/
def pat4123 : Fin 4 → Fin 4 := ![3, 0, 1, 2]

/-- The pattern `3412` (0-based). -/
def pat3412 : Fin 4 → Fin 4 := ![2, 3, 0, 1]

/-- The pattern `3124` (0-based). -/
def pat3124 : Fin 4 → Fin 4 := ![2, 0, 1, 3]

/-- **Proposition 1**: `|Sₙ(321, 4123)| = F_{2n-1}`.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", Proposition 1. -/
theorem_wanted card_avoid_321_4123 (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {σ : Equiv.Perm (Fin n) //
      ¬ HasPattern σ pat321 ∧ ¬ HasPattern σ pat4123} =
      Nat.fib (2 * n - 1)

/-- **Proposition 7**: `|Sₙ(321, 3412)| = F_{2n-1}`.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", Proposition 7. -/
theorem_wanted card_avoid_321_3412 (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {σ : Equiv.Perm (Fin n) //
      ¬ HasPattern σ pat321 ∧ ¬ HasPattern σ pat3412} =
      Nat.fib (2 * n - 1)

/-- **Proposition 10**: `|Sₙ(231, 3124)| = F_{2n-1}`.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", Proposition 10. -/
theorem_wanted card_avoid_231_3124 (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {σ : Equiv.Perm (Fin n) //
      ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124} =
      Nat.fib (2 * n - 1)

/-- **Proposition 2** (count): for `1 ≤ k < n`, the number
of `(321, 4123)`-avoiding permutations of `[n]` with
`σ(k) = 1` is `k * |S_{n-k}(321, 4123)|` (positions and
values 1-based in the paper; here the position is
`j : Fin n` with `σ j = 0`, so `k = j + 1`).

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", Proposition 2. -/
theorem_wanted card_avoid_321_4123_pos_zero (n : ℕ)
    (hn : 1 ≤ n) (j : Fin n) (hj : j.val + 1 < n) :
    Nat.card {σ : Equiv.Perm (Fin n) //
      ¬ HasPattern σ pat321 ∧ ¬ HasPattern σ pat4123 ∧
        σ j = ⟨0, hn⟩} =
      (j.val + 1) * Nat.card
        {σ : Equiv.Perm (Fin (n - j.val - 1)) //
          ¬ HasPattern σ pat321 ∧ ¬ HasPattern σ pat4123}

/-- **Proposition 11** (count): for `1 ≤ k < n`, the
number of `(231, 3124)`-avoiding permutations of `[n]`
with `σ(k) = 1` is `k * |S_{n-k}(231, 3124)|`.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", Proposition 11. -/
theorem_wanted card_avoid_231_3124_pos_zero (n : ℕ)
    (hn : 1 ≤ n) (j : Fin n) (hj : j.val + 1 < n) :
    Nat.card {σ : Equiv.Perm (Fin n) //
      ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124 ∧
        σ j = ⟨0, hn⟩} =
      (j.val + 1) * Nat.card
        {σ : Equiv.Perm (Fin (n - j.val - 1)) //
          ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124}

/-- **Proposition 8**, first clause: for `n > 1`, the
numbers of `(321, 3412)`-avoiding permutations of `[n]`
with `σ(1) = 1` and with `σ(2) = 1` (1-based) both equal
`F_{2n-3}`.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", Proposition 8. -/
theorem_wanted card_avoid_321_3412_pos_zero_le (n : ℕ)
    (hn : 2 ≤ n) :
    Nat.card {σ : Equiv.Perm (Fin n) //
      ¬ HasPattern σ pat321 ∧ ¬ HasPattern σ pat3412 ∧
        σ ⟨0, by omega⟩ = ⟨0, by omega⟩} =
      Nat.fib (2 * n - 3) ∧
    Nat.card {σ : Equiv.Perm (Fin n) //
      ¬ HasPattern σ pat321 ∧ ¬ HasPattern σ pat3412 ∧
        σ ⟨1, hn⟩ = ⟨0, by omega⟩} =
      Nat.fib (2 * n - 3)

/-! ### Revisit with the journal text: vincular `2143`,
bijection partner classes -/

/-- The vincular pattern `2143`: a classical `2143`
occurrence at positions `i₁ < i₂ < i₃ < i₄` with
`i₂ = i₁ + 1`, i.e. `σ(i₁ + 1) < σ(i₁) < σ(i₄) < σ(i₃)`.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", INTEGERS 25 (2025), Article A79, Section 1 (vincular
pattern `2143`). -/
def HasVincular2143 {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∃ i i' j k : Fin n, i'.val = i.val + 1 ∧ i' < j ∧ j < k ∧
    σ i' < σ i ∧ σ i < σ k ∧ σ k < σ j

/-- The identity permutation avoids the vincular pattern
`2143`.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", INTEGERS 25 (2025), Article A79, Section 1. -/
theorem not_hasVincular2143_one (n : ℕ) :
    ¬ HasVincular2143 (1 : Equiv.Perm (Fin n)) := by
  rintro ⟨i, i', j, k, hi, -, -, h, -, -⟩
  simp only [Equiv.Perm.one_apply, Fin.lt_def] at h
  omega

/-- Rows of coins stacked on a row occupying the positions
`a, …, a + l - 1`: each further row `(a', l')` is a nonempty
contiguous block whose coin at position `p` rests on the
coins at positions `p` and `p + 1` of the row beneath, i.e.
`a ≤ a'` and `a' + l' + 1 ≤ a + l` (a row at height `h`
is drawn shifted right by `h/2`). A block `n`-fountain is a
list `rows` with `IsBlockFountainAbove 0 n rows`.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", INTEGERS 25 (2025), Article A79, Section 3.1
(block `n`-fountains). -/
def IsBlockFountainAbove : ℕ → ℕ → List (ℕ × ℕ) → Prop
  | _, _, [] => True
  | a, l, (a', l') :: rows =>
      a ≤ a' ∧ 1 ≤ l' ∧ a' + l' + 1 ≤ a + l ∧ IsBlockFountainAbove a' l' rows

/-- The bare bottom row is a block fountain, and so is a
single row of `l - 1` coins on a row of `l ≥ 2` coins.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", INTEGERS 25 (2025), Article A79, Section 3.1. -/
theorem isBlockFountainAbove_small (a l : ℕ) (hl : 2 ≤ l) :
    IsBlockFountainAbove a l [] ∧ IsBlockFountainAbove a l [(a, l - 1)] := by
  refine ⟨trivial, ?_, ?_, ?_, trivial⟩ <;> omega

/-- An arc of a set partition of `[n]`: `i < j` lie in one
block with no element of that block strictly between them.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", INTEGERS 25 (2025), Article A79, Section 4.1 (arc
diagrams). -/
def IsPartitionArc {n : ℕ} (P : Finpartition (Finset.univ : Finset (Fin n)))
    (i j : Fin n) : Prop :=
  i < j ∧ ∃ b ∈ P.parts, i ∈ b ∧ j ∈ b ∧ ∀ m ∈ b, ¬ (i < m ∧ m < j)

/-- A set partition of `[n]` is noncrossing and nonnesting:
it is noncrossing in the sense of the canonical
`NoncrossingPartition.IsNoncrossing`, and no two arcs
`(i₁, j₁)`, `(i₂, j₂)` nest, `i₁ < i₂ < j₂ < j₁`.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", INTEGERS 25 (2025), Article A79, Section 4.1. -/
def IsNoncrossingNonnesting {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) : Prop :=
  NoncrossingPartition.IsNoncrossing P ∧
    ∀ i₁ j₁ i₂ j₂ : Fin n, IsPartitionArc P i₁ j₁ → IsPartitionArc P i₂ j₂ →
      ¬ (i₁ < i₂ ∧ i₂ < j₂ ∧ j₂ < j₁)

/-- The partition into singletons has no arcs, so it is
noncrossing and nonnesting.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", INTEGERS 25 (2025), Article A79, Section 4.1. -/
theorem isNoncrossingNonnesting_bot (n : ℕ) :
    IsNoncrossingNonnesting (⊥ : Finpartition (Finset.univ : Finset (Fin n))) := by
  have key : ∀ b ∈ (⊥ : Finpartition (Finset.univ : Finset (Fin n))).parts,
      ∀ x ∈ b, ∀ y ∈ b, x = y := by
    intro b hb x hx y hy
    rw [Finpartition.parts_bot] at hb
    obtain ⟨z, -, rfl⟩ := Finset.mem_map.1 hb
    simp only [Function.Embedding.coeFn_mk, Finset.mem_singleton] at hx hy
    exact hx.trans hy.symm
  refine ⟨?_, ?_⟩
  · rintro ⟨a, b, c, d, hab, hbc, -, hac, -, -⟩
    have hc : c ∈ (⊥ : Finpartition (Finset.univ : Finset (Fin n))).part a :=
      hac ▸ NoncrossingPartition.mem_part_self _ c
    exact absurd (key _ (NoncrossingPartition.part_mem_parts _ a) a
      (NoncrossingPartition.mem_part_self _ a) c hc) (hab.trans hbc).ne
  · rintro i₁ j₁ - - ⟨hlt, b, hb, hi, hj, -⟩
    exact absurd (key b hb i₁ hi j₁ hj) hlt.ne

/-- A set partition of `[n]` is indecomposable: no set of
its blocks partitions `[k]` for `1 ≤ k < n`, i.e. for every
such `k` some block meets both `[k]` and its complement.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", INTEGERS 25 (2025), Article A79, Section 4.1. -/
def IsIndecomposablePartition {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k < n →
    ¬ ∀ b ∈ P.parts, (∀ x ∈ b, x.val < k) ∨ (∀ x ∈ b, k ≤ x.val)

/-- A permutation of `[n]` is indecomposable: it is not a
direct sum of two nonempty permutations, i.e. it maps no
initial segment `[k]`, `1 ≤ k < n`, to itself.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", INTEGERS 25 (2025), Article A79, Section 4.1, footnote 2. -/
def IsIndecomposablePerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k < n → ¬ ∀ x : Fin n, x.val < k → (σ x).val < k

/-- The identity of `[n]` is indecomposable exactly when
`n ≤ 1`; here the forward direction for `n = 2`: the
identity of `[2]` is decomposable.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", INTEGERS 25 (2025), Article A79, Section 4.1, footnote 2. -/
theorem not_isIndecomposablePerm_one_two :
    ¬ IsIndecomposablePerm (1 : Equiv.Perm (Fin 2)) := by
  intro h
  exact h 1 le_rfl (by norm_num) fun x hx => by simpa using hx

/-- A directed column-convex polyomino, as a finite set of
unit cells `(x, y) ∈ ℤ × ℤ` translated so that its source
cell is the origin: it contains `(0, 0)`, every other cell
has its south or west neighbour in the set (so it is built
from `(0, 0)` by adding cells on the right or on top of
existing cells), and every column is contiguous. Its area is
its cardinality.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", INTEGERS 25 (2025), Article A79, Section 5.1. -/
def IsDCCPolyomino (S : Finset (ℤ × ℤ)) : Prop :=
  (0, 0) ∈ S ∧ (∀ c ∈ S, c ≠ (0, 0) → (c.1, c.2 - 1) ∈ S ∨ (c.1 - 1, c.2) ∈ S) ∧
    ∀ c ∈ S, ∀ d ∈ S, c.1 = d.1 → ∀ y : ℤ, c.2 ≤ y → y ≤ d.2 → (c.1, y) ∈ S

/-- The single cell is the directed column-convex polyomino
of area `1`.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", INTEGERS 25 (2025), Article A79, Section 5.1. -/
theorem isDCCPolyomino_singleton : IsDCCPolyomino {((0 : ℤ), (0 : ℤ))} := by
  refine ⟨Finset.mem_singleton_self _, ?_, ?_⟩
  · intro c hc hne
    exact absurd (Finset.mem_singleton.1 hc) hne
  · intro c hc d hd _ y h1 h2
    rw [Finset.mem_singleton] at hc hd ⊢
    subst hc hd
    simp only at h1 h2 ⊢
    ext <;> simp; omega

/-- A Dyck word has height at most `3` when no prefix has
more than three more `U`s than `D`s (the height-`3` analogue
of `MetaMathlibExt.IsDyckHeightAtMostTwo`).

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", INTEGERS 25 (2025), Article A79, Proposition 3
(Dyck paths of height at most `3`). -/
def IsDyckHeightAtMostThree (p : DyckWord) : Prop :=
  ∀ i ≤ p.toList.length,
    (p.toList.take i).count DyckStep.U ≤ (p.toList.take i).count DyckStep.D + 3

/-- The empty Dyck word has height at most `3`.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", INTEGERS 25 (2025), Article A79, Proposition 3. -/
theorem isDyckHeightAtMostThree_zero : IsDyckHeightAtMostThree 0 := by
  intro i _
  rw [(DyckWord.toList_eq_nil (p := 0)).mpr rfl]
  simp

/-- **Proposition 3**: for every `n`, `Sₙ(321, 4123)` is in
bijection with the Dyck paths of semilength `n` and height at
most `3` (Mathlib `DyckWord`s, `IsDyckHeightAtMostThree`).

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", INTEGERS 25 (2025), Article A79, Proposition 3. -/
theorem_wanted avoid_321_4123_equiv_dyck_height_le_three (n : ℕ) :
    Nonempty ({σ : Equiv.Perm (Fin n) //
        ¬ HasPattern σ pat321 ∧ ¬ HasPattern σ pat4123} ≃
      {p : DyckWord // p.semilength = n ∧ IsDyckHeightAtMostThree p})

/-- **Proposition 4**: `|Sₙ(321, 2143)| = F_{2n-1}` for the
vincular pattern `2143`.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", INTEGERS 25 (2025), Article A79, Proposition 4. -/
theorem_wanted card_avoid_321_vincular2143 (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {σ : Equiv.Perm (Fin n) //
      ¬ HasPattern σ pat321 ∧ ¬ HasVincular2143 σ} =
      Nat.fib (2 * n - 1)

/-- **Proposition 5**: with `a(n, k)` the number of
`σ ∈ Sₙ(321, 2143)` (vincular `2143`) with `σ(k) = n`
(1-based), `a(n, 1) = 1` for `n ≥ 1`, `a(n, n) = F_{2n-3}`
for `n > 1`, `a(n, k) = a(n-1, k-1) + a(n-1, k)` for
`1 < k < n`, and `g(x, t) = Σ_{n ≥ 1} Σ_{k=1}^n a(n, k) tᵏ xⁿ`
satisfies
`(1 - x - tx)(1 - 3tx + t²x²) g = tx(1 - tx)(1 - 2tx)`
in `ℚ[t][[x]]`.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", INTEGERS 25 (2025), Article A79, Proposition 5. -/
theorem_wanted avoid_321_vincular2143_max_position :
    let a : ℕ → ℕ → ℕ := fun n k => Nat.card {σ : Equiv.Perm (Fin n) //
      ¬ HasPattern σ pat321 ∧ ¬ HasVincular2143 σ ∧
        ∃ j : Fin n, j.val + 1 = k ∧ (σ j).val + 1 = n}
    let t : PowerSeries (Polynomial ℚ) := PowerSeries.C Polynomial.X
    (∀ n : ℕ, 1 ≤ n → a n 1 = 1) ∧
      (∀ n : ℕ, 1 < n → a n n = Nat.fib (2 * n - 3)) ∧
      (∀ n k : ℕ, 1 < k → k < n → a n k = a (n - 1) (k - 1) + a (n - 1) k) ∧
      (1 - PowerSeries.X - t * PowerSeries.X) *
          (1 - 3 * t * PowerSeries.X + t ^ 2 * PowerSeries.X ^ 2) *
          PowerSeries.mk (fun n => ∑ k ∈ Finset.Icc 1 n,
            (a n k : Polynomial ℚ) * Polynomial.X ^ k) =
        t * PowerSeries.X * (1 - t * PowerSeries.X) * (1 - 2 * t * PowerSeries.X)

/-- **Proposition 6**: the block `n`-fountains (see
`IsBlockFountainAbove`) are in bijection with
`Sₙ(321, 2143)` (vincular `2143`).

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", INTEGERS 25 (2025), Article A79, Proposition 6. -/
theorem_wanted blockFountain_equiv_avoid_321_vincular2143 (n : ℕ) (hn : 1 ≤ n) :
    Nonempty ({rows : List (ℕ × ℕ) // IsBlockFountainAbove 0 n rows} ≃
      {σ : Equiv.Perm (Fin n) // ¬ HasPattern σ pat321 ∧ ¬ HasVincular2143 σ})

/-- **Proposition 9**: the indecomposable, noncrossing,
nonnesting set partitions of `[n]` are in bijection with the
indecomposable permutations in `Sₙ(321, 3412)`.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", INTEGERS 25 (2025), Article A79, Proposition 9. -/
theorem_wanted indecomposable_ncnn_equiv_avoid_321_3412 (n : ℕ) (hn : 1 ≤ n) :
    Nonempty ({P : Finpartition (Finset.univ : Finset (Fin n)) //
        IsNoncrossingNonnesting P ∧ IsIndecomposablePartition P} ≃
      {σ : Equiv.Perm (Fin n) //
        ¬ HasPattern σ pat321 ∧ ¬ HasPattern σ pat3412 ∧ IsIndecomposablePerm σ})

/-- **Corollary 1**: the noncrossing, nonnesting set
partitions of `[n]` are in bijection with `Sₙ(321, 3412)`.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", INTEGERS 25 (2025), Article A79, Corollary 1. -/
theorem_wanted ncnn_equiv_avoid_321_3412 (n : ℕ) (hn : 1 ≤ n) :
    Nonempty ({P : Finpartition (Finset.univ : Finset (Fin n)) //
        IsNoncrossingNonnesting P} ≃
      {σ : Equiv.Perm (Fin n) // ¬ HasPattern σ pat321 ∧ ¬ HasPattern σ pat3412})

/-- **Proposition 12**: the directed column-convex
polyominoes of area `n` (see `IsDCCPolyomino`) are in
bijection with `Sₙ(231, 3124)`.

Source: Juan B. Gil, Felix H. Xu, and William Y. Zhu,
"Odd-Indexed Fibonacci Numbers via Pattern-Avoiding
Permutations", INTEGERS 25 (2025), Article A79, Proposition 12. -/
theorem_wanted dccPolyomino_equiv_avoid_231_3124 (n : ℕ) (hn : 1 ≤ n) :
    Nonempty ({S : Finset (ℤ × ℤ) // IsDCCPolyomino S ∧ S.card = n} ≃
      {σ : Equiv.Perm (Fin n) // ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124})

end MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted
