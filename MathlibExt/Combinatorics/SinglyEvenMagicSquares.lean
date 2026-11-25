/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# The extended Strachey construction

The extended Strachey construction combines two reduced magic squares of odd order with
four blocks of radix digits to make a reduced magic square of twice the order.
-/

namespace MetaMathlibExt

@[expose] public section

open Finset

/-- **Magic squares.** An $n \times n$ array $M$ of natural numbers, with rows and columns
indexed by $0, 1, \dots, n - 1$, is a *magic square* when there is a natural number $s$ such
that every row of $M$ and every column of $M$ sums to $s$, and also $\sum_i M_{i,i} = s$ (the
main diagonal) and $\sum_i M_{i,n-1-i} = s$ (the anti-diagonal).

No condition is imposed on the entries themselves.

Source: Gek L. Chia and Wai Keong Kok, *Self-Complementary Magic Squares of Singly Even Orders*,
Journal of Integer Sequences 27 (2024), Article 24.1.4, Section 1. -/
def IsMagicSquare {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  ∃ s : ℕ, (∀ i, ∑ j, M i j = s) ∧ (∀ j, ∑ i, M i j = s) ∧ ∑ i, M i i = s ∧
    ∑ i, M i i.rev = s

/-- **Reduced magic squares.** An $n \times n$ array $M$ of natural numbers is a *reduced magic
square of order $n$* when it is a magic square and its entries are $0, 1, \dots, n^2 - 1$, each
exactly once; equivalently, every entry of $M$ is less than $n^2$ and distinct cells of $M$
hold distinct entries.

These are the magic squares of order $n$ with entries $1, 2, \dots, n^2$, each exactly once,
with every entry reduced by $1$.

Source: Gek L. Chia and Wai Keong Kok, *Self-Complementary Magic Squares of Singly Even Orders*,
Journal of Integer Sequences 27 (2024), Article 24.1.4, Section 3. -/
def IsReducedMagicSquare {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  IsMagicSquare M ∧ (∀ i j, M i j < n ^ 2) ∧
    Function.Injective (fun p : Fin n × Fin n => M p.1 p.2)

/-- **The reduced Lo Shu square.** The $3 \times 3$ square with rows $(7, 0, 5)$, $(2, 4, 6)$ and
$(3, 8, 1)$, a form of the Lo Shu square with every entry reduced by $1$, is a reduced magic
square of order $3$; its magic sum is $12$.

Source: Gek L. Chia and Wai Keong Kok, *Self-Complementary Magic Squares of Singly Even Orders*,
Journal of Integer Sequences 27 (2024), Article 24.1.4, Section 3 (reduced magic squares). -/
theorem isReducedMagicSquare_loShu :
    IsReducedMagicSquare !![7, 0, 5; 2, 4, 6; 3, 8, 1] := by
  refine ⟨⟨12, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    first | decide | (intro i j; fin_cases i <;> fin_cases j <;> decide)

/-- **A 2×2 square that is not a reduced magic square.** The $2 \times 2$ square with rows
$(0, 1)$ and $(2, 3)$ is not a reduced magic square.

Its entries are $0, 1, 2, 3$, each once, but its row sums are $1$ and $5$, so it is not magic.

Source: Gek L. Chia and Wai Keong Kok, *Self-Complementary Magic Squares of Singly Even Orders*,
Journal of Integer Sequences 27 (2024), Article 24.1.4, Section 3 (reduced magic squares). -/
theorem not_isReducedMagicSquare_zero_one_two_three :
    ¬ IsReducedMagicSquare !![0, 1; 2, 3] := by
  rintro ⟨⟨s, hrow, -, -, -⟩, -, -⟩
  have h0 := hrow 0
  have h1 := hrow 1
  simp [Fin.sum_univ_two] at h0 h1
  omega

namespace ExtendedStrachey

/-- Counting the entries of a two-valued line determines its sum. -/
private theorem sum_two_values {n : ℕ} (f : Fin n → ℕ) (a b k : ℕ)
    (hf : ∀ i, f i = a ∨ f i = b) (hk : #{i | f i = a} = k) :
    ∑ i, f i = k * a + (n - k) * b := by
  have hsplit := card_filter_add_card_filter_not (s := univ) (fun i => f i = a)
  simp only [hk, card_univ, Fintype.card_fin] at hsplit
  calc
    ∑ i, f i = ∑ i, if f i = a then a else b := by
      apply sum_congr rfl
      intro i _
      rcases hf i with hi | hi <;> simp [hi]
    _ = _ := by
      rw [sum_ite]
      simp only [sum_const, smul_eq_mul, hk]
      congr 2
      omega

private theorem sum_complement {n : ℕ} (f : Fin n → ℕ) (hf : ∀ i, f i ≤ 3) :
    (∑ i, (3 - f i)) + ∑ i, f i = n * 3 := by
  rw [← sum_add_distrib]
  simp [Nat.sub_add_cancel (hf _)]

/-- A reduced square enumerates all the possible unit digits. Summing by rows gives
the same total for every reduced square of the same order. -/
private theorem total_of_rows {n s : ℕ} {B : Matrix (Fin n) (Fin n) ℕ}
    (hB : IsReducedMagicSquare B) (hr : ∀ i, ∑ j, B i j = s) :
    n * s = ∑ x : Fin (n ^ 2), x.val := by
  let entry (p : Fin n × Fin n) : Fin (n ^ 2) := ⟨B p.1 p.2, hB.2.1 ..⟩
  have bij : Function.Bijective entry := (Fintype.bijective_iff_injective_and_card _).2
    ⟨fun _ _ h => hB.2.2 (congrArg Fin.val h), by simp [pow_two]⟩
  calc
    n * s = ∑ p : Fin n × Fin n, (entry p).val := by
      simp [Fintype.sum_prod_type, entry, hr]
    _ = _ := (Equiv.ofBijective entry bij).sum_comp Fin.val

/-- Sum the high and low digits separately along a pair of half-lines. -/
private theorem line_sum {n q r s : ℕ} {a c b d : Fin n → ℕ}
    (hrad : (∑ i, a i) + ∑ i, c i = r) (hb : ∑ i, b i = s) (hd : ∑ i, d i = s) :
    (∑ i, (a i * q + b i)) + ∑ i, (c i * q + d i) = r * q + (s + s) := by
  rw [← hrad, add_mul]
  simp only [sum_add_distrib, ← sum_mul, hb, hd]
  omega

/-- Splitting at the block boundary sends the two halves of the anti-diagonal
to the anti-diagonals of the off-diagonal blocks. -/
private theorem magic_of_blocks {n s : ℕ} (A B C D : Matrix (Fin n) (Fin n) ℕ)
    (ht : ∀ i, (∑ j, A i j) + ∑ j, B i j = s)
    (hb : ∀ i, (∑ j, C i j) + ∑ j, D i j = s)
    (hl : ∀ j, (∑ i, A i j) + ∑ i, C i j = s)
    (hr : ∀ j, (∑ i, B i j) + ∑ i, D i j = s)
    (hd : (∑ i, A i i) + ∑ i, D i i = s)
    (ha : (∑ i, B i i.rev) + ∑ i, C i i.rev = s) :
    IsMagicSquare ((Matrix.fromBlocks A B C D).submatrix finSumFinEquiv.symm
      finSumFinEquiv.symm) := by
  have right (i : Fin n) : finSumFinEquiv.symm (i.addNat n) = Sum.inr i := by
    rw [← Fin.natAdd_eq_addNat, finSumFinEquiv_symm_apply_natAdd]
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.sum_univ_add]
      simpa [Matrix.submatrix, right] using ht i
    · rw [Fin.sum_univ_add]
      simpa [Matrix.submatrix, right] using hb i
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [Fin.sum_univ_add]
      simpa [Matrix.submatrix, right] using hl j
    · rw [Fin.sum_univ_add]
      simpa [Matrix.submatrix, right] using hr j
  · rw [Fin.sum_univ_add]
    simpa [Matrix.submatrix, right] using hd
  · rw [Fin.sum_univ_add]
    simpa [Matrix.submatrix, right, Fin.rev_castAdd, Fin.rev_addNat] using ha

private theorem digits_unique {q a b c d : ℕ} (hb : b < q) (hd : d < q)
    (h : a * q + b = c * q + d) : a = c ∧ b = d := by
  have hq : 0 < q := by omega
  constructor
  · simpa only [Nat.mul_comm _ q, Nat.mul_add_div hq, Nat.div_eq_of_lt hb,
      Nat.div_eq_of_lt hd, Nat.add_zero] using congrArg (· / q) h
  · simpa only [Nat.mul_comm _ q, Nat.mul_add_mod, Nat.mod_eq_of_lt hb,
      Nat.mod_eq_of_lt hd] using congrArg (· % q) h

/-- The outer radix digits 0 and 3 identify the left block column, and the inner
digits 1 and 2 identify the right one. In each column the unit digit recovers
the local cell, where the two radix digits distinguish the top and bottom halves. -/
private theorem blocks_injective {n : ℕ} (A₀ A₁ B₁ B₂ : Matrix (Fin n) (Fin n) ℕ)
    (hA₀ : ∀ i j, A₀ i j = 0 ∨ A₀ i j = 3) (hA₁ : ∀ i j, A₁ i j = 1 ∨ A₁ i j = 2)
    (hB₁ : IsReducedMagicSquare B₁) (hB₂ : IsReducedMagicSquare B₂) :
    Function.Injective (fun p : (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) =>
      Matrix.fromBlocks
        (fun i j => A₀ i j * n ^ 2 + B₁ i j)
        (fun i j => (3 - A₁ i j) * n ^ 2 + B₂ i j)
        (fun i j => (3 - A₀ i j) * n ^ 2 + B₁ i j)
        (fun i j => A₁ i j * n ^ 2 + B₂ i j) p.1 p.2) := by
  have cell₁ {i j k l} (h : B₁ i j = B₁ k l) : (i, j) = (k, l) := hB₁.2.2 h
  have cell₂ {i j k l} (h : B₂ i j = B₂ k l) : (i, j) = (k, l) := hB₂.2.2 h
  rintro ⟨i, j⟩ ⟨k, l⟩ h
  rcases i with i | i <;> rcases j with j | j <;>
    rcases k with k | k <;> rcases l with l | l
  all_goals
    obtain ⟨high, low⟩ := digits_unique
      (by first | exact hB₁.2.1 i j | exact hB₂.2.1 i j)
      (by first | exact hB₁.2.1 k l | exact hB₂.2.1 k l) h
    have hi₀ := hA₀ i j
    have hi₁ := hA₁ i j
    have hk₀ := hA₀ k l
    have hk₁ := hA₁ k l
    try first
    | obtain ⟨rfl, rfl⟩ := Prod.mk.inj (cell₁ low)
    | obtain ⟨rfl, rfl⟩ := Prod.mk.inj (cell₂ low)
    first | rfl | omega

end ExtendedStrachey

open ExtendedStrachey

/-- **Extended Strachey construction.** Let $m$ be a natural number, let $q = (2m+1)^2$, and let
$A_0$, $A_1$, $B_1$, $B_2$ be $(2m+1) \times (2m+1)$ arrays of natural numbers. Suppose that every
entry of $A_0$ is $0$ or $3$, every row of $A_0$ has exactly $m+1$ zeros, and the main diagonal
and the anti-diagonal of $A_0$ each have exactly $m+1$ threes; that every entry of $A_1$ is $1$
or $2$, every row of $A_1$ has exactly $m+2$ ones, and the main diagonal and the anti-diagonal
of $A_1$ each have exactly $m+2$ ones; and that $B_1$ and $B_2$ are reduced magic squares. Then
the square of order $2(2m+1)$ made of four $(2m+1) \times (2m+1)$ blocks, whose $(i, j)$ entries
are $q A_0(i,j) + B_1(i,j)$ in the top left block, $q (3 - A_1(i,j)) + B_2(i,j)$ in the top
right block, $q (3 - A_0(i,j)) + B_1(i,j)$ in the bottom left block and
$q A_1(i,j) + B_2(i,j)$ in the bottom right block, is a reduced magic square.

At $m = 0$ no array $A_1$ satisfies the row condition (a row of length $1$ cannot hold two
ones), so the statement is vacuous there.

Source: Gek L. Chia and Wai Keong Kok, *Self-Complementary Magic Squares of Singly Even Orders*,
Journal of Integer Sequences 27 (2024), Article 24.1.4, Theorem 1, with Definitions 1-3
(`jis-2024-24.1.4-thm-1`). -/
theorem isReducedMagicSquare_extendedStrachey (m : ℕ)
    (A₀ A₁ B₁ B₂ : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℕ)
    (hA₀ : ∀ i j, A₀ i j = 0 ∨ A₀ i j = 3)
    (hA₀row : ∀ i, #{j | A₀ i j = 0} = m + 1)
    (hA₀diag : #{i | A₀ i i = 3} = m + 1) (hA₀anti : #{i | A₀ i i.rev = 3} = m + 1)
    (hA₁ : ∀ i j, A₁ i j = 1 ∨ A₁ i j = 2)
    (hA₁row : ∀ i, #{j | A₁ i j = 1} = m + 2)
    (hA₁diag : #{i | A₁ i i = 1} = m + 2) (hA₁anti : #{i | A₁ i i.rev = 1} = m + 2)
    (hB₁ : IsReducedMagicSquare B₁) (hB₂ : IsReducedMagicSquare B₂) :
    IsReducedMagicSquare
      ((Matrix.fromBlocks
          (fun i j => A₀ i j * (2 * m + 1) ^ 2 + B₁ i j)
          (fun i j => (3 - A₁ i j) * (2 * m + 1) ^ 2 + B₂ i j)
          (fun i j => (3 - A₀ i j) * (2 * m + 1) ^ 2 + B₁ i j)
          (fun i j => A₁ i j * (2 * m + 1) ^ 2 + B₂ i j)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm) := by
  let n := 2 * m + 1
  have bound₀ (i j) : A₀ i j ≤ 3 := by rcases hA₀ i j with h | h <;> omega
  have bound₁ (i j) : A₁ i j ≤ 3 := by rcases hA₁ i j with h | h <;> omega
  have hm := card_le_univ (univ.filter fun j => A₁ 0 j = 1)
  rw [hA₁row, Fintype.card_fin] at hm
  obtain ⟨s, hr₁, hc₁, hd₁, ha₁⟩ := hB₁.1
  obtain ⟨t, hr₂, hc₂, hd₂, ha₂⟩ := hB₂.1
  obtain rfl : s = t := Nat.eq_of_mul_eq_mul_left (by dsimp [n]; omega : 0 < n)
    ((total_of_rows hB₁ hr₁).trans (total_of_rows hB₂ hr₂).symm)
  -- The prescribed counts make the two uncomplemented row sums equal.
  have rows (i) : ∑ j, A₀ i j = ∑ j, A₁ i j := by
    rw [sum_two_values _ 0 3 _ (hA₀ i) (hA₀row i),
      sum_two_values _ 1 2 _ (hA₁ i) (hA₁row i)]
    omega
  -- On either diagonal, the two uncomplemented sums instead add to three per position.
  have diagonal (f : Fin n → Fin n) (h₀ : #{i | A₀ i (f i) = 3} = m + 1)
      (h₁ : #{i | A₁ i (f i) = 1} = m + 2) :
      (∑ i, A₀ i (f i)) + ∑ i, A₁ i (f i) = n * 3 := by
    rw [sum_two_values _ 3 0 _ (fun i => (hA₀ i (f i)).symm) h₀,
      sum_two_values _ 1 2 _ (fun i => hA₁ i (f i)) h₁]
    dsimp [n]
    omega
  refine ⟨magic_of_blocks (s := n * 3 * n ^ 2 + (s + s)) _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_, ?_, ?_⟩
  · intro i
    refine line_sum ?_ (hr₁ i) (hr₂ i)
    rw [rows]
    exact (add_comm ..).trans (sum_complement _ (bound₁ i))
  · intro i
    refine line_sum ?_ (hr₁ i) (hr₂ i)
    rw [← rows]
    exact sum_complement _ (bound₀ i)
  · intro j
    refine line_sum ?_ (hc₁ j) (hc₁ j)
    exact (add_comm ..).trans (sum_complement _ (fun i => bound₀ i j))
  · intro j
    refine line_sum ?_ (hc₂ j) (hc₂ j)
    exact sum_complement _ (fun i => bound₁ i j)
  · refine line_sum ?_ hd₁ hd₂
    exact diagonal id hA₀diag hA₁diag
  · refine line_sum ?_ ha₂ ha₁
    have := diagonal Fin.rev hA₀anti hA₁anti
    have := sum_complement _ (fun i => bound₀ i i.rev)
    have := sum_complement _ (fun i => bound₁ i i.rev)
    omega
  · intro i j
    have bound {a b : ℕ} (ha : a ≤ 3) (hb : b < n ^ 2) :
        a * n ^ 2 + b < (n + n) ^ 2 := by
      calc
        a * n ^ 2 + b < 3 * n ^ 2 + n ^ 2 :=
          Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_right _ ha) hb
        _ = _ := by simp only [pow_two, add_mul, mul_add]; omega
    simp only [Matrix.submatrix_apply]
    cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;>
      apply bound <;> first | exact bound₀ .. | exact bound₁ .. | omega
                            | exact hB₁.2.1 .. | exact hB₂.2.1 ..
  · exact (blocks_injective _ _ _ _ hA₀ hA₁ hB₁ hB₂).comp
      (finSumFinEquiv.symm.prodCongr finSumFinEquiv.symm).injective

/-- **Ref-symmetric squares from the Strachey construction.** Let $m$ be a natural number, let
$q = (2m+1)^2$, and let $A_0$, $A_1$ and $M$ be $(2m+1) \times (2m+1)$ arrays of natural
numbers, with rows and columns indexed by $0, 1, \dots, 2m$; write $\bar\imath = 2m - i$ and
$\bar\jmath = 2m - j$. Suppose that every entry of $A_0$ is $0$ or $3$, every row of $A_0$ has
exactly $m+1$ zeros, and the main diagonal and the anti-diagonal of $A_0$ each have exactly
$m+1$ threes; that every entry of $A_1$ is $1$ or $2$, every row of $A_1$ has exactly $m+2$
ones, and the main diagonal and the anti-diagonal of $A_1$ each have exactly $m+2$ ones; that
$A_k(\bar\imath, j) = A_k(i, j)$ and $A_k(m, \bar\jmath) = A_k(m, j)$ for $k = 0, 1$ and all
$i$, $j$; that $M$ is a reduced magic square; and that
$M(i, j) + M(\bar\imath, \bar\jmath) = q - 1$ for all $i$, $j$. Let $B_1(i, j) = M(i, \bar\jmath)$
if $i > m$ and $B_1(i, j) = M(i, j)$ otherwise, and let $B_1^*(i, j) = M(i, \bar\jmath)$ if
$i \ge m$ and $B_1^*(i, j) = M(i, j)$ otherwise. Let $n = 2(2m+1)$ and let $S$ be the square of
order $n$, with rows and columns indexed by $0, 1, \dots, n-1$, made of four
$(2m+1) \times (2m+1)$ blocks whose $(i, j)$ entries are $q A_0(i, j) + B_1(i, j)$ in the top
left block, $q (3 - A_1(i, j)) + B_1(i, \bar\jmath)$ in the top right block,
$q (3 - A_0(i, j)) + B_1^*(i, j)$ in the bottom left block and
$q A_1(i, j) + B_1^*(i, \bar\jmath)$ in the bottom right block. Then $S$ is a reduced magic
square, and $S(i, j) + S(n - 1 - i, j) = n^2 - 1$ for all $i$, $j$.

The last identity is the reduced form of the paper's condition $a_{i,j} + a_{n+1-i,j} = n^2 + 1$.
As in the extended Strachey construction, the statement is vacuous at $m = 0$, where no array
$A_1$ satisfies the row condition.

Source: Gek L. Chia and Wai Keong Kok, *Self-Complementary Magic Squares of Singly Even Orders*,
Journal of Integer Sequences 27 (2024), Article 24.1.4, Theorem 2, with Definitions 4-6
(`jis-2024-24.1.4-thm-2`). -/
theorem isReducedMagicSquare_refSymmetric_strachey (m : ℕ)
    (A₀ A₁ M : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℕ)
    (hA₀ : ∀ i j, A₀ i j = 0 ∨ A₀ i j = 3)
    (hA₀row : ∀ i, #{j | A₀ i j = 0} = m + 1)
    (hA₀diag : #{i | A₀ i i = 3} = m + 1) (hA₀anti : #{i | A₀ i i.rev = 3} = m + 1)
    (hA₁ : ∀ i j, A₁ i j = 1 ∨ A₁ i j = 2)
    (hA₁row : ∀ i, #{j | A₁ i j = 1} = m + 2)
    (hA₁diag : #{i | A₁ i i = 1} = m + 2) (hA₁anti : #{i | A₁ i i.rev = 1} = m + 2)
    (hA₀ρ : ∀ i j, A₀ i.rev j = A₀ i j) (hA₁ρ : ∀ i j, A₁ i.rev j = A₁ i j)
    (hA₀mid : ∀ j, A₀ ⟨m, by omega⟩ j.rev = A₀ ⟨m, by omega⟩ j)
    (hA₁mid : ∀ j, A₁ ⟨m, by omega⟩ j.rev = A₁ ⟨m, by omega⟩ j)
    (hM : IsReducedMagicSquare M)
    (hMro : ∀ i j, M i j + M i.rev j.rev = (2 * m + 1) ^ 2 - 1) :
    let B₁ : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℕ :=
      fun i j => if m < (i : ℕ) then M i j.rev else M i j
    let B₁' : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℕ :=
      fun i j => if m ≤ (i : ℕ) then M i j.rev else M i j
    let S := (Matrix.fromBlocks
          (fun i j => A₀ i j * (2 * m + 1) ^ 2 + B₁ i j)
          (fun i j => (3 - A₁ i j) * (2 * m + 1) ^ 2 + B₁ i j.rev)
          (fun i j => (3 - A₀ i j) * (2 * m + 1) ^ 2 + B₁' i j)
          (fun i j => A₁ i j * (2 * m + 1) ^ 2 + B₁' i j.rev)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm
    IsReducedMagicSquare S ∧
      ∀ i j, S i j + S i.rev j = (2 * m + 1 + (2 * m + 1)) ^ 2 - 1 := by
  intro B₁ B₁' S
  let n := 2 * m + 1
  let q := n ^ 2
  have hq : 0 < q := Nat.pow_pos (by dsimp [n]; omega)
  have square : (n + n) ^ 2 = 4 * q := by
    simp only [q, pow_two, add_mul, mul_add]
    omega
  have bound₀ (i j) : A₀ i j ≤ 3 := by rcases hA₀ i j with h | h <;> omega
  have bound₁ (i j) : A₁ i j ≤ 3 := by rcases hA₁ i j with h | h <;> omega
  have hm := card_le_univ (univ.filter fun j => A₁ 0 j = 1)
  rw [hA₁row, Fintype.card_fin] at hm
  obtain ⟨s, hr, -, -, -⟩ := hM.1
  have revSum (f : Fin n → ℕ) : (∑ i : Fin n, f i.rev) = ∑ i, f i :=
    Equiv.sum_comp Fin.revPerm f
  -- The strict upper cut becomes the weak lower cut under row reflection.
  have lowPair (i j : Fin n) : B₁ i j + B₁' i.rev j = q - 1 := by
    have hi : (i : ℕ) < 2 * m + 1 := i.isLt
    have hcut : m ≤ (i.rev : ℕ) ↔ ¬ m < (i : ℕ) := by
      simp only [Fin.val_rev, n]
      omega
    by_cases h : m < (i : ℕ)
    · simpa only [B₁, B₁', ite_eq_left h, ite_eq_right (fun hn => (hcut.mp hn) h), Fin.rev_rev]
        using hMro i j.rev
    · simpa only [B₁, B₁', ite_eq_right h, ite_eq_left (hcut.mpr h)] using hMro i j
  have lowLine (f : Fin n → Fin n) :
      (∑ i, B₁ i (f i)) + ∑ i, B₁' i (f i.rev) = n * (q - 1) := by
    rw [← revSum (fun i => B₁' i (f i.rev)), ← sum_add_distrib]
    simp only [Fin.rev_rev, lowPair, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, n]
  have lowRow (i : Fin n) : (∑ j, M i j) + ∑ j : Fin n, M i j.rev = n * (q - 1) := by
    calc
      _ = (∑ j, M i j) + ∑ j : Fin n, M i.rev j.rev := by
        rw [revSum (M i), hr i, revSum (M i.rev), hr i.rev]
      _ = _ := by rw [← sum_add_distrib]; simp [hMro, q, n]
  have lowTop (i : Fin n) : (∑ j, B₁ i j) + ∑ j : Fin n, B₁ i j.rev = n * (q - 1) := by
    by_cases h : m < (i : ℕ)
    · simpa [B₁, h, add_comm] using lowRow i
    · simpa [B₁, h] using lowRow i
  have lowBottom (i : Fin n) : (∑ j, B₁' i j) + ∑ j : Fin n, B₁' i j.rev = n * (q - 1) := by
    by_cases h : m ≤ (i : ℕ)
    · simpa [B₁', h, add_comm] using lowRow i
    · simpa [B₁', h] using lowRow i
  have rows (i : Fin n) : ∑ j, A₀ i j = ∑ j, A₁ i j := by
    rw [sum_two_values _ 0 3 _ (hA₀ i) (hA₀row i),
      sum_two_values _ 1 2 _ (hA₁ i) (hA₁row i)]
    omega
  have diagonal (f : Fin n → Fin n) (h₀ : #{i | A₀ i (f i) = 3} = m + 1)
      (h₁ : #{i | A₁ i (f i) = 1} = m + 2) :
      (∑ i, A₀ i (f i)) + ∑ i, A₁ i (f i) = n * 3 := by
    rw [sum_two_values _ 3 0 _ (fun i => (hA₀ i (f i)).symm) h₀,
      sum_two_values _ 1 2 _ (fun i => hA₁ i (f i)) h₁]
    dsimp [n]
    omega
  have assemble {a b c d : Fin n → ℕ}
      (hhigh : (∑ i, a i) + ∑ i, c i = n * 3)
      (hlow : (∑ i, b i) + ∑ i, d i = n * (q - 1)) :
      (∑ i, (a i * q + b i)) + ∑ i, (c i * q + d i) = n * 3 * q + n * (q - 1) := by
    simp only [sum_add_distrib, ← sum_mul]
    rw [add_add_add_comm, ← add_mul, hhigh, hlow]
  refine ⟨⟨magic_of_blocks (s := n * 3 * q + n * (q - 1)) _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_,
    ?_, ?_⟩, ?_⟩
  · intro i
    refine assemble ?_ (lowTop i)
    rw [rows]
    exact (add_comm ..).trans (sum_complement _ (bound₁ i))
  · intro i
    refine assemble ?_ (lowBottom i)
    rw [← rows]
    exact sum_complement _ (bound₀ i)
  · intro j
    exact assemble ((add_comm ..).trans (sum_complement _ (fun i => bound₀ i j)))
      (lowLine fun _ => j)
  · intro j
    exact assemble (sum_complement _ (fun i => bound₁ i j)) (lowLine fun _ => j.rev)
  · exact assemble (diagonal id hA₀diag hA₁diag) (lowLine id)
  · refine assemble ?_ ?_
    · let f₀ (i : Fin n) := A₀ i i.rev
      let f₁ (i : Fin n) := A₁ i i.rev
      change (∑ i, (3 - f₁ i)) + ∑ i, (3 - f₀ i) = n * 3
      have h : (∑ i, f₀ i) + ∑ i, f₁ i = n * 3 := diagonal Fin.rev hA₀anti hA₁anti
      have h₀ := sum_complement f₀ (fun i => bound₀ i i.rev)
      have h₁ := sum_complement f₁ (fun i => bound₁ i i.rev)
      omega
    · simpa only [Fin.rev_rev, id_eq] using lowLine id
  · intro i j
    have bound {a b : ℕ} (ha : a ≤ 3) (hb : b < q) : a * q + b < (n + n) ^ 2 := by
      rw [square]
      have := Nat.mul_le_mul_right q ha
      omega
    have b₁ (i j : Fin n) : B₁ i j < q := by
      dsimp [B₁]
      split <;> exact hM.2.1 ..
    have b₁' (i j : Fin n) : B₁' i j < q := by
      dsimp [B₁']
      split <;> exact hM.2.1 ..
    simp only [S, Matrix.submatrix_apply]
    cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;>
      apply bound <;> first | exact bound₀ .. | exact bound₁ .. | omega
                            | exact b₁ .. | exact b₁' ..
  · -- Low digits recover the local row and the column after its row flip.
    let flip (p : Prop) [Decidable p] (j : Fin n) := if p then j.rev else j
    have flipInj (p : Prop) [Decidable p] : Function.Injective (flip p) := by
      by_cases h : p
      · intro j l hl
        simpa [flip, h] using congrArg Fin.rev hl
      · intro j l hl
        simpa [flip, h] using hl
    have top (i j : Fin n) : B₁ i j = M i (flip (m < (i : ℕ)) j) := by
      by_cases h : m < (i : ℕ) <;> simp [B₁, flip, h]
    have bottom (i j : Fin n) : B₁' i j = M i (flip (m ≤ (i : ℕ)) j) := by
      by_cases h : m ≤ (i : ℕ) <;> simp [B₁', flip, h]
    have topCell {i j k l : Fin n} (h : B₁ i j = B₁ k l) : i = k ∧ j = l := by
      rw [top, top] at h
      obtain ⟨rfl, hcol⟩ := Prod.mk.inj (hM.2.2 h)
      exact ⟨rfl, flipInj _ hcol⟩
    have bottomCell {i j k l : Fin n} (h : B₁' i j = B₁' k l) : i = k ∧ j = l := by
      rw [bottom, bottom] at h
      obtain ⟨rfl, hcol⟩ := Prod.mk.inj (hM.2.2 h)
      exact ⟨rfl, flipInj _ hcol⟩
    -- Across halves the low digits still recover the same high digit before
    -- complementation: the two cuts differ only on the symmetric middle row.
    have crossDigit (A : Matrix (Fin n) (Fin n) ℕ)
        (hmid : ∀ j, A ⟨m, by dsimp [n]; omega⟩ j.rev = A ⟨m, by dsimp [n]; omega⟩ j)
        {i j k l : Fin n} (h : B₁ i j = B₁' k l) : A i j = A k l := by
      rw [top, bottom] at h
      obtain ⟨rfl, hcol⟩ := Prod.mk.inj (hM.2.2 h)
      change (if m < (i : ℕ) then j.rev else j) = (if m ≤ (i : ℕ) then l.rev else l) at hcol
      by_cases hh : m < (i : ℕ)
      · rw [ite_eq_left hh, ite_eq_left (Nat.le_of_lt hh)] at hcol
        rw [Fin.rev_injective hcol]
      · by_cases he : m ≤ (i : ℕ)
        · have hi : i = ⟨m, by dsimp [n]; omega⟩ := Fin.ext (by dsimp; omega)
          rw [ite_eq_right hh, ite_eq_left he] at hcol
          rw [hi, hcol, hmid]
        · rw [ite_eq_right hh, ite_eq_right he] at hcol
          rw [hcol]
    have crossRight {i j k l : Fin n} (h : B₁ i j.rev = B₁' k l.rev) :
        A₁ i j = A₁ k l := by
      simpa only [Fin.rev_rev] using crossDigit (fun a b => A₁ a b.rev)
        (fun j => by simpa only [Fin.rev_rev] using (hA₁mid j).symm) h
    have b₁ (i j : Fin n) : B₁ i j < q := top i j ▸ hM.2.1 ..
    have b₁' (i j : Fin n) : B₁' i j < q := bottom i j ▸ hM.2.1 ..
    let blocks : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℕ := Matrix.fromBlocks
      (fun i j => A₀ i j * q + B₁ i j)
      (fun i j => (3 - A₁ i j) * q + B₁ i j.rev)
      (fun i j => (3 - A₀ i j) * q + B₁' i j)
      (fun i j => A₁ i j * q + B₁' i j.rev)
    change Function.Injective ((fun p => blocks p.1 p.2) ∘
      (finSumFinEquiv.symm.prodCongr finSumFinEquiv.symm))
    refine Function.Injective.comp ?_ (Equiv.injective _)
    rintro ⟨i, j⟩ ⟨k, l⟩ h
    rcases i with i | i <;> rcases j with j | j <;>
      rcases k with k | k <;> rcases l with l | l
    all_goals
      obtain ⟨high, low⟩ := digits_unique
        (by first | exact b₁ .. | exact b₁' ..) (by first | exact b₁ .. | exact b₁' ..) h
      first
      | obtain ⟨rfl, rfl⟩ := topCell low; rfl
      | obtain ⟨rfl, hcol⟩ := topCell low
        have : j = l := by simpa using congrArg Fin.rev hcol
        subst l
        rfl
      | obtain ⟨rfl, rfl⟩ := bottomCell low; rfl
      | obtain ⟨rfl, hcol⟩ := bottomCell low
        have : j = l := by simpa using congrArg Fin.rev hcol
        subst l
        rfl
      | have := crossDigit A₀ hA₀mid low
        have := hA₀ i j
        omega
      | have := crossDigit A₀ hA₀mid low.symm
        have := hA₀ i j
        omega
      | have := crossRight low
        have := hA₁ i j
        omega
      | have := crossRight low.symm
        have := hA₁ i j
        omega
      | have h₀ := hA₀ i j
        have h₁ := hA₁ i j
        have h₀' := hA₀ k l
        have h₁' := hA₁ k l
        omega
  · have right (i : Fin (2 * m + 1)) :
        finSumFinEquiv.symm (i.addNat (2 * m + 1)) = Sum.inr i := by
      rw [← Fin.natAdd_eq_addNat, finSumFinEquiv_symm_apply_natAdd]
    have pair {a b c d : ℕ} (hhigh : a + c = 3) (hlow : b + d = q - 1) :
        (a * q + b) + (c * q + d) = (n + n) ^ 2 - 1 := by
      rw [add_add_add_comm, ← add_mul, hhigh, hlow, square]
      omega
    have leftPair (i j : Fin n) :
        (A₀ i j * q + B₁ i j) + ((3 - A₀ i.rev j) * q + B₁' i.rev j) = (n + n) ^ 2 - 1 := by
      refine pair ?_ (lowPair i j)
      rw [hA₀ρ]
      exact Nat.add_sub_of_le (bound₀ i j)
    have rightPair (i j : Fin n) :
        ((3 - A₁ i j) * q + B₁ i j.rev) + (A₁ i.rev j * q + B₁' i.rev j.rev) =
          (n + n) ^ 2 - 1 := by
      refine pair ?_ (lowPair i j.rev)
      rw [hA₁ρ]
      exact Nat.sub_add_cancel (bound₁ i j)
    have topHalf (i : Fin n) (j : Fin (n + n)) :
        S (i.castAdd n) j + S (i.castAdd n).rev j = (n + n) ^ 2 - 1 := by
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [S, Matrix.submatrix_apply, Fin.rev_castAdd, finSumFinEquiv_symm_apply_castAdd,
          n, right]
        exact leftPair i j
      · simp only [S, Matrix.submatrix_apply, Fin.rev_castAdd, finSumFinEquiv_symm_apply_castAdd,
          n, right, finSumFinEquiv_symm_apply_natAdd]
        exact rightPair i j
    have bottomHalf (i : Fin n) (j : Fin (n + n)) :
        S (i.addNat n) j + S (i.addNat n).rev j = (n + n) ^ 2 - 1 := by
      rw [Fin.rev_addNat, add_comm]
      simpa only [Fin.rev_castAdd, Fin.rev_rev] using topHalf i.rev j
    intro i j
    refine Fin.addCases (fun i => topHalf i j) (fun i => ?_) i
    simpa only [← Fin.natAdd_eq_addNat] using bottomHalf i j

end

end MetaMathlibExt
