/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.Divisors

namespace MetaMathlibExt

@[expose] public section

/-- Let `H(n, v)` be the set of partitions of `n` that contain exactly `v` partitions of some
`m` with `v ≤ m ≤ n - v`, and exactly one partition of every other positive integer less than
`n`; here a partition of `m` contained in `λ` is a sub-multiset of the parts of `λ` with sum
`m`, counted once per distinct sub-multiset. For `v ≥ 1`, some `H(n, v)` is nonempty if and
only if `v = 1` or `v = 2` (`v = 1` gives the perfect partitions). The hypothesis `v ≥ 1` is
added: for `v = 0` the partition `(2)` of `2` lies in `H(2, 0)`, since `1` has no partition
inside it.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Lemma 1 (`integers-2025-A109-lem-1`). -/
public theorem_wanted exists_partition_unique_subsums_but_one_iff (v : ℕ) (hv : 1 ≤ v) :
    (∃ n : ℕ, ∃ p : n.Partition,
      let c : ℕ → ℕ := fun m => (p.parts.powerset.toFinset.filter fun s => s.sum = m).card
      ∃ m, v ≤ m ∧ m ≤ n - v ∧ c m = v ∧ ∀ m', 0 < m' → m' < n → m' ≠ m → c m' = 1) ↔
      v = 1 ∨ v = 2

/-! ### Perfect and double-perfect partitions of order `r` -/

/-- The number of partitions of `m` contained in the partition `l`, i.e. the number of distinct
sub-multisets of `l` with sum `m` (the paper's example counts `(1)` once in `(1^5, 2)`).

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Section 1 (Definitions 1, 3 and the example `(1^5, 2) ⊢ 7` after Definition 3). -/
def subpartitionCount (l : Multiset ℕ) (m : ℕ) : ℕ :=
  (l.powerset.toFinset.filter fun s => s.sum = m).card

/-- A perfect partition of `n`: a partition of `n` whose parts contain exactly one partition of
every positive integer `m ≤ n`.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Definition 1. -/
def IsPerfectPartition (n : ℕ) (l : Multiset ℕ) : Prop :=
  (∀ a ∈ l, 0 < a) ∧ l.sum = n ∧ ∀ m ∈ Finset.Icc 1 n, subpartitionCount l m = 1

/-- A double-perfect partition of `N` of order `r` (the set `U_r(N)`): a partition of `N` whose
parts contain exactly two partitions of every `m` with `r + 1 ≤ m ≤ N - r - 1` and exactly one
partition of every other positive integer `m ≤ N`. Order `1` gives the double-perfect partitions
of Definition 3.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Definition 4 and display (11). -/
def IsDoublePerfectOfOrder (r N : ℕ) (l : Multiset ℕ) : Prop :=
  (∀ a ∈ l, 0 < a) ∧ l.sum = N ∧
    ∀ m ∈ Finset.Icc 1 N,
      subpartitionCount l m = if r + 1 ≤ m ∧ m + r + 1 ≤ N then 2 else 1

/-- A Type-A double-perfect partition of `N` of order `r` (the set `D_r(N)`): a member of
`U_r(N)` obtained from a perfect partition of `N - r - 1` by inserting the parts `1^{r+1}` or the
part `r + 1`.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Section 3 (definition of `D_r(N)` after display (12)). -/
def IsTypeADoublePerfect (r N : ℕ) (l : Multiset ℕ) : Prop :=
  IsDoublePerfectOfOrder r N l ∧ ∃ β, IsPerfectPartition (N - r - 1) β ∧
    (l = β + Multiset.replicate (r + 1) 1 ∨ l = β + {r + 1})

/-- MacMahon's bijection (1) from ordered factorizations to perfect partitions: the factorization
`a₁ a₂ ⋯ a_k` maps to `(1^{a₁-1}, a₁^{a₂-1}, (a₁a₂)^{a₃-1}, …, (a₁⋯a_{k-1})^{a_k-1})`.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, display (1). -/
def perfectPartitionOfFactorization : List ℕ → Multiset ℕ
  | [] => 0
  | a :: as => Multiset.replicate (a - 1) 1 + (perfectPartitionOfFactorization as).map (a * ·)

/-- The factorization `2 · 3` of `6` corresponds to the perfect partition `(1, 2^2)` of `5`.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Table 1. -/
theorem perfectPartitionOfFactorization_two_three :
    perfectPartitionOfFactorization [2, 3] = {1, 2, 2} := by
  decide

/-- The parts of the partition attached to a factorization with factors `≥ 1` sum to the product
minus one.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, display (1) (perfect partitions of `n` correspond to factorizations of `n + 1`). -/
theorem perfectPartitionOfFactorization_sum_add_one (a : List ℕ) (ha : ∀ x ∈ a, 1 ≤ x) :
    (perfectPartitionOfFactorization a).sum + 1 = a.prod := by
  induction a with
  | nil => simp [perfectPartitionOfFactorization]
  | cons x xs ih =>
    have hx := ha x (by simp)
    have h := ih fun y hy => ha y (by simp [hy])
    obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
    simp only [perfectPartitionOfFactorization, Multiset.sum_add, Multiset.sum_replicate,
      smul_eq_mul, mul_one, List.prod_cons, Nat.add_sub_cancel]
    rw [Multiset.sum_map_mul_left, Multiset.map_id', ← h, Nat.mul_add, Nat.mul_one]
    generalize (y + 1) * (perfectPartitionOfFactorization xs).sum = t
    omega

/-- Fuel-bounded form of `orderedFactorizationCount`: with fuel `k + 1` the value at `1` is `1`
and the value at `n ≠ 1` is the sum of the values at the proper divisors of `n`.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Section 1 (definition of `f(n)`; summing over the first factor `n / d` of an
ordered factorization gives the recursion). -/
def orderedFactorizationCountAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n => if n = 1 then 1 else ∑ d ∈ n.properDivisors, orderedFactorizationCountAux k d

/-- `f(n)`, the number of ordered factorizations of `n` into factors greater than `1`, with
`f(0) = 0` and `f(1) = 1` (OEIS A074206).

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Section 1 (`f(n) := Σ_k f(n, k)`, `f(0) = 0`, `f(1) = 1`). -/
def orderedFactorizationCount (n : ℕ) : ℕ :=
  orderedFactorizationCountAux n n

/-- The fuel-bounded recursion is independent of the fuel once the fuel is at least the argument.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Section 1 (definition of `f(n)`). -/
theorem orderedFactorizationCountAux_eq (n : ℕ) :
    ∀ k, n ≤ k → orderedFactorizationCountAux k n = orderedFactorizationCount n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k hk
    unfold orderedFactorizationCount
    rcases n with _ | n
    · cases k <;> simp [orderedFactorizationCountAux]
    · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [orderedFactorizationCountAux]
      split_ifs
      · rfl
      · refine Finset.sum_congr rfl fun d hd => ?_
        have hdn := Nat.mem_properDivisors.mp hd
        rw [ih d hdn.2 k (by omega), ih d hdn.2 n (by omega)]

/-- The recursion `f(n) = Σ_{d ∣ n, d < n} f(d)` for `n ≥ 2` (split off the first factor).

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Section 1 (definition of `f(n)`). -/
theorem orderedFactorizationCount_eq_sum {n : ℕ} (hn : 2 ≤ n) :
    orderedFactorizationCount n = ∑ d ∈ n.properDivisors, orderedFactorizationCount d := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [orderedFactorizationCount, orderedFactorizationCountAux]
  split_ifs with h
  · omega
  refine Finset.sum_congr rfl fun d hd => ?_
  have := Nat.mem_properDivisors.mp hd
  exact orderedFactorizationCountAux_eq d m (by omega)

/-- `f(0) = 0`, `f(1) = 1`, `f(6) = 3` and `f(12) = 8`.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Section 1 (the eight ordered factorizations of `12`, Table 1 for `6`). -/
theorem orderedFactorizationCount_small :
    orderedFactorizationCount 0 = 0 ∧ orderedFactorizationCount 1 = 1 ∧
      orderedFactorizationCount 6 = 3 ∧ orderedFactorizationCount 12 = 8 := by
  decide

/-- `(1^3, 4)` is a perfect partition of `7`.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, example after Definition 1. -/
theorem isPerfectPartition_seven : IsPerfectPartition 7 {1, 1, 1, 4} := by
  unfold IsPerfectPartition subpartitionCount
  decide

/-- `(1^5, 2)` is a double-perfect partition of `7` (order `1`), and it is of Type A: it arises
from the perfect partition `(1^5)` of `5` by inserting the part `2`.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, example after Definition 3 and Table 3. -/
theorem isTypeADoublePerfect_one_seven : IsTypeADoublePerfect 1 7 {1, 1, 1, 1, 1, 2} := by
  refine ⟨?_, {1, 1, 1, 1, 1}, ?_, Or.inr ?_⟩
  · unfold IsDoublePerfectOfOrder subpartitionCount
    decide +kernel
  · unfold IsPerfectPartition subpartitionCount
    decide
  · decide

/-- Every double-perfect partition `λ ⊢ N` (order `1`) has the form
`(1^{q₁}, 2^{q₂}, B^{q₃}, (B(q₃+1))^{q₄}, (B(q₃+1)(q₄+1))^{q₅}, …)` with `B = q₁ + 2q₂ - 1`,
`q₁ ≥ 2`, `q₂, q₃, … ≥ 1`, and `q₁ ≠ 3 → q₂ = 1`. The tail is written as the image of
`perfectPartitionOfFactorization [q₃+1, q₄+1, …]` under multiplication by `B`. Added hypothesis
`N ≥ 4`: for `N ≤ 3` the defining condition is vacuous above uniqueness and, e.g., `(1^3) ⊢ 3`
qualifies.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Proposition 1 (Lee), display (3) (`integers-2025-A109-prop-1`). -/
public theorem_wanted doublePerfect_form (N : ℕ) (hN : 4 ≤ N) (l : Multiset ℕ)
    (hl : IsDoublePerfectOfOrder 1 N l) :
    ∃ q₁ q₂ : ℕ, ∃ qs : List ℕ, 2 ≤ q₁ ∧ 1 ≤ q₂ ∧ (∀ q ∈ qs, 1 ≤ q) ∧ (q₁ ≠ 3 → q₂ = 1) ∧
      l = Multiset.replicate q₁ 1 + Multiset.replicate q₂ 2 +
        (perfectPartitionOfFactorization (qs.map (· + 1))).map ((q₁ + 2 * q₂ - 1) * ·)

/-- Lee's count of double-perfect partitions: for `n ≥ 4`, `d(n) = f(n-1)` unless
`n ≡ 1 (mod 4)`, in which case `d(n) = f(n-1) - f((n-1)/4)`. Added hypothesis `n ≥ 4` (the
record says every positive `n`): for `n = 3` both perfect partitions `(1^3)` and `(1, 2)` qualify
vacuously while `f(2) = 1`, and for `n = 1` the partition `(1)` qualifies while `f(0) = 0`.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Theorem 1 (Lee), display (4) (`integers-2025-A109-thm-1`). -/
public theorem_wanted doublePerfect_ncard (n : ℕ) (hn : 4 ≤ n) :
    ({l | IsDoublePerfectOfOrder 1 n l}.ncard : ℤ) =
      if n % 4 = 1 then
        (orderedFactorizationCount (n - 1) : ℤ) - orderedFactorizationCount ((n - 1) / 4)
      else orderedFactorizationCount (n - 1)

/-- Every double-perfect partition of `N > 3` arises from a perfect partition `β` of `N - 2`,
either by inserting `1^2` when `1` has multiplicity `1` in `β` (the set `E(1^2)`), or by inserting
`2` when `2` is not a part of `β` (the set `W(2)`), and every such insertion is double-perfect:
`D(N) = E(1^2) ∪ W(2)`.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Proposition 2 (`integers-2025-A109-prop-2`). -/
public theorem_wanted isDoublePerfect_one_iff (N : ℕ) (hN : 3 < N) (l : Multiset ℕ) :
    IsDoublePerfectOfOrder 1 N l ↔ ∃ β, IsPerfectPartition (N - 2) β ∧
      ((β.count 1 = 1 ∧ l = β + {1, 1}) ∨ (2 ∉ β ∧ l = β + {2}))

/-- Every double-perfect partition (order `1`, `N ≥ 4`) has one of Lee's forms (5)
`(1^3, 2^{q₂}, (2(q₂+1))^{q₃}, (2(q₂+1)(q₃+1))^{q₄}, …)` with `q₂ > 1`, or (6)
`(1^{q₁}, 2, (q₁+1)^{q₃}, ((q₁+1)(q₃+1))^{q₄}, …)` with `q₁ ≥ 2`, all `qᵢ ≥ 1`; the tails are
written through `perfectPartitionOfFactorization`. Added hypothesis `N ≥ 4` as in
`doublePerfect_form`.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Corollary 1 with displays (5), (6) (`integers-2025-A109-cor-1`). -/
public theorem_wanted doublePerfect_lee_forms (N : ℕ) (hN : 4 ≤ N) (l : Multiset ℕ)
    (hl : IsDoublePerfectOfOrder 1 N l) :
    (∃ q₂ : ℕ, ∃ qs : List ℕ, 1 < q₂ ∧ (∀ q ∈ qs, 1 ≤ q) ∧
      l = Multiset.replicate 3 1 + Multiset.replicate q₂ 2 +
        (perfectPartitionOfFactorization (qs.map (· + 1))).map ((2 * (q₂ + 1)) * ·)) ∨
    (∃ q₁ : ℕ, ∃ qs : List ℕ, 2 ≤ q₁ ∧ (∀ q ∈ qs, 1 ≤ q) ∧
      l = Multiset.replicate q₁ 1 + {2} +
        (perfectPartitionOfFactorization (qs.map (· + 1))).map ((q₁ + 1) * ·))

/-- Type-A double-perfect partitions of order `r ≥ 1` of `N ≥ 2(r+1)` are exactly the partitions
`β ∪ (1^{r+1})` with `β` a perfect partition of `N - r - 1` in which `1` has multiplicity `r`,
and `β ∪ (r+1)` with `β` such a perfect partition in which `1` has multiplicity `≠ r` and
`r + 1` is not a part. Corrected reading: as printed, method II does not require `r + 1 ∉ β`,
and then `D_r(N) = A(1^{r+1}) ∪ B(r+1)` is false: for `r = 3`, `N = 11`, `β = (1, 2, 4)` is
perfect with one `1`, but `(1, 2, 4^2)` is not double-perfect of order `3` (it contains only one
partition of `4`). The added condition is the paper's own in the proof of Theorem 3, part (ia)
(if `β` already contains `r + 1`, "Method II does not apply"), and matches `W(2)` of
Proposition 2.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Theorem 2, display (13) (`integers-2025-A109-thm-2`). -/
public theorem_wanted isTypeADoublePerfect_iff (r N : ℕ) (hr : 1 ≤ r) (hN : 2 * (r + 1) ≤ N)
    (l : Multiset ℕ) :
    IsTypeADoublePerfect r N l ↔ ∃ β, IsPerfectPartition (N - r - 1) β ∧
      ((β.count 1 = r ∧ l = β + Multiset.replicate (r + 1) 1) ∨
        (β.count 1 ≠ r ∧ r + 1 ∉ β ∧ l = β + {r + 1}))

/-- Every Type-A double-perfect partition of `N` of order `r` has form (14)
`(1^{2r+1}, (r+1)^{a₂-1}, ((r+1)a₂)^{a₃-1}, …)`, coming from a factorization
`N - r = (r+1) a₂ ⋯ a_k`, or form (15), the perfect partition of a factorization
`N - r = a₁ a₂ ⋯ a_k` with `a₁ ≠ r + 1` plus one part `r + 1`. Factors are `≥ 2`.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Corollary 2 with displays (14)-(17) (`integers-2025-A109-cor-2`). -/
public theorem_wanted typeADoublePerfect_forms (r N : ℕ) (hr : 1 ≤ r) (hN : 2 * (r + 1) ≤ N)
    (l : Multiset ℕ) (hl : IsTypeADoublePerfect r N l) :
    (∃ as : List ℕ, (∀ a ∈ as, 2 ≤ a) ∧ (r + 1) * as.prod = N - r ∧
      l = Multiset.replicate (r + 1) 1 + perfectPartitionOfFactorization ((r + 1) :: as)) ∨
    (∃ as : List ℕ, (∀ a ∈ as, 2 ≤ a) ∧ as.prod = N - r ∧ as.head? ≠ some (r + 1) ∧
      l = perfectPartitionOfFactorization as + {r + 1})

/-- The number `d_r(N)` of Type-A double-perfect partitions of `N` of order `r`,
`1 ≤ r ≤ ⌊(N-2)/2⌋`: with `M = 2(r+1)`, `d_r(N)` is
`f(N-r) - f((N-r)/M) - (f(r+1) - 1) f((N-r)/(r+1))` if `N ≡ r (mod M)`,
`f(N-r) - (f(r+1) - 1) f((N-r)/(r+1))` if `N ≡ -1 (mod M)`, and `f(N-r)` otherwise. The record's
range `⌊(n-2)/2⌋` is read with `n = N`. The special cases (19), (20) for `r = 2, 3` are omitted.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Theorem 3, display (18) (`integers-2025-A109-thm-3`). -/
public theorem_wanted typeADoublePerfect_ncard (r N : ℕ) (hr : 1 ≤ r) (hN : 2 * (r + 1) ≤ N) :
    ({l | IsTypeADoublePerfect r N l}.ncard : ℤ) =
      if N % (2 * (r + 1)) = r then
        (orderedFactorizationCount (N - r) : ℤ) -
          orderedFactorizationCount ((N - r) / (2 * (r + 1))) -
          ((orderedFactorizationCount (r + 1) : ℤ) - 1) *
            orderedFactorizationCount ((N - r) / (r + 1))
      else if N % (2 * (r + 1)) = 2 * (r + 1) - 1 then
        (orderedFactorizationCount (N - r) : ℤ) -
          ((orderedFactorizationCount (r + 1) : ℤ) - 1) *
            orderedFactorizationCount ((N - r) / (r + 1))
      else orderedFactorizationCount (N - r)

/-- Inserting `m` copies of `n - r` into a Type-A double-perfect partition of `n` of order `r`
gives a Type-A double-perfect partition of `n + m(n - r)` of order `r`. Added hypothesis
`n ≥ 2(r+1)` (the range of display (12)): for `r = 1`, `n = 2`, `λ = (1^2)` (obtained from the
empty perfect partition) and `m = 2`, `(1^4)` is not double-perfect.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Proposition 3 (`integers-2025-A109-prop-3`). -/
public theorem_wanted isTypeADoublePerfect_add_replicate (r n : ℕ) (hr : 1 ≤ r)
    (hn : 2 * (r + 1) ≤ n) (l : Multiset ℕ) (hl : IsTypeADoublePerfect r n l) (m : ℕ) :
    IsTypeADoublePerfect r (n + m * (n - r)) (l + Multiset.replicate m (n - r))

/-- Inserting `m` copies of `n - r` into a double-perfect partition of `n` of order `r` gives a
double-perfect partition of `n + m(n - r)` of order `r`. Added hypothesis `n ≥ 2(r+1)` (the
range of display (12)): for `r = 1`, `n = 2`, `λ = (1^2)` and `m = 2`, `(1^4)` is not
double-perfect.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Theorem 4 (`integers-2025-A109-thm-4`). -/
public theorem_wanted isDoublePerfectOfOrder_add_replicate (r n : ℕ) (hr : 1 ≤ r)
    (hn : 2 * (r + 1) ≤ n) (l : Multiset ℕ) (hl : IsDoublePerfectOfOrder r n l) (m : ℕ) :
    IsDoublePerfectOfOrder r (n + m * (n - r)) (l + Multiset.replicate m (n - r))

/-- If `λ ∈ U_r(n)` has largest part `ℓ ≠ r + 1`, then `λ ∪ (ℓ) ∈ U_r(n + ℓ)`; and the condition
is needed: `(1^2, 3^4, 6) ∈ D_5(20)` but `(1^2, 3^4, 6^2) ∉ U_5(26)`. Added hypothesis
`n ≥ 2(r+1)` (the range of display (12)): for `r = 1`, `n = 3`, `λ = (1^3)`, `(1^4)` is not
double-perfect. The remark on when exceptions with `ℓ = r + 1` occur and the `E_3` examples are
omitted.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Corollary 3 (`integers-2025-A109-cor-3`). -/
public theorem_wanted isDoublePerfectOfOrder_add_largest :
    (∀ (r n : ℕ), 1 ≤ r → 2 * (r + 1) ≤ n → ∀ l : Multiset ℕ, IsDoublePerfectOfOrder r n l →
      l.sup ≠ r + 1 → IsDoublePerfectOfOrder r (n + l.sup) (l + {l.sup})) ∧
    IsTypeADoublePerfect 5 20 {1, 1, 3, 3, 3, 3, 6} ∧
    ¬ IsDoublePerfectOfOrder 5 26 {1, 1, 3, 3, 3, 3, 6, 6}

/-- Halved perfect partitions: let `2(N - r) = a₁ ⋯ a_j a_{j+1} ⋯ a_k` with factors `≥ 2`,
`a₁ ⋯ a_j = 2(r+1)`, `1 < j < k`, `a_j > 2` and `a_{j+1} > 2`. Then
`(1^{a₁-1}, a₁^{a₂-1}, …, (a₁⋯a_{j-1})^{a_j-1}, (a₁⋯a_j/2)^{a_{j+1}-1}, …, (a₁⋯a_{k-1}/2)^{a_k-1})`
is double-perfect of order `r` and is not of Type A (it lies in `E_r(N)`). With
`b = [a₁, …, a_j]` and `c = [a_{j+1}, …, a_k]` the partition is
`perfectPartitionOfFactorization b` plus `(r+1)` times `perfectPartitionOfFactorization c`.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Theorem 5 with conditions (23)-(25) and display (26)
(`integers-2025-A109-thm-5`). -/
public theorem_wanted halvedPerfect_isDoublePerfect_not_typeA (r N : ℕ) (hr : 1 ≤ r)
    (b c : List ℕ) (hb : ∀ a ∈ b, 2 ≤ a) (hc : ∀ a ∈ c, 2 ≤ a) (hblen : 2 ≤ b.length)
    (hc0 : c ≠ []) (hbprod : b.prod = 2 * (r + 1)) (hprod : (b ++ c).prod = 2 * (N - r))
    (hbj : ∀ x ∈ b.getLast?, 2 < x) (hcj : ∀ x ∈ c.head?, 2 < x) :
    IsDoublePerfectOfOrder r N
        (perfectPartitionOfFactorization b +
          (perfectPartitionOfFactorization c).map ((r + 1) * ·)) ∧
      ¬ IsTypeADoublePerfect r N
        (perfectPartitionOfFactorization b +
          (perfectPartitionOfFactorization c).map ((r + 1) * ·))

/-- The number `e_r(N)` of Type-B double-perfect partitions of `N` of order `r` (members of
`U_r(N)` not of Type A), `1 ≤ r ≤ ⌊(N-4)/3⌋`: with `M = 2(r+1)` and
`c = f(M) - 1 - f(r+1)`, `e_r(N)` is `c (f((N-r)/(r+1)) - f((N-r)/M))` if `N ≡ r (mod M)`,
`c f((N-r)/(r+1))` if `N ≡ -1 (mod M)`, and `0` otherwise. The record's range `⌊(n-4)/3⌋` is
read with `n = N`.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Theorem 6, display (27) (`integers-2025-A109-thm-6`). -/
public theorem_wanted typeBDoublePerfect_ncard (r N : ℕ) (hr : 1 ≤ r) (hN : 3 * r + 4 ≤ N) :
    ({l | IsDoublePerfectOfOrder r N l ∧ ¬ IsTypeADoublePerfect r N l}.ncard : ℤ) =
      if N % (2 * (r + 1)) = r then
        ((orderedFactorizationCount (2 * (r + 1)) : ℤ) - 1 - orderedFactorizationCount (r + 1)) *
          ((orderedFactorizationCount ((N - r) / (r + 1)) : ℤ) -
            orderedFactorizationCount ((N - r) / (2 * (r + 1))))
      else if N % (2 * (r + 1)) = 2 * (r + 1) - 1 then
        ((orderedFactorizationCount (2 * (r + 1)) : ℤ) - 1 - orderedFactorizationCount (r + 1)) *
          orderedFactorizationCount ((N - r) / (r + 1))
      else 0

/-- The number `u_r(N)` of all double-perfect partitions of `N` of order `r`,
`1 ≤ r ≤ ⌊(N-2)/2⌋`: with `M = 2(r+1)`, `u_r(N)` is
`f(N-r) + (f(M) - 2f(r+1)) f((N-r)/(r+1)) - (f(M) - f(r+1)) f((N-r)/M)` if `N ≡ r (mod M)`,
`f(N-r) + (f(M) - 2f(r+1)) f((N-r)/(r+1))` if `N ≡ -1 (mod M)`, and `f(N-r)` otherwise. The
record's range `⌊(n-2)/2⌋` is read with `n = N`.

Source: Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025),
Article A109, Theorem 7, display (28) (`integers-2025-A109-thm-7`). -/
public theorem_wanted doublePerfectOfOrder_ncard (r N : ℕ) (hr : 1 ≤ r)
    (hN : 2 * (r + 1) ≤ N) :
    ({l | IsDoublePerfectOfOrder r N l}.ncard : ℤ) =
      if N % (2 * (r + 1)) = r then
        (orderedFactorizationCount (N - r) : ℤ) +
          ((orderedFactorizationCount (2 * (r + 1)) : ℤ) - 2 * orderedFactorizationCount (r + 1)) *
            orderedFactorizationCount ((N - r) / (r + 1)) -
          ((orderedFactorizationCount (2 * (r + 1)) : ℤ) - orderedFactorizationCount (r + 1)) *
            orderedFactorizationCount ((N - r) / (2 * (r + 1)))
      else if N % (2 * (r + 1)) = 2 * (r + 1) - 1 then
        (orderedFactorizationCount (N - r) : ℤ) +
          ((orderedFactorizationCount (2 * (r + 1)) : ℤ) - 2 * orderedFactorizationCount (r + 1)) *
            orderedFactorizationCount ((N - r) / (r + 1))
      else orderedFactorizationCount (N - r)

end

end MetaMathlibExt
