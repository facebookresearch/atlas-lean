/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Counting appearances of integers in sets of arithmetic progressions

Statements from Florian Pausinger, "Counting Appearances of
Integers in Sets of Arithmetic Progressions", *INTEGERS* 26
(2026), Article A50
(<https://math.colgate.edu/~integers/aa50/aa50.pdf>),
DOI `10.5281/zenodo.19949416`.

For primes `p : Fin k → ℕ` and a choice `r : Fin k → ℕ` of
residue classes, `γ(n) = #{i : n ≡ r i (mod p i)}` counts the
chosen residue classes containing `n`; `n ∈ [1, ∏ i, p i]` is
*free* if `γ(n) = 0`, *available* if `γ(n) ≤ 1`, and *occupied*
if `γ(n) > 1`.  The paper's sequences are determinants:
`A_k(p_1, …, p_k)` is the determinant of the `k × k` matrix of
ones with `p_1, …, p_k` on the diagonal, and `F_k` is `(-1)^k`
times the determinant of the `(k+1) × (k+1)` matrix obtained by
bordering it with a first row and last column of ones.  For the
first `k` primes these are the paper's `a_k` (OEIS A067549:
`2, 5, 22, 140, 1448, …`) and `f_k` (OEIS A005867:
`1, 2, 8, 48, 480, …`), with `Nat.nth Nat.Prime` zero-indexed.

Lemmas 3-4 compare the first `k + 1` primes with the first `k`;
the restriction of the residue choice is `r ∘ Fin.castSucc`, and
the last prime is `Nat.nth Nat.Prime k`.  Lemma 3's occupied
recurrence is written without subtraction:
`occ(k+1) + free(k) = P_k + (p_{k+1} - 1)·occ(k)`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted

/-- The determinant of the matrix of ones with `p` on the
diagonal: the paper's `A_k(p_1, …, p_k)`. -/
def onesDiagDet {k : ℕ} (p : Fin k → ℕ) : ℤ :=
  Matrix.det (fun i j => if i = j then (p i : ℤ) else 1)

/-- The `(k+1) × (k+1)` bordered matrix in the definition of
`F_k`: first row of ones, and row `i + 1` equal to row `i` of the
ones/diagonal matrix followed by a final `1`. -/
def borderedOnesDiag {k : ℕ} (p : Fin k → ℕ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
  fun i j => if i = 0 then 1
    else if h : j.val + 1 = i.val then
      (p ⟨j.val, by have hi := i.isLt; omega⟩ : ℤ)
    else 1

/-- `F_k(p_1, …, p_k) = (-1)^k det` of the bordered matrix. -/
def borderedOnesDiagDet {k : ℕ} (p : Fin k → ℕ) : ℤ :=
  (-1 : ℤ) ^ k * (borderedOnesDiag p).det

/-- The first `k` primes, `p i = ` the `(i+1)`-st prime. -/
noncomputable def firstPrimes (k : ℕ) : Fin k → ℕ :=
  fun i => Nat.nth Nat.Prime i.val

/-- `γ(n)`: the number of chosen residue classes containing
`n`. -/
def residueHitCount {k : ℕ} (p r : Fin k → ℕ) (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => n % p i = r i % p i)).card

/-- The number of available integers in `[1, ∏ i, p i]`
(`γ(n) ≤ 1`): the paper's `av(k)` for the first `k` primes. -/
def availableCount {k : ℕ} (p r : Fin k → ℕ) : ℕ :=
  ((Finset.Icc 1 (∏ i, p i)).filter
    (fun n => residueHitCount p r n ≤ 1)).card

/-- The number of free integers in `[1, ∏ i, p i]` (`γ(n) = 0`):
the paper's `free(k)` for the first `k` primes. -/
def freeCount {k : ℕ} (p r : Fin k → ℕ) : ℕ :=
  ((Finset.Icc 1 (∏ i, p i)).filter
    (fun n => residueHitCount p r n = 0)).card

/-- The number of occupied integers in `[1, ∏ i, p i]`
(`γ(n) > 1`): the paper's `occ(k)` for the first `k` primes. -/
def occupiedCount {k : ℕ} (p r : Fin k → ℕ) : ℕ :=
  ((Finset.Icc 1 (∏ i, p i)).filter
    (fun n => 1 < residueHitCount p r n)).card

/-- **Lemma 1**: `f_k = (p_k - 1)·f_{k-1}` for `k ≥ 2`, where
`p_k` is the `k`-th prime.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Lemma 1. -/
theorem_wanted borderedOnesDiagDet_firstPrimes_recurrence (k : ℕ)
    (hk : 2 ≤ k) :
    borderedOnesDiagDet (firstPrimes k) =
      ((Nat.nth Nat.Prime (k - 1) : ℤ) - 1) *
        borderedOnesDiagDet (firstPrimes (k - 1))

/-- **Lemma 2**: `a_k = f_{k-1} + (p_k - 1)·a_{k-1}` for
`k ≥ 2`.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Lemma 2. -/
theorem_wanted onesDiagDet_firstPrimes_recurrence (k : ℕ)
    (hk : 2 ≤ k) :
    onesDiagDet (firstPrimes k) =
      borderedOnesDiagDet (firstPrimes (k - 1)) +
        ((Nat.nth Nat.Prime (k - 1) : ℤ) - 1) *
          onesDiagDet (firstPrimes (k - 1))

/-- **Lemma 3, occupied recurrence**:
`occ(k+1) + free(k) = P_k + (p_{k+1} - 1)·occ(k)` for every
choice of residue classes (paper form
`occ(k+1) = P_k + (p_{k+1} - 1)·occ(k) - free(k)`).

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Lemma 3. -/
theorem_wanted occupiedCount_firstPrimes_succ_add_free (k : ℕ)
    (hk : 1 ≤ k) (r : Fin (k + 1) → ℕ) :
    occupiedCount (firstPrimes (k + 1)) r +
        freeCount (firstPrimes k) (r ∘ Fin.castSucc) =
      (∏ i : Fin k, Nat.nth Nat.Prime i.val) +
        (Nat.nth Nat.Prime k - 1) *
          occupiedCount (firstPrimes k) (r ∘ Fin.castSucc)

/-- **Lemma 3, free recurrence**:
`free(k+1) = (p_{k+1} - 1)·free(k)` for every choice of residue
classes.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Lemma 3. -/
theorem_wanted freeCount_firstPrimes_succ (k : ℕ) (hk : 1 ≤ k)
    (r : Fin (k + 1) → ℕ) :
    freeCount (firstPrimes (k + 1)) r =
      (Nat.nth Nat.Prime k - 1) *
        freeCount (firstPrimes k) (r ∘ Fin.castSucc)

/-- **Lemma 4**: `av(k+1) = (p_{k+1} - 1)·av(k) + free(k)` for
every choice of residue classes.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Lemma 4. -/
theorem_wanted availableCount_firstPrimes_succ (k : ℕ) (hk : 1 ≤ k)
    (r : Fin (k + 1) → ℕ) :
    availableCount (firstPrimes (k + 1)) r =
      (Nat.nth Nat.Prime k - 1) *
          availableCount (firstPrimes k) (r ∘ Fin.castSucc) +
        freeCount (firstPrimes k) (r ∘ Fin.castSucc)

/-- **Theorem 1, available count**: for every choice of residue
classes modulo the first `k` primes, the number of available
integers in `[1, P_k]` is `a_k`.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Theorem 1. -/
theorem_wanted availableCount_firstPrimes (k : ℕ)
    (r : Fin k → ℕ) :
    (availableCount (firstPrimes k) r : ℤ) =
      onesDiagDet (firstPrimes k)

/-- **Theorem 1, free count**: for every choice of residue
classes modulo the first `k` primes, the number of free integers
in `[1, P_k]` is `f_k`.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Theorem 1. -/
theorem_wanted freeCount_firstPrimes (k : ℕ) (r : Fin k → ℕ) :
    (freeCount (firstPrimes k) r : ℤ) =
      borderedOnesDiagDet (firstPrimes k)

/-- **Lemma 5, available count**: for two distinct primes and
any residue classes, the number of available integers in
`[1, p·q]` is `A_2(p, q)`.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Lemma 5. -/
theorem_wanted availableCount_two_primes (p q : ℕ) (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (r : Fin 2 → ℕ) :
    (availableCount ![p, q] r : ℤ) = onesDiagDet ![p, q]

/-- **Lemma 5, free count**: for two distinct primes and any
residue classes, the number of free integers in `[1, p·q]` is
`F_2(p, q)`.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Lemma 5. -/
theorem_wanted freeCount_two_primes (p q : ℕ) (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (r : Fin 2 → ℕ) :
    (freeCount ![p, q] r : ℤ) = borderedOnesDiagDet ![p, q]

/-- **Lemma 6**: for three distinct primes and any residue
classes, the number of available integers in `[1, p·q·s]` is
`A_3(p, q, s)`.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Lemma 6. -/
theorem_wanted availableCount_three_primes (p q s : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hs : s.Prime) (hpq : p ≠ q)
    (hps : p ≠ s) (hqs : q ≠ s) (r : Fin 3 → ℕ) :
    (availableCount ![p, q, s] r : ℤ) = onesDiagDet ![p, q, s]

/-- **Theorem 2, available count**: for `k ≥ 2` distinct primes
and any residue classes, the number of available integers in
`[1, P_k]` is `A_k(p_1, …, p_k)`.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Theorem 2. -/
theorem_wanted availableCount_distinct_primes (k : ℕ) (hk : 2 ≤ k)
    (p : Fin k → ℕ) (hprime : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (r : Fin k → ℕ) :
    (availableCount p r : ℤ) = onesDiagDet p

/-- **Theorem 2, free count**: for `k ≥ 2` distinct primes and
any residue classes, the number of free integers in `[1, P_k]`
is `F_k(p_1, …, p_k)`.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Theorem 2. -/
theorem_wanted freeCount_distinct_primes (k : ℕ) (hk : 2 ≤ k)
    (p : Fin k → ℕ) (hprime : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (r : Fin k → ℕ) :
    (freeCount p r : ℤ) = borderedOnesDiagDet p

end MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted
