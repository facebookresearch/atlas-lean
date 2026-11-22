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

/-- **Ones-diagonal determinant.** For natural numbers $p_1, \dots, p_k$, the determinant
$A_k(p_1, \dots, p_k)$ is the determinant of the $k \times k$ integer matrix with
$p_1, \dots, p_k$ on the diagonal and $1$ in every other entry. -/
def onesDiagDet {k : ℕ} (p : Fin k → ℕ) : ℤ :=
  Matrix.det (fun i j => if i = j then (p i : ℤ) else 1)

/-- **Bordered ones-diagonal matrix.** For natural numbers $p_1, \dots, p_k$, the
$(k+1) \times (k+1)$ integer matrix whose first row consists of ones and whose row $i + 1$, for
$1 \le i \le k$, has $p_i$ in column $i$ and $1$ in every other column. Equivalently, it is the
$k \times k$ matrix with diagonal entries $p_1, \dots, p_k$ and all other entries $1$, with a
column of ones appended on the right and then a row of ones placed on top. -/
def borderedOnesDiag {k : ℕ} (p : Fin k → ℕ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
  fun i j => if i = 0 then 1
    else if h : j.val + 1 = i.val then
      (p ⟨j.val, by have hi := i.isLt; omega⟩ : ℤ)
    else 1

/-- **Bordered ones-diagonal determinant.** For natural numbers $p_1, \dots, p_k$, the integer
$F_k(p_1, \dots, p_k)$ is $(-1)^k$ times the determinant of the bordered ones-diagonal matrix of
$p_1, \dots, p_k$: the $(k+1) \times (k+1)$ integer matrix whose first row consists of ones and
whose row $i + 1$, for $1 \le i \le k$, has $p_i$ in column $i$ and $1$ in every other column. -/
def borderedOnesDiagDet {k : ℕ} (p : Fin k → ℕ) : ℤ :=
  (-1 : ℤ) ^ k * (borderedOnesDiag p).det

/-- **The first primes.** For a natural number $k$, the $k$-tuple whose entry with index $i$, for
$0 \le i < k$, is the $(i+1)$-st prime; that is, the first $k$ primes $2, 3, 5, \dots$ in
increasing order. -/
noncomputable def firstPrimes (k : ℕ) : Fin k → ℕ :=
  fun i => Nat.nth Nat.Prime i.val

/-- **Residue hit count.** For natural numbers $p_1, \dots, p_k$, $r_1, \dots, r_k$ and $n$, the
residue hit count $\gamma(n)$ is the number of indices $i$ with $n \equiv r_i \pmod{p_i}$, that
is, the number of the residue classes $r_i \bmod p_i$ that contain $n$. -/
def residueHitCount {k : ℕ} (p r : Fin k → ℕ) (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => n % p i = r i % p i)).card

/-- **Number of available integers.** For natural numbers $p_1, \dots, p_k$ and $r_1, \dots, r_k$,
let $\gamma(n)$ be the number of indices $i$ with $n \equiv r_i \pmod{p_i}$, and call $n$ available
if $\gamma(n) \le 1$. This is the number of available integers $n$ with
$1 \le n \le p_1 p_2 \cdots p_k$. For the first $k$ primes it is the count written
$\mathrm{av}(k)$. -/
def availableCount {k : ℕ} (p r : Fin k → ℕ) : ℕ :=
  ((Finset.Icc 1 (∏ i, p i)).filter
    (fun n => residueHitCount p r n ≤ 1)).card

/-- **Free count.** For natural numbers $p_1, \dots, p_k$ and $r_1, \dots, r_k$, let $\gamma(n)$
be the number of indices $i$ with $n \equiv r_i \pmod{p_i}$. The free count is the number of
integers $n$ with $1 \le n \le p_1 \cdots p_k$ and $\gamma(n) = 0$.

When $p_1, \dots, p_k$ are the first $k$ primes, this is the count $\mathrm{free}(k)$ of
Pausinger's paper. -/
def freeCount {k : ℕ} (p r : Fin k → ℕ) : ℕ :=
  ((Finset.Icc 1 (∏ i, p i)).filter
    (fun n => residueHitCount p r n = 0)).card

/-- **Occupied count.** For natural numbers $p_1, \dots, p_k$ and $r_1, \dots, r_k$, let
$\gamma(n)$ be the number of indices $i$ with $n \equiv r_i \pmod{p_i}$. The occupied count is
the number of integers $n$ with $1 \le n \le p_1 \cdots p_k$ and $\gamma(n) > 1$.

When $p_1, \dots, p_k$ are the first $k$ primes, this is the count $\mathrm{occ}(k)$ of
Pausinger's paper. -/
def occupiedCount {k : ℕ} (p r : Fin k → ℕ) : ℕ :=
  ((Finset.Icc 1 (∏ i, p i)).filter
    (fun n => 1 < residueHitCount p r n)).card

/-- **Recurrence for the bordered determinants of the first primes.** Let $k \ge 2$ and let
$p_1, \dots, p_k$ be the first $k$ primes. For $m \le k$ let $f_m = F_m(p_1, \dots, p_m)$, where
$F_m(p_1, \dots, p_m)$ is $(-1)^m$ times the determinant of the $(m+1) \times (m+1)$ matrix whose
first row consists of ones and whose row $i + 1$, for $1 \le i \le m$, has $p_i$ in column $i$ and
$1$ in every other column. Then $f_k = (p_k - 1) f_{k-1}$.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Lemma 1. -/
theorem_wanted borderedOnesDiagDet_firstPrimes_recurrence (k : ℕ)
    (hk : 2 ≤ k) :
    borderedOnesDiagDet (firstPrimes k) =
      ((Nat.nth Nat.Prime (k - 1) : ℤ) - 1) *
        borderedOnesDiagDet (firstPrimes (k - 1))

/-- **Lemma 2, determinant recurrence.** Let $p_1 < p_2 < \cdots$ be the primes in increasing
order. For $m \ge 0$ let $a_m$ be the determinant of the $m \times m$ integer matrix with
$p_1, \dots, p_m$ on the diagonal and $1$ in every other entry, and let $f_m = (-1)^m \det B_m$,
where $B_m$ is the $(m+1) \times (m+1)$ integer matrix whose first row consists of ones and
whose row $i + 1$, for $1 \le i \le m$, has $p_i$ in column $i$ and $1$ in every other column.
Then for every $k \ge 2$, $a_k = f_{k-1} + (p_k - 1) \cdot a_{k-1}$.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Lemma 2. -/
theorem_wanted onesDiagDet_firstPrimes_recurrence (k : ℕ)
    (hk : 2 ≤ k) :
    onesDiagDet (firstPrimes k) =
      borderedOnesDiagDet (firstPrimes (k - 1)) +
        ((Nat.nth Nat.Prime (k - 1) : ℤ) - 1) *
          onesDiagDet (firstPrimes (k - 1))

/-- **Lemma 3, occupied recurrence.** Let $k \ge 1$, let $p_1 < p_2 < \cdots$ be the primes in
increasing order, and let $r_1, \dots, r_{k+1}$ be natural numbers. For $m \in \{k, k + 1\}$
write $P_m = p_1 \cdots p_m$, let $\gamma_m(n)$ be the number of $i \le m$ with
$n \equiv r_i \pmod{p_i}$, let $\mathrm{occ}(m)$ be the number of integers $n$ with
$1 \le n \le P_m$ and $\gamma_m(n) > 1$, and let $\mathrm{free}(m)$ be the number of those with
$\gamma_m(n) = 0$. Then
$\mathrm{occ}(k+1) + \mathrm{free}(k) = P_k + (p_{k+1} - 1) \cdot \mathrm{occ}(k)$.

In the paper's form this reads
$\mathrm{occ}(k+1) = P_k + (p_{k+1} - 1) \cdot \mathrm{occ}(k) - \mathrm{free}(k)$.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Lemma 3. -/
theorem_wanted occupiedCount_firstPrimes_succ_add_free (k : ℕ)
    (hk : 1 ≤ k) (r : Fin (k + 1) → ℕ) :
    occupiedCount (firstPrimes (k + 1)) r +
        freeCount (firstPrimes k) (r ∘ Fin.castSucc) =
      (∏ i : Fin k, Nat.nth Nat.Prime i.val) +
        (Nat.nth Nat.Prime k - 1) *
          occupiedCount (firstPrimes k) (r ∘ Fin.castSucc)

/-- **Lemma 3, free recurrence.** Let $k \ge 1$, let $p_1 < p_2 < \cdots$ be the primes in
increasing order, and let $r_1, \dots, r_{k+1}$ be natural numbers. For $m \in \{k, k + 1\}$
write $\mathrm{free}(m)$ for the number of integers $n$ with $1 \le n \le p_1 \cdots p_m$ such
that $n \not\equiv r_i \pmod{p_i}$ for every $i \le m$. Then
$\mathrm{free}(k+1) = (p_{k+1} - 1) \cdot \mathrm{free}(k)$.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Lemma 3. -/
theorem_wanted freeCount_firstPrimes_succ (k : ℕ) (hk : 1 ≤ k)
    (r : Fin (k + 1) → ℕ) :
    freeCount (firstPrimes (k + 1)) r =
      (Nat.nth Nat.Prime k - 1) *
        freeCount (firstPrimes k) (r ∘ Fin.castSucc)

/-- **Recurrence for the number of available integers.** Let $k \ge 1$, let $p_1, \dots, p_{k+1}$
be the first $k + 1$ primes, and let $r_1, \dots, r_{k+1}$ be any natural numbers. For $m = k$ and
$m = k + 1$, call an integer $n$ free if $n \not\equiv r_i \pmod{p_i}$ for every $i \le m$, and
available if $n \equiv r_i \pmod{p_i}$ for at most one $i \le m$; let $\mathrm{av}(m)$ and
$\mathrm{free}(m)$ be the numbers of available and of free integers $n$ with
$1 \le n \le p_1 \cdots p_m$. Then
$\mathrm{av}(k+1) = (p_{k+1} - 1) \cdot \mathrm{av}(k) + \mathrm{free}(k)$.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Lemma 4. -/
theorem_wanted availableCount_firstPrimes_succ (k : ℕ) (hk : 1 ≤ k)
    (r : Fin (k + 1) → ℕ) :
    availableCount (firstPrimes (k + 1)) r =
      (Nat.nth Nat.Prime k - 1) *
          availableCount (firstPrimes k) (r ∘ Fin.castSucc) +
        freeCount (firstPrimes k) (r ∘ Fin.castSucc)

/-- **Available integers for the first primes.** Let $k$ be a natural number, let
$p_1, \dots, p_k$ be the first $k$ primes, and let $r_1, \dots, r_k$ be any natural numbers. Call an
integer $n$ available if $n \equiv r_i \pmod{p_i}$ holds for at most one index $i$. Then the number
of available integers $n$ with $1 \le n \le p_1 p_2 \cdots p_k$ equals
$a_k = A_k(p_1, \dots, p_k)$, the determinant of the $k \times k$ matrix with diagonal entries
$p_1, \dots, p_k$ and all other entries $1$.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Theorem 1. -/
theorem_wanted availableCount_firstPrimes (k : ℕ)
    (r : Fin k → ℕ) :
    (availableCount (firstPrimes k) r : ℤ) =
      onesDiagDet (firstPrimes k)

/-- **Theorem 1, free count.** Let $k$ be a natural number, let $p_1 < \cdots < p_k$ be the
first $k$ primes and let $r_1, \dots, r_k$ be natural numbers. Then the number of integers $n$
with $1 \le n \le p_1 \cdots p_k$ such that $n \not\equiv r_i \pmod{p_i}$ for every $i$ equals
$f_k = (-1)^k \det B$, where $B$ is the $(k+1) \times (k+1)$ integer matrix whose first row
consists of ones and whose row $i + 1$, for $1 \le i \le k$, has $p_i$ in column $i$ and $1$ in
every other column.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Theorem 1. -/
theorem_wanted freeCount_firstPrimes (k : ℕ) (r : Fin k → ℕ) :
    (freeCount (firstPrimes k) r : ℤ) =
      borderedOnesDiagDet (firstPrimes k)

/-- **Available integers for two distinct primes.** Let $p \ne q$ be primes and let $r_1, r_2$ be
any natural numbers. Call an integer $n$ available if it satisfies at most one of the congruences
$n \equiv r_1 \pmod p$ and $n \equiv r_2 \pmod q$. Then the number of available integers $n$ with
$1 \le n \le pq$ equals $A_2(p, q)$, the determinant of the $2 \times 2$ matrix with diagonal
entries $p, q$ and both other entries $1$.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Lemma 5. -/
theorem_wanted availableCount_two_primes (p q : ℕ) (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (r : Fin 2 → ℕ) :
    (availableCount ![p, q] r : ℤ) = onesDiagDet ![p, q]

/-- **Lemma 5, free count.** Let $p$ and $q$ be distinct primes and let $r_1, r_2$ be natural
numbers. Then the number of integers $n$ with $1 \le n \le pq$ such that
$n \not\equiv r_1 \pmod p$ and $n \not\equiv r_2 \pmod q$ equals $F_2(p, q)$, where
$$F_2(p, q) = \det \begin{pmatrix} 1 & 1 & 1 \\ p & 1 & 1 \\ 1 & q & 1 \end{pmatrix}.$$

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Lemma 5. -/
theorem_wanted freeCount_two_primes (p q : ℕ) (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (r : Fin 2 → ℕ) :
    (freeCount ![p, q] r : ℤ) = borderedOnesDiagDet ![p, q]

/-- **Available integers for three distinct primes.** Let $p$, $q$, $s$ be pairwise distinct
primes and let $r_1, r_2, r_3$ be any natural numbers. Call an integer $n$ available if it satisfies
at most one of the congruences $n \equiv r_1 \pmod p$, $n \equiv r_2 \pmod q$ and
$n \equiv r_3 \pmod s$. Then the number of available integers $n$ with $1 \le n \le pqs$ equals
$A_3(p, q, s)$, the determinant of the $3 \times 3$ matrix with diagonal entries $p, q, s$ and all
other entries $1$.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Lemma 6. -/
theorem_wanted availableCount_three_primes (p q s : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hs : s.Prime) (hpq : p ≠ q)
    (hps : p ≠ s) (hqs : q ≠ s) (r : Fin 3 → ℕ) :
    (availableCount ![p, q, s] r : ℤ) = onesDiagDet ![p, q, s]

/-- **Available integers for distinct primes.** Let $k \ge 2$, let $p_1, \dots, p_k$ be pairwise
distinct primes, and let $r_1, \dots, r_k$ be any natural numbers. Call an integer $n$ available if
$n \equiv r_i \pmod{p_i}$ holds for at most one index $i$. Then the number of available integers $n$
with $1 \le n \le p_1 p_2 \cdots p_k$ equals $A_k(p_1, \dots, p_k)$, the determinant of the
$k \times k$ matrix with diagonal entries $p_1, \dots, p_k$ and all other entries $1$.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Theorem 2. -/
theorem_wanted availableCount_distinct_primes (k : ℕ) (hk : 2 ≤ k)
    (p : Fin k → ℕ) (hprime : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (r : Fin k → ℕ) :
    (availableCount p r : ℤ) = onesDiagDet p

/-- **Theorem 2, free count.** Let $k \ge 2$, let $p_1, \dots, p_k$ be distinct primes and
let $r_1, \dots, r_k$ be natural numbers. Then the number of integers $n$ with
$1 \le n \le p_1 p_2 \cdots p_k$ such that $n \not\equiv r_i \pmod{p_i}$ for every $i$ equals
$F_k(p_1, \dots, p_k) = (-1)^k \det B$, where $B$ is the $(k+1) \times (k+1)$ integer matrix
whose first row consists of ones and whose row $i + 1$, for $1 \le i \le k$, has $p_i$ in
column $i$ and $1$ in every other column.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Theorem 2. -/
theorem_wanted freeCount_distinct_primes (k : ℕ) (hk : 2 ≤ k)
    (p : Fin k → ℕ) (hprime : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (r : Fin k → ℕ) :
    (freeCount p r : ℤ) = borderedOnesDiagDet p

end MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted
