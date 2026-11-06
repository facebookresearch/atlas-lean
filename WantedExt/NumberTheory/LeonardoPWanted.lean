/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# On generalized Leonardo `p`-numbers

Statements from Kusrini, A. Putra, and K. Kuhapatanakul
as presented in "On Generalized Leonardo `p`-Numbers",
*Journal of Integer Sequences* 27 (2024), Article 24.4.6
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Kuhapatanakul/kuha13.tex>).

The Fibonacci `p`-numbers `F_p` (`F_p(0) = 0`,
`F_p(1) = ⋯ = F_p(p) = 1`, `F_p(n) = F_p(n-1) +
F_p(n-p-1)`), the generalized Leonardo `p`-numbers
`ℒ_{p,k}` (`1` on `[0, p]`,
`ℒ(n) = ℒ(n-1) + ℒ(n-p-1) + k`), and the two-sided
auxiliary sequences `A_p`, `B_p` (elements of the paper's
`H(p)`: `H(n) = H(n-1) + H(n-p) - H(n-2p-1)` on `ℤ`, with
the initial values on `[-p, p]` given in the paper) are
`leonardoPK`, `seqAZ`, `seqBZ` (the Fibonacci `p`-numbers are the existing `MetaMathlibExt.fibonacciP`, cast to `ℤ`). The companion
matrix `Q_p` (for `p ≥ 2`) is `companionQ`, from the
paper's displayed examples; Theorem 9's entry formula for
`Q_p^n` is `qPowEntry` (the paper's display of the `B`
rows has the index direction after the first entry
reversed relative to the actual powers; the formula here
is the one matching `Q_p^n`, verified entrywise). `R_{p,m}`
for `ℋ ∈ H(p)` is `rMatrix`. Proposition 7 and the matrix
results are stated for `p ≥ 2`, the range of the paper's
main-results section (Proposition 7(i) fails at `p = 1`).
Theorem 13's summation index `j` in `ℒ_{p,k}(m-j)` is the
printed typo for `i`.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.Recurrences.HonsbergerFibonacciP
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.LeonardoPWanted

/-- **Initial values of the generalized Leonardo $p$-numbers.** For natural numbers $p$, $k$
and $n$, this is the list of integers $(\mathcal{L}_{p,k}(0), \mathcal{L}_{p,k}(1), \dots,
\mathcal{L}_{p,k}(n))$ of length $n + 1$, where $\mathcal{L}_{p,k}(i) = 1$ for $0 \le i \le p$
and $\mathcal{L}_{p,k}(i) = \mathcal{L}_{p,k}(i-1) + \mathcal{L}_{p,k}(i-p-1) + k$ for $i > p$. -/
def leonardoPKSeq (p k : ℕ) : ℕ → List ℤ
  | 0 => [1]
  | n + 1 =>
      let prev := leonardoPKSeq p k n
      prev ++ [if n + 1 ≤ p then 1
        else prev.getD n 0 + prev.getD (n - p) 0 + (k : ℤ)]

/-- **Generalized Leonardo $p$-numbers.** For natural numbers $p$ and $k$, the generalized
Leonardo $p$-numbers are the integers $\mathcal{L}_{p,k}(n)$, $n \in \mathbb{N}$, given by
$\mathcal{L}_{p,k}(n) = 1$ for $0 \le n \le p$ and
$\mathcal{L}_{p,k}(n) = \mathcal{L}_{p,k}(n-1) + \mathcal{L}_{p,k}(n-p-1) + k$ for $n > p$. -/
def leonardoPK (p k n : ℕ) : ℤ := (leonardoPKSeq p k n).getD n 0

/-- **Forward evaluation of the $H(p)$ recurrence.** For a natural number $p$, a function
$s : \mathbb{Z} \to \mathbb{Z}$ and $n \in \mathbb{N}$, this is the list of the $2p + n + 1$
values at $-p, -p+1, \dots, p+n$ (the entry at position $i$ is the value at $i - p$) of the
sequence $H$ that equals $s$ on $[-p, p]$ and continues by the $H(p)$ recurrence
$H(t) = H(t-1) + H(t-p) - H(t-2p-1)$ for $t > p$. Each step appends one value to the previous
list, so evaluation takes polynomial time.

For $p = 0$, where this rule is circular, every appended value is $0$. -/
def hSeqForward (seedA : ℤ → ℤ) (p : ℕ) : ℕ → List ℤ
  | 0 => (List.range (2 * p + 1)).map fun i => seedA ((i : ℤ) - p)
  | n + 1 =>
      let prev := hSeqForward seedA p n
      prev ++ [prev.getD (2 * p + n) 0 + prev.getD (p + 1 + n) 0 -
        prev.getD n 0]

/-- **Backward evaluation of the $H(p)$ recurrence.** For a natural number $p$, a function
$s : \mathbb{Z} \to \mathbb{Z}$ and $n \in \mathbb{N}$, this is the list of the values at
$-p-n, \dots, p$ of the sequence $H$ that equals $s$ on $[-p, p]$ and continues to the left by
$H(t) = H(t+2p) + H(t+p+1) - H(t+2p+1)$ for $t < -p$, which is the $H(p)$ recurrence
$H(u) = H(u-1) + H(u-p) - H(u-2p-1)$ at $u = t+2p+1$ solved for $H(t)$. Each step prepends one
value to the previous list.

For $p = 0$, where this rule is circular, every prepended value equals $s(0)$. -/
def hSeqBackward (seedA : ℤ → ℤ) (p : ℕ) : ℕ → List ℤ
  | 0 => (List.range (2 * p + 1)).map fun i => seedA ((i : ℤ) - p)
  | n + 1 =>
      let prev := hSeqBackward seedA p n
      (prev.getD (2 * p - 1) 0 + prev.getD p 0 - prev.getD (2 * p) 0) ::
        prev

/-- **Two-sided extension of initial values by the $H(p)$ recurrence.** For a natural number
$p \ge 1$ and a function $s : \mathbb{Z} \to \mathbb{Z}$, this is the unique function
$H : \mathbb{Z} \to \mathbb{Z}$ that agrees with $s$ on $[-p, p]$ and satisfies
$H(t) = H(t-1) + H(t-p) - H(t-2p-1)$ for every integer $t$: its values at $t > p$ are computed
forward and its values at $t < -p$ backward from this recurrence. For $p = 0$ its value is $s(0)$
at every $t \le 0$ and $0$ at every $t > 0$. -/
def hSeqZ (seedA : ℤ → ℤ) (p : ℕ) (z : ℤ) : ℤ :=
  if -(p : ℤ) ≤ z then
    (hSeqForward seedA p (z + p).toNat).getD (z + p).toNat 0
  else
    (hSeqBackward seedA p (-(z + p)).toNat).getD 0 0

/-- **The sequence $A_p$.** For a natural number $p \ge 1$, $A_p : \mathbb{Z} \to \mathbb{Z}$ is
the unique sequence with $A_p(n) = 0$ for $-p \le n \le 0$ and $A_p(n) = 1$ for $1 \le n \le p$
that satisfies $A_p(n) = A_p(n-1) + A_p(n-p) - A_p(n-2p-1)$ for every integer $n$. For $p = 0$
it is the zero sequence. -/
def seqAZ (p : ℕ) (z : ℤ) : ℤ :=
  hSeqZ (fun w => if w ≤ 0 then 0 else 1) p z

/-- **The two-sided sequence $B_p$.** For a natural number $p \ge 1$, the sequence $B_p$ of
integers indexed by $\mathbb{Z}$ is the unique solution of the recurrence
$B_p(n) = B_p(n-1) + B_p(n-p) - B_p(n-2p-1)$ for every integer $n$ (the defining recurrence of
the paper's class $H(p)$) with initial values $B_p(n) = 1$ for $1 \le n \le p$,
$B_p(-p+1) = 1$, and $B_p(n) = 0$ for the other integers $n$ with $-p \le n \le 0$.

The definition also accepts $p = 0$, where the recurrence is trivial and the construction has no
mathematical meaning. -/
def seqBZ (p : ℕ) (z : ℤ) : ℤ :=
  hSeqZ (fun w => if w ≤ 0 then (if w = -(p : ℤ) + 1 then 1 else 0)
    else 1) p z

/-- **The companion matrix $Q_p$.** For a natural number $p$, $Q_p$ is the $(2p+1) \times (2p+1)$
integer matrix with rows and columns indexed by $0, 1, \dots, 2p$ whose entry $(2p, 0)$ is $-1$,
whose other entries $(0, 0)$, $(p-1, 0)$ and $(i, i+1)$ for $0 \le i < 2p$ are $1$, and whose
remaining entries are $0$. -/
def companionQ (p : ℕ) : Matrix (Fin (2 * p + 1)) (Fin (2 * p + 1)) ℤ :=
  Matrix.of fun i j =>
    if j.val = 0 ∧ i.val = 2 * p then -1
    else if (j.val = 0 ∧ (i.val = 0 ∨ i.val = p - 1)) ∨
        j.val = i.val + 1 then 1
    else 0

/-- **Entry formula for the powers of $Q_p$.** For natural numbers $p$ and $n$ and indices
$a, b \in \{0, 1, \dots, 2p\}$, the value is the integer $A_p(n + 1 - b)$ if $a = 0$, the integer
$B_p(n - p + 1 + a - b)$ if $1 \le a \le p - 1$, and the integer $-A_p(n - 2p + a - b)$ otherwise,
where $A_p$ and $B_p$ are the two-sided auxiliary sequences of the generalized Leonardo
$p$-numbers.

This is the formula of Theorem 9 of the source for the $(a, b)$ entry of $Q_p^n$, where $p \ge 2$
and $Q_p$ is the $(2p+1) \times (2p+1)$ companion matrix of the source, with the index direction
along the $B_p$ rows corrected (the source's display reverses it after the first entry). -/
def qPowEntry (p n : ℕ) (a b : Fin (2 * p + 1)) : ℤ :=
  if a.val = 0 then seqAZ p ((n : ℤ) + 1 - b.val)
  else if a.val ≤ p - 1 then seqBZ p ((n : ℤ) - p + 1 + a.val - b.val)
  else -seqAZ p ((n : ℤ) - (2 * p - a.val) - b.val)

/-- **The Hankel matrix $R_{p,m}$.** For a natural number $p$, a sequence
$H : \mathbb{Z} \to \mathbb{Z}$ and a natural number $m$, $R_{p,m}$ is the $(2p+1) \times (2p+1)$
integer matrix, with rows and columns indexed by $0, 1, \dots, 2p$, whose $(a, b)$ entry is
$H(m - a - b)$. -/
def rMatrix (p : ℕ) (H : ℤ → ℤ) (m : ℕ) :
    Matrix (Fin (2 * p + 1)) (Fin (2 * p + 1)) ℤ :=
  Matrix.of fun a b => H ((m : ℤ) - a.val - b.val)

/-- **Generalized Leonardo $p$-numbers in terms of Fibonacci $p$-numbers.** For all natural
numbers $p$, $k$ and $n$ with $p \ge 1$ and $k \ge 1$, the generalized Leonardo $p$-number
$\mathcal{L}_{p,k}(n)$ and the Fibonacci $p$-number $F_p(n+1)$ satisfy
$\mathcal{L}_{p,k}(n) = (k+1)F_p(n+1) - k$.

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6, Theorem 2. -/
theorem_wanted leonardoPK_eq (p k n : ℕ) (hp : 1 ≤ p)
    (hk : 1 ≤ k) :
    leonardoPK p k n = ((k : ℤ) + 1) * (MetaMathlibExt.fibonacciP p (n + 1) : ℤ) - (k : ℤ)

/-- **Partial sums of the generalized Leonardo $p$-numbers.** Let $p \ge 1$ and $k \ge 1$ be
natural numbers, and let $\mathcal{L}_{p,k}$ denote the generalized Leonardo $p$-numbers
($\mathcal{L}_{p,k}(j) = 1$ for $0 \le j \le p$ and
$\mathcal{L}_{p,k}(j) = \mathcal{L}_{p,k}(j-1) + \mathcal{L}_{p,k}(j-p-1) + k$ for $j > p$).
Then for every natural number $n$,
$\sum_{i=0}^{n} \mathcal{L}_{p,k}(i) = \mathcal{L}_{p,k}(n+p+1) - k(n+1) - 1$.

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6, Theorem 3. -/
theorem_wanted sum_leonardoPK (p k n : ℕ) (hp : 1 ≤ p)
    (hk : 1 ≤ k) :
    ∑ i ∈ Finset.range (n + 1), leonardoPK p k i =
      leonardoPK p k (n + p + 1) - (k : ℤ) * (n + 1) - 1

/-- **Stride sums of the generalized Leonardo $p$-numbers.** Let $p \ge 1$ and $k \ge 1$ be
natural numbers, and let $\mathcal{L}_{p,k}$ denote the generalized Leonardo $p$-numbers
($\mathcal{L}_{p,k}(j) = 1$ for $0 \le j \le p$ and
$\mathcal{L}_{p,k}(j) = \mathcal{L}_{p,k}(j-1) + \mathcal{L}_{p,k}(j-p-1) + k$ for $j > p$).
Then for all natural numbers $m \le p$ and $n$, the sum
$S = \sum_{i=0}^{n} \mathcal{L}_{p,k}((p+1)i + m)$ satisfies
$S = \mathcal{L}_{p,k}((p+1)n + m + 1) - kn$ if $m < p$, and
$S = \mathcal{L}_{p,k}((p+1)(n+1)) - k(n+1) - 1$ if $m = p$.

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6, Theorem 4. -/
theorem_wanted sum_leonardoPK_stride (p k m n : ℕ)
    (hp : 1 ≤ p) (hk : 1 ≤ k) (hm : m ≤ p) :
    ∑ i ∈ Finset.range (n + 1), leonardoPK p k ((p + 1) * i + m) =
      if m < p then
        leonardoPK p k ((p + 1) * n + m + 1) - (k : ℤ) * n
      else
        leonardoPK p k ((p + 1) * (n + 1)) - (k : ℤ) * (n + 1) - 1

/-- **Fibonacci $p$-numbers as differences of $A_p$.** For all natural numbers $p \ge 1$ and
$n \ge 1$, the Fibonacci $p$-number $F_p(n)$ equals $A_p(n) - A_p(n-p)$. Here
$A_p : \mathbb{Z} \to \mathbb{Z}$ is the sequence with $A_p(t) = 0$ for $-p \le t \le 0$,
$A_p(t) = 1$ for $1 \le t \le p$, and $A_p(t) = A_p(t-1) + A_p(t-p) - A_p(t-2p-1)$ for every
integer $t$.

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6, Theorem 5. -/
theorem_wanted fibonacciP_eq_seqAZ_sub (p n : ℕ) (hp : 1 ≤ p)
    (hn : 1 ≤ n) :
    (MetaMathlibExt.fibonacciP p n : ℤ) = seqAZ p (n : ℤ) - seqAZ p ((n : ℤ) - p)

/-- **The sequence $A_p$ as a sum of Fibonacci $p$-numbers.** For natural numbers $p$, $j$ and $m$
with $j < p$, the auxiliary sequence $A_p$ and the Fibonacci $p$-numbers $F_p$ satisfy
$A_p(mp + j) = \sum_{i=0}^{m} F_p(ip + j)$.

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6,
Corollary 6. -/
theorem_wanted seqAZ_eq_sum_fibonacciP (p j m : ℕ) (hp : 1 ≤ p)
    (hj : j < p) :
    seqAZ p ((m * p + j : ℕ) : ℤ) =
      ∑ i ∈ Finset.range (m + 1), (MetaMathlibExt.fibonacciP p (i * p + j) : ℤ)

/-- **Recurrence for the sequence $A_p$.** For natural numbers $p \ge 2$ and $n \ge 1$, the
auxiliary sequence $A_p$ satisfies $A_p(n) = A_p(n-1) + A_p(n-p-1) + 1$ if
$n \equiv 1 \pmod p$, and $A_p(n) = A_p(n-1) + A_p(n-p-1)$ otherwise.

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6,
Proposition 7. -/
theorem_wanted seqAZ_recurrence (p n : ℕ) (hp : 2 ≤ p)
    (hn : 1 ≤ n) :
    seqAZ p (n : ℤ) =
      seqAZ p ((n : ℤ) - 1) + seqAZ p ((n : ℤ) - p - 1) +
        (if n % p = 1 % p then 1 else 0)

/-- **Recurrence for the sequence $B_p$.** For natural numbers $p \ge 2$ and $n \ge 1$, the
auxiliary sequence $B_p$ satisfies $B_p(n) = B_p(n-1) + B_p(n-p-1) + \varepsilon$, where
$\varepsilon = 1$ if $n \equiv 1 \pmod p$, $\varepsilon = -1$ if $n \equiv 2 \pmod p$, and
$\varepsilon = 0$ otherwise. For $p = 2$ this means $\varepsilon = 1$ for odd $n$ and
$\varepsilon = -1$ for even $n$.

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6,
Proposition 7. -/
theorem_wanted seqBZ_recurrence (p n : ℕ) (hp : 2 ≤ p)
    (hn : 1 ≤ n) :
    seqBZ p (n : ℤ) =
      seqBZ p ((n : ℤ) - 1) + seqBZ p ((n : ℤ) - p - 1) +
        (if n % p = 1 % p then 1 else if n % p = 2 % p then -1 else 0)

/-- **Relation between the sequences $A_p$ and $B_p$.** For natural numbers $p \ge 2$ and $n$,
the auxiliary sequences $A_p$ and $B_p$ satisfy $A_p(n) = B_p(n+1) - 1$ if $p$ divides $n$, and
$A_p(n) = B_p(n+1)$ otherwise.

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6,
Proposition 8. -/
theorem_wanted seqAZ_eq_seqBZ (p n : ℕ) (hp : 2 ≤ p) :
    seqAZ p (n : ℤ) =
      if n % p = 0 then seqBZ p ((n : ℤ) + 1) - 1
      else seqBZ p ((n : ℤ) + 1)

/-- **Entries of the powers of the companion matrix $Q_p$.** Let $p \ge 2$ and $n$ be natural
numbers, and index the rows and columns of the $(2p+1) \times (2p+1)$ companion matrix $Q_p$ by
$0, 1, \dots, 2p$. Then for all indices $a$ and $b$, the entry $(a, b)$ of $Q_p^n$ equals
$A_p(n + 1 - b)$ if $a = 0$, equals $B_p(n - p + 1 + a - b)$ if $1 \le a \le p - 1$, and equals
$-A_p(n - (2p - a) - b)$ if $p \le a \le 2p$. Here $A_p, B_p : \mathbb{Z} \to \mathbb{Z}$ are the
sequences satisfying $S(t) = S(t-1) + S(t-p) - S(t-2p-1)$ for every integer $t$, with
$A_p(t) = 1$ for $1 \le t \le p$ and $A_p(t) = 0$ for $-p \le t \le 0$, and with $B_p(t) = 1$ for
$1 \le t \le p$ and for $t = -p+1$ and $B_p(t) = 0$ for the other $-p \le t \le 0$.

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6, Theorem 9. -/
theorem_wanted companionQ_pow_apply (p n : ℕ) (hp : 2 ≤ p)
    (a b : Fin (2 * p + 1)) :
    (companionQ p ^ n) a b = qPowEntry p n a b

/-- **Powers of $Q_p$ shift the Hankel matrices $R_{p,m}$.** Let $p \ge 2$ be a natural number and
let $H : \mathbb{Z} \to \mathbb{Z}$ satisfy $H(t) = H(t-1) + H(t-p) - H(t-2p-1)$ for every
integer $t$. For a natural number $m$, let $R_{p,m}$ be the $(2p+1) \times (2p+1)$ integer matrix
whose $(a, b)$ entry is $H(m - a - b)$ for $0 \le a, b \le 2p$, and let $Q_p$ be the
$(2p+1) \times (2p+1)$ companion matrix with entries $1$ at $(0, 0)$, at $(p-1, 0)$ and on the
superdiagonal, $-1$ at $(2p, 0)$, and $0$ elsewhere. Then $R_{p,m} Q_p^n = R_{p,m+n}$ for all
natural numbers $m \ge 1$ and $n$.

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6,
Theorem 10. -/
theorem_wanted rMatrix_mul_companionQ_pow (p : ℕ) (hp : 2 ≤ p)
    (H : ℤ → ℤ)
    (hH : ∀ n : ℤ, H n = H (n - 1) + H (n - p) - H (n - 2 * p - 1))
    (m n : ℕ) (hm : 1 ≤ m) :
    rMatrix p H m * companionQ p ^ n = rMatrix p H (m + n)

/-- **Convolution identity for sequences in $H(p)$.** Let $p \ge 2$ be a natural number and let
$\mathcal{H} : \mathbb{Z} \to \mathbb{Z}$ be a sequence in $H(p)$, that is,
$\mathcal{H}(t) = \mathcal{H}(t-1) + \mathcal{H}(t-p) - \mathcal{H}(t-2p-1)$ for every integer
$t$. Then for all natural numbers $m \ge 1$ and $n \ge 1$,
$$
\mathcal{H}(m+n) = \mathcal{H}(m)A_p(n+1) + \sum_{i=1}^{p-1} \mathcal{H}(m-i)B_p(n-p+i+1) -
\sum_{i=0}^{p} \mathcal{H}(m-p-i)A_p(n-p+i),
$$
where $A_p, B_p : \mathbb{Z} \to \mathbb{Z}$ are the sequences in $H(p)$ with $A_p(t) = 1$ for
$1 \le t \le p$ and $A_p(t) = 0$ for $-p \le t \le 0$, and with $B_p(t) = 1$ for $1 \le t \le p$
and for $t = -p+1$ and $B_p(t) = 0$ for the other $-p \le t \le 0$.

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6,
Corollary 11. -/
theorem_wanted h_add_eq (p : ℕ) (hp : 2 ≤ p) (H : ℤ → ℤ)
    (hH : ∀ n : ℤ, H n = H (n - 1) + H (n - p) - H (n - 2 * p - 1))
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    H ((m : ℤ) + n) =
      H (m : ℤ) * seqAZ p ((n : ℤ) + 1) +
        ∑ i ∈ Finset.Icc 1 (p - 1), H ((m : ℤ) - i) *
          seqBZ p ((n : ℤ) - p + i + 1) -
        ∑ i ∈ Finset.range (p + 1), H ((m : ℤ) - p - i) *
          seqAZ p ((n : ℤ) - p + i)

/-- **Sums of $p+1$ consecutive Fibonacci $p$-numbers.** Let $p \ge 1$ and $n \ge 1$ be natural
numbers and let $k$ be a natural number. Let $F_p$ denote the Fibonacci $p$-numbers
($F_p(0) = 0$, $F_p(m) = 1$ for $1 \le m \le p$, and $F_p(m) = F_p(m-1) + F_p(m-p-1)$ for
$m > p$), and let $\mathcal{L}_{p,k}$ denote the generalized Leonardo $p$-numbers
($\mathcal{L}_{p,k}(m) = 1$ for $0 \le m \le p$ and
$\mathcal{L}_{p,k}(m) = \mathcal{L}_{p,k}(m-1) + \mathcal{L}_{p,k}(m-p-1) + k$ for $m > p$).
Then $(k+1) \sum_{i=0}^{p} F_p(n+i) = \mathcal{L}_{p,k}(n+2p-1) + k$.

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6, Lemma 12. -/
theorem_wanted succ_mul_sum_fibonacciP (p k n : ℕ) (hp : 1 ≤ p)
    (hn : 1 ≤ n) :
    ((k : ℤ) + 1) * ∑ i ∈ Finset.range (p + 1), (MetaMathlibExt.fibonacciP p (n + i) : ℤ) =
      leonardoPK p k (n + 2 * p - 1) + (k : ℤ)

/-- **Generalized Leonardo $p$-numbers at integer arguments.** For natural numbers $p$ and $k$
and an integer $z$, the value is the generalized Leonardo $p$-number $\mathcal{L}_{p,k}(z)$ if
$z \ge 0$, and $-k$ if $z < 0$.

For $-p \le z \le -1$ these are the values $\mathcal{L}_{p,k}(z) = -k$ obtained by running the
recurrence $\mathcal{L}_{p,k}(n) = \mathcal{L}_{p,k}(n-1) + \mathcal{L}_{p,k}(n-p-1) + k$
backwards; below $-p$ they need not be, but Theorem 13 of the source only uses arguments
$z \ge -p$. -/
def leonardoPKZ (p k : ℕ) (z : ℤ) : ℤ :=
  if 0 ≤ z then leonardoPK p k z.toNat else -(k : ℤ)

/-- **Honsberger-type identity for generalized Leonardo $p$-numbers.** Let $p$, $k$, $m$ and $n$
be natural numbers with $p, k, m, n \ge 1$. Write $\mathcal{L}$ for the generalized Leonardo
$p$-numbers $\mathcal{L}_{p,k}$, extended to negative integers by $\mathcal{L}(t) = -k$ for
$t < 0$. Then
$$
\mathcal{L}(m)\mathcal{L}(n+1) + \sum_{i=1}^{p} \mathcal{L}(m-i)\mathcal{L}(n-p+i) =
(k+1)\mathcal{L}(m+n+1) - k\bigl(\mathcal{L}(m+p) + \mathcal{L}(n+p+1)\bigr) + pk^2 + k.
$$

The arguments that occur are at least $-p$, and on $[-p, -1]$ the value $-k$ is the one forced by
the recurrence $\mathcal{L}(t) = \mathcal{L}(t-1) + \mathcal{L}(t-p-1) + k$ read backwards. The
paper prints the summation index as $j$ in $\mathcal{L}(m-j)$; it is corrected to $i$ here.

Source: "On Generalized Leonardo `p`-Numbers", Journal
of Integer Sequences 27 (2024), Article 24.4.6,
Theorem 13. -/

theorem_wanted leonardoPK_honsberger (p k m n : ℕ)
    (hp : 1 ≤ p) (hk : 1 ≤ k) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    leonardoPK p k m * leonardoPK p k (n + 1) +
        ∑ i ∈ Finset.Icc 1 p, leonardoPKZ p k ((m : ℤ) - i) *
          leonardoPKZ p k ((n : ℤ) - p + i) =
      ((k : ℤ) + 1) * leonardoPK p k (m + n + 1) -
        (k : ℤ) * (leonardoPK p k (m + p) +
          leonardoPK p k (n + p + 1)) +
        (p : ℤ) * k ^ 2 + (k : ℤ)

end MathlibExt.NumberTheory.LeonardoPWanted
