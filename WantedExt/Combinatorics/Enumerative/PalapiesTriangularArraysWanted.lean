/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Int.GCD
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Palapies, triangular arrays at negative row indices — wishlist

Statement-only records for Lars Palapies' INTEGERS 26 (2026) paper. A triangular
array `a_{n,k}` (`n, k ≥ 0`) satisfies the linear recurrence (1)
`a_{n,k} = (αn + βk + γ) a_{n-1,k} + (α'n + β'k + γ') a_{n-1,k-1}` with
`a_{n,-1} = 0`, `a_{0,k} = δ_{k=0}` and integer parameters. Definitions 1 and 2 of
the paper continue it to all `n, k ∈ ℤ` (negative-positive `a^{NP}` and
negative-negative `a^{NN}` numbers) by running (1) backwards; the divisions are in
`ℚ`, where a zero denominator gives the junk value `0` (the paper assumes the
denominators do not vanish, and calls the numbers non-existent otherwise).

Theorem 2 (Hankel-transform representation) is not formalized: its hypotheses
(a)–(d) evaluate the generating function `F(u, y)` of the `a_{n,k}` with `n ≥ 0`
along a real integration range reaching `1/α` or `±∞`, i.e. an analytic
continuation of the closed form (7) (complex powers, seven limiting cases) whose
branch and domain the paper does not pin down.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Triangular recurrence.** A triangular recurrence is a tuple
$(\alpha, \beta, \gamma; \alpha', \beta', \gamma')$ of six integers, the parameters of the linear
recurrence
$$
a_{n,k} = (\alpha n + \beta k + \gamma)\, a_{n-1,k} +
  (\alpha' n + \beta' k + \gamma')\, a_{n-1,k-1}.
$$

Source: Lars Palapies, *On Extensions of Triangular Arrays to Negative Row Indices
and Their Generating Functions*, INTEGERS 26 (2026), Article A83, Equation (1). -/
public structure TriangularRecurrence where
  /-- The coefficient `α` of `n` in the first weight. -/
  α : ℤ
  /-- The coefficient `β` of `k` in the first weight. -/
  β : ℤ
  /-- The constant `γ` of the first weight. -/
  γ : ℤ
  /-- The coefficient `α'` of `n` in the second weight. -/
  α' : ℤ
  /-- The coefficient `β'` of `k` in the second weight. -/
  β' : ℤ
  /-- The constant `γ'` of the second weight. -/
  γ' : ℤ

namespace TriangularRecurrence

/-- **Triangular array of a linear recurrence.** Given integer parameters
$(\alpha, \beta, \gamma; \alpha', \beta', \gamma')$, the array $a_{n,k} \in \mathbb{Q}$,
$n, k \ge 0$, is defined by $a_{0,k} = \delta_{k,0}$ and, for $n \ge 1$, by the recurrence (1)
$a_{n,k} = (\alpha n + \beta k + \gamma)\, a_{n-1,k} +
(\alpha' n + \beta' k + \gamma')\, a_{n-1,k-1}$, where $a_{n-1,-1} = 0$.

Source: Lars Palapies, *On Extensions of Triangular Arrays to Negative Row Indices
and Their Generating Functions*, INTEGERS 26 (2026), Article A83, Equation (1). -/
public def array (P : TriangularRecurrence) : ℕ → ℕ → ℚ
  | 0, k => if k = 0 then 1 else 0
  | n + 1, 0 => (P.α * (n + 1) + P.γ) * array P n 0
  | n + 1, k + 1 => (P.α * (n + 1) + P.β * (k + 1) + P.γ) * array P n (k + 1) +
      (P.α' * (n + 1) + P.β' * (k + 1) + P.γ') * array P n k

/-- **The binomial array at $(4, 2)$.** For the parameters
$(\alpha, \beta, \gamma; \alpha', \beta', \gamma') = (0, 0, 1; 0, 0, 1)$ of the binomial
coefficients (Table 1), the triangular array $a$ satisfies $a_{4,2} = 6$.

Source: Lars Palapies, *On Extensions of Triangular Arrays to Negative Row Indices
and Their Generating Functions*, INTEGERS 26 (2026), Article A83, Table 1. -/
public theorem array_binomial_four_two : array ⟨0, 0, 1, 0, 0, 1⟩ 4 2 = 6 := by
  simp [array]
  norm_num

/-- **First weight of a triangular recurrence.** For a triangular recurrence with parameters
$(\alpha, \beta, \gamma; \alpha', \beta', \gamma')$ and integers $n, k$, the first weight is the
rational number $\alpha(n + 1) + \beta k + \gamma$.

It is the divisor in the recurrence defining the negative-positive number $a^{NP}_{n,k}$.

Source: Lars Palapies, *On Extensions of Triangular Arrays to Negative Row Indices
and Their Generating Functions*, INTEGERS 26 (2026), Article A83, Definition 1. -/
public def weight (P : TriangularRecurrence) (n k : ℤ) : ℚ :=
  P.α * (n + 1) + P.β * k + P.γ

/-- **Second weight of a triangular recurrence.** For a triangular recurrence with parameters
$(\alpha, \beta, \gamma; \alpha', \beta', \gamma')$ and integers $n, k$, the second weight is the
rational number $\alpha'(n + 1) + \beta' k + \gamma'$.

It is the divisor in the recurrence defining the negative-negative number $a^{NN}_{n,k-1}$.

Source: Lars Palapies, *On Extensions of Triangular Arrays to Negative Row Indices
and Their Generating Functions*, INTEGERS 26 (2026), Article A83, Definition 2. -/
public def weight' (P : TriangularRecurrence) (n k : ℤ) : ℚ :=
  P.α' * (n + 1) + P.β' * k + P.γ'

/-- **Negative-positive numbers at negative rows (auxiliary).** For integer parameters
$(\alpha, \beta, \gamma; \alpha', \beta', \gamma')$ and $p, k \ge 0$, put $n = -(p + 1)$. The
rational numbers $c_{p,k}$ are defined by recursion on $p$ and then on $k$ through
$c_{p,k} = (r - (\alpha'(n+1) + \beta' k + \gamma')\, s) / (\alpha(n+1) + \beta k + \gamma)$,
where $r = c_{p-1,k}$ if $p \ge 1$, $r = 1$ if $p = k = 0$, and $r = 0$ if $p = 0 < k$; and
$s = c_{p,k-1}$ if $k \ge 1$, $s = 0$ if $k = 0$. Division by $0$ gives $0$.

Source: Lars Palapies, *On Extensions of Triangular Arrays to Negative Row Indices
and Their Generating Functions*, INTEGERS 26 (2026), Article A83, Definition 1. -/
public def negPosAux (P : TriangularRecurrence) : ℕ → ℕ → ℚ
  | 0, 0 => 1 / P.weight (-1) 0
  | 0, k + 1 => (0 - P.weight' (-1) (k + 1) * negPosAux P 0 k) / P.weight (-1) (k + 1)
  | p + 1, 0 => negPosAux P p 0 / P.weight (-(p + 2)) 0
  | p + 1, k + 1 => (negPosAux P p (k + 1) -
      P.weight' (-(p + 2)) (k + 1) * negPosAux P (p + 1) k) / P.weight (-(p + 2)) (k + 1)

/-- **Negative-positive numbers.** Let $a_{n,k}$ ($n, k \ge 0$) be the triangular array of a
triangular recurrence with parameters $(\alpha, \beta, \gamma; \alpha', \beta', \gamma')$. Its
negative-positive numbers $a^{NP}_{n,k} \in \mathbb{Q}$, for $n, k \in \mathbb{Z}$, are defined by
$a^{NP}_{n,k} = a_{n,k}$ for $n, k \ge 0$, $a^{NP}_{n,k} = 0$ for $k < 0$, and, for $n < 0 \le k$,
recursively by
$$
a^{NP}_{n,k} = \frac{a^{NP}_{n+1,k} - (\alpha'(n+1) + \beta' k + \gamma')\, a^{NP}_{n,k-1}}
  {\alpha(n+1) + \beta k + \gamma},
$$
where division by $0$ gives $0$.

Source: Lars Palapies, *On Extensions of Triangular Arrays to Negative Row Indices
and Their Generating Functions*, INTEGERS 26 (2026), Article A83, Definition 1. -/
public def negPos (P : TriangularRecurrence) : ℤ → ℤ → ℚ
  | .ofNat n, .ofNat k => P.array n k
  | .negSucc p, .ofNat k => P.negPosAux p k
  | _, .negSucc _ => 0

/-- **The negative-positive number at $(-1, 0)$.** For every triangular recurrence with
parameters $(\alpha, \beta, \gamma; \alpha', \beta', \gamma')$, its negative-positive number at
row $-1$ and column $0$ is $a^{NP}_{-1,0} = 1/\gamma$, computed in $\mathbb{Q}$ with $1/0 = 0$.

Source: Lars Palapies, *On Extensions of Triangular Arrays to Negative Row Indices
and Their Generating Functions*, INTEGERS 26 (2026), Article A83, Definition 1. -/
public theorem negPos_neg_one_zero (P : TriangularRecurrence) :
    P.negPos (-1) 0 = 1 / P.γ := by
  change P.negPosAux 0 0 = _
  simp [negPosAux, weight]

/-- **Recurrence for the negative-positive numbers.** For every triangular recurrence with
parameters $(\alpha, \beta, \gamma; \alpha', \beta', \gamma')$ and all integers $n \le -2$ and
$k \ge 1$, the negative-positive numbers satisfy
$$
a^{NP}_{n,k} = \frac{a^{NP}_{n+1,k} - (\alpha'(n+1) + \beta' k + \gamma')\, a^{NP}_{n,k-1}}
  {\alpha(n+1) + \beta k + \gamma},
$$
where the division is in $\mathbb{Q}$ and division by $0$ gives $0$.

Source: Lars Palapies, *On Extensions of Triangular Arrays to Negative Row Indices
and Their Generating Functions*, INTEGERS 26 (2026), Article A83, Definition 1. -/
public theorem negPos_rec (P : TriangularRecurrence) (p k : ℕ) :
    P.negPos (Int.negSucc (p + 1)) (k + 1) =
      (P.negPos (Int.negSucc p) (k + 1) -
        P.weight' (Int.negSucc (p + 1)) (k + 1) * P.negPos (Int.negSucc (p + 1)) k) /
      P.weight (Int.negSucc (p + 1)) (k + 1) := by
  change P.negPosAux (p + 1) (k + 1) = (P.negPosAux p (k + 1) -
    P.weight' (Int.negSucc (p + 1)) (k + 1) * P.negPosAux (p + 1) k) /
      P.weight (Int.negSucc (p + 1)) (k + 1)
  rw [negPosAux, Int.negSucc_eq]
  push_cast
  ring_nf

/-- **Negative-negative numbers on and below the diagonal (auxiliary).** For integer parameters
$(\alpha, \beta, \gamma; \alpha', \beta', \gamma')$ and $p, q \ge 0$, put $n = -(p + 1)$ and
$k = n - q$. The rational numbers $b_{p,q}$ are defined by recursion on $p$ and then on $q$ through
$b_{p,q} = (c - (\alpha(n+1) + \beta(k+1) + \gamma)\, e) / (\alpha'(n+1) + \beta'(k+1) + \gamma')$,
where $c = b_{p-1,q}$ if $p \ge 1$, $c = 1$ if $p = q = 0$, and $c = 0$ if $p = 0 < q$; and
$e = b_{p,q-1}$ if $q \ge 1$, $e = 0$ if $q = 0$. Division by $0$ gives $0$.

Source: Lars Palapies, *On Extensions of Triangular Arrays to Negative Row Indices
and Their Generating Functions*, INTEGERS 26 (2026), Article A83, Definition 2. -/
public def negNegAux (P : TriangularRecurrence) : ℕ → ℕ → ℚ
  | 0, 0 => 1 / P.weight' (-1) 0
  | 0, q + 1 => (0 - P.weight (-1) (-(q + 1)) * negNegAux P 0 q) / P.weight' (-1) (-(q + 1))
  | p + 1, 0 => negNegAux P p 0 / P.weight' (-(p + 2)) (-(p + 1))
  | p + 1, q + 1 => (negNegAux P p (q + 1) -
      P.weight (-(p + 2)) (-(p + 2) - q) * negNegAux P (p + 1) q) /
      P.weight' (-(p + 2)) (-(p + 2) - q)

/-- **Negative-negative numbers.** For parameters
$(\alpha, \beta, \gamma; \alpha', \beta', \gamma')$ with triangular array $a_{n,k}$ ($n, k \ge 0$),
the negative-negative numbers $a^{NN}_{n,k} \in \mathbb{Q}$, $n, k \in \mathbb{Z}$, are defined
as follows (Definition 2): $a^{NN}_{0,k} = \delta_{k,0}$ for all $k$; $a^{NN}_{n,k} = a_{n,k}$ for
$n > 0$ and $k \ge 0$; $a^{NN}_{n,k} = 0$ for $n > 0 > k$ and for $n < 0$, $k > n$; and, for
$k \le n < 0$,
$a^{NN}_{n,k} = (a^{NN}_{n+1,k+1} - (\alpha(n+1) + \beta(k+1) + \gamma)\, a^{NN}_{n,k+1}) /
(\alpha'(n+1) + \beta'(k+1) + \gamma')$, where division by $0$ gives $0$.

Source: Lars Palapies, *On Extensions of Triangular Arrays to Negative Row Indices
and Their Generating Functions*, INTEGERS 26 (2026), Article A83, Definition 2. -/
public def negNeg (P : TriangularRecurrence) : ℤ → ℤ → ℚ
  | .ofNat 0, k => if k = 0 then 1 else 0
  | .ofNat (n + 1), .ofNat k => P.array (n + 1) k
  | .ofNat (_ + 1), .negSucc _ => 0
  | .negSucc p, k => if k ≤ .negSucc p then P.negNegAux p (Int.negSucc p - k).toNat else 0

/-- **Negative-negative numbers at $(-1, -1)$ and $(-1, 0)$.** For all parameters
$(\alpha, \beta, \gamma; \alpha', \beta', \gamma')$, the negative-negative numbers $a^{NN}$ satisfy
$a^{NN}_{-1,-1} = 1/\gamma'$ (read as $0$ when $\gamma' = 0$) and $a^{NN}_{-1,0} = 0$.

Source: Lars Palapies, *On Extensions of Triangular Arrays to Negative Row Indices
and Their Generating Functions*, INTEGERS 26 (2026), Article A83, Definition 2. -/
public theorem negNeg_neg_one (P : TriangularRecurrence) :
    P.negNeg (-1) (-1) = 1 / P.γ' ∧ P.negNeg (-1) 0 = 0 := by
  refine ⟨?_, ?_⟩
  · change (if (-1 : ℤ) ≤ Int.negSucc 0 then P.negNegAux 0 (Int.negSucc 0 - -1).toNat
      else 0) = _
    simp [Int.negSucc_eq, negNegAux, weight']
  · change (if (0 : ℤ) ≤ Int.negSucc 0 then P.negNegAux 0 (Int.negSucc 0 - 0).toNat
      else 0) = _
    simp [Int.negSucc_eq]

/-- **Recurrence for the negative-negative numbers.** For all parameters
$(\alpha, \beta, \gamma; \alpha', \beta', \gamma')$ and all integers $k < n \le -2$, the
negative-negative numbers $a^{NN}$ satisfy
$a^{NN}_{n,k} = (a^{NN}_{n+1,k+1} - (\alpha(n+1) + \beta(k+1) + \gamma)\, a^{NN}_{n,k+1}) /
(\alpha'(n+1) + \beta'(k+1) + \gamma')$, where division by $0$ gives $0$.

Source: Lars Palapies, *On Extensions of Triangular Arrays to Negative Row Indices
and Their Generating Functions*, INTEGERS 26 (2026), Article A83, Definition 2. -/
public theorem negNeg_rec (P : TriangularRecurrence) (p q : ℕ) :
    P.negNeg (Int.negSucc (p + 1)) (Int.negSucc (p + 1) - (q + 1)) =
      (P.negNeg (Int.negSucc p) (Int.negSucc (p + 1) - q) -
        P.weight (Int.negSucc (p + 1)) (Int.negSucc (p + 1) - q) *
          P.negNeg (Int.negSucc (p + 1)) (Int.negSucc (p + 1) - q)) /
      P.weight' (Int.negSucc (p + 1)) (Int.negSucc (p + 1) - q) := by
  have e1 : Int.negSucc (p + 1) - (Int.negSucc (p + 1) - (q + 1)) = ((q + 1 : ℕ) : ℤ) := by
    push_cast; ring
  have e2 : Int.negSucc p - (Int.negSucc (p + 1) - q) = ((q + 1 : ℕ) : ℤ) := by
    rw [Int.negSucc_eq, Int.negSucc_eq]; push_cast; ring
  have e3 : Int.negSucc (p + 1) - (Int.negSucc (p + 1) - q) = ((q : ℕ) : ℤ) := by ring
  have l1 : Int.negSucc (p + 1) - (q + 1) ≤ Int.negSucc (p + 1) := by omega
  have l2 : Int.negSucc (p + 1) - q ≤ Int.negSucc p := by
    rw [Int.negSucc_eq, Int.negSucc_eq]; push_cast; omega
  have l3 : Int.negSucc (p + 1) - q ≤ Int.negSucc (p + 1) := by omega
  simp only [negNeg, l1, l2, l3, ↓reduceIte, e1, e2, e3, Int.toNat_natCast]
  rw [negNegAux, Int.negSucc_eq]
  push_cast
  ring_nf

/-- **Reflected triangular recurrence.** The reflection of a triangular recurrence with
parameters $(\alpha, \beta, \gamma; \alpha', \beta', \gamma')$ is the triangular recurrence with
parameters $(\alpha' + \beta', -\beta', \gamma'; \alpha + \beta, -\beta, \gamma)$.

If $a_{n,k}$ is the triangular array of the original recurrence, these are the parameters of the
reflected array $\tilde a_{n,k} = a_{n,n-k}$.

Source: Lars Palapies, *On Extensions of Triangular Arrays to Negative Row Indices
and Their Generating Functions*, INTEGERS 26 (2026), Article A83, Proposition 3. -/
public def reflect (P : TriangularRecurrence) : TriangularRecurrence :=
  ⟨P.α' + P.β', -P.β', P.γ', P.α + P.β, -P.β, P.γ⟩

/-- **Reflection of triangular recurrences is an involution.** Reflecting a triangular
recurrence with parameters $(\alpha, \beta, \gamma; \alpha', \beta', \gamma')$ twice gives back the
recurrence with parameters $(\alpha, \beta, \gamma; \alpha', \beta', \gamma')$.

Source: Lars Palapies, *On Extensions of Triangular Arrays to Negative Row Indices
and Their Generating Functions*, INTEGERS 26 (2026), Article A83, proof of
Proposition 3. -/
public theorem reflect_reflect (P : TriangularRecurrence) : P.reflect.reflect = P := by
  cases P
  simp [reflect]

end TriangularRecurrence

/-- **Linear Diophantine equations.** Let $a, b, c, u, v \in \mathbb{Z}$ with $a \ne 0$ or
$b \ne 0$, let $d = \gcd(a, b)$, and suppose $a u + b v = d$ (Bézout). If $d \mid c$, then the
integers $x, y$ with $a x + b y + c = 0$ are exactly those of the form
$x = -(c/d) u + m (b/d)$, $y = -(c/d) v - m (a/d)$ with $m \in \mathbb{Z}$. If $d \nmid c$, then
$a x + b y + c = 0$ has no solution in integers $x, y$.

Source: Lars Palapies, *On Extensions of Triangular Arrays to Negative Row Indices
and Their Generating Functions*, INTEGERS 26 (2026), Article A83, Proposition 1. -/
public theorem_wanted linear_diophantine_solutions (a b c u v : ℤ) (hab : a ≠ 0 ∨ b ≠ 0)
    (huv : a * u + b * v = Int.gcd a b) :
    ((Int.gcd a b : ℤ) ∣ c → ∀ x y : ℤ, a * x + b * y + c = 0 ↔
      ∃ m : ℤ, x = -(c / Int.gcd a b) * u + m * (b / Int.gcd a b) ∧
        y = -(c / Int.gcd a b) * v - m * (a / Int.gcd a b)) ∧
    (¬ (Int.gcd a b : ℤ) ∣ c → ∀ x y : ℤ, a * x + b * y + c ≠ 0)

/-- **Knuth-type duality.** For integers $\alpha, \beta, \gamma$, let $a$ and $b$ be the arrays with
parameters $(\alpha, \beta, \gamma; 0, 0, 1)$ and $(\beta, \alpha, -\gamma; 0, 0, 1)$. Then their
negative-negative numbers satisfy $a^{NN}_{-n,-k} = b^{NN}_{k-1,n-1}$ for all $n, k \in \mathbb{Z}$.

This generalizes the identity $[-n, -k] = \{k, n\}$ between the Stirling numbers $[n, k]$ of the
first kind and $\{n, k\}$ of the second kind.

Source: Lars Palapies, *On Extensions of Triangular Arrays to Negative Row Indices
and Their Generating Functions*, INTEGERS 26 (2026), Article A83, Proposition 2. -/
public theorem_wanted TriangularRecurrence.negNeg_duality (α β γ : ℤ) (n k : ℤ) :
    TriangularRecurrence.negNeg ⟨α, β, γ, 0, 0, 1⟩ (-n) (-k) =
      TriangularRecurrence.negNeg ⟨β, α, -γ, 0, 0, 1⟩ (k - 1) (n - 1)

/-- **NP/NN duality.** Let $a$ be the array of a triangular recurrence with parameters
$(\alpha, \beta, \gamma; \alpha', \beta', \gamma')$, with weights
$w(n, k) = \alpha(n + 1) + \beta k + \gamma$ and $w'(n, k) = \alpha'(n + 1) + \beta' k + \gamma'$,
and let $\tilde a$ be the array of the reflected recurrence, with parameters
$(\alpha' + \beta', -\beta', \gamma'; \alpha + \beta, -\beta, \gamma)$ and weights $\tilde w$,
$\tilde w'$. Then for all integers $n, k$ the negative-positive and negative-negative numbers
satisfy $\tilde a^{NP}_{n,k} = a^{NN}_{n,n-k}$ and $\tilde a^{NN}_{n,n-k} = a^{NP}_{n,k}$.
Moreover, $\tilde w(n, k) \ne 0$ for all integers $n < 0 \le k$ if and only if
$w'(n, k + 1) \ne 0$ for all integers $k \le n < 0$; and $\tilde w'(n, k + 1) \ne 0$ for all
integers $k \le n < 0$ if and only if $w(n, k) \ne 0$ for all integers $n < 0 \le k$.

Thus the divisor condition of Definition 1 for $\tilde a$ is equivalent to that of Definition 2
for $a$, and conversely, so the left-hand sides exist exactly when the right-hand sides do.
With junk value $0$ for a zero divisor, the two identities need no existence hypothesis.

Source: Lars Palapies, *On Extensions of Triangular Arrays to Negative Row Indices
and Their Generating Functions*, INTEGERS 26 (2026), Article A83, Proposition 3. -/
public theorem_wanted TriangularRecurrence.reflect_negPos_eq_negNeg
    (P : TriangularRecurrence) :
    (∀ n k : ℤ, P.reflect.negPos n k = P.negNeg n (n - k)) ∧
    (∀ n k : ℤ, P.reflect.negNeg n (n - k) = P.negPos n k) ∧
    ((∀ n k : ℤ, n < 0 → 0 ≤ k → P.reflect.weight n k ≠ 0) ↔
      ∀ n k : ℤ, k ≤ n → n < 0 → P.weight' n (k + 1) ≠ 0) ∧
    ((∀ n k : ℤ, k ≤ n → n < 0 → P.reflect.weight' n (k + 1) ≠ 0) ↔
      ∀ n k : ℤ, n < 0 → 0 ≤ k → P.weight n k ≠ 0)

/-- **Generating function of the negative-positive numbers for $\beta = \beta' = 0$.** Let
$\alpha, \gamma, \alpha', \gamma'$ be integers and let $a^{NP}$ be the negative-positive numbers
for the parameters $(\alpha, 0, \gamma; \alpha', 0, \gamma')$. For every $n \ge 0$, in the ring
$\mathbb{Q}[[u]]$ of formal power series,
$$
\sum_{k \ge 0} a^{NP}_{-n,k} u^k =
\Bigl(\prod_{j=0}^{n-1} \bigl((\gamma - j\alpha) + (\gamma' - j\alpha') u\bigr)\Bigr)^{-1},
$$
where the inverse of a power series with constant term $0$ is taken to be $0$.

Coefficientwise in $x^n/n!$ this is Theorem 1, which says that the exponential generating
function $\bar F(u, x) = \sum_{n,k \ge 0} a^{NP}_{-n,k} u^k x^n/n!$ equals the hypergeometric
series ${}_0F_1(-; b; -x/(\alpha + \alpha' u))$
with $b = -(\gamma + \gamma' u)/(\alpha + \alpha' u)$, and $e^{x/(\gamma + \gamma' u)}$ when
$\alpha = \alpha' = 0$: the rising factorial $b^{\overline{n}} = b(b+1)\cdots(b+n-1)$ satisfies
$b^{\overline{n}} (-(\alpha + \alpha' u))^n =
\prod_{j<n} (\gamma + \gamma' u - j(\alpha + \alpha' u))$. The paper's existence hypothesis
($\gamma - j\alpha \ne 0$ for all $j$) is not needed: a zero divisor makes both sides $0$ from
that row on.

Source: Lars Palapies, *On Extensions of Triangular Arrays to Negative Row Indices
and Their Generating Functions*, INTEGERS 26 (2026), Article A83, Theorem 1. -/
public theorem_wanted TriangularRecurrence.negPos_egf_beta_zero (α γ α' γ' : ℤ) (n : ℕ) :
    (PowerSeries.mk fun k : ℕ => TriangularRecurrence.negPos ⟨α, 0, γ, α', 0, γ'⟩ (-n) k) =
      (∏ j ∈ Finset.range n,
        (PowerSeries.C ((γ : ℚ) - j * α) + PowerSeries.C ((γ' : ℚ) - j * α') * PowerSeries.X))⁻¹

end

end MetaMathlibExt
