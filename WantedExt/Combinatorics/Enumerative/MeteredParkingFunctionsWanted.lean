/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.Combinatorics.Enumerative.ClassicalMeteredParkingFunctions
public import MathlibExt.Combinatorics.Enumerative.LongMeteredParkingFunctions
public import MathlibExt.Combinatorics.Enumerative.MeteredParkingLowerBound
public import MathlibExt.Combinatorics.Enumerative.OneMeteredParkingFunctions
public import MathlibExt.Combinatorics.Enumerative.OneMeteredTwoSpots
public import MathlibExt.Combinatorics.Enumerative.ParkingFunction
public import MathlibExt.Combinatorics.Enumerative.TwoMeteredParkingFunctions

namespace MetaMathlibExt

@[expose] public section

/-!
Conventions for the statements below. Spots and preferences are zero-based: preference
`f i : Fin n` and spot `s` are the source's `f i + 1` and `s + 1`, and car `i : Fin m` is the
source's car `i + 1`. Classical `(m, n)`-parking functions are MathlibExt's
`IsPartialParkingFunction m n` (and `IsParkingFunction n` for `m = n`).
-/

/-- **Window condition for metered parking functions.** Number the cars $1, \dots, m$ and the
spots $1, \dots, n$, and let $a_k$ be the preferred spot of car $k$. If $(a_1, \dots, a_m)$ is a
$t$-metered $(m, n)$-parking function, then for every $i$ with $1 \le i \le n$ and every $j$ with
$1 \le j \le m - t$ (truncated subtraction, so there is no such $j$ when $m \le t$),
$$t + 1 + i \le \#\{k : j \le k \le j + t,\ a_k \le i\} + n,$$
that is, at least $t + 1 - n + i$ of the cars $j, \dots, j + t$ prefer one of the spots
$1, \dots, i$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Proposition 1 (`integers-2025-A73-prop-1`). -/
public theorem_wanted metered_window_count_ge {m n t : ℕ} {f : Fin m → Fin n}
    (hf : IsMeteredParkingFunction t f) (i j : ℕ) (hi : i ∈ Finset.Icc 1 n)
    (hj : j ∈ Finset.Icc 1 (m - t)) :
    t + 1 + i ≤
      (Finset.univ.filter fun k : Fin m =>
          j ≤ (k : ℕ) + 1 ∧ (k : ℕ) + 1 ≤ j + t ∧ (f k : ℕ) + 1 ≤ i).card + n

/-- **Lucky cars of 1-metered parking are the lace starts.** Let $0 < m \le n$ and let
$\alpha = (a_1, \dots, a_m)$, with each $a_i \in \{1, \dots, n\}$, be any sequence of preferred
spots of $m$ cars on $n$ spots. Under the $1$-metered parking scheme, car $i$ is lucky (it parks
in its preferred spot $a_i$) if and only if position $i$ is the first position of one of the
laces of the lace decomposition $\mathrm{lace}(\alpha)$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Lemma 1 (`integers-2025-A73-lem-1`). -/
public theorem_wanted one_metered_lucky_iff_lace_start {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (f : Fin m → Fin n) :
    ((List.ofFn fun i => (f i : ℕ)).zip (meteredOutcome 1 n (List.ofFn fun i => (f i : ℕ)))).map
        (fun p => decide (p.2 = some p.1)) =
      (laceDecomposition (List.ofFn fun i => (f i : ℕ))).flatMap
        fun c => true :: List.replicate (c.length - 1) false

/-- **One-metered parking functions and laces.** Let $0 < m \le n$ and
$f : \{0, \dots, m-1\} \to \{0, \dots, n-1\}$. Then $f$ is a $1$-metered parking function if and
only if, in the lace decomposition of $(f(0), \dots, f(m-1))$, the last spot $n - 1$ occurs in
no lace other than as its first entry.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Theorem 1 (`integers-2025-A73-thm-1`). -/
public theorem_wanted isMeteredParkingFunction_one_iff_lace {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (f : Fin m → Fin n) :
    IsMeteredParkingFunction 1 f ↔
      ∀ c ∈ laceDecomposition (List.ofFn fun i => (f i : ℕ)), n - 1 ∉ c.tail

/-- **Equal last-spot counts for 1-metered parking functions.** Let $1 \le m \le j < k \le n$
and number the spots $1, \dots, n$. The number of $1$-metered $(m, n)$-parking functions whose
last car parks in spot $j$ equals the number of those whose last car parks in spot $k$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Lemma 2 (`integers-2025-A73-lem-2`). -/
public theorem_wanted one_metered_last_spot_card_eq {m n j k : ℕ} (hm : 1 ≤ m) (hmj : m ≤ j)
    (hjk : j < k) (hkn : k ≤ n) :
    (Finset.univ.filter fun f : Fin m → Fin n => IsMeteredParkingFunction 1 f ∧
        (meteredOutcome 1 n (List.ofFn fun i => (f i : ℕ))).getLast? = some (some (j - 1))).card =
      (Finset.univ.filter fun f : Fin m → Fin n => IsMeteredParkingFunction 1 f ∧
        (meteredOutcome 1 n (List.ofFn fun i => (f i : ℕ))).getLast? = some (some (k - 1))).card

/-- **1-metered parking functions whose last car parks in the last spot.** Let $1 \le m \le n$
and number the spots $1, \dots, n$. The number of $1$-metered $(m, n)$-parking functions whose
last car parks in spot $n$ equals $\mathrm{mpf}_{m-1,n}(1)$, the number of $1$-metered
$(m - 1, n)$-parking functions.

The source leaves $1 \le m$ implicit (there is a last car).

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Lemma 3 (`integers-2025-A73-lem-3`). -/
public theorem_wanted one_metered_last_spot_n_card {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    (Finset.univ.filter fun f : Fin m → Fin n => IsMeteredParkingFunction 1 f ∧
        (meteredOutcome 1 n (List.ofFn fun i => (f i : ℕ))).getLast? = some (some (n - 1))).card =
      meteredParkingCount 1 (m - 1) n

/-- **1-metered parking functions with as many cars as spots.** For every natural number
$n > 2$, the number of $1$-metered $(n, n)$-parking functions is
$$\mathrm{mpf}_{n,n}(1) = \sum_{k=0}^{n} (n-2)^{n-k} \binom{2n+1-k}{k}.$$

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Corollary 4 (`integers-2025-A73-cor-4`). -/
public theorem_wanted meteredParkingCount_one_diag {n : ℕ} (hn : 2 < n) :
    meteredParkingCount 1 n n =
      ∑ k ∈ Finset.range (n + 1), (n - 2) ^ (n - k) * (2 * n + 1 - k).choose k

/-- **Metered parking functions in which every car is lucky.** Let $m \ge 2$, $n \ge 2$ and
$t \le m - 1$. The number of $t$-metered $(m, n)$-parking functions in which every car parks in
its preferred spot is $n(n-1)\cdots(n-t+1) \cdot (n-t)^{m-t}$, where the falling factorial
$n(n-1)\cdots(n-t+1)$ has $t$ factors (it equals $1$ for $t = 0$ and $0$ for $t > n$).

The source's companion formula (12) for exactly one lucky car is not stated: it is false as
printed when $m > n + 1$ (for $n = 2$, $m = 4$, $t = 1$ the count is $0$, while the formula
$(t-1)!\,(n-m+1)\,t^{m-t}$ gives $-1$).

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Proposition 8, Equation (13)
(`integers-2025-A73-prop-8`). -/
public theorem_wanted metered_all_lucky_card {m n t : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (ht : t ≤ m - 1) :
    (Finset.univ.filter fun f : Fin m → Fin n =>
        IsMeteredParkingFunction t f ∧ meteredLuckyCount t f = m).card =
      n.descFactorial t * (n - t) ^ (m - t)

/-- **Closed form for (m-2)-metered parking functions.** Let $m, n$ be natural numbers with
$2 < m \le n + 1$. Then the number $\mathrm{mpf}_{m,n}(m-2)$ of $(m-2)$-metered
$(m, n)$-parking functions is
$$(n-m+2)^2 (m-1)^{m-3} + \sum_{k=n-m+3}^{n} \binom{m-2}{n-k} (n-k+1)^{n-k-1} S_k,$$
where
$$S_k = \binom{k+1}{2}(n-m+2)\, k^{m-n+k-3} +
\left(k(n-m+1) - \binom{n-m+2}{2}\right)(k-n+m-1)^{k-n+m-3} +
\sum_{j=n-m+2}^{k-1} \left(jk - \binom{j+1}{2}\right) \binom{m-2-n+k}{k-1-j} (n-m+1)\,
j^{j+m-2-n} (k-j)^{k-j-2}.$$
Every subtraction is nonnegative on the summation ranges except in the exponents of the bases
$n - k + 1$ (at $k = n$) and $k - j$ (at $j = k - 1$), which equal $1$ there, so the formula is
the same with exponents truncated at $0$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Theorem 5 (`integers-2025-A73-thm-5`). -/
public theorem_wanted meteredParkingCount_sub_two {m n : ℕ} (hm : 2 < m) (hmn : m ≤ n + 1) :
    meteredParkingCount (m - 2) m n =
      (n + 2 - m) ^ 2 * (m - 1) ^ (m - 3) +
        ∑ k ∈ Finset.Icc (n + 3 - m) n,
          (m - 2).choose (n - k) * (n - k + 1) ^ (n - k - 1) *
            ((k + 1).choose 2 * (n + 2 - m) * k ^ (m + k - n - 3) +
              (k * (n + 1 - m) - (n + 2 - m).choose 2) * (k + m - n - 1) ^ (k + m - n - 3) +
              ∑ j ∈ Finset.Ico (n + 2 - m) k,
                (j * k - (j + 1).choose 2) * (m + k - 2 - n).choose (k - 1 - j) * (n + 1 - m) *
                  j ^ (j + m - 2 - n) * (k - j) ^ (k - j - 2))

/-- **Parking functions with a given first entry.** Let $1 \le m \le n$ and $1 \le j \le n$, and
number the spots $1, \dots, n$. Write
$$S(i) = \binom{m-1}{n-i} (n-m+1)\, i^{i+m-n-2} (n-i+1)^{n-i-1}.$$
If $j > n - m + 1$, the number of partial parking functions with $m$ cars and $n$ spots
(classical $(m, n)$-parking functions) whose first entry is $a_1 = j$ is $\sum_{i=j}^{n} S(i)$;
if $j \le n - m + 1$, it is $m^{m-2} + \sum_{i=n-m+2}^{n} S(i)$. Exponents are natural numbers
with truncated subtraction; the only affected powers are $1^{-1}$, at $i = n$ and at $m = 1$,
which equal the truncated $1^0$.

The text prints the factor $n - m + 1$ as $n - m - 1$, which is false ($m = n = 2$, $j = 1$: two
parking functions, formula $0$); the factor $n - m + 1$ is the one in the source's Lemma 4
($|\mathrm{Sh}_m(k-1, n-k)|$), from which the source derives this corollary, and it matches
exact counts.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Corollary 6 (`integers-2025-A73-cor-6`). -/
public theorem_wanted parkingFunction_first_entry_card {m n j : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (hj : j ∈ Finset.Icc 1 n) :
    (Finset.univ.filter fun f : Fin m → Fin n =>
        IsPartialParkingFunction m n f ∧ (f ⟨0, hm⟩ : ℕ) + 1 = j).card =
      if n - m + 1 < j then
        ∑ i ∈ Finset.Icc j n, (m - 1).choose (n - i) * (n - m + 1) * i ^ (i + m - n - 2) *
          (n - i + 1) ^ (n - i - 1)
      else
        m ^ (m - 2) + ∑ i ∈ Finset.Icc (n - m + 2) n, (m - 1).choose (n - i) * (n - m + 1) *
          i ^ (i + m - n - 2) * (n - i + 1) ^ (n - i - 1)

/-- **Metered parking functions with one spot fewer than cars.** Let $m \ge 2$ be a natural
number. The number $\mathrm{mpf}_{m,m-1}(m-2)$ of $(m-2)$-metered $(m, m-1)$-parking functions
equals the sum, over all parking functions $f$ of length $m - 1$, of $f(0) + 1$ (the preferred
spot of the first car, with spots numbered from $1$), and it also equals
$$\sum_{i=1}^{m-1} \sum_{s=0}^{m-1-i} \binom{m-2}{s}\, i\, (s+1)^{s-1} (m-s-1)^{m-s-3}.$$
The only negative exponents occur at $s = 0$ and $s = m - 2$, where the base is $1$, so the
formula is the same with exponents truncated at $0$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Corollary 7 (`integers-2025-A73-cor-7`). -/
public theorem_wanted meteredParkingCount_sub_two_pred (k : ℕ) :
    meteredParkingCount k (k + 2) (k + 1) =
        ∑ f ∈ Finset.univ.filter (fun f : Fin (k + 1) → Fin (k + 1) => IsParkingFunction (k + 1) f),
          ((f 0 : ℕ) + 1) ∧
      meteredParkingCount k (k + 2) (k + 1) =
        ∑ i ∈ Finset.Icc 1 (k + 1), ∑ s ∈ Finset.range (k + 2 - i),
          k.choose s * i * (s + 1) ^ (s - 1) * (k + 1 - s) ^ (k - 1 - s)

/-- **Parking-function shuffles and the first entry.** Let $1 \le m \le n$ and $1 \le k \le n$,
and let $w = (w_1, \dots, w_{m-1})$ be a word with entries in $\{0, \dots, n-1\}$. Then the set
of spots $j \in \{0, \dots, n-1\}$ for which $(j, w_1, \dots, w_{m-1})$ is a partial parking
function with $m$ cars and $n$ spots equals $\{0, \dots, k-1\}$ if and only if $w$ lies in the
set $\mathrm{Sh}_m(k - 1, n - k)$ of $(m, n)$-parking-function shuffles with parameter $k$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Theorem 3 (`integers-2025-A73-thm-3`), with
Definition 6 (the sets `A^n`). -/
public theorem_wanted firstEntrySet_eq_iff_isParkingShuffle {m' n k : ℕ} (hmn : m' + 1 ≤ n)
    (hk : k ∈ Finset.Icc 1 n) (π : Fin m' → Fin n) :
    (Finset.univ.filter fun j : Fin n => IsPartialParkingFunction (m' + 1) n (Fin.cons j π)) =
        Finset.univ.filter (fun j : Fin n => (j : ℕ) < k) ↔
      IsParkingShuffle m' n k π

/-- **Number of parking-function shuffles.** Let $1 \le m \le n$ and $1 \le k \le n$, and write
$\mathrm{Sh}_m(k - 1, n - k)$ for the set of $(m, n)$-parking-function shuffles with parameter
$k$, words of length $m - 1$ with entries in $\{0, \dots, n-1\}$. Then
$|\mathrm{Sh}_m(k - 1, n - k)|$ equals $\binom{m-1}{n-k}(n-m+1)\,k^{m-n+k-2}(n-k+1)^{n-k-1}$
if $k > n - m + 1$, equals $m^{m-2}$ if $k = n - m + 1$, and equals $0$ if $k < n - m + 1$.
The exponent $-1$ occurs only on the base $1$ (at $k = n$, and at $m = 1$), and $1^{-1} = 1$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Lemma 4 (`integers-2025-A73-lem-4`). -/
public theorem_wanted isParkingShuffle_card {m' n k : ℕ} (hmn : m' + 1 ≤ n)
    (hk : k ∈ Finset.Icc 1 n) :
    (Finset.univ.filter fun π : Fin m' → Fin n => IsParkingShuffle m' n k π).card =
      if n - (m' + 1) + 1 < k then
        m'.choose (n - k) * (n - (m' + 1) + 1) * k ^ (m' + 1 + k - n - 2) *
          (n - k + 1) ^ (n - k - 1)
      else if k = n - (m' + 1) + 1 then (m' + 1) ^ (m' + 1 - 2)
      else 0

/-- **Characterization of $(m-2)$-metered parking functions.** Let $2 < m \le n + 1$,
$f : \{0, \dots, m-1\} \to \{0, \dots, n-1\}$, $1 \le k \le n$ and $j \in \mathbb{N}$. Write
$\mathrm{Sh}_p(q - 1, N - q)$ for the set of $(p, N)$-parking-function shuffles with parameter
$q$, words of length $p - 1$ with entries in $\{0, \dots, N-1\}$. Suppose that the middle word
$w = (f(1), \dots, f(m-2))$ lies in $\mathrm{Sh}_{m-1}(k - 1, n - k)$, and that either
$m = n + 1$ and $j = 0$, or $m \le n$, $1 \le j \le k - 1$ and the subsequence $\sigma$ of the
entries of $w$ that are less than $k - 1$, a word of length $m + k - n - 2$ with entries in
$\{0, \dots, k-2\}$, lies in $\mathrm{Sh}_{m+k-n-1}(j - 1, k - 1 - j)$. Then $f$ is an
$(m-2)$-metered parking function if and only if either $f(0) < j$ and $f(m-1) < k$, or
$j \le f(0) < k$ and $f(m-1) \le f(0)$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Theorem 4 (`integers-2025-A73-thm-4`). -/
public theorem_wanted isMeteredParkingFunction_sub_two_iff {m n k j : ℕ} (hm : 2 < m)
    (hmn : m ≤ n + 1) (f : Fin m → Fin n) (hk : k ∈ Finset.Icc 1 n)
    (hsh : IsParkingShuffle (m - 2) n k fun i => f ⟨(i : ℕ) + 1, by have := i.2; omega⟩)
    (hj : (m = n + 1 ∧ j = 0) ∨
      (m ≤ n ∧ j ∈ Finset.Icc 1 (k - 1) ∧
        ∃ σ : Fin (m + k - n - 2) → Fin (k - 1),
          List.ofFn (fun i => (σ i : ℕ)) =
              (List.ofFn fun i : Fin (m - 2) =>
                (f ⟨(i : ℕ) + 1, by have := i.2; omega⟩ : ℕ)).filter (fun x => x + 1 < k) ∧
            IsParkingShuffle (m + k - n - 2) (k - 1) j σ)) :
    IsMeteredParkingFunction (m - 2) f ↔
      ((f ⟨0, by omega⟩ : ℕ) + 1 ≤ j ∧ (f ⟨m - 1, by omega⟩ : ℕ) + 1 ≤ k) ∨
        (j < (f ⟨0, by omega⟩ : ℕ) + 1 ∧ (f ⟨0, by omega⟩ : ℕ) + 1 ≤ k ∧
          (f ⟨m - 1, by omega⟩ : ℕ) ≤ f ⟨0, by omega⟩)

/-- **Metered parking functions with meter $n - 1$ and more cars than spots.** Let $k > 0$ and
$f : \{0, \dots, n+k-1\} \to \{0, \dots, n-1\}$, and let $\pi_0, \dots, \pi_{n-1}$ be the
$(n-1)$-metered outcome of the first $n$ preferences $(f(0), \dots, f(n-1))$ on $n$ spots, where
$\pi_c$ is the spot in which car $c$ parks, if it parks. Then $f$ is an $(n-1)$-metered parking
function if and only if $(f(0), \dots, f(n-1))$ is a parking function and, for every
$i \in \{0, \dots, k-1\}$, car $i \bmod n$ parks in this outcome and $f(n + i) \le \pi_{i \bmod n}$.

The outcome is read periodically: the later preferences $f(n), f(n+1), \dots$ are compared with
$\pi_0, \dots, \pi_{n-1}, \pi_0, \dots$ in turn.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Theorem 6 (`integers-2025-A73-thm-6`). -/
public theorem_wanted isMeteredParkingFunction_pred_iff {n k : ℕ} (hk : 0 < k)
    (f : Fin (n + k) → Fin n) :
    IsMeteredParkingFunction (n - 1) f ↔
      IsParkingFunction n (fun i => f (Fin.castAdd k i)) ∧
        ∀ i : Fin k, ∃ s, (meteredOutcome (n - 1) n
            (List.ofFn fun i : Fin n => (f (Fin.castAdd k i) : ℕ)))[(i : ℕ) % n]? = some (some s) ∧
          (f (Fin.natAdd n i) : ℕ) ≤ s

end

end MetaMathlibExt
