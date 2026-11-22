/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.Combinatorics.Enumerative.ParkingFunction

namespace MetaMathlibExt

@[expose] public section

/-!
Conventions for the statements below. Spots and preferences are zero-based: preference
`f i : Fin n` and spot `s` are the source's `f i + 1` and `s + 1`, and car `i : Fin m` is the
source's car `i + 1`. Classical `(m, n)`-parking functions are MathlibExt's
`IsPartialParkingFunction m n` (and `IsParkingFunction n` for `m = n`).
-/

/-- **Outcome of the metered parking scheme.** Let $t, n \in \mathbb{N}$, number the $n$ spots
$0, \dots, n-1$, and let $a_0, a_1, \dots, a_{m-1}$ be a list of preferences in $\mathbb{N}$.
Cars arrive in order, and car $i$ parks in the least spot $s$ with $a_i \le s < n$ that is not
taken by one of the previous $t$ cars (cars $\max(0, i - t), \dots, i - 1$) that parked; if
there is no such spot, car $i$ fails. The outcome is the list whose $i$-th entry is the spot of
car $i$, or a failure marker if car $i$ fails. Thus after car $j$ arrives, car $j - t$ leaves,
and only the cars among the last $t$ entries of the outcome so far occupy spots.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 1 (definition of the `t`-metered scheme) and
Section 2
(definition of the outcome). -/
public def meteredOutcome (t n : ℕ) (prefs : List ℕ) : List (Option ℕ) :=
  prefs.foldl
    (fun out a => out ++ [(List.range' a (n - a)).find?
      (fun s => decide (s ∉ (out.drop (out.length - t)).filterMap id))])
    []

/-- **A 1-metered example in which every car parks.** In the $1$-metered parking scheme on two
spots $\{0, 1\}$, if three cars arrive all preferring spot $0$, then they park in spots $0$, $1$
and $0$, in that order.

In the source's one-based numbering: preferences $(1, 1, 1)$ give spots $1, 2, 1$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, example after the definition of `t`-metered parking
functions (Section 1). -/
public theorem meteredOutcome_one_two_ones :
    meteredOutcome 1 2 [0, 0, 0] = [some 0, some 1, some 0] := by decide

/-- **A 1-metered example in which the third car fails.** In the $1$-metered parking scheme on
two spots $\{0, 1\}$, if three cars arrive with preferences $0$, $0$, $1$, then the first two
cars park in spots $0$ and $1$ and the third car fails to park.

In the source's one-based numbering: with preferences $(1, 1, 2)$, car $3$ fails.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, example after the definition of `t`-metered parking
functions (Section 1). -/
public theorem meteredOutcome_one_two_fail :
    meteredOutcome 1 2 [0, 0, 1] = [some 0, some 1, none] := by decide

/-- **Metered outcomes of a seven-car example on six spots.** On the six spots
$\{0, \dots, 5\}$, for seven cars with preferences $(2, 2, 2, 2, 3, 4, 5)$, the $2$-metered
parking scheme parks the cars in spots $(2, 3, 4, 2, 3, 4, 5)$, while in the $1$-metered scheme
the first six cars park in spots $(2, 3, 2, 3, 4, 5)$ and the seventh car fails to park.

In the source's one-based notation, where $O^t_n$ is the outcome of the $t$-metered scheme on
$n$ spots and $X$ marks a car that fails to park, $O^2_6(3,3,3,3,4,5,6) = (3,4,5,3,4,5,6)$ and
$O^1_6(3,3,3,3,4,5,6) = (3,4,3,4,5,6,X)$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, example after the definition of the outcome
(Section 2). -/
public theorem meteredOutcome_example_six :
    meteredOutcome 2 6 [2, 2, 2, 2, 3, 4, 5] =
        [some 2, some 3, some 4, some 2, some 3, some 4, some 5] ∧
      meteredOutcome 1 6 [2, 2, 2, 2, 3, 4, 5] =
        [some 2, some 3, some 2, some 3, some 4, some 5, none] := by decide

/-- **Metered parking function.** Let $m, n, t \in \mathbb{N}$, number the $n$ spots
$0, \dots, n-1$, and let $f : \{0, \dots, m-1\} \to \{0, \dots, n-1\}$ give the preferred spot of
each of $m$ cars. In the $t$-metered scheme the cars arrive in the order $0, 1, \dots, m-1$, and
car $i$ parks in the least spot $s$ with $f(i) \le s \le n - 1$ that is not occupied by any of the
(at most $t$) cars that arrived just before car $i$; it fails to park if there is no such spot.
Then $f$ is a $t$-metered parking function if every car parks.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 1 (definition of `t`-metered parking
functions). -/
public def IsMeteredParkingFunction {m n : ℕ} (t : ℕ) (f : Fin m → Fin n) : Prop :=
  ∀ o ∈ meteredOutcome t n (List.ofFn fun i => (f i : ℕ)), o ≠ none

/-- Decidability of `IsMeteredParkingFunction` (a finite check of the outcome list).

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 1 (definition of `t`-metered parking
functions). -/
public instance {m n : ℕ} (t : ℕ) (f : Fin m → Fin n) :
    Decidable (IsMeteredParkingFunction t f) := by
  unfold IsMeteredParkingFunction
  infer_instance

/-- **Number of metered parking functions.** For natural numbers $t$, $m$ and $n$,
$\mathrm{mpf}_{m,n}(t)$ is the number of $t$-metered $(m, n)$-parking functions, that is, of maps
$f$ from the $m$ cars $\{0, \dots, m-1\}$ to the $n$ spots $\{0, \dots, n-1\}$ under which every
car parks in the $t$-metered parking scheme.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 1 (definition and the notation
`mpf_{m,n}(t)`). -/
public def meteredParkingCount (t m n : ℕ) : ℕ :=
  (Finset.univ.filter fun f : Fin m → Fin n => IsMeteredParkingFunction t f).card

/-- **1-metered parking functions with two cars and two spots.** The number of $1$-metered
$(2, 2)$-parking functions is $\mathrm{mpf}_{2,2}(1) = 3$.

This is an entry of the source's Table 1.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Table 1. -/
public theorem meteredParkingCount_one_two_two : meteredParkingCount 1 2 2 = 3 := by decide

/-- **Lucky cars in the metered scheme.** For natural numbers $t$, $m$, $n$ and a preference
function $f : \{0, \dots, m - 1\} \to \{0, \dots, n - 1\}$ (car $i$ prefers spot $f(i)$), the
lucky count of $f$ under the $t$-metered parking scheme on $n$ spots is the number of cars $i$
that park in their preferred spot $f(i)$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 2 (`lucky(α)`). -/
public def meteredLuckyCount {m n : ℕ} (t : ℕ) (f : Fin m → Fin n) : ℕ :=
  ((List.ofFn fun i => (f i : ℕ)).zip (meteredOutcome t n (List.ofFn fun i => (f i : ℕ)))).countP
    fun p => decide (p.2 = some p.1)

/-- **One step of the lace decomposition.** Given a list of blocks (each a list of natural
numbers) and a natural number $a$: if the last block is $(p)$ with $a = p$, or the last block has
at least two entries and ends with $e$ where $a = e + 1$, then $a$ is appended to the last block;
otherwise, including when there is no block, a new block $(a)$ is added at the end.

Applied to a list of laces, where a lace is $(p)$ or $(p, p, p+1, \dots, p+\ell-2)$ for some
natural number $p$ and some length $\ell \ge 2$, this extends the last lace exactly when the
result is again a lace.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 3 (definitions of a lace and of the lace
decomposition). -/
public def laceStep (acc : List (List ℕ)) (a : ℕ) : List (List ℕ) :=
  match acc.getLast? with
  | some [p] => if a = p then acc.dropLast ++ [[p, a]] else acc ++ [[a]]
  | some l@(_ :: _ :: _) =>
      if a = l.getLastD 0 + 1 then acc.dropLast ++ [l ++ [a]] else acc ++ [[a]]
  | _ => acc ++ [[a]]

/-- **Lace decomposition.** A lace is a sequence of natural numbers of the form $(p)$ or
$(p, p, p+1, \dots, p+\ell-2)$ for some natural number $p$ and some length $\ell \ge 2$. The lace
decomposition of a finite sequence $(a_1, \dots, a_k)$ of natural numbers is its partition into
blocks of consecutive entries built greedily from left to right: starting with no blocks, each
entry $a_i$ in turn is appended to the last block if the result is again a lace, and otherwise
starts a new block $(a_i)$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 3 (definitions of a lace and of the lace
decomposition). -/
public def laceDecomposition (l : List ℕ) : List (List ℕ) :=
  l.foldl laceStep []

/-- **Examples of lace decompositions.** The lace decomposition of $(3, 3, 3, 3, 4, 6)$ is
$((3, 3), (3, 3, 4), (6))$, and the lace decomposition of $(4, 1, 2, 2, 3, 4, 5, 5, 1, 2)$ is
$((4), (1), (2, 2, 3, 4, 5), (5), (1), (2))$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 3, example after the definition of the lace
decomposition. -/
public theorem laceDecomposition_examples :
    laceDecomposition [3, 3, 3, 3, 4, 6] = [[3, 3], [3, 3, 4], [6]] ∧
      laceDecomposition [4, 1, 2, 2, 3, 4, 5, 5, 1, 2] =
        [[4], [1], [2, 2, 3, 4, 5], [5], [1], [2]] := by decide

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

/-- **Vanishing of metered parking counts.** Let $m, n, t$ be natural numbers with $m > n$ and
$t \ge n$. Then there are no $t$-metered $(m, n)$-parking functions, that is,
$\mathrm{mpf}_{m,n}(t) = 0$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Proposition 2 (`integers-2025-A73-prop-2`). -/
public theorem_wanted meteredParkingCount_eq_zero {m n t : ℕ} (hmn : n < m) (htn : n ≤ t) :
    meteredParkingCount t m n = 0

/-- **Metered parking functions with a long meter are classical.** Let $m \le n$ and
$t \ge m - 1$. A map $f : \{0, \dots, m-1\} \to \{0, \dots, n-1\}$ is a $t$-metered parking
function if and only if it is a partial parking function with $m$ cars and $n$ spots.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Proposition 3 (`integers-2025-A73-prop-3`). -/
public theorem_wanted isMeteredParkingFunction_iff_of_le {m n t : ℕ} (ht : m - 1 ≤ t)
    (hmn : m ≤ n) (f : Fin m → Fin n) :
    IsMeteredParkingFunction t f ↔ IsPartialParkingFunction m n f

/-- **Classical parking functions are metered parking functions.** Let $m \le n$. Every partial
parking function $f$ with $m$ cars and $n$ spots is a $t$-metered parking function for every
$t \in \mathbb{N}$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Proposition 4 (`integers-2025-A73-prop-4`). -/
public theorem_wanted IsPartialParkingFunction.isMeteredParkingFunction {m n : ℕ} (hmn : m ≤ n)
    {f : Fin m → Fin n} (hf : IsPartialParkingFunction m n f) (t : ℕ) :
    IsMeteredParkingFunction t f

/-- **Displacement bound in the metered scheme.** Let $t$, $m$, $n$ be natural numbers, let
$f : \{0, \dots, m - 1\} \to \{0, \dots, n - 1\}$ be a preference function and let $i < m$ be a
car. Under the $t$-metered parking scheme on $n$ spots, if car $i$ parks in spot $s$ then
$s \le f(i) + t$, that is, its displacement is at most $t$; and if car $i$ fails to park then
$f(i) + t \ge n$.

In the source's one-based numbering, with preference $a_i = f(i) + 1$, a car that fails to park
has $a_i \ge n - t + 1$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Proposition 5 (`integers-2025-A73-prop-5`). -/
public theorem_wanted meteredOutcome_displacement_le {m n t : ℕ} (f : Fin m → Fin n) (i : Fin m) :
    (∀ s, (meteredOutcome t n (List.ofFn fun i => (f i : ℕ)))[(i : ℕ)]? = some (some s) →
        s ≤ (f i : ℕ) + t) ∧
      ((meteredOutcome t n (List.ofFn fun i => (f i : ℕ)))[(i : ℕ)]? = some none →
        n ≤ (f i : ℕ) + t)

/-- **Lower bound for the number of metered parking functions.** For all natural numbers $t$,
$m$ and $n$, $\mathrm{mpf}_{m,n}(t) \ge (n - t)^m$, where $n - t$ is truncated subtraction
(equal to $0$ when $t \ge n$).

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Corollary 1 (`integers-2025-A73-cor-1`). -/
public theorem_wanted pow_sub_le_meteredParkingCount (t m n : ℕ) :
    (n - t) ^ m ≤ meteredParkingCount t m n

/-- **Metered parking functions with two cars.** For every natural number $t \ge 1$ and every
natural number $n$, the number of $t$-metered $(2, n)$-parking functions is
$\mathrm{mpf}_{2,n}(t) = \max(n^2 - 1, 0)$, that is, $n^2 - 1$ for $n \ge 1$ and $0$ for $n = 0$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Corollary 2 (`integers-2025-A73-cor-2`). -/
public theorem_wanted meteredParkingCount_two {t : ℕ} (ht : 1 ≤ t) (n : ℕ) :
    meteredParkingCount t 2 n = n ^ 2 - 1

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

/-- **One-metered parking functions with two spots.** Let $m \ge 1$ and
$f : \{0, \dots, m-1\} \to \{0, 1\}$. Then $f$ is a $1$-metered parking function with $m$ cars and
$2$ spots if and only if every lace of the lace decomposition of $(f(0), \dots, f(m-1))$ that
contains the value $1$ has length $1$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Corollary 3 (`integers-2025-A73-cor-3`). -/
public theorem_wanted isMeteredParkingFunction_one_two_iff_lace {m : ℕ} (hm : 1 ≤ m)
    (f : Fin m → Fin 2) :
    IsMeteredParkingFunction 1 f ↔
      ∀ c ∈ laceDecomposition (List.ofFn fun i => (f i : ℕ)), 1 ∈ c → c.length = 1

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

/-- **Lucas-type recursion for 1-metered parking functions.** Write $\mathrm{mpf}_{m,n}(1)$ for
the number of $1$-metered $(m, n)$-parking functions. For every natural number $n$,
$\mathrm{mpf}_{1,n}(1) = n$ and $\mathrm{mpf}_{0,n}(1) = 1$, and for every natural number $m$
with $1 \le m \le n$,
$$\mathrm{mpf}_{m+1,n}(1) = n \cdot \mathrm{mpf}_{m,n}(1) - \mathrm{mpf}_{m-1,n}(1),$$
where the subtraction is taken in the integers.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Theorem 2 (`integers-2025-A73-thm-2`). -/
public theorem_wanted meteredParkingCount_one_recursion (n : ℕ) :
    meteredParkingCount 1 1 n = n ∧ meteredParkingCount 1 0 n = 1 ∧
      ∀ m, 1 ≤ m → m ≤ n →
        (meteredParkingCount 1 (m + 1) n : ℤ) =
          n * meteredParkingCount 1 m n - meteredParkingCount 1 (m - 1) n

/-- **1-metered parking functions with as many cars as spots.** For every natural number
$n > 2$, the number of $1$-metered $(n, n)$-parking functions is
$$\mathrm{mpf}_{n,n}(1) = \sum_{k=0}^{n} (n-2)^{n-k} \binom{2n+1-k}{k}.$$

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Corollary 4 (`integers-2025-A73-cor-4`). -/
public theorem_wanted meteredParkingCount_one_diag {n : ℕ} (hn : 2 < n) :
    meteredParkingCount 1 n n =
      ∑ k ∈ Finset.range (n + 1), (n - 2) ^ (n - k) * (2 * n + 1 - k).choose k

/-- **Binet formula for 1-metered parking functions.** Let $m, n$ be natural numbers with
$m \le n + 1$ and $n > 2$. Then the number $\mathrm{mpf}_{m,n}(1)$ of $1$-metered
$(m, n)$-parking functions satisfies, as real numbers,
$$\mathrm{mpf}_{m,n}(1) = \frac{n(n + \sqrt{n^2-4}) - 2}{n(n + \sqrt{n^2-4}) - 4}
\left(\frac{n + \sqrt{n^2-4}}{2}\right)^m +
\frac{n(n - \sqrt{n^2-4}) - 2}{n(n - \sqrt{n^2-4}) - 4}
\left(\frac{n - \sqrt{n^2-4}}{2}\right)^m.$$

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Corollary 5 (`integers-2025-A73-cor-5`). -/
public theorem_wanted meteredParkingCount_one_binet {m n : ℕ} (hm : m ≤ n + 1) (hn : 2 < n) :
    (meteredParkingCount 1 m n : ℝ) =
      (n * (n + Real.sqrt (n ^ 2 - 4)) - 2) / (n * (n + Real.sqrt (n ^ 2 - 4)) - 4) *
          ((n + Real.sqrt (n ^ 2 - 4)) / 2) ^ m +
        (n * (n - Real.sqrt (n ^ 2 - 4)) - 2) / (n * (n - Real.sqrt (n ^ 2 - 4)) - 4) *
          ((n - Real.sqrt (n ^ 2 - 4)) / 2) ^ m

/-- **1-metered parking functions with three cars.** For every natural number $n \ge 2$, the
number of $1$-metered $(3, n)$-parking functions is $\mathrm{mpf}_{3,n}(1) = n^3 - 2n$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Proposition 7 (`integers-2025-A73-prop-7`). -/
public theorem_wanted meteredParkingCount_one_three {n : ℕ} (hn : 2 ≤ n) :
    meteredParkingCount 1 3 n = n ^ 3 - 2 * n

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

/-- **Parking-function shuffles.** Let $m'$, $n$, $k$ be natural numbers and let
$\pi : \{0, \dots, m' - 1\} \to \{0, \dots, n - 1\}$, with one-based letters $w_i = \pi(i) + 1$.
Then $\pi$ is a parking-function shuffle with parameters $(m', n, k)$ when all of the following
hold: no letter $w_i$ equals $k$; exactly $\max(m' + k - n, 0)$ letters satisfy $w_i < k$;
exactly $\max(n - k, 0)$ letters satisfy $w_i > k$; for every $s$ with $1 \le s \le k - 1$, at
most $k - s$ letters satisfy $s \le w_i \le k - 1$; and for every $s$ with $k + 1 \le s \le n$, at
most $n + 1 - s$ letters satisfy $w_i \ge s$.

With $m = m' + 1$, the word $(w_0, \dots, w_{m'-1})$ plays the role of the source's
$(\pi_2, \dots, \pi_m)$, and the conditions express membership in the source's set
$\mathrm{Sh}_m(k - 1, n - k)$ of shuffles of a parking function of $m - n + k - 1$ cars on
$k - 1$ spots (the letters below $k$) with a parking function of length $n - k$ shifted up by
$k$ (the letters above $k$): parking-function membership does not depend on the order of the
letters, and the last two conditions are the usual counting criterion for every car to park.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 4, Definition of `(m, n)`-parking function
shuffles (`Sh_m(k - 1, n - k)`). -/
public def IsParkingShuffle (m' n k : ℕ) (π : Fin m' → Fin n) : Prop :=
  (∀ i, (π i : ℕ) + 1 ≠ k) ∧
    (Finset.univ.filter fun i => (π i : ℕ) + 1 < k).card = m' + 1 + k - n - 1 ∧
    (Finset.univ.filter fun i => k < (π i : ℕ) + 1).card = n - k ∧
    (∀ j < k - 1, (Finset.univ.filter fun i => j ≤ (π i : ℕ) ∧ (π i : ℕ) < k - 1).card ≤
      k - 1 - j) ∧
    ∀ j ∈ Finset.Ico k n, (Finset.univ.filter fun i => j ≤ (π i : ℕ)).card ≤ n - j

/-- Membership in the parking-function shuffle set is decidable.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 4 (`Sh_m(k - 1, n - k)`). -/
public instance (m' n k : ℕ) (π : Fin m' → Fin n) : Decidable (IsParkingShuffle m' n k π) := by
  unfold IsParkingShuffle
  infer_instance

/-- **An example of a parking-function shuffle.** The word $(2, 6, 1, 0, 6, 1)$ with entries
in $\{0, \dots, 7\}$, which is $(3, 7, 2, 1, 7, 2)$ in one-based values, is a
$(7, 8)$-parking-function shuffle with parameter $k = 6$, that is, it lies in
$\mathrm{Sh}_7(5, 2)$. In one-based values it is a shuffle of the parking function
$(3, 2, 1, 2)$ with $4$ cars and $5$ spots and of $(7, 7) = (1, 1) + (6, 6)$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Section 4, Example 5. -/
public theorem isParkingShuffle_example :
    IsParkingShuffle 6 8 6 ![2, 6, 1, 0, 6, 1] := by
  unfold IsParkingShuffle
  decide

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
