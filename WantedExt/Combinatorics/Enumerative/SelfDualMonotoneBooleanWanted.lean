/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SetFamily.Intersecting
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.Order.Hom.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Order.BooleanFunction.SelfDual

/-!
# Counting self-dual monotone Boolean functions

Statements from Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone
Boolean Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5 (definitions read
from arXiv `2310.12637` and from the journal TeX source).

`D_n` is the set of monotone `f : (Fin n → Bool) → Bool` with the pointwise order, `f*` is
`booleanFunctionDual n f`, `x | y` and `x & y` are `⊔` and `⊓`, `Λ_n` is
`{f | IsSelfDualMonotone n f}` with `λ_n = Nat.card Λ_n`, and `d_n = |D_n|`. For `x ≤ y`,
`re(x, y) = |{z ∈ D_n | x ≤ z ≤ y}|`; `ℓ(b)` is the number of inputs where `b` is `true`.
Permutations act by `f ↦ (x ↦ f (x ∘ π))`; `γ(b)` is the size of the class of `b`. The
paper's sums over the class set `R_n` (classes identified with representatives) are stated for
any system of representatives `reps`. A concatenation of `2^k` elements of `D_n` is the
function on `n + k` variables that reads the last `k` variables as a binary index `∑ yⱼ 2^j`
into the word and applies the selected element to the first `n` variables.

A family `𝒰` of subsets of `X = {1, …, n}` (here `Fin n`) is linked when any two members meet
(`Set.Intersecting`), and a maximal linked system (mls) is a maximal linked family
(`Maximal Set.Intersecting 𝒰`). `Φ(π, Λ_n)` is the set of `f ∈ Λ_n` fixed by `π`, that is
with `(fun x => f (x ∘ π)) = f`.
-/

namespace MetaMathlibExt

open scoped Classical

@[expose] public section

/-- **Concatenation of a list of Boolean functions.** Let $n$ and $k$ be natural numbers and let
$W = (W_0, W_1, \dots, W_{m-1})$ be a finite list of Boolean functions on $n$ variables. The
concatenation $W_0 \cdot W_1 \cdots W_{m-1}$ on $n + k$ variables is the Boolean function that
sends $(x_0, \dots, x_{n-1}, y_0, \dots, y_{k-1})$ to $W_i(x_0, \dots, x_{n-1})$, where
$i = \sum_{j < k} y_j 2^j$ is the number whose binary digits are the last $k$ variables (true
counted as $1$ and false as $0$), and to false when $i \ge m$.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, the concatenation
representation of `D_n^{B^k}` before Theorem 10. -/
public def booleanCubeConcat (n k : ℕ) (W : List ((Fin n → Bool) → Bool)) :
    (Fin (n + k) → Bool) → Bool :=
  fun x => (W.getD (∑ j : Fin k, if x (Fin.natAdd n j) then 2 ^ (j : ℕ) else 0) fun _ => false)
    fun i => x (Fin.castAdd k i)

/-- **Concatenation at the all-false input.** For natural numbers $n$ and $k$ and a finite list
$W = (W_0, \dots, W_{m-1})$ of Boolean functions on $n$ variables, the concatenation of $W$ on
$n + k$ variables takes the value $W_0(\mathrm{false}, \dots, \mathrm{false})$ at the all-false
input when $W$ is nonempty, and the value false when $W$ is empty.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, the concatenation
representation of `D_n^{B^k}` before Theorem 10. -/
public theorem booleanCubeConcat_false (n k : ℕ) (W : List ((Fin n → Bool) → Bool)) :
    booleanCubeConcat n k W (fun _ => false) = W.getD 0 (fun _ => false) (fun _ => false) := by
  simp [booleanCubeConcat]

/-- **Currying monotone Boolean functions (Lemma 1).** For a natural number $m$, let $D_m$ be the
poset of monotone Boolean functions $\{0,1\}^m \to \{0,1\}$, where $0 < 1$, inputs are ordered
coordinatewise and functions are ordered pointwise. Then for all natural numbers $n$ and $k$,
$D_{n+k}$ is order-isomorphic to the poset of monotone maps $\{0,1\}^k \to D_n$, ordered
pointwise.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Lemma 1
(`jis-2025-25.6.5-lem-1`). -/
public theorem_wanted monotoneBooleanFunction_orderIso_curry (n k : ℕ) :
    Nonempty (((Fin (n + k) → Bool) →o Bool) ≃o
      ((Fin k → Bool) →o ((Fin n → Bool) →o Bool)))

/-- **Duality reverses order and exchanges joins and meets.** Let $f$ and $g$ be monotone
Boolean functions on $n$ variables, ordered pointwise, with duals $f^*$ and $g^*$. If $f \le g$
then $g^* \le f^*$. Moreover $(f \lor g)^* = f^* \land g^*$ and $(f \land g)^* = f^* \lor g^*$,
where $\lor$ and $\land$ are pointwise disjunction and conjunction.

Part 1 of the paper's lemma, $f^{**} = f$, holds for every Boolean function.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Lemma 2
(`jis-2025-25.6.5-lem-2`). -/
public theorem_wanted booleanFunctionDual_antitone_sup_inf (n : ℕ)
    (f g : (Fin n → Bool) → Bool) (hf : Monotone f) (hg : Monotone g) :
    (f ≤ g → booleanFunctionDual n g ≤ booleanFunctionDual n f) ∧
      booleanFunctionDual n (f ⊔ g) = booleanFunctionDual n f ⊓ booleanFunctionDual n g ∧
      booleanFunctionDual n (f ⊓ g) = booleanFunctionDual n f ⊔ booleanFunctionDual n g

/-- **Permuting variables preserves monotonicity, duals and self-duality.** Let $f$ be a Boolean
function on $n$ variables, let $\pi$ be a permutation of the $n$ coordinates, and let $f^\pi$
be the function $x \mapsto f(x \circ \pi)$. If $f$ is monotone, then $f^\pi$ is monotone and
$(f^*)^\pi = (f^\pi)^*$, where $f^*$ is the dual of $f$. If $f$ is self-dual monotone, then so
is $f^\pi$.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Lemma 5
(`jis-2025-25.6.5-lem-5`). -/
public theorem_wanted booleanFunction_perm_monotone_dual_selfDual (n : ℕ)
    (f : (Fin n → Bool) → Bool) (π : Equiv.Perm (Fin n)) :
    (Monotone f → Monotone fun x => f (x ∘ π)) ∧
      (Monotone f →
        (fun x => booleanFunctionDual n f (x ∘ π)) = booleanFunctionDual n fun x => f (x ∘ π)) ∧
      (IsSelfDualMonotone n f → IsSelfDualMonotone n fun x => f (x ∘ π))

/-- **Counting self-dual monotone functions on $n + 1$ variables.** For every $n \ge 0$, the
number of self-dual monotone Boolean functions on $n + 1$ variables equals the number of
monotone Boolean functions $b$ on $n$ variables with $b \le b^*$, where $b^*$ is the dual of $b$
and functions are ordered pointwise. Moreover, for a permutation $\pi$ of the $n$ coordinates
write $b^\pi$ for the function $x \mapsto b(x \circ \pi)$, and let $R$ be any finite set of
monotone Boolean functions on $n$ variables such that for every monotone $f$ there is exactly
one $b \in R$ with $f = b^\pi$ for some permutation $\pi$. Then the number of self-dual
monotone Boolean functions on $n + 1$ variables equals $\sum_{b \in R,\ b \le b^*} \gamma(b)$,
where $\gamma(b)$ is the number of distinct functions $b^\pi$ as $\pi$ ranges over all
permutations.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Theorem 6
(`jis-2025-25.6.5-thm-6`). -/
public theorem_wanted card_selfDualMonotone_succ (n : ℕ) :
    Nat.card {f : (Fin (n + 1) → Bool) → Bool // IsSelfDualMonotone (n + 1) f} =
        Nat.card {b : (Fin n → Bool) → Bool // Monotone b ∧ b ≤ booleanFunctionDual n b} ∧
      ∀ reps : Finset ((Fin n → Bool) → Bool), (∀ b ∈ reps, Monotone b) →
        (∀ f : (Fin n → Bool) → Bool, Monotone f →
          ∃! b, b ∈ reps ∧ ∃ π : Equiv.Perm (Fin n), f = fun x => b (x ∘ π)) →
        Nat.card {f : (Fin (n + 1) → Bool) → Bool // IsSelfDualMonotone (n + 1) f} =
          ∑ b ∈ reps with b ≤ booleanFunctionDual n b,
            Nat.card {g : (Fin n → Bool) → Bool //
              ∃ π : Equiv.Perm (Fin n), g = fun x => b (x ∘ π)}

/-- **Upper bound for self-dual monotone functions on $n + 1$ variables.** For every $n \ge 0$,
the number of self-dual monotone Boolean functions on $n + 1$ variables is at most the number
of monotone Boolean functions on $n$ variables.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Corollary 7
(`jis-2025-25.6.5-cor-7`). -/
public theorem_wanted card_selfDualMonotone_succ_le (n : ℕ) :
    Nat.card {f : (Fin (n + 1) → Bool) → Bool // IsSelfDualMonotone (n + 1) f} ≤
      Nat.card {f : (Fin n → Bool) → Bool // Monotone f}

/-- **Weights of monotone Boolean functions and their duals (Lemma 8).** Order $\{0,1\}$ by
$0 < 1$, inputs in $\{0,1\}^n$ coordinatewise and Boolean functions on $\{0,1\}^n$ pointwise. For
such a function $f$, let $f^*(x) = \lnot f(\bar x)$ be its dual, where $\bar x$ is the
coordinatewise complement of $x$, and let $\ell(f)$ be the number of $x \in \{0,1\}^n$ with
$f(x) = 1$. Let $b$ be a monotone Boolean function on $\{0,1\}^n$. Then: if $b \le b^*$, then
$2\ell(b) \le 2^n$; if $2\ell(b) = 2^n$ and $b \le b^*$, then $b = b^*$; if $b = b^*$, then
$2\ell(b) = 2^n$; and $\ell(b^*) = 2^n - \ell(b)$. Moreover, the number of monotone Boolean
functions $f$ on $\{0,1\}^n$ with $2\ell(f) < 2^n$ equals the number of those with
$2\ell(f) > 2^n$.

For $n \ge 1$ the comparisons of $2\ell$ with $2^n$ are the paper's comparisons of $\ell$ with
$2^{n-1}$; written this way the statement also covers $n = 0$.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Lemma 8
(`jis-2025-25.6.5-lem-8`). -/
public theorem_wanted monotoneBooleanFunction_weight_dual (n : ℕ) (b : (Fin n → Bool) → Bool)
    (hb : Monotone b) :
    (b ≤ booleanFunctionDual n b → 2 * Nat.card {x // b x = true} ≤ 2 ^ n) ∧
      (2 * Nat.card {x // b x = true} = 2 ^ n → b ≤ booleanFunctionDual n b →
        b = booleanFunctionDual n b) ∧
      (b = booleanFunctionDual n b → 2 * Nat.card {x // b x = true} = 2 ^ n) ∧
      Nat.card {x // booleanFunctionDual n b x = true} = 2 ^ n - Nat.card {x // b x = true} ∧
      Nat.card {f : (Fin n → Bool) → Bool // Monotone f ∧ 2 * Nat.card {x // f x = true} < 2 ^ n} =
        Nat.card {f : (Fin n → Bool) → Bool //
          Monotone f ∧ 2 ^ n < 2 * Nat.card {x // f x = true}}

/-- **Recursion for self-dual monotone functions from $n$ to $n + 1$ variables.** Let $n \ge 1$,
let $\lambda_m$ be the number of self-dual monotone Boolean functions on $m$ variables, and let
$d_n$ be the number of monotone Boolean functions on $n$ variables. For a Boolean function $b$
on $n$ variables let $b^*$ be its dual and $\ell(b)$ the number of inputs at which $b$ is true,
order functions pointwise, and for a permutation $\pi$ of the $n$ coordinates write $b^\pi$ for
the function $x \mapsto b(x \circ \pi)$. Let $R$ be any finite set of monotone Boolean
functions on $n$ variables such that for every monotone $f$ there is exactly one $b \in R$ with
$f = b^\pi$ for some permutation $\pi$, and let $\gamma(b)$ be the number of distinct functions
$b^\pi$ as $\pi$ ranges over all permutations. Then
$$
\lambda_{n+1} = \lambda_n + \sum_{b \in R,\ \ell(b) < 2^{n-1},\ b \le b^*} \gamma(b),
$$
and $2 \lambda_{n+1} \le d_n + \lambda_n$.

The bound is the paper's $\lambda_{n+1} \le (d_n + \lambda_n) / 2$ with the division cleared.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Theorem 9
(`jis-2025-25.6.5-thm-9`). -/
public theorem_wanted card_selfDualMonotone_succ_eq_add (n : ℕ) (hn : 1 ≤ n) :
    (∀ reps : Finset ((Fin n → Bool) → Bool), (∀ b ∈ reps, Monotone b) →
        (∀ f : (Fin n → Bool) → Bool, Monotone f →
          ∃! b, b ∈ reps ∧ ∃ π : Equiv.Perm (Fin n), f = fun x => b (x ∘ π)) →
        Nat.card {f : (Fin (n + 1) → Bool) → Bool // IsSelfDualMonotone (n + 1) f} =
          Nat.card {f : (Fin n → Bool) → Bool // IsSelfDualMonotone n f} +
            ∑ b ∈ reps with
                2 * Nat.card {x // b x = true} < 2 ^ n ∧ b ≤ booleanFunctionDual n b,
              Nat.card {g : (Fin n → Bool) → Bool //
                ∃ π : Equiv.Perm (Fin n), g = fun x => b (x ∘ π)}) ∧
      2 * Nat.card {f : (Fin (n + 1) → Bool) → Bool // IsSelfDualMonotone (n + 1) f} ≤
        Nat.card {f : (Fin n → Bool) → Bool // Monotone f} +
          Nat.card {f : (Fin n → Bool) → Bool // IsSelfDualMonotone n f}

/-- **Counting self-dual monotone functions on $n + 2$ variables.** Let $n \ge 0$ and let
$\lambda_{n+2}$ be the number of self-dual monotone Boolean functions on $n + 2$ variables. For
a monotone Boolean function $b$ on $n$ variables let $r(b)$ be the number of monotone Boolean
functions $z$ on $n$ variables with $b \lor b^* \le z$, where $b^*$ is the dual of $b$, $\lor$
is pointwise disjunction and functions are ordered pointwise. Then $\lambda_{n+2}$ is the sum
of $r(b)$ over all monotone Boolean functions $b$ on $n$ variables. Moreover, for a permutation
$\pi$ of the $n$ coordinates write $b^\pi$ for the function $x \mapsto b(x \circ \pi)$, and let
$R$ be any finite set of monotone Boolean functions on $n$ variables such that for every
monotone $f$ there is exactly one $b \in R$ with $f = b^\pi$ for some permutation $\pi$. Then
$\lambda_{n+2} = \sum_{b \in R} \gamma(b) \, r(b)$, where $\gamma(b)$ is the number of distinct
functions $b^\pi$ as $\pi$ ranges over all permutations.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Theorem 10
(`jis-2025-25.6.5-thm-10`). -/
public theorem_wanted card_selfDualMonotone_add_two (n : ℕ) :
    Nat.card {f : (Fin (n + 2) → Bool) → Bool // IsSelfDualMonotone (n + 2) f} =
        ∑ b ∈ Finset.univ.filter (fun b : (Fin n → Bool) → Bool => Monotone b),
          Nat.card {z : (Fin n → Bool) → Bool // Monotone z ∧ b ⊔ booleanFunctionDual n b ≤ z} ∧
      ∀ reps : Finset ((Fin n → Bool) → Bool), (∀ b ∈ reps, Monotone b) →
        (∀ f : (Fin n → Bool) → Bool, Monotone f →
          ∃! b, b ∈ reps ∧ ∃ π : Equiv.Perm (Fin n), f = fun x => b (x ∘ π)) →
        Nat.card {f : (Fin (n + 2) → Bool) → Bool // IsSelfDualMonotone (n + 2) f} =
          ∑ b ∈ reps, Nat.card {g : (Fin n → Bool) → Bool //
              ∃ π : Equiv.Perm (Fin n), g = fun x => b (x ∘ π)} *
            Nat.card {z : (Fin n → Bool) → Bool // Monotone z ∧ b ⊔ booleanFunctionDual n b ≤ z}

/-- **Dedekind numbers bound self-dual counts from below (Corollary 11).** For a natural number
$n$, let $d_n$ be the number of monotone Boolean functions $\{0,1\}^n \to \{0,1\}$ (for the
coordinatewise order with $0 < 1$) and let $\lambda_{n+2}$ be the number of self-dual monotone
Boolean functions $\{0,1\}^{n+2} \to \{0,1\}$, that is, monotone functions $f$ with
$f(\bar x) = \lnot f(x)$ for every $x$, where $\bar x$ is the coordinatewise complement of $x$.
Then $d_n \le \lambda_{n+2}$.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Corollary 11
(`jis-2025-25.6.5-cor-11`). -/
public theorem_wanted le_card_selfDualMonotone_add_two (n : ℕ) :
    Nat.card {f : (Fin n → Bool) → Bool // Monotone f} ≤
      Nat.card {f : (Fin (n + 2) → Bool) → Bool // IsSelfDualMonotone (n + 2) f}

/-- **Self-dual monotone functions on $n+4$ variables as concatenations (Theorem 12).** Order
$\{0,1\}$ by $0 < 1$, inputs coordinatewise and Boolean functions pointwise, with $\vee$ the
pointwise maximum. Let $D_n$ be the set of monotone Boolean functions on $\{0,1\}^n$, and let
$f^*(x) = \lnot f(\bar x)$ be the dual of $f$, where $\bar x$ is the coordinatewise complement of
$x$; a Boolean function $F$ is self-dual monotone if it is monotone and $F^* = F$. The
concatenation $W_0 \cdot W_1 \cdots W_{15}$ of Boolean functions on $\{0,1\}^n$ is the Boolean
function on $\{0,1\}^{n+4}$ sending $(x, y_0, y_1, y_2, y_3)$, with $x \in \{0,1\}^n$, to
$W_i(x)$, where $i = y_0 + 2y_1 + 4y_2 + 8y_3$. Let $a, b, c, d, e, f, g, h \in D_n$ satisfy
$a \vee b \vee c \vee a^* \vee b^* \vee c^* \le h$, $a \vee b \vee c \le d \le h$,
$a \vee b^* \vee c^* \le e \le h$, $b \vee a^* \vee c^* \le f \le h$ and
$c \vee a^* \vee b^* \le g \le h$. Then the concatenation
$$h^* \cdot g^* \cdot f^* \cdot a \cdot e^* \cdot b \cdot c \cdot d \cdot
d^* \cdot c^* \cdot b^* \cdot e \cdot a^* \cdot f \cdot g \cdot h$$
is a self-dual monotone Boolean function on $\{0,1\}^{n+4}$. Conversely, every self-dual
monotone Boolean function on $\{0,1\}^{n+4}$ equals this concatenation for some
$a, b, c, d, e, f, g, h \in D_n$ satisfying these inequalities.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Theorem 12
(`jis-2025-25.6.5-thm-12`). -/
public theorem_wanted selfDualMonotone_add_four_iff_concat (n : ℕ) :
    (∀ a b c d e f g h : (Fin n → Bool) → Bool,
      Monotone a → Monotone b → Monotone c → Monotone d → Monotone e → Monotone f →
      Monotone g → Monotone h →
      a ⊔ b ⊔ c ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n b ⊔
        booleanFunctionDual n c ≤ h →
      a ⊔ b ⊔ c ≤ d → d ≤ h →
      a ⊔ booleanFunctionDual n b ⊔ booleanFunctionDual n c ≤ e → e ≤ h →
      b ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n c ≤ f → f ≤ h →
      c ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n b ≤ g → g ≤ h →
      IsSelfDualMonotone (n + 4) (booleanCubeConcat n 4
        [booleanFunctionDual n h, booleanFunctionDual n g, booleanFunctionDual n f, a,
          booleanFunctionDual n e, b, c, d, booleanFunctionDual n d, booleanFunctionDual n c,
          booleanFunctionDual n b, e, booleanFunctionDual n a, f, g, h])) ∧
    ∀ F : (Fin (n + 4) → Bool) → Bool, IsSelfDualMonotone (n + 4) F →
      ∃ a b c d e f g h : (Fin n → Bool) → Bool,
        Monotone a ∧ Monotone b ∧ Monotone c ∧ Monotone d ∧ Monotone e ∧ Monotone f ∧
        Monotone g ∧ Monotone h ∧
        a ⊔ b ⊔ c ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n b ⊔
          booleanFunctionDual n c ≤ h ∧
        a ⊔ b ⊔ c ≤ d ∧ d ≤ h ∧
        a ⊔ booleanFunctionDual n b ⊔ booleanFunctionDual n c ≤ e ∧ e ≤ h ∧
        b ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n c ≤ f ∧ f ≤ h ∧
        c ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n b ≤ g ∧ g ≤ h ∧
        F = booleanCubeConcat n 4
          [booleanFunctionDual n h, booleanFunctionDual n g, booleanFunctionDual n f, a,
            booleanFunctionDual n e, b, c, d, booleanFunctionDual n d, booleanFunctionDual n c,
            booleanFunctionDual n b, e, booleanFunctionDual n a, f, g, h]

/-- **Counting self-dual monotone functions on $n + 4$ variables.** Let $D_n$ be the set of
monotone Boolean functions on $n$ variables, ordered pointwise, with $\lor$ the pointwise
disjunction and $f^*$ the dual of $f$. For $x, h \in D_n$ let $\mathrm{re}(x, h)$ be the number
of $z \in D_n$ with $x \le z \le h$. Then the number of self-dual monotone Boolean functions on
$n + 4$ variables equals
$$
\sum_{a, b, c \in D_n} \ \sum_{h \in D_n,\ h \ge a \lor b \lor c \lor a^* \lor b^* \lor c^*}
\mathrm{re}(a \lor b \lor c, h) \, \mathrm{re}(a \lor b^* \lor c^*, h) \,
\mathrm{re}(b \lor a^* \lor c^*, h) \, \mathrm{re}(c \lor a^* \lor b^*, h).
$$

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Theorem 13
(`jis-2025-25.6.5-thm-13`). -/
public theorem_wanted card_selfDualMonotone_add_four (n : ℕ) :
    Nat.card {F : (Fin (n + 4) → Bool) → Bool // IsSelfDualMonotone (n + 4) F} =
      ∑ a ∈ Finset.univ.filter (fun b : (Fin n → Bool) → Bool => Monotone b),
      ∑ b ∈ Finset.univ.filter (fun b : (Fin n → Bool) → Bool => Monotone b),
      ∑ c ∈ Finset.univ.filter (fun b : (Fin n → Bool) → Bool => Monotone b),
      ∑ h ∈ Finset.univ.filter (fun h : (Fin n → Bool) → Bool => Monotone h ∧
          a ⊔ b ⊔ c ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n b ⊔
            booleanFunctionDual n c ≤ h),
        Nat.card {z : (Fin n → Bool) → Bool // Monotone z ∧ a ⊔ b ⊔ c ≤ z ∧ z ≤ h} *
        Nat.card {z : (Fin n → Bool) → Bool // Monotone z ∧
          a ⊔ booleanFunctionDual n b ⊔ booleanFunctionDual n c ≤ z ∧ z ≤ h} *
        Nat.card {z : (Fin n → Bool) → Bool // Monotone z ∧
          b ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n c ≤ z ∧ z ≤ h} *
        Nat.card {z : (Fin n → Bool) → Bool // Monotone z ∧
          c ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n b ≤ z ∧ z ≤ h}

/-- **Self-dual monotone functions on $n+4$ variables, interval form (Theorem 14).** Order
$\{0,1\}$ by $0 < 1$, inputs coordinatewise and Boolean functions pointwise, with $\vee$ the
pointwise maximum. Let $D_n$ be the set of monotone Boolean functions on $\{0,1\}^n$, and let
$f^*(x) = \lnot f(\bar x)$ be the dual of $f$, where $\bar x$ is the coordinatewise complement of
$x$; a Boolean function $F$ is self-dual monotone if it is monotone and $F^* = F$. The
concatenation $W_0 \cdot W_1 \cdots W_{15}$ of Boolean functions on $\{0,1\}^n$ is the Boolean
function on $\{0,1\}^{n+4}$ sending $(x, y_0, y_1, y_2, y_3)$, with $x \in \{0,1\}^n$, to
$W_i(x)$, where $i = y_0 + 2y_1 + 4y_2 + 8y_3$. Let $a, b, c, d, e, f, g, h \in D_n$ satisfy
$h^* \le h$, $h^* \le a \le h$, $h^* \le b \le h$, $h^* \le c \le h$,
$a \vee b \vee c \le d \le h$, $a \vee b^* \vee c^* \le e \le h$,
$b \vee a^* \vee c^* \le f \le h$ and $c \vee a^* \vee b^* \le g \le h$. Then the concatenation
$$h^* \cdot g^* \cdot f^* \cdot a \cdot e^* \cdot b \cdot c \cdot d \cdot
d^* \cdot c^* \cdot b^* \cdot e \cdot a^* \cdot f \cdot g \cdot h$$
is a self-dual monotone Boolean function on $\{0,1\}^{n+4}$. Conversely, every self-dual
monotone Boolean function on $\{0,1\}^{n+4}$ equals this concatenation for some
$a, b, c, d, e, f, g, h \in D_n$ satisfying these inequalities.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Theorem 14
(`jis-2025-25.6.5-thm-14`). -/
public theorem_wanted selfDualMonotone_add_four_iff_concat_of_dual_le (n : ℕ) :
    (∀ a b c d e f g h : (Fin n → Bool) → Bool,
      Monotone a → Monotone b → Monotone c → Monotone d → Monotone e → Monotone f →
      Monotone g → Monotone h →
      booleanFunctionDual n h ≤ h →
      booleanFunctionDual n h ≤ a → a ≤ h → booleanFunctionDual n h ≤ b → b ≤ h →
      booleanFunctionDual n h ≤ c → c ≤ h →
      a ⊔ b ⊔ c ≤ d → d ≤ h →
      a ⊔ booleanFunctionDual n b ⊔ booleanFunctionDual n c ≤ e → e ≤ h →
      b ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n c ≤ f → f ≤ h →
      c ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n b ≤ g → g ≤ h →
      IsSelfDualMonotone (n + 4) (booleanCubeConcat n 4
        [booleanFunctionDual n h, booleanFunctionDual n g, booleanFunctionDual n f, a,
          booleanFunctionDual n e, b, c, d, booleanFunctionDual n d, booleanFunctionDual n c,
          booleanFunctionDual n b, e, booleanFunctionDual n a, f, g, h])) ∧
    ∀ F : (Fin (n + 4) → Bool) → Bool, IsSelfDualMonotone (n + 4) F →
      ∃ a b c d e f g h : (Fin n → Bool) → Bool,
        Monotone a ∧ Monotone b ∧ Monotone c ∧ Monotone d ∧ Monotone e ∧ Monotone f ∧
        Monotone g ∧ Monotone h ∧
        booleanFunctionDual n h ≤ h ∧
        booleanFunctionDual n h ≤ a ∧ a ≤ h ∧ booleanFunctionDual n h ≤ b ∧ b ≤ h ∧
        booleanFunctionDual n h ≤ c ∧ c ≤ h ∧
        a ⊔ b ⊔ c ≤ d ∧ d ≤ h ∧
        a ⊔ booleanFunctionDual n b ⊔ booleanFunctionDual n c ≤ e ∧ e ≤ h ∧
        b ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n c ≤ f ∧ f ≤ h ∧
        c ⊔ booleanFunctionDual n a ⊔ booleanFunctionDual n b ≤ g ∧ g ≤ h ∧
        F = booleanCubeConcat n 4
          [booleanFunctionDual n h, booleanFunctionDual n g, booleanFunctionDual n f, a,
            booleanFunctionDual n e, b, c, d, booleanFunctionDual n d, booleanFunctionDual n c,
            booleanFunctionDual n b, e, booleanFunctionDual n a, f, g, h]

/-- **Maximal intersecting families split complementary pairs (Lemma 3, L2).** Let $n \ge 1$ and
let $\mathcal U$ be a maximal intersecting family of subsets of $X = \{0, \dots, n-1\}$: any two
members of $\mathcal U$, not necessarily distinct, have nonempty intersection, and no family of
subsets of $X$ strictly containing $\mathcal U$ has this property. Then for every
$A \subseteq X$, $A \in \mathcal U$ if and only if $X \setminus A \notin \mathcal U$.

The hypothesis $n \ge 1$ is needed: for $n = 0$ the empty family is the maximal intersecting
family, and it contains neither $\emptyset$ nor its complement $\emptyset$.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Lemma 3
(`jis-2025-25.6.5-lem-3`). -/
public theorem_wanted maximal_intersecting_mem_iff_compl_notMem {n : ℕ} (hn : 1 ≤ n)
    {U : Set (Finset (Fin n))} (hU : Maximal Set.Intersecting U) (A : Finset (Fin n)) :
    A ∈ U ↔ Aᶜ ∉ U

/-- **A criterion for maximal intersecting families (Lemma 4).** Let $n$ be a natural number and
let $\mathcal U$ be a family of subsets of $X = \{0, \dots, n-1\}$ such that $\mathcal U$ is an
upper set (if $A \in \mathcal U$ and $A \subseteq B \subseteq X$ then $B \in \mathcal U$) and,
for every $A \subseteq X$, $A \in \mathcal U$ if and only if $X \setminus A \notin \mathcal U$.
Then $\mathcal U$ is a maximal intersecting family: any two members of $\mathcal U$, not
necessarily distinct, have nonempty intersection, and no family of subsets of $X$ strictly
containing $\mathcal U$ has this property.

The paper's hypothesis $n \ge 1$ is not needed: for $n = 0$ the complement of $\emptyset$ is
$\emptyset$, so no family satisfies the second condition.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Lemma 4
(`jis-2025-25.6.5-lem-4`). -/
public theorem_wanted maximal_intersecting_of_isUpperSet_of_mem_iff_compl_notMem {n : ℕ}
    {U : Set (Finset (Fin n))} (h₁ : IsUpperSet U) (h₂ : ∀ A : Finset (Fin n), A ∈ U ↔ Aᶜ ∉ U) :
    Maximal Set.Intersecting U

/-- **Permutations with only even cycles fix no self-dual monotone function (Lemma 15).** Let
$\pi$ be a permutation of $\{0, \dots, n-1\}$ all of whose cycles have even length, that is,
every point has an orbit of even size under $\pi$. Let $f : \{0,1\}^n \to \{0,1\}$ be self-dual
monotone, that is, monotone for the coordinatewise order with $0 < 1$ and such that
$f(\bar x) = \lnot f(x)$ for every $x$, where $\bar x$ is the coordinatewise complement of $x$.
Then $f$ is not fixed by $\pi$: the function $x \mapsto f(x \circ \pi)$, where
$(x \circ \pi)_i = x_{\pi(i)}$, differs from $f$.

The paper also assumes that $n$ is even; this follows from the condition on the cycles.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Lemma 15
(`jis-2025-25.6.5-lem-15`). -/
public theorem_wanted selfDualMonotone_not_fixed_of_even_minimalPeriod {n : ℕ}
    (π : Equiv.Perm (Fin n)) (hπ : ∀ i, Even (Function.minimalPeriod π i))
    (f : (Fin n → Bool) → Bool) (hf : IsSelfDualMonotone n f) :
    (fun x => f (x ∘ π)) ≠ f

/-- **Permutations of eight variables fixing no self-dual monotone function (Corollary 16).**
Let $\pi$ be one of the permutations $(0\,1\,2\,3\,4\,5\,6\,7)$, $(0\,1)(2\,3\,4\,5\,6\,7)$,
$(0\,1\,2\,3)(4\,5\,6\,7)$, $(0\,1)(2\,3)(4\,5\,6\,7)$ and $(0\,1)(2\,3)(4\,5)(6\,7)$ of
$\{0, \dots, 7\}$, in cycle notation. Let $f : \{0,1\}^8 \to \{0,1\}$ be self-dual monotone,
that is, monotone for the coordinatewise order with $0 < 1$ and such that
$f(\bar x) = \lnot f(x)$ for every $x$, where $\bar x$ is the coordinatewise complement of $x$.
Then $f$ is not fixed by $\pi$: the function $x \mapsto f(x \circ \pi)$, where
$(x \circ \pi)_i = x_{\pi(i)}$, differs from $f$.

In the paper the points are numbered $1, \dots, 8$, so these permutations are $(12345678)$,
$(12)(345678)$, $(1234)(5678)$, $(12)(34)(5678)$ and $(12)(34)(56)(78)$.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Corollary 16
(`jis-2025-25.6.5-cor-16`). -/
public theorem_wanted selfDualMonotone_eight_not_fixed (π : Equiv.Perm (Fin 8))
    (hπ : π = c[0, 1, 2, 3, 4, 5, 6, 7] ∨ π = c[0, 1] * c[2, 3, 4, 5, 6, 7] ∨
      π = c[0, 1, 2, 3] * c[4, 5, 6, 7] ∨ π = c[0, 1] * c[2, 3] * c[4, 5, 6, 7] ∨
      π = c[0, 1] * c[2, 3] * c[4, 5] * c[6, 7])
    (f : (Fin 8 → Bool) → Bool) (hf : IsSelfDualMonotone 8 f) :
    (fun x => f (x ∘ π)) ≠ f

/-- **For odd $n$, every permutation fixes a self-dual monotone function.** Let $n$ be odd and
let $\pi$ be a permutation of the $n$ coordinates. Then there is a self-dual monotone Boolean
function $f$ on $n$ variables with $f(x \circ \pi) = f(x)$ for every input $x$.

Source: Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean
Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Lemma 17
(`jis-2025-25.6.5-lem-17`). -/
public theorem_wanted exists_selfDualMonotone_fixed_of_odd {n : ℕ} (hn : Odd n)
    (π : Equiv.Perm (Fin n)) :
    ∃ f : (Fin n → Bool) → Bool, IsSelfDualMonotone n f ∧ (fun x => f (x ∘ π)) = f

end

end MetaMathlibExt
