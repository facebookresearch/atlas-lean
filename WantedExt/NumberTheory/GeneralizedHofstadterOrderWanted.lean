/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.GeneralizedHofstadterOrder
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Order.GaloisConnection.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.NumberTheory.GeneralizedHofstadterOrderHofLEqAddHofCount

/-!
# Pointwise order of generalized Hofstadter functions

Statements from Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3
(arXiv:2410.00529; TeX source read for the definitions).

For `k ≥ 1`, `F_k(0) = 0` and `F_k(n) = n - F_k^k(n - 1)` (`hofstadterF`; exponents are
iterates, written `f^[j]`). `F_2` is Hofstadter's `G` and `F_3` is `H`. The substitution
`τ_k` maps `k ↦ k 1` and `i ↦ i + 1` for `1 ≤ i < k` (`hofTau`), `x_k` is its fixed point,
read off the prefixes `τ_k^n(k)` (`hofWord`), `L_k(n) = |τ_k(x_k[0:n))|` (`hofL`), and
`C_k^{(P)}(n) = #{0 ≤ j < n : P(x_k[j])}` (`hofCount`). The constants `α_k` and `β_k`, the
positive zeros of `X^k + X - 1` and `X^k - X^{k-1} - 1`, enter statements as hypotheses on a
real root, so no new definition is needed. The paper's `f <_∞ g` is `∀ᶠ n in atTop, f n < g n`.
-/

open Filter Topology

namespace MetaMathlibExt

@[expose] public section

/-- **Pointwise order of the generalized Hofstadter functions.** For every $k \ge 1$ and every
natural number $n$, the generalized Hofstadter functions satisfy $F_k(n) \le F_{k+1}(n)$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Theorem 1 (`jis-2026-26.3.3-thm-1`). -/
public theorem_wanted hofstadterF_le_succ {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    hofstadterF k n ≤ hofstadterF (k + 1) n

/-- **Basic properties of the iterated Hofstadter functions.** Let $j, k \ge 1$, let $F_k$ be the
generalized Hofstadter function, and write $F_k^i$ for its $i$-fold iterate. Then
$F_k^j(1) = F_k^j(2) = 1$; $F_k^j(n) \ge 1$ for every $n \ge 1$; $F_k^j(n) < n$ for every
$n \ge 2$; $F_k(n+1) - F_k(n) = 1 - \bigl(F_k^k(n) - F_k^k(n-1)\bigr)$ in $\mathbb{Z}$ for every
$n \ge 1$; $F_k^j(n+1)$ equals $F_k^j(n)$ or $F_k^j(n) + 1$ for every $n \ge 0$; and $F_k^j$ is
monotone and surjective from $\mathbb{N}$ to $\mathbb{N}$ but not injective.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Proposition 2 (`jis-2026-26.3.3-prop-2`). -/
public theorem_wanted hofstadterF_iterate_basic {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) :
    (hofstadterF k)^[j] 1 = 1 ∧ (hofstadterF k)^[j] 2 = 1 ∧
      (∀ n, 1 ≤ n → 1 ≤ (hofstadterF k)^[j] n) ∧
      (∀ n, 2 ≤ n → (hofstadterF k)^[j] n < n) ∧
      (∀ n, 1 ≤ n →
        (hofstadterF k (n + 1) : ℤ) - hofstadterF k n =
          1 - (((hofstadterF k)^[k] n : ℤ) - (hofstadterF k)^[k] (n - 1))) ∧
      (∀ n, (hofstadterF k)^[j] (n + 1) = (hofstadterF k)^[j] n ∨
        (hofstadterF k)^[j] (n + 1) = (hofstadterF k)^[j] n + 1) ∧
      Monotone (hofstadterF k)^[j] ∧ Function.Surjective (hofstadterF k)^[j] ∧
      ¬ Function.Injective (hofstadterF k)^[j]

/-- **Basic properties of the iterates of $L_k$.** Let $k \ge 1$, let $x_k$ be the fixed point of
the substitution $\tau_k$, with letters $x_k[0], x_k[1], \dots$ and prefixes
$x_k[0:n) = x_k[0] \cdots x_k[n-1]$, let $L_k(n) = |\tau_k(x_k[0:n))|$, and write $f^j$ for the
$j$-fold iterate of a map $f$ (so $f^0$ is the identity). Then for every $j \ge 0$:
(1) $L_k^j(n) = |\tau_k^j(x_k[0:n))|$ for every $n$;
(2) $L_k^j(0) = 0$, and $L_k^j(n+1) = L_k^j(n) + |\tau_k^j(x_k[n])|$ for every $n$;
(3) $L_k^j(1) = j + 1$ if $j \le k$, and $L_k^j(1) = L_k^{j-1}(1) + L_k^{j-k}(1)$ if $j \ge k$;
(4) $n \mapsto L_k^j(n)$ is strictly increasing;
(5) $L_k^j(n) \ge n$ for every $n$, with equality if and only if $j = 0$ or $n = 0$;
(6) for every $n \ge 1$, the sequence $i \mapsto L_k^i(n)$ is strictly increasing.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Proposition 4 (`jis-2026-26.3.3-prop-4`). -/
public theorem_wanted hofL_iterate_basic {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    (∀ n, (hofL k)^[j] n = ((hofTauList k)^[j] (hofPrefix k n)).length) ∧
      (hofL k)^[j] 0 = 0 ∧
      (∀ n, (hofL k)^[j] (n + 1) =
        (hofL k)^[j] n + ((hofTauList k)^[j] [hofWord k n]).length) ∧
      (j ≤ k → (hofL k)^[j] 1 = j + 1) ∧
      (k ≤ j → (hofL k)^[j] 1 = (hofL k)^[j - 1] 1 + (hofL k)^[j - k] 1) ∧
      StrictMono (hofL k)^[j] ∧
      (∀ n, n ≤ (hofL k)^[j] n ∧ ((hofL k)^[j] n = n ↔ j = 0 ∨ n = 0)) ∧
      (∀ n, 1 ≤ n → StrictMono fun i => (hofL k)^[i] n)

/-- **Fibres of the iterated Hofstadter functions.** Let $k \ge 1$ and $j \ge 0$. Let $F_k$ be the
generalized Hofstadter function, let $x_k[0]\,x_k[1] \cdots$ be the fixed point, beginning with
$k$, of the substitution $\tau_k$ that sends $k$ to $k\,1$ and every other letter $i$ to $i + 1$,
let $L_k(m)$ be the length of the word $\tau_k(x_k[0] \cdots x_k[m-1])$, and write $f^j$ for the
$j$-fold iterate of a function $f$. Then for every $n \ge 1$, the set of $m$ with $F_k^j(m) = n$
is the interval $L_k^j(n-1) < m \le L_k^j(n)$; and for every $m \ge 1$,
$L_k^j(F_k^j(m) - 1) < m \le L_k^j(F_k^j(m))$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Theorem 6 (`jis-2026-26.3.3-thm-6`). -/
public theorem_wanted hofstadterF_iterate_preimage_eq_Ioc {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    (∀ n, 1 ≤ n →
      (hofstadterF k)^[j] ⁻¹' {n} = Set.Ioc ((hofL k)^[j] (n - 1)) ((hofL k)^[j] n)) ∧
      (∀ m, 1 ≤ m →
        (hofL k)^[j] ((hofstadterF k)^[j] m - 1) < m ∧ m ≤ (hofL k)^[j] ((hofstadterF k)^[j] m))

/-- **Galois insertion between iterated Hofstadter functions.** Let $k \ge 1$ and $j \ge 0$. Let
$F_k$ be the generalized Hofstadter function, let $x_k[0]\,x_k[1] \cdots$ be the fixed point,
beginning with $k$, of the substitution $\tau_k$ that sends $k$ to $k\,1$ and every other letter
$i$ to $i + 1$, let $L_k(m)$ be the length of the word $\tau_k(x_k[0] \cdots x_k[m-1])$, and
write $f^j$ for the $j$-fold iterate of a function $f$. Then for all $n, m \ge 0$,
$F_k^j(n) \le m$ if and only if $n \le L_k^j(m)$, so $F_k^j$ and $L_k^j$ form a Galois
connection; and $F_k^j(L_k^j(m)) = m$ for every $m \ge 0$, so it is a Galois insertion.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Corollary 7 (`jis-2026-26.3.3-cor-7`). -/
public theorem_wanted hofstadterF_hofL_galoisInsertion {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    GaloisConnection (hofstadterF k)^[j] (hofL k)^[j] ∧
      ∀ m, (hofstadterF k)^[j] ((hofL k)^[j] m) = m

/-- **Iterated Hofstadter functions as letter counts.** Let $k \ge 1$ and $n \ge 0$. Let $F_k$ be
the generalized Hofstadter function and $F_k^j$ its $j$-fold iterate, let $x_k[0]\,x_k[1] \cdots$
be the fixed point, beginning with $k$, of the substitution $\tau_k$ that sends $k$ to $k\,1$ and
every other letter $i$ to $i + 1$, and for a property $P$ of letters let $C_k^{(P)}(m)$ be the
number of indices $0 \le i < m$ with $P(x_k[i])$. Then $F_k^{k-1}(n) = C_k^{(=k)}(n)$;
$F_k^j(n) = C_k^{(>j)}(n)$ for every $0 \le j < k$; and $F_k^{k+i-1}(n) = C_k^{(=i)}(n+i)$ for
every $1 \le i < k$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Proposition 8 (`jis-2026-26.3.3-prop-8`). -/
public theorem_wanted hofstadterF_iterate_eq_hofCount {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    (hofstadterF k)^[k - 1] n = hofCount k (· = k) n ∧
      (∀ j < k, (hofstadterF k)^[j] n = hofCount k (j < ·) n) ∧
      (∀ i, 1 ≤ i → i < k → (hofstadterF k)^[k + i - 1] n = hofCount k (· = i) (n + i))

/-- **Generalized Hofstadter function as a letter count.** Let $k > 1$ and $n \ge 0$. Let $F_k$ be
the generalized Hofstadter function, defined by $F_k(0) = 0$ and $F_k(m) = m - F_k^k(m - 1)$ for
$m \ge 1$, where $F_k^k$ is the $k$-fold iterate of $F_k$. Let $x_k[0]\,x_k[1] \cdots$ be the
fixed point, beginning with $k$, of the substitution $\tau_k$ that sends $k$ to $k\,1$ and every
other letter $i$ to $i + 1$, and for a property $P$ of letters let $C_k^{(P)}(n)$ be the number
of indices $0 \le i < n$ with $P(x_k[i])$. Then $F_k(n) = n - C_k^{(=1)}(n)$ and
$F_k(n) = C_k^{(\ne 1)}(n)$. Moreover, $F_k(n+1) = F_k(n)$ if and only if $x_k[n] = 1$, and
$F_k(n+1) = F_k(n) + 1$ whenever $x_k[n] \ne 1$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Proposition 10 (`jis-2026-26.3.3-prop-10`). -/
public theorem_wanted hofstadterF_eq_hofCount_ne_one {k : ℕ} (hk : 1 < k) (n : ℕ) :
    hofstadterF k n = n - hofCount k (· = 1) n ∧ hofstadterF k n = hofCount k (· ≠ 1) n ∧
      (hofstadterF k (n + 1) = hofstadterF k n ↔ hofWord k n = 1) ∧
      (hofWord k n ≠ 1 → hofstadterF k (n + 1) = hofstadterF k n + 1)

/-- **The letters of $x_k$ from the increments of the iterates of $F_k$.** Let $k \ge 1$, let $F_k$
be the generalized Hofstadter function with $j$-th iterate $F_k^j$ ($F_k^0$ the identity), and
let $x_k = x_k[0]\,x_k[1] \cdots$ be the fixed point of the substitution $\tau_k$
($k \mapsto k\,1$, $i \mapsto i + 1$ for $i \ne k$). For every natural number $n$: for each $j$
with $1 \le j < k$, $x_k[n] = j$ if and only if $F_k^{j-1}(n+1) = F_k^{j-1}(n) + 1$ and
$F_k^j(n+1) = F_k^j(n)$; and $x_k[n] = k$ if and only if $F_k^{k-1}(n+1) = F_k^{k-1}(n) + 1$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Proposition 11 (`jis-2026-26.3.3-prop-11`). -/
public theorem_wanted hofWord_eq_iff_hofstadterF_iterate_diff {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    (∀ j, 1 ≤ j → j < k →
      (hofWord k n = j ↔
        (hofstadterF k)^[j - 1] (n + 1) = (hofstadterF k)^[j - 1] n + 1 ∧
          (hofstadterF k)^[j] (n + 1) = (hofstadterF k)^[j] n)) ∧
      (hofWord k n = k ↔ (hofstadterF k)^[k - 1] (n + 1) = (hofstadterF k)^[k - 1] n + 1)

/-- **Monotonicity and asymptotics of the Hofstadter constants.** For each integer $k \ge 1$ let
$\alpha_k$ be a positive zero of $X^k + X - 1$ and $\beta_k$ a positive zero of
$X^k - X^{k-1} - 1$. Then for every $k \ge 1$ we have $\alpha_k < \alpha_{k+1}$,
$\beta_{k+1} < \beta_k$, $1 + 1/k \le \beta_k \le 1 + 1/\sqrt{k}$ and
$\sqrt{k} \le \beta_k^{k-1} \le k$. Moreover $\beta_k \to 1$ and $\alpha_k \to 1$ as
$k \to \infty$, and $\alpha_k = 1 - \ln k / k + o(\ln k / k)$ and
$\beta_k = 1 + \ln k / k + o(\ln k / k)$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Proposition 13 and Definition 12 (`jis-2026-26.3.3-prop-13`). -/
public theorem_wanted hofstadter_roots_monotone_asymptotics (α β : ℕ → ℝ)
    (hα : ∀ k, 1 ≤ k → 0 < α k ∧ α k ^ k + α k - 1 = 0)
    (hβ : ∀ k, 1 ≤ k → 0 < β k ∧ β k ^ k - β k ^ (k - 1) - 1 = 0) :
    (∀ k, 1 ≤ k → α k < α (k + 1)) ∧ (∀ k, 1 ≤ k → β (k + 1) < β k) ∧
      (∀ k : ℕ, 1 ≤ k →
        1 + 1 / (k : ℝ) ≤ β k ∧ β k ≤ 1 + 1 / Real.sqrt k ∧
          Real.sqrt k ≤ β k ^ (k - 1) ∧ β k ^ (k - 1) ≤ k) ∧
      Tendsto β atTop (𝓝 1) ∧ Tendsto α atTop (𝓝 1) ∧
      (fun k : ℕ => α k - (1 - Real.log k / k)) =o[atTop] (fun k : ℕ => Real.log k / k) ∧
      (fun k : ℕ => β k - (1 + Real.log k / k)) =o[atTop] (fun k : ℕ => Real.log k / k)

/-- **Limits of Hofstadter iterates and letter frequencies.** Let $k \ge 1$ and $j \ge 0$, let
$\alpha > 0$ satisfy $\alpha^k + \alpha - 1 = 0$ and let $\beta > 0$ satisfy
$\beta^k - \beta^{k-1} - 1 = 0$. Write $f^j$ for the $j$-fold iterate of a function $f$ and let
$F_k$ be the generalized Hofstadter function. Let $\tau_k$ be the substitution on letters with
$\tau_k(k) = k\,1$ and $\tau_k(i) = i + 1$ for $1 \le i < k$, let $x_k$ be the infinite word fixed
by $\tau_k$ that is the limit of the words $\tau_k^m(k)$, write $x_k[m]$ for its letter at index
$m$ (counting from $0$) and $x_k[0:n)$ for its prefix of length $n$, let
$L_k(n) = |\tau_k(x_k[0:n))|$, and for a letter $i$ let $C_k^{(=i)}(n)$ be the number of indices
$m < n$ with $x_k[m] = i$. Then, as $n \to \infty$: $F_k^j(n)/n \to \alpha^j$;
$L_k^j(n)/n \to \beta^j$; $C_k^{(=i)}(n)/n \to \alpha^{k+i-1}$ for every $i$ with $1 \le i < k$;
and $C_k^{(=k)}(n)/n \to \alpha^{k-1}$. Moreover $\alpha^{k-1} = \beta - 1$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Theorem 14 (`jis-2026-26.3.3-thm-14`). -/
public theorem_wanted hofstadter_limits {k : ℕ} (hk : 1 ≤ k) (j : ℕ) {α β : ℝ}
    (hα : 0 < α ∧ α ^ k + α - 1 = 0) (hβ : 0 < β ∧ β ^ k - β ^ (k - 1) - 1 = 0) :
    Tendsto (fun n : ℕ => ((hofstadterF k)^[j] n : ℝ) / n) atTop (𝓝 (α ^ j)) ∧
      Tendsto (fun n : ℕ => ((hofL k)^[j] n : ℝ) / n) atTop (𝓝 (β ^ j)) ∧
      (∀ i, 1 ≤ i → i < k →
        Tendsto (fun n : ℕ => (hofCount k (· = i) n : ℝ) / n) atTop (𝓝 (α ^ (k + i - 1)))) ∧
      Tendsto (fun n : ℕ => (hofCount k (· = k) n : ℝ) / n) atTop (𝓝 (α ^ (k - 1))) ∧
      α ^ (k - 1) = β - 1

/-- **Eventual order of iterated Hofstadter functions from their growth rates.** Let $k, k' \ge 1$
and $j, j' \ge 0$, let $F_k$ be the generalized Hofstadter function, write $F_k^i$ for its
$i$-fold iterate, let $\alpha > 0$ be a root of $X^k + X - 1$, and let $\alpha' > 0$ be a root of
$X^{k'} + X - 1$. If $\alpha^j < \alpha'^{j'}$, then $F_k^j(n) < F_{k'}^{j'}(n)$ for all
sufficiently large $n$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Corollary 16 (`jis-2026-26.3.3-cor-16`). -/
public theorem_wanted hofstadterF_iterate_eventually_lt_of_root_pow_lt {k k' : ℕ} (hk : 1 ≤ k)
    (hk' : 1 ≤ k') (j j' : ℕ) {α α' : ℝ} (hα : 0 < α ∧ α ^ k + α - 1 = 0)
    (hα' : 0 < α' ∧ α' ^ k' + α' - 1 = 0) (hlt : α ^ j < α' ^ j') :
    ∀ᶠ n in atTop, (hofstadterF k)^[j] n < (hofstadterF k')^[j'] n

/-- **Eventual order of iterates of consecutive Hofstadter functions.** Let $k \ge 1$, let $F_k$ be
the generalized Hofstadter function, write $F_k^i$ for its $i$-fold iterate, let $\alpha > 0$ be
a root of $X^k + X - 1$, and let $\alpha' > 0$ be a root of $X^{k+1} + X - 1$. Then for all
sufficiently large $n$, $F_k(n) < F_{k+1}(n)$, $F_{k+1}^{k+1}(n) < F_k^k(n)$ and
$F_{k+1}^{k+2}(n) < F_k^{k+1}(n)$. Moreover, for every $j \ge 0$: if $j/(j+1) \le \alpha$ or
$j^2 \le k$, then $F_{k+1}^{k+j+1}(n) < F_k^{k+j}(n)$ for all sufficiently large $n$; and if
$\alpha' \le j/(j+1)$ or $k < j$, then $F_k^{k+j}(n) < F_{k+1}^{k+j+1}(n)$ for all sufficiently
large $n$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Corollary 17 (`jis-2026-26.3.3-cor-17`). -/
public theorem_wanted hofstadterF_iterate_eventual_order_succ {k : ℕ} (hk : 1 ≤ k) {α α' : ℝ}
    (hα : 0 < α ∧ α ^ k + α - 1 = 0) (hα' : 0 < α' ∧ α' ^ (k + 1) + α' - 1 = 0) :
    (∀ᶠ n in atTop, hofstadterF k n < hofstadterF (k + 1) n) ∧
      (∀ᶠ n in atTop, (hofstadterF (k + 1))^[k + 1] n < (hofstadterF k)^[k] n) ∧
      (∀ᶠ n in atTop, (hofstadterF (k + 1))^[k + 2] n < (hofstadterF k)^[k + 1] n) ∧
      (∀ j : ℕ, ((j : ℝ) / (j + 1) ≤ α ∨ j ^ 2 ≤ k) →
        ∀ᶠ n in atTop, (hofstadterF (k + 1))^[k + j + 1] n < (hofstadterF k)^[k + j] n) ∧
      (∀ j : ℕ, (α' ≤ (j : ℝ) / (j + 1) ∨ k < j) →
        ∀ᶠ n in atTop, (hofstadterF k)^[k + j] n < (hofstadterF (k + 1))^[k + j + 1] n)

open Classical in
/-- **Values with exactly one preimage under a Hofstadter function.** Let $k \ge 1$, let
$\alpha > 0$ satisfy $\alpha^k + \alpha - 1 = 0$ and let $\beta > 0$ satisfy
$\beta^k - \beta^{k-1} - 1 = 0$. Write $f^j$ for the $j$-fold iterate of a function $f$ and let
$F_k$ be the generalized Hofstadter function. Let $\tau_k$ be the substitution on letters with
$\tau_k(k) = k\,1$ and $\tau_k(i) = i + 1$ for $1 \le i < k$, let $x_k$ be the infinite word fixed
by $\tau_k$ that is the limit of the words $\tau_k^m(k)$, write $x_k[0:n)$ for its prefix of
length $n$ and let $L_k(n) = |\tau_k(x_k[0:n))|$. Let $U_k(n)$ be the number of $j$ with
$0 \le j < n$ for which exactly one natural number $m$ satisfies $F_k(m) = j$. Then for every
$n \ge 1$, $U_k(n) = 2n - 1 - L_k(n - 1)$ and $U_k(n) = n - F_k^{k-1}(n - 1)$. Moreover
$U_k(n)/n \to 1 - \alpha^{k-1}$ as $n \to \infty$, and $1 - \alpha^{k-1} = 2 - \beta$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Proposition 18 (`jis-2026-26.3.3-prop-18`). -/
public theorem_wanted hofstadter_single_antecedent_count {k : ℕ} (hk : 1 ≤ k) {α β : ℝ}
    (hα : 0 < α ∧ α ^ k + α - 1 = 0) (hβ : 0 < β ∧ β ^ k - β ^ (k - 1) - 1 = 0) :
    (∀ n, 0 < n →
      ((Finset.range n).filter fun j => Nat.card {m // hofstadterF k m = j} = 1).card =
          2 * n - 1 - hofL k (n - 1) ∧
        ((Finset.range n).filter fun j => Nat.card {m // hofstadterF k m = j} = 1).card =
          n - (hofstadterF k)^[k - 1] (n - 1)) ∧
      Tendsto (fun n : ℕ =>
          (((Finset.range n).filter fun j => Nat.card {m // hofstadterF k m = j} = 1).card : ℝ) /
            n) atTop (𝓝 (1 - α ^ (k - 1))) ∧
      1 - α ^ (k - 1) = 2 - β

/-- **Order of iterates of $L_k$ against order of iterates of $F_k$.** Let $F_k$ be the
generalized Hofstadter function, let $x_k[0]\,x_k[1] \cdots$ be the fixed point, beginning with
$k$, of the substitution $\tau_k$ that sends $k$ to $k\,1$ and every other letter $i$ to
$i + 1$, let $L_k(n)$ be the length of the word $\tau_k(x_k[0] \cdots x_k[n-1])$, and write
$f^j$ for the $j$-fold iterate of a function $f$. Let $k, k' \ge 1$ and $j, j' \ge 0$. Then
$L_k^j(n) \le L_{k'}^{j'}(n)$ for every $n$ if and only if $F_{k'}^{j'}(n) \le F_k^j(n)$ for
every $n$. Moreover, for every natural number $n$:
(a) $L_k^j(n) \le L_{k'}^{j'}(n)$ if and only if $F_{k'}^{j'}(m) \le F_k^j(m)$ for
$m = L_k^j(n)$;
(b) $L_k^j(n) < L_{k'}^{j'}(n)$ if and only if $F_{k'}^{j'}(m) < F_k^j(m)$ for
$m = L_{k'}^{j'}(n)$;
(c) if $L_k^j(m) \le L_{k'}^{j'}(m)$ for $m = F_k^j(n)$, then $F_{k'}^{j'}(n) \le F_k^j(n)$;
(d) if $F_k^j(n) < F_{k'}^{j'}(n)$, then $L_{k'}^{j'}(m) < L_k^j(m)$ for $m = F_k^j(n)$.

In (d) the paper prints $m = F_{k'}^{j'}(n)$; its proof derives (d) as the contrapositive of
(c), which gives $m = F_k^j(n)$. The printed form fails for $k = 1$, $j = 1$, $k' = 4$,
$j' = 2$ and $n = 8$: $F_1(8) = 4 < F_4^2(8) = 5$, but $L_4^2(5) = L_1(5) = 10$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Proposition 19 (`jis-2026-26.3.3-prop-19`). -/
public theorem_wanted hofL_iterate_le_iff_hofstadterF_iterate_le {k k' : ℕ} (hk : 1 ≤ k)
    (hk' : 1 ≤ k') (j j' : ℕ) :
    ((hofL k)^[j] ≤ (hofL k')^[j'] ↔ (hofstadterF k')^[j'] ≤ (hofstadterF k)^[j]) ∧
      ∀ n,
        ((hofL k)^[j] n ≤ (hofL k')^[j'] n ↔
          (hofstadterF k')^[j'] ((hofL k)^[j] n) ≤ (hofstadterF k)^[j] ((hofL k)^[j] n)) ∧
        ((hofL k)^[j] n < (hofL k')^[j'] n ↔
          (hofstadterF k')^[j'] ((hofL k')^[j'] n) < (hofstadterF k)^[j] ((hofL k')^[j'] n)) ∧
        ((hofL k)^[j] ((hofstadterF k)^[j] n) ≤ (hofL k')^[j'] ((hofstadterF k)^[j] n) →
          (hofstadterF k')^[j'] n ≤ (hofstadterF k)^[j] n) ∧
        ((hofstadterF k)^[j] n < (hofstadterF k')^[j'] n →
          (hofL k')^[j'] ((hofstadterF k)^[j] n) < (hofL k)^[j] ((hofstadterF k)^[j] n))

/-- **Comparing $L_k$ with $L_{k+1}$.** Let $x_k[0]\,x_k[1] \cdots$ be the fixed point,
beginning with $k$, of the substitution $\tau_k$ that sends $k$ to $k\,1$ and every other
letter $i$ to $i + 1$, let $L_k(n)$ be the length of the word $\tau_k(x_k[0] \cdots x_k[n-1])$,
write $L_k^j$ for the $j$-fold iterate of $L_k$, and let $C_k^{(=k)}(n)$ be the number of
indices $i < n$ with $x_k[i] = k$. For all $k \ge 1$, $n \ge 1$ and $j$ with $0 \le j \le k$:
$L_{k+1}(n) \le L_k(n)$, $C_{k+1}^{(=k+1)}(n) \le C_k^{(=k)}(n)$, and
$L_k^j(n) < L_{k+1}^{j+1}(n)$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Theorem 20 (`jis-2026-26.3.3-thm-20`). -/
public theorem_wanted hofL_succ_comparison {k n j : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) (hj : j ≤ k) :
    hofL (k + 1) n ≤ hofL k n ∧ hofCount (k + 1) (· = k + 1) n ≤ hofCount k (· = k) n ∧
      (hofL k)^[j] n < (hofL (k + 1))^[j + 1] n

/-- **Iterates of consecutive Hofstadter functions are ordered.** For every $k \ge 1$, $j \ge 0$
and $n \ge 0$, $F_k^j(n) \le F_{k+1}^j(n)$, where $F_k$ is the generalized Hofstadter function and
$F_k^j$ is its $j$-fold iterate.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Theorem 22 (`jis-2026-26.3.3-thm-22`). -/
public theorem_wanted hofstadterF_iterate_le_succ {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    (hofstadterF k)^[j] ≤ (hofstadterF (k + 1))^[j]

/-- **Shifted order of iterates of consecutive Hofstadter functions.** Let $F_k$ denote the
generalized Hofstadter functions and write $f^j$ for the $j$-fold iterate of a function $f$. For
every $k \ge 1$, every $j$ with $0 \le j \le k$ and every natural number $n$,
$F_{k+1}^{j+1}(n) \le F_k^j(n)$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Theorem 23 (`jis-2026-26.3.3-thm-23`). -/
public theorem_wanted hofstadterF_iterate_succ_le_iterate {k j : ℕ} (hk : 1 ≤ k) (hj : j ≤ k) :
    (hofstadterF (k + 1))^[j + 1] ≤ (hofstadterF k)^[j]

/-- **Comparing $L_{k+1}^{j+1}(1)$ with $L_k^j(1)$.** Let $x_k[0]\,x_k[1] \cdots$ be the fixed
point, beginning with $k$, of the substitution $\tau_k$ that sends $k$ to $k\,1$ and every
other letter $i$ to $i + 1$, let $L_k(n)$ be the length of the word
$\tau_k(x_k[0] \cdots x_k[n-1])$, and write $L_k^j$ for the $j$-fold iterate of $L_k$. Let
$k \ge 1$, and take differences in $\mathbb{Z}$. Then $L_{k+1}^{j+1}(1) - L_k^j(1) = 1$ for
every $j \le 2k$; $2\bigl(L_{k+1}^{j+1}(1) - L_k^j(1)\bigr) = -(j - 2k - 1)(j - 2k + 2)$ for
every $j$ with $2k \le j \le 3k$; $L_{k+1}^{2k+2}(1) = L_k^{2k+1}(1)$; and
$L_{k+1}^{j+1}(1) < L_k^j(1)$ for every $j \ge 2k + 2$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Lemma 24 (`jis-2026-26.3.3-lem-24`). -/
public theorem_wanted hofL_iterate_one_succ_sub {k : ℕ} (hk : 1 ≤ k) :
    (∀ j, j ≤ 2 * k → ((hofL (k + 1))^[j + 1] 1 : ℤ) - (hofL k)^[j] 1 = 1) ∧
      (∀ j, 2 * k ≤ j → j ≤ 3 * k →
        2 * (((hofL (k + 1))^[j + 1] 1 : ℤ) - (hofL k)^[j] 1) =
          -(((j : ℤ) - 2 * k - 1) * ((j : ℤ) - 2 * k + 2))) ∧
      (hofL (k + 1))^[2 * k + 2] 1 = (hofL k)^[2 * k + 1] 1 ∧
      (∀ j, 2 * k + 2 ≤ j → (hofL (k + 1))^[j + 1] 1 < (hofL k)^[j] 1)

/-- **Points where $L_k^j$ exceeds $L_{k+1}^{j+1}$.** Let $x_k[0]\,x_k[1] \cdots$ be the fixed
point, beginning with $k$, of the substitution $\tau_k$ that sends $k$ to $k\,1$ and every
other letter $i$ to $i + 1$, let $L_k(n)$ be the length of the word
$\tau_k(x_k[0] \cdots x_k[n-1])$, and write $L_k^j$ for the $j$-fold iterate of $L_k$. Let
$k \ge 1$. Then $L_{k+1}^{j+1}(2k + 3 - j) < L_k^j(2k + 3 - j)$ for every $j$ with
$k + 2 \le j \le 2k + 2$, and $L_{k+1}^{j+1}(1) < L_k^j(1)$ for every $j \ge 2k + 2$.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Lemma 25 (`jis-2026-26.3.3-lem-25`). -/
public theorem_wanted hofL_iterate_witness_gt {k : ℕ} (hk : 1 ≤ k) :
    (∀ j, k + 2 ≤ j → j ≤ 2 * k + 2 →
      (hofL (k + 1))^[j + 1] (2 * k + 3 - j) < (hofL k)^[j] (2 * k + 3 - j)) ∧
      (∀ j, 2 * k + 2 ≤ j → (hofL (k + 1))^[j + 1] 1 < (hofL k)^[j] 1)

/-- **Witnesses that the letter counts of $x_k$ and $x_{k+1}$ are not ordered.** For a natural
number $k$, let $\tau_k$ be the substitution sending the letter $k$ to $k\,1$ and every other
letter $a$ to $a + 1$, let $x_k = x_k[0]\,x_k[1] \cdots$ be its fixed point beginning with $k$,
let $C_k^{(=i)}(n)$ be the number of indices $j < n$ with $x_k[j] = i$, let $L_k(n)$ be the
length of the word $\tau_k(x_k[0] \cdots x_k[n-1])$, and write $L_k^j$ for the $j$-fold iterate
of $L_k$. For all natural numbers $i$ and $k$ with $3 \le i < k$, put $n = i + L_k^{2k+2}(1)$
and $m = i + L_{k+1}^{k+i}(1)$. Then $C_k^{(=i)}(n) < C_{k+1}^{(=i)}(n)$ and
$C_{k+1}^{(=i)}(m) < C_k^{(=i)}(m)$, so for these letters $i$ the letter counts of $x_k$ and
$x_{k+1}$ are not ordered.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Proposition 27 (`jis-2026-26.3.3-prop-27`). -/
public theorem_wanted hofCount_eq_witnesses {i k : ℕ} (hi : 3 ≤ i) (hik : i < k) :
    hofCount k (· = i) (i + (hofL k)^[2 * k + 2] 1) <
        hofCount (k + 1) (· = i) (i + (hofL k)^[2 * k + 2] 1) ∧
      hofCount (k + 1) (· = i) (i + (hofL (k + 1))^[k + i] 1) <
        hofCount k (· = i) (i + (hofL (k + 1))^[k + i] 1)

end

end MetaMathlibExt
