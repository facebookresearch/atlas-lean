/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.CyclotomicTraceMetric
public import MathlibExt.NumberTheory.SymmetricPowerSums
public import MathlibExt.NumberTheory.CyclotomicTraceMetricCyclotomicDistMomentTwo
public import MathlibExt.NumberTheory.CyclotomicTraceMetricEventuallyAdjoinAddNsmulEq
public import MathlibExt.NumberTheory.CyclotomicTraceMetricAdjoinLeAdjoinOfCyclotomicTraceDistLt
public import MathlibExt.NumberTheory.CyclotomicTraceMetricCyclotomicBoxDiam

/-!
# A trace metric on the `p`-th cyclotomic field

Statements from Katerina Saettone, Alexandru Zaharescu and Zhuo Zhang, *On a Special
Metric in Cyclotomic Fields*, INTEGERS 25 (2025), Article A10 (arXiv:2410.22687).

For `K = ℚ(ω)` with `ω` a primitive `p`-th root of unity, `α ∈ K` is sent to the vector
`(Tr_{K/ℚ}(α ω^j))_{1 ≤ j ≤ p-1} ∈ ℚ^{p-1}`; `‖α‖` is its Euclidean length and
`d(α, β) = ‖α - β‖`. The field is any `K` with `IsCyclotomicExtension {p} ℚ K` (for
example `CyclotomicField p ℚ`), and `ω = IsCyclotomicExtension.zeta p ℚ K`.
The box `B(p, N)` consists of the points `a₁ ω + ⋯ + a_{p-1} ω^{p-1}` with integer
`aᵢ ∈ [-N, N]`; it is indexed by its coefficient vectors, which is faithful since
`ω, …, ω^{p-1}` is a `ℚ`-basis of `K`.

The paper fixes `p` an odd prime throughout; statements that also hold for `p = 2`
assume only that `p` is prime.
-/

namespace MetaMathlibExt

@[expose] public section

open IsCyclotomicExtension

variable {p : ℕ} [NeZero p] {K : Type*} [Field K] [CharZero K] [IsCyclotomicExtension {p} ℚ K]

/-- **Fourth-power sum of coordinate differences over a box.** Let $p$ be a prime and $N$ a
natural number, and let $B(p, N)$ be the set of integer vectors $a = (a_1, \dots, a_{p-1})$
with $|a_i| \le N$ for all $i$. Then
$$\sum_{i=1}^{p-1} \sum_{j=1}^{p-1} \sum_{a, b \in B(p, N)} (a_i - b_i)^2 (a_j - b_j)^2 =
(2N+1)^{2(p-1)} \cdot \tfrac{2}{45} N (N+1) (p-1) (10N^2 p + 4N^2 + 10Np + 4N - 3).$$

This corrects the paper's printed right side, which omits the factor $(2N+1)^{2(p-1)}$: for
$p = 3$ and $N = 1$ the sum is $936$, while the printed right side is $104/9$. The paper's own
proof carries the factors $(2N+1)^{2p-4}$ and $(2N+1)^{2p-6}$ in its pieces (10) and (11), and
combining them gives the value above; the printed formula is the sum divided by
$|B(p, N)|^2 = (2N+1)^{2(p-1)}$. The paper takes $p$ an odd prime; here only $p$ prime is
assumed.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Lemma 5 (`integers-2025-A10-lem-5`). -/
public theorem_wanted sum_sq_sub_mul_sq_sub_box (p : ℕ) (hp : p.Prime) (N : ℕ) :
    ∑ i : Fin (p - 1), ∑ j : Fin (p - 1),
      ∑ a ∈ Fintype.piFinset (fun _ : Fin (p - 1) => Finset.Icc (-(N : ℤ)) N),
        ∑ b ∈ Fintype.piFinset (fun _ : Fin (p - 1) => Finset.Icc (-(N : ℤ)) N),
          (((a i - b i) ^ 2 * (a j - b j) ^ 2 : ℤ) : ℚ) =
      (2 * N + 1) ^ (2 * (p - 1)) * (2 / 45 * N * (N + 1) * ((p : ℚ) - 1) *
        (10 * N ^ 2 * p + 4 * N ^ 2 + 10 * N * p + 4 * N - 3))

/-- **Fourth moment of the trace distance on the cyclotomic box.** Let $p$ be a prime, let $N$ be
a natural number, and let $K$ be a field generated over $\mathbb{Q}$ by a primitive $p$-th root of
unity, with fixed primitive $p$-th root of unity $\omega \in K$. Let $M_4(p, N)$ be the fourth
moment of the trace metric $d$ of $K$ over the box $B(p, N)$: the average of
$d(\alpha_a, \alpha_b)^4$ over all pairs $(a, b)$ of integer vectors in $\mathbb{Z}^{p-1}$ whose
coordinates lie in $[-N, N]$, where $\alpha_a = a_1 \omega + \dots + a_{p-1} \omega^{p-1}$ and
$d(\alpha, \beta)^2 = \sum_{j=1}^{p-1} \mathrm{Tr}_{K/\mathbb{Q}}((\alpha - \beta) \omega^j)^2$.
Then
$$
M_4(p, N) = \frac{2}{45} N (N + 1) (p - 1) \bigl( (2 N^2 + 2 N)
(5 p^5 - 8 p^4 + p^3 + 8 p^2 - 21 p - 18) - 3 (p^2 - p - 1)^2 \bigr).
$$

The asymptotic form $M_4(p, N) = \frac{4}{9} p^6 N^4 + O(p^5 N^4 + p^6 N^3)$ follows from this
exact formula.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Lemma 6 (`integers-2025-A10-lem-6`). -/
public theorem_wanted cyclotomicDistMoment_four (hp : p.Prime) (N : ℕ) :
    cyclotomicDistMoment p K N 4 = 2 / 45 * N * (N + 1) * (p - 1) *
      ((2 * (N : ℝ) ^ 2 + 2 * N) * (5 * p ^ 5 - 8 * p ^ 4 + p ^ 3 + 8 * p ^ 2 - 21 * p - 18) -
        3 * ((p : ℝ) ^ 2 - p - 1) ^ 2)

/-- **Variance bound for squared trace distances in the box.** There is a real number $C$
such that the following holds for every prime $p$, every integer $N \ge 1$ and every $p$-th
cyclotomic extension $K$ of $\mathbb{Q}$. Let $\omega$ be the chosen primitive $p$-th root of
unity in $K$, let $d$ be the trace distance on $K$, and let $B(p, N)$ be the set of integer
vectors $a = (a_1, \dots, a_{p-1})$ with $|a_i| \le N$ for all $i$, where $a$ stands for the
point $a_1 \omega + \dots + a_{p-1} \omega^{p-1}$ of $K$. Then
$$R(p, N) = \frac{1}{|B(p, N)|^2} \sum_{\alpha, \beta \in B(p, N)}
\left( d(\alpha, \beta)^2 - \tfrac{2}{3} p^3 N^2 \right)^2 \le
C \left( p^5 N^4 + p^6 N^3 \right).$$

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Lemma 7 (`integers-2025-A10-lem-7`). -/
public theorem_wanted exists_cyclotomicDist_variance_le :
    ∃ C : ℝ, ∀ p N : ℕ, ∀ (_ : NeZero p) (K : Type) [Field K] [CharZero K]
      [IsCyclotomicExtension {p} ℚ K], p.Prime → 1 ≤ N →
      (∑ a ∈ cyclotomicBox p N, ∑ b ∈ cyclotomicBox p N,
          (cyclotomicTraceDist p (cyclotomicLatticePoint K a) (cyclotomicLatticePoint K b) ^ 2 -
            2 / 3 * (p : ℝ) ^ 3 * N ^ 2) ^ 2) / ((cyclotomicBox p N).card : ℝ) ^ 2 ≤
        C * ((p : ℝ) ^ 5 * N ^ 4 + (p : ℝ) ^ 6 * N ^ 3)

/-- **Almost all pairs in the cyclotomic box are nearly equidistant.** For every real
$\varepsilon > 0$ there is a natural number $A$ with the following property. Let $p$ be a prime
and $N$ a natural number with $p > A$ and $N > A$, and let $K$ be a field generated over
$\mathbb{Q}$ by a primitive $p$-th root of unity, with fixed primitive $p$-th root of unity
$\omega \in K$. Let $d(\alpha, \beta) = \lVert \alpha - \beta \rVert$ be the trace metric on $K$,
where $\lVert \gamma \rVert \ge 0$ and
$\lVert \gamma \rVert^2 = \sum_{j=1}^{p-1} \operatorname{Tr}_{K/\mathbb{Q}}(\gamma \omega^j)^2$.
Let $B(p, N)$ be the set of integer vectors $a = (a_1, \dots, a_{p-1})$ with $-N \le a_i \le N$
for all $i$, and write $\alpha_a = a_1 \omega + \dots + a_{p-1} \omega^{p-1}$. Then fewer than
$\varepsilon \lvert B(p, N) \rvert^2$ pairs $(a, b) \in B(p, N)^2$ satisfy
$$
\left| \frac{d(\alpha_a, \alpha_b)}{2 N p \sqrt{p - 1}} - \frac{1}{\sqrt{6}} \right| > \varepsilon.
$$

The constant $A$ depends only on $\varepsilon$; it is not claimed to be effectively computable.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Theorem 1 (`integers-2025-A10-thm-1`). -/
public theorem_wanted cyclotomicBox_almost_equidistant :
    ∀ ε > (0 : ℝ), ∃ A : ℕ, ∀ p N : ℕ, ∀ (_ : NeZero p) (K : Type) [Field K] [CharZero K]
      [IsCyclotomicExtension {p} ℚ K], p.Prime → A < p → A < N →
      ((((cyclotomicBox p N ×ˢ cyclotomicBox p N).filter fun ab =>
          ε < |cyclotomicTraceDist p (cyclotomicLatticePoint K ab.1)
              (cyclotomicLatticePoint K ab.2) /
            (2 * N * p * √(p - 1 : ℝ)) - 1 / √6|).card : ℝ)) <
        ε * ((cyclotomicBox p N).card : ℝ) ^ 2

/-- **Concentration of trace distances in the box, quantitative form.** There is a real
number $C$ such that the following holds for every real $\varepsilon > 0$, every prime $p$,
every integer $N \ge 1$ and every $p$-th cyclotomic extension $K$ of $\mathbb{Q}$. Let $\omega$
be the chosen primitive $p$-th root of unity in $K$, let $d$ be the trace distance on $K$, and
let $B(p, N)$ be the set of integer vectors $a = (a_1, \dots, a_{p-1})$ with $|a_i| \le N$ for
all $i$, where $a$ stands for the point $a_1 \omega + \dots + a_{p-1} \omega^{p-1}$ of $K$.
Among all pairs $(\alpha, \beta) \in B(p, N)^2$, the proportion of pairs with
$$\left| \frac{d(\alpha, \beta)}{2 N p^{3/2}} - \frac{1}{\sqrt{6}} \right| > \varepsilon$$
is at most $C \varepsilon^{-2} (1/p + 1/N)$.

The paper takes $p$ odd; here $p = 2$ is allowed. The paper also shows that $C$ is
effectively computable; only its existence is stated here.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Theorem 5 (`integers-2025-A10-thm-5`). -/
public theorem_wanted exists_cyclotomicBox_deviation_le :
    ∃ C : ℝ, ∀ ε > (0 : ℝ), ∀ p N : ℕ, ∀ (_ : NeZero p) (K : Type) [Field K] [CharZero K]
      [IsCyclotomicExtension {p} ℚ K], p.Prime → 1 ≤ N →
      ((((cyclotomicBox p N ×ˢ cyclotomicBox p N).filter fun ab =>
          ε < |cyclotomicTraceDist p (cyclotomicLatticePoint K ab.1)
              (cyclotomicLatticePoint K ab.2) /
            (2 * N * (p * √(p : ℝ))) - 1 / √6|).card : ℝ)) /
        ((cyclotomicBox p N).card : ℝ) ^ 2 ≤ C / ε ^ 2 * (1 / p + 1 / N)

end

end MetaMathlibExt
