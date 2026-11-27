/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Topology.ArithmeticalSelfSimilarCompactSetDerived
public import MathlibExt.Topology.ArithmeticalSelfSimilarCompactSetLayerEnumTendsto

namespace MetaMathlibExt

@[expose] public section

open Ordinal Filter Topology
open scoped Pointwise

/-- **Order type of a self-similar compact set.** Let $K$ be a self-similar compact set of module
$\mu \ge 1$ and ratio $\rho$. Then there is a strictly decreasing map $\alpha \mapsto K[\alpha]$
from the ordinals $\alpha \le \omega^\omega$ onto $K$ (so $K$ has order type $\omega^\omega + 1$
under the reverse order) with $K[\omega^\omega] = 0$, $K[0] > 0$ and $K \subseteq [0, K[0]]$.

The hypothesis $\mu \ge 1$ is the paper's convention that $\mu$ is a natural number; for
$\mu = 0$ the set $\{0\}$ would satisfy the definition.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Proposition 1. -/
public theorem_wanted isSelfSimilarCompactSet_enumeration {K : Set ℝ} {μ : ℕ} {ρ : ℝ}
    (hμ : 0 < μ) (hK : IsSelfSimilarCompactSet K μ ρ) :
    ∃ f : Ordinal.{0} → ℝ, StrictAntiOn f (Set.Iic (ω ^ ω)) ∧ f '' Set.Iic (ω ^ ω) = K ∧
      f (ω ^ ω) = 0 ∧ 0 < f 0 ∧ K ⊆ Set.Icc 0 (f 0)

/-- **Decomposition of a self-similar compact set into layers.** Let $K$ be a self-similar
compact set of module $\mu$ and ratio $\rho$, and for $u \ge 0$ let
$T_u = K^{(u)} \setminus K^{(u+1)}$, where $K^{(u)}$ is the $u$-th derived set of $K$. Then

$$K = \{0\} \cup \bigcup_{n \ge 0} \bigcup_{0 \le u < \mu} \rho^{-n} T_u,$$

where $\rho^{-n} T_u = \{\rho^{-n} x : x \in T_u\}$.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Proposition 2, equation (2). -/
public theorem_wanted isSelfSimilarCompactSet_eq_union_layers {K : Set ℝ} {μ : ℕ} {ρ : ℝ}
    (hK : IsSelfSimilarCompactSet K μ ρ) :
    K = {0} ∪ ⋃ n : ℕ, ⋃ u ∈ Finset.range μ, (ρ ^ n)⁻¹ • selfSimilarLayer K u

/-- **Enumerating the isolated points of a self-similar compact set.** Let $K$ be a self-similar
compact set of module $\mu$ and ratio $\rho$, and let $T_0 = K \setminus K'$ be the set of
isolated points of $K$, where $K'$ is the derived set of $K$. Let $\alpha \mapsto K[\alpha]$ be a
strictly decreasing map from the ordinals $\alpha \le \omega^\omega$ onto $K$, and
$\alpha \mapsto T_0[\alpha]$ a strictly decreasing map from the ordinals $\alpha < \omega^\omega$
onto $T_0$. Then for every ordinal $\alpha < \omega^\omega$, $T_0[\alpha] = K[\alpha]$ if
$\alpha < \omega$, and $T_0[\alpha] = K[\alpha + 1]$ if $\omega \le \alpha$.

The paper writes $0 \le \alpha \le \omega^\omega$; the layer has order type $\omega^\omega$ (its
indices in $K$ are $0$ and the successor ordinals below $\omega^\omega$), so $T_0[\omega^\omega]$
is undefined and the range here is $\alpha < \omega^\omega$.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Proposition 3. -/
public theorem_wanted isSelfSimilarCompactSet_layer_zero_enum {K : Set ℝ} {μ : ℕ} {ρ : ℝ}
    (hK : IsSelfSimilarCompactSet K μ ρ) {f t : Ordinal.{0} → ℝ}
    (hf : StrictAntiOn f (Set.Iic (ω ^ ω))) (hfK : f '' Set.Iic (ω ^ ω) = K)
    (ht : StrictAntiOn t (Set.Iio (ω ^ ω))) (htK : t '' Set.Iio (ω ^ ω) = selfSimilarLayer K 0)
    {α : Ordinal.{0}} (hα : α < ω ^ ω) :
    (α < ω → t α = f α) ∧ (ω ≤ α → t α = f (α + 1))

/-- **Enumerating the higher layers of a self-similar compact set.** Let $K$ be a self-similar
compact set of module $\mu$ and ratio $\rho$, let $u \ge 1$, and let
$T_u = K^{(u)} \setminus K^{(u+1)}$, where $K^{(u)}$ is the $u$-th derived set of $K$. Let
$\alpha \mapsto K[\alpha]$ be a strictly decreasing map from the ordinals $\alpha \le \omega^\omega$
onto $K$, and $\alpha \mapsto T_u[\alpha]$ a strictly decreasing map from the ordinals
$\alpha < \omega^\omega$ onto $T_u$. Then $T_u[\alpha] = K[\omega^u (\alpha + 1)]$ (ordinal
arithmetic) for every ordinal $\alpha < \omega^\omega$.

The paper writes $0 \le \alpha \le \omega^\omega$; the layer has order type $\omega^\omega$, so the
range here is $\alpha < \omega^\omega$.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Proposition 3. -/
public theorem_wanted isSelfSimilarCompactSet_layer_enum {K : Set ℝ} {μ : ℕ} {ρ : ℝ}
    (hK : IsSelfSimilarCompactSet K μ ρ) {u : ℕ} (hu : 1 ≤ u) {f t : Ordinal.{0} → ℝ}
    (hf : StrictAntiOn f (Set.Iic (ω ^ ω))) (hfK : f '' Set.Iic (ω ^ ω) = K)
    (ht : StrictAntiOn t (Set.Iio (ω ^ ω))) (htK : t '' Set.Iio (ω ^ ω) = selfSimilarLayer K u)
    {α : Ordinal.{0}} (hα : α < ω ^ ω) :
    t α = f (ω ^ (u : Ordinal) * (α + 1))

/-- **Limits across the last layer of a self-similar compact set.** Let $K$ be a self-similar
compact set of module $\mu$ and ratio $\rho$, with layers $T_u = K^{(u)} \setminus K^{(u+1)}$
for $u \ge 0$, where $K^{(u)}$ is the $u$-th derived set of $K$. Suppose that for every $u$,
$\alpha \mapsto T_u[\alpha]$ is a strictly decreasing map from the ordinals $\alpha < \omega^\omega$
onto $T_u$. Then for every ordinal $\alpha < \omega^\omega$,
$T_{\mu-1}[\omega \alpha + n] \to T_0[\alpha] / \rho$ as $n \to \infty$ through the natural numbers
(ordinal arithmetic in the index).

These hypotheses force $\mu \ge 1$, so $\mu - 1$ is a genuine index.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Proposition 4. -/
public theorem_wanted isSelfSimilarCompactSet_layer_enum_tendsto_last {K : Set ℝ} {μ : ℕ}
    {ρ : ℝ} (hK : IsSelfSimilarCompactSet K μ ρ) {t : ℕ → Ordinal.{0} → ℝ}
    (ht : ∀ u, StrictAntiOn (t u) (Set.Iio (ω ^ ω)))
    (htK : ∀ u, t u '' Set.Iio (ω ^ ω) = selfSimilarLayer K u)
    {α : Ordinal.{0}} (hα : α < ω ^ ω) :
    Tendsto (fun n : ℕ => t (μ - 1) (ω * α + n)) atTop (𝓝 (t 0 α / ρ))

/-- **Multiplying by the ratio raises the gauge index by the module (Proposition 6).** Let
$K \subseteq \mathbb{R}$ be a quasi-arithmetical compact set of module $\mu$ and ratio $\rho$. For
each natural number $j$ let $K^{(j)}$ be the $j$-th iterated derived set of $K$ and
$T_j = K^{(j)} \setminus K^{(j+1)}$ its $j$-th layer. If $n, \ell, u, \ell', u'$ are natural
numbers with $n / \rho^\ell \in T_u$ and $\rho n / \rho^{\ell'} \in T_{u'}$, then
$\ell' \mu - u' = \ell \mu - u + \mu$ as integers.

The stability gauge of Definition 3 is $\lVert m \rVert_K = \ell \mu + d - u$ whenever
$m / \rho^\ell \in T_u$, with a displacement $d$ independent of $m$; so this is the identity
$\lVert \rho n \rVert_K = \lVert n \rVert_K + \mu$.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Proposition 6. -/
public theorem_wanted isQuasiArithmeticalCompactSet_gauge_ratio_mul {K : Set ℝ} {μ ρ : ℕ}
    (hK : IsQuasiArithmeticalCompactSet K μ ρ) {n ℓ u ℓ' u' : ℕ}
    (h : (n : ℝ) / (ρ : ℝ) ^ ℓ ∈ selfSimilarLayer K u)
    (h' : ((ρ * n : ℕ) : ℝ) / (ρ : ℝ) ^ ℓ' ∈ selfSimilarLayer K u') :
    (ℓ' * μ - u' : ℤ) = ℓ * μ - u + μ

/-- **Derived sets of an arithmetical compact set are arithmetical (Proposition 7).** Let $K$ be
an arithmetical compact set of module $\mu$ and ratio $\rho$. For every natural number $n$, the
$n$-th derived set $K^{(n)}$ of $K$ (the set of accumulation points, iterated $n$ times, so that
$K^{(0)} = K$) is an arithmetical compact set of module $\mu$ and ratio $\rho$.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Proposition 7. -/
public theorem_wanted isArithmeticalCompactSet_derivedSet_iterate {K : Set ℝ} {μ ρ : ℕ}
    (hK : IsArithmeticalCompactSet K μ ρ) (n : ℕ) :
    IsArithmeticalCompactSet (derivedSet^[n] K) μ ρ

/-- **The closure of $T_0$ is an arithmetical compact set (Theorem 2).** Let $T_0$ be the set of
reals $n / 3^k$, where $n$ and $k$ are natural numbers, $n$ is stable and
$\lVert n \rVert = 3k + 2$ (with $\lVert n \rVert$ the integer complexity of $n$), and let $K$ be
the closure of $T_0$ in $\mathbb{R}$. Then $K$ is an arithmetical compact set of module $3$ and
ratio $3$, and for every natural number $n \ge 1$ the stability gauge $\lVert n \rVert_K$ of $K$
with module $3$ and ratio $3$ equals the stable complexity $\lVert n \rVert_{\mathrm{st}}$.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Theorem 2. -/
public theorem_wanted isArithmeticalCompactSet_closure_complexityLayerZero :
    IsArithmeticalCompactSet (closure complexityLayerZero) 3 3 ∧
      ∀ n : ℕ, 0 < n → stabilityGauge (closure complexityLayerZero) 3 3 n = stableComplexity n

end

end MetaMathlibExt
