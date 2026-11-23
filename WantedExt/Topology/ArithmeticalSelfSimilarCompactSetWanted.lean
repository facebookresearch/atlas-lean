/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.SetTheory.Ordinal.Exponential
public import Mathlib.Topology.DerivedSet
public import Mathlib.Topology.Instances.Real.Lemmas
public import WantedExt.NumberTheory.IntegerComplexityWanted

namespace MetaMathlibExt

@[expose] public section

open Ordinal Filter Topology
open MathlibExt.NumberTheory.IntegerComplexityWanted (cx)
open scoped Pointwise

/-- **Self-similar compact set.** Let $\mu$ be a natural number and $\rho$ a real number. A set
$K \subseteq \mathbb{R}$ is a self-similar compact set of module $\mu$ and ratio $\rho$ when
$\rho > 1$, $K$ is nonempty and compact, $K \subseteq [0, \infty)$, $K$ is well ordered by the
reverse order $x \preceq y \iff x \ge y$ (every nonempty subset of $K$ has a largest element),
and $\rho K^{(\mu)} = K$, where $K^{(\mu)}$ is the $\mu$-th derived set of $K$ (the operation
$A \mapsto A'$ taking a set to its set of accumulation points, applied $\mu$ times) and
$\rho K^{(\mu)} = \{\rho x : x \in K^{(\mu)}\}$.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Definition 1. -/
public def IsSelfSimilarCompactSet (K : Set ℝ) (μ : ℕ) (ρ : ℝ) : Prop :=
  1 < ρ ∧ K.Nonempty ∧ IsCompact K ∧ K ⊆ Set.Ici 0 ∧ K.WellFoundedOn (· > ·) ∧
    ρ • derivedSet^[μ] K = K

/-- **Self-similarity equation.** If $K \subseteq \mathbb{R}$ is a self-similar compact set of
module $\mu$ and ratio $\rho$, then $\rho K^{(\mu)} = K$, where $K^{(\mu)}$ is the $\mu$-th derived
set of $K$ (the set of accumulation points, iterated $\mu$ times) and $\rho K^{(\mu)}$ is its
image under multiplication by $\rho$.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Definition 1, equation (1). -/
public theorem IsSelfSimilarCompactSet.smul_derivedSet_iterate {K : Set ℝ} {μ : ℕ} {ρ : ℝ}
    (hK : IsSelfSimilarCompactSet K μ ρ) : ρ • derivedSet^[μ] K = K :=
  hK.2.2.2.2.2

/-- **Layers of the iterated derived sets.** For a set $K \subseteq \mathbb{R}$ and a natural
number $u$, let $K^{(u)}$ be the $u$-th derived set of $K$ (the derived set, i.e. the set of
accumulation points, iterated $u$ times, with $K^{(0)} = K$). The layer of $K$ of index $u$ is
$T_u = K^{(u)} \setminus K^{(u+1)}$, the set of points of $K^{(u)}$ that are isolated in
$K^{(u)}$.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Proposition 2. -/
public def selfSimilarLayer (K : Set ℝ) (u : ℕ) : Set ℝ :=
  derivedSet^[u] K \ derivedSet^[u + 1] K

/-- **The zeroth layer is the set of isolated points.** For every set
$K \subseteq \mathbb{R}$, the layer $T_0$ of $K$ equals $K \setminus K'$, where $K'$ is the derived
set of $K$ (its set of accumulation points); that is, $T_0$ is the set of isolated points of $K$.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Proposition 2. -/
public theorem selfSimilarLayer_zero (K : Set ℝ) :
    selfSimilarLayer K 0 = K \ derivedSet K := rfl

/-- **Layers of the derived set.** For a set $A \subseteq \mathbb{R}$ and $u \ge 0$, write
$T_u(A) = A^{(u)} \setminus A^{(u+1)}$ for the $u$-th layer of $A$, where $A^{(u)}$ is the $u$-th
derived set of $A$. Then for every set $K \subseteq \mathbb{R}$ and every $u \ge 0$,
$T_{u+1}(K) = T_u(K')$, where $K'$ is the derived set of $K$.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, proof of Proposition 7. -/
public theorem selfSimilarLayer_succ (K : Set ℝ) (u : ℕ) :
    selfSimilarLayer K (u + 1) = selfSimilarLayer (derivedSet K) u := by
  simp only [selfSimilarLayer, Function.iterate_succ, Function.comp_apply]

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

/-- **Enumerating the derived sets of a self-similar compact set.** Let $K$ be a self-similar
compact set of module $\mu$ and ratio $\rho$, let $n \ge 1$, and write $K^{(n)}$ for the $n$-th
derived set of $K$. Let $\alpha \mapsto K[\alpha]$ and $\alpha \mapsto K^{(n)}[\alpha]$ be
strictly decreasing maps from the ordinals $\alpha \le \omega^\omega$ onto $K$ and onto
$K^{(n)}$, respectively. Then $K^{(n)}[\alpha] = K[\omega^n (1 + \alpha)]$ (ordinal
arithmetic) for every ordinal $\alpha \le \omega^\omega$.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Proposition 3. -/
public theorem_wanted isSelfSimilarCompactSet_derivedSet_enum {K : Set ℝ} {μ : ℕ} {ρ : ℝ}
    (hK : IsSelfSimilarCompactSet K μ ρ) {n : ℕ} (hn : 1 ≤ n) {f g : Ordinal.{0} → ℝ}
    (hf : StrictAntiOn f (Set.Iic (ω ^ ω))) (hfK : f '' Set.Iic (ω ^ ω) = K)
    (hg : StrictAntiOn g (Set.Iic (ω ^ ω))) (hgK : g '' Set.Iic (ω ^ ω) = derivedSet^[n] K)
    {α : Ordinal.{0}} (hα : α ≤ ω ^ ω) :
    g α = f (ω ^ (n : Ordinal) * (1 + α))

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

/-- **Limits between consecutive layers of a self-similar compact set.** Let $K$ be a
self-similar compact set of module $\mu$ and ratio $\rho$, with layers
$T_u = K^{(u)} \setminus K^{(u+1)}$ for $u \ge 0$, where $K^{(u)}$ is the $u$-th derived set of
$K$. Suppose that for every $u$, $\alpha \mapsto T_u[\alpha]$ is a strictly decreasing map from
the ordinals $\alpha < \omega^\omega$ onto $T_u$. Then for every $u \ge 0$ and every ordinal
$\alpha < \omega^\omega$, $T_u[\omega \alpha + n] \to T_{u+1}[\alpha]$ as $n \to \infty$ through
the natural numbers (ordinal arithmetic in the index).

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Proposition 4. -/
public theorem_wanted isSelfSimilarCompactSet_layer_enum_tendsto {K : Set ℝ} {μ : ℕ} {ρ : ℝ}
    (hK : IsSelfSimilarCompactSet K μ ρ) {t : ℕ → Ordinal.{0} → ℝ}
    (ht : ∀ u, StrictAntiOn (t u) (Set.Iio (ω ^ ω)))
    (htK : ∀ u, t u '' Set.Iio (ω ^ ω) = selfSimilarLayer K u)
    (u : ℕ) {α : Ordinal.{0}} (hα : α < ω ^ ω) :
    Tendsto (fun n : ℕ => t u (ω * α + n)) atTop (𝓝 (t (u + 1) α))

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

/-- **Quasi-arithmetical compact sets.** Let $K \subseteq \mathbb{R}$ and let $\mu$ and $\rho$ be
natural numbers. Then $K$ is a quasi-arithmetical compact set of module $\mu$ and ratio $\rho$
when $\rho \ge 2$, $K$ is a self-similar compact set of module $\mu$ and ratio $\rho$, and there
is a function $\kappa : \mathbb{N} \to \mathbb{N}$ such that
$K \setminus \{0\} = \{n / \rho^k : n, k \in \mathbb{N},\ \rho \nmid n,\ k \ge \kappa(n)\}$.

The paper's $\kappa$ is defined only on $\mathbb{N} \setminus \rho\mathbb{N}$; here its values at
multiples of $\rho$ are irrelevant.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Definition 2. -/
public def IsQuasiArithmeticalCompactSet (K : Set ℝ) (μ ρ : ℕ) : Prop :=
  2 ≤ ρ ∧ IsSelfSimilarCompactSet K μ ρ ∧
    ∃ κ : ℕ → ℕ, K \ {0} = {x | ∃ n k : ℕ, ¬ ρ ∣ n ∧ κ n ≤ k ∧ x = n / (ρ : ℝ) ^ k}

/-- **Quasi-arithmetical compact sets are self-similar.** If $K$ is a quasi-arithmetical compact
set of module $\mu$ and natural-number ratio $\rho$, then $K$ is a self-similar compact set of
module $\mu$ and ratio $\rho$.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Definition 2. -/
public theorem IsQuasiArithmeticalCompactSet.isSelfSimilarCompactSet {K : Set ℝ} {μ ρ : ℕ}
    (hK : IsQuasiArithmeticalCompactSet K μ ρ) : IsSelfSimilarCompactSet K μ ρ :=
  hK.2.1

/-- **The layer index of a quasi-arithmetical compact set is well defined (Proposition 5).** Let
$K \subseteq \mathbb{R}$ be a quasi-arithmetical compact set of module $\mu$ and ratio $\rho$. For
each natural number $j$ let $K^{(j)}$ be the $j$-th iterated derived set of $K$ and
$T_j = K^{(j)} \setminus K^{(j+1)}$ its $j$-th layer. If $n, p, q, v, w$ are natural numbers with
$n / \rho^p \in T_v$ and $n / \rho^q \in T_w$, then $p \mu - v = q \mu - w$ as integers.

The paper takes $n$ positive; $n = 0$ is allowed here, and then the claim is vacuous because $0$
lies in no layer.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Proposition 5. -/
public theorem_wanted isQuasiArithmeticalCompactSet_layer_index {K : Set ℝ} {μ ρ : ℕ}
    (hK : IsQuasiArithmeticalCompactSet K μ ρ) {n p q v w : ℕ}
    (hv : (n : ℝ) / (ρ : ℝ) ^ p ∈ selfSimilarLayer K v)
    (hw : (n : ℝ) / (ρ : ℝ) ^ q ∈ selfSimilarLayer K w) :
    (p * μ - v : ℤ) = q * μ - w

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

/-- **Un-normalized stability gauge.** Let $K \subseteq \mathbb{R}$, let $\mu$, $\rho$ and $n$ be
natural numbers, and let $T_u$ denote the layer of $K$ of index $u$. Let $\ell$ be the least
natural number such that $n / \rho^\ell$ lies in some layer $T_u$ (division by $0$ gives $0$), and
let $u$ be the least index with $n / \rho^\ell \in T_u$. The un-normalized stability gauge of $n$
is the integer $\ell \mu - u$. If $n / \rho^\ell$ lies in no layer for any $\ell$, its value is $0$.

When $K$ is a quasi-arithmetical compact set of module $\mu$ and ratio $\rho$, Proposition 5 of the
source says that $\ell \mu - u$ is the same for every $\ell$ and $u$ with $n / \rho^\ell \in T_u$;
taking the least $\ell$ only fixes a choice.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Definition 3. -/
public noncomputable def stabilityGaugeIndex (K : Set ℝ) (μ ρ : ℕ) (n : ℕ) : ℤ :=
  let ℓ : ℕ := sInf {ℓ : ℕ | ∃ u, (n : ℝ) / (ρ : ℝ) ^ ℓ ∈ selfSimilarLayer K u}
  ((ℓ * μ : ℕ) : ℤ) - (sInf {u : ℕ | (n : ℝ) / (ρ : ℝ) ^ ℓ ∈ selfSimilarLayer K u} : ℕ)

/-- **Stability gauge.** Let $K \subseteq \mathbb{R}$, let $\mu$ and $\rho$ be natural numbers, and
for a natural number $n$ let $g(n)$ be the un-normalized stability gauge of $n$ for $K$, $\mu$
and $\rho$: the integer $\ell \mu - u$, where $\ell$ is least such that $n / \rho^\ell$ lies in
some layer $T_u$ of $K$ and $u$ is the least such index (and $g(n) = 0$ if there is no such
$\ell$). The stability gauge of $n$ is the integer $\lVert n \rVert_K = g(n) - g(1)$. When such
an $\ell$ exists, this is $\ell \mu + d - u$ with the displacement $d = -g(1)$, chosen so that
$\lVert 1 \rVert_K = 0$.

The source defines the gauge only for quasi-arithmetical compact sets of module $\mu$ and ratio
$\rho$; this definition applies to every set $K$.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Definition 3. -/
public noncomputable def stabilityGauge (K : Set ℝ) (μ ρ : ℕ) (n : ℕ) : ℤ :=
  stabilityGaugeIndex K μ ρ n - stabilityGaugeIndex K μ ρ 1

/-- **The stability gauge vanishes at one.** For every set $K \subseteq \mathbb{R}$ and all
natural numbers $\mu$ and $\rho$, the stability gauge $n \mapsto \lVert n \rVert_K$ of $K$ with
module $\mu$ and ratio $\rho$ takes the value $0$ at $n = 1$, that is, $\lVert 1 \rVert_K = 0$.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Definition 3. -/
public theorem stabilityGauge_one (K : Set ℝ) (μ ρ : ℕ) : stabilityGauge K μ ρ 1 = 0 :=
  sub_self _

/-- **Arithmetical compact sets.** Let $K \subseteq \mathbb{R}$ and let $\mu$ and $\rho$ be natural
numbers. For each natural number $j$ let $K^{(j)}$ be the $j$-th iterated derived set (the set of
accumulation points, iterated $j$ times) of $K$ and $T_j = K^{(j)} \setminus K^{(j+1)}$ its $j$-th
layer, and for a natural number $m$ let $\lVert m \rVert_K$ be the stability gauge of $K$ with
module $\mu$ and ratio $\rho$ at $m$. Then $K$ is an arithmetical compact set of module $\mu$ and
ratio $\rho$ when $K$ is a quasi-arithmetical compact set of module $\mu$ and ratio $\rho$ and the
following holds for every family of maps $\alpha \mapsto T_j[\alpha]$ ($j \in \mathbb{N}$), each
strictly decreasing on the ordinals $\alpha < \omega^\omega$ and mapping them onto $T_j$: for every
$j \in \mathbb{N}$, every ordinal $\alpha < \omega^\omega$ and all natural numbers $n$ and $k$ with
$\rho \nmid n$ and $T_{j+1}[\alpha] = n / \rho^k$, the sets
$\{T_j[\omega \alpha + r] : r \in \mathbb{N}\}$ and
$\{b (a \rho^r + 1) / \rho^{r+k} : a, b, r \in \mathbb{N},\ n = ab,\
\lVert n \rVert_K = \lVert a \rVert_K + \lVert b \rVert_K\}$ have finite symmetric difference.

Such an enumeration of a layer is unique when it exists; by Proposition 3 each layer has order
type $\omega^\omega$.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Definition 4, displays (4) and (5). -/
public def IsArithmeticalCompactSet (K : Set ℝ) (μ ρ : ℕ) : Prop :=
  IsQuasiArithmeticalCompactSet K μ ρ ∧
    ∀ t : ℕ → Ordinal.{0} → ℝ, (∀ u, StrictAntiOn (t u) (Set.Iio (ω ^ ω))) →
      (∀ u, t u '' Set.Iio (ω ^ ω) = selfSimilarLayer K u) →
      ∀ (u : ℕ) (α : Ordinal.{0}), α < ω ^ ω → ∀ n k : ℕ, ¬ ρ ∣ n →
        t (u + 1) α = (n : ℝ) / (ρ : ℝ) ^ k →
        (symmDiff (Set.range fun r : ℕ => t u (ω * α + r))
          {x : ℝ | ∃ a b r : ℕ, n = a * b ∧
            stabilityGauge K μ ρ n = stabilityGauge K μ ρ a + stabilityGauge K μ ρ b ∧
            x = b * (a * (ρ : ℝ) ^ r + 1) / (ρ : ℝ) ^ (r + k)}).Finite

/-- **Arithmetical compact sets are quasi-arithmetical.** If $K \subseteq \mathbb{R}$ is an
arithmetical compact set of module $\mu$ and ratio $\rho$, then $K$ is a quasi-arithmetical
compact set of module $\mu$ and ratio $\rho$.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Definition 4. -/
public theorem IsArithmeticalCompactSet.isQuasiArithmeticalCompactSet {K : Set ℝ}
    {μ ρ : ℕ} (hK : IsArithmeticalCompactSet K μ ρ) : IsQuasiArithmeticalCompactSet K μ ρ :=
  hK.1

/-- **Derived sets of an arithmetical compact set are arithmetical (Proposition 7).** Let $K$ be
an arithmetical compact set of module $\mu$ and ratio $\rho$. For every natural number $n$, the
$n$-th derived set $K^{(n)}$ of $K$ (the set of accumulation points, iterated $n$ times, so that
$K^{(0)} = K$) is an arithmetical compact set of module $\mu$ and ratio $\rho$.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Proposition 7. -/
public theorem_wanted isArithmeticalCompactSet_derivedSet_iterate {K : Set ℝ} {μ ρ : ℕ}
    (hK : IsArithmeticalCompactSet K μ ρ) (n : ℕ) :
    IsArithmeticalCompactSet (derivedSet^[n] K) μ ρ

/-- **Stable numbers for integer complexity.** A natural number $n$ is stable when $n > 0$ and
$\lVert 3^k n \rVert = \lVert n \rVert + 3k$ for every natural number $k$, where $\lVert m \rVert$
is the integer complexity of $m$.

The paper quantifies over $k \ge 1$; the case $k = 0$ holds trivially.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Section 1. -/
public def IsComplexityStable (n : ℕ) : Prop :=
  0 < n ∧ ∀ k : ℕ, cx (3 ^ k * n) = cx n + 3 * k

/-- **Stable complexity.** For a natural number $n$, let $\lVert m \rVert$ denote the integer
complexity of a positive integer $m$, with $\lVert 0 \rVert = 0$, and let $a$ be the least natural
number such that $3^a n$ is stable, with $a = 0$ if there is none. The stable complexity of $n$
is the integer $\lVert n \rVert_{\mathrm{st}} = \lVert 3^a n \rVert - 3a$.

Altman and Zelinsky show that such an $a$ exists for $n \ge 1$, and any larger $a$ gives the
same value. For $n = 0$ there is none, so $\lVert 0 \rVert_{\mathrm{st}} = \lVert 0 \rVert = 0$.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Section 1. -/
public noncomputable def stableComplexity (n : ℕ) : ℤ :=
  (cx (3 ^ sInf {a : ℕ | IsComplexityStable (3 ^ a * n)} * n) : ℤ) -
    3 * (sInf {a : ℕ | IsComplexityStable (3 ^ a * n)} : ℕ)

/-- **Stable complexity of a stable number.** If $n$ is a stable natural number, then its
stable complexity equals its integer complexity: $\lVert n \rVert_{\mathrm{st}} = \lVert n \rVert$.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Section 1. -/
public theorem stableComplexity_of_isComplexityStable {n : ℕ} (h : IsComplexityStable n) :
    stableComplexity n = cx n := by
  have h0 : sInf {a : ℕ | IsComplexityStable (3 ^ a * n)} = 0 :=
    Nat.sInf_eq_zero.mpr (Or.inl (by simpa using h))
  simp [stableComplexity, h0]

/-- **The set $T_0$ built from stable numbers.** Write $\lVert n \rVert$ for the integer complexity
of a natural number $n$, and call $n$ stable when $n > 0$ and
$\lVert 3^k n \rVert = \lVert n \rVert + 3k$ for every natural number $k$. The set
$T_0 \subseteq \mathbb{R}$ consists of the reals $n / 3^k$, where $n$ and $k$ are natural numbers,
$n$ is stable and $\lVert n \rVert = 3k + 2$.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Section 3, equation (7). -/
public def complexityLayerZero : Set ℝ :=
  {x | ∃ n k : ℕ, IsComplexityStable n ∧ cx n = 3 * k + 2 ∧ x = n / (3 : ℝ) ^ k}

/-- **The set $T_0$ is nonnegative.** Every element of the set $T_0$ of reals $n / 3^k$, where
$n$ and $k$ are natural numbers, $n$ is stable and $\lVert n \rVert = 3k + 2$ (with
$\lVert n \rVert$ the integer complexity of $n$), is a nonnegative real number.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Section 3, equation (7). -/
public theorem complexityLayerZero_subset_Ici : complexityLayerZero ⊆ Set.Ici 0 := by
  rintro x ⟨n, k, -, -, rfl⟩
  exact Set.mem_Ici.mpr (by positivity)

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
