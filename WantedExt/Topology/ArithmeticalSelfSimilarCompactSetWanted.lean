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

/-- A self-similar compact set of module `μ` and ratio `ρ`: a nonempty compact set
`K ⊆ [0, ∞)` that is well ordered by the reverse order `x ≼ y ↔ x ≥ y` (every
nonempty subset has a largest element) and satisfies `ρ K^{(μ)} = K`, where
`K^{(μ)}` is the `μ`-th derived set (Mathlib's `derivedSet`, the set of accumulation
points, iterated `μ` times).

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Definition 1. -/
public def IsSelfSimilarCompactSet (K : Set ℝ) (μ : ℕ) (ρ : ℝ) : Prop :=
  1 < ρ ∧ K.Nonempty ∧ IsCompact K ∧ K ⊆ Set.Ici 0 ∧ K.WellFoundedOn (· > ·) ∧
    ρ • derivedSet^[μ] K = K

/-- Characteristic lemma: a self-similar compact set satisfies its defining equation
`ρ K^{(μ)} = K`.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Definition 1, equation (1). -/
public theorem IsSelfSimilarCompactSet.smul_derivedSet_iterate {K : Set ℝ} {μ : ℕ} {ρ : ℝ}
    (hK : IsSelfSimilarCompactSet K μ ρ) : ρ • derivedSet^[μ] K = K :=
  hK.2.2.2.2.2

/-- The layer `T_u := K^{(u)} \ K^{(u+1)}` of a set `K ⊆ ℝ`: the points of the `u`-th
derived set that are isolated in it.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Proposition 2. -/
public def selfSimilarLayer (K : Set ℝ) (u : ℕ) : Set ℝ :=
  derivedSet^[u] K \ derivedSet^[u + 1] K

/-- Characteristic value: the layer `T_0` is `K \ K'`, the isolated points of `K`.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Proposition 2. -/
public theorem selfSimilarLayer_zero (K : Set ℝ) :
    selfSimilarLayer K 0 = K \ derivedSet K := rfl

/-- Recurrence: the layer `T_{u+1}` of `K` is the layer `T_u` of the derived set `K'`.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, proof of Proposition 7. -/
public theorem selfSimilarLayer_succ (K : Set ℝ) (u : ℕ) :
    selfSimilarLayer K (u + 1) = selfSimilarLayer (derivedSet K) u := by
  simp only [selfSimilarLayer, Function.iterate_succ, Function.comp_apply]

/-- Proposition 1 together with the order-type claim of its proof: a self-similar
compact set of positive module has order type `ω^ω + 1` under the reverse order,
i.e. it is the image of `[0, ω^ω]` under a strictly decreasing enumeration
`α ↦ K[α]`, and `K[ω^ω] = 0`, `K[0] > 0`, `K ⊆ [0, K[0]]`. The hypothesis `0 < μ`
is the paper's convention that `μ` is a natural number (for `μ = 0` the set `{0}`
satisfies Definition 1).

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Proposition 1. -/
public theorem_wanted isSelfSimilarCompactSet_enumeration {K : Set ℝ} {μ : ℕ} {ρ : ℝ}
    (hμ : 0 < μ) (hK : IsSelfSimilarCompactSet K μ ρ) :
    ∃ f : Ordinal.{0} → ℝ, StrictAntiOn f (Set.Iic (ω ^ ω)) ∧ f '' Set.Iic (ω ^ ω) = K ∧
      f (ω ^ ω) = 0 ∧ 0 < f 0 ∧ K ⊆ Set.Icc 0 (f 0)

/-- Proposition 2: a self-similar compact set of module `μ` and ratio `ρ` is
`K = {0} ∪ ⋃_{n ≥ 0} (T_0 ∪ ⋯ ∪ T_{μ-1}) / ρ^n`.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Proposition 2, equation (2). -/
public theorem_wanted isSelfSimilarCompactSet_eq_union_layers {K : Set ℝ} {μ : ℕ} {ρ : ℝ}
    (hK : IsSelfSimilarCompactSet K μ ρ) :
    K = {0} ∪ ⋃ n : ℕ, ⋃ u ∈ Finset.range μ, (ρ ^ n)⁻¹ • selfSimilarLayer K u

/-- Proposition 3, first formula: if `α ↦ K[α]` and `α ↦ K^{(n)}[α]` are the strictly
decreasing enumerations of `K` and of its `n`-th derived set by `[0, ω^ω]`, then
`K^{(n)}[α] = K[ω^n (1 + α)]` for `n ≥ 1` and `0 ≤ α ≤ ω^ω`.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Proposition 3. -/
public theorem_wanted isSelfSimilarCompactSet_derivedSet_enum {K : Set ℝ} {μ : ℕ} {ρ : ℝ}
    (hK : IsSelfSimilarCompactSet K μ ρ) {n : ℕ} (hn : 1 ≤ n) {f g : Ordinal.{0} → ℝ}
    (hf : StrictAntiOn f (Set.Iic (ω ^ ω))) (hfK : f '' Set.Iic (ω ^ ω) = K)
    (hg : StrictAntiOn g (Set.Iic (ω ^ ω))) (hgK : g '' Set.Iic (ω ^ ω) = derivedSet^[n] K)
    {α : Ordinal.{0}} (hα : α ≤ ω ^ ω) :
    g α = f (ω ^ (n : Ordinal) * (1 + α))

/-- Proposition 3, second formula: if `α ↦ T_0[α]` is the strictly decreasing
enumeration of the layer `T_0` by `[0, ω^ω)`, then `T_0[α] = K[α]` for `α < ω` and
`T_0[α] = K[α + 1]` for `ω ≤ α`. The paper writes `0 ≤ α ≤ ω^ω`; the layer has order
type `ω^ω` (its indices in `K` are `0` and the successor ordinals below `ω^ω`), so
`T_0[ω^ω]` is undefined and the range here is `α < ω^ω`.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Proposition 3. -/
public theorem_wanted isSelfSimilarCompactSet_layer_zero_enum {K : Set ℝ} {μ : ℕ} {ρ : ℝ}
    (hK : IsSelfSimilarCompactSet K μ ρ) {f t : Ordinal.{0} → ℝ}
    (hf : StrictAntiOn f (Set.Iic (ω ^ ω))) (hfK : f '' Set.Iic (ω ^ ω) = K)
    (ht : StrictAntiOn t (Set.Iio (ω ^ ω))) (htK : t '' Set.Iio (ω ^ ω) = selfSimilarLayer K 0)
    {α : Ordinal.{0}} (hα : α < ω ^ ω) :
    (α < ω → t α = f α) ∧ (ω ≤ α → t α = f (α + 1))

/-- Proposition 3, third formula: for `u ≥ 1`, if `α ↦ T_u[α]` is the strictly
decreasing enumeration of the layer `T_u` by `[0, ω^ω)`, then
`T_u[α] = K[ω^u (α + 1)]`. The paper writes `0 ≤ α ≤ ω^ω`; the layer has order type
`ω^ω`, so the range here is `α < ω^ω`.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Proposition 3. -/
public theorem_wanted isSelfSimilarCompactSet_layer_enum {K : Set ℝ} {μ : ℕ} {ρ : ℝ}
    (hK : IsSelfSimilarCompactSet K μ ρ) {u : ℕ} (hu : 1 ≤ u) {f t : Ordinal.{0} → ℝ}
    (hf : StrictAntiOn f (Set.Iic (ω ^ ω))) (hfK : f '' Set.Iic (ω ^ ω) = K)
    (ht : StrictAntiOn t (Set.Iio (ω ^ ω))) (htK : t '' Set.Iio (ω ^ ω) = selfSimilarLayer K u)
    {α : Ordinal.{0}} (hα : α < ω ^ ω) :
    t α = f (ω ^ (u : Ordinal) * (α + 1))

/-- Proposition 4, first part: if `T_u[·]` denotes the strictly decreasing enumeration
of the layer `T_u` by `[0, ω^ω)` (for every `u`), then
`lim_{n → ∞} T_u[ω α + n] = T_{u+1}[α]` for every ordinal `α < ω^ω` and `u ≥ 0`.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Proposition 4. -/
public theorem_wanted isSelfSimilarCompactSet_layer_enum_tendsto {K : Set ℝ} {μ : ℕ} {ρ : ℝ}
    (hK : IsSelfSimilarCompactSet K μ ρ) {t : ℕ → Ordinal.{0} → ℝ}
    (ht : ∀ u, StrictAntiOn (t u) (Set.Iio (ω ^ ω)))
    (htK : ∀ u, t u '' Set.Iio (ω ^ ω) = selfSimilarLayer K u)
    (u : ℕ) {α : Ordinal.{0}} (hα : α < ω ^ ω) :
    Tendsto (fun n : ℕ => t u (ω * α + n)) atTop (𝓝 (t (u + 1) α))

/-- Proposition 4, second part: with the enumerations of the first part,
`lim_{n → ∞} T_{μ-1}[ω α + n] = T_0[α] / ρ`. (The enumeration hypotheses force
`μ ≥ 1`, so `μ - 1` is the paper's index.)

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Proposition 4. -/
public theorem_wanted isSelfSimilarCompactSet_layer_enum_tendsto_last {K : Set ℝ} {μ : ℕ}
    {ρ : ℝ} (hK : IsSelfSimilarCompactSet K μ ρ) {t : ℕ → Ordinal.{0} → ℝ}
    (ht : ∀ u, StrictAntiOn (t u) (Set.Iio (ω ^ ω)))
    (htK : ∀ u, t u '' Set.Iio (ω ^ ω) = selfSimilarLayer K u)
    {α : Ordinal.{0}} (hα : α < ω ^ ω) :
    Tendsto (fun n : ℕ => t (μ - 1) (ω * α + n)) atTop (𝓝 (t 0 α / ρ))

/-- A quasi-arithmetical compact set of module `μ` and ratio `ρ`: a self-similar compact
set whose ratio is a natural number `ρ ≥ 2` and for which there is `κ` with
`K \ {0} = {n / ρ^k : ρ ∤ n, k ≥ κ(n)}`. The paper's `κ` is defined on `ℕ \ ρℕ`; here it
is a function on `ℕ` whose values off `ℕ \ ρℕ` are irrelevant.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Definition 2. -/
public def IsQuasiArithmeticalCompactSet (K : Set ℝ) (μ ρ : ℕ) : Prop :=
  2 ≤ ρ ∧ IsSelfSimilarCompactSet K μ ρ ∧
    ∃ κ : ℕ → ℕ, K \ {0} = {x | ∃ n k : ℕ, ¬ ρ ∣ n ∧ κ n ≤ k ∧ x = n / (ρ : ℝ) ^ k}

/-- Characteristic lemma: a quasi-arithmetical compact set is self-similar with the same
module and ratio.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Definition 2. -/
public theorem IsQuasiArithmeticalCompactSet.isSelfSimilarCompactSet {K : Set ℝ} {μ ρ : ℕ}
    (hK : IsQuasiArithmeticalCompactSet K μ ρ) : IsSelfSimilarCompactSet K μ ρ :=
  hK.2.1

/-- Proposition 5: in a quasi-arithmetical compact set, if `n / ρ^p ∈ T_v` and
`n / ρ^q ∈ T_w` then `p μ - v = q μ - w`. The paper takes `n` a positive natural number;
`n = 0` is allowed here (then `0` lies in no layer and the claim is vacuous).

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Proposition 5. -/
public theorem_wanted isQuasiArithmeticalCompactSet_layer_index {K : Set ℝ} {μ ρ : ℕ}
    (hK : IsQuasiArithmeticalCompactSet K μ ρ) {n p q v w : ℕ}
    (hv : (n : ℝ) / (ρ : ℝ) ^ p ∈ selfSimilarLayer K v)
    (hw : (n : ℝ) / (ρ : ℝ) ^ q ∈ selfSimilarLayer K w) :
    (p * μ - v : ℤ) = q * μ - w

/-- Proposition 6: the stability gauge satisfies `‖ρ n‖_K = ‖n‖_K + μ`. The gauge is
`‖n‖_K = ℓ μ + d - u` whenever `n / ρ^ℓ ∈ T_u`, with a displacement `d` independent of
`n` (Definition 3); `d` cancels, so the claim is stated as: if `n / ρ^ℓ ∈ T_u` and
`ρ n / ρ^{ℓ'} ∈ T_{u'}` then `ℓ' μ - u' = ℓ μ - u + μ`.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Proposition 6. -/
public theorem_wanted isQuasiArithmeticalCompactSet_gauge_ratio_mul {K : Set ℝ} {μ ρ : ℕ}
    (hK : IsQuasiArithmeticalCompactSet K μ ρ) {n ℓ u ℓ' u' : ℕ}
    (h : (n : ℝ) / (ρ : ℝ) ^ ℓ ∈ selfSimilarLayer K u)
    (h' : ((ρ * n : ℕ) : ℝ) / (ρ : ℝ) ^ ℓ' ∈ selfSimilarLayer K u') :
    (ℓ' * μ - u' : ℤ) = ℓ * μ - u + μ

/-- The un-normalized stability gauge `ℓ μ - u` of `n`, read off the witness
`n / ρ^ℓ ∈ T_u` with the least `ℓ` (and the `u` of that witness). By Proposition 5 the
value `ℓ μ - u` is the same for every witness when `K` is quasi-arithmetical; the least
`ℓ` only fixes a choice.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Definition 3. -/
public noncomputable def stabilityGaugeIndex (K : Set ℝ) (μ ρ : ℕ) (n : ℕ) : ℤ :=
  let ℓ : ℕ := sInf {ℓ : ℕ | ∃ u, (n : ℝ) / (ρ : ℝ) ^ ℓ ∈ selfSimilarLayer K u}
  ((ℓ * μ : ℕ) : ℤ) - (sInf {u : ℕ | (n : ℝ) / (ρ : ℝ) ^ ℓ ∈ selfSimilarLayer K u} : ℕ)

/-- The stability gauge `‖n‖_K := ℓ μ + d - u` (when `n / ρ^ℓ ∈ T_u`) of a
quasi-arithmetical compact set of module `μ` and ratio `ρ`, with the displacement `d`
chosen so that `‖1‖_K = 0`, i.e. `d = -(ℓ₁ μ - u₁)` for the witness `1 / ρ^{ℓ₁} ∈ T_{u₁}`.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Definition 3. -/
public noncomputable def stabilityGauge (K : Set ℝ) (μ ρ : ℕ) (n : ℕ) : ℤ :=
  stabilityGaugeIndex K μ ρ n - stabilityGaugeIndex K μ ρ 1

/-- Characteristic value: the displacement normalizes the gauge so that `‖1‖_K = 0`.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Definition 3. -/
public theorem stabilityGauge_one (K : Set ℝ) (μ ρ : ℕ) : stabilityGauge K μ ρ 1 = 0 :=
  sub_self _

/-- An arithmetical compact set of module `μ` and ratio `ρ`: a quasi-arithmetical compact
set such that, for every ordinal `α < ω^ω` and `u ≥ 0`, writing `T_{u+1}[α] = n / ρ^k`
with `ρ ∤ n`, the sets `{T_u[ω α + r] : r ≥ 0}` and
`{b (a ρ^r + 1) / ρ^{r+k} : n = a b, ‖n‖_K = ‖a‖_K + ‖b‖_K, r ≥ 0}` have finite
symmetric difference. `T_u[·]` is the strictly decreasing enumeration of the layer `T_u`
by `[0, ω^ω)` (such an enumeration is unique; Proposition 3 gives the order type `ω^ω`),
taken here as a quantified family `t`.

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

/-- Characteristic lemma: an arithmetical compact set is quasi-arithmetical with the same
module and ratio.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Definition 4. -/
public theorem IsArithmeticalCompactSet.isQuasiArithmeticalCompactSet {K : Set ℝ}
    {μ ρ : ℕ} (hK : IsArithmeticalCompactSet K μ ρ) : IsQuasiArithmeticalCompactSet K μ ρ :=
  hK.1

/-- Proposition 7: every derived set `K^{(n)}` of an arithmetical compact set of module `μ`
and ratio `ρ` is an arithmetical compact set of the same module and ratio.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Proposition 7. -/
public theorem_wanted isArithmeticalCompactSet_derivedSet_iterate {K : Set ℝ} {μ ρ : ℕ}
    (hK : IsArithmeticalCompactSet K μ ρ) (n : ℕ) :
    IsArithmeticalCompactSet (derivedSet^[n] K) μ ρ

/-- A stable number: a positive `n` with `‖3^k n‖ = ‖n‖ + 3k` for all `k`, where `‖·‖` is
integer complexity (`cx`, MathlibExt's `IntegerComplexity.complexity` over `ℕ`). The paper
quantifies over `k ≥ 1`; `k = 0` is trivial.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Section 1. -/
public def IsComplexityStable (n : ℕ) : Prop :=
  0 < n ∧ ∀ k : ℕ, cx (3 ^ k * n) = cx n + 3 * k

/-- The stable complexity `‖n‖_st := ‖3^a n‖ - 3a`, for the least `a` with `3^a n` stable
(Altman and Zelinsky show such `a` exists for `n ≥ 1`; any larger `a` gives the same value).

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Section 1. -/
public noncomputable def stableComplexity (n : ℕ) : ℤ :=
  (cx (3 ^ sInf {a : ℕ | IsComplexityStable (3 ^ a * n)} * n) : ℤ) -
    3 * (sInf {a : ℕ | IsComplexityStable (3 ^ a * n)} : ℕ)

/-- Characteristic value: a stable number's stable complexity is its complexity.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Section 1. -/
public theorem stableComplexity_of_isComplexityStable {n : ℕ} (h : IsComplexityStable n) :
    stableComplexity n = cx n := by
  have h0 : sInf {a : ℕ | IsComplexityStable (3 ^ a * n)} = 0 :=
    Nat.sInf_eq_zero.mpr (Or.inl (by simpa using h))
  simp [stableComplexity, h0]

/-- The set `T_0 := {n / 3^k : n stable with ‖n‖ = 3k + 2}` of display (7).

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Section 3, equation (7). -/
public def complexityLayerZero : Set ℝ :=
  {x | ∃ n k : ℕ, IsComplexityStable n ∧ cx n = 3 * k + 2 ∧ x = n / (3 : ℝ) ^ k}

/-- Characteristic lemma: `T_0` consists of nonnegative reals.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Section 3, equation (7). -/
public theorem complexityLayerZero_subset_Ici : complexityLayerZero ⊆ Set.Ici 0 := by
  rintro x ⟨n, k, -, -, rfl⟩
  exact Set.mem_Ici.mpr (by positivity)

/-- Theorem 2: the closure `K` of `T_0` (display (7)) is an arithmetical compact set with
module `μ = 3` and ratio `ρ = 3`, and its stability gauge coincides with the stable
complexity, `‖n‖_K = ‖n‖_st` for `n ≥ 1`. The extracted record prints `K = T0`; the paper
writes `K` as the closure of `T_0`.

Source: J. Arias de Reyna, *Arithmetical Self-Similar Compact Sets*, INTEGERS 24
(2024), Article A21, Theorem 2. -/
public theorem_wanted isArithmeticalCompactSet_closure_complexityLayerZero :
    IsArithmeticalCompactSet (closure complexityLayerZero) 3 3 ∧
      ∀ n : ℕ, 0 < n → stabilityGauge (closure complexityLayerZero) 3 3 n = stableComplexity n

end

end MetaMathlibExt
