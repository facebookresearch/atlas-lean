/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Protected polymorphism in the finite-niche Levene model

The same allele frequency `p` enters every niche. Selection acts within each niche *before*
the resulting frequencies are averaged with fixed weights `c`. At fixation of either
homozygote the slope is the reciprocal of the weighted harmonic mean of that homozygote's
viabilities.

Source: J. Felsenstein, *Theoretical Evolutionary Genetics* (December 2019), §IV.10,
“The Levene Model: High Migration”, pp. 196–198, equations (IV-42)–(IV-46).
<https://felsenst.github.io/pgbook/pgbook.pdf>
-/

public section

open Filter Set
open scoped BigOperators Topology

namespace MathlibExt.Biology.PopulationGenetics.Levene

/-- In Levene's diploid model the genotype viabilities in niche `i` are `w i`, `1`, `v i`.
The frequency map fixes both endpoints. A boundary slope above one gives strict increase of
the rare allele; if both exceed one there is an interior fixed point. A slope below one makes
the corresponding endpoint locally attracting under iteration, within the frequency interval.

With haploid relative viability `a i`, taking `w i = a i` and `v i = 1 / a i` gives the
same map: multiplying the diploid numerator and denominator by `a i` reveals a common factor
`p * a i + (1 - p)`, positive on `[0, 1]`. The two strict invasion tests are now equivalences.
At mean viability one the quadratic coefficient of the frequency change is minus the weighted
variance: the rare type decreases unless all viabilities are one, when the map is the identity.
Exchanging the types reflects the frequency and reciprocates the relative viabilities, so the
same boundary analysis applies at the other end. -/
theorem_wanted protected_polymorphism {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (hc_sum : ∑ i, c i = 1) :
    let diploid (w v : ι → ℝ) (p : ℝ) :=
      ∑ i, c i * ((p ^ 2 * w i + p * (1 - p)) /
        (p ^ 2 * w i + 2 * p * (1 - p) + (1 - p) ^ 2 * v i))
    let haploid (a : ι → ℝ) (p : ℝ) := ∑ i, c i * (p * a i / (p * a i + (1 - p)))
    (∀ w v : ι → ℝ, (∀ i, 0 < w i) → (∀ i, 0 < v i) →
      let F := diploid w v
      let d₀ := ∑ i, c i / v i
      let d₁ := ∑ i, c i / w i
      F 0 = 0 ∧ F 1 = 1 ∧ HasDerivAt F d₀ 0 ∧ HasDerivAt F d₁ 1 ∧
        (1 < d₀ → ∀ᶠ p in 𝓝[>] 0, p < F p) ∧
        (1 < d₁ → ∀ᶠ p in 𝓝[<] 1, F p < p) ∧
        (1 < d₀ → 1 < d₁ → ∃ p ∈ Ioo 0 1, F p = p) ∧
        (d₀ < 1 → ∀ᶠ p in 𝓝[Icc 0 1] 0, Tendsto (fun n : ℕ ↦ F^[n] p) atTop (𝓝 0)) ∧
        (d₁ < 1 → ∀ᶠ p in 𝓝[Icc 0 1] 1, Tendsto (fun n : ℕ ↦ F^[n] p) atTop (𝓝 1))) ∧
    (∀ a : ι → ℝ, (∀ i, 0 < a i) →
      let H := haploid a
      let m₁ := ∑ i, c i * a i
      let m₂ := ∑ i, c i * (a i) ^ 2
      let r := ∑ i, c i / a i
      EqOn H (diploid a (fun i ↦ (a i)⁻¹)) (Icc 0 1) ∧
        (∀ p ∈ Icc 0 1, haploid (fun i ↦ (a i)⁻¹) (1 - p) = 1 - H p) ∧
        HasDerivAt H m₁ 0 ∧ HasDerivAt H r 1 ∧
        ((∀ᶠ p in 𝓝[>] 0, p < H p) ↔ 1 < m₁) ∧
        ((∀ᶠ p in 𝓝[<] 1, H p < p) ↔ 1 < r) ∧
        ((fun p ↦ H p - (p * m₁ - p ^ 2 * ∑ i, c i * a i * (a i - 1))) =O[𝓝 0]
          (fun p : ℝ ↦ p ^ 3)) ∧
        m₁ ^ 2 ≤ m₂ ∧
        ((∀ i, a i = 1) → EqOn H id (Icc 0 1)) ∧
        (m₁ = 1 →
          ((fun p ↦ H p - p + p ^ 2 * (m₂ - 1)) =O[𝓝 0] (fun p : ℝ ↦ p ^ 3)) ∧
          (m₂ = 1 ↔ ∀ i, a i = 1) ∧
          ((∃ i, a i ≠ 1) → ∀ᶠ p in 𝓝[>] 0, H p < p)))

end MathlibExt.Biology.PopulationGenetics.Levene
