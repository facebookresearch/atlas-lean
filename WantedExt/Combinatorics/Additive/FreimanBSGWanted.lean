/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Additive.Energy
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic

/-!
# Freiman's theorem and the Balog–Szemerédi–Gowers theorem: wanted theorems

The two inverse theorems of additive combinatorics used in §7 of Gowers's proof of
Szemerédi's theorem. Mathlib already has the Plünnecke–Ruzsa inequalities
(`Mathlib.Combinatorics.Additive.PluenneckeRuzsa`) and additive energy (`Finset.addEnergy`),
which these statements reuse.

Source: [G01] W. T. Gowers, *A new proof of Szemerédi's theorem*, Geom. Funct. Anal. 11 (2001)
465–588; numbering of the author's preprint `sz898.dvi`,
https://www.dpmms.cam.ac.uk/~wtg10/papers.html (journal numbering not checked).
-/

@[expose] public section

open scoped Pointwise

namespace MathlibExt.Combinatorics.Additive.FreimanBSGWanted

/-- **Freiman's theorem.** For every constant `C` there are `d₀` and `K` such that every
nonempty finite `A ⊆ ℤ` with `|A + A| ≤ C|A|` lies in a `d`-dimensional arithmetic progression
`{x₀ + ∑ aᵢ xᵢ : 0 ≤ aᵢ < kᵢ}` with `d ≤ d₀`, positive integers `xᵢ, kᵢ` and size
`k₁ ⋯ k_d ≤ K|A|`: Theorem 7.1 of Gowers [G01] (Freiman's theorem, with Ruzsa's proof). The
nonemptiness hypothesis is implicit there (`|A| = m` and the size bound `≤ Km` fail for
`A = ∅`). -/
theorem_wanted freiman (C : ℝ) :
    ∃ (d₀ : ℕ) (K : ℝ), ∀ A : Finset ℤ, A.Nonempty → ((A + A).card : ℝ) ≤ C * A.card →
      ∃ (d : ℕ) (x₀ : ℤ) (x : Fin d → ℤ) (k : Fin d → ℕ),
        d ≤ d₀ ∧ (∀ i, 0 < x i) ∧ (∀ i, 0 < k i) ∧ ((∏ i, k i : ℕ) : ℝ) ≤ K * A.card ∧
        ∀ a ∈ A, ∃ c : Fin d → ℕ, (∀ i, c i < k i) ∧ a = x₀ + ∑ i, (c i : ℤ) * x i

/-- **Balog–Szemerédi–Gowers theorem.** Let `A ⊆ ℤⁿ` have `m` elements and additive energy
`E(A) ≥ c₀ m³` with `c₀ > 0`. Then some `A'' ⊆ A` has `|A''| ≥ 2^{-20} c₀^{12} m` and
`|A'' - A''| ≤ 2^{38} c₀^{-24} m`: Proposition 7.3 of Gowers [G01], with these explicit
constants. Gowers writes the hypothesis as `‖A * A‖₂² = #{(a, b, c, d) ∈ A⁴ : a - b = c - d}`,
which is Mathlib's `Finset.addEnergy A A` (it counts the quadruples `((a₁, a₂), (b₁, b₂))` with
`a₁ + b₁ = a₂ + b₂`, a relabelling of `a - b = c - d`). Balog and Szemerédi proved the
qualitative version with the regularity lemma; the polynomial bounds are Gowers's. -/
theorem_wanted balog_szemeredi_gowers (n : ℕ) (A : Finset (Fin n → ℤ)) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hE : c₀ * (A.card : ℝ) ^ 3 ≤ (Finset.addEnergy A A : ℝ)) :
    ∃ A'' ⊆ A, (2 : ℝ)⁻¹ ^ 20 * c₀ ^ 12 * A.card ≤ A''.card ∧
      ((A'' - A'').card : ℝ) ≤ 2 ^ 38 * c₀⁻¹ ^ 24 * A.card

end MathlibExt.Combinatorics.Additive.FreimanBSGWanted
