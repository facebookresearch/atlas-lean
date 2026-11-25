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
public import MathlibExt.Combinatorics.Additive.BalogSzemerediGowers

/-!
# Freiman's theorem

The wanted statement of Freiman's theorem used in §7 of Gowers's proof of Szemerédi's theorem.
This module also re-exports the Balog–Szemerédi–Gowers theorem.

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

end MathlibExt.Combinatorics.Additive.FreimanBSGWanted
