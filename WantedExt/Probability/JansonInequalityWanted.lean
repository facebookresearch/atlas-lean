/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Combinatorics.RandomSubset
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Janson's inequalities

Let `R` be a random subset of a finite ground set containing each element independently, let
`S₁, …, S_k` be subsets of the ground set and `Aᵢ` the event `Sᵢ ⊆ R`. With
`μ = ∑ᵢ P(Aᵢ)` and `Δ = ∑ P(Aᵢ ∩ Aⱼ)` over ordered pairs `i ≠ j` with `Sᵢ ∩ Sⱼ ≠ ∅`, Janson's
inequalities bound the probability that no `Aᵢ` occurs:

* `P(no Aᵢ) ≤ exp(-μ + Δ/2)` (first Janson inequality);
* `P(no Aᵢ) ≤ exp(-μ² / (2Δ))` when `Δ ≥ μ` (second Janson inequality).

They are the exponential counterpart of the second moment method
(`MathlibExt.Probability.Combinatorics.SecondMomentMethod`) and match the Harris lower bound
`P(no Aᵢ) ≥ ∏ (1 - P(Aᵢ))` when `Δ = o(μ)`.

Reference: Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 lecture notes,
Spring 2019, Setup 7.10, Theorems 7.11 and 7.14 (https://yufeizhao.com/pm/sp19/pmnotes.pdf);
originally S. Janson, T. Łuczak and A. Ruciński (1990).
-/

@[expose] public section

open MeasureTheory unitInterval MathlibExt.Probability.Combinatorics.RandomSubset

namespace MathlibExt.Probability.JansonInequalityWanted

variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]

/-- **Expected number of contained sets (Janson's `μ`).** For a random subset `R` with element
probabilities `p` and sets `S i`, `μ = ∑ᵢ P(Sᵢ ⊆ R)` (Y. Zhao, *The Probabilistic Method in
Combinatorics*, MIT 18.218 notes, 2019, Setup 7.10). -/
noncomputable def jansonMu (p : α → I) (S : ι → Finset α) : ℝ :=
  ∑ i, (randomSubsetLaw p).real (containsEvent (S i))

/-- **Janson's correlation sum `Δ`.** `Δ = ∑ P(Sᵢ ⊆ R and Sⱼ ⊆ R)` over the ordered pairs
`(i, j)` with `i ≠ j` and `Sᵢ ∩ Sⱼ ≠ ∅` (Y. Zhao, *The Probabilistic Method in Combinatorics*,
MIT 18.218 notes, 2019, Setup 7.10). -/
noncomputable def jansonDelta (p : α → I) (S : ι → Finset α) : ℝ :=
  ∑ i, ∑ j, if i ≠ j ∧ ¬ Disjoint (S i) (S j) then
    (randomSubsetLaw p).real (containsEvent (S i) ∩ containsEvent (S j)) else 0

/-- **First Janson inequality.** Let `R` be a random subset of a finite set containing each
element `a` independently with probability `p a`, and let `Aᵢ` be the event `Sᵢ ⊆ R`. Then
`P(no Aᵢ occurs) ≤ exp(-μ + Δ/2)`, where `μ = ∑ᵢ P(Aᵢ)` and `Δ` sums `P(Aᵢ ∩ Aⱼ)` over ordered
pairs `i ≠ j` with `Sᵢ ∩ Sⱼ ≠ ∅` (Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT
18.218 notes, 2019, Theorem 7.11; Setup 7.10 there chooses each element independently, and its
proof, by the Harris inequality for independent boolean variables (Proposition 7.2), covers
element-dependent probabilities `p a` as here). -/
theorem_wanted janson_inequality (p : α → I) (S : ι → Finset α) :
    (randomSubsetLaw p).real {ω | ∀ i, ω ∉ containsEvent (S i)} ≤
      Real.exp (-jansonMu p S + jansonDelta p S / 2)

/-- **Second Janson inequality.** In the setting of the first Janson inequality, if `Δ ≥ μ`
then `P(no Aᵢ occurs) ≤ exp(-μ² / (2Δ))` (Y. Zhao, *The Probabilistic Method in
Combinatorics*, MIT 18.218 notes, 2019, Theorem 7.14). -/
theorem_wanted janson_inequality_of_le (p : α → I) (S : ι → Finset α)
    (h : jansonMu p S ≤ jansonDelta p S) :
    (randomSubsetLaw p).real {ω | ∀ i, ω ∉ containsEvent (S i)} ≤
      Real.exp (-(jansonMu p S ^ 2 / (2 * jansonDelta p S)))

end MathlibExt.Probability.JansonInequalityWanted
