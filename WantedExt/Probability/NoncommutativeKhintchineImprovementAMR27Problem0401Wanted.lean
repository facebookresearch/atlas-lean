/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Improving the noncommutative Khintchine inequality (Bandeira, Open Problem 4.1)

Bandeira, Ten Lectures and Forty-Two Open Problems, Open Problem 4.1: for symmetric `A₁, …, Aₙ ∈
ℝ^{d × d}` and i.i.d. standard Gaussians `gₖ`, does `E ‖∑ₖ gₖ Aₖ‖ ≲ σ + (log d)^{1/2} σ_*` hold?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

namespace MathlibExt.Probability.NoncommutativeKhintchineImprovementAMR27Problem0401Wanted

/-!
Source: A. S. Bandeira, Ten Lectures and Forty-Two Open Problems in the Mathematics of Data Science
(2015-2016), Open Problem 4.1, https://afonsobandeira.wordpress.com/2015/10/25/10l42concentration/.
UnsolvedMath record UM-02800401 (`AMR-027-0401`), dataset ulamai/UnsolvedMath v1.8.0.

Open Problem 4.1 asks to prove or disprove Conjecture 4.21 of the notes. There `σ = ‖∑ₖ Aₖ²‖^{1/2}`
and the weak variance is `σ_* = max_{‖v‖ = 1} (∑ₖ (vᵀ Aₖ v)²)^{1/2}` (Definition 4.15); `‖·‖` is the
spectral norm (`Matrix.Norms.L2Operator`), `≲` means `≤ C ·` with a universal constant `C`, and the
expectation is over independent standard Gaussians `gₖ`. This `σ_*` is the case `w = v` of the weak
variance `σ_*(X) = sup_{‖v‖ = ‖w‖ = 1} (∑ₖ ⟨v, Aₖ w⟩²)^{1/2}` of Bandeira-Boedihardjo-van Handel, so
it is at most `σ_*(X)`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator

/-- `σ = ‖∑ₖ Aₖ²‖^{1/2}`, with the spectral norm. -/
noncomputable def sigma {d n : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  Real.sqrt ‖∑ k, A k * A k‖

/-- The weak variance `σ_* = max_{‖v‖ = 1} (∑ₖ (vᵀ Aₖ v)²)^{1/2}` (Bandeira, Definition 4.15). -/
noncomputable def sigmaStar {d n : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ⨆ (v : Fin d → ℝ) (_ : ∑ i, v i ^ 2 = 1), Real.sqrt (∑ k, (v ⬝ᵥ (A k *ᵥ v)) ^ 2)

/-- Bandeira's Conjecture 4.21, with a positive answer: there is a universal `C` such that for all
real symmetric `A₁, …, Aₙ ∈ ℝ^{d × d}` and independent standard Gaussians `gₖ`,
`E ‖∑ₖ gₖ Aₖ‖ ≤ C (σ + (log d)^{1/2} σ_*)`. -/
def noncommutativeKhintchineImprovement : Prop :=
  ∃ C : ℝ, ∀ (d n : ℕ) (A : Fin n → Matrix (Fin d) (Fin d) ℝ), (∀ k, (A k).IsSymm) →
    ∫ g, ‖∑ k, g k • A k‖ ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) ≤
      C * (sigma A + Real.sqrt (Real.log d) * sigmaStar A)

/--
Resolved false: Bandeira, Boedihardjo and van Handel (Proposition 8.2) show that no bound `E ‖X‖ ≤ C
σ(X) + C σ_*(X) (log d)^β` holds for any universal `C, β > 0`, which disproves the conjecture of
Bandeira's notes; the counterexamples `X_{n,N} = ∑ₖ 1 ⊗ ⋯ ⊗ G_k ⊗ ⋯ ⊗ 1` are built from independent
real Wigner matrices, so they are real symmetric Gaussian series `∑ gᵢ Aᵢ`, and the `σ_*` of the
notes is at most their `σ_*(X)`. Source: A. S. Bandeira, Ten Lectures and Forty-Two Open Problems in
the Mathematics of Data Science (2015-2016), Open Problem 4.1,
https://afonsobandeira.wordpress.com/2015/10/25/10l42concentration/; resolution: A. S. Bandeira, M.
T. Boedihardjo and R. van Handel, Matrix concentration inequalities and free probability, Invent.
Math. 234 (2023); arXiv:2108.06312, Section 8.1.2, Proposition 8.2 and the paragraph after it: 'A
special case of Proposition 8.2 disproves the conjecture made in [41, 43, 5]: the parameter σ∗(X)
satisfies all four properties (1)-(4), and thus an inequality of the form (8.1) with σ∗∗(X) = σ∗(X)
cannot hold', where (8.1) is E‖X‖ ≤ Cσ(X) + Cσ∗∗(X)(log d)^β for d × d centered Gaussian matrices
and [5] is Bandeira's lecture notes; the counterexample X_{n,N} is a sum of tensor products of
standard Wigner matrices, which Definition 1.1 makes real symmetric with independent centered
Gaussian entries on and above the diagonal, https://doi.org/10.1007/s00222-023-01204-6.
-/
public theorem_wanted noncommutativeKhintchineImprovement_refuted :
    ¬ noncommutativeKhintchineImprovement

end MathlibExt.Probability.NoncommutativeKhintchineImprovementAMR27Problem0401Wanted
