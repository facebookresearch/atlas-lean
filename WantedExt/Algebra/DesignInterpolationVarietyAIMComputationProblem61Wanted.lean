/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Interpolating the generators of a standard-monomial ideal on a design (AIM, Question 47)

AIM workshop Computational algebraic statistics, problem list, Question 47 [Pistone]: take a design
of `N` distinct rational vectors `D = {v_1, …, v_N} ⊆ ℚ^d` and monomials `x^{α_1}, …, x^{α_N}` which
are linearly independent modulo the design ideal `I(D)`, and suppose these monomials are the
standard monomials of some monomial ideal `M = ⟨m_1, …, m_r⟩`. Since they are a basis of the
quotient space, each `m_i` has a unique representation as a linear combination of the `x^{α_j}`
modulo `I(D)`; this produces `r` polynomials `f_1, …, f_r` in `I(D)`. Are the only points on which
these polynomials vanish the design points, that is, is `V(f_1, …, f_r) = D`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace MathlibExt.Algebra.DesignInterpolationVarietyAIMComputationProblem61Wanted

/-!
Source: AIM workshop Computational algebraic statistics, problem list,
https://aimath.org/WWN/compalgstat/compalgstat.pdf, Question 47 (Pistone). UnsolvedMath record
UM-20001223 (`AIM-COMPUTATION-0061`), dataset ulamai/UnsolvedMath v1.8.0.

Reading choices. The source writes the polynomial ring as `ℚ[x_1, …, x_n]` with `D ⊆ ℚ^d`; the
variables are the `d` coordinates. Monomials are exponent vectors `α : Fin d →₀ ℕ`. The monomials
in `B` are linearly independent modulo `I(D)` when no nonzero combination of them vanishes on all
of `D`; `B` is the set of standard monomials of `M = ⟨x^g : g ∈ G⟩` when an exponent lies in `B`
exactly if no generator exponent `g ∈ G` divides it (`g ≤ α` coordinatewise). `c g` holds the
coefficients of the representation of `x^g` (only the values on `B` enter), and
`f_g = x^g - ∑_{α ∈ B} c g α x^α`. `V(f_1, …, f_r)` is the set of common complex zeros, compared
with `D` viewed in `ℂ^d`.
-/

open MvPolynomial

/-- `f_g = x^g - ∑_{α ∈ B} c_α x^α`, the generator `x^g` minus its representation in the monomials
of `B`. -/
noncomputable def interpolationDefect {d : ℕ} (B : Finset (Fin d →₀ ℕ)) (g : Fin d →₀ ℕ)
    (c : (Fin d →₀ ℕ) → ℚ) : MvPolynomial (Fin d) ℚ :=
  monomial g 1 - ∑ α ∈ B, monomial α (c α)

/-- Question 47 (Pistone): for every design `D ⊆ ℚ^d`, every set `B` of `|D|` monomials that are
linearly independent modulo `I(D)` and form the standard monomials of the monomial ideal generated
by `{x^g : g ∈ G}`, and every representation `c` of the generators modulo `I(D)`, the common complex
zeros of the polynomials `f_g` (`g ∈ G`) are exactly the points of `D`. -/
def designInterpolationVarietyIsDesign : Prop :=
  ∀ (d : ℕ) (D : Finset (Fin d → ℚ)) (B G : Finset (Fin d →₀ ℕ))
    (c : (Fin d →₀ ℕ) → (Fin d →₀ ℕ) → ℚ),
    B.card = D.card →
    (∀ a : (Fin d →₀ ℕ) → ℚ, (∀ v ∈ D, eval v (∑ α ∈ B, monomial α (a α)) = 0) →
      ∀ α ∈ B, a α = 0) →
    (∀ α : Fin d →₀ ℕ, α ∈ B ↔ ∀ g ∈ G, ¬ g ≤ α) →
    (∀ g ∈ G, ∀ v ∈ D, eval v (interpolationDefect B g (c g)) = 0) →
    {z : Fin d → ℂ | ∀ g ∈ G, aeval z (interpolationDefect B g (c g)) = 0} =
      (fun v : Fin d → ℚ => fun i => (v i : ℂ)) '' (D : Set (Fin d → ℚ))

/--
Resolved false: the problem list records that Question 47 was answered in the negative by Bernd
Sturmfels at the workshop. Source: AIM workshop Computational algebraic statistics, problem list,
https://aimath.org/WWN/compalgstat/compalgstat.pdf, Question 47 (Pistone); resolution: the same
list, note after Question 47 ("Question 47 was answered in the negative by Bernd Sturmfels at the
conference"), https://aimath.org/WWN/compalgstat/compalgstat.pdf.
-/
public theorem_wanted designInterpolationVarietyIsDesign_refuted :
    ¬ designInterpolationVarietyIsDesign

end MathlibExt.Algebra.DesignInterpolationVarietyAIMComputationProblem61Wanted
