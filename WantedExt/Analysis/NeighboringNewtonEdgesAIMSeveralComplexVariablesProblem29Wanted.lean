/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Neighboring extreme edges of a plurisubharmonic polynomial (AIM CR mappings, Problem 2)

AIM workshop Emerging applications of complexity for CR mappings, Plurisubharmonic polynomials,
Problem 2 (B. Stensønes): let `p(z, z̄, w, w̄) = ∑ p_{αβγδ} z^α z̄^β w^γ w̄^δ` be a plurisubharmonic
real-valued polynomial on `ℂ²` and `N(p) = {(a, b) : a = α + β, b = γ + δ, p_{αβγδ} ≠ 0}`. Let `Γ₁,
Γ₂` be extreme edges of `N(p)` with `Γ₁ ∩ Γ₂ ≠ ∅`, where an extreme edge is a line in `N(p)` with no
points of `N(p)` below. Can `q = ∑_{(α+β, γ+δ) ∈ Γ₁ ∪ Γ₂} p_{αβγδ} z^α z̄^β w^γ w̄^δ` be written as
the sum of two plurisubharmonic weighted homogeneous polynomials? Remark: the polynomial `q` is
plurisubharmonic but not necessarily weighted homogeneous.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import MathlibExt.Analysis.Complex.ComplexHessian

@[expose] public section

namespace MathlibExt.Analysis.NeighboringNewtonEdgesAIMSeveralComplexVariablesProblem29Wanted

/-!
Source: AIM workshop Emerging applications of complexity for CR mappings, problem list,
Plurisubharmonic polynomials, https://aimath.org/WWN/crmappings/crmappings.pdf, Problem 2 (B.
Stensønes) and its remark. UnsolvedMath record UM-20002871 (`AIM-SEVERAL_COMPLEX_VARIABLES-0029`),
dataset ulamai/UnsolvedMath v1.8.0.

Polynomials are `MvPolynomial (Fin 4) ℂ` in the variables `z, z̄, w, w̄`, evaluated at `(z, z̄, w,
w̄)`; real-valued means the value is always real, and plurisubharmonic means that the complex
Hessian of the real part (`MetaMathlibExt.complexHessian`) is positive semidefinite everywhere.
Extreme edges follow Simon and Stensønes' Definition 3.1 (at least two points of `N(p)` on a line of
negative slope with every other point strictly above); the list's 'line with no points below' admits
more lines, so this reading makes the claim weaker and its refutation remains valid. The refuted
claim is the problem's remark that `q` is plurisubharmonic, in the local form of the first item of
Simon and Stensønes' Question 3.6 (plurisubharmonic in some neighborhood of the origin, which the
remark's global claim implies). The decomposition question itself is not formalized: Simon and
Stensønes do not state its answer, and deriving it from their example needs a step not printed in
the sources (a sum of plurisubharmonic polynomials is plurisubharmonic).
-/

open MvPolynomial MetaMathlibExt
open scoped ComplexOrder

/-- The value `P(z, z̄, w, w̄)` at `x = (z, w) ∈ ℂ²` of a polynomial `P` in four variables, read
as `z, z̄, w, w̄` (indices `0, 1, 2, 3`). -/
noncomputable def evalZW (P : MvPolynomial (Fin 4) ℂ) (x : EuclideanSpace ℂ (Fin 2)) : ℂ :=
  eval ![x 0, starRingEnd ℂ (x 0), x 1, starRingEnd ℂ (x 1)] P

/-- `P(z, z̄, w, w̄)` is real for every `(z, w) ∈ ℂ²`. -/
def IsRealValued (P : MvPolynomial (Fin 4) ℂ) : Prop :=
  ∀ x : EuclideanSpace ℂ (Fin 2), (evalZW P x).im = 0

/-- A real-valued polynomial `p = ∑ p_{αβγδ} z^α z̄^β w^γ w̄^δ` is plurisubharmonic on `ℂ²`: its
complex Hessian `(∂²p/∂z_j∂z̄_k)` is positive semidefinite at every point. -/
def IsPlurisubharmonic (P : MvPolynomial (Fin 4) ℂ) : Prop :=
  IsRealValued P ∧ ∀ x, (complexHessian (fun y => (evalZW P y).re) x).PosSemidef

/-- The Newton diagram `N(p) = {(α + β, γ + δ) : p_{αβγδ} ≠ 0}`. -/
def newtonDiagram (P : MvPolynomial (Fin 4) ℂ) : Set (ℕ × ℕ) :=
  {ab | ∃ m ∈ P.support, (m 0 + m 1, m 2 + m 3) = ab}

/-- An extreme edge of `N(p)` (Simon-Stensønes, Def. 3.1): a set `E ⊆ N(p)` of at least two points
on a line `b = s a + c` of negative slope `s` such that every other point of `N(p)` lies strictly
above the line ("a line in `N(p)` with no points in `N(p)` below"). -/
def IsExtremeEdge (P : MvPolynomial (Fin 4) ℂ) (E : Set (ℕ × ℕ)) : Prop :=
  E ⊆ newtonDiagram P ∧ (∃ e ∈ E, ∃ e' ∈ E, e ≠ e') ∧
    ∃ s c : ℝ, s < 0 ∧ (∀ e ∈ E, (e.2 : ℝ) = s * e.1 + c) ∧
      ∀ e ∈ newtonDiagram P, e ∉ E → s * e.1 + c < e.2

open Classical in
/-- The truncation `p_S = ∑_{(α + β, γ + δ) ∈ S} p_{αβγδ} z^α z̄^β w^γ w̄^δ`. -/
noncomputable def truncation (P : MvPolynomial (Fin 4) ℂ) (S : Set (ℕ × ℕ)) :
    MvPolynomial (Fin 4) ℂ :=
  ∑ m ∈ P.support with (m 0 + m 1, m 2 + m 3) ∈ S, monomial m (P.coeff m)

/-- The problem's remark ("the polynomial `q` is plurisubharmonic"), in the form of
Simon-Stensønes' Question 3.6 (first item), as a claim: for every plurisubharmonic real-valued
polynomial `p` on `ℂ²` and distinct extreme edges `Γ₁, Γ₂` of `N(p)` with `Γ₁ ∩ Γ₂ ≠ ∅`, the
truncation `p_{Γ₁ ∪ Γ₂}` is plurisubharmonic on some neighborhood of the origin. -/
def neighboringEdgesTruncationPsh : Prop :=
  ∀ (P : MvPolynomial (Fin 4) ℂ) (E₁ E₂ : Set (ℕ × ℕ)), IsPlurisubharmonic P →
    IsExtremeEdge P E₁ → IsExtremeEdge P E₂ → E₁ ≠ E₂ → (E₁ ∩ E₂).Nonempty →
      ∃ ε : ℝ, 0 < ε ∧ ∀ x : EuclideanSpace ℂ (Fin 2), ‖x‖ < ε →
        (complexHessian (fun y => (evalZW (truncation P (E₁ ∪ E₂)) y).re) x).PosSemidef

/--
Resolved false: the problem's remark fails. Simon and Stensønes' polynomial (two extreme edges `E₁ ≠
E₂` meeting at a vertex) has `P_{E₁ ∪ E₂}` plurisubharmonic in no neighborhood of the origin, the
negative answer to the first item of their Question 3.6. Source: AIM workshop Emerging applications
of complexity for CR mappings, problem list, Plurisubharmonic polynomials,
https://aimath.org/WWN/crmappings/crmappings.pdf, Problem 2 (B. Stensønes) and its remark;
resolution: L. Simon and B. Stensønes, On Newton diagrams of plurisubharmonic polynomials, J. Geom.
Anal. (2018), arXiv:1710.01125, abstract and §4: a plurisubharmonic polynomial P on ℂ² with
precisely two extreme edges E1, E2 such that neither P_{E1 ∪ E2} nor P_{Conv(E1 ∪ E2)} is
plurisubharmonic in any neighborhood of the origin, answering 'no' to Question 3.6 (first two items:
E1 ≠ E2, E1 ∩ E2 ≠ ∅); Definition 3.1 (Newton diagram, extreme edges),
https://doi.org/10.1007/s12220-018-0092-5.
-/
public theorem_wanted neighboringEdgesTruncationPsh_refuted : ¬ neighboringEdgesTruncationPsh

end MathlibExt.Analysis.NeighboringNewtonEdgesAIMSeveralComplexVariablesProblem29Wanted
