/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Eigenvalue sensitivity and elasticity in matrix population models

For a population projection matrix `A` with a simple real eigenvalue `λ`, right eigenvector `w`
(the stable stage structure when `λ` is dominant) and left eigenvector `v` (reproductive value),
Caswell (1978) showed that `λ` depends differentiably on the entries of `A` with sensitivity
`∂λ/∂a_ij = v_i w_j / ⟨v, w⟩`. The elasticities `e_ij = (a_ij / λ) ∂λ/∂a_ij` then sum to one,
because `vᵀ A w = λ ⟨v, w⟩` (Euler's identity for the degree-one homogeneous function `λ`).
Simplicity of `λ` (multiplicity one as a root of the characteristic polynomial) also forces
`⟨v, w⟩ ≠ 0`. Matrices are written as functions `Fin n → Fin n → ℝ` so that the sup norm
measures perturbations of the entries.

`Domains.Biology.Demography.Leslie` lists sensitivity and elasticity analysis as not covered.

Sources: H. Caswell, "A general formula for the sensitivity of population growth rate to
changes in life history parameters", Theor. Popul. Biol. 14 (1978) 215–230; J. R. Magnus,
"On differentiating eigenvalues and eigenvectors", Econometric Theory 1 (1985) 179–191,
Theorem 2, eq. (17); H. de Kroon, A. Plaisier, J. van Groenendael and H. Caswell, "Elasticity:
the relative contribution of demographic parameters to population growth rate", Ecology 67
(1986) 1427–1431.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Group.Constructions

@[expose] public section

namespace WantedExt.Biology.Ecology.EigenvalueSensitivityWanted

open Matrix Polynomial Filter Topology

variable {n : ℕ}

/-- `lam` is a **simple eigenvalue** of the matrix with entries `a`: a root of multiplicity
exactly one of its characteristic polynomial. -/
def IsSimpleEigenvalue (a : Fin n → Fin n → ℝ) (lam : ℝ) : Prop :=
  (Matrix.of a).charpoly.rootMultiplicity lam = 1

/-- **Caswell's sensitivity formula** (Caswell 1978; Magnus 1985, Theorem 2, eq. (17)). Let
`lam` be a simple real eigenvalue of `A = (a_ij)` with nonzero right eigenvector `w`
(`A w = lam w`) and nonzero left eigenvector `v` (`vᵀ A = lam vᵀ`). Then `⟨v, w⟩ ≠ 0`, and
there is a function `Λ` of the entries, with `Λ(A) = lam`, that is differentiable at `A`, whose
value at every matrix near `A` is a root of that matrix's characteristic polynomial, and whose
partial derivative in the entry `a_ij` is `v_i w_j / ⟨v, w⟩`.

Sources: Caswell (1978); Magnus (1985), Theorem 2. -/
public theorem_wanted eigenvalue_sensitivity (a : Fin n → Fin n → ℝ) (lam : ℝ)
    (hsimple : IsSimpleEigenvalue a lam) (w v : Fin n → ℝ) (hw : w ≠ 0) (hv : v ≠ 0)
    (hAw : Matrix.of a *ᵥ w = lam • w) (hvA : v ᵥ* Matrix.of a = lam • v) :
    v ⬝ᵥ w ≠ 0 ∧
      ∃ Λ : (Fin n → Fin n → ℝ) → ℝ, Λ a = lam ∧ DifferentiableAt ℝ Λ a ∧
        (∀ᶠ b in 𝓝 a, (Matrix.of b).charpoly.eval (Λ b) = 0) ∧
        ∀ i j, fderiv ℝ Λ a (Pi.single i (Pi.single j (1 : ℝ))) = v i * w j / (v ⬝ᵥ w)

/-- **Elasticities sum to one** (de Kroon et al. 1986). Under the hypotheses of
`eigenvalue_sensitivity` and `lam ≠ 0`, the elasticities
`e_ij = (a_ij / lam) · v_i w_j / ⟨v, w⟩` satisfy `∑_{i,j} e_ij = 1`.

Sources: de Kroon, Plaisier, van Groenendael and Caswell (1986); Caswell (1978). -/
public theorem_wanted sum_elasticities (a : Fin n → Fin n → ℝ) (lam : ℝ)
    (hsimple : IsSimpleEigenvalue a lam) (hlam : lam ≠ 0) (w v : Fin n → ℝ) (hw : w ≠ 0)
    (hv : v ≠ 0) (hAw : Matrix.of a *ᵥ w = lam • w) (hvA : v ᵥ* Matrix.of a = lam • v) :
    ∑ i, ∑ j, a i j / lam * (v i * w j / (v ⬝ᵥ w)) = 1

end WantedExt.Biology.Ecology.EigenvalueSensitivityWanted
