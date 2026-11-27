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
`∂λ/∂a_ij = v_i w_j / ⟨v, w⟩`. Simplicity of `λ` (multiplicity one as a root of the
characteristic polynomial) also forces `⟨v, w⟩ ≠ 0`. For the dominant eigenvalue of a
nonnegative primitive matrix, the population growth rate and the setting in which Jones's notes
state it, the elasticities `e_ij = (a_ij / λ) ∂λ/∂a_ij` sum to one, because
`vᵀ A w = λ ⟨v, w⟩` (Euler's identity for the degree-one homogeneous function `λ`). Matrices are
written as functions `Fin n → Fin n → ℝ` so that the sup norm measures perturbations of the
entries.

`Domains.Biology.Demography.Leslie` lists sensitivity and elasticity analysis as not covered.

Sources: H. Caswell, "A general formula for the sensitivity of population growth rate to
changes in life history parameters", Theor. Popul. Biol. 14 (1978) 215–230; J. R. Magnus,
"On differentiating eigenvalues and eigenvectors", Econometric Theory 1 (1985) 179–191,
Theorem 2, eq. (17); H. de Kroon, A. Plaisier, J. van Groenendael and H. Caswell, "Elasticity:
the relative contribution of demographic parameters to population growth rate", Ecology 67
(1986) 1427–1431; J. H. Jones, "Notes on Fitness Sensitivities", Stanford University (2023),
§§1.3, 1.4, 1.5.1, 1.8 and 1.9.
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

Sources: H. Caswell, "A general formula for the sensitivity of population growth rate to changes
in life history parameters", Theor. Popul. Biol. 14 (1978) 215–230,
doi:10.1016/0040-5809(78)90025-4 (restated in H. de Kroon, J. van Groenendael and J. Ehrlén,
"Elasticities: a review of methods and model limitations", Ecology 81 (2000) 607–618);
J. R. Magnus, "On differentiating eigenvalues and eigenvectors", Econometric Theory 1 (1985)
179–191, Theorem 2, eq. (17). -/
public theorem_wanted eigenvalue_sensitivity (a : Fin n → Fin n → ℝ) (lam : ℝ)
    (hsimple : IsSimpleEigenvalue a lam) (w v : Fin n → ℝ) (hw : w ≠ 0) (hv : v ≠ 0)
    (hAw : Matrix.of a *ᵥ w = lam • w) (hvA : v ᵥ* Matrix.of a = lam • v) :
    v ⬝ᵥ w ≠ 0 ∧
      ∃ Λ : (Fin n → Fin n → ℝ) → ℝ, Λ a = lam ∧ DifferentiableAt ℝ Λ a ∧
        (∀ᶠ b in 𝓝 a, (Matrix.of b).charpoly.eval (Λ b) = 0) ∧
        ∀ i j, fderiv ℝ Λ a (Pi.single i (Pi.single j (1 : ℝ))) = v i * w j / (v ⬝ᵥ w)

/-- **Elasticities sum to one** (de Kroon et al. 1986; Jones 2023, §1.9). Let `A = (a_ij)` be a
nonnegative primitive matrix (some power of `A` has all entries positive) and let `lam` be its
dominant eigenvalue, given by a right eigenvector `w` (`A w = lam w`) and a left eigenvector `v`
(`vᵀ A = lam vᵀ`) whose entries are all positive; by the Perron–Frobenius theorem no other
eigenvalue has such an eigenvector. Then the elasticities
`e_ij = (a_ij / lam) · v_i w_j / ⟨v, w⟩` satisfy `∑_{i,j} e_ij = 1`.

Sources: Jones, "Notes on Fitness Sensitivities" (2023), §§1.3, 1.4, 1.5.1, 1.8 and 1.9;
de Kroon, Plaisier, van Groenendael and Caswell (1986). -/
public theorem_wanted sum_elasticities (a : Fin n → Fin n → ℝ) (ha : ∀ i j, 0 ≤ a i j)
    (hprim : ∃ k : ℕ, ∀ i j, 0 < (Matrix.of a ^ k) i j) (lam : ℝ) (w v : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) (hAw : Matrix.of a *ᵥ w = lam • w)
    (hvA : v ᵥ* Matrix.of a = lam • v) :
    ∑ i, ∑ j, a i j / lam * (v i * w j / (v ⬝ᵥ w)) = 1

end WantedExt.Biology.Ecology.EigenvalueSensitivityWanted
