/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Convex.Function

/-!
# Lieb's concavity theorem (wanted)

For a fixed Hermitian matrix `H`, the map `A ↦ tr exp(H + log A)` is concave on the cone of
positive-definite matrices (E. H. Lieb, *Convex trace functions and the Wigner–Yanase–Dyson
conjecture*, Adv. Math. 11 (1973), 267–288, Theorem 6). It is a theorem of matrix analysis,
beside the trace inequalities of Peierls, Klein and von Neumann. Its best-known use is in matrix
concentration: with Jensen's inequality it makes matrix cumulant generating functions
subadditive (J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*, Found. Trends
Mach. Learn. 8 (2015), arXiv:1501.01571, Theorem 3.4.1, Corollary 3.4.2 and Lemma 3.5.1; Chapter 8
proves it from the joint convexity of matrix relative entropy). The proof is deferred.
-/

@[expose] public section

open scoped ComplexOrder

namespace MathlibExt.LinearAlgebra.Matrix.LiebConcavityWanted

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Lieb's concavity theorem** (E. H. Lieb, *Convex trace functions and the Wigner–Yanase–Dyson
conjecture*, Adv. Math. 11 (1973), 267–288, Theorem 6; Tropp, *An Introduction to Matrix
Concentration Inequalities*, arXiv:1501.01571, Theorem 3.4.1 and Theorem 8.1.1). For a fixed
Hermitian matrix `H`, the map `A ↦ tr exp(H + log A)` is concave on the cone of positive-definite
matrices. Here `log A` is the standard matrix function `cfc Real.log A`. -/
theorem_wanted lieb_concavity {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    ConcaveOn ℝ {A : Matrix n n ℂ | A.PosDef}
      (fun A => RCLike.re (NormedSpace.exp (H + cfc Real.log A)).trace)

end MathlibExt.LinearAlgebra.Matrix.LiebConcavityWanted
