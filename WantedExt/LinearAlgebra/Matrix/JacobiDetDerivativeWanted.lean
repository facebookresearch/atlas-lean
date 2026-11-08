/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open scoped Matrix.Norms.Elementwise

namespace MathlibExt.LinearAlgebra.Matrix.JacobiDetDerivativeWanted

variable {n : Type*} [Fintype n] [DecidableEq n]

/--
Jacobi's formula for the derivative of the determinant: the derivative of `t ↦ det (A t)`
along a differentiable curve of square real matrices equals the trace of the adjugate times
the derivative, `d/dt det A = tr (adj A * dA/dt)`.

Sources: Mathlib repository, `docs/undergrad.yaml` (the undergraduate curriculum list),
section "Multivariable calculus" / "differentials";
R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge Univ. Press, 2013, §0.8.10;
https://en.wikipedia.org/wiki/Jacobi%27s_formula
-/
public theorem_wanted jacobi_det_derivative
    (A : ℝ → Matrix n n ℝ) (t : ℝ) (hA : DifferentiableAt ℝ A t) :
    deriv (fun t => Matrix.det (A t)) t
      = Matrix.trace (Matrix.adjugate (A t) * deriv A t)

end MathlibExt.LinearAlgebra.Matrix.JacobiDetDerivativeWanted
