/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace MetaMathlibExt

@[expose] public section

/-- A rectangular real matrix has nonnegative minors when every finite square
submatrix selected by strictly increasing row and column maps has nonnegative
determinant. The quantification over all `k : ℕ` includes the `0 × 0` minor
(`k = 0`).

This rectangular-indexed predicate is named for its defining property rather
than as a second spelling of Mathlib's square-matrix total-nonnegativity API.

Source: Ming-Jian Ding and Jiang Zeng, "Some New Results on the Minuscule
Polynomials of Type A", Journal of Integer Sequences 28 (2025),
Article 25.1.2, "Total positivity of the coefficient matrix" section
(label `sec+TP`), definition at lines 638–639 (used by the
Schoenberg–Edrei lemma, label `lem+SE+PF`, line 654),
<https://cs.uwaterloo.ca/journals/JIS/VOL28/Zeng/zeng26.tex>. -/
public def Matrix.HasNonnegativeMinors {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (M : Matrix ι κ ℝ) : Prop :=
  ∀ (k : ℕ) (r : Fin k → ι) (c : Fin k → κ),
    StrictMono r → StrictMono c → 0 ≤ (M.submatrix r c).det

end

end MetaMathlibExt
