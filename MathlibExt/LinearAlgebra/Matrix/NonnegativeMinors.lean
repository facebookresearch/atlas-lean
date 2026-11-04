/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Matrices with nonnegative minors.** Let $\iota$ and $\kappa$ be linearly ordered types and
let $M$ be a real matrix with rows indexed by $\iota$ and columns indexed by $\kappa$. Then $M$
has nonnegative minors when, for every $k \in \mathbb{N}$ and all strictly increasing maps
$r \colon \{0, \dots, k-1\} \to \iota$ and $c \colon \{0, \dots, k-1\} \to \kappa$, the
$k \times k$ submatrix $(M_{r(a), c(b)})_{a, b < k}$ has nonnegative determinant. The case
$k = 0$, the empty minor, is included.

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
