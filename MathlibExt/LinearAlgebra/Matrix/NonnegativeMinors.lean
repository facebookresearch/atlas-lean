/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyNonneg

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

/-- **Bridge to Mathlib's total nonnegativity.** For a square real matrix indexed by a linearly
ordered type, `Matrix.HasNonnegativeMinors` is Mathlib's `Matrix.IsTotallyNonneg`: both say that
every minor with strictly increasing row and column maps has nonnegative determinant (Fomin and
Zelevinsky, *Total positivity: tests and parametrizations*, Math. Intelligencer 22 (2000),
arXiv:math/9912128v1, Introduction: a matrix is totally nonnegative if all its minors are
nonnegative). -/
public theorem Matrix.hasNonnegativeMinors_iff_isTotallyNonneg {ι : Type*} [LinearOrder ι]
    (M : Matrix ι ι ℝ) : Matrix.HasNonnegativeMinors M ↔ M.IsTotallyNonneg :=
  ⟨fun h _ _ _ hr hc => h _ _ _ hr hc, fun h _ _ _ hr hc => h hr hc⟩

end

end MetaMathlibExt
