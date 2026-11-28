/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The secant criterion for diagonal stability of cyclic matrices

For `n ≥ 3` and positive `α_1, …, α_n`, `β_1, …, β_n`, let `A` be the `n × n` matrix of a
negative feedback cycle: diagonal entries `-α_i`, subdiagonal entries `A_{i+1,i} = β_i` for
`i = 1, …, n - 1`, the corner entry `A_{1n} = -β_n`, and zeros elsewhere. A matrix is diagonally
stable if `D A + Aᵀ D` is negative definite for some diagonal matrix `D` with positive diagonal.

**Theorem 1** (Arcak–Sontag 2006). The matrix `A` is diagonally stable if and only if the secant
condition `(β_1 ⋯ β_n)/(α_1 ⋯ α_n) < sec(π/n)^n` holds.

The source states no range for `n`; for `n = 2`, `sec(π/2)` is undefined (and such matrices are
diagonally stable for all positive parameters), and for `n = 1` the form degenerates, so the
theorem is stated for `n ≥ 3`. The source's further results (global stability of cyclic
interconnections of output strictly passive systems, and the application to cyclic biochemical
feedback systems) are not stated here. With `sec(π/n) = 1/cos(π/n)`, the condition reads
`∏ β_i < (∏ α_i)/cos(π/n)^n`.

Sources: M. Arcak, E. D. Sontag, "Diagonal stability of a class of cyclic systems and its
connection with the secant criterion", Automatica 42 (2006) 1531–1537, matrix (2), condition (3),
Theorem 1.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Data.Fintype.Fin

@[expose] public section

namespace WantedExt.Biology.Biophysics.SecantCriterionWanted

open Matrix

/-- The cyclic matrix of a negative feedback loop of length `n + 1`: diagonal entries `-α i`,
subdiagonal entries `β i` in position `(i + 1, i)` for `i < n`, the corner entry `-β n` in
position `(0, n)`, and zeros elsewhere. When `n = 0` (size `1 × 1`), the diagonal and corner
positions coincide and the diagonal entry `-α 0` takes precedence; the secant criterion requires
`n + 1 ≥ 3`. -/
noncomputable def cyclicMatrix {n : ℕ} (α β : Fin (n + 1) → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j =>
    if i = j then -α i
    else if (i : ℕ) = j + 1 then β j
    else if (i : ℕ) = 0 ∧ (j : ℕ) = n then -β j
    else 0

/-- `A` is diagonally stable: there is `d` with all entries positive such that
`diag(d) A + Aᵀ diag(d)` is negative definite. -/
def IsDiagonallyStable {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix m m ℝ) : Prop :=
  ∃ d : m → ℝ, (∀ i, 0 < d i) ∧ (-(diagonal d * A + Aᵀ * diagonal d)).PosDef

/-- **Secant criterion** (Arcak–Sontag 2006, Theorem 1). Let `m = n + 1 ≥ 3` and let `α`, `β`
(indexed by `Fin m`) have all entries positive. The cyclic matrix with diagonal entries `-α_i`,
subdiagonal entries `β_i` and corner entry `-β_{m-1}` is diagonally stable if and only if
`(∏_i β_i)/(∏_i α_i) < sec(π/m)^m`, written as `(∏_i β_i)/(∏_i α_i) < (1/cos(π/m))^m`.

Source: M. Arcak and E. D. Sontag, "Diagonal stability of a class of cyclic systems and its
connection with the secant criterion", Automatica 42 (2006) 1531–1537, Theorem 1,
doi:10.1016/j.automatica.2006.04.009. -/
theorem_wanted isDiagonallyStable_cyclicMatrix_iff {n : ℕ} (hn : 2 ≤ n)
    {α β : Fin (n + 1) → ℝ} (hα : ∀ i, 0 < α i) (hβ : ∀ i, 0 < β i) :
    IsDiagonallyStable (cyclicMatrix α β) ↔
      (∏ i, β i) / (∏ i, α i) < (1 / Real.cos (Real.pi / (n + 1))) ^ (n + 1)

end WantedExt.Biology.Biophysics.SecantCriterionWanted
