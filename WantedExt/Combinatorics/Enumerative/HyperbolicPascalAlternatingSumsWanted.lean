/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Basic.Complex.Basic

/-!
# Alternating sums in the generalized hyperbolic Pascal triangle

Statements from Hacène Belbachir, Fella Rami, and László Szalay, *Alternating Sums in the
Generalized Hyperbolic Pascal Triangle*, INTEGERS 24 (2024), Article A84: the identity
relating a linear recurrence `f` and an inhomogeneous recurrence `G` with the same
coefficients (Theorem 1, Corollary 1, quoted from the authors' earlier paper), and the
weighted alternating row sums of the generalized hyperbolic Pascal triangle linked to the
mosaic `{4, q}` (Corollary 2).

The recurrence (10) for the alternating row sums (Theorem 2), its generating function
(Theorem 3) and explicit formula (Theorem 4) are not stated: they fail for simple leg
sequences (see the audit table).
-/

namespace MetaMathlibExt

@[expose] public section

/-- One step of the generalized hyperbolic Pascal triangle, without the two winger elements:
for a row `v₀, v₁, …, v_m` of (type, value) pairs, consecutive entries `v_{i-1}, v_i` produce a
type-`A` vertex (code `1`) with value `v_{i-1} + v_i`, and each interior entry `v_i`
(`0 < i < m`) then produces its type-`B` descendants (code `2`) with its value: `q - 4` of them
for a type-`A` vertex and `q - 3` for a type-`B` vertex. Wingers have code `0`.

Source: Hacène Belbachir, Fella Rami, and László Szalay, *Alternating Sums in the Generalized
Hyperbolic Pascal Triangle*, INTEGERS 24 (2024), Article A84, Section 1 (construction of the
triangle linked to `{4, q}`). -/
def ghptInterior {R : Type*} [Add R] (q : ℕ) : List (ℕ × R) → List (ℕ × R)
  | u :: v :: [] => [(1, u.2 + v.2)]
  | u :: v :: w :: rest =>
    (1, u.2 + v.2) :: (List.replicate (if v.1 = 1 then q - 4 else q - 3) (2, v.2) ++
      ghptInterior q (v :: w :: rest))
  | _ => []

/-- Row `n ≥ 1` of the generalized hyperbolic Pascal triangle linked to `{4, q}` with leg
sequences `α` (left) and `β` (right), as (type, value) pairs from left to right: row `1` is
`α₁, β₁`, and row `n + 1` is `α_{n+1}`, the interior step applied to row `n`, then `β_{n+1}`.
Row `0` (the indeterminate root `Ω`) is represented by the empty list.

Source: Hacène Belbachir, Fella Rami, and László Szalay, *Alternating Sums in the Generalized
Hyperbolic Pascal Triangle*, INTEGERS 24 (2024), Article A84, Section 1 (construction of the
triangle linked to `{4, q}`, Figure 1). -/
def ghptRow {R : Type*} [Add R] (q : ℕ) (α β : ℕ → R) : ℕ → List (ℕ × R)
  | 0 => []
  | 1 => [(0, α 1), (0, β 1)]
  | n + 2 => (0, α (n + 2)) :: (ghptInterior q (ghptRow q α β (n + 1)) ++ [(0, β (n + 2))])

/-- Rows `3` and `4` of Figure 1 (`q = 5`, `αₙ = 3n`, `βₙ = 3ⁿ`): `9, 12, 6, 15, 27` and
`12, 21, 12, 18, 6, 6, 21, 15, 42, 81`.

Source: Hacène Belbachir, Fella Rami, and László Szalay, *Alternating Sums in the Generalized
Hyperbolic Pascal Triangle*, INTEGERS 24 (2024), Article A84, Figure 1. -/
theorem ghptRow_figure_one :
    (ghptRow 5 (fun n => 3 * n) (fun n => 3 ^ n) 3).map Prod.snd = [9, 12, 6, 15, 27] ∧
      (ghptRow 5 (fun n => 3 * n) (fun n => 3 ^ n) 4).map Prod.snd =
        [12, 21, 12, 18, 6, 6, 21, 15, 42, 81] := by
  decide +kernel

/-- **Theorem 1** (quoted from Belbachir–Rami–Szalay 2022). Let `f` satisfy
`f_n = A_1 f_{n-1} + ⋯ + A_k f_{n-k}` and `G` satisfy
`G_n = A_1 G_{n-1} + ⋯ + A_k G_{n-k} + w_{n-k}` for `n ≥ k`. Then for `n ≥ k`,
`∑_{j<k} f_j G_{n+k-j} = ∑_{j<k} ∑_{i<k-j} f_{n-j} A_{j+1+i} G_{k-1-i}
  + ∑_{j<k-1} ∑_{i=1}^{k-1-j} f_j A_i G_{n+k-j-i} + ∑_{j=0}^{n} f_{n-j} w_j`.
The paper's `A_k ≠ 0` and `k ≥ 1` are not needed.

Source: Hacène Belbachir, Fella Rami, and László Szalay, *Alternating Sums in the Generalized
Hyperbolic Pascal Triangle*, INTEGERS 24 (2024), Article A84, Theorem 1
(`integers-2024-A84-thm-1`). -/
public theorem_wanted linearRecurrence_inhomogeneous_identity (k : ℕ) (A f G w : ℕ → ℂ)
    (hf : ∀ n, k ≤ n → f n = ∑ i ∈ Finset.Icc 1 k, A i * f (n - i))
    (hG : ∀ n, k ≤ n → G n = ∑ i ∈ Finset.Icc 1 k, A i * G (n - i) + w (n - k))
    {n : ℕ} (hn : k ≤ n) :
    ∑ j ∈ Finset.range k, f j * G (n + k - j) =
      ∑ j ∈ Finset.range k, ∑ i ∈ Finset.range (k - j), f (n - j) * A (j + 1 + i) * G (k - 1 - i) +
        ∑ j ∈ Finset.range (k - 1), ∑ i ∈ Finset.Icc 1 (k - 1 - j),
          f j * A i * G (n + k - j - i) +
        ∑ j ∈ Finset.range (n + 1), f (n - j) * w j

/-- **Corollary 1.** If moreover `f_0 = ⋯ = f_{k-2} = 0` and `f_{k-1} = 1`, then
`G_{n+1} = ∑_{j<k} ∑_{i<k-j} f_{n-j} A_{j+1+i} G_{k-1-i} + ∑_{j=0}^{n} f_{n-j} w_j`.
Stated for `n ≥ k - 1` (the paper: `n ≥ k`, from Theorem 1).

Source: Hacène Belbachir, Fella Rami, and László Szalay, *Alternating Sums in the Generalized
Hyperbolic Pascal Triangle*, INTEGERS 24 (2024), Article A84, Corollary 1
(`integers-2024-A84-cor-1`). -/
public theorem_wanted linearRecurrence_inhomogeneous_explicit (k : ℕ) (A f G w : ℕ → ℂ)
    (hf : ∀ n, k ≤ n → f n = ∑ i ∈ Finset.Icc 1 k, A i * f (n - i))
    (hG : ∀ n, k ≤ n → G n = ∑ i ∈ Finset.Icc 1 k, A i * G (n - i) + w (n - k))
    (hf₀ : ∀ j, j + 1 < k → f j = 0) (hf₁ : f (k - 1) = 1) {n : ℕ} (hn : k ≤ n + 1) :
    G (n + 1) =
      ∑ j ∈ Finset.range k, ∑ i ∈ Finset.range (k - j), f (n - j) * A (j + 1 + i) * G (k - 1 - i) +
        ∑ j ∈ Finset.range (n + 1), f (n - j) * w j

/-- **Corollary 2.** Weighting the entries of row `n` alternately by `v` (even positions) and `w`
(odd positions) gives `s̃_{(v,w),n} = (ŝ_n + s̃_n)/2 · v + (ŝ_n - s̃_n)/2 · w
= (v + w)/2 · ŝ_n + (v - w)/2 · s̃_n`, where `ŝ_n` is the row sum and `s̃_n` the alternating
row sum. Stated for every `q` and `n` (the identity does not use the row structure).

Source: Hacène Belbachir, Fella Rami, and László Szalay, *Alternating Sums in the Generalized
Hyperbolic Pascal Triangle*, INTEGERS 24 (2024), Article A84, Corollary 2
(`integers-2024-A84-cor-2`). -/
public theorem_wanted ghptRow_weighted_alternating_sum (q n : ℕ) (α β : ℕ → ℂ) (v w : ℂ) :
    let r := (ghptRow q α β n).map Prod.snd
    let alt := (r.mapIdx fun i x => (-1) ^ i * x).sum
    let weighted := (r.mapIdx fun i x => (if Even i then v else w) * x).sum
    weighted = (r.sum + alt) / 2 * v + (r.sum - alt) / 2 * w ∧
      weighted = (v + w) / 2 * r.sum + (v - w) / 2 * alt

end

end MetaMathlibExt
