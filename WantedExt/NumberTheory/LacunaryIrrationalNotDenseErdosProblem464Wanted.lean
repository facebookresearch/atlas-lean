/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Irrational multiples of lacunary sequences avoiding density (Erdős Problem 464)

Erdős Problem 464: let `n₁ < n₂ < ⋯` be lacunary (`n_{k+1} ≥ (1 + ε) n_k`). Must there be an
irrational `θ` such that `{‖θ n_k‖ : k ≥ 1}` is not dense, `‖x‖` being the distance to the nearest
integer?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Real.Irrational

@[expose] public section

namespace MathlibExt.NumberTheory.LacunaryIrrationalNotDenseErdosProblem464Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #464, https://www.erdosproblems.com/464 (status PROVED
(LEAN)). UnsolvedMath record UM-30006883 (`EP-464`), dataset ulamai/UnsolvedMath v1.8.0.

The page says "not dense in `[0, 1]`", which would hold for every `θ` since `‖x‖ ≤ 1/2`; the target
uses `[0, 1/2]`, the range of `‖·‖`. `‖x‖` is `|x - round x|`; the sequence has positive terms.
formal-conjectures (`ErdosProblems/464.lean`) states that `θ n_k` is not dense modulo `1`, which the
target implies (if `‖θ n_k‖` avoids an interval `(u, v)`, then `θ n_k` modulo `1` avoids `(u, v)`);
no code imported.
-/

/-- Erdős Problem 464: for every lacunary sequence `n₁ < n₂ < ⋯` of positive integers
(`n_(k+1) ≥ (1 + ε) n_k`) there is an irrational `θ` such that the distances `‖θ n_k‖` to the
nearest integer are not dense in `[0, 1/2]`. -/
def lacunaryIrrationalNotDense : Prop :=
  ∀ n : ℕ → ℕ, (∀ k, 0 < n k) → (∃ ε : ℝ, 0 < ε ∧ ∀ k, (1 + ε) * n k ≤ n (k + 1)) →
    ∃ θ : ℝ, Irrational θ ∧
      ¬ Set.Icc (0 : ℝ) (1 / 2) ⊆ closure (Set.range fun k => |θ * n k - round (θ * n k)|)

/--
Resolved true: de Mathan and Pollington independently proved that for every such sequence there is
an irrational `θ` with `inf_k ‖θ n_k‖ ≫ ε⁴ / log(1/ε)`, so the values `‖θ n_k‖` stay away from `0`
and are not dense in `[0, 1/2]`; Peres and Schlag improved the bound to `≫ ε / log(1/ε)`
(erdosproblems.com/464). Source: T. F. Bloom, Erdős Problems, Problem #464,
https://www.erdosproblems.com/464 (status PROVED (LEAN)); resolution: A. D. Pollington, On the
density of sequence {n_k ξ}, Illinois J. Math. (1979), 511-515; B. de Mathan, Numbers contravening a
condition in density modulo 1, Acta Math. Acad. Sci. Hungar. (1980), 237-241, some irrational θ has
inf_k ‖θ n_k‖ ≫ ε⁴ / log(1/ε) (erdosproblems.com/464).
-/
public theorem_wanted lacunaryIrrationalNotDense_holds : lacunaryIrrationalNotDense

end MathlibExt.NumberTheory.LacunaryIrrationalNotDenseErdosProblem464Wanted
