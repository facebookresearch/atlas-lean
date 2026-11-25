/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Asymptotics.NoncrossingChordDiagramNormalLimit
import Mathlib.Tactic.NormNum

/-! # Tests for the short-chord normal limit -/

open Filter Topology
open scoped BigOperators

namespace MathlibExtTest.Analysis.Asymptotics.NoncrossingChordDiagramNormalLimit

-- At the lower arity bound, the centering and scaling are those of the Narayana numbers.
example (T : ℕ → ℕ → ℕ)
    (hT : T 0 0 = 1 ∧
      (∀ ℓ, 0 < ℓ → T 0 ℓ = 0) ∧
      ∀ n ℓ,
        T (n + 1) ℓ =
          (∑ m : Fin 2 → Fin (n + 1),
            ∑ s : Fin 2 → Fin (ℓ + 1),
              if (∑ i, (m i : ℕ)) = n ∧ (∑ i, (s i : ℕ)) = ℓ then
                ∏ i, T (m i) (s i)
              else 0) - T n ℓ + if ℓ = 0 then 0 else T n (ℓ - 1))
    (t : ℝ) :
    Tendsto (fun n : ℕ =>
      (∑ ℓ ∈ Finset.range (n + 1), (T n ℓ : ℝ) *
        Real.exp (t * (((ℓ : ℝ) - (n : ℝ) / 2) / Real.sqrt ((n : ℝ) / 8)))) /
        ∑ ℓ ∈ Finset.range (n + 1), (T n ℓ : ℝ))
      atTop (nhds (Real.exp (t ^ 2 / 2))) := by
  have h := MetaMathlibExt.noncrossingLinearKChordDiagram_shortChords_asymptoticallyNormal
    (k := 2) (hk := by decide) (T := T) (hT := hT) t
  norm_num at h
  simpa [div_eq_mul_inv, mul_comm] using h

end MathlibExtTest.Analysis.Asymptotics.NoncrossingChordDiagramNormalLimit
