/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.CorrelationMonotone

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.CorrelationMonotone`

* `corr_monotone` on the triangle `⊤ : SimpleGraph (Fin 3)` at `h = 0` for the two-point function
  `⟨σ_0 σ_1⟩` (values at `β = 0` and `β = 1` compared) and at `h = 1` for the one-point function;
* `corr_deriv_nonneg`'s setting: the empty correlation `⟨σ_∅⟩ = 1` is constant in `β`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.FKRepresentation.CorrelationMonotone

open _root_.StatMech _root_.StatMech.Ising _root_.StatMech.IsingFK

-- The two-point function of the triangle at zero field increases from `β = 0` to `β = 1`.
example :
    isingExpectation (⊤ : SimpleGraph (Fin 3)) 0 0 (spinProd {0, 1}) ≤
      isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 0 (spinProd {0, 1}) :=
  corr_monotone _ 0 le_rfl {0, 1} (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr zero_le_one)
    zero_le_one

-- The one-point function at positive field is nondecreasing on `[0, ∞)`.
example :
    MonotoneOn (fun β => isingExpectation (⊤ : SimpleGraph (Fin 3)) β 1 (spinProd {2}))
      (Set.Ici 0) :=
  corr_monotone _ 1 zero_le_one {2}

-- The empty correlation is identically one.
example (β h : ℝ) :
    isingExpectation (⊤ : SimpleGraph (Fin 3)) β h (spinProd ∅) = 1 := by
  simp [isingExpectation, isingProb_sum_eq_one]

end PhyslibExtTest.CondensedMatter.IsingModel.FKRepresentation.CorrelationMonotone
