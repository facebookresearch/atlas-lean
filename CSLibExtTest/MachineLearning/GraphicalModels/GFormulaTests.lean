/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.GFormula
import Mathlib.Tactic.NormNum

/-!
# Tests for the g-formula

Table 21.1 of Hernán and Robins, *Causal Inference: What If* (§21.1, p. 271, revision of
2 January 2025): 32,000 individuals with treatments `A₀, A₁` and a covariate `L₁`, with no
baseline covariate (encoded as a constant `L₀`). The g-formula is `60` under "never treat" and
under "always treat", the values computed on p. 272.
-/

@[expose] public section

namespace Cslib.MachineLearning.GFormulaTests

open Finset MathlibExt.Probability.FiniteProbability
open Cslib.MachineLearning.GraphicalModels Cslib.MachineLearning.GraphicalModels.GFormula

/-- Table 21.1 of *What If* (p. 271) as an observed model on `Ω = A₀ × L₁ × A₁`: the weights are
the cell counts divided by `32000`, and `Y` is the mean outcome of the cell. -/
noncomputable def table211 : ObsModel (Bool × Bool × Bool) Bool Bool 1 where
  p ω := (if ω.1 then (if ω.2.1 then (if ω.2.2 then 6400 else 1600)
              else (if ω.2.2 then 3200 else 4800))
          else (if ω.2.1 then (if ω.2.2 then 9600 else 2400)
              else (if ω.2.2 then 1600 else 2400))) / 32000
  L k ω := if k = 0 then false else ω.2.1
  A k ω := if k = 0 then ω.1 else ω.2.2
  Y ω := if ω.1 then (if ω.2.1 then 44 else 76) else (if ω.2.1 then 52 else 84)

/-- The g-formula under "never treat" is `60` (*What If*, p. 272: `84 × 0.25 + 52 × 0.75`). -/
theorem table211_never : table211.gFormula (fun _ => false) = 60 := by
  rw [ObsModel.gFormula, sum_snoc, sum_snoc, Fintype.sum_unique]
  simp [ObsModel.condL, cmean, prob, table211, Fintype.sum_prod_type, Finset.sum_filter,
    Fin.forall_fin_two, Fin.prod_univ_two, Fin.snoc]
  norm_num

/-- The g-formula under "always treat" is `60` (*What If*, p. 272: `76 × 0.50 + 44 × 0.50`). -/
theorem table211_always : table211.gFormula (fun _ => true) = 60 := by
  rw [ObsModel.gFormula, sum_snoc, sum_snoc, Fintype.sum_unique]
  simp [ObsModel.condL, cmean, prob, table211, Fintype.sum_prod_type, Finset.sum_filter,
    Fin.forall_fin_two, Fin.prod_univ_two, Fin.snoc]
  norm_num

end Cslib.MachineLearning.GFormulaTests
