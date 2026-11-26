/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.SidorenkoConjecture

namespace MathlibExtTest.Combinatorics.SimpleGraph.SidorenkoConjecture

open MathlibExt.Combinatorics.SimpleGraph.GraphLimits
open MathlibExt.Combinatorics.SimpleGraph.SidorenkoConjectureWanted
open MeasureTheory

-- A constant graphon attains the bound, including at edge densities zero and one.
example (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    graphonHomDensity (SimpleGraph.cycleGraph 4) (fun _ _ => p) = p ^ 4 := by
  have hedge : graphonHomDensity (⊤ : SimpleGraph (Fin 2)) (fun _ _ => p) = p := by
    simp (config := { decide := true }) [graphonHomDensity, Fin.prod_univ_two,
      measureReal_def, Real.volume_Icc_pi]
  apply le_antisymm
  · simp (config := { decide := true }) only [graphonHomDensity, Fin.prod_univ_four,
      ↓reduceIte, one_mul, mul_one, setIntegral_const, smul_eq_mul, measureReal_def]
    simp [Real.volume_Icc_pi, pow_succ, mul_assoc]
  · simpa only [hedge] using graphonHomDensity_cycleGraph_four_ge
      ⟨measurable_const, fun _ _ => rfl, fun _ _ => hp⟩

end MathlibExtTest.Combinatorics.SimpleGraph.SidorenkoConjecture
