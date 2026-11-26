/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.FinitePatternEnergy

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.FinitePatternEnergy`

On the one-edge graph `⊤` on `Fin 2` at `p = 1/2`, `q = 2`, with the pattern "the edge `s(0, 1)` is
open" on `I = {s(0, 1)}`:
* `setPattern_of_mem` (`simp`) and `setPattern_mem_patternEvent`;
* `cFE_pow_le_condBcProb_pattern` for the empty wiring and the all-closed exterior;
* `cFE_pow_mul_event_le_pattern_inter` for the outside event `setPattern I η ⁻¹' A`
  (outside-dependence from `dependsOnOutside_preimage_setPattern`);
* `cFE_pow_mul_bcPreimage_le_event` for the event "the edge is open".
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.FinitePatternEnergy

open _root_.StatMech _root_.StatMech.FK

/-- The one-edge test graph. -/
abbrev G2 : SimpleGraph (Fin 2) := ⊤

/-- The pattern set: the single edge `s(0, 1)`. -/
def I1 : Finset (Sym2 (Fin 2)) := {s(0, 1)}

/-- The all-open pattern on `I1`. -/
def η1 : ConfigSpace ↥I1 := fun _ => true

-- The pattern is imposed on `I1`, and the result lies in the pattern event.
example (ψ : ConfigSpace (Sym2 (Fin 2))) :
    setPattern I1 η1 ψ s(0, 1) = true ∧ setPattern I1 η1 ψ ∈ patternEvent I1 η1 :=
  ⟨setPattern_of_mem η1 (Finset.mem_singleton_self _) ψ, setPattern_mem_patternEvent I1 η1 ψ⟩

-- Conditional finite energy for the pattern given the all-closed exterior.
example : cFE (1 / 2) 2 ^ I1.card ≤
    ∑ ω, (patternEvent I1 η1).indicator (fun _ => (1 : ℝ)) ω *
      condBcProb G2 ⊥ (1 / 2) 2 I1 (fun _ => false) ω :=
  cFE_pow_le_condBcProb_pattern G2 ⊥ (by norm_num) (by norm_num) one_le_two _ _ _

-- Finite energy for the intersection of the pattern with an outside event.
example (A : Set (ConfigSpace (Sym2 (Fin 2)))) :=
  cFE_pow_mul_event_le_pattern_inter G2 (p := 1 / 2) (q := 2) (by norm_num) (by norm_num)
    one_le_two I1 η1 _ (dependsOnOutside_preimage_setPattern I1 η1 A)

-- Forcing the pattern costs at most `cFE ^ |I|`.
example : cFE (1 / 2) 2 ^ I1.card *
      (∑ ω, (setPattern I1 η1 ⁻¹' {ω | ω s(0, 1) = true}).indicator (fun _ => (1 : ℝ)) ω *
        bcProb G2 ⊥ (1 / 2) 2 ω) ≤
    ∑ ω, ({ω | ω s(0, 1) = true} : Set _).indicator (fun _ => (1 : ℝ)) ω *
      bcProb G2 ⊥ (1 / 2) 2 ω :=
  cFE_pow_mul_bcPreimage_le_event G2 ⊥ (by norm_num) (by norm_num) one_le_two _ _ _

end PhyslibExtTest.StatisticalMechanics.RandomCluster.FinitePatternEnergy
