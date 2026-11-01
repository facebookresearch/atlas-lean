/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.PopulationGenetics.HudsonKaplan
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

@[expose] public section

open Cslib.Bioinformatics.PopulationGenetics.HudsonKaplan

namespace CSLibExtTest.Bioinformatics.PopulationGenetics.HudsonKaplan

/-! ### All four gametes at two sites (non-vacuity witness)

Haplotypes `00, 01, 10, 11`: the single pair `(0, 1)` shows all four gametes, so `R_m = 1`. -/

/-- Four haplotypes at two sites carrying all four gametes. -/
def M₁ : Fin 4 → Fin 2 → Bool := ![![false, false], ![false, true], ![true, false], ![true, true]]

example : FourGametes M₁ 0 1 := by decide
example : rm M₁ = 1 := by decide +kernel
example : sweep M₁ = [(0, 1)] := by decide +kernel

/-- A valid breakpoint set: one cut just left of site `1`. -/
example : IsBreakpointSet M₁ {1} := by
  intro i j hij h
  exact ⟨1, by simp, by fin_cases i <;> fin_cases j <;> simp_all [Separates]⟩

/-- No valid breakpoint set is empty. -/
example (B : Finset (Fin 2)) (hB : IsBreakpointSet M₁ B) : 1 ≤ B.card := by
  have := rm_le_card_of_isBreakpointSet M₁ hB
  rwa [show rm M₁ = 1 by decide +kernel] at this

/-! ### Three adjacent conflicts

Haplotypes `0000, 0110, 1011, 1101`: the pairs `(0,1)`, `(1,2)`, `(2,3)` show all four gametes
and are pairwise disjoint, so `R_m = 3`; the sweep keeps exactly them. -/

/-- Row `0000`. -/
def r₀ : Fin 4 → Bool := ![false, false, false, false]
/-- Row `0110`. -/
def r₁ : Fin 4 → Bool := ![false, true, true, false]
/-- Row `1011`. -/
def r₂ : Fin 4 → Bool := ![true, false, true, true]
/-- Row `1101`. -/
def r₃ : Fin 4 → Bool := ![true, true, false, true]
/-- Four haplotypes at four sites with three adjacent four-gamete pairs. -/
def M₂ : Fin 4 → Fin 4 → Bool := ![r₀, r₁, r₂, r₃]

example : rm M₂ = 3 := by decide +kernel
example : sweep M₂ = [(2, 3), (1, 2), (0, 1)] := by decide +kernel

/-! ### Overlapping conflicts: greedy picks the shortest

Haplotypes `000, 011, 101, 110`: every pair of the three sites shows all four gametes; the
intervals `(0,1)`, `(0,2)`, `(1,2)` pairwise overlap except `(0,1)` and `(1,2)`, so `R_m = 2`. -/

/-- Four haplotypes at three sites, all pairs four-gamete. -/
def M₃ : Fin 4 → Fin 3 → Bool :=
  ![![false, false, false], ![false, true, true], ![true, false, true], ![true, true, false]]

example : FourGametes M₃ 0 2 := by decide
example : rm M₃ = 2 := by decide +kernel

/-! ### Boundary cases -/

/-- A sample without recombination signal (nested clades `{2,3} ⊆ {1,2,3}`) has `R_m = 0`. -/
def M₄ : Fin 4 → Fin 2 → Bool := ![![false, false], ![false, true], ![true, true], ![true, true]]

example : ¬FourGametes M₄ 0 1 := by decide
example : rm M₄ = 0 := by decide +kernel

/-- No segregating sites: `R_m = 0`. -/
example : rm (fun (_ : Fin 3) (_ : Fin 0) => true) = 0 := by decide +kernel

end CSLibExtTest.Bioinformatics.PopulationGenetics.HudsonKaplan
