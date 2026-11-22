/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.FvES

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.FvES`

On the triangle `⊤ : SimpleGraph (Fin 3)` with boundary `{0}`:
* `ConnToBdry` (decided) for an open and a closed configuration;
* the Edwards–Sokal one-point identity `esWiredOnePoint_eq_wiredConnToBdryProb` at `x = 2`,
  `p = 1/2`;
* its consequence at the boundary vertex: `⟨σ_0⟩⁺ = 1` for `0 < p < 1`, since every configuration
  connects `0` to the boundary and the wired measure has total mass one.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.FKRepresentation.FvES

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.IsingFK _root_.StatMech.Lattice

/-- The boundary `{0}` of the triangle. -/
def bdry0 (x : Fin 3) : Prop := x = 0

/-- Membership in the boundary is decidable. -/
instance : DecidablePred bdry0 := fun x => inferInstanceAs (Decidable (x = 0))

-- With every edge open, vertex `2` is connected to the boundary.
example : ConnToBdry (⊤ : SimpleGraph (Fin 3)) bdry0 (fun _ => true) 2 :=
  ⟨0, rfl, SimpleGraph.Adj.reachable ⟨by simp, rfl⟩⟩

-- With every edge closed, vertex `2` is not connected to the boundary.
example : ¬ ConnToBdry (⊤ : SimpleGraph (Fin 3)) bdry0 (fun _ => false) 2 := by
  decide

-- The Edwards–Sokal one-point identity at `x = 2`, `p = 1/2`.
example :
    esWiredOnePoint (⊤ : SimpleGraph (Fin 3)) bdry0 0 (1 / 2) 2 =
      wiredConnToBdryProb (⊤ : SimpleGraph (Fin 3)) bdry0 (1 / 2) 2 :=
  esWiredOnePoint_eq_wiredConnToBdryProb _ _ _ _ 0 rfl

-- At the boundary vertex the plus-boundary magnetization is `1`.
example {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    esWiredOnePoint (⊤ : SimpleGraph (Fin 3)) bdry0 0 p 0 = 1 := by
  rw [esWiredOnePoint_eq_wiredConnToBdryProb (⊤ : SimpleGraph (Fin 3)) bdry0 p 0 0 rfl,
    wiredConnToBdryProb]
  rw [Finset.filter_true_of_mem fun ω _ => ⟨0, rfl, SimpleGraph.Reachable.refl _⟩]
  exact bcProb_sum_eq_one _ _ hp hp1 (by norm_num)

end PhyslibExtTest.CondensedMatter.IsingModel.FKRepresentation.FvES
