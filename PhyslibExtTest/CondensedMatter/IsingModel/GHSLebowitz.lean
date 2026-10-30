/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.GHSLebowitz

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.GHSLebowitz`

On the triangle `⊤ : SimpleGraph (Fin 3)`:
* `ghsL_threePoint` at `β = 1/2`, `h = 1/4` and `o = 0` gives the predicate `GHSThreePointSym`;
* unfolded at the edge `{1, 2}` not containing `o`, it is the GHS inequality
  `⟨σ_0 σ_1 σ_2⟩ - ⟨σ_0⟩⟨σ_1 σ_2⟩ ≤ cov(σ_0, σ_1)⟨σ_2⟩ + cov(σ_0, σ_2)⟨σ_1⟩`, i.e. `u₃(0, 1, 2) ≤ 0`;
* the predicate also holds at the boundary values `β = 0`, `h = 0`, for every site `o`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.GHSLebowitz

open _root_.StatMech _root_.StatMech.Ising

/-- The triangle, the complete graph on three vertices. -/
abbrev triangle : SimpleGraph (Fin 3) := ⊤

-- The GHS predicate holds at `o = 0` for `β = 1/2`, `h = 1/4`.
example : GHSThreePointSym triangle (1 / 2) (1 / 4) 0 :=
  ghsL_threePoint triangle (1 / 2) (1 / 4) (by norm_num) (by norm_num) 0

-- Unfolded at the edge `{1, 2}`: the third Ursell function `u₃(0, 1, 2)` is nonpositive.
example :
    isingExpectation triangle (1 / 2) (1 / 4) (fun s => spin s 0 * (spin s 1 * spin s 2))
        - isingExpectation triangle (1 / 2) (1 / 4) (fun s => spin s 0)
          * isingExpectation triangle (1 / 2) (1 / 4) (fun s => spin s 1 * spin s 2)
      ≤ cov2 triangle (1 / 2) (1 / 4) 0 1 * onePt triangle (1 / 2) (1 / 4) 2
        + cov2 triangle (1 / 2) (1 / 4) 0 2 * onePt triangle (1 / 2) (1 / 4) 1 := by
  have h := ghsL_threePoint triangle (1 / 2) (1 / 4) (by norm_num) (by norm_num) 0 s(1, 2)
    (by simp)
  simpa only [cov3sym_mk, ghsBoundSym_mk] using h

-- The GHS predicate at infinite temperature and zero field.
example (o : Fin 3) : GHSThreePointSym triangle 0 0 o :=
  ghsL_threePoint triangle 0 0 le_rfl le_rfl o

end PhyslibExtTest.CondensedMatter.IsingModel.GHSLebowitz
