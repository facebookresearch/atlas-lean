/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.ThreePointSplitMass

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.ThreePointSplitMass`

On `Fin 3` with the complete graph:
* `hnw_mass_nonneg` at `β = 0`, `J = 0` for the zero current;
* `hnw_ghs_distinct_site_of_hdom` and `hnw_inclusion_exclusion_decomp` applied to the empty
  family `M = ∅`, which satisfies the coherence and domination hypotheses (the hypotheses are
  satisfiable);
* `hnw_noneConn_not_allConn`: the two connectivity patterns are exclusive.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.ThreePointSplitMass

open _root_.StatMech _root_.StatMech.Ising
open scoped symmDiff

-- The split mass is nonnegative.
example : 0 ≤ hnw_mass (⊤ : SimpleGraph (Fin 3)) 0 (fun _ => 0) (fun _ => 0) ∅ :=
  hnw_mass_nonneg _ 0 _ le_rfl (fun _ => le_rfl) _ _

-- The three-point inequality holds for the empty family.
example :
    ∑ m ∈ (∅ : Finset (Current (Fin 3))), hnw_mass ⊤ 1 (fun _ => 1) m ({0, 1} ∆ {1, 2}) +
        ∑ m ∈ (∅ : Finset (Current (Fin 3))), hnw_mass ⊤ 1 (fun _ => 1) m ({0, 1} ∆ {0, 2}) +
        ∑ m ∈ (∅ : Finset (Current (Fin 3))), hnw_mass ⊤ 1 (fun _ => 1) m ({0, 1} ∆ {0, 1}) ≤
      ∑ m ∈ (∅ : Finset (Current (Fin 3))), hnw_mass ⊤ 1 (fun _ => 1) m {0, 1} :=
  hnw_ghs_distinct_site_of_hdom ⊤ 1 _ ∅ (by simp) _ (by simp) (o := 0) (x := 1) (y := 2)
    (by decide) (by decide) (by decide) (by simp) (by simp)

-- The inclusion–exclusion identity for the empty family.
open Classical in
example :
    ∑ m ∈ (∅ : Finset (Current (Fin 3))), hnw_gap ⊤ 1 (fun _ => 1) m ∅ 0 1 2 =
      ∑ m ∈ (∅ : Finset (Current (Fin 3))) with hnw_noneConn ⊤ m 0 1 2,
          hnw_mass ⊤ 1 (fun _ => 1) m ∅ -
        2 * ∑ m ∈ (∅ : Finset (Current (Fin 3))) with hnw_allConn ⊤ m 0 1 2,
          hnw_mass ⊤ 1 (fun _ => 1) m ∅ := by
  exact hnw_inclusion_exclusion_decomp ⊤ 1 _ ∅ (by simp) _ (by simp) (o := 0) (x := 1) (y := 2)
    (by decide) (by decide) (by decide) (by simp)

-- No current is both "none connected" and "all connected".
example (m : Current (Fin 3)) (h : hnw_noneConn ⊤ m 0 1 2) : ¬ hnw_allConn ⊤ m 0 1 2 :=
  hnw_noneConn_not_allConn _ m h

end PhyslibExtTest.CondensedMatter.IsingModel.ThreePointSplitMass
