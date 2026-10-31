/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OriginTrifurcationRewiring

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OriginTrifurcationRewiring`

* `bc12_isolated_origin_not_trifurcation`: in the all-closed configuration of `ℤ²` the origin is
  not a canonical trifurcation (instance).
* `bc12_canonicalTrif_discharges_boxReach` as a conditional statement, and
  `bc12_BoxOriginTrifurcation` unfolds to a canonical trifurcation on `threeMeetBox`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.OriginTrifurcationRewiring

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

-- An isolated origin is not a canonical trifurcation.
example : ¬ IsCanonicalTrifurcation 2 (fun _ => false) 0 :=
  bc12_isolated_origin_not_trifurcation _ fun v h => by simp at h

-- A canonical trifurcation gives three origin connections after forcing edges away from it.
example (ω : ConfigSpace (Sym2 (Site 2))) (h : IsCanonicalTrifurcation 2 ω 0) :
    ∃ W : Finset (Sym2 (Site 2)), (∀ e ∈ W, (0 : Site 2) ∉ e) ∧
      ∃ y₁ y₂ y₃ : Site 2, y₁ ≠ 0 ∧ y₂ ≠ 0 ∧ y₃ ≠ 0 := by
  obtain ⟨W, hW, y₁, y₂, y₃, h₁, h₂, h₃, -⟩ := bc12_canonicalTrif_discharges_boxReach ω h
  exact ⟨W, hW, y₁, y₂, y₃, h₁, h₂, h₃⟩

-- The box condition is a canonical trifurcation on each configuration of the event.
example (n : ℕ) (h : bc12_BoxOriginTrifurcation 2 n) (ω : ConfigSpace (Sym2 (Site 2)))
    (hω : ω ∈ threeMeetBox 2 n) : IsCanonicalTrifurcation 2 ω 0 :=
  h ω hω

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.OriginTrifurcationRewiring
