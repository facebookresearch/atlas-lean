/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.UniqueInfiniteComponent

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.UniqueInfiniteComponent`

Applies `unique_infinite_component` at `d = 2` to the removed set `F = {0}` and to the removed
box `[-1, 1]^2`, and at `d = 3` to `F = ∅`. Instantiates `box_exterior_connected` at `d = 2`,
`R = 0` for the sites `(1, 0)` and `(-1, 0)` (opposite sides of the origin), `finite_subset_box`
for a two-point set, and computes `exterior` and `beacon` at small inputs.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.UniqueInfiniteComponent

open _root_.StatMech _root_.StatMech.Lattice

-- `exterior 2 1` contains `(2, 0)` but not `(1, -1)`.
example : (![2, 0] : Site 2) ∈ exterior 2 1 := ⟨0, by simp⟩

example : (![1, -1] : Site 2) ∉ exterior 2 1 := by
  rintro ⟨i, hi⟩; fin_cases i <;> simp at hi

-- `beacon 2 3` is the site `(4, 4)`.
example : beacon 2 3 = ![4, 4] := by
  funext i; fin_cases i <;> simp [beacon]

-- `finite_subset_box`: the set `{(3, 0), (0, -5)}` lies in some box.
example : ∃ R : ℕ, ({![3, 0], ![0, -5]} : Set (Site 2)) ⊆ box 2 R :=
  finite_subset_box _ (Set.toFinite _)

-- `box_exterior_connected`: `(1, 0)` and `(-1, 0)` are joined outside the box `{0}`.
example : ((hypercubicLattice 2).induce (exterior 2 0)).Reachable
    ⟨![1, 0], ⟨0, by simp⟩⟩ ⟨![-1, 0], ⟨0, by simp⟩⟩ :=
  box_exterior_connected 0 le_rfl _ _ _ _

-- `unique_infinite_component` for `ℤ²` minus the origin.
example : ∃! C : ((hypercubicLattice 2).induce ({![0, 0]} : Set (Site 2))ᶜ).ConnectedComponent,
    C.supp.Infinite :=
  unique_infinite_component le_rfl _ (Set.finite_singleton _)

-- `unique_infinite_component` for `ℤ²` minus the box `[-1, 1]^2`.
example : ∃! C : ((hypercubicLattice 2).induce (box 2 1)ᶜ).ConnectedComponent, C.supp.Infinite :=
  unique_infinite_component le_rfl _ (box_finite 2 1)

-- `unique_infinite_component` for `ℤ³` with nothing removed.
example : ∃! C : ((hypercubicLattice 3).induce (∅ : Set (Site 3))ᶜ).ConnectedComponent,
    C.supp.Infinite :=
  unique_infinite_component (by norm_num) _ Set.finite_empty

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.UniqueInfiniteComponent
