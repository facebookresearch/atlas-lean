/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.CWComplex.Classical.Basic
public import MathlibExt.Topology.Category.TopPair.ClosedBall

/-!
# Canonical characteristic disks of a classical CW complex

Restrict the given classical characteristic map to its existing closed disk.
The canonical definition is shared by realization and attachment APIs.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology

universe u

namespace Topology.CWComplex

variable {X : TopCat.{u}} [CWComplex (Set.univ : Set X)]

/-- The actual characteristic map on the closed disk of a classical cell. -/
def characteristicDiskMap (n : ℕ) (j : cell (Set.univ : Set X) n) :
    (classicalCellDiskPair.{u} n).fst ⟶ X :=
  TopCat.ofHom
    ⟨fun x => map n j x.down.val,
      (continuousOn n j).domRestrict.comp continuous_uliftDown⟩

@[simp]
theorem characteristicDiskMap_apply (n : ℕ) (j : cell (Set.univ : Set X) n)
    (x : (classicalCellDiskPair.{u} n).fst) :
    characteristicDiskMap n j x = map n j x.down.val := rfl

end Topology.CWComplex
