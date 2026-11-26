/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.CenteredFirstHit

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.CenteredFirstHit`

* `center_mem_centeredClosedBox` at the origin of `ℤ²` (concrete instance);
* `connectedToSet_centered_has_within` applied to a connection hypothesis;
* `connected_centeredBoundary_has_within` applied to a boundary point and a connection.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.CenteredFirstHit

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.OSSS
open _root_.StatMech.OSSS.RevealmentConstruction _root_.StatMech.OSSS.RevealmentTranslation
open _root_.StatMech.OSSS.CenteredFirstHit

-- The center lies in its own centered box (here `d = 2`, radius `3`, center the origin).
example : (0 : Site 2) ∈ centeredClosedBox (0 : Site 2) 3 :=
  center_mem_centeredClosedBox 0 3

-- A connection from `u` to the centered boundary can be realized inside the centered box.
example {d m : ℕ} {ω : ConfigSpace (Sym2 (Site d))} {u : Site d}
    (h : ConnectedToSet d ω u (centeredBoundary u m)) :
    ∃ z : centeredClosedBox u m, (z : Site d) ∈ centeredBoundary u m ∧
      ConnectedWithin d ω (centeredClosedBox u m) ⟨u, center_mem_centeredClosedBox u m⟩ z :=
  connectedToSet_centered_has_within h

-- The same for a connection to a specific boundary point `z`.
example {d m : ℕ} {ω : ConfigSpace (Sym2 (Site d))} {u z : Site d}
    (hz : z ∈ centeredBoundary u m) (h : Connected d ω u z) :
    ∃ z' : centeredClosedBox u m, (z' : Site d) ∈ centeredBoundary u m ∧
      ConnectedWithin d ω (centeredClosedBox u m) ⟨u, center_mem_centeredClosedBox u m⟩ z' :=
  connected_centeredBoundary_has_within hz h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.CenteredFirstHit
