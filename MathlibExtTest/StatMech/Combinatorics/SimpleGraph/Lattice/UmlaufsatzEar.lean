/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.UmlaufsatzEar
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.UmlaufsatzEar`

* `umEar_totalTurnZ_split` on the unit cell, splitting its four turns at position `2`.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.UmlaufsatzEar

example : totalTurnZ unitCell ucDart0 4 =
    umEar_windowTurn unitCell ucDart0 0 2 + umEar_windowTurn unitCell ucDart0 2 4 :=
  umEar_totalTurnZ_split unitCell ucDart0 2 4 (by norm_num)

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.UmlaufsatzEar
