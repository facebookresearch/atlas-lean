/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Crypto.Pedersen
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.Group.PUnit

@[expose] public section

/-- Boundary check: the hiding count instantiates in the trivial
group, where the unique commitment has exactly one opening. -/
example : (Finset.univ.filter (fun r : ZMod (Fintype.card PUnit) =>
      (1 : PUnit) ^ (0 : ZMod (Fintype.card PUnit)).val *
        (1 : PUnit) ^ r.val = 1)).card = 1 :=
  pedersen_hiding 1 1 (by simp) (by simp) 0 1
