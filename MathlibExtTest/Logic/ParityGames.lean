/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Logic.ParityGames

@[expose] public section

/-- Boundary check: the target set is contained in its attractor
(zero steps already reach it). -/
example {V : Type*} [Fintype V] [DecidableEq V]
    (owner : V → Bool) (edge : V → Finset V) (T : Finset V) :
    T ⊆ attr owner edge T :=
  attrLe_mono owner edge T (Nat.zero_le _)
