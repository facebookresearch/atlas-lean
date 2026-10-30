/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.AddCyclicSquarefree

@[expose] public section

example {A : Type*} [AddCommGroup A] (hA : Squarefree (Nat.card A)) :
    IsAddCyclic A :=
  IsAddCyclic.of_squarefree_natCard hA
