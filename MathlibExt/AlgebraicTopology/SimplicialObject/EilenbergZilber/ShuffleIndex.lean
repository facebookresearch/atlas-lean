/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Perm.Fin

@[expose] public section

namespace AlgebraicTopology.EilenbergZilber

def IsShuffle {p q : ℕ} (σ : Equiv.Perm (Fin (p + q))) : Prop :=
  StrictMono (fun i => σ (Fin.castAdd q i)) ∧
    StrictMono (fun j => σ (Fin.natAdd p j))

structure Shuffle (p q : ℕ) where
  perm : Equiv.Perm (Fin (p + q))
  isShuffle : IsShuffle perm

def shuffleSign {p q : ℕ} (s : Shuffle p q) : ℤˣ :=
  Equiv.Perm.sign s.perm

def shuffleSignZ {p q : ℕ} (s : Shuffle p q) : ℤ :=
  (shuffleSign s : ℤ)

theorem shuffleSign_eq_prod_prod_Iio {p q : ℕ} (s : Shuffle p q) :
  shuffleSign s =
    ∏ j, ∏ i ∈ Finset.Iio j,
      (if s.perm i < s.perm j then (1 : ℤˣ) else -1) :=
  Equiv.Perm.sign_eq_prod_prod_Iio s.perm

end AlgebraicTopology.EilenbergZilber
