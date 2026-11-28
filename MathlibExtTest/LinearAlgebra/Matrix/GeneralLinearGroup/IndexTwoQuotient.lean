/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.IndexTwoQuotient

import Mathlib.Data.ZMod.Basic

open Matrix Matrix.GeneralLinearGroup

-- An abelian group (the whole group is an abelian subgroup of index `1`) does not surject onto
-- `GL₂(ℤ/3ℤ)`.
example (f : Multiplicative (ZMod 7) →* GL (Fin 2) (ZMod 3)) : ¬ Function.Surjective f :=
  not_surjective_zmod_of_isMulCommutative_of_index_le_two (by decide) ⊤
    (by rw [Subgroup.index_top]; norm_num) f

-- The same for `GL₂(ℤ)` (`n = 0`, as `0 ∤ 4`).
example {G : Type} [CommGroup G] (f : G →* GL (Fin 2) ℤ) : ¬ Function.Surjective f :=
  not_surjective_of_isMulCommutative_of_index_le_two (by norm_num) ⊤
    (by rw [Subgroup.index_top]; norm_num) f

-- A group with an abelian subgroup of index `2` (a group of dihedral type) does not surject onto `GL₂(ℤ/5ℤ)`.
example {G : Type} [Group G] (A : Subgroup G) [IsMulCommutative A] (hA : A.index = 2)
    (f : G →* GL (Fin 2) (ZMod 5)) : ¬ Function.Surjective f :=
  have : A.FiniteIndex := ⟨by omega⟩
  not_surjective_zmod_of_isMulCommutative_of_index_le_two (by decide) A hA.le f
