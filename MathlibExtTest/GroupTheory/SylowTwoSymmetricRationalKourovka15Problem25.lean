/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.SylowTwoSymmetricRationalKourovka15Problem25
import Mathlib.Data.ZMod.Basic

/-! # Tests for rationality of Sylow 2-subgroups of symmetric groups -/

open MathlibExt.GroupTheory.SylowTwoSymmetricRationalKourovka15Problem25Wanted

-- In degree one the identity admits even the zeroth power.
example (P : Sylow 2 (Equiv.Perm (Fin 1))) : IsConj (1 : P) ((1 : P) ^ 0) :=
  sylowTwoSubgroupSymmetricRational_holds 0 P 1 0 (by simp)

-- The conjugator for a four-cycle and its cube belongs to the same Sylow subgroup.
example (P : Sylow 2 (Equiv.Perm (Fin 4))) (g : P) (hg : orderOf g = 4) :
    ∃ c : P, c * g * c⁻¹ = g ^ 3 :=
  isConj_iff.mp (sylowTwoSubgroupSymmetricRational_holds 2 P g 3 (by rw [hg]; decide))

-- In the cyclic group of order three, the generator and its square are distinct.
example : ¬ IsRationalGroup (Multiplicative (ZMod 3)) := by
  intro h
  have hc := h (Multiplicative.ofAdd (1 : ZMod 3)) 2 (by
    rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
    decide)
  exact (by decide : Multiplicative.ofAdd (1 : ZMod 3) ≠ _ ^ 2) (isConj_iff_eq.mp hc)
