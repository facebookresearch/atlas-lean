/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.NeggersStanley
import Mathlib.GroupTheory.Perm.Fin

open MathlibExt.Combinatorics.NeggersStanleyPosetConjectureAMR156Problem0020Wanted
open Polynomial

-- A fact about the shared statistic simplifies a polynomial exponent using the legacy name.
example {n : ℕ} (w : Equiv.Perm (Fin n)) (h : MetaMathlibExt.permDescents w = 0) :
    (X : ℤ[X]) ^ descentCount w = 1 := by
  simp [h]

-- The last position cannot be a descent, even in a completely decreasing word.
example : descentCount (Fin.revPerm : Equiv.Perm (Fin 4)) = 3 := by decide

-- The empty poset has one extension, the empty word.
example : wPolynomial (fun _ _ : Fin 0 => False) = 1 := by
  simp [wPolynomial, descentCount]

-- Both permutations extend the two-element antichain.
example : wPolynomial (fun _ _ : Fin 2 => False) = 1 + X := by
  classical
  simp only [wPolynomial, false_implies, forall_const, Finset.filter_true]
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Fintype.sum_unique]
  have hid : descentCount (Equiv.refl (Fin 2)) = 0 := by decide
  have hswap : descentCount (Equiv.swap (0 : Fin 2) 1) = 1 := by decide
  simp [hid, hswap]
