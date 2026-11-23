/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.NerveSingleObj
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Perm.Basic

/-!
# One-object nerve clients

Noncommuting permutations distinguish the ordinary nerve's multiplication
order from the opposite nerve used by bar constructions. A natural-number
client checks that the tuple API also accepts monoids without inverses.
-/

open CategoryTheory
open scoped Simplicial

noncomputable section

namespace MathlibExtTest.NerveSingleObj

private abbrev Perm := Equiv.Perm (Fin 3)

private def swaps : Fin 2 → Perm := ![Equiv.swap 0 1, Equiv.swap 1 2]

example :
    (nerve.singleObjEquiv Perm 1
      ((nerve (SingleObj Perm)).δ (1 : Fin 3)
        ((nerve.singleObjEquiv Perm 2).symm swaps)) 0) (0 : Fin 3) = 2 := by
  rw [nerve.singleObjEquiv_middle_face]
  decide

example :
    (nerve.singleObjOppEquiv Perm 1
      ((nerve (SingleObj Permᵐᵒᵖ)).δ (1 : Fin 3)
        ((nerve.singleObjOppEquiv Perm 2).symm swaps)) 0) (0 : Fin 3) = 1 := by
  rw [nerve.singleObjOppEquiv_middle_face]
  decide

example :
    nerve.singleObjEquiv ℕ 1
      ((nerve (SingleObj ℕ)).δ (1 : Fin 3)
        ((nerve.singleObjEquiv ℕ 2).symm ![2, 3])) 0 = 6 := by
  rw [nerve.singleObjEquiv_middle_face]
  decide

/-- The generic inversion comparison is available from the tuple provider alone. -/
example (G : Type*) [Group G] (n : ℕ) (g : Fin n → G) :
    (nerve.inversionIso G).hom.app (Opposite.op ⦋n⦌)
        ((nerve.singleObjOppEquiv G n).symm g) =
      (nerve.singleObjEquiv G n).symm (fun i => (g i)⁻¹) :=
  nerve.inversionIso_simplex G n g

/-- Its inverse retains all original direct tuple coordinates. -/
example (G : Type*) [Group G] (n : ℕ) (g : Fin n → G) :
    (nerve.inversionIso G).inv.app (Opposite.op ⦋n⦌)
        ((nerve.singleObjEquiv G n).symm g) =
      (nerve.singleObjOppEquiv G n).symm (fun i => (g i)⁻¹) :=
  nerve.inversionIso_inv_simplex G n g

end MathlibExtTest.NerveSingleObj
