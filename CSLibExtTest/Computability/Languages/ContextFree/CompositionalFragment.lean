/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.CompositionalFragment

/-!
# Tests for the compositional fragment

Invalid productions are rejected and ill-typed quantifier application
does not typecheck.
-/

@[expose] public section

namespace Cslib.Language.CompositionalFragment

open Cslib.Languages.LambdaCalculus.Stlc
open scoped CslibStlc

/-! ### Invalid productions are rejected -/

/-- Boundary fixture: the leaf `Subj → someone` is not valid; `compile`
has no callable valid-domain input for it. -/
theorem leaf_subj_someone_not_valid :
    ¬ IsValidTree Token g (PDerivTree.leaf catSubj someoneTok) := by
  simp only [IsValidTree]
  decide

/-- Boundary fixture: there is no binary rule `S → TV Obj`. -/
theorem node_s_tv_obj_not_valid :
    ¬ IsValidTree Token g
      (PDerivTree.node catS catTV catObj
        (PDerivTree.leaf catTV admiresTok)
        (PDerivTree.leaf catObj someoneTok)) := by
  simp only [IsValidTree, PDerivTree.rootOf]
  rintro ⟨hmem, -, -, -, -⟩
  exact absurd hmem (by decide)

/-! ### Ill-typed Q-to-Q application is rejected

`everybodyTm : Tm LexCtx QTy` with `QTy = PTy ⇒ tTy` expects a
`PTy`-typed argument, not the `QTy`-typed `someoneTm`; the would-be
term `Tm.app everybodyTm someoneTm` is rejected by the elaborator.
The checkable content is pinned here as type discrimination; the test
file additionally pins the elaboration failure itself. No new
typechecker is introduced. -/

/-- `Q`'s domain is `P`, and `P ≠ Q`: a `Q`-typed term cannot be
applied to a `Q`-typed argument. -/
theorem qTy_ne_pTy : QTy ≠ PTy := by decide

theorem qTy_domain (A B : Ty Bool) (h : QTy = Ty.arr A B) :
    A = PTy ∧ B = tTy := by
  unfold QTy at h
  cases h
  exact ⟨rfl, rfl⟩


end Cslib.Language.CompositionalFragment
