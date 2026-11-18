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

/-! ### End-to-end compiler outputs (UNVERIFIED)

UNVERIFIED: the upstream `CSLibExt` modules are unavailable where these
tests were derived, so the assertions below have not been checked
against the real upstream elaborator. The expected terms were derived
by hand from the seven semantic actions, and the proof scripts were
checked against local API stubs mirroring the production file's
interface. Re-verify by compiling this file once the imports resolve.
-/

/-- UNVERIFIED: expected surface meaning, written out from the actions:
`everybody (λ x. someone (λ y. admires x y))`. -/
def surfaceExpected : Tm LexCtx tTy :=
  actS1 everybodyTm (actVP admiresTm someoneTm)

/-- UNVERIFIED: expected inverse meaning, written out from the actions:
`someone (λ y. everybody (λ x. admires x y))`. -/
def inverseExpected : Tm LexCtx tTy :=
  actSObj (actSP everybodyTm admiresTm) someoneTm

/-- UNVERIFIED: fully expanded surface term over the raw `Tm`
constructors. -/
def surfaceExpanded : Tm LexCtx tTy :=
  Tm.app everybodyTm
    (Tm.lam (Tm.app (Tm.weaken someoneTm)
      (Tm.lam (Tm.app (Tm.app (Tm.weaken (Tm.weaken admiresTm))
        (Tm.var (Var.succ Var.zero))) (Tm.var Var.zero)))))

/-- UNVERIFIED: fully expanded inverse term over the raw `Tm`
constructors. -/
def inverseExpanded : Tm LexCtx tTy :=
  Tm.app someoneTm
    (Tm.lam (Tm.app (Tm.weaken everybodyTm)
      (Tm.lam (Tm.app (Tm.app (Tm.weaken (Tm.weaken admiresTm))
        (Tm.var Var.zero)) (Tm.var (Var.succ Var.zero))))))

/-- UNVERIFIED: the action-composed surface term is the expansion. -/
theorem surfaceExpected_expanded : surfaceExpected = surfaceExpanded := rfl

/-- UNVERIFIED: the action-composed inverse term is the expansion. -/
theorem inverseExpected_expanded : inverseExpected = inverseExpanded := rfl

/-- UNVERIFIED: `compileAt` on the `everybody` leaf. -/
theorem compileAt_leaf_everybody
    (hroot : (PDerivTree.leaf catSubj everybodyTok).rootOf = catSubj)
    (h : IsValidTree Token g (PDerivTree.leaf catSubj everybodyTok)) :
    compileAt catSubj (PDerivTree.leaf catSubj everybodyTok) hroot h =
      everybodyTm := by
  unfold compileAt
  rw [compile_leaf_everybody]

/-- UNVERIFIED: `compileAt` on the `someone` leaf. -/
theorem compileAt_leaf_someone
    (hroot : (PDerivTree.leaf catObj someoneTok).rootOf = catObj)
    (h : IsValidTree Token g (PDerivTree.leaf catObj someoneTok)) :
    compileAt catObj (PDerivTree.leaf catObj someoneTok) hroot h =
      someoneTm := by
  unfold compileAt
  rw [compile_leaf_someone]

/-- UNVERIFIED: `compileAt` on the `admires` leaf. -/
theorem compileAt_leaf_admires
    (hroot : (PDerivTree.leaf catTV admiresTok).rootOf = catTV)
    (h : IsValidTree Token g (PDerivTree.leaf catTV admiresTok)) :
    compileAt catTV (PDerivTree.leaf catTV admiresTok) hroot h =
      admiresTm := by
  unfold compileAt
  rw [compile_leaf_admires]

/-- UNVERIFIED: `compileAt` on the `VP` subtree. -/
theorem compileAt_vpnode
    (hroot : (PDerivTree.node catVP catTV catObj
      (PDerivTree.leaf catTV admiresTok)
      (PDerivTree.leaf catObj someoneTok)).rootOf = catVP)
    (h : IsValidTree Token g (PDerivTree.node catVP catTV catObj
      (PDerivTree.leaf catTV admiresTok)
      (PDerivTree.leaf catObj someoneTok))) :
    compileAt catVP (PDerivTree.node catVP catTV catObj
      (PDerivTree.leaf catTV admiresTok)
      (PDerivTree.leaf catObj someoneTok)) hroot h =
      actVP admiresTm someoneTm := by
  have hcopy := h
  obtain ⟨_, hBl, hCr, hVl, hVr⟩ := hcopy
  have hEq := compile_node_vp_apply_object _ _ hVl hVr hBl hCr h
  unfold compileAt
  erw [hEq, compileAt_leaf_admires, compileAt_leaf_someone]

/-- UNVERIFIED: `compileAt` on the `SP` subtree. -/
theorem compileAt_spnode
    (hroot : (PDerivTree.node catSP catSubj catTV
      (PDerivTree.leaf catSubj everybodyTok)
      (PDerivTree.leaf catTV admiresTok)).rootOf = catSP)
    (h : IsValidTree Token g (PDerivTree.node catSP catSubj catTV
      (PDerivTree.leaf catSubj everybodyTok)
      (PDerivTree.leaf catTV admiresTok))) :
    compileAt catSP (PDerivTree.node catSP catSubj catTV
      (PDerivTree.leaf catSubj everybodyTok)
      (PDerivTree.leaf catTV admiresTok)) hroot h =
      actSP everybodyTm admiresTm := by
  have hcopy := h
  obtain ⟨_, hBl, hCr, hVl, hVr⟩ := hcopy
  have hEq := compile_node_sp_apply_subject _ _ hVl hVr hBl hCr h
  unfold compileAt
  erw [hEq, compileAt_leaf_everybody, compileAt_leaf_admires]

/-- UNVERIFIED: end-to-end surface compiler output. -/
theorem compile_surfaceTree :
    compile surfaceTree surfaceTree_valid = surfaceExpected := by
  have hcopy := surfaceTree_valid
  obtain ⟨_, hBl, hCr, hVl, hVr⟩ := hcopy
  have hEq := compile_node_s_subject_wide _ _ hVl hVr hBl hCr surfaceTree_valid
  unfold surfaceTree surfaceExpected
  erw [hEq, compileAt_leaf_everybody, compileAt_vpnode]

/-- UNVERIFIED: end-to-end inverse compiler output. -/
theorem compile_inverseTree :
    compile inverseTree inverseTree_valid = inverseExpected := by
  have hcopy := inverseTree_valid
  obtain ⟨_, hBl, hCr, hVl, hVr⟩ := hcopy
  have hEq := compile_node_s_object_wide _ _ hVl hVr hBl hCr inverseTree_valid
  unfold inverseTree inverseExpected
  erw [hEq, compileAt_spnode, compileAt_leaf_someone]

/-- error: Application type mismatch -/
#guard_msgs (error, substring := true) in
#check Tm.app everybodyTm someoneTm


end Cslib.Language.CompositionalFragment
