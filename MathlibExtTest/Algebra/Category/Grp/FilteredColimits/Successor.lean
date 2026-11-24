/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.Algebra.Category.Grp.FilteredColimits.NatTail
import MathlibExt.Algebra.Category.Grp.FilteredColimits.Successor
import Batteries.Tactic.Lint
import Lean

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe v
open CategoryTheory CategoryTheory.Limits
open GrpCat.FilteredColimits

namespace MathlibExtTest.Algebra.Category.Grp.FilteredColimits.Successor
open GrpCat.FilteredColimits.Successor

#check @successorFunctor
#print axioms successorFunctor
#check @successorDiagramFunctor
#print axioms successorDiagramFunctor
#check @successorIndexNatTrans
#print axioms successorIndexNatTrans
#check @successorTransitionNatTrans
#print axioms successorTransitionNatTrans
#check @successorTransitionNatTrans_app_app
#print axioms successorTransitionNatTrans_app_app
#check @successorFunctor_final
#print axioms successorFunctor_final
#check @successorCocone
#print axioms successorCocone
#check @successorCoconeIsColimit
#print axioms successorCoconeIsColimit
#check @successorComparisonIso
#print axioms successorComparisonIso
#check @successorComparisonIso_hom_ι
#print axioms successorComparisonIso_hom_ι
#check @successorTransition_colimit_comp_hom
#print axioms successorTransition_colimit_comp_hom
#check @successorTransition_colimit_eq_inv
#print axioms successorTransition_colimit_eq_inv
#check @successorTransition_colimit_isIso
#print axioms successorTransition_colimit_isIso

-- These examples import only Algebra and retain the actual diagrams and quotient functions.
example : successorFunctor.obj 0 = 1 := rfl

example : successorFunctor.obj 1 = 2 := rfl

example (D : ℕ ⥤ GrpCat.{v}) :
    (successorDiagramFunctor.obj D).obj 0 = D.obj 1 := rfl

example {D E : ℕ ⥤ GrpCat.{v}} (a : D ⟶ E) :
    (successorDiagramFunctor.map a).app 1 = a.app 2 := rfl

example (D : ℕ ⥤ GrpCat.{v}) :
    (successorTransitionNatTrans.app D).app 0 = D.map (homOfLE (Nat.le_succ 0)) :=
  successorTransitionNatTrans_app_app D 0

example (D : ℕ ⥤ GrpCat.{v}) :
    (successorTransitionNatTrans.app D).app 1 = D.map (homOfLE (Nat.le_succ 1)) :=
  successorTransitionNatTrans_app_app D 1

example (D : ℕ ⥤ GrpCat.{v}) :
    (colimitCocone D).ι.app 0 ≫ (successorComparisonIso D).inv =
      (successorTransitionNatTrans.app D).app 0 ≫
        (colimitCocone (successorFunctor ⋙ D)).ι.app 0 := by
  let a : D ⟶ successorFunctor ⋙ D := successorTransitionNatTrans.app D
  exact (congrArg (fun f => (colimitCocone D).ι.app 0 ≫ f)
    (successorTransition_colimit_eq_inv D)).symm.trans
      ((colimitCoconeIsColimit D).ι_map
        (colimitCocone (successorFunctor ⋙ D)) a 0)

example (D : ℕ ⥤ GrpCat.{v}) :
    (colimitCocone D).ι.app 1 ≫ (successorComparisonIso D).inv =
      (successorTransitionNatTrans.app D).app 1 ≫
        (colimitCocone (successorFunctor ⋙ D)).ι.app 1 := by
  let a : D ⟶ successorFunctor ⋙ D := successorTransitionNatTrans.app D
  exact (congrArg (fun f => (colimitCocone D).ι.app 1 ≫ f)
    (successorTransition_colimit_eq_inv D)).symm.trans
      ((colimitCoconeIsColimit D).ι_map
        (colimitCocone (successorFunctor ⋙ D)) a 1)

example (D : ℕ ⥤ GrpCat.{v}) (a : D.obj 1) :
    (successorComparisonIso D).hom.hom
        (G.mk (successorFunctor ⋙ D) ⟨0, a⟩) = G.mk D ⟨1, a⟩ :=
  ConcreteCategory.congr_hom (successorComparisonIso_hom_ι D 0) a

example (D : ℕ ⥤ GrpCat.{v}) (z : GrpCat.FilteredColimits.colimit D) :
    (successorComparisonIso D).hom.hom ((successorComparisonIso D).inv.hom z) = z :=
  ConcreteCategory.congr_hom (successorComparisonIso D).inv_hom_id z

example (D : ℕ ⥤ GrpCat.{v}) (z : GrpCat.FilteredColimits.colimit (successorFunctor ⋙ D)) :
    (successorComparisonIso D).inv.hom ((successorComparisonIso D).hom.hom z) = z :=
  ConcreteCategory.congr_hom (successorComparisonIso D).hom_inv_id z

-- Both whole diagram maps survive passage through the actual inverse comparison.
example {D E : ℕ ⥤ GrpCat.{v}} (a : D ⟶ E) :
    natQuotientColimit.map a ≫ (successorComparisonIso E).inv =
      (successorComparisonIso D).inv ≫ natQuotientColimit.map (successorDiagramFunctor.map a) := by
  rw [← successorTransition_colimit_eq_inv, ← successorTransition_colimit_eq_inv]
  let Q : (ℕ ⥤ GrpCat.{v}) ⥤ GrpCat.{v} := natQuotientColimit
  exact (Q.map_comp _ _).symm.trans
    ((Q.congr_map (successorTransitionNatTrans.naturality a)).trans (Q.map_comp _ _))

/-- Every moved root retains its original kernel kind in the canonical Algebra module. -/
def expectedKernelKinds : Array (Lean.Name × String) := #[
  ((`GrpCat.FilteredColimits.Successor).append
    `successorFunctor, "def"),
  ((`GrpCat.FilteredColimits.Successor).append
    `successorDiagramFunctor, "def"),
  ((`GrpCat.FilteredColimits.Successor).append
    `successorIndexNatTrans, "def"),
  ((`GrpCat.FilteredColimits.Successor).append
    `successorTransitionNatTrans, "def"),
  ((`GrpCat.FilteredColimits.Successor).append
    `successorTransitionNatTrans_app_app, "theorem"),
  ((`GrpCat.FilteredColimits.Successor).append
    `successorFunctor_final, "theorem"),
  ((`GrpCat.FilteredColimits.Successor).append
    `successorCocone, "def"),
  ((`GrpCat.FilteredColimits.Successor).append
    `successorCoconeIsColimit, "def"),
  ((`GrpCat.FilteredColimits.Successor).append
    `successorComparisonIso, "def"),
  ((`GrpCat.FilteredColimits.Successor).append
    `successorComparisonIso_hom_ι, "theorem"),
  ((`GrpCat.FilteredColimits.Successor).append
    `successorTransition_colimit_comp_hom, "theorem"),
  ((`GrpCat.FilteredColimits.Successor).append
    `successorTransition_colimit_eq_inv, "theorem"),
  ((`GrpCat.FilteredColimits.Successor).append
    `successorTransition_colimit_isIso, "theorem")
]

run_cmd do
  let env ← Lean.getEnv
  let m := `MathlibExt.Algebra.Category.Grp.FilteredColimits.Successor
  let idx ← match env.getModuleIdx? m with
    | some i => pure i
    | none => throwError "missing actual original producer module"
  let mut count : Nat := 0
  for (n, _) in env.constants do
    if env.getModuleIdxFor? n == some idx then count := count + 1
  unless count > 0 do throwError "zero actual producer declarations"
  for (n, expectedKind) in expectedKernelKinds do
    let info ← match env.find? n with
      | some c => pure c
      | none => throwError "missing actual original root: {n}"
    let kind := match info with
      | .defnInfo _ => "def"
      | .thmInfo _ => "theorem"
      | _ => "other"
    unless kind == expectedKind do throwError "wrong actual kernel kind: {n} {kind}"
    let actualIdx ← match env.getModuleIdxFor? n with
      | some i => pure i
      | none => throwError "missing actual numeric root module: {n}"
    unless actualIdx == idx do throwError "wrong actual original producer membership: {n}"
    Lean.logInfo m!"SOURCE_ROOT_MODULE {m} {n}"
    Lean.logInfo m!"KERNEL_KIND_MODULE {m} {n} KIND {kind} NUMERIC_MODULE {actualIdx.toNat}"
  Lean.logInfo m!"SOURCE_MODULE_COUNT {m} {count} EXPECTED_ROOTS {expectedKernelKinds.size}"

#lint only unusedArguments in MathlibExt.Algebra.Category.Grp.FilteredColimits.Successor
#lint in MathlibExt.Algebra.Category.Grp.FilteredColimits.Successor

end MathlibExtTest.Algebra.Category.Grp.FilteredColimits.Successor
