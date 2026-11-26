/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ModuleInternalHom
public import MathlibExt.AlgebraicGeometry.CompactifiedPoincareKernels
public import MathlibExt.AlgebraicGeometry.SheafTensorSections

/-!
# The computed inverse line module

The inverse object is the actual sheaf Hom(L,O), constructed by the
completed native presheaf internal-Hom and sheaf theorem. Evaluation and
invertibility dictionaries refer to that exact module. No independently
selected inverse line or scalar trivialization is substituted.
The imported internal-Hom source is AxiomMath/Stacks
c496df0d9beea9deaeabcea8492605f9a0a2313b, Apache 2.0;
its original authorship/adaptation notices are retained there.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeLineDuals

open _root_.CategoryTheory _root_.AlgebraicGeometry
open CoherentCurveLinearSeries CompactifiedPoincareKernels
open SheafTensorSections

def dualModule (X : Scheme.{0}) (L : X.Modules) : X.Modules where
  val := ModuleInternalHom.internalHom X.presheaf L.val (structureModule X).val
  isSheaf := ModuleInternalHom.internalHom_isSheaf X.presheaf L.val
    (structureModule X).val (structureModule X).isSheaf

/-- Evaluate the actual internal-Hom section on the identity slice object. -/
def localEvaluation (X : Scheme.{0}) (L : X.Modules) (U : X.Opens)
    (f : Γ(dualModule X L, U)) (s : Γ(L, U)) : Γ(X, U) :=
  ((show (ModuleInternalHom.restrFun X.presheaf U).obj L.val ⟶
      (ModuleInternalHom.restrFun X.presheaf U).obj (structureModule X).val from f).app
    (Opposite.op (Over.mk (𝟙 U)))).hom s

/-- The universal evaluation belongs to the computed sheaf dual. -/
structure LineDuality (X : Scheme.{0}) (L : X.Modules) where
  evaluation : SheafDual L
  object_eq : evaluation.dual = dualModule X L
  line : IsLineBundle (dualModule X L)
  invertible : IsIso evaluation.evaluation
  normalized : ∀ (U : X.Opens) (s : Γ(L, U)) (f : Γ(dualModule X L, U)),
    (evaluation.evaluation.val.app (Opposite.op U)).hom
      (tensorSection X L evaluation.dual U s
        (((eqToIso object_eq).inv.val.app (Opposite.op U)).hom f)) = localEvaluation X L U f s

end MathlibExt.AlgebraicGeometry.NativeLineDuals
