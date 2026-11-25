/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.ChainComplex.BalancedTensor.Differential

/-!
# The actual full integer tensor–Hom total-cochain isomorphism

The degree maps are the proved signed currying and its actual inverse.
Native `isoOfComponents` assembles their differential square, preserving
the original tensor-total and full Hom products.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace ChainComplex.BalancedTensor

universe u v

variable (R : Type u) [Ring R]
  (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
  (Q : ChainComplex (ModuleCat.{v} R) ℤ)
  (I : CochainComplex AddCommGrpCat.{v} ℤ)

/-- The original sum/product tensor–Hom adjunction in the full integer cochain grading. -/
def homIso :
    homCochainComplex (complex R P Q) I ≅
      homCochainComplex P (moduleHomCochainComplex R Q I) :=
  HomologicalComplex.Hom.isoOfComponents
    (C₁ := homCochainComplex (complex R P Q) I)
    (C₂ := homCochainComplex P (moduleHomCochainComplex R Q I))
    (fun n => AddEquiv.toAddCommGrpIso
      (X := (homCochainComplex (complex R P Q) I).X n)
      (Y := (homCochainComplex P (moduleHomCochainComplex R Q I)).X n)
      (cochainEquiv R P Q I n)) (by
    intro n m hnm
    change n + 1 = m at hnm
    subst m
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro f
    change ((homCochainComplex P (moduleHomCochainComplex R Q I)).d n (n + 1)).hom
      (curryCochain R P Q I n f) =
      curryCochain R P Q I (n + 1)
        (((homCochainComplex (complex R P Q) I).d n (n + 1)).hom f)
    exact (curryCochain_d R P Q I n f).symm)

/-- The forward component is exactly the earned signed currying. -/
theorem homIso_hom_f (n : ℤ) :
    ((homIso R P Q I).hom.f n).hom =
      (cochainEquiv R P Q I n).toAddMonoidHom := rfl

/-- The inverse component is exactly the earned uncurrying, without a support restriction. -/
theorem homIso_inv_f (n : ℤ) :
    ((homIso R P Q I).inv.f n).hom =
      (cochainEquiv R P Q I n).symm.toAddMonoidHom := rfl

end ChainComplex.BalancedTensor
