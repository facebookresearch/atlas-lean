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
# Full integer tensor–Hom isomorphism

For a right-module chain complex `P`, a left-module chain complex `Q`, and an additive-group
cochain complex `I`, signed currying gives an isomorphism `Hom_ℤ(P ⊗_R Q, I) ≅ Hom_(Rᵐᵒᵖ)(P,
Hom_ℤ(Q, I))` of additive-group cochain complexes. The inner additive Hom has its right
`R`-action by domain precomposition.

The tensor complex uses direct sums over all integer diagonals, while both Hom constructions
use full products. Each degree map is the additive cochain equivalence defined by currying
with `θ(b) = (-1)^(b*(b+1)/2)` in inner degree `b`; the inverse is signed uncurrying.
Differential compatibility assembles these maps into the complex isomorphism.
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

/-- Full tensor-total Hom complex is isomorphic to nested Hom.

Signed currying and uncurrying in every integer degree give an isomorphism from
`homCochainComplex (complex R P Q) I` to `homCochainComplex P (moduleHomCochainComplex R Q
I)`. -/
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

/-- Forward component of the full tensor–Hom isomorphism.

In integer degree `n`, the forward map of the tensor–Hom isomorphism is the additive map
underlying `cochainEquiv R P Q I n`. -/
theorem homIso_hom_f (n : ℤ) :
    ((homIso R P Q I).hom.f n).hom =
      (cochainEquiv R P Q I n).toAddMonoidHom := rfl

/-- Inverse component of the full tensor–Hom isomorphism.

In integer degree `n`, the inverse map of the tensor–Hom isomorphism is the additive map
underlying the inverse of `cochainEquiv R P Q I n`. -/
theorem homIso_inv_f (n : ℤ) :
    ((homIso R P Q I).inv.f n).hom =
      (cochainEquiv R P Q I n).symm.toAddMonoidHom := rfl

end ChainComplex.BalancedTensor
