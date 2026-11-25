/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.PointedPicardFamilies

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies
open MathlibExt.AlgebraicGeometry.PointedPicardFamilies

universe u

variable {k : Type u} [Field k]

-- The tensor product and powers re-exported here are the single definitions of
-- `SchemeModulesTensor`, not parallel copies.
example : @AlgebraicLineBundleFamilies.moduleTensor = @SchemeModulesTensor.moduleTensor := rfl
example : @AlgebraicLineBundleFamilies.power = @SchemeModulesTensor.power := rfl

-- Tensor powers start at the structure sheaf and tensor on the right.
example {X : Scheme.{u}} (L : X.Modules) : power L 0 = structureModule X := rfl
example {X : Scheme.{u}} (L : X.Modules) (n : ℕ) :
    power L (n + 1) = moduleTensor X (power L n) L := rfl

-- `familyPullback` is the actual pullback: along the identity it returns the family.
example (A D : Over (Spec (.of k))) (P : (prod A D).left.Modules) :
    Nonempty (familyPullback A D D P (𝟙 D) ≅ P) :=
  ⟨(Scheme.Modules.pullbackCongr (by simp)).app P ≪≫ (Scheme.Modules.pullbackId _).app P⟩

-- A Picard-zero model of a pointed proper curve has relative dimension the genus,
-- and its identity parametrizes the trivial bundle.
example (C : Over (Spec (.of k))) [IsProperCurve C.hom] [HasConstantGlobalSections C.hom]
    (p : 𝟙_ (Over (Spec (.of k))) ⟶ C) (J : PicardZeroModel C p) :
    SmoothOfRelativeDimension (genus C.hom) J.J.hom :=
  J.smoothDimension

-- The model is also available for proper schemes of higher dimension (such as a
-- compactified Jacobian), with relative dimension `dim H¹(X, 𝒪_X)`.
example (X : Over (Spec (.of k))) [IsProper X.hom]
    (p : 𝟙_ (Over (Spec (.of k))) ⟶ X) (J : PicardZeroModel X p) :
    SmoothOfRelativeDimension (Module.finrank k (cohomology X.hom (structureModule X.left) 1))
      J.J.hom :=
  J.smoothDimension

attribute [local instance] PicardZeroModel.group in
example (C : Over (Spec (.of k))) [IsProper C.hom]
    (p : 𝟙_ (Over (Spec (.of k))) ⟶ C) (J : PicardZeroModel C p) :
    Nonempty ((Scheme.Modules.pullback (pointSection C J.J η[J.J]).left).obj J.P ≅
      structureModule C.left) :=
  J.identity

-- Normalization along the chosen point of the curve: a family pulled back from the
-- parameter scheme is normalized exactly when it comes from the trivial bundle.
example (C T : Over (Spec (.of k))) (p : 𝟙_ (Over (Spec (.of k))) ⟶ C) (Q : T.left.Modules) :
    IsNormalized C T p ((Scheme.Modules.pullback (prod.snd : prod C T ⟶ T).left).obj Q) ↔
      Nonempty (Q ≅ structureModule T.left) := by
  have h : (sectionAt C T p).left ≫ (prod.snd : prod C T ⟶ T).left = 𝟙 T.left := by
    rw [← Over.comp_left, sectionAt, prod.lift_snd]
    rfl
  let e : (Scheme.Modules.pullback (sectionAt C T p).left).obj
      ((Scheme.Modules.pullback (prod.snd : prod C T ⟶ T).left).obj Q) ≅ Q :=
    (Scheme.Modules.pullbackComp _ _).app Q ≪≫ (Scheme.Modules.pullbackCongr h).app Q ≪≫
      (Scheme.Modules.pullbackId _).app Q
  exact ⟨fun ⟨i⟩ ↦ ⟨e.symm ≪≫ i⟩, fun ⟨i⟩ ↦ ⟨e ≪≫ i⟩⟩
