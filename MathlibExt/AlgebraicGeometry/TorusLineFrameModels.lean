/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ContractedTorsorModels
public import MathlibExt.AlgebraicGeometry.ExpansionParameterModels
public import MathlibExt.AlgebraicGeometry.SchemeModuleLinear
public import MathlibExt.AlgebraicGeometry.FiniteCoverLocalComparison

/-!
# Actual line-frame torsors and torus character lines

A line-frame torsor represents actual isomorphisms O_U to L|_U on every
scheme over the base. Its multiplicative action is the native scalar
action and its restriction uses actual pullback composition maps.
The line associated with a torus character is bound to the actual
contracted pushout of the original torus torsor to the frame torsor.
References: Stacks Project Tag0CQJ; Donagi--Gaitsgory
arXiv:math/0005132v3, Sections5--6.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.TorusLineFrameModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open ContractedTorsorModels ExpansionParameterModels CoherentCurveLinearSeries
open FiniteCoverLocalComparison

def scalarIso (X : Scheme.{0}) (M : X.Modules) (u : Γ(X, ⊤)ˣ) : M ≅ M :=
  letI : Linear Γ(X, ⊤) X.Modules :=
    SchemeModuleLinear.modulesLinear Γ(X, ⊤) (Over.mk X.toSpecΓ)
  { hom := (u : Γ(X, ⊤)) • 𝟙 M
    inv := (↑u⁻¹ : Γ(X, ⊤)) • 𝟙 M
    hom_inv_id := by simp [Linear.comp_smul, smul_smul]
    inv_hom_id := by simp [Linear.comp_smul, smul_smul] }

variable {k : Type} [Field k] (Gm : TorusTheory k 1)

@[implicit_reducible] def testScheme (Y : Over (Spec (.of k)))
    (U : Over Y.left) : Over (Spec (.of k)) :=
  Over.mk (U.hom ≫ Y.hom)

def testMap (Y : Over (Spec (.of k))) (U : Over Y.left) : testScheme Y U ⟶ Y :=
  Over.homMk U.hom rfl

def testArrow {Y : Over (Spec (.of k))} {U U' : Over Y.left} (h : U' ⟶ U) :
    testScheme Y U' ⟶ testScheme Y U :=
  Over.homMk h.left (by
    change h.left ≫ (U.hom ≫ Y.hom) = U'.hom ≫ Y.hom
    rw [← Category.assoc, Over.w h])

structure LineFrames (Y : Over (Spec (.of k))) (L : Y.left.Modules) where
  line : IsLineBundle L
  bundle : letI := Gm.group; Bundle (torusScheme k 1) Y
  basis : letI := Gm.group; ∀ U : Over Y.left,
    {f : testScheme Y U ⟶ bundle.torsor.total // f ≫ bundle.torsor.projection = testMap Y U} ≃
      (structureModule U.left ≅ (Scheme.Modules.pullback U.hom).obj L)
  naturality : letI := Gm.group; ∀ {U U' : Over Y.left} (h : U' ⟶ U)
      (p : {f : testScheme Y U ⟶ bundle.torsor.total //
        f ≫ bundle.torsor.projection = testMap Y U})
      (p' : {f : testScheme Y U' ⟶ bundle.torsor.total //
        f ≫ bundle.torsor.projection = testMap Y U'}),
    p'.val = testArrow h ≫ p.val →
      basis U' p' = (pullbackStructureIso h.left).symm ≪≫
        (Scheme.Modules.pullback h.left).mapIso (basis U p) ≪≫
        (Scheme.Modules.pullbackComp h.left U.hom).app L ≪≫
        (Scheme.Modules.pullbackCongr (Over.w h)).app L
  scalar : letI := Gm.group
    ∀ (U : Over Y.left) (t : testScheme Y U ⟶ torusScheme k 1)
      (p p' : {f : testScheme Y U ⟶ bundle.torsor.total //
        f ≫ bundle.torsor.projection = testMap Y U}),
    p'.val = CartesianMonoidalCategory.lift t p.val ≫ γ[torusScheme k 1,bundle.torsor.total] →
      basis U p' = basis U p ≪≫ scalarIso U.left ((Scheme.Modules.pullback U.hom).obj L)
        (Gm.units (testScheme Y U) t 0)

variable {r : ℕ} (T : TorusTheory k r) (Y : Over (Spec (.of k)))
  (δ : torusScheme k r ⟶ torusScheme k 1)
  (hom : letI := T.group; letI := Gm.group; IsMonHom δ)
  (P : letI := T.group; Bundle (torusScheme k r) Y)

structure CharacterLine where
  module : Y.left.Modules
  frames : LineFrames Gm Y module
  pushout : letI := T.group; letI := Gm.group; letI := hom
    ContractedTorsorModels.Pushout (torusScheme k 1) δ P frames.bundle

end MathlibExt.AlgebraicGeometry.TorusLineFrameModels
