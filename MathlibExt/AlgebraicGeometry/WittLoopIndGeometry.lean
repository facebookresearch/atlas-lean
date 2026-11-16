/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.WittLoopCorrespondences
public import MathlibExt.AlgebraicGeometry.ReductiveGroupSchemeModels
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Normalized ind-perfect geometry for actual Witt loop quotients

Finite stages are actual perfect schemes, with a separate proper finite
presentation deperfection and its universal perfection map. They are
identified with the fixed quotient sheaf through the actual colimit of
their represented point sheaves. The twofold multiplication is pinned on
every finite stage to actual scheme maps and the coequalizer product.

Reference: Zhu, arXiv:1407.8519v3, Theorem1.4 and Proposition1.20.
No perverse coefficient category, Satake equivalence or rational-base
Frobenius descent is assumed here. Generic scheme perfection and ordinary
quotient descent are completed public source integration prerequisites.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.WittLoopIndGeometry

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open WittLoopGroups WittLoopCorrespondences WittLatticeFamilies

variable (p : ℕ) [Fact p.Prime]

/-- The actual prime-field affine test functor. -/
def residueTests : (PerfectAlgebra p)ᵒᵖ ⥤ Over (Spec (.of (ZMod p))) where
  obj R := testScheme p R.unop
  map f := testMap p f.unop
  map_id R := by
    apply Over.OverMorphism.ext
    change Spec.map (𝟙 (CommRingCat.of R.unop.obj)) = 𝟙 _
    exact Spec.map_id _
  map_comp f g := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (f ≫ g).unop.hom.hom.toRingHom) =
      Spec.map (CommRingCat.ofHom f.unop.hom.hom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom g.unop.hom.hom.toRingHom)
    rw [← Spec.map_comp]
    rfl

/-- Actual scheme-valued points, restricted to perfect affine tests. -/
def schemePoints (X : Over (Spec (.of (ZMod p)))) : AffinePresheaf p :=
  (residueTests p).rightOp ⋙ yoneda.obj X ⋙ uliftFunctor.{1, 0}

/-- The actual represented-point map for a genuine scheme morphism. -/
def schemePointMap {X Y : Over (Spec (.of (ZMod p)))} (f : X ⟶ Y) :
    schemePoints p X ⟶ schemePoints p Y :=
  Functor.whiskerLeft (residueTests p).rightOp
    (Functor.whiskerRight (yoneda.map f) uliftFunctor.{1, 0})

/-- The fixed represented fpqc sheaf of each actual scheme. -/
def represented : Over (Spec (.of (ZMod p))) ⥤ Sheaf (fpqcTopology p) (Type 1) where
  obj X := (presheafToSheaf (fpqcTopology p) (Type 1)).obj
    ((opOpEquivalence (PerfectAlgebra p)).functor ⋙ schemePoints p X)
  map f := (presheafToSheaf (fpqcTopology p) (Type 1)).map
    (Functor.whiskerLeft (opOpEquivalence (PerfectAlgebra p)).functor
      (schemePointMap p f))
  map_id X := by
    have h : Functor.whiskerLeft (opOpEquivalence (PerfectAlgebra p)).functor
        (schemePointMap p (𝟙 X)) = 𝟙 _ := by
      ext R x
      simp [schemePointMap]
      rfl
    rw [h]
    exact (presheafToSheaf (fpqcTopology p) (Type 1)).map_id _
  map_comp f g := by simp [schemePointMap]

/-- Actual ind-perfect stages, with separate ordinary proper models. -/
structure IndPerfectGeometry (F : Sheaf (fpqcTopology p) (Type 1)) where
  stages : ℕ ⥤ Over (Spec (.of (ZMod p)))
  ordinary : ℕ → Over (Spec (.of (ZMod p)))
  perfection : ∀ n, PerfectSchemeModels.PerfectionModel p (ordinary n)
  stageIso : ∀ n, stages.obj n ≅ (perfection n).scheme
  [proper : ∀ n, IsProper (ordinary n).hom]
  [presentation : ∀ n, LocallyOfFinitePresentation (ordinary n).hom]
  [closed : ∀ {n m} (f : n ⟶ m), IsClosedImmersion (stages.map f).left]
  realization : colimit (stages ⋙ represented p) ≅ F

attribute [instance] IndPerfectGeometry.proper IndPerfectGeometry.presentation
  IndPerfectGeometry.closed

variable (G : Over (Spec (.of ℤ_[p]))) [GrpObj G]

/-- The actual ind-perfect Grassmannian geometric interface. -/
abbrev GrassmannianGeometry := IndPerfectGeometry p (grassmannian p G)

/-- The actual ind-perfect convolution and its normalized finite-stage maps. -/
structure ConvolutionGeometry (M : GrassmannianGeometry p G) where
  geometry : IndPerfectGeometry p (convolution p G)
  targetStage : ℕ →o ℕ
  maps : geometry.stages ⟶ targetStage.toFunctor ⋙ M.stages
  normalization : ∀ n,
    colimit.ι (geometry.stages ⋙ represented p) n ≫ geometry.realization.hom ≫
      convolutionMap p G =
        (represented p).map (maps.app n) ≫
          colimit.ι (M.stages ⋙ represented p) (targetStage n) ≫ M.realization.hom

end MathlibExt.AlgebraicGeometry.WittLoopIndGeometry
