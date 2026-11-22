/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightCubeRealization
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFrameHom

/-!
# Genuine original quotient-cube realization and singular adjunction

The canonical coefficient Yoneda complex is right adjoint to the
SAME original colimit over every actual simplex. Both inverses of
the full Hom equivalence and all naturality maps are retained.
-/

noncomputable section
universe u
open CategoryTheory Opposite Limits
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalRightCubeRealization

/-- The SAME original full quotient-cube singular complex functor. -/
def singular : SSet.{u} ⥤ SSet.{u} :=
  yoneda ⋙ (Functor.whiskeringLeft SimplexCategoryᵒᵖ SSet.{u}ᵒᵖ (Type u)).obj
    RightCubeCosimplicial.diagram.{u}.op

/-- The original singular object is the entire same original coefficient Hom complex. -/
theorem singular_obj (H : SSet.{u}) :
    singular.obj H = FrameHom.complex RightCubeCosimplicial.diagram H := rfl

/-- Each SAME original singular source map is full coefficient postcomposition. -/
theorem singular_map_app {H H' : SSet.{u}} (f : H ⟶ H') {n : SimplexCategory}
    (g : RightCubeCosimplicial.diagram.obj n ⟶ H) :
    (singular.map f).app (op n) g = g ≫ f := rfl

/-- A whole actual original realization Hom has its SAME original coefficient restriction natural transformation. -/
def toSingular {K H : SSet.{u}} (f : object K ⟶ H) : K ⟶ singular.obj H where
  app n := ↾fun x => insertion K (op (K.elementsMk n x)) ≫ f
  naturality n m θ := by
    apply ConcreteCategory.hom_ext
    intro x
    let g : K.elementsMk n x ⟶ K.elementsMk m (K.map θ x) := Functor.Elements.homMk θ rfl
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun q => q ≫ f) (insertion_naturality K g.op)) |>.symm

/-- Every SAME original singular map determines a genuine full coefficient cocone. -/
def fromSingularCocone {K H : SSet.{u}} (f : K ⟶ singular.obj H) : Cocone (diagram K) where
  pt := H
  ι := {
    app e := f.app e.unop.obj e.unop.val
    naturality e d θ := by
      have h := congrArg (fun q => q d.unop.val) (f.naturality θ.unop.hom)
      change (diagram K).map θ ≫ f.app d.unop.obj d.unop.val =
        f.app e.unop.obj e.unop.val ≫ 𝟙 _
      exact h.symm.trans ((congrArg (fun x => f.app e.unop.obj x)
        θ.unop.map_val).trans (Category.comp_id _).symm) }

/-- The genuine same original realization map supplied by the entire coefficient cocone. -/
def fromSingular {K H : SSet.{u}} (f : K ⟶ singular.obj H) : object K ⟶ H :=
  colimit.desc (diagram K) (fromSingularCocone f)

/-- Every complete original coefficient is read back by the genuine colimit universal map. -/
theorem insertion_fromSingular {K H : SSet.{u}} (f : K ⟶ singular.obj H) (e : K.Elementsᵒᵖ) :
    insertion K e ≫ fromSingular f = f.app e.unop.obj e.unop.val :=
  colimit.ι_desc _ _

/-- Both full original maps return the SAME original realization Hom. -/
theorem from_to {K H : SSet.{u}} (f : object K ⟶ H) :
    fromSingular (toSingular f) = f := by
  apply colimit.hom_ext
  intro e
  exact insertion_fromSingular _ _

/-- Both whole original transformations return every SAME supplied original scalar simplex. -/
theorem to_from {K H : SSet.{u}} (f : K ⟶ singular.obj H) :
    toSingular (fromSingular f) = f := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  exact insertion_fromSingular _ _

/-- The genuine natural original quotient-cube realization/coefficient Hom equivalence. -/
def homEquiv (K H : SSet.{u}) :
    (object K ⟶ H) ≃ (K ⟶ singular.obj H) where
  toFun := toSingular
  invFun := fromSingular
  left_inv := from_to
  right_inv := to_from

/-- The SAME whole original coefficient Hom equivalence is natural for source simplicial maps. -/
theorem homEquiv_naturality_left {K L H : SSet.{u}} (f : K ⟶ L) (g : object L ⟶ H) :
    toSingular (map f ≫ g) = f ≫ toSingular g := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun q => q ≫ g) (insertion_map f (op (K.elementsMk n x))))

/-- The SAME whole original coefficient Hom equivalence is natural for target scalar maps. -/
theorem homEquiv_naturality_right {K H H' : SSet.{u}} (f : object K ⟶ H) (g : H ⟶ H') :
    toSingular (f ≫ g) = toSingular f ≫ singular.map g := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  change insertion K (op (K.elementsMk n x)) ≫ (f ≫ g) =
    (insertion K (op (K.elementsMk n x)) ≫ f) ≫ g
  exact (Category.assoc (insertion K (op (K.elementsMk n x))) f g).symm

/-- The actual original quotient-cube realization and original coefficient complex form a genuine adjunction. -/
def adjunction : functor.{u} ⊣ singular.{u} :=
  Adjunction.mkOfHomEquiv (F := functor.{u}) (G := singular.{u}) {
    homEquiv := homEquiv
    homEquiv_naturality_left_symm f g := by
      apply (homEquiv _ _).injective
      exact (to_from (f ≫ g)).trans
        ((congrArg (fun q => f ≫ q) (to_from g).symm).trans
          (homEquiv_naturality_left f (fromSingular g)).symm)
    homEquiv_naturality_right f g := homEquiv_naturality_right f g }

end CategoryTheory.CoherentRealization.OriginalRightCubeRealization
