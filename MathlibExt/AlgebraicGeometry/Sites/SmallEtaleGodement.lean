/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleGeometricStalkExactness
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# The original small étale Godement construction

Use the actual canonical residue-field geometric points of every original
scheme. Their stalk functor takes values in families of additive groups; the
opposite direction is the actual product of their skyscraper sheaves.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- The family of actual common-universe geometric stalks on the original site. -/
def smallEtaleGodementStalks (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w} ⥤
      (X → AddCommGrpCat.{max u w}) where
  obj Q x := (smallEtaleGeometricPointCommon.{u, w}
    (smallEtaleCanonicalGeometricMorphism X x)).sheafFiber.obj Q
  map f x := (smallEtaleGeometricPointCommon.{u, w}
    (smallEtaleCanonicalGeometricMorphism X x)).sheafFiber.map f
  map_id Q := by
    funext x
    exact (smallEtaleGeometricPointCommon.{u, w}
      (smallEtaleCanonicalGeometricMorphism X x)).sheafFiber.map_id Q
  map_comp f g := by
    funext x
    exact (smallEtaleGeometricPointCommon.{u, w}
      (smallEtaleCanonicalGeometricMorphism X x)).sheafFiber.map_comp f g

/-- The actual product of canonical geometric-point skyscrapers on the same site. -/
def smallEtaleGodementSkyscrapers (X : Scheme.{u}) :
    (X → AddCommGrpCat.{max u w}) ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w} where
  obj M := ∏ᶜ fun x : X => (smallEtaleGeometricPointCommon.{u, w}
    (smallEtaleCanonicalGeometricMorphism X x)).skyscraperSheafFunctor.obj (M x)
  map {M N} f := Pi.lift fun x : X =>
    Pi.π (fun y : X => (smallEtaleGeometricPointCommon.{u, w}
      (smallEtaleCanonicalGeometricMorphism X y)).skyscraperSheafFunctor.obj (M y)) x ≫
      (smallEtaleGeometricPointCommon.{u, w}
        (smallEtaleCanonicalGeometricMorphism X x)).skyscraperSheafFunctor.map (f x)
  map_id M := by
    apply Pi.hom_ext
    intro x
    simp only [Pi.lift_comp_π, CategoryTheory.Pi.id_apply, Category.id_comp]
    have h := ((smallEtaleGeometricPointCommon.{u, w}
      (smallEtaleCanonicalGeometricMorphism X x)).skyscraperSheafFunctor
        (A := AddCommGrpCat.{max u w})).map_id (M x)
    exact (congrArg (fun f =>
      Pi.π (fun y : X => (smallEtaleGeometricPointCommon.{u, w}
        (smallEtaleCanonicalGeometricMorphism X y)).skyscraperSheafFunctor.obj (M y)) x ≫ f)
        h).trans (Category.comp_id _)
  map_comp f g := by
    apply Pi.hom_ext
    intro x
    simp only [CategoryTheory.Pi.comp_apply, Functor.map_comp, Pi.lift_comp_π,
      Category.assoc, Pi.lift_comp_π_assoc]

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual point adjunctions identify maps to the skyscraper product with stalk maps. -/
def smallEtaleGodementHomEquiv (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})
    (M : X → AddCommGrpCat.{max u w}) :
    ((smallEtaleGodementStalks.{u, w} X).obj Q ⟶ M) ≃
      (Q ⟶ (smallEtaleGodementSkyscrapers.{u, w} X).obj M) where
  toFun f := Pi.lift fun x : X =>
    (smallEtaleGeometricPointCommon.{u, w}
      (smallEtaleCanonicalGeometricMorphism X x)).skyscraperSheafAdjunction.homEquiv Q (M x)
        (f x)
  invFun g x := ((smallEtaleGeometricPointCommon.{u, w}
    (smallEtaleCanonicalGeometricMorphism X x)).skyscraperSheafAdjunction.homEquiv Q (M x)).symm
      (g ≫ Pi.π (fun y : X => (smallEtaleGeometricPointCommon.{u, w}
        (smallEtaleCanonicalGeometricMorphism X y)).skyscraperSheafFunctor.obj (M y)) x)
  left_inv f := by
    funext x
    let e := (smallEtaleGeometricPointCommon.{u, w}
      (smallEtaleCanonicalGeometricMorphism X x)).skyscraperSheafAdjunction.homEquiv Q (M x)
    have hp := Pi.lift_comp_π
      (fun y : X => (smallEtaleGeometricPointCommon.{u, w}
        (smallEtaleCanonicalGeometricMorphism X y)).skyscraperSheafAdjunction.homEquiv Q (M y)
          (f y)) x
    exact (congrArg e.symm hp).trans (e.symm_apply_apply (f x))
  right_inv g := by
    apply Pi.hom_ext
    intro x
    simp only [Pi.lift_comp_π, Equiv.apply_symm_apply]
    rfl

/-- Every product projection is exactly the original point adjunction map. -/
theorem smallEtaleGodementHomEquiv_projection (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})
    (M : X → AddCommGrpCat.{max u w})
    (f : (smallEtaleGodementStalks.{u, w} X).obj Q ⟶ M) (x : X) :
    smallEtaleGodementHomEquiv.{u, w} X Q M f ≫
        Pi.π (fun y : X => (smallEtaleGeometricPointCommon.{u, w}
          (smallEtaleCanonicalGeometricMorphism X y)).skyscraperSheafFunctor.obj (M y)) x =
      (smallEtaleGeometricPointCommon.{u, w}
        (smallEtaleCanonicalGeometricMorphism X x)).skyscraperSheafAdjunction.homEquiv Q (M x)
          (f x) :=
  Pi.lift_comp_π _ x

set_option backward.isDefEq.respectTransparency.types false in
/-- Naturality in every original sheaf morphism uses the same point adjunctions. -/
theorem smallEtaleGodementHomEquiv_naturality_left_symm (X : Scheme.{u})
    {Q Q' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}}
    (M : X → AddCommGrpCat.{max u w}) (f : Q ⟶ Q')
    (g : Q' ⟶ (smallEtaleGodementSkyscrapers.{u, w} X).obj M) :
    (smallEtaleGodementHomEquiv.{u, w} X Q M).symm (f ≫ g) =
      (smallEtaleGodementStalks.{u, w} X).map f ≫
        (smallEtaleGodementHomEquiv.{u, w} X Q' M).symm g := by
  funext x
  change ((smallEtaleGeometricPointCommon.{u, w}
    (smallEtaleCanonicalGeometricMorphism X x)).skyscraperSheafAdjunction.homEquiv Q (M x)).symm
      ((f ≫ g) ≫ Pi.π _ x) = _
  rw [Category.assoc]
  exact (smallEtaleGeometricPointCommon.{u, w}
    (smallEtaleCanonicalGeometricMorphism X
        x)).skyscraperSheafAdjunction.homEquiv_naturality_left_symm
      f (g ≫ Pi.π _ x)

/-- Every original product map has the literal skyscraper component at each point. -/
theorem smallEtaleGodementSkyscrapers_map_projection (X : Scheme.{u})
    {M N : X → AddCommGrpCat.{max u w}} (g : M ⟶ N) (x : X) :
    (smallEtaleGodementSkyscrapers.{u, w} X).map g ≫
        Pi.π (fun y : X => (smallEtaleGeometricPointCommon.{u, w}
          (smallEtaleCanonicalGeometricMorphism X y)).skyscraperSheafFunctor.obj (N y)) x =
      Pi.π (fun y : X => (smallEtaleGeometricPointCommon.{u, w}
        (smallEtaleCanonicalGeometricMorphism X y)).skyscraperSheafFunctor.obj (M y)) x ≫
          (smallEtaleGeometricPointCommon.{u, w}
            (smallEtaleCanonicalGeometricMorphism X x)).skyscraperSheafFunctor.map (g x) :=
  Pi.lift_comp_π _ x

set_option backward.isDefEq.respectTransparency.types false in
/-- Naturality in each family morphism is the original skyscraper product map. -/
theorem smallEtaleGodementHomEquiv_naturality_right (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})
    {M N : X → AddCommGrpCat.{max u w}}
    (f : (smallEtaleGodementStalks.{u, w} X).obj Q ⟶ M) (g : M ⟶ N) :
    smallEtaleGodementHomEquiv.{u, w} X Q N (f ≫ g) =
      smallEtaleGodementHomEquiv.{u, w} X Q M f ≫
        (smallEtaleGodementSkyscrapers.{u, w} X).map g := by
  apply Pi.hom_ext
  intro x
  let p := smallEtaleGeometricPointCommon.{u, w} (smallEtaleCanonicalGeometricMorphism X x)
  let h := smallEtaleGodementHomEquiv.{u, w} X Q M f
  let πM := Pi.π (fun y : X => (smallEtaleGeometricPointCommon.{u, w}
    (smallEtaleCanonicalGeometricMorphism X y)).skyscraperSheafFunctor.obj (M y)) x
  let πN := Pi.π (fun y : X => (smallEtaleGeometricPointCommon.{u, w}
    (smallEtaleCanonicalGeometricMorphism X y)).skyscraperSheafFunctor.obj (N y)) x
  have hmap := smallEtaleGodementSkyscrapers_map_projection.{u, w} X g x
  have hp := smallEtaleGodementHomEquiv_projection.{u, w} X Q M f x
  have hr : (h ≫ (smallEtaleGodementSkyscrapers.{u, w} X).map g) ≫ πN =
      p.skyscraperSheafAdjunction.homEquiv Q (M x) (f x) ≫
        p.skyscraperSheafFunctor.map (g x) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => h ≫ z) hmap).trans
        ((Category.assoc h πM (p.skyscraperSheafFunctor.map (g x))).symm.trans
          (congrArg (fun z => z ≫ p.skyscraperSheafFunctor.map (g x)) hp)))
  exact (smallEtaleGodementHomEquiv_projection.{u, w} X Q N (f ≫ g) x).trans
    ((p.skyscraperSheafAdjunction.homEquiv_naturality_right (f x) (g x)).trans hr.symm)

/-- The original stalk-family and skyscraper-product functors are genuinely adjoint. -/
def smallEtaleGodementAdjunction (X : Scheme.{u}) :
    smallEtaleGodementStalks.{u, w} X ⊣ smallEtaleGodementSkyscrapers.{u, w} X :=
  Adjunction.mkOfHomEquiv
    { homEquiv := smallEtaleGodementHomEquiv.{u, w} X
      homEquiv_naturality_left_symm := smallEtaleGodementHomEquiv_naturality_left_symm.{u, w} X _
      homEquiv_naturality_right := smallEtaleGodementHomEquiv_naturality_right.{u, w} X _ }

/-- The actual canonical geometric-stalk family is a left adjoint. -/
instance smallEtaleGodementStalks_isLeftAdjoint (X : Scheme.{u}) :
    (smallEtaleGodementStalks.{u, w} X).IsLeftAdjoint :=
  (smallEtaleGodementAdjunction.{u, w} X).isLeftAdjoint

/-- The actual product of the same point skyscrapers is the right adjoint. -/
instance smallEtaleGodementSkyscrapers_isRightAdjoint (X : Scheme.{u}) :
    (smallEtaleGodementSkyscrapers.{u, w} X).IsRightAdjoint :=
  (smallEtaleGodementAdjunction.{u, w} X).isRightAdjoint

/-- The Godement monad is constructed from the same actual point-family adjunction. -/
def smallEtaleGodementMonad (X : Scheme.{u}) :
    Monad (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :=
  (smallEtaleGodementAdjunction.{u, w} X).toMonad

/-- The constructed adjunction has precisely the original product-of-point Hom equivalence. -/
theorem smallEtaleGodementAdjunction_homEquiv (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})
    (M : X → AddCommGrpCat.{max u w}) :
    (smallEtaleGodementAdjunction.{u, w} X).homEquiv Q M =
      smallEtaleGodementHomEquiv.{u, w} X Q M :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) Q) M

/-- The actual Godement endofunctor is the same stalk family followed by its skyscraper product. -/
def smallEtaleGodement (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w} :=
  smallEtaleGodementStalks.{u, w} X ⋙ smallEtaleGodementSkyscrapers.{u, w} X

/-- The canonical Godement unit is the actual unit of the constructed point-family adjunction. -/
def smallEtaleGodementUnit (X : Scheme.{u}) :
    𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) ⟶
      smallEtaleGodement.{u, w} X :=
  (smallEtaleGodementAdjunction.{u, w} X).unit

set_option backward.isDefEq.respectTransparency.types false in
/-- Each projection of the actual Godement unit is the same original geometric germ unit. -/
theorem smallEtaleGodementUnit_projection (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (x : X) :
    (smallEtaleGodementUnit.{u, w} X).app Q ≫
        Pi.π (fun y : X => (smallEtaleGeometricPointCommon.{u, w}
          (smallEtaleCanonicalGeometricMorphism X y)).skyscraperSheafFunctor.obj
            ((smallEtaleGodementStalks.{u, w} X).obj Q y)) x =
      (smallEtaleGeometricPointCommon.{u, w}
        (smallEtaleCanonicalGeometricMorphism X x)).skyscraperSheafAdjunction.unit.app Q := by
  let L := smallEtaleGodementStalks.{u, w} X
  let adj := smallEtaleGodementAdjunction.{u, w} X
  let p := smallEtaleGeometricPointCommon.{u, w} (smallEtaleCanonicalGeometricMorphism X x)
  have he := smallEtaleGodementAdjunction_homEquiv.{u, w} X Q (L.obj Q)
  have hu : (smallEtaleGodementUnit.{u, w} X).app Q =
      smallEtaleGodementHomEquiv.{u, w} X Q (L.obj Q) (𝟙 _) :=
    (adj.homEquiv_id Q).symm.trans (congrArg (fun e => e (𝟙 _)) he)
  exact (congrArg (fun h => h ≫ Pi.π _ x) hu).trans
    ((smallEtaleGodementHomEquiv_projection.{u, w} X Q (L.obj Q) (𝟙 _) x).trans
      (p.skyscraperSheafAdjunction.homEquiv_id Q))

/-- The actual projection and point counit retract the Godement unit on each original stalk. -/
def smallEtaleGodementUnitStalkRetraction (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (x : X) :
    let p := smallEtaleGeometricPointCommon.{u, w} (smallEtaleCanonicalGeometricMorphism X x)
    p.sheafFiber.obj ((smallEtaleGodement.{u, w} X).obj Q) ⟶ p.sheafFiber.obj Q :=
  let p := smallEtaleGeometricPointCommon.{u, w} (smallEtaleCanonicalGeometricMorphism X x)
  p.sheafFiber.map (Pi.π (fun y : X => (smallEtaleGeometricPointCommon.{u, w}
    (smallEtaleCanonicalGeometricMorphism X y)).skyscraperSheafFunctor.obj
      ((smallEtaleGodementStalks.{u, w} X).obj Q y)) x) ≫
        p.skyscraperSheafAdjunction.counit.app (p.sheafFiber.obj Q)

set_option backward.isDefEq.respectTransparency.types false in
/-- The original point triangle proves the actual stalk unit and retraction compose to identity. -/
theorem smallEtaleGodementUnitStalkRetraction_identity (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (x : X) :
    let p := smallEtaleGeometricPointCommon.{u, w} (smallEtaleCanonicalGeometricMorphism X x)
    p.sheafFiber.map ((smallEtaleGodementUnit.{u, w} X).app Q) ≫
      smallEtaleGodementUnitStalkRetraction.{u, w} X Q x = 𝟙 _ := by
  let p := smallEtaleGeometricPointCommon.{u, w} (smallEtaleCanonicalGeometricMorphism X x)
  let η := (smallEtaleGodementUnit.{u, w} X).app Q
  let π := Pi.π (fun y : X => (smallEtaleGeometricPointCommon.{u, w}
    (smallEtaleCanonicalGeometricMorphism X y)).skyscraperSheafFunctor.obj
      ((smallEtaleGodementStalks.{u, w} X).obj Q y)) x
  let ε := p.skyscraperSheafAdjunction.counit.app (p.sheafFiber.obj Q)
  have hp := congrArg (fun f => p.sheafFiber.map f)
    (smallEtaleGodementUnit_projection.{u, w} X Q x)
  have hf := p.sheafFiber.map_comp η π
  exact (Category.assoc (p.sheafFiber.map η) (p.sheafFiber.map π) ε).symm.trans
    ((congrArg (fun f => f ≫ ε) (hf.symm.trans hp)).trans
      (p.skyscraperSheafAdjunction.left_triangle_components Q))

/-- On every original canonical stalk, the actual Godement unit is a split monomorphism. -/
theorem smallEtaleGodementUnit_stalk_mono (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (x : X) :
    let p := smallEtaleGeometricPointCommon.{u, w} (smallEtaleCanonicalGeometricMorphism X x)
    Mono (p.sheafFiber.map ((smallEtaleGodementUnit.{u, w} X).app Q)) := by
  let p := smallEtaleGeometricPointCommon.{u, w} (smallEtaleCanonicalGeometricMorphism X x)
  let : IsSplitMono (p.sheafFiber.map ((smallEtaleGodementUnit.{u, w} X).app Q)) :=
    IsSplitMono.mk'
      { retraction := smallEtaleGodementUnitStalkRetraction.{u, w} X Q x
        id := smallEtaleGodementUnitStalkRetraction_identity.{u, w} X Q x }
  infer_instance

/-- The same actual conservative geometric-point family makes the original Godement unit mono. -/
theorem smallEtaleGodementUnit_mono (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    Mono ((smallEtaleGodementUnit.{u, w} X).app Q) := by
  let P := smallEtaleCanonicalGeometricPointsCommon.{u, w} X
  let : ∀ Φ : P.FullSubcategory,
      Mono (Φ.obj.sheafFiber.map ((smallEtaleGodementUnit.{u, w} X).app Q)) := by
    rintro ⟨Φ, hΦ⟩
    obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff _ Φ).mp hΦ
    subst Φ
    exact smallEtaleGodementUnit_stalk_mono.{u, w} X Q x
  exact
      ((smallEtaleCanonicalGeometricPointsCommon_conservative.{u, w} X).jointlyReflectMonomorphisms
    AddCommGrpCat.{max u w}).mono _

end AlgebraicGeometry.Scheme.DerivedSections
