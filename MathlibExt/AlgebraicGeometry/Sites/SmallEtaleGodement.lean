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
# The geometric stalk and skyscraper adjunction

For a scheme `X`, choose at each point the geometric morphism from the separable closure of
its residue field. With coefficient universe `max u w`, the stalk-family functor takes a sheaf
to its family of geometric stalks. Its right adjoint takes a family of additive groups to the
product of the corresponding skyscraper sheaves.

The resulting Godement monad sends a sheaf to the product of its stalk skyscrapers. Its unit
is monic: at each canonical stalk it has a retraction given by the relevant product projection
and skyscraper counit.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- Family of canonical geometric stalks.

Send an abelian sheaf to its stalk at each canonical residue-field geometric point, giving a
functor to families of additive groups indexed by `X`. -/
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

/-- Product of canonical geometric skyscraper sheaves.

Send a coefficient family `M` to the product over all points `x` of the skyscraper sheaf with
coefficient `M x` at the canonical geometric point. -/
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
/-- Stalk family maps correspond to skyscraper product maps.

A family of maps from the canonical stalks of `Q` to `M` corresponds to a sheaf map from `Q`
to the product of skyscrapers of `M`. -/
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

/-- Stalk skyscraper correspondence at a product coordinate.

Project the associated sheaf map to the skyscraper at `x`; the result is the individual stalk-
skyscraper adjunction map of the family component at `x`. -/
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
/-- Stalk skyscraper correspondence is natural in the sheaf.

The inverse Hom correspondence commutes with precomposition by a sheaf morphism and its
induced stalk-family map. -/
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

/-- Skyscraper product map at a point coordinate.

The product map induced by a coefficient-family morphism, followed by projection at `x`,
equals projection at `x` followed by the skyscraper map of the family component. -/
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
/-- Stalk skyscraper correspondence is natural in coefficient families.

Postcomposition by a family map corresponds to postcomposition by its product-of-skyscrapers
map. -/
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

/-- Canonical stalk families are left adjoint to skyscraper products.

The pointwise stalk-skyscraper adjunctions and product universal property give the adjunction
of the stalk-family and skyscraper-product functors. -/
def smallEtaleGodementAdjunction (X : Scheme.{u}) :
    smallEtaleGodementStalks.{u, w} X ⊣ smallEtaleGodementSkyscrapers.{u, w} X :=
  Adjunction.mkOfHomEquiv
    { homEquiv := smallEtaleGodementHomEquiv.{u, w} X
      homEquiv_naturality_left_symm := smallEtaleGodementHomEquiv_naturality_left_symm.{u, w} X _
      homEquiv_naturality_right := smallEtaleGodementHomEquiv_naturality_right.{u, w} X _ }

/-- Canonical stalk family functor is a left adjoint.

The stalk-family functor has the skyscraper-product functor as right adjoint. -/
instance smallEtaleGodementStalks_isLeftAdjoint (X : Scheme.{u}) :
    (smallEtaleGodementStalks.{u, w} X).IsLeftAdjoint :=
  (smallEtaleGodementAdjunction.{u, w} X).isLeftAdjoint

/-- Canonical skyscraper product functor is a right adjoint.

The skyscraper-product functor is right adjoint to the stalk-family functor. -/
instance smallEtaleGodementSkyscrapers_isRightAdjoint (X : Scheme.{u}) :
    (smallEtaleGodementSkyscrapers.{u, w} X).IsRightAdjoint :=
  (smallEtaleGodementAdjunction.{u, w} X).isRightAdjoint

/-- Godement monad from the stalk skyscraper adjunction.

The stalk-family adjunction induces a monad on common-universe small étale abelian sheaves. -/
def smallEtaleGodementMonad (X : Scheme.{u}) :
    Monad (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :=
  (smallEtaleGodementAdjunction.{u, w} X).toMonad

/-- Godement adjunction has the pointwise Hom correspondence.

The Hom equivalence of the assembled adjunction is the correspondence formed from the
individual stalk-skyscraper adjunctions. -/
theorem smallEtaleGodementAdjunction_homEquiv (X : Scheme.{u})
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})
    (M : X → AddCommGrpCat.{max u w}) :
    (smallEtaleGodementAdjunction.{u, w} X).homEquiv Q M =
      smallEtaleGodementHomEquiv.{u, w} X Q M :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) Q) M

/-- Godement endofunctor on abelian sheaves.

Apply the canonical stalk-family functor and then the product-of-skyscrapers functor. -/
def smallEtaleGodement (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w} :=
  smallEtaleGodementStalks.{u, w} X ⋙ smallEtaleGodementSkyscrapers.{u, w} X

/-- Natural map from a sheaf to its stalk skyscraper product.

The unit of the stalk-family adjunction gives `Q → Godement(Q)` naturally in the sheaf. -/
def smallEtaleGodementUnit (X : Scheme.{u}) :
    𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) ⟶
      smallEtaleGodement.{u, w} X :=
  (smallEtaleGodementAdjunction.{u, w} X).unit

set_option backward.isDefEq.respectTransparency.types false in
/-- Godement unit projects to the individual point unit.

At point `x`, the Godement unit followed by the corresponding skyscraper projection equals the
unit of that point's stalk-skyscraper adjunction. -/
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

/-- Retraction of the Godement unit at a canonical stalk.

At the stalk of `x`, project the Godement product to its `x` skyscraper and apply the point
counit to obtain a map back to the stalk of `Q`. -/
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
/-- Canonical stalk retraction is a left inverse to the unit.

The stalk map of the Godement unit followed by its point retraction is the identity. -/
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

/-- Godement unit is monic at every canonical stalk.

Each canonical stalk map of the Godement unit is a monomorphism, since it has the displayed
retraction. -/
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

/-- Godement unit is a sheaf monomorphism.

The map from a sheaf to its canonical stalk skyscraper product is monic, as detected by the
conservative canonical geometric stalk family. -/
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
