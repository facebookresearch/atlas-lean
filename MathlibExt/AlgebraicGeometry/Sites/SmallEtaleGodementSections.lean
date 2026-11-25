/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleGodement
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleSkyscraperSections
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Global sections of the original Godement skyscraper product

Global sections preserve the actual product of canonical geometric-point
skyscrapers. The original terminal-section comparison at every point then
identifies these sections with the product of the given additive coefficients.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- The original skyscraper-product sections are the actual coefficient product. -/
def smallEtaleGodementSectionsComponent (X : Scheme.{u})
    (M : X → AddCommGrpCat.{max u w}) :
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).obj
        ((smallEtaleGodementSkyscrapers.{u, w} X).obj M) ≅ ∏ᶜ M :=
  PreservesProduct.iso
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w})
      (fun x : X => (smallEtaleGeometricPointCommon.{u, w}
        (smallEtaleCanonicalGeometricMorphism X x)).skyscraperSheafFunctor.obj (M x)) ≪≫
    Pi.mapIso (fun x : X =>
      (smallEtaleSkyscraperSectionsIso.{u, w}
        (smallEtaleCanonicalGeometricMorphism X x)).app (M x))

set_option backward.isDefEq.respectTransparency.types false in
/-- Every coordinate is the same actual skyscraper global-section evaluation. -/
theorem smallEtaleGodementSectionsComponent_projection (X : Scheme.{u})
    (M : X → AddCommGrpCat.{max u w}) (x : X) :
    (smallEtaleGodementSectionsComponent.{u, w} X M).hom ≫ Pi.π M x =
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).map
          (Pi.π (fun y : X => (smallEtaleGeometricPointCommon.{u, w}
            (smallEtaleCanonicalGeometricMorphism X y)).skyscraperSheafFunctor.obj (M y)) x) ≫
        (smallEtaleSkyscraperSectionsIso.{u, w}
          (smallEtaleCanonicalGeometricMorphism X x)).hom.app (M x) := by
  let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}
  let P := fun y : X => (smallEtaleGeometricPointCommon.{u, w}
    (smallEtaleCanonicalGeometricMorphism X y)).skyscraperSheafFunctor.obj (M y)
  let e : (y : X) → Γ.obj (P y) ≅ M y := fun y : X =>
    (smallEtaleSkyscraperSectionsIso.{u, w}
    (smallEtaleCanonicalGeometricMorphism X y)).app (M y)
  change ((PreservesProduct.iso Γ P).hom ≫ (Pi.mapIso e).hom) ≫ Pi.π M x = _
  rw [Category.assoc, Pi.mapIso_hom_π, ← Category.assoc,
    PreservesProduct.iso_hom, piComparison_comp_π]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The original coefficient-product comparison is natural in every family morphism. -/
theorem smallEtaleGodementSectionsComponent_naturality (X : Scheme.{u})
    {M N : X → AddCommGrpCat.{max u w}} (f : M ⟶ N) :
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).map
        ((smallEtaleGodementSkyscrapers.{u, w} X).map f) ≫
      (smallEtaleGodementSectionsComponent.{u, w} X N).hom =
        (smallEtaleGodementSectionsComponent.{u, w} X M).hom ≫
          CategoryTheory.Limits.Pi.map f := by
  apply Pi.hom_ext
  intro x
  let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}
  let R := smallEtaleGodementSkyscrapers.{u, w} X
  let p := smallEtaleGeometricPointCommon.{u, w}
    (smallEtaleCanonicalGeometricMorphism X x)
  let e := smallEtaleSkyscraperSectionsIso.{u, w}
    (smallEtaleCanonicalGeometricMorphism X x)
  let πM := Pi.π (fun y : X => (smallEtaleGeometricPointCommon.{u, w}
    (smallEtaleCanonicalGeometricMorphism X y)).skyscraperSheafFunctor.obj (M y)) x
  let πN := Pi.π (fun y : X => (smallEtaleGeometricPointCommon.{u, w}
    (smallEtaleCanonicalGeometricMorphism X y)).skyscraperSheafFunctor.obj (N y)) x
  have hp := smallEtaleGodementSkyscrapers_map_projection.{u, w} X f x
  have he : Γ.map (p.skyscraperSheafFunctor.map (f x)) ≫ e.hom.app (N x) =
      e.hom.app (M x) ≫ f x := e.hom.naturality (f x)
  have hM : (smallEtaleGodementSectionsComponent.{u, w} X M).hom ≫ Pi.π M x =
      Γ.map πM ≫ e.hom.app (M x) :=
    smallEtaleGodementSectionsComponent_projection.{u, w} X M x
  have hN : (smallEtaleGodementSectionsComponent.{u, w} X N).hom ≫ Pi.π N x =
      Γ.map πN ≫ e.hom.app (N x) :=
    smallEtaleGodementSectionsComponent_projection.{u, w} X N x
  have hm : Γ.map (R.map f) ≫ Γ.map πN =
      Γ.map πM ≫ Γ.map (p.skyscraperSheafFunctor.map (f x)) :=
    (Γ.map_comp (R.map f) πN).symm.trans
      ((congrArg Γ.map hp).trans (Γ.map_comp πM (p.skyscraperSheafFunctor.map (f x))))
  have hl : (Γ.map (R.map f) ≫ (smallEtaleGodementSectionsComponent.{u, w} X N).hom) ≫
      Pi.π N x = (Γ.map πM ≫ e.hom.app (M x)) ≫ f x :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun g => Γ.map (R.map f) ≫ g) hN).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun g => g ≫ e.hom.app (N x)) hm).trans
            ((Category.assoc _ _ _).trans
              ((congrArg (fun g => Γ.map πM ≫ g) he).trans (Category.assoc _ _ _).symm)))))
  have hr : ((smallEtaleGodementSectionsComponent.{u, w} X M).hom ≫
      CategoryTheory.Limits.Pi.map f) ≫ Pi.π N x =
        (Γ.map πM ≫ e.hom.app (M x)) ≫ f x :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun g => (smallEtaleGodementSectionsComponent.{u, w} X M).hom ≫ g)
        (Pi.map_π f x)).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (fun g => g ≫ f x) hM)))
  exact hl.trans hr.symm

/-- Actual global sections after the original skyscraper product form the coefficient product. -/
def smallEtaleGodementSectionsIso (X : Scheme.{u}) :
    smallEtaleGodementSkyscrapers.{u, w} X ⋙
        Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w} ≅
      Pi.functor (C := AddCommGrpCat.{max u w}) X :=
  NatIso.ofComponents (smallEtaleGodementSectionsComponent.{u, w} X)
    (fun f => smallEtaleGodementSectionsComponent_naturality.{u, w} X f)

end AlgebraicGeometry.Scheme.DerivedSections
