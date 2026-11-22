/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Algebra.Category.Grp.FilteredColimits
import MathlibExt.CategoryTheory.Filtered.NatTail

/-!
# Complete natural-number tails of the actual filtered group colimit

The actual index shift is final. The same group quotient and every original
colimit leg are retained, with both comparison maps and full naturality for
all diagram transformations.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe v
open CategoryTheory CategoryTheory.Limits

namespace GrpCat.FilteredColimits

private theorem tail_desc_map_naturality {F G : ℕ ⥤ GrpCat.{v}} (c : Cocone F) (d : Cocone G)
    (a : F ⟶ G) (g : c.pt ⟶ d.pt)
    (hg : ∀ j : ℕ, c.ι.app j ≫ g = a.app j ≫ d.ι.app j) :
    colimitMap a ≫ (GrpCat.FilteredColimits.colimitCoconeIsColimit G).desc d =
      (GrpCat.FilteredColimits.colimitCoconeIsColimit F).desc c ≫ g := by
  apply (GrpCat.FilteredColimits.colimitCoconeIsColimit F).hom_ext
  intro j
  have hF := (GrpCat.FilteredColimits.colimitCoconeIsColimit F).fac c j
  have hG := (GrpCat.FilteredColimits.colimitCoconeIsColimit G).fac d j
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun r => r ≫ (GrpCat.FilteredColimits.colimitCoconeIsColimit G).desc d)
      (colimitMap_ι a j)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun r => a.app j ≫ r) hG).trans
            ((hg j).symm.trans
              ((congrArg (fun r => r ≫ g) hF.symm).trans (Category.assoc _ _ _))))))


namespace OriginalNatTailGeometry
open CategoryTheory.NatTail (tailFunctor tailFunctor_final)

/-- The entire original diagram tail retains all objects, maps and input NatTrans functions. -/
def tailDiagramFunctor (r : ℕ) : (ℕ ⥤ GrpCat.{v}) ⥤ (ℕ ⥤ GrpCat.{v}) :=
  (Functor.whiskeringLeft ℕ ℕ GrpCat.{v}).obj (tailFunctor r)

/-- The actual tail cocone retains the SAME genuine original Group quotient and original legs. -/
def tailCocone (D : ℕ ⥤ GrpCat.{v}) (r : ℕ) : Cocone (tailFunctor r ⋙ D) :=
  (GrpCat.FilteredColimits.colimitCocone D).whisker (tailFunctor r)

/-- The entire actual original tail cocone point is the SAME genuine original group colimit. -/
theorem tailCocone_pt (D : ℕ ⥤ GrpCat.{v}) (r : ℕ) :
    (tailCocone D r).pt = GrpCat.FilteredColimits.colimit D := rfl

/-- EVERY complete retained tail leg is the SAME actual original group-colimit leg. -/
theorem tailCocone_ι (D : ℕ ⥤ GrpCat.{v}) (r n : ℕ) :
    (tailCocone D r).ι.app n = (GrpCat.FilteredColimits.colimitCocone D).ι.app (r + n) := rfl

/-- Genuine source finality proves the original tail cocone's actual full colimit property. -/
def tailCoconeIsColimit (D : ℕ ⥤ GrpCat.{v}) (r : ℕ) : IsColimit (tailCocone D r) := by
  let _ : (tailFunctor r).Final := tailFunctor_final r
  exact (Functor.Final.isColimitWhiskerEquiv (tailFunctor r)
    (GrpCat.FilteredColimits.colimitCocone D)).symm
      (GrpCat.FilteredColimits.colimitCoconeIsColimit D)

/-- BOTH genuine original Group colimit maps are retained by the full actual cofinal-tail Iso. -/
def tailComparisonIso (D : ℕ ⥤ GrpCat.{v}) (r : ℕ) :
    GrpCat.FilteredColimits.colimit (tailFunctor r ⋙ D) ≅ GrpCat.FilteredColimits.colimit D :=
  (GrpCat.FilteredColimits.colimitCoconeIsColimit (tailFunctor r ⋙ D)).coconePointUniqueUpToIso
    (tailCoconeIsColimit D r)

/-- The ENTIRE full tail comparison hom is the actual genuine original quotient descent. -/
theorem tailComparisonIso_hom (D : ℕ ⥤ GrpCat.{v}) (r : ℕ) :
    (tailComparisonIso D r).hom =
      (GrpCat.FilteredColimits.colimitCoconeIsColimit (tailFunctor r ⋙ D)).desc
        (tailCocone D r) := rfl

/-- EVERY full tail-Iso hom leg is the SAME actual original unshifted group-colimit leg. -/
theorem tailComparisonIso_hom_ι (D : ℕ ⥤ GrpCat.{v}) (r n : ℕ) :
    (GrpCat.FilteredColimits.colimitCocone (tailFunctor r ⋙ D)).ι.app n ≫
        (tailComparisonIso D r).hom =
      (GrpCat.FilteredColimits.colimitCocone D).ι.app (r + n) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (GrpCat.FilteredColimits.colimitCoconeIsColimit (tailFunctor r ⋙ D))
    (tailCoconeIsColimit D r) n

/-- Every retained source leg is the full inverse tail comparison's actual tail leg. -/
theorem tailComparisonIso_inv_ι (D : ℕ ⥤ GrpCat.{v}) (r n : ℕ) :
    (GrpCat.FilteredColimits.colimitCocone D).ι.app (r + n) ≫
        (tailComparisonIso D r).inv =
      (GrpCat.FilteredColimits.colimitCocone (tailFunctor r ⋙ D)).ι.app n :=
  IsColimit.comp_coconePointUniqueUpToIso_inv
    (GrpCat.FilteredColimits.colimitCoconeIsColimit (tailFunctor r ⋙ D))
    (tailCoconeIsColimit D r) n

/-- Every original cocone leg, including indices below the offset, maps to its shifted tail leg
through the actual diagram transition. -/
theorem tailComparisonIso_inv_ι_all (D : ℕ ⥤ GrpCat.{v}) (r j : ℕ) :
    (GrpCat.FilteredColimits.colimitCocone D).ι.app j ≫ (tailComparisonIso D r).inv =
      D.map (homOfLE (Nat.le_add_left j r)) ≫
        (GrpCat.FilteredColimits.colimitCocone (tailFunctor r ⋙ D)).ι.app j := by
  have h := (GrpCat.FilteredColimits.colimitCocone D).w
    (homOfLE (Nat.le_add_left j r))
  exact (congrArg (fun f => f ≫ (tailComparisonIso D r).inv) h.symm).trans
    ((Category.assoc _ _ _).trans
      (congrArg (fun f => D.map (homOfLE (Nat.le_add_left j r)) ≫ f)
        (tailComparisonIso_inv_ι D r j)))

/-- ALL entire original diagram NatTrans maps retain the full forward cofinal-tail square. -/
theorem tailComparisonIso_naturality (r : ℕ) {D E : ℕ ⥤ GrpCat.{v}} (a : D ⟶ E) :
    GrpCat.FilteredColimits.colimitMap (Functor.whiskerLeft (tailFunctor r) a) ≫
        (tailComparisonIso E r).hom =
      (tailComparisonIso D r).hom ≫ GrpCat.FilteredColimits.colimitMap a := by
  have h := tail_desc_map_naturality (tailCocone D r)
    (tailCocone E r) (Functor.whiskerLeft (tailFunctor r) a)
    (GrpCat.FilteredColimits.colimitMap a)
    (fun n => GrpCat.FilteredColimits.colimitMap_ι a (r + n))
  exact (congrArg (fun f =>
      GrpCat.FilteredColimits.colimitMap (Functor.whiskerLeft (tailFunctor r) a) ≫ f)
        (tailComparisonIso_hom E r)).trans
    (h.trans (congrArg (fun f => f ≫ GrpCat.FilteredColimits.colimitMap a)
      (tailComparisonIso_hom D r).symm))

/-- The ENTIRE actual positive-tail colimit construction is naturally the same Group colimit. -/
def tailColimitNatIso (r : ℕ) : tailDiagramFunctor.{v} r ⋙
    GrpCat.FilteredColimits.colimitFunctor ≅
      GrpCat.FilteredColimits.colimitFunctor :=
  NatIso.ofComponents (fun D => tailComparisonIso D r)
    (fun a => tailComparisonIso_naturality r a)

/-- The ENTIRE component-Iso function is the same actual original tail quotient comparison. -/
theorem tailColimitNatIso_app (r : ℕ) (D : ℕ ⥤ GrpCat.{v}) :
    (tailColimitNatIso r).app D = tailComparisonIso D r := rfl

/-- ALL entire original diagram maps retain the full inverse actual cofinal-tail square. -/
theorem tailComparisonIso_inv_naturality (r : ℕ) {D E : ℕ ⥤ GrpCat.{v}} (a : D ⟶ E) :
    GrpCat.FilteredColimits.colimitMap a ≫ (tailComparisonIso E r).inv =
      (tailComparisonIso D r).inv ≫
        GrpCat.FilteredColimits.colimitMap (Functor.whiskerLeft (tailFunctor r) a) :=
  (tailColimitNatIso r).inv.naturality a


end OriginalNatTailGeometry
end GrpCat.FilteredColimits
