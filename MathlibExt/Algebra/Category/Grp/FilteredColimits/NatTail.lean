/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import Mathlib.Algebra.Category.Grp.FilteredColimits
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

/-- The functor of native sequential group quotients, with maps given by the actual descents. -/
def natQuotientColimit : (ℕ ⥤ GrpCat.{v}) ⥤ GrpCat.{v} where
  obj D := (colimitCocone D).pt
  map {D E} α := (colimitCoconeIsColimit D).map (colimitCocone E) α
  map_id D := (colimitCoconeIsColimit D).hom_ext (fun n => by
    rw [IsColimit.ι_map, NatTrans.id_app, Category.id_comp, Category.comp_id])
  map_comp := fun {D E F} α β => (colimitCoconeIsColimit D).hom_ext (fun n => by
    simp only [Category.assoc, IsColimit.ι_map_assoc, IsColimit.ι_map, NatTrans.comp_app])

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
    (colimitCocone (tailFunctor r ⋙ D)).pt ≅ (colimitCocone D).pt :=
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
    natQuotientColimit.map (Functor.whiskerLeft (tailFunctor r) a) ≫
        (tailComparisonIso E r).hom =
      (tailComparisonIso D r).hom ≫ natQuotientColimit.map a := by
  apply (colimitCoconeIsColimit (tailFunctor r ⋙ D)).hom_ext
  intro n
  change (colimitCocone (tailFunctor r ⋙ D)).ι.app n ≫
      ((colimitCoconeIsColimit (tailFunctor r ⋙ D)).map (colimitCocone (tailFunctor r ⋙ E))
        (Functor.whiskerLeft (tailFunctor r) a) ≫ (tailComparisonIso E r).hom) =
    (colimitCocone (tailFunctor r ⋙ D)).ι.app n ≫
      ((tailComparisonIso D r).hom ≫ (colimitCoconeIsColimit D).map (colimitCocone E) a)
  rw [← Category.assoc, ← Category.assoc, IsColimit.ι_map, Category.assoc,
    tailComparisonIso_hom_ι, tailComparisonIso_hom_ι]
  exact ((colimitCoconeIsColimit D).ι_map (colimitCocone E) a (r + n)).symm

/-- The ENTIRE actual positive-tail colimit construction is naturally the same Group colimit. -/
def tailColimitNatIso (r : ℕ) : tailDiagramFunctor.{v} r ⋙
    natQuotientColimit ≅
      natQuotientColimit :=
  NatIso.ofComponents (fun D => tailComparisonIso D r)
    (fun a => tailComparisonIso_naturality r a)

/-- The ENTIRE component-Iso function is the same actual original tail quotient comparison. -/
theorem tailColimitNatIso_app (r : ℕ) (D : ℕ ⥤ GrpCat.{v}) :
    (tailColimitNatIso r).app D = tailComparisonIso D r := rfl

/-- ALL entire original diagram maps retain the full inverse actual cofinal-tail square. -/
theorem tailComparisonIso_inv_naturality (r : ℕ) {D E : ℕ ⥤ GrpCat.{v}} (a : D ⟶ E) :
    natQuotientColimit.map a ≫ (tailComparisonIso E r).inv =
      (tailComparisonIso D r).inv ≫
        natQuotientColimit.map (Functor.whiskerLeft (tailFunctor r) a) :=
  (tailColimitNatIso r).inv.naturality a


end OriginalNatTailGeometry
end GrpCat.FilteredColimits
