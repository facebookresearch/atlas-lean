/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarUnderNerveSourceMaps

/-!
# Literal original fibre maps and exact Hom weak-class readback

The actual native pullback map of the SAME full original scalar under
projection is retained. Both full original fibre projections and the
genuine Hom-fibre Iso commute with the SAME entire enriched Hom map.
Consequently the actual full vertex-fibre map is weak exactly when that
original Hom map is weak. This does not assume or derive a desired
completion-unit weak outcome from an ordinary total-space comparison.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.ScalarUnderCategory

variable {C D : CategoryTheory.SimplicialEnrichment.Carrier.{u}}

/-- The SAME original point map commutes with the entire original induced base map. -/
theorem point_natural (F : C ⟶ D) (y : C) : point C y ≫ baseMap F = point D (F.obj y) := by
  have h₀ : (baseMap F).app (op ⦋0⦌) (baseVertex C y) = baseVertex D (F.obj y) :=
    Functor.ext_of_iso (Functor.constComp (Fin 1) (sourceObject C y (op ⦋0⦌)) (SSet.scalarFunctor F (op ⦋0⦌)))
      (fun _ => rfl) (fun _ => rfl)
  exact (SSet.const_comp (X := (Δ[0] : SSet.{u})) (baseVertex C y) (baseMap F)).trans
    (congrArg (fun a => SSet.const (X := (Δ[0] : SSet.{u})) a) h₀)

/-- The literal native full pullback fibre map induced by the SAME original enriched functor. -/
def fibreMap (F : C ⟶ D) (z y : C) : vertexFibre C z y ⟶ vertexFibre D (F.obj z) (F.obj y) :=
  pullback.map (projection C z) (point C y) (projection D (F.obj z)) (point D (F.obj y))
    (totalMap F z) (𝟙 (Δ[0] : SSet.{u})) (baseMap F) (projection_natural F z).symm
      ((point_natural F y).trans (Category.id_comp _).symm)

/-- The SAME actual full original fibre map retains the whole original first-projection formula. -/
theorem fibreMap_fst (F : C ⟶ D) (z y : C) :
    fibreMap F z y ≫ pullback.fst _ _ = pullback.fst _ _ ≫ totalMap F z := pullback.lift_fst _ _ _

/-- The SAME actual full original fibre map retains the complete original point-coefficient projection formula. -/
theorem fibreMap_snd (F : C ⟶ D) (z y : C) :
    fibreMap F z y ≫ pullback.snd _ _ = pullback.snd _ _ :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The genuine original whole Hom-fibre comparison square retains the SAME actual enriched Hom map and literal
native fibre map. -/
theorem homToFibre_natural (F : C ⟶ D) (z y : C) :
    homToFibre C z y ≫ fibreMap F z y = F.map z y ≫ homToFibre D (F.obj z) (F.obj y) := by
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun m => homToFibre C z y ≫ m) (fibreMap_fst F z y)).trans
        (((Category.assoc _ _ _).symm.trans
          (congrArg (fun m => m ≫ totalMap F z) (homToFibre_fst C z y))).trans
            ((homInclusion_natural F z y).trans
              ((congrArg (fun m => F.map z y ≫ m) (homToFibre_fst D (F.obj z) (F.obj y))).symm.trans
                (Category.assoc _ _ _).symm))))
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _

/-- Actual full original vertex-fibre weakness is precisely the SAME original enriched Hom weakness. -/
theorem fibreMap_weak_iff (F : C ⟶ D) (z y : C) : realizationWeakEquivalences (fibreMap F z y) ↔
    realizationWeakEquivalences (F.map z y) := by
  calc
    realizationWeakEquivalences (fibreMap F z y) ↔
        realizationWeakEquivalences (homToFibre C z y ≫ fibreMap F z y) :=
      (realizationWeakEquivalences.cancel_left_of_respectsIso _ _).symm
    _ ↔ realizationWeakEquivalences (F.map z y ≫ homToFibre D (F.obj z) (F.obj y)) :=
      Iff.of_eq (congrArg (fun f : (z ⟶[SSet.{u}] y) ⟶ vertexFibre D (F.obj z) (F.obj y) =>
        realizationWeakEquivalences f) (homToFibre_natural F z y))
    _ ↔ realizationWeakEquivalences (F.map z y) := realizationWeakEquivalences.cancel_right_of_respectsIso _ _

end SSet.ScalarUnderCategory
