/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.SharpFibreMapWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarUnderProjectionSharp
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarUnderNerveHomFibreMaps
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RightProper

/-!
# Actual original enriched Hom weakness from a genuine weak base map

Both original component categories are groupoids, making their SAME
full native scalar-under projections sharp. Their actual full total
map is weak by the native contractions. Genuine weakness of the original
base map therefore gives the SAME full native fibre map weak, and the
actual Hom-fibre isomorphisms read back the original enriched Hom map.
This recognition does not supply weakness of a completion base map.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen
namespace SSet.ScalarUnderCategory
variable {C D : CategoryTheory.SimplicialEnrichment.Carrier.{u}}

/-- The SAME actual full original enriched Hom map is weak from its genuine original base map and groupoid
components. -/
theorem homMap_weak_of_baseMap
    [IsGroupoid (CategoryTheory.SimplicialEnrichment.ComponentCategory.objects.{u} C)]
    [IsGroupoid (CategoryTheory.SimplicialEnrichment.ComponentCategory.objects.{u} D)]
    (F : C ⟶ D) (hF : realizationWeakEquivalences (baseMap F)) (z y : C) :
    realizationWeakEquivalences (F.map z y) := by
  let _ : ModelCategory SSet.{u} := modelCategoryQuillen.modelCategory
  let m := HomotopicalAlgebra.SharpFibreMapWeak.fibreMap
    (projection C z) (projection D (F.obj z)) (totalMap F z) (baseMap F)
    (projection_natural F z) (point C y)
  have hm : realizationWeakEquivalences m :=
    HomotopicalAlgebra.SharpFibreMapWeak.fibreMap_weak
      (projection C z) (projection D (F.obj z)) (totalMap F z) (baseMap F)
      (projection_natural F z) (point C y) (projection_sharp C z)
      (projection_sharp D (F.obj z)) (totalMap_weak F z) hF
  let e : pullback (projection D (F.obj z)) (point C y ≫ baseMap F) ≅
      vertexFibre D (F.obj z) (F.obj y) :=
    pullback.congrHom rfl (point_natural F y)
  have e_fst : e.hom ≫ pullback.fst _ _ =
      pullback.fst (projection D (F.obj z)) (point C y ≫ baseMap F) := by
    exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have e_snd : e.hom ≫ pullback.snd _ _ =
      pullback.snd (projection D (F.obj z)) (point C y ≫ baseMap F) := by
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have m_fst : m ≫ pullback.fst _ _ = pullback.fst _ _ ≫ totalMap F z := pullback.lift_fst _ _ _
  have m_snd : m ≫ pullback.snd _ _ = pullback.snd (projection C z) (point C y) :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have heq : m ≫ e.hom = fibreMap F z y := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (fun k => m ≫ k) e_fst).trans
        (m_fst.trans (fibreMap_fst F z y).symm))
    · exact (Category.assoc _ _ _).trans ((congrArg (fun k => m ≫ k) e_snd).trans
        (m_snd.trans (fibreMap_snd F z y).symm))
  have hfibre : realizationWeakEquivalences (fibreMap F z y) :=
    heq ▸ realizationWeakEquivalences.comp_mem _ _ hm (realizationWeakEquivalences.of_isIso e.hom)
  exact (fibreMap_weak_iff F z y).mp hfibre

end SSet.ScalarUnderCategory
