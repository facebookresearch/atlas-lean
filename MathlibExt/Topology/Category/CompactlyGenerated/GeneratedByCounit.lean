/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CompactlyGenerated.GeneratedBy

/-!
# The transported compact-generation counit

This file exposes the exact three-factor formula for the counit of the
compact-generation coreflection and its pointwise identity formula.
-/

@[expose] public section

universe u v

open CategoryTheory Topology

namespace CompactlyGenerated

/-- The transported compact-generation counit factors through the equivalence
counit and the generic generated-topology counit. -/
theorem adj_counit_app_eq_generatedBy (Y : TopCat.{v}) :
    let P := CompactlyGenerated.compactHausProbes.{u}
    let e := CompactlyGenerated.equivalenceGeneratedByTopCat.{u, v}
    let T := TopCat.toGeneratedByTopCat (X := P)
    let U := GeneratedByTopCat.toTopCat (X := P)
    let eToTop : e.functor ⋙ U ≅
      CompactlyGenerated.compactlyGeneratedToTop := Iso.refl _
    CompactlyGenerated.adj.counit.app Y =
      eToTop.inv.app ((T ⋙ e.inverse).obj Y) ≫
        U.map (e.counitIso.hom.app (T.obj Y)) ≫
          (GeneratedByTopCat.adjCounit (X := P)).app Y := by
  dsimp only
  let P := CompactlyGenerated.compactHausProbes.{u}
  let e := CompactlyGenerated.equivalenceGeneratedByTopCat.{u, v}
  let T := TopCat.toGeneratedByTopCat (X := P)
  let U := GeneratedByTopCat.toTopCat (X := P)
  let eToTop : e.functor ⋙ U ≅
      CompactlyGenerated.compactlyGeneratedToTop := Iso.refl _
  let baseAdj := e.toAdjunction.comp (GeneratedByTopCat.adj (X := P))
  change (baseAdj.ofNatIsoLeft eToTop).counit.app Y = _
  change eToTop.inv.app ((T ⋙ e.inverse).obj Y) ≫
      baseAdj.counit.app Y = _
  rw [Adjunction.comp_counit_app]
  rfl

/-- The compact-generation counit is the identity on underlying points. -/
@[simp]
theorem adjCounit_apply (Y : TopCat.{v}) (y : Y) :
    CompactlyGenerated.adj.counit.app Y y = y := by
  rw [adj_counit_app_eq_generatedBy]
  rfl

/-- The coreflection of a compactly generated space, with its identity point formula. -/
noncomputable def coreflectionCounitHomeoData
    (T : Type v) [TopologicalSpace T]
    [UCompactlyGeneratedSpace.{u} T] :
    { h : (TopCat.toCompactlyGenerated.{u, v}.obj
        (TopCat.of T) : Type v) ≃ₜ T // ∀ x, h x = x } := by
  let K : CompactlyGenerated.{u, v} := CompactlyGenerated.of T
  let e := asIso (CompactlyGenerated.adj.{u, v}.unit.app K)
  let h := TopCat.homeoOfIso
    (CompactlyGenerated.compactlyGeneratedToTop.mapIso e.symm)
  refine ⟨h, ?_⟩
  intro x
  have hmap :
      CompactlyGenerated.compactlyGeneratedToTop.map e.inv =
        CompactlyGenerated.adj.{u, v}.counit.app
          (CompactlyGenerated.compactlyGeneratedToTop.obj K) := by
    apply (cancel_epi
      (CompactlyGenerated.compactlyGeneratedToTop.map e.hom)).1
    rw [← CompactlyGenerated.compactlyGeneratedToTop.map_comp,
      Iso.hom_inv_id, CompactlyGenerated.compactlyGeneratedToTop.map_id]
    exact CompactlyGenerated.adj.{u, v}.left_triangle_components K |>.symm
  have hx := ConcreteCategory.congr_hom hmap x
  change (CompactlyGenerated.compactlyGeneratedToTop.map e.inv) x = x
  exact hx.trans
    (CompactlyGenerated.adjCounit_apply.{v, u}
      (CompactlyGenerated.compactlyGeneratedToTop.obj K) x)

end CompactlyGenerated
