/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHHornIntervalAction
public import MathlibExt.Topology.Category.CGWH.Path
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath

/-!
# Comparing the literal and realized native intervals

The literal lifted unit interval used by the horn homotopy is compared with
the native realization of the one-simplex. The maps are the fully faithful
preimages of the existing realization comparison and simplex homeomorphism.
The ordered endpoints retain `δ 1` at time zero and `δ 0` at time one.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace CGWH

/-- The literal lifted homotopy interval is canonically the realized native
one-simplex, using the complete existing TopCat realization isomorphism. -/
noncomputable def homotopyIntervalIsoInterval :
    homotopyInterval.{u, v} ≅ interval.{u, v} :=
  fullyFaithfulCgwhToTop.{u, v}.preimageIso
    (X := homotopyInterval.{u, v}) (Y := interval.{u, v})
    ((SSet.realizationToTopIso.{u, v}.app (Δ[1] : SSet.{v})) ≪≫
      SSet.stdSimplex.toTopObjIsoI.{v}).symm

/-- The forward native comparison is the full inverse simplex realization
map after forgetting to TopCat. -/
theorem cgwhToTop_map_homotopyIntervalIsoInterval_hom :
    cgwhToTop.map homotopyIntervalIsoInterval.{u, v}.hom =
      ((SSet.realizationToTopIso.{u, v}.app (Δ[1] : SSet.{v})) ≪≫
        SSet.stdSimplex.toTopObjIsoI.{v}).inv := by
  dsimp only [homotopyIntervalIsoInterval, Functor.FullyFaithful.preimageIso]
  exact fullyFaithfulCgwhToTop.map_preimage _

/-- The inverse native comparison is the full forward simplex realization
map after forgetting to TopCat. -/
theorem cgwhToTop_map_homotopyIntervalIsoInterval_inv :
    cgwhToTop.map homotopyIntervalIsoInterval.{u, v}.inv =
      ((SSet.realizationToTopIso.{u, v}.app (Δ[1] : SSet.{v})) ≪≫
        SSet.stdSimplex.toTopObjIsoI.{v}).hom := by
  dsimp only [homotopyIntervalIsoInterval, Functor.FullyFaithful.preimageIso]
  exact fullyFaithfulCgwhToTop.map_preimage _

/-- Time zero of the literal interval becomes the realized source vertex,
with the actual terminal map from the selected tensor unit retained. -/
theorem homotopyIntervalIsoInterval_zero :
    homotopyIntervalEndpoint.{u, v} 0 ≫ homotopyIntervalIsoInterval.{u, v}.hom =
      point_isTerminal.from (𝟙_ CGWH.{u, v}) ≫ intervalZero.{u, v} := by
  apply fullyFaithfulCgwhToTop.{u, v}.map_injective
  rw [Functor.map_comp, Functor.map_comp,
    cgwhToTop_map_homotopyIntervalIsoInterval_hom]
  apply TopCat.ext
  intro x
  let p : point.{u, v} :=
    cgwhToTop.map (point_isTerminal.from (𝟙_ CGWH.{u, v})) x
  have hp : cgwhToTop.{u, v}.map
      SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}.inv p =
      (default : SSet.toTop.obj (Δ[0] : SSet.{v})) := by
    apply (TopCat.homeoOfIso (cgwhToTop.mapIso
      SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v})).injective
    cases p
    rfl
  change SSet.stdSimplex.toTopObjIsoI.inv (0 : TopCat.I.{v}) =
    SSet.toTop.map (SSet.stdSimplex.δ 1)
      (cgwhToTop.map SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.inv p)
  rw [hp]
  exact SSet.toTopObjIsoI_inv_zero

/-- Time one of the literal interval becomes the realized target vertex,
with the actual terminal map from the selected tensor unit retained. -/
theorem homotopyIntervalIsoInterval_one :
    homotopyIntervalEndpoint.{u, v} 1 ≫ homotopyIntervalIsoInterval.{u, v}.hom =
      point_isTerminal.from (𝟙_ CGWH.{u, v}) ≫ intervalOne.{u, v} := by
  apply fullyFaithfulCgwhToTop.{u, v}.map_injective
  rw [Functor.map_comp, Functor.map_comp,
    cgwhToTop_map_homotopyIntervalIsoInterval_hom]
  apply TopCat.ext
  intro x
  let p : point.{u, v} :=
    cgwhToTop.map (point_isTerminal.from (𝟙_ CGWH.{u, v})) x
  have hp : cgwhToTop.{u, v}.map
      SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}.inv p =
      (default : SSet.toTop.obj (Δ[0] : SSet.{v})) := by
    apply (TopCat.homeoOfIso (cgwhToTop.mapIso
      SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v})).injective
    cases p
    rfl
  change SSet.stdSimplex.toTopObjIsoI.inv (1 : TopCat.I.{v}) =
    SSet.toTop.map (SSet.stdSimplex.δ 0)
      (cgwhToTop.map SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.inv p)
  rw [hp]
  exact SSet.toTopObjIsoI_inv_one

end CGWH
