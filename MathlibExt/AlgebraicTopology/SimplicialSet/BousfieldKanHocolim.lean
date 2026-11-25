/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialDiagonal
public import MathlibExt.CategoryTheory.CategoryBar.SimplicialReplacement
public import MathlibExt.CategoryTheory.Enriched.WeightedBarMapF

/-!
# Bousfield--Kan homotopy-colimit carrier

For a diagram `D : J ⥤ SSet.{max uJ vJ}` with `J : Type uJ` and
`Category.{vJ} J`, its Bousfield--Kan carrier is the
simplicial diagonal of the strict ordinary weighted bar with terminal right
weight. Diagram natural transformations induce maps of these carriers through
the landed weighted-bar functoriality.

The `GeneralizedTarget` section mirrors this API as `bkHocolimOf` /
`bkHocolimMapOf` over diagrams in `SSet.{max uJ vJ w'}`, for clients whose
indexing categories live in smaller universes than their simplicial sets.
The extra level does not infer at concrete levels, so those clients pass it
explicitly; the canonical declarations above keep their original inferable
signatures.

This file exposes only the carrier, its map, strict identity/composition laws,
and the computation on each weighted-bar coproduct inclusion. It proves no
homotopy invariance, weak-equivalence, Quillen Theorem A, realization, or
Waldhausen additivity statement.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial

universe uJ vJ

namespace SSet

/-- Bousfield--Kan homotopy-colimit carrier: the diagonal of the strict
ordinary weighted bar with terminal right weight. -/
noncomputable def bkHocolim {J : Type uJ} [Category.{vJ} J]
    (D : J ⥤ SSet.{max uJ vJ}) : SSet.{max uJ vJ} :=
  simplicialDiagonalFunctor.obj
    (StrictOrdinaryWeightedBar.wbarSimplicial
      (CategoryBar.replUnit J) D)

/-- Map of Bousfield--Kan carriers induced by a natural transformation of
diagrams. -/
noncomputable def bkHocolimMap {J : Type uJ} [Category.{vJ} J]
    {D E : J ⥤ SSet.{max uJ vJ}} (α : D ⟶ E) :
    bkHocolim D ⟶ bkHocolim E :=
  simplicialDiagonalFunctor.map
    (StrictOrdinaryWeightedBar.wbarSimplicialMapF
      (CategoryBar.replUnit J) α)

/-- In diagonal degree `n`, the carrier is the inner degree-`n` simplices of
weighted-bar degree `n`. -/
@[simp]
theorem bkHocolim_obj_mk {J : Type uJ} [Category.{vJ} J]
    (D : J ⥤ SSet.{max uJ vJ}) (n : ℕ) :
    (bkHocolim D).obj (op ⦋n⦌) =
      (StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit J) D n).obj (op ⦋n⦌) :=
  rfl

/-- In diagonal degree `n`, the induced map is the inner degree-`n` component
of the degree-`n` weighted-bar map. -/
@[simp]
theorem bkHocolimMap_app_mk {J : Type uJ} [Category.{vJ} J]
    {D E : J ⥤ SSet.{max uJ vJ}} (α : D ⟶ E) (n : ℕ) :
    (bkHocolimMap α).app (op ⦋n⦌) =
      (StrictOrdinaryWeightedBar.wbarMapF
        (W := CategoryBar.replUnit J) n α).app (op ⦋n⦌) := by
  change
    ((StrictOrdinaryWeightedBar.wbarSimplicialMapF
      (CategoryBar.replUnit J) α).app (op ⦋n⦌)).app (op ⦋n⦌) = _
  rw [StrictOrdinaryWeightedBar.wbarSimplicialMapF_app_mk]

/-- The map of Bousfield--Kan carriers preserves identity transformations
strictly. -/
@[simp]
theorem bkHocolimMap_id {J : Type uJ} [Category.{vJ} J]
    (D : J ⥤ SSet.{max uJ vJ}) :
    bkHocolimMap (𝟙 D) = 𝟙 (bkHocolim D) := by
  unfold bkHocolimMap bkHocolim
  rw [StrictOrdinaryWeightedBar.wbarSimplicialMapF_id]
  exact simplicialDiagonalFunctor.map_id _

/-- The map of Bousfield--Kan carriers preserves composition strictly. -/
@[simp]
theorem bkHocolimMap_comp {J : Type uJ} [Category.{vJ} J]
    {D E F : J ⥤ SSet.{max uJ vJ}} (α : D ⟶ E) (β : E ⟶ F) :
    bkHocolimMap (α ≫ β) = bkHocolimMap α ≫ bkHocolimMap β := by
  unfold bkHocolimMap
  rw [StrictOrdinaryWeightedBar.wbarSimplicialMapF_comp,
    Functor.map_comp]
  rfl

/-- On a weighted-bar coproduct inclusion, the diagonal map applies the
corresponding component of the diagram transformation and then includes the
same weighted chain. -/
theorem bkHocolimMap_app_mk_ι {J : Type uJ} [Category.{vJ} J]
    {D E : J ⥤ SSet.{max uJ vJ}} (α : D ⟶ E) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) ≫
      (bkHocolimMap α).app (op ⦋n⦌) =
    (α.app p.1.left).app (op ⦋n⦌) ≫
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) E n p).app (op ⦋n⦌) := by
  unfold bkHocolimMap bkHocolim
  change
    (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) ≫
      ((StrictOrdinaryWeightedBar.wbarSimplicialMapF
        (CategoryBar.replUnit J) α).app (op ⦋n⦌)).app (op ⦋n⦌) = _
  rw [StrictOrdinaryWeightedBar.wbarSimplicialMapF_app_mk]
  simpa only [NatTrans.comp_app,
    StrictOrdinaryWeightedBar.wbarSimplicial_obj_mk] using
    congrArg (fun q => q.app (op ⦋n⦌))
      (StrictOrdinaryWeightedBar.wbarMapF_ι n α p)

/-- Elementwise form of `bkHocolimMap_app_mk_ι`. -/
-- Apply before simplifying the component map, which would erase the
-- Bousfield--Kan map from the left-hand side of this rule.
@[simp↓]
theorem bkHocolimMap_app_mk_ι_apply {J : Type uJ} [Category.{vJ} J]
    {D E : J ⥤ SSet.{max uJ vJ}} (α : D ⟶ E) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n)
    (x : (D.obj p.1.left).obj (op ⦋n⦌)) :
    (bkHocolimMap α).app (op ⦋n⦌)
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) x) =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) E n p).app (op ⦋n⦌)
          ((α.app p.1.left).app (op ⦋n⦌) x) := by
  exact ConcreteCategory.congr_hom
    (bkHocolimMap_app_mk_ι α n p) x

section GeneralizedTarget

universe w'

-- Generalized-target variants: diagrams land in `SSet.{max uJ vJ w'}`
-- so one common universe can serve smaller indexing categories. The
-- target level does not infer at concrete levels; clients pass it
-- explicitly. Proofs mirror the canonical versions above.

/-- Bousfield--Kan homotopy-colimit carrier: the diagonal of the strict
ordinary weighted bar with terminal right weight. -/
noncomputable def bkHocolimOf {J : Type uJ} [Category.{vJ} J]
    (D : J ⥤ SSet.{max uJ vJ w'}) : SSet.{max uJ vJ w'} :=
  simplicialDiagonalFunctor.obj
    (StrictOrdinaryWeightedBar.wbarSimplicial
      (CategoryBar.replUnit J) D)

/-- Map of Bousfield--Kan carriers induced by a natural transformation of
diagrams. -/
noncomputable def bkHocolimMapOf {J : Type uJ} [Category.{vJ} J]
    {D E : J ⥤ SSet.{max uJ vJ w'}} (α : D ⟶ E) :
    bkHocolimOf D ⟶ bkHocolimOf E :=
  simplicialDiagonalFunctor.map
    (StrictOrdinaryWeightedBar.wbarSimplicialMapF
      (CategoryBar.replUnit J) α)

/-- In diagonal degree `n`, the carrier is the inner degree-`n` simplices of
weighted-bar degree `n`. -/
@[simp]
theorem bkHocolimOf_obj_mk {J : Type uJ} [Category.{vJ} J]
    (D : J ⥤ SSet.{max uJ vJ w'}) (n : ℕ) :
    (bkHocolimOf D).obj (op ⦋n⦌) =
      (StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit J) D n).obj (op ⦋n⦌) :=
  rfl

/-- In diagonal degree `n`, the induced map is the inner degree-`n` component
of the degree-`n` weighted-bar map. -/
@[simp]
theorem bkHocolimMapOf_app_mk {J : Type uJ} [Category.{vJ} J]
    {D E : J ⥤ SSet.{max uJ vJ w'}} (α : D ⟶ E) (n : ℕ) :
    (bkHocolimMapOf α).app (op ⦋n⦌) =
      (StrictOrdinaryWeightedBar.wbarMapF
        (W := CategoryBar.replUnit J) n α).app (op ⦋n⦌) := by
  change
    ((StrictOrdinaryWeightedBar.wbarSimplicialMapF
      (CategoryBar.replUnit J) α).app (op ⦋n⦌)).app (op ⦋n⦌) = _
  rw [StrictOrdinaryWeightedBar.wbarSimplicialMapF_app_mk]

/-- The map of Bousfield--Kan carriers preserves identity transformations
strictly. -/
@[simp]
theorem bkHocolimMapOf_id {J : Type uJ} [Category.{vJ} J]
    (D : J ⥤ SSet.{max uJ vJ w'}) :
    bkHocolimMapOf (𝟙 D) = 𝟙 (bkHocolimOf D) := by
  unfold bkHocolimMapOf bkHocolimOf
  rw [StrictOrdinaryWeightedBar.wbarSimplicialMapF_id]
  exact simplicialDiagonalFunctor.map_id _

/-- The map of Bousfield--Kan carriers preserves composition strictly. -/
@[simp]
theorem bkHocolimMapOf_comp {J : Type uJ} [Category.{vJ} J]
    {D E F : J ⥤ SSet.{max uJ vJ w'}} (α : D ⟶ E) (β : E ⟶ F) :
    bkHocolimMapOf (α ≫ β) = bkHocolimMapOf α ≫ bkHocolimMapOf β := by
  unfold bkHocolimMapOf
  rw [StrictOrdinaryWeightedBar.wbarSimplicialMapF_comp,
    Functor.map_comp]
  rfl

/-- On a weighted-bar coproduct inclusion, the diagonal map applies the
corresponding component of the diagram transformation and then includes the
same weighted chain. -/
theorem bkHocolimMapOf_app_mk_ι {J : Type uJ} [Category.{vJ} J]
    {D E : J ⥤ SSet.{max uJ vJ w'}} (α : D ⟶ E) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) ≫
      (bkHocolimMapOf α).app (op ⦋n⦌) =
    (α.app p.1.left).app (op ⦋n⦌) ≫
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) E n p).app (op ⦋n⦌) := by
  unfold bkHocolimMapOf bkHocolimOf
  change
    (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) ≫
      ((StrictOrdinaryWeightedBar.wbarSimplicialMapF
        (CategoryBar.replUnit J) α).app (op ⦋n⦌)).app (op ⦋n⦌) = _
  rw [StrictOrdinaryWeightedBar.wbarSimplicialMapF_app_mk]
  simpa only [NatTrans.comp_app,
    StrictOrdinaryWeightedBar.wbarSimplicial_obj_mk] using
    congrArg (fun q => q.app (op ⦋n⦌))
      (StrictOrdinaryWeightedBar.wbarMapF_ι n α p)

/-- Elementwise form of `bkHocolimMapOf_app_mk_ι`. -/
-- Apply before simplifying the component map, which would erase the
-- Bousfield--Kan map from the left-hand side of this rule.
@[simp↓]
theorem bkHocolimMapOf_app_mk_ι_apply {J : Type uJ} [Category.{vJ} J]
    {D E : J ⥤ SSet.{max uJ vJ w'}} (α : D ⟶ E) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n)
    (x : (D.obj p.1.left).obj (op ⦋n⦌)) :
    (bkHocolimMapOf α).app (op ⦋n⦌)
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) x) =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) E n p).app (op ⦋n⦌)
          ((α.app p.1.left).app (op ⦋n⦌) x) := by
  exact ConcreteCategory.congr_hom
    (bkHocolimMapOf_app_mk_ι α n p) x

end GeneralizedTarget

end SSet

end
