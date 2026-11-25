/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanHocolim

/-!
# Original common-universe BK carrier clients

The original terminal-weight index retains its right endpoint and every
diagram-map computation retains that entire index, acting at its left endpoint.
All simplicial operators and the strict functor laws use the original map.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Simplicial

universe uJ vJ

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.CommonUniverseBKCarrierTests

variable {J : Type uJ} [Category.{vJ} J]
variable {D E F : J ⥤ SSet.{max uJ vJ}}

/-- The original degree is the matching inner degree of the terminal-weight
bar, for independent object and morphism universes. -/
theorem originalDiagonalDegree (n : ℕ) :
    (SSet.bkHocolim D).obj (op ⦋n⦌) =
      (StrictOrdinaryWeightedBar.wbarObj (CategoryBar.replUnit J) D n).obj (op ⦋n⦌) :=
  SSet.bkHocolim_obj_mk D n

/-- Both transformations retain the actual terminal-right index and apply
their components at the original left endpoint of every original simplex. -/
theorem originalTerminalIndex_leftMap (α : D ⟶ E) (β : E ⟶ F) (n : ℕ)
    (s : ComposableArrows J n) (x : (D.obj s.left).obj (op ⦋n⦌)) :
    let p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n := ⟨s, PUnit.unit⟩
    p.2 = PUnit.unit ∧
      (SSet.bkHocolimMap α).app (op ⦋n⦌)
        ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) x) =
        (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) E n p).app (op ⦋n⦌)
          ((α.app s.left).app (op ⦋n⦌) x) ∧
      (SSet.bkHocolimMap (α ≫ β)).app (op ⦋n⦌)
        ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) x) =
        (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) F n p).app (op ⦋n⦌)
          ((β.app s.left).app (op ⦋n⦌) ((α.app s.left).app (op ⦋n⦌) x)) := by
  let p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n := ⟨s, PUnit.unit⟩
  exact ⟨rfl, SSet.bkHocolimMap_app_mk_ι_apply α n p x,
    SSet.bkHocolimMap_app_mk_ι_apply (α ≫ β) n p x⟩

/-- Every original simplicial operator commutes with the actual diagram map. -/
theorem originalSimplicialMap_naturality (α : D ⟶ E)
    {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    (SSet.bkHocolim D).map f ≫ (SSet.bkHocolimMap α).app b =
      (SSet.bkHocolimMap α).app a ≫ (SSet.bkHocolim E).map f :=
  (SSet.bkHocolimMap α).naturality f

/-- All faces and degeneracies retain both original endpoints and commute
with the same original carrier map. -/
theorem originalFacesDegeneracies (α : D ⟶ E) (n : ℕ) :
    (∀ i : Fin (n + 2),
      (SSet.bkHocolim D).δ i ≫ (SSet.bkHocolimMap α).app (op ⦋n⦌) =
        (SSet.bkHocolimMap α).app (op ⦋n + 1⦌) ≫ (SSet.bkHocolim E).δ i) ∧
    (∀ i : Fin (n + 1),
      (SSet.bkHocolim D).σ i ≫ (SSet.bkHocolimMap α).app (op ⦋n + 1⦌) =
        (SSet.bkHocolimMap α).app (op ⦋n⦌) ≫ (SSet.bkHocolim E).σ i) :=
  ⟨fun i => originalSimplicialMap_naturality α (SimplexCategory.δ i).op,
    fun i => originalSimplicialMap_naturality α (SimplexCategory.σ i).op⟩

/-- The original complete maps retain strict identities and composition. -/
theorem originalStrictFunctorLaws (α : D ⟶ E) (β : E ⟶ F) :
    SSet.bkHocolimMap (𝟙 D) = 𝟙 (SSet.bkHocolim D) ∧
      SSet.bkHocolimMap (α ≫ β) = SSet.bkHocolimMap α ≫ SSet.bkHocolimMap β :=
  ⟨SSet.bkHocolimMap_id D, SSet.bkHocolimMap_comp α β⟩

end MathlibExtTest.AlgebraicTopology.SimplicialSet.CommonUniverseBKCarrierTests

end
