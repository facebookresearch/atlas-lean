/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Presentable.FiniteSourceClosure
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.SimplexClosedSource
public import MathlibExt.Topology.Category.CGWH.Colimits
public import Batteries.Tactic.Lint

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace MathlibExtTest.ActualFiniteSourceClosure

example {C : Type u} [Category.{v} C]
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    {J : Type w} [SmallCategory J] [IsCardinalFiltered J κ]
    (F : J ⥤ C) {K : Type} [SmallCategory K] [FinCategory K]
    {D : K ⥤ C} (c : Cocone D) (hc : IsColimit c)
    (hSources : ∀ k : K, PreservesColimit F (coyoneda.obj (Opposite.op (D.obj k)))) :
    PreservesColimit F (coyoneda.obj (Opposite.op c.pt)) :=
  preservesColimit_coyoneda_of_finiteColimit κ F c hc hSources

section ActualPointedSimplexCoproduct

variable (n m : ℕ)
    (F : realizedGeneratorCardinal.{v}.ord.ToType ⥤ PointedCGWH.{u, v})
    [F.IsWellOrderContinuous]
    (hF : ∀ ⦃a b⦄ (φ : a ⟶ b),
      Topology.IsClosedEmbedding (ConcreteCategory.hom (F.map φ).right))

example : PreservesColimit F (coyoneda.obj (Opposite.op
    (((Under.costar CGWH.point.{u, v}).obj
        (SSet.toCGWH.{u, v}.obj (Δ[n] : SSet.{v}))) ⨿
      ((Under.costar CGWH.point.{u, v}).obj
        (SSet.toCGWH.{u, v}.obj (Δ[m] : SSet.{v})))))) := by
  let κ := realizedGeneratorCardinal.{v}
  let L := Under.costar CGWH.point.{u, v}
  let A := L.obj (SSet.toCGWH.{u, v}.obj (Δ[n] : SSet.{v}))
  let B := L.obj (SSet.toCGWH.{u, v}.obj (Δ[m] : SSet.{v}))
  let _ : Fact κ.IsRegular := ⟨isRegular_realizedGeneratorCardinal.{v}⟩
  let _ : IsCardinalFiltered κ.ord.ToType κ := inferInstance
  apply preservesColimit_coyoneda_of_finiteColimit κ F
    (BinaryCofan.mk coprod.inl coprod.inr) (coprodIsCoprod A B)
  intro k
  rcases k with ⟨k⟩
  cases k with
  | left => exact PointedCGWH.realizedSimplexSource_preservesClosedColimit n F hF
  | right => exact PointedCGWH.realizedSimplexSource_preservesClosedColimit m F hF

end ActualPointedSimplexCoproduct

#print axioms CategoryTheory.Limits.preservesColimit_coyoneda_of_isColimit
#print axioms CategoryTheory.Limits.preservesColimit_coyoneda_of_finiteColimit

#lint only unusedArguments in MathlibExt.CategoryTheory.Presentable.FiniteSourceClosure

end MathlibExtTest.ActualFiniteSourceClosure
