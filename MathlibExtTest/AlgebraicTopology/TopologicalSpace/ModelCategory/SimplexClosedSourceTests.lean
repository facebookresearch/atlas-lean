/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.SimplexClosedSource
public import Batteries.Tactic.Lint

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace MathlibExtTest.NativeSimplexClosedSource

example (n : ℕ) :
    Retract (Δ[n] : SSet.{v})
      (Λ[n + 1, (0 : Fin (n + 1)).succ] : SSet.{v}) :=
  SSet.simplexHornRetract n

example (n : ℕ) :
    (SSet.simplexHornRetract.{v} n).i ≫ (SSet.simplexHornRetract.{v} n).r =
      𝟙 (Δ[n] : SSet.{v}) :=
  (SSet.simplexHornRetract n).retract

example (n : ℕ) :
    (SSet.simplexHornRetract.{v} n).i ≫
        (Λ[n + 1, (0 : Fin (n + 1)).succ]).ι =
      SSet.stdSimplex.δ (0 : Fin (n + 1)).castSucc :=
  SSet.simplexHornRetract_i_ι n

-- The zero-dimensional case remains the actual zero coface/codegeneracy retract.
example :
    (SSet.simplexHornRetract.{v} 0).i ≫ (SSet.simplexHornRetract.{v} 0).r =
      𝟙 (Δ[0] : SSet.{v}) :=
  (SSet.simplexHornRetract 0).retract

example (n : ℕ) :
    (CGWH.realizedSimplexHornRetract.{u, v} n).i ≫
        (CGWH.realizedSimplexHornRetract.{u, v} n).r =
      𝟙 (SSet.toCGWH.{u, v}.obj (Δ[n] : SSet.{v})) :=
  (CGWH.realizedSimplexHornRetract n).retract

example (n : ℕ) :
    (PointedCGWH.realizedSimplexHornRetract.{u, v} n).i ≫
        (PointedCGWH.realizedSimplexHornRetract.{u, v} n).r =
      𝟙 ((Under.costar CGWH.point.{u, v}).obj
        (SSet.toCGWH.{u, v}.obj (Δ[n] : SSet.{v}))) :=
  (PointedCGWH.realizedSimplexHornRetract n).retract

section NativeChains

variable (n : ℕ)
    (F : realizedGeneratorCardinal.{v}.ord.ToType ⥤ CGWH.{u, v})
    [F.IsWellOrderContinuous]
    (hF : ∀ ⦃a b⦄ (φ : a ⟶ b),
      Topology.IsClosedEmbedding (CGWH.cgwhToTop.map (F.map φ)).hom)

example : PreservesColimit F
    (coyoneda.obj (Opposite.op (SSet.toCGWH.{u, v}.obj (Δ[n] : SSet.{v})))) :=
  CGWH.realizedSimplexSource_preservesClosedColimit n F hF

example (c : Cocone F) (hc : IsColimit c) :
    IsColimit ((coyoneda.obj (Opposite.op
      (SSet.toCGWH.{u, v}.obj (Δ[n] : SSet.{v})))).mapCocone c) := by
  let _ := CGWH.realizedSimplexSource_preservesClosedColimit n F hF
  exact isColimitOfPreserves _ hc

end NativeChains

section PointedChains

variable (n : ℕ)
    (F : realizedGeneratorCardinal.{v}.ord.ToType ⥤ PointedCGWH.{u, v})
    [F.IsWellOrderContinuous]
    (hF : ∀ ⦃a b⦄ (φ : a ⟶ b),
      Topology.IsClosedEmbedding (ConcreteCategory.hom (F.map φ).right))

example : PreservesColimit F (coyoneda.obj (Opposite.op
    ((Under.costar CGWH.point.{u, v}).obj
      (SSet.toCGWH.{u, v}.obj (Δ[n] : SSet.{v}))))) :=
  PointedCGWH.realizedSimplexSource_preservesClosedColimit n F hF

example (c : Cocone F) (hc : IsColimit c) :
    IsColimit ((coyoneda.obj (Opposite.op
      ((Under.costar CGWH.point.{u, v}).obj
        (SSet.toCGWH.{u, v}.obj (Δ[n] : SSet.{v}))))).mapCocone c) := by
  let _ := PointedCGWH.realizedSimplexSource_preservesClosedColimit n F hF
  exact isColimitOfPreserves _ hc

end PointedChains

#check @CGWH.realizedSimplexSource_preservesClosedColimit.{0, 0}
#check @CGWH.realizedSimplexSource_preservesClosedColimit.{0, 1}
#check @CGWH.realizedSimplexSource_preservesClosedColimit.{1, 0}
#check @CGWH.realizedSimplexSource_preservesClosedColimit.{1, 1}
#check @PointedCGWH.realizedSimplexSource_preservesClosedColimit.{0, 0}
#check @PointedCGWH.realizedSimplexSource_preservesClosedColimit.{0, 1}
#check @PointedCGWH.realizedSimplexSource_preservesClosedColimit.{1, 0}
#check @PointedCGWH.realizedSimplexSource_preservesClosedColimit.{1, 1}

#print axioms SSet.simplexHornRetract
#print axioms SSet.simplexHornRetract_i_ι
#print axioms SSet.simplexHornRetract_r
#print axioms CGWH.realizedSimplexHornRetract
#print axioms CGWH.realizedSimplexSource_preservesClosedColimit
#print axioms PointedCGWH.realizedSimplexHornRetract
#print axioms PointedCGWH.realizedSimplexSource_preservesClosedColimit

#lint only unusedArguments in MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.SimplexClosedSource

end MathlibExtTest.NativeSimplexClosedSource
