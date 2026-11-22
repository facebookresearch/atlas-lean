/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedBeadOperator
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentIntervalFlagReadbacks
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentIntervalCoefficientOperators

/-!
# The SAME original full component outer-operator relation

Every original simplex operator gives the actual map between both whole
endpoint-trimmed flagged generators. Its complete input square and full
coefficient images are proved from the original interval square and both
whole flag readbacks. No weak outcome is supplied.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components

open OriginalBead OriginalBeadInterval SimplicialEnrichment SimplicialQuiver

variable {K : SSet.{u}} {n m : SimplexCategory} {q : SimplexCategoryᵒᵖ}
    (f : n ⟶ m) (σ : K.obj (op m)) (i j : coherentSimplex.{u} n)
    {x y : K _⦋0⦌} (hx : vertex K (K.map f.op σ) i = x)
    (hy : vertex K (K.map f.op σ) j = y) (a : (i ⟶[SSet.{u}] j).obj q)

/-- The SAME complete original source generator of the original outer-operator equation. -/
def operatorSource : Arrow K x y q := arrow K (K.map f.op σ) i j hx hy a

/-- The SAME complete original target generator of the original outer-operator equation. -/
def operatorTarget : Arrow K x y q :=
  arrow K σ ((coherentSimplexMap f).obj i) ((coherentSimplexMap f).obj j)
    ((vertex_operator K f σ i).symm.trans hx) ((vertex_operator K f σ j).symm.trans hy)
    (((coherentSimplexMap f).map i j).app q a)

private theorem sourceOrder (a : (i ⟶[SSet.{u}] j).obj q) : i.as.down ≤ j.as.down :=
  show i.as ≤ j.as from
    ((show (nerve (SimplicialThickening.Path i.as j.as)).obj q from a).obj 0).le

/-- The actual original full endpoint-trimmed operator of these SAME two original generators. -/
def generatorIntervalOperator : ⦋(trim (operatorSource f σ i j hx hy a)).dimension⦌ ⟶
    ⦋(trim (operatorTarget f σ i j hx hy a)).dimension⦌ :=
  intervalOperator f i.as.down j.as.down (sourceOrder i j a)

/-- The SAME entire endpoint-trimmed input square is the original outer operator square. -/
theorem generatorIntervalOperator_input :
    K.map (generatorIntervalOperator f σ i j hx hy a).op
      (trim (operatorTarget f σ i j hx hy a)).simplex =
        (trim (operatorSource f σ i j hx hy a)).simplex := by
  change K.map (intervalOperator f i.as.down j.as.down (sourceOrder i j a)).op
      (K.map (OriginalBeadInterval.operator (f.toOrderHom i.as.down) (f.toOrderHom j.as.down)
        (f.toOrderHom.monotone (sourceOrder i j a))).op σ) =
    K.map (OriginalBeadInterval.operator i.as.down j.as.down (sourceOrder i j a)).op (K.map f.op σ)
  rw [← CategoryTheory.comp_apply, ← K.map_comp, ← CategoryTheory.comp_apply, ← K.map_comp]
  exact congrArg (fun g : ⦋length i.as.down j.as.down⦌ ⟶ m => K.map g.op σ)
    (intervalOperator_square f i.as.down j.as.down (sourceOrder i j a))

/-- EVERY SAME full trimmed coefficient retains its literal original operator image. -/
theorem generatorIntervalOperator_flags :
    (OriginalBead.OuterOperator.map (generatorIntervalOperator f σ i j hx hy a)
      (intervalOperator_zero f i.as.down j.as.down (sourceOrder i j a))
      (intervalOperator_last f i.as.down j.as.down (sourceOrder i j a))).app q
      (trim (operatorSource f σ i j hx hy a)).coefficient =
        (trim (operatorTarget f σ i j hx hy a)).coefficient := by
  exact intervalCoefficient_operator f i.as.down j.as.down (sourceOrder i j a) a

/-- The actual full original outer-operator flagged map between the SAME complete generators. -/
def generatorOperatorMap : generatorObject (operatorSource f σ i j hx hy a) ⟶
    generatorObject (operatorTarget f σ i j hx hy a) :=
  beadOperator (trim (operatorSource f σ i j hx hy a)) (trim (operatorTarget f σ i j hx hy a))
    (generatorIntervalOperator f σ i j hx hy a)
    (intervalOperator_zero f i.as.down j.as.down (sourceOrder i j a))
    (intervalOperator_last f i.as.down j.as.down (sourceOrder i j a))
    (generatorIntervalOperator_input f σ i j hx hy a) (generatorIntervalOperator_flags f σ i j hx hy a)

/-- Both SAME original outer-operator generators have precisely the same actual full component. -/
theorem operator_component :
    ConnectedComponents.mk (generatorObject (operatorSource f σ i j hx hy a)) =
      ConnectedComponents.mk (generatorObject (operatorTarget f σ i j hx hy a)) :=
  _root_.Quotient.sound (Zigzag.of_hom (generatorOperatorMap f σ i j hx hy a))

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components
