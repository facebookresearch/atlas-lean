/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.CartesianClosed
public import MathlibExt.AlgebraicTopology.SimplicialSet.CGWHRealization
public import MathlibExt.AlgebraicTopology.TopologicalSpace.CGWH.FiniteZero
public import MathlibExt.Topology.Category.CGWH.Colimits

/-!
# Native paths in compactly generated weak Hausdorff spaces

The interval is the native CGWH realization of the simplicial one-simplex.
Its two vertices define endpoint evaluations on the internal-Hom path
functor, and currying the Cartesian projection defines constant paths.
Everything in this file is independent of the selected model structure.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped Simplicial

namespace CGWH

/-- The native interval, realized from the simplicial one-simplex. -/
noncomputable def interval : CGWH.{u, v} :=
  SSet.toCGWH.{u, v}.obj (Δ[1] : SSet.{v})

/-- The time-zero point of the native interval. -/
noncomputable def intervalZero :
    CGWH.point.{u, v} ⟶ interval.{u, v} :=
  (SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv ≫
    SSet.toCGWH.{u, v}.map
      (SSet.stdSimplex.δ (1 : Fin 2))

/-- The time-one point of the native interval. -/
noncomputable def intervalOne :
    CGWH.point.{u, v} ⟶ interval.{u, v} :=
  (SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv ≫
    SSet.toCGWH.{u, v}.map
      (SSet.stdSimplex.δ (0 : Fin 2))

/-- The ordered pair of endpoints included into the native interval. -/
noncomputable def intervalBoundary :
    CGWH.point.{u, v} ⨿ CGWH.point.{u, v} ⟶ interval.{u, v} :=
  coprod.desc intervalZero intervalOne

/-- The terminal augmentation of the native interval. -/
noncomputable def intervalAugmentation :
    interval.{u, v} ⟶ CGWH.point.{u, v} :=
  CGWH.point_isTerminal.from interval

/-- The native path endofunctor, as the internal Hom from the interval. -/
noncomputable abbrev path : CGWH.{u, v} ⥤ CGWH.{u, v} :=
  ihom interval

/-- Evaluation of a native path at time zero. -/
noncomputable def pathEvalZero :
    path.{u, v} ⟶ 𝟭 CGWH.{u, v} where
  app B := by
    let e : (𝟙_ CGWH.{u, v}) ⟶ interval.{u, v} :=
      CGWH.point_isTerminal.from (𝟙_ CGWH.{u, v}) ≫ intervalZero
    exact (λ_ (path.{u, v}.obj B)).inv ≫
      (e ▷ path.{u, v}.obj B) ≫ (ihom.ev interval.{u, v}).app B
  naturality _ _ f := by
    dsimp [path]
    rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
      ihom.ev_naturality]
    simp only [Category.assoc]

/-- Evaluation of a native path at time one. -/
noncomputable def pathEvalOne :
    path.{u, v} ⟶ 𝟭 CGWH.{u, v} where
  app B := by
    let e : (𝟙_ CGWH.{u, v}) ⟶ interval.{u, v} :=
      CGWH.point_isTerminal.from (𝟙_ CGWH.{u, v}) ≫ intervalOne
    exact (λ_ (path.{u, v}.obj B)).inv ≫
      (e ▷ path.{u, v}.obj B) ≫ (ihom.ev interval.{u, v}).app B
  naturality _ _ f := by
    dsimp [path]
    rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
      ihom.ev_naturality]
    simp only [Category.assoc]

/-- The paired endpoint evaluation of a native path. -/
noncomputable def pathEndpoints :
    path.{u, v} ⟶
      Functor.diag CGWH.{u, v} ⋙ tensor CGWH.{u, v} where
  app B := CartesianMonoidalCategory.lift
    (pathEvalZero.app B) (pathEvalOne.app B)
  naturality X Y f := by
    change path.map f ≫ CartesianMonoidalCategory.lift
        (pathEvalZero.app Y) (pathEvalOne.app Y) =
      CartesianMonoidalCategory.lift
          (pathEvalZero.app X) (pathEvalOne.app X) ≫ (f ⊗ₘ f)
    rw [CartesianMonoidalCategory.comp_lift,
      pathEvalZero.naturality, pathEvalOne.naturality,
      CartesianMonoidalCategory.lift_map]
    simp only [Functor.id_map]

/-- The natural transformation of constant native paths. -/
noncomputable def pathConstant :
    𝟭 CGWH.{u, v} ⟶ path.{u, v} where
  app B := MonoidalClosed.curry
    (CartesianMonoidalCategory.snd interval.{u, v} B)
  naturality X Y f := by
    change f ≫ MonoidalClosed.curry
        (CartesianMonoidalCategory.snd interval.{u, v} Y) =
      MonoidalClosed.curry
          (CartesianMonoidalCategory.snd interval.{u, v} X) ≫
        (ihom interval.{u, v}).map f
    rw [← MonoidalClosed.curry_natural_left,
      ← MonoidalClosed.curry_natural_right,
      CartesianMonoidalCategory.whiskerLeft_snd]

/-- The paired endpoint map projects to time-zero evaluation. -/
theorem pathEndpoints_fst (B : CGWH.{u, v}) :
    pathEndpoints.{u, v}.app B ≫
        CartesianMonoidalCategory.fst B B =
      pathEvalZero.{u, v}.app B := by
  simp [pathEndpoints]

/-- The paired endpoint map projects to time-one evaluation. -/
theorem pathEndpoints_snd (B : CGWH.{u, v}) :
    pathEndpoints.{u, v}.app B ≫
        CartesianMonoidalCategory.snd B B =
      pathEvalOne.{u, v}.app B := by
  simp [pathEndpoints]

/-- A constant path evaluates to its point at time zero. -/
theorem pathConstant_evalZero (B : CGWH.{u, v}) :
    pathConstant.{u, v}.app B ≫ pathEvalZero.{u, v}.app B =
      𝟙 B := by
  unfold pathConstant pathEvalZero
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
    MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
  change (λ_ B).inv ≫
      ((CGWH.point_isTerminal.from (𝟙_ CGWH.{u, v}) ≫ intervalZero) ▷ B) ≫
        CartesianMonoidalCategory.snd interval B = 𝟙 B
  rw [CartesianMonoidalCategory.whiskerRight_snd]
  exact CartesianMonoidalCategory.leftUnitor_inv_snd B

/-- A constant path evaluates to its point at time one. -/
theorem pathConstant_evalOne (B : CGWH.{u, v}) :
    pathConstant.{u, v}.app B ≫ pathEvalOne.{u, v}.app B =
      𝟙 B := by
  unfold pathConstant pathEvalOne
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
    MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
  change (λ_ B).inv ≫
      ((CGWH.point_isTerminal.from (𝟙_ CGWH.{u, v}) ≫ intervalOne) ▷ B) ≫
        CartesianMonoidalCategory.snd interval B = 𝟙 B
  rw [CartesianMonoidalCategory.whiskerRight_snd]
  exact CartesianMonoidalCategory.leftUnitor_inv_snd B

end CGWH
