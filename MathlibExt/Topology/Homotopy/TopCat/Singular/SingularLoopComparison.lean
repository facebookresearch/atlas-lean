/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.LoopSpaceWeakEquivalence
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.PathSpace
public import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularPathComparisonMonoidal
public import MathlibExt.Topology.Homotopy.StrictLoopMap
public import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy

/-!
# Singular comparisons for based paths and loops

The monoidal characteristic of the singular/free-path comparison identifies
its two simplicial endpoints with compact-open evaluation at `0` and `1`.
These equations restrict the comparison first to paths starting at a chosen
point and then to loops ending at that point.

For an arbitrary continuous map, the resulting loop comparison commutes
strictly with literal topological postcomposition and the frozen simplicial
`SSet.loopSpaceMap`.  The comparison also sends the reflexive topological
loop to the distinguished constant simplicial loop.

Only forward comparison maps and strict naturality are asserted.  This file
defines no inverse fiber map, comparison isomorphism, weak-equivalence
theorem, weakly-pointed preservation result, or Q/S specialization.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory MonoidalClosed Simplicial Opposite
open Functor.LaxMonoidal
open scoped Simplicial Topology

noncomputable section

set_option autoImplicit false

universe u

namespace TopCat

noncomputable def intervalContinuousMapEvalAt
    (X : Type u) [TopologicalSpace X] (t : unitInterval) :
    TopCat.of C(unitInterval, X) ⟶ TopCat.of X :=
  TopCat.ofHom
    { toFun := fun gamma => gamma t
      continuous_toFun := continuous_eval_const t }

@[simp]
theorem intervalContinuousMapEvalAt_apply
    (X : Type u) [TopologicalSpace X] (t : unitInterval)
    (gamma : C(unitInterval, X)) :
    intervalContinuousMapEvalAt X t gamma = gamma t :=
  rfl

end TopCat

namespace SSet

local instance : TopCat.toSSet.{u}.Braided :=
  Functor.Braided.ofChosenFiniteProducts _

private theorem tensorLeftIsoProd_hom_fst_top
    (X Y : TopCat.{u}) :
    (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app Y ≫
        Limits.prod.fst =
      CartesianMonoidalCategory.fst X Y :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y)
    (limit.isLimit _) ⟨WalkingPair.left⟩

private theorem tensorLeftIsoProd_hom_snd_top
    (X Y : TopCat.{u}) :
    (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app Y ≫
        Limits.prod.snd =
      CartesianMonoidalCategory.snd X Y :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y)
    (limit.isLimit _) ⟨WalkingPair.right⟩

private noncomputable def intervalConstPathTop
    (X : Type u) [TopologicalSpace X] :
    TopCat.of X ⟶ TopCat.of C(unitInterval, X) :=
  TopCat.ofHom (ContinuousMap.curry
    { toFun := fun p : X × unitInterval => p.1
      continuous_toFun := continuous_fst })

private theorem intervalConstPathTop_apply
    (X : Type u) [TopologicalSpace X] (x : X) (t : unitInterval) :
    intervalConstPathTop X x t = x :=
  rfl

private theorem intervalConstPath_evaluation
    (X : Type u) [TopologicalSpace X] :
    TopCat.I.{u} ◁ intervalConstPathTop X ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd
          TopCat.I.{u}).hom.app (TopCat.of C(unitInterval, X)) ≫
        TopCat.intervalContinuousMapEvaluation X =
      CartesianMonoidalCategory.snd TopCat.I.{u} (TopCat.of X) := by
  apply TopCat.hom_ext
  ext p
  let q : TopCat.I.{u} ⊗ TopCat.of C(unitInterval, X) :=
    (TopCat.I.{u} ◁ intervalConstPathTop X) p
  have hfst := ConcreteCategory.congr_hom
    (tensorLeftIsoProd_hom_fst_top TopCat.I.{u}
      (TopCat.of C(unitInterval, X))) q
  have hsnd := ConcreteCategory.congr_hom
    (tensorLeftIsoProd_hom_snd_top TopCat.I.{u}
      (TopCat.of C(unitInterval, X))) q
  with_unfolding_all
    change
      (Limits.prod.fst : TopCat.I.{u} ⨯
          TopCat.of C(unitInterval, X) ⟶ TopCat.I.{u})
          ((CartesianMonoidalCategory.tensorLeftIsoProd
            TopCat.I.{u}).hom.app
              (TopCat.of C(unitInterval, X)) q) =
        (CartesianMonoidalCategory.fst TopCat.I.{u}
          (TopCat.of C(unitInterval, X))) q at hfst
  with_unfolding_all
    change
      (Limits.prod.snd : TopCat.I.{u} ⨯
          TopCat.of C(unitInterval, X) ⟶
            TopCat.of C(unitInterval, X))
          ((CartesianMonoidalCategory.tensorLeftIsoProd
            TopCat.I.{u}).hom.app
              (TopCat.of C(unitInterval, X)) q) =
        (CartesianMonoidalCategory.snd TopCat.I.{u}
          (TopCat.of C(unitInterval, X))) q at hsnd
  change
    ((Limits.prod.snd : TopCat.I.{u} ⨯
        TopCat.of C(unitInterval, X) ⟶
          TopCat.of C(unitInterval, X))
      ((CartesianMonoidalCategory.tensorLeftIsoProd
        TopCat.I.{u}).hom.app
          (TopCat.of C(unitInterval, X)) q))
      (TopCat.I.homeomorph
        ((Limits.prod.fst : TopCat.I.{u} ⨯
          TopCat.of C(unitInterval, X) ⟶ TopCat.I.{u})
          ((CartesianMonoidalCategory.tensorLeftIsoProd
            TopCat.I.{u}).hom.app
              (TopCat.of C(unitInterval, X)) q))) =
      (CartesianMonoidalCategory.snd TopCat.I.{u} (TopCat.of X)) p
  rw [hfst, hsnd]
  rfl

theorem singularPathComparison_eval₀
    (X : Type u) [TopologicalSpace X] :
    singularPathComparison X ≫ (eval₀ :
        pathSpace (TopCat.toSSet.obj (TopCat.of X)) ⟶
          TopCat.toSSet.obj (TopCat.of X)) =
      TopCat.toSSet.map (TopCat.intervalContinuousMapEvalAt X 0) := by
  rw [SSet.comp_eval₀_eq_ι₀_braiding_uncurry]
  rw [singularPathComparison_uncurry_lax]
  let P := TopCat.of C(unitInterval, X)
  let A := TopCat.toSSet.obj P
  let ev : (Limits.prod.functor.obj TopCat.I.{u}).obj P ⟶
      TopCat.of X := TopCat.intervalContinuousMapEvaluation X
  change SSet.ι₀ ≫ (β_ A (Δ[1] : SSet.{u})).hom ≫
      SSet.stdSimplex.toSSetObjI.{u} ▷ A ≫
      μ TopCat.toSSet TopCat.I.{u} P ≫
      TopCat.toSSet.map
        ((CartesianMonoidalCategory.tensorLeftIsoProd
          TopCat.I.{u}).hom.app P) ≫
      TopCat.toSSet.map ev = _
  slice_lhs 2 3 =>
    change (β_ _ _).hom ≫
      (SSet.stdSimplex.toSSetObjI.{u} ⊗ₘ 𝟙 _)
    rw [← BraidedCategory.braiding_naturality]
    simp only [id_tensorHom]
  slice_lhs 3 4 =>
    rw [← Functor.LaxBraided.braided]
  slice_lhs 1 3 =>
    rw [SSet.stdSimplex.ι₀_whiskerLeft_toSSetObjI_μ]
  simp only [← TopCat.toSSet.map_comp]
  congr 1
  apply TopCat.hom_ext
  ext gamma
  let p : TopCat.I.{u} ⊗ P :=
    (TopCat.ι₀ ≫ (β_ P TopCat.I.{u}).hom) gamma
  have hfst := ConcreteCategory.congr_hom
    (tensorLeftIsoProd_hom_fst_top TopCat.I.{u} P) p
  have hsnd := ConcreteCategory.congr_hom
    (tensorLeftIsoProd_hom_snd_top TopCat.I.{u} P) p
  with_unfolding_all
    change
      (Limits.prod.fst : TopCat.I.{u} ⨯ P ⟶ TopCat.I.{u})
          ((CartesianMonoidalCategory.tensorLeftIsoProd
            TopCat.I.{u}).hom.app P p) =
        (CartesianMonoidalCategory.fst TopCat.I.{u} P) p at hfst
  with_unfolding_all
    change
      (Limits.prod.snd : TopCat.I.{u} ⨯ P ⟶ P)
          ((CartesianMonoidalCategory.tensorLeftIsoProd
            TopCat.I.{u}).hom.app P p) =
        (CartesianMonoidalCategory.snd TopCat.I.{u} P) p at hsnd
  change
    ((Limits.prod.snd : TopCat.I.{u} ⨯ P ⟶ P)
      ((CartesianMonoidalCategory.tensorLeftIsoProd
        TopCat.I.{u}).hom.app P p))
      (TopCat.I.homeomorph
        ((Limits.prod.fst : TopCat.I.{u} ⨯ P ⟶ TopCat.I.{u})
          ((CartesianMonoidalCategory.tensorLeftIsoProd
            TopCat.I.{u}).hom.app P p))) = gamma 0
  rw [hfst, hsnd]
  rfl

theorem singularPathComparison_eval₁
    (X : Type u) [TopologicalSpace X] :
    singularPathComparison X ≫ (eval₁ :
        pathSpace (TopCat.toSSet.obj (TopCat.of X)) ⟶
          TopCat.toSSet.obj (TopCat.of X)) =
      TopCat.toSSet.map (TopCat.intervalContinuousMapEvalAt X 1) := by
  rw [SSet.comp_eval₁_eq_ι₁_braiding_uncurry]
  rw [singularPathComparison_uncurry_lax]
  let P := TopCat.of C(unitInterval, X)
  let A := TopCat.toSSet.obj P
  let ev : (Limits.prod.functor.obj TopCat.I.{u}).obj P ⟶
      TopCat.of X := TopCat.intervalContinuousMapEvaluation X
  change SSet.ι₁ ≫ (β_ A (Δ[1] : SSet.{u})).hom ≫
      SSet.stdSimplex.toSSetObjI.{u} ▷ A ≫
      μ TopCat.toSSet TopCat.I.{u} P ≫
      TopCat.toSSet.map
        ((CartesianMonoidalCategory.tensorLeftIsoProd
          TopCat.I.{u}).hom.app P) ≫
      TopCat.toSSet.map ev = _
  slice_lhs 2 3 =>
    change (β_ _ _).hom ≫
      (SSet.stdSimplex.toSSetObjI.{u} ⊗ₘ 𝟙 _)
    rw [← BraidedCategory.braiding_naturality]
    simp only [id_tensorHom]
  slice_lhs 3 4 =>
    rw [← Functor.LaxBraided.braided]
  slice_lhs 1 3 =>
    rw [SSet.stdSimplex.ι₁_whiskerLeft_toSSetObjI_μ]
  simp only [← TopCat.toSSet.map_comp]
  congr 1
  apply TopCat.hom_ext
  ext gamma
  let p : TopCat.I.{u} ⊗ P :=
    (TopCat.ι₁ ≫ (β_ P TopCat.I.{u}).hom) gamma
  have hfst := ConcreteCategory.congr_hom
    (tensorLeftIsoProd_hom_fst_top TopCat.I.{u} P) p
  have hsnd := ConcreteCategory.congr_hom
    (tensorLeftIsoProd_hom_snd_top TopCat.I.{u} P) p
  with_unfolding_all
    change
      (Limits.prod.fst : TopCat.I.{u} ⨯ P ⟶ TopCat.I.{u})
          ((CartesianMonoidalCategory.tensorLeftIsoProd
            TopCat.I.{u}).hom.app P p) =
        (CartesianMonoidalCategory.fst TopCat.I.{u} P) p at hfst
  with_unfolding_all
    change
      (Limits.prod.snd : TopCat.I.{u} ⨯ P ⟶ P)
          ((CartesianMonoidalCategory.tensorLeftIsoProd
            TopCat.I.{u}).hom.app P p) =
        (CartesianMonoidalCategory.snd TopCat.I.{u} P) p at hsnd
  change
    ((Limits.prod.snd : TopCat.I.{u} ⨯ P ⟶ P)
      ((CartesianMonoidalCategory.tensorLeftIsoProd
        TopCat.I.{u}).hom.app P p))
      (TopCat.I.homeomorph
        ((Limits.prod.fst : TopCat.I.{u} ⨯ P ⟶ TopCat.I.{u})
          ((CartesianMonoidalCategory.tensorLeftIsoProd
            TopCat.I.{u}).hom.app P p))) = gamma 1
  rw [hfst, hsnd]
  rfl

private theorem singularPathComparison_const
    (X : Type u) [TopologicalSpace X] :
    TopCat.toSSet.map (intervalConstPathTop X) ≫
        singularPathComparison X =
      constPath (TopCat.toSSet.obj (TopCat.of X)) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left]
  rw [singularPathComparison_uncurry_lax]
  rw [SSet.uncurry_constPath]
  let P := TopCat.of C(unitInterval, X)
  let A := TopCat.toSSet.obj (TopCat.of X)
  let ev : (Limits.prod.functor.obj TopCat.I.{u}).obj P ⟶
      TopCat.of X := TopCat.intervalContinuousMapEvaluation X
  change (Δ[1] : SSet.{u}) ◁ TopCat.toSSet.map (intervalConstPathTop X) ≫
      SSet.stdSimplex.toSSetObjI.{u} ▷ TopCat.toSSet.obj P ≫
      μ TopCat.toSSet TopCat.I.{u} P ≫
      TopCat.toSSet.map
        ((CartesianMonoidalCategory.tensorLeftIsoProd
          TopCat.I.{u}).hom.app P) ≫
      TopCat.toSSet.map ev =
    CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) A
  slice_lhs 1 2 =>
    rw [MonoidalCategory.whisker_exchange]
  slice_lhs 2 3 =>
    rw [Functor.LaxMonoidal.μ_natural_right]
  slice_lhs 3 5 =>
    rw [← TopCat.toSSet.map_comp,
      ← TopCat.toSSet.map_comp,
      intervalConstPath_evaluation]
  slice_lhs 2 3 =>
    rw [Functor.Monoidal.μ_snd]
  rw [CartesianMonoidalCategory.whiskerRight_snd]

private def intervalBasedPathIncl
    (X : Type u) [TopologicalSpace X] (x : X) :
    C({ gamma : C(unitInterval, X) // gamma 0 = x },
      C(unitInterval, X)) where
  toFun gamma := gamma.1
  continuous_toFun := continuous_subtype_val

private def loopToIntervalBasedPath
    (X : Type u) [TopologicalSpace X] (x : X) :
    C(LoopSpace X x,
      { gamma : C(unitInterval, X) // gamma 0 = x }) where
  toFun gamma := ⟨gamma.toContinuousMap, gamma.source⟩
  continuous_toFun := Continuous.subtype_mk continuous_induced_dom _

private def loopToContinuousMap
    (X : Type u) [TopologicalSpace X] (x : X) :
    C(LoopSpace X x, C(unitInterval, X)) where
  toFun gamma := gamma.toContinuousMap
  continuous_toFun := continuous_induced_dom

private theorem loopToIntervalBasedPath_comp_incl
    (X : Type u) [TopologicalSpace X] (x : X) :
    (intervalBasedPathIncl X x).comp
        (loopToIntervalBasedPath X x) =
      loopToContinuousMap X x :=
  rfl

private theorem loopToIntervalBasedPath_comp_incl_top
    (X : Type u) [TopologicalSpace X] (x : X) :
    TopCat.ofHom (loopToIntervalBasedPath X x) ≫
        TopCat.ofHom (intervalBasedPathIncl X x) =
      TopCat.ofHom (loopToContinuousMap X x) := by
  rw [← TopCat.ofHom_comp,
    loopToIntervalBasedPath_comp_incl]

private theorem strictLoopMap_comp_loopToContinuousMap
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    TopCat.ofHom (ContinuousMap.strictLoopMap f x) ≫
        TopCat.ofHom (loopToContinuousMap Y (f x)) =
      TopCat.ofHom (loopToContinuousMap X x) ≫
        TopCat.intervalContinuousMapPostcomp f := by
  apply TopCat.hom_ext
  ext gamma t
  rfl

private theorem loopToContinuousMap_eval_one
    (X : Type u) [TopologicalSpace X] (x : X) :
    TopCat.ofHom (loopToContinuousMap X x) ≫
        TopCat.intervalContinuousMapEvalAt X 1 =
      TopCat.const x := by
  apply TopCat.hom_ext
  ext gamma
  exact gamma.target

@[no_expose]
noncomputable def singularBasedPathComparison
    (X : Type u) [TopologicalSpace X] (x : X) :
    TopCat.toSSet.obj
        (TopCat.of { gamma : C(unitInterval, X) // gamma 0 = x }) ⟶
      SSet.basedPath (TopCat.toSSet.obj (TopCat.of X))
        (TopCat.toSSetObj₀Equiv.symm x) :=
  Subcomplex.lift
    (TopCat.toSSet.map
        (TopCat.ofHom (intervalBasedPathIncl X x)) ≫
      singularPathComparison X)
    (by
      rw [Subcomplex.range_le_fiber_iff]
      calc
        (TopCat.toSSet.map
              (TopCat.ofHom (intervalBasedPathIncl X x)) ≫
            singularPathComparison X) ≫ eval₀ =
          TopCat.toSSet.map
              (TopCat.ofHom (intervalBasedPathIncl X x)) ≫
            (singularPathComparison X ≫ eval₀) := by
              rw [Category.assoc]
        _ = TopCat.toSSet.map
              (TopCat.ofHom (intervalBasedPathIncl X x)) ≫
            TopCat.toSSet.map
              (TopCat.intervalContinuousMapEvalAt X 0) := by
              rw [singularPathComparison_eval₀]
        _ = TopCat.toSSet.map
              (TopCat.const
                (X := TopCat.of
                  { gamma : C(unitInterval, X) // gamma 0 = x }) x) := by
              rw [← TopCat.toSSet.map_comp]
              congr 1
              apply TopCat.hom_ext
              ext gamma
              exact gamma.property
        _ = SSet.const (TopCat.toSSetObj₀Equiv.symm x) := by
              rw [TopCat.toSSet_map_const])

@[reassoc]
private theorem singularBasedPathComparison_ι_private
    (X : Type u) [TopologicalSpace X] (x : X) :
    singularBasedPathComparison X x ≫
        basedPathIncl (TopCat.toSSet.obj (TopCat.of X))
          (TopCat.toSSetObj₀Equiv.symm x) =
      TopCat.toSSet.map
          (TopCat.ofHom (intervalBasedPathIncl X x)) ≫
        singularPathComparison X :=
  Subcomplex.lift_ι _ _

@[simp, reassoc]
theorem singularBasedPathComparison_ι
    (X : Type u) [TopologicalSpace X] (x : X) :
    singularBasedPathComparison X x ≫
        basedPathIncl (TopCat.toSSet.obj (TopCat.of X))
          (TopCat.toSSetObj₀Equiv.symm x) =
      TopCat.toSSet.map
          (TopCat.ofHom
            { toFun := fun gamma :
                  { gamma : C(unitInterval, X) // gamma 0 = x } => gamma.1
              continuous_toFun := continuous_subtype_val }) ≫
        singularPathComparison X := by
  change singularBasedPathComparison X x ≫
      basedPathIncl (TopCat.toSSet.obj (TopCat.of X))
        (TopCat.toSSetObj₀Equiv.symm x) =
    TopCat.toSSet.map (TopCat.ofHom (intervalBasedPathIncl X x)) ≫
      singularPathComparison X
  exact singularBasedPathComparison_ι_private X x

@[no_expose]
noncomputable def singularLoopComparison
    (X : Type u) [TopologicalSpace X] (x : X) :
    TopCat.toSSet.obj (TopCat.of (LoopSpace X x)) ⟶
      SSet.loopSpace (TopCat.toSSet.obj (TopCat.of X))
        (TopCat.toSSetObj₀Equiv.symm x) :=
  Subcomplex.lift
    (TopCat.toSSet.map
        (TopCat.ofHom (loopToIntervalBasedPath X x)) ≫
      singularBasedPathComparison X x)
    (by
      rw [Subcomplex.range_le_fiber_iff]
      change
        (TopCat.toSSet.map
              (TopCat.ofHom (loopToIntervalBasedPath X x)) ≫
            singularBasedPathComparison X x) ≫
            (basedPathIncl (TopCat.toSSet.obj (TopCat.of X))
                (TopCat.toSSetObj₀Equiv.symm x) ≫ eval₁) =
          SSet.const (TopCat.toSSetObj₀Equiv.symm x)
      simp only [Category.assoc]
      rw [singularBasedPathComparison_ι_private_assoc,
        singularPathComparison_eval₁]
      rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp]
      rw [show
        TopCat.ofHom (loopToIntervalBasedPath X x) ≫
              TopCat.ofHom (intervalBasedPathIncl X x) ≫
              TopCat.intervalContinuousMapEvalAt X 1 =
            TopCat.const x by
          rw [← Category.assoc, ← TopCat.ofHom_comp,
            loopToIntervalBasedPath_comp_incl]
          exact loopToContinuousMap_eval_one X x]
      exact TopCat.toSSet_map_const
        (TopCat.of (LoopSpace X x)) (Y := TopCat.of X) x)

@[reassoc]
private theorem singularLoopComparison_ι_private
    (X : Type u) [TopologicalSpace X] (x : X) :
    singularLoopComparison X x ≫
        loopSpaceIncl (TopCat.toSSet.obj (TopCat.of X))
          (TopCat.toSSetObj₀Equiv.symm x) =
      TopCat.toSSet.map
          (TopCat.ofHom (loopToIntervalBasedPath X x)) ≫
        singularBasedPathComparison X x :=
  Subcomplex.lift_ι _ _

@[simp, reassoc]
theorem singularLoopComparison_ι
    (X : Type u) [TopologicalSpace X] (x : X) :
    singularLoopComparison X x ≫
        loopSpaceIncl (TopCat.toSSet.obj (TopCat.of X))
          (TopCat.toSSetObj₀Equiv.symm x) =
      TopCat.toSSet.map
          (TopCat.ofHom
            { toFun := fun gamma : LoopSpace X x =>
                ⟨gamma.toContinuousMap, gamma.source⟩
              continuous_toFun :=
                Continuous.subtype_mk continuous_induced_dom _ }) ≫
        singularBasedPathComparison X x := by
  change singularLoopComparison X x ≫
      loopSpaceIncl (TopCat.toSSet.obj (TopCat.of X))
        (TopCat.toSSetObj₀Equiv.symm x) =
    TopCat.toSSet.map
        (TopCat.ofHom (loopToIntervalBasedPath X x)) ≫
      singularBasedPathComparison X x
  exact singularLoopComparison_ι_private X x

@[simp]
theorem singularLoopComparison_refl
    (X : Type u) [TopologicalSpace X] (x : X) :
    (singularLoopComparison X x).app (op (SimplexCategory.mk 0))
        (TopCat.toSSetObj₀Equiv.symm (Path.refl x)) =
      Subcomplex.fiber.basePoint
        (basedPathPoint (TopCat.toSSet.obj (TopCat.of X))
          (TopCat.toSSetObj₀Equiv.symm x))
        (basedPathProj_basedPathPoint
          (TopCat.toSSet.obj (TopCat.of X))
          (TopCat.toSSetObj₀Equiv.symm x)) := by
  apply Subtype.ext
  apply Subtype.ext
  let l : (TopCat.toSSet.obj (TopCat.of (LoopSpace X x))).obj
      (op (SimplexCategory.mk 0)) :=
    TopCat.toSSetObj₀Equiv.symm (Path.refl x)
  let sx : (TopCat.toSSet.obj (TopCat.of X)).obj
      (op (SimplexCategory.mk 0)) :=
    TopCat.toSSetObj₀Equiv.symm x
  have hComp :
      singularLoopComparison X x ≫
          loopSpaceIncl (TopCat.toSSet.obj (TopCat.of X)) sx ≫
          basedPathIncl (TopCat.toSSet.obj (TopCat.of X)) sx =
        TopCat.toSSet.map
              (TopCat.ofHom (loopToContinuousMap X x)) ≫
            singularPathComparison X := by
    calc
      singularLoopComparison X x ≫
          loopSpaceIncl (TopCat.toSSet.obj (TopCat.of X)) sx ≫
          basedPathIncl (TopCat.toSSet.obj (TopCat.of X)) sx =
        TopCat.toSSet.map
              (TopCat.ofHom (loopToIntervalBasedPath X x)) ≫
            singularBasedPathComparison X x ≫
              basedPathIncl (TopCat.toSSet.obj (TopCat.of X)) sx := by
                rw [singularLoopComparison_ι_private_assoc]
      _ = TopCat.toSSet.map
              (TopCat.ofHom (loopToIntervalBasedPath X x)) ≫
            TopCat.toSSet.map
                (TopCat.ofHom (intervalBasedPathIncl X x)) ≫
              singularPathComparison X := by
                slice_lhs 2 3 =>
                  rw [singularBasedPathComparison_ι_private]
      _ = TopCat.toSSet.map
              (TopCat.ofHom (loopToContinuousMap X x)) ≫
              singularPathComparison X := by
                slice_lhs 1 2 =>
                  rw [← TopCat.toSSet.map_comp,
                    loopToIntervalBasedPath_comp_incl_top]
  have hCarrier := congrArg
    (fun q : TopCat.toSSet.obj (TopCat.of (LoopSpace X x)) ⟶
        pathSpace (TopCat.toSSet.obj (TopCat.of X)) =>
      q.app (op (SimplexCategory.mk 0)) l) hComp
  have hInput :
      (TopCat.toSSet.map
          (TopCat.ofHom (loopToContinuousMap X x))).app _ l =
        (TopCat.toSSet.map (intervalConstPathTop X)).app _ sx := by
    apply TopCat.toSSetObj₀Equiv.injective
    change (loopToContinuousMap X x) (Path.refl x) =
      intervalConstPathTop X x
    apply ContinuousMap.ext
    intro t
    rfl
  have hConst := congrArg
    (fun q : TopCat.toSSet.obj (TopCat.of X) ⟶
        pathSpace (TopCat.toSSet.obj (TopCat.of X)) =>
      q.app (op (SimplexCategory.mk 0)) sx)
    (singularPathComparison_const X)
  change
    ((singularLoopComparison X x).app _ l).val.val =
      (basedPathPoint (TopCat.toSSet.obj (TopCat.of X)) sx).val
  calc
    ((singularLoopComparison X x).app _ l).val.val =
        (singularPathComparison X).app _
          ((TopCat.toSSet.map
            (TopCat.ofHom (loopToContinuousMap X x))).app _ l) := by
          exact hCarrier
    _ = (singularPathComparison X).app _
          ((TopCat.toSSet.map (intervalConstPathTop X)).app _ sx) := by
            rw [hInput]
    _ = (constPath (TopCat.toSSet.obj (TopCat.of X))).app _ sx := by
          exact hConst
    _ = (basedPathPoint (TopCat.toSSet.obj (TopCat.of X)) sx).val := rfl

theorem singularLoopComparison_naturality
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    TopCat.toSSet.map
          (TopCat.ofHom (ContinuousMap.strictLoopMap f x)) ≫
        singularLoopComparison Y (f x) =
      singularLoopComparison X x ≫
        SSet.loopSpaceMap
          (x := TopCat.toSSetObj₀Equiv.symm x)
          (y := TopCat.toSSetObj₀Equiv.symm (f x))
          (TopCat.toSSet.map (TopCat.ofHom f))
          (by rfl) := by
  let _ : Mono (loopSpaceIncl
      (TopCat.toSSet.obj (TopCat.of Y))
      (TopCat.toSSetObj₀Equiv.symm (f x))) :=
    inferInstanceAs
      (Mono ((Subcomplex.fiber
        (basedPathProj (TopCat.toSSet.obj (TopCat.of Y))
          (TopCat.toSSetObj₀Equiv.symm (f x)))
        (TopCat.toSSetObj₀Equiv.symm (f x))).ι))
  apply (cancel_mono (loopSpaceIncl
    (TopCat.toSSet.obj (TopCat.of Y))
    (TopCat.toSSetObj₀Equiv.symm (f x)))).mp
  slice_lhs 2 3 =>
    rw [singularLoopComparison_ι_private Y (f x)]
  slice_rhs 2 3 =>
    rw [loopSpaceMap_ι
      (x := TopCat.toSSetObj₀Equiv.symm x)
      (y := TopCat.toSSetObj₀Equiv.symm (f x))
      (TopCat.toSSet.map (TopCat.ofHom f)) (by rfl)]
  slice_rhs 1 2 =>
    rw [singularLoopComparison_ι_private X x]
  let _ : Mono (basedPathIncl
      (TopCat.toSSet.obj (TopCat.of Y))
      (TopCat.toSSetObj₀Equiv.symm (f x))) :=
    inferInstanceAs
      (Mono ((Subcomplex.fiber
        (eval₀ : pathSpace (TopCat.toSSet.obj (TopCat.of Y)) ⟶
          TopCat.toSSet.obj (TopCat.of Y))
        (TopCat.toSSetObj₀Equiv.symm (f x))).ι))
  apply (cancel_mono (basedPathIncl
    (TopCat.toSSet.obj (TopCat.of Y))
    (TopCat.toSSetObj₀Equiv.symm (f x)))).mp
  slice_lhs 3 4 =>
    rw [singularBasedPathComparison_ι_private Y (f x)]
  slice_rhs 3 4 =>
    rw [basedPathMap_ι
      (x := TopCat.toSSetObj₀Equiv.symm x)
      (y := TopCat.toSSetObj₀Equiv.symm (f x))
      (TopCat.toSSet.map (TopCat.ofHom f)) (by rfl)]
  slice_rhs 2 3 =>
    rw [singularBasedPathComparison_ι_private X x]
  slice_lhs 2 3 =>
    rw [← TopCat.toSSet.map_comp,
      loopToIntervalBasedPath_comp_incl_top]
  slice_lhs 1 2 =>
    rw [← TopCat.toSSet.map_comp,
      strictLoopMap_comp_loopToContinuousMap,
      TopCat.toSSet.map_comp]
  slice_rhs 1 2 =>
    rw [← TopCat.toSSet.map_comp,
      loopToIntervalBasedPath_comp_incl_top]
  slice_lhs 2 3 =>
    rw [singularPathComparison_naturality]
  rw [Category.assoc]

end SSet
