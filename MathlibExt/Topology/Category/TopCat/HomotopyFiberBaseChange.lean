/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyFiberHomotopySquare
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy

import MathlibExt.AlgebraicTopology.ModelCategory.ProperSpanGluing
import MathlibExt.CategoryTheory.MorphismProperty.Limits
import Mathlib.AlgebraicTopology.ModelCategory.Opposite

/-!
# Canonical homotopy-fiber maps under a changing-base square

A strict square induces maps of strict fibers and compact-open homotopy fibers
over a point and its image. The homotopy-fiber map is the existing
`homotopyPullbackMap`: its path is postcomposed with the base map.

Weak equivalences of the total and base spaces make this actual map a weak
equivalence. Naturality of the constant-path comparison then gives a descent
criterion whose hypotheses concern the target comparison and the strict-fiber
map. The source comparison is the conclusion.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Topology HomotopicalAlgebra

universe u

namespace TopCat

private def scalePathParameter (t : unitInterval) (s : TopCat.I.{u}) : TopCat.I.{u} :=
  TopCat.I.homeomorph.symm
    ⟨(t : ℝ) * (TopCat.I.homeomorph s : ℝ),
      unitInterval.mul_mem t.property (TopCat.I.homeomorph s).property⟩

private theorem continuous_scalePathParameter :
    Continuous (fun z : unitInterval × TopCat.I.{u} => scalePathParameter z.1 z.2) := by
  apply TopCat.I.homeomorph.symm.continuous.comp
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp
      (TopCat.I.homeomorph.continuous.comp continuous_snd))

private theorem scalePathParameter_zero (s : TopCat.I.{u}) :
    scalePathParameter 0 s = 0 := by
  apply TopCat.I.homeomorph.injective
  simp [scalePathParameter]

private theorem scalePathParameter_one (s : TopCat.I.{u}) :
    scalePathParameter 1 s = s := by
  apply TopCat.I.homeomorph.injective
  simp [scalePathParameter]

private def scalePathFamily (B : TopCat.{u}) :
    C(unitInterval × pathObject B, pathObject B) :=
  (show C((unitInterval × pathObject B) × TopCat.I.{u}, B) from
    ⟨fun z => z.1.2 (scalePathParameter z.1.1 z.2), by
      have hpair : Continuous
          (fun z : (unitInterval × pathObject B) × TopCat.I.{u} =>
            (z.1.2, scalePathParameter z.1.1 z.2)) :=
        (continuous_snd.comp continuous_fst).prodMk
          (continuous_scalePathParameter.comp
            ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
      have heval : Continuous
          (fun z : C(TopCat.I.{u}, B) × TopCat.I.{u} => z.1 z.2) := continuous_eval
      exact heval.comp hpair⟩).curry

private def pathEvaluationHomotopy (B : TopCat.{u}) :
    ContinuousMap.Homotopy ((pathConstant B).hom.comp (pathEvalZero B).hom)
      (ContinuousMap.id (pathObject B)) where
  toContinuousMap := scalePathFamily B
  map_zero_left γ := by
    apply ContinuousMap.ext
    intro s
    change γ (scalePathParameter 0 s) = γ 0
    rw [scalePathParameter_zero]
  map_one_left γ := by
    apply ContinuousMap.ext
    intro s
    change γ (scalePathParameter 1 s) = γ s
    rw [scalePathParameter_one]

private def pathEvaluationHomotopyEquiv (B : TopCat.{u}) :
    ContinuousMap.HomotopyEquiv (pathObject B) B where
  toFun := (pathEvalZero B).hom
  invFun := (pathConstant B).hom
  left_inv := ⟨pathEvaluationHomotopy B⟩
  right_inv := ⟨ContinuousMap.Homotopy.refl (ContinuousMap.id B)⟩

/-- Evaluation at the initial endpoint of compact-open paths is a weak homotopy equivalence. -/
theorem pathEvalZero_mem_weakHomotopyEquivalences (B : TopCat.{u}) :
    weakHomotopyEquivalences (pathEvalZero B) :=
  homotopyEquiv_toFun_mem (pathEvaluationHomotopyEquiv B)

private theorem pathObjectMap_mem_weakHomotopyEquivalences
    {B B' : TopCat.{u}} (h : B ⟶ B') (hh : weakHomotopyEquivalences h) :
    weakHomotopyEquivalences (pathObjectMap h) := by
  have hcomp : weakHomotopyEquivalences (pathObjectMap h ≫ pathEvalZero B') := by
    rw [pathObjectMap_evalZero]
    exact weakHomotopyEquivalences.comp_mem _ _
      (pathEvalZero_mem_weakHomotopyEquivalences B) hh
  exact weakHomotopyEquivalences.of_postcomp _ _
    (pathEvalZero_mem_weakHomotopyEquivalences B') hcomp

private theorem oppositeLeftProper :
    let _ : ModelCategory TopCat.{u} := TopCat.modelCategory
    IsLeftProper TopCat.{u}ᵒᵖ := by
  let _ : ModelCategory TopCat.{u} := TopCat.modelCategory
  let _ : IsRightProper TopCat.{u} := TopCat.modelCategory.rightProper
  refine ⟨?_⟩
  constructor
  intro A B i hi
  constructor
  intro X Y j f' f sq hf
  have hiUnop : fibrations TopCat.{u} i.unop := by
    rw [cofibrations_op] at hi
    exact hi
  have hfUnop : weakEquivalences TopCat.{u} f.unop := by
    rw [weakEquivalences_op] at hf
    exact hf
  have hf'Unop : weakEquivalences TopCat.{u} f'.unop :=
    (inferInstance :
        (weakEquivalences TopCat.{u}).IsStableUnderBaseChangeAgainst
          (fibrations TopCat.{u}))
      |>.isStableUnderBaseChangeAlong i.unop hiUnop
      |>.of_isPullback sq.unop hfUnop
  rw [weakEquivalences_op]
  exact hf'Unop

/-- The actual compact-open homotopy-pullback map preserves pointwise weak
equivalences of its three cospan inputs. -/
theorem homotopyPullbackMap_mem_weakHomotopyEquivalences
    {X Y B X' Y' B' : TopCat.{u}}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : X' ⟶ B'} {g' : Y' ⟶ B'}
    (l : X ⟶ X') (r : Y ⟶ Y') (h : B ⟶ B')
    (hf : f ≫ h = l ≫ f') (hg : g ≫ h = r ≫ g')
    (hl : weakHomotopyEquivalences l) (hr : weakHomotopyEquivalences r)
    (hh : weakHomotopyEquivalences h) :
    weakHomotopyEquivalences (homotopyPullbackMap l r h hf hg) := by
  let _ : ModelCategory TopCat.{u} := TopCat.modelCategory
  let _ : IsRightProper TopCat.{u} := TopCat.modelCategory.rightProper
  let _ : IsLeftProper TopCat.{u}ᵒᵖ := oppositeLeftProper
  let _ : Fibration (pathEndpoints B) := TopCat.modelCategory.pathEndpoints_fibration B
  let _ : Fibration (pathEndpoints B') := TopCat.modelCategory.pathEndpoints_fibration B'
  let _ : Cofibration (pathEndpoints B).op := by
    rw [cofibration_op_iff]
    infer_instance
  let _ : Cofibration (pathEndpoints B').op := by
    rw [cofibration_op_iff]
    infer_instance
  let _ : WeakEquivalence (Limits.prod.map h h).op := by
    rw [weakEquivalences_op_iff, weakEquivalence_iff]
    exact weakHomotopyEquivalences.prodMap hh hh
  let _ : WeakEquivalence (pathObjectMap h).op := by
    rw [weakEquivalences_op_iff, weakEquivalence_iff]
    exact pathObjectMap_mem_weakHomotopyEquivalences h hh
  let _ : WeakEquivalence (Limits.prod.map l r).op := by
    rw [weakEquivalences_op_iff, weakEquivalence_iff]
    exact weakHomotopyEquivalences.prodMap hl hr
  have hprod : Limits.prod.map f g ≫ Limits.prod.map h h =
      Limits.prod.map l r ≫ Limits.prod.map f' g' := by
    simp only [Limits.prod.map_map]
    rw [hf, hg]
  have hfst : homotopyPullbackMap l r h hf hg ≫
      pullback.fst (Limits.prod.map f' g') (pathEndpoints B') =
      pullback.fst (Limits.prod.map f g) (pathEndpoints B) ≫ Limits.prod.map l r := by
    rw [homotopyPullbackMap, pullback.lift_fst]
  have hweak : WeakEquivalence (homotopyPullbackMap l r h hf hg).op := by
    exact IsLeftProper.weakEquivalence_map_of_isPushouts_of_fst
      (IsPullback.of_hasPullback (Limits.prod.map f' g') (pathEndpoints B')).op
      (IsPullback.of_hasPullback (Limits.prod.map f g) (pathEndpoints B)).op
      (by simpa only [op_comp] using congrArg Quiver.Hom.op (pathObjectMap_endpoints h))
      (by simpa only [op_comp] using congrArg Quiver.Hom.op hprod.symm)
      (by
        simpa only [op_comp] using
          congrArg Quiver.Hom.op (homotopyPullbackMap_path l r h hf hg))
      (by simpa only [op_comp] using congrArg Quiver.Hom.op hfst)
  have hm : WeakEquivalence (homotopyPullbackMap l r h hf hg) :=
    (weakEquivalences_op_iff _).mp hweak
  exact (weakEquivalence_iff _).mp hm

/-- A strict square gives the canonical map to the homotopy fiber over the
image of the source point. -/
def homotopyFiberMapOfSquare
    {E B E' B' : TopCat.{u}} {p : E ⟶ B} {q : E' ⟶ B'}
    (s : E ⟶ E') (h : B ⟶ B') (comm : p ≫ h = s ≫ q) (b : B) :
    homotopyFiber p b ⟶ homotopyFiber q (h b) :=
  homotopyPullbackMap s (𝟙 (TopCat.of PUnit)) h comm (by ext; rfl)

/-- The homotopy-fiber map retains the specified total-space map. -/
@[reassoc (attr := simp)]
theorem homotopyFiberMapOfSquare_toTotal
    {E B E' B' : TopCat.{u}} {p : E ⟶ B} {q : E' ⟶ B'}
    (s : E ⟶ E') (h : B ⟶ B') (comm : p ≫ h = s ≫ q) (b : B) :
    homotopyFiberMapOfSquare s h comm b ≫ homotopyFiberToTotal q (h b) =
      homotopyFiberToTotal p b ≫ s := by
  exact homotopyPullbackMap_left _ _ _ _ _

/-- The path in the induced homotopy fiber is postcomposed with the base map. -/
@[reassoc (attr := simp)]
theorem homotopyFiberMapOfSquare_path
    {E B E' B' : TopCat.{u}} {p : E ⟶ B} {q : E' ⟶ B'}
    (s : E ⟶ E') (h : B ⟶ B') (comm : p ≫ h = s ≫ q) (b : B) :
    homotopyFiberMapOfSquare s h comm b ≫ homotopyFiberPath q (h b) =
      homotopyFiberPath p b ≫ pathObjectMap h := by
  exact homotopyPullbackMap_path _ _ _ _ _

/-- Weak equivalences of both maps in a strict square induce a weak
equivalence of the actual compact-open homotopy fibers. -/
theorem homotopyFiberMapOfSquare_mem_weakHomotopyEquivalences
    {E B E' B' : TopCat.{u}} {p : E ⟶ B} {q : E' ⟶ B'}
    (s : E ⟶ E') (h : B ⟶ B') (comm : p ≫ h = s ≫ q) (b : B)
    (hs : weakHomotopyEquivalences s) (hh : weakHomotopyEquivalences h) :
    weakHomotopyEquivalences (homotopyFiberMapOfSquare s h comm b) :=
  homotopyPullbackMap_mem_weakHomotopyEquivalences s (𝟙 _) h comm
    (by ext; rfl) hs (weakHomotopyEquivalences.id_mem _) hh

/-- Repointing a weak-equivalence fiber map along a basepoint equation
preserves weakness. -/
theorem homotopyFiberMapOfSquare_mem_weakHomotopyEquivalences_of_basepoint_eq
    {E B E' B' : TopCat.{u}} {p : E ⟶ B} {q : E' ⟶ B'}
    (s : E ⟶ E') (h : B ⟶ B') (comm : p ≫ h = s ≫ q) (b : B) {b' : B'}
    (e : h b = b') (hs : weakHomotopyEquivalences s)
    (hh : weakHomotopyEquivalences h) :
    weakHomotopyEquivalences
      (e ▸ homotopyFiberMapOfSquare s h comm b) := by
  cases e
  exact homotopyFiberMapOfSquare_mem_weakHomotopyEquivalences s h comm b hs hh

/-- The same strict square induces a map of the actual strict point fibers. -/
def strictFiberMapOfSquare
    {E B E' B' : TopCat.{u}} {p : E ⟶ B} {q : E' ⟶ B'}
    (s : E ⟶ E') (h : B ⟶ B') (comm : p ≫ h = s ≫ q) (b : B) :
    pullback p (TopCat.const (X := TopCat.of PUnit) b) ⟶
      pullback q (TopCat.const (X := TopCat.of PUnit) (h b)) :=
  pullback.map p (TopCat.const (X := TopCat.of PUnit) b) q
    (TopCat.const (X := TopCat.of PUnit) (h b)) s (𝟙 _) h
    comm (by ext; rfl)

/-- The strict-fiber map retains its actual total-space map. -/
@[reassoc (attr := simp)]
theorem strictFiberMapOfSquare_fst
    {E B E' B' : TopCat.{u}} {p : E ⟶ B} {q : E' ⟶ B'}
    (s : E ⟶ E') (h : B ⟶ B') (comm : p ≫ h = s ≫ q) (b : B) :
    strictFiberMapOfSquare s h comm b ≫
      pullback.fst q (TopCat.const (X := TopCat.of PUnit) (h b)) =
      pullback.fst p (TopCat.const (X := TopCat.of PUnit) b) ≫ s := by
  dsimp only [strictFiberMapOfSquare, pullback.map]
  rw [pullback.lift_fst]

/-- The constant-path comparison is natural for the actual strict and
homotopy fiber maps of a square. -/
theorem strictFiberToHomotopyFiber_naturality
    {E B E' B' : TopCat.{u}} {p : E ⟶ B} {q : E' ⟶ B'}
    (s : E ⟶ E') (h : B ⟶ B') (comm : p ≫ h = s ≫ q) (b : B) :
    strictFiberMapOfSquare s h comm b ≫ strictFiberToHomotopyFiber q (h b) =
      strictFiberToHomotopyFiber p b ≫ homotopyFiberMapOfSquare s h comm b := by
  apply homotopyPullback_hom_ext
  · change (strictFiberMapOfSquare s h comm b ≫
        strictFiberToHomotopyFiber q (h b)) ≫ homotopyFiberToTotal q (h b) =
      (strictFiberToHomotopyFiber p b ≫ homotopyFiberMapOfSquare s h comm b) ≫
        homotopyFiberToTotal q (h b)
    rw [Category.assoc, strictFiberToHomotopyFiber_toTotal,
      strictFiberMapOfSquare_fst]
    rw [Category.assoc, homotopyFiberMapOfSquare_toTotal,
      ← Category.assoc, strictFiberToHomotopyFiber_toTotal]
  · apply TopCat.isTerminalPUnit.hom_ext
  · rw [Category.assoc, strictFiberToHomotopyFiber_path,
      Category.assoc, homotopyFiberMapOfSquare_path]
    rw [← Category.assoc (strictFiberToHomotopyFiber p b)
      (homotopyFiberPath p b) (pathObjectMap h), strictFiberToHomotopyFiber_path]
    ext z t
    rfl

/-- A weak strict-fiber map and a weak target comparison descend through
weak total and base maps to prove the source comparison. -/
theorem strictFiberToHomotopyFiber_mem_of_square
    {E B E' B' : TopCat.{u}} {p : E ⟶ B} {q : E' ⟶ B'}
    (s : E ⟶ E') (h : B ⟶ B') (comm : p ≫ h = s ≫ q) (b : B)
    (hs : weakHomotopyEquivalences s) (hh : weakHomotopyEquivalences h)
    (hfiber : weakHomotopyEquivalences (strictFiberMapOfSquare s h comm b))
    (hcomparison : weakHomotopyEquivalences (strictFiberToHomotopyFiber q (h b))) :
    weakHomotopyEquivalences (strictFiberToHomotopyFiber p b) := by
  have hcomp : weakHomotopyEquivalences
      (strictFiberToHomotopyFiber p b ≫ homotopyFiberMapOfSquare s h comm b) := by
    rw [← strictFiberToHomotopyFiber_naturality]
    exact weakHomotopyEquivalences.comp_mem _ _ hfiber hcomparison
  exact weakHomotopyEquivalences.of_postcomp _ _
    (homotopyFiberMapOfSquare_mem_weakHomotopyEquivalences s h comm b hs hh) hcomp

end TopCat
