/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.PathHomotopyFiber
public import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularPathComparisonIso
public import MathlibExt.Topology.Category.TopCat.HomotopyPullback
public import Mathlib.Combinatorics.Quiver.ReflQuiver

import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularFiberIso
import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularLoopComparison
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Singular comparison for compact-open homotopy fibers

The singular simplicial set of the compact-open homotopy fiber is canonically
isomorphic to the explicit simplicial path homotopy fiber.  The full-path law
passes through the canonical homeomorphism from paths on the lifted TopCat
interval to paths on the ordinary unit interval.

This file introduces no model-category instance, weak-equivalence theorem,
fibration or Kan premise, bar or Quillen-B result, quasifibration, principal
bundle, or delooping conclusion.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace SSet

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped Simplicial

universe v

private noncomputable abbrev singularTopEndingPath
    (B : TopCat.{v}) (b : B) : TopCat.{v} :=
  pullback (TopCat.pathEvalOne B)
    (TopCat.const b : TopCat.of PUnit ⟶ B)

private noncomputable abbrev singularTopEndingPathPath
    (B : TopCat.{v}) (b : B) :
    singularTopEndingPath B b ⟶ TopCat.pathObject B :=
  pullback.fst (TopCat.pathEvalOne B) (TopCat.const b)

private noncomputable abbrev singularTopEndingPathUnit
    (B : TopCat.{v}) (b : B) :
    singularTopEndingPath B b ⟶ TopCat.of PUnit :=
  pullback.snd (TopCat.pathEvalOne B) (TopCat.const b)

private noncomputable abbrev singularTopEndingPathEvalZero
    (B : TopCat.{v}) (b : B) : singularTopEndingPath B b ⟶ B :=
  singularTopEndingPathPath B b ≫ TopCat.pathEvalZero B

@[reassoc]
private theorem singularTopEndingPathPath_evalOne
    (B : TopCat.{v}) (b : B) :
    singularTopEndingPathPath B b ≫ TopCat.pathEvalOne B =
      singularTopEndingPathUnit B b ≫ TopCat.const b :=
  pullback.condition

private noncomputable def singularHomotopyFiberToEndingPath
    {E B : TopCat.{v}} (p : E ⟶ B) (b : B) :
    TopCat.homotopyFiber p b ⟶ singularTopEndingPath B b :=
  pullback.lift
    (TopCat.homotopyFiberPath p b)
    (TopCat.homotopyPullbackRight p (TopCat.const b))
    (TopCat.homotopyPullbackPath_evalOne p (TopCat.const b))

@[reassoc (attr := simp)]
private theorem singularHomotopyFiberToEndingPath_path
    {E B : TopCat.{v}} (p : E ⟶ B) (b : B) :
    singularHomotopyFiberToEndingPath p b ≫
        singularTopEndingPathPath B b =
      TopCat.homotopyFiberPath p b := by
  rw [singularHomotopyFiberToEndingPath, pullback.lift_fst]

@[reassoc (attr := simp)]
private theorem singularHomotopyFiberToEndingPath_unit
    {E B : TopCat.{v}} (p : E ⟶ B) (b : B) :
    singularHomotopyFiberToEndingPath p b ≫
        singularTopEndingPathUnit B b =
      TopCat.homotopyPullbackRight p (TopCat.const b) := by
  rw [singularHomotopyFiberToEndingPath, pullback.lift_snd]

@[reassoc (attr := simp)]
private theorem singularHomotopyFiberToEndingPath_evalZero
    {E B : TopCat.{v}} (p : E ⟶ B) (b : B) :
    singularHomotopyFiberToEndingPath p b ≫
        singularTopEndingPathEvalZero B b =
      TopCat.homotopyFiberToTotal p b ≫ p := by
  simp [singularTopEndingPathEvalZero, Category.assoc,
    TopCat.homotopyPullbackPath_evalZero]

private theorem singularHomotopyFiber_isPullback_endingPath
    {E B : TopCat.{v}} (p : E ⟶ B) (b : B) :
    IsPullback (TopCat.homotopyFiberToTotal p b)
      (singularHomotopyFiberToEndingPath p b) p
      (singularTopEndingPathEvalZero B b) := by
  have hw := (singularHomotopyFiberToEndingPath_evalZero p b).symm
  refine { w := hw, isLimit' := ?_ }
  refine ⟨PullbackCone.IsLimit.mk
    (singularHomotopyFiberToEndingPath_evalZero p b).symm
    (fun s => pullback.lift
      (Limits.prod.lift s.fst
        (s.snd ≫ singularTopEndingPathUnit B b))
      (s.snd ≫ singularTopEndingPathPath B b) ?_)
    (fun s => by
      rw [← Category.assoc, pullback.lift_fst]
      simp)
    (fun s => by
      apply pullback.hom_ext
      · rw [Category.assoc, singularHomotopyFiberToEndingPath_path,
          pullback.lift_snd]
      · rw [Category.assoc, singularHomotopyFiberToEndingPath_unit,
          ← Category.assoc, pullback.lift_fst]
        simp)
    (fun s m h₁ h₂ => by
      apply TopCat.homotopyPullback_hom_ext
      · rw [h₁]
        symm
        rw [← Category.assoc, pullback.lift_fst]
        simp
      · have h := congrArg
          (fun k => k ≫ singularTopEndingPathUnit B b) h₂
        calc
          m ≫ TopCat.homotopyPullbackRight p (TopCat.const b) =
              (m ≫ singularHomotopyFiberToEndingPath p b) ≫
                singularTopEndingPathUnit B b := by
            rw [Category.assoc, singularHomotopyFiberToEndingPath_unit]
          _ = s.snd ≫ singularTopEndingPathUnit B b := h
          _ = pullback.lift
                (Limits.prod.lift s.fst
                  (s.snd ≫ singularTopEndingPathUnit B b))
                (s.snd ≫ singularTopEndingPathPath B b) _ ≫
              TopCat.homotopyPullbackRight p (TopCat.const b) := by
            rw [← Category.assoc, pullback.lift_fst]
            simp
      · have h := congrArg
          (fun k => k ≫ singularTopEndingPathPath B b) h₂
        calc
          m ≫ TopCat.homotopyFiberPath p b =
              (m ≫ singularHomotopyFiberToEndingPath p b) ≫
                singularTopEndingPathPath B b := by
            rw [Category.assoc, singularHomotopyFiberToEndingPath_path]
          _ = s.snd ≫ singularTopEndingPathPath B b := h
          _ = pullback.lift
                (Limits.prod.lift s.fst
                  (s.snd ≫ singularTopEndingPathUnit B b))
                (s.snd ≫ singularTopEndingPathPath B b) _ ≫
              TopCat.homotopyFiberPath p b := by
            rw [pullback.lift_snd])⟩
  apply Limits.prod.hom_ext
  · simpa [TopCat.pathEndpoints, singularTopEndingPathEvalZero,
      Category.assoc] using s.condition
  · simp [TopCat.pathEndpoints, Category.assoc,
      singularTopEndingPathPath_evalOne]

private noncomputable def singularHomotopyFiberEndingPullbackIso
    {E B : TopCat.{v}} (p : E ⟶ B) (b : B) :
    TopCat.homotopyFiber p b ≅
      pullback p (singularTopEndingPathEvalZero B b) :=
  (singularHomotopyFiber_isPullback_endingPath p b).isoPullback

@[reassoc]
private theorem singularHomotopyFiberEndingPullbackIso_hom_fst
    {E B : TopCat.{v}} (p : E ⟶ B) (b : B) :
    (singularHomotopyFiberEndingPullbackIso p b).hom ≫
        pullback.fst p (singularTopEndingPathEvalZero B b) =
      TopCat.homotopyFiberToTotal p b :=
  (singularHomotopyFiber_isPullback_endingPath p b).isoPullback_hom_fst

@[reassoc]
private theorem singularHomotopyFiberEndingPullbackIso_hom_snd
    {E B : TopCat.{v}} (p : E ⟶ B) (b : B) :
    (singularHomotopyFiberEndingPullbackIso p b).hom ≫
        pullback.snd p (singularTopEndingPathEvalZero B b) =
      singularHomotopyFiberToEndingPath p b :=
  (singularHomotopyFiber_isPullback_endingPath p b).isoPullback_hom_snd

private noncomputable def singularIntervalBridgeIso (B : TopCat.{v}) :
    TopCat.pathObject B ≅ TopCat.of C(unitInterval, B) :=
  TopCat.isoOfHomeo
    (Homeomorph.arrowCongr TopCat.I.homeomorph (Homeomorph.refl B))

private def singularOrdinaryPathEvalZero (B : TopCat.{v}) :
    TopCat.of C(unitInterval, B) ⟶ B :=
  TopCat.ofHom ⟨fun gamma => gamma 0, continuous_eval_const 0⟩

private def singularOrdinaryPathEvalOne (B : TopCat.{v}) :
    TopCat.of C(unitInterval, B) ⟶ B :=
  TopCat.ofHom ⟨fun gamma => gamma 1, continuous_eval_const 1⟩

@[reassoc]
private theorem singularIntervalBridgeIso_hom_evalZero
    (B : TopCat.{v}) :
    (singularIntervalBridgeIso B).hom ≫
        singularOrdinaryPathEvalZero B =
      TopCat.pathEvalZero B := by
  ext gamma
  rfl

@[reassoc]
private theorem singularIntervalBridgeIso_hom_evalOne
    (B : TopCat.{v}) :
    (singularIntervalBridgeIso B).hom ≫
        singularOrdinaryPathEvalOne B =
      TopCat.pathEvalOne B := by
  ext gamma
  rfl

private noncomputable def singularTopEndingPathIntervalMap
    (B : TopCat.{v}) (b : B) :
    singularTopEndingPath B b ⟶
      pullback (singularOrdinaryPathEvalOne B)
        (TopCat.const b : TopCat.of PUnit ⟶ B) :=
  pullback.map
    (TopCat.pathEvalOne B) (TopCat.const b)
    (singularOrdinaryPathEvalOne B) (TopCat.const b)
    (singularIntervalBridgeIso B).hom
    (𝟙 (TopCat.of PUnit)) (𝟙 B)
    (by
      rw [Category.comp_id, singularIntervalBridgeIso_hom_evalOne])
    (by simp)

private noncomputable def singularTopEndingPathIntervalIso
    (B : TopCat.{v}) (b : B) :
    singularTopEndingPath B b ≅
      pullback (singularOrdinaryPathEvalOne B)
        (TopCat.const b : TopCat.of PUnit ⟶ B) := by
  let _ : IsIso (singularTopEndingPathIntervalMap B b) := by
    dsimp [singularTopEndingPathIntervalMap]
    infer_instance
  exact asIso (singularTopEndingPathIntervalMap B b)

@[reassoc (attr := simp)]
private theorem singularTopEndingPathIntervalIso_hom_fst
    (B : TopCat.{v}) (b : B) :
    (singularTopEndingPathIntervalIso B b).hom ≫
        pullback.fst (singularOrdinaryPathEvalOne B) (TopCat.const b) =
      singularTopEndingPathPath B b ≫
        (singularIntervalBridgeIso B).hom := by
  change singularTopEndingPathIntervalMap B b ≫
      pullback.fst (singularOrdinaryPathEvalOne B) (TopCat.const b) = _
  simp only [singularTopEndingPathIntervalMap, pullback.lift_fst]

@[reassoc (attr := simp)]
private theorem singularTopEndingPathIntervalIso_hom_snd
    (B : TopCat.{v}) (b : B) :
    (singularTopEndingPathIntervalIso B b).hom ≫
        pullback.snd (singularOrdinaryPathEvalOne B) (TopCat.const b) =
      singularTopEndingPathUnit B b := by
  change singularTopEndingPathIntervalMap B b ≫
      pullback.snd (singularOrdinaryPathEvalOne B) (TopCat.const b) = _
  simp only [singularTopEndingPathIntervalMap, pullback.lift_snd,
    Category.comp_id]

private def singularOrdinaryEndingPairHomeomorph
    (B : TopCat.{v}) (b : B) :
    {q : C(unitInterval, B) × PUnit //
      singularOrdinaryPathEvalOne B q.1 =
        (TopCat.const b : TopCat.of PUnit ⟶ B) q.2} ≃ₜ
      {gamma : C(unitInterval, B) //
        (singularOrdinaryPathEvalOne B).hom gamma = b} where
  toFun q := ⟨q.1.1, by simpa [TopCat.const] using q.2⟩
  invFun gamma := ⟨(gamma.1, PUnit.unit), by
    simpa [TopCat.const] using gamma.2⟩
  left_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · subsingleton
  right_inv gamma := by
    apply Subtype.ext
    rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_fst.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.prodMk continuous_const

private noncomputable def singularOrdinaryEndingPairIso
    (B : TopCat.{v}) (b : B) :
    TopCat.of {q : C(unitInterval, B) × PUnit //
      singularOrdinaryPathEvalOne B q.1 =
        (TopCat.const b : TopCat.of PUnit ⟶ B) q.2} ≅
      TopCat.of {gamma : C(unitInterval, B) //
        (singularOrdinaryPathEvalOne B).hom gamma = b} :=
  TopCat.isoOfHomeo (singularOrdinaryEndingPairHomeomorph B b)

private noncomputable def singularOrdinaryEndingPathIncl
    (B : TopCat.{v}) (b : B) :
    TopCat.of {gamma : C(unitInterval, B) //
      (singularOrdinaryPathEvalOne B).hom gamma = b} ⟶
      TopCat.of C(unitInterval, B) :=
  AlgebraicTopology.subspaceIncl
    (X := TopCat.of C(unitInterval, B))
    (Set.ofPred fun gamma : C(unitInterval, B) =>
      (singularOrdinaryPathEvalOne B).hom gamma = b)

@[reassoc]
private theorem singularOrdinaryEndingPairIso_hom_incl
    (B : TopCat.{v}) (b : B) :
    (singularOrdinaryEndingPairIso B b).hom ≫
      singularOrdinaryEndingPathIncl B b =
      TopCat.pullbackFst (singularOrdinaryPathEvalOne B)
        (TopCat.const (X := TopCat.of PUnit) b) := by
  ext q
  rfl

private noncomputable def singularTopEndingPathLiteralIso
    (B : TopCat.{v}) (b : B) :
    singularTopEndingPath B b ≅
      TopCat.of {gamma : C(unitInterval, B) //
        (singularOrdinaryPathEvalOne B).hom gamma = b} :=
  singularTopEndingPathIntervalIso B b ≪≫
    TopCat.pullbackIsoProdSubtype
      (singularOrdinaryPathEvalOne B) (TopCat.const b) ≪≫
    singularOrdinaryEndingPairIso B b

@[reassoc]
private theorem singularTopEndingPathLiteralIso_hom_incl
    (B : TopCat.{v}) (b : B) :
    (singularTopEndingPathLiteralIso B b).hom ≫
        singularOrdinaryEndingPathIncl B b =
      singularTopEndingPathPath B b ≫
        (singularIntervalBridgeIso B).hom := by
  simp only [singularTopEndingPathLiteralIso, Iso.trans_hom,
    Category.assoc]
  rw [singularOrdinaryEndingPairIso_hom_incl]
  rw [TopCat.pullbackIsoProdSubtype_hom_fst]
  rw [singularTopEndingPathIntervalIso_hom_fst]

@[reassoc]
private theorem singularTopEndingPathLiteralIso_hom_evalZero
    (B : TopCat.{v}) (b : B) :
    (singularTopEndingPathLiteralIso B b).hom ≫
        singularOrdinaryEndingPathIncl B b ≫
          singularOrdinaryPathEvalZero B =
      singularTopEndingPathEvalZero B b := by
  rw [← Category.assoc, singularTopEndingPathLiteralIso_hom_incl,
    Category.assoc, singularIntervalBridgeIso_hom_evalZero]

end SSet
namespace SSet

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped Simplicial

universe v

private noncomputable abbrev singularSimpEndingPath
    (B : TopCat.{v}) (b : B) : SSet.{v} :=
  Subcomplex.fiber
    (eval₁ : pathSpace (TopCat.toSSet.obj B) ⟶ TopCat.toSSet.obj B)
    (TopCat.toSSetObj₀Equiv.symm b)

private noncomputable abbrev singularSimpEndingPathIncl
    (B : TopCat.{v}) (b : B) :
    singularSimpEndingPath B b ⟶ pathSpace (TopCat.toSSet.obj B) :=
  (Subcomplex.fiber
    (eval₁ : pathSpace (TopCat.toSSet.obj B) ⟶ TopCat.toSSet.obj B)
    (TopCat.toSSetObj₀Equiv.symm b)).ι

private noncomputable abbrev singularSimpEndingPathEvalZero
    (B : TopCat.{v}) (b : B) :
    singularSimpEndingPath B b ⟶ TopCat.toSSet.obj B :=
  singularSimpEndingPathIncl B b ≫ eval₀

@[reassoc]
private theorem singularPathIso_hom_evalZero (B : TopCat.{v}) :
    (singularPathIso B).hom ≫
        (eval₀ : pathSpace (TopCat.toSSet.obj B) ⟶
          TopCat.toSSet.obj B) =
      TopCat.toSSet.map (singularOrdinaryPathEvalZero B) := by
  simpa [singularPathIso, singularOrdinaryPathEvalZero,
    TopCat.intervalContinuousMapEvalAt] using
      (singularPathComparison_eval₀ B)

@[reassoc]
private theorem singularPathIso_hom_evalOne (B : TopCat.{v}) :
    (singularPathIso B).hom ≫
        (eval₁ : pathSpace (TopCat.toSSet.obj B) ⟶
          TopCat.toSSet.obj B) =
      TopCat.toSSet.map (singularOrdinaryPathEvalOne B) := by
  simpa [singularPathIso, singularOrdinaryPathEvalOne,
    TopCat.intervalContinuousMapEvalAt] using
      (singularPathComparison_eval₁ B)

private noncomputable def singularEndingPathMapFiberIso
    (B : TopCat.{v}) (b : B) :
    (Subcomplex.fiber
      (TopCat.toSSet.map (singularOrdinaryPathEvalOne B))
      (TopCat.toSSetObj₀Equiv.symm b) : SSet.{v}) ≅
      singularSimpEndingPath B b := by
  let ePath := singularPathIso B
  let eBase := Iso.refl (TopCat.toSSet.obj B)
  have hc : ePath.hom ≫
        (eval₁ : pathSpace (TopCat.toSSet.obj B) ⟶
          TopCat.toSSet.obj B) =
      TopCat.toSSet.map (singularOrdinaryPathEvalOne B) ≫ eBase.hom := by
    simpa [ePath, eBase] using singularPathIso_hom_evalOne B
  exact Subcomplex.mapFiberIso ePath eBase hc rfl

@[reassoc]
private theorem singularOrdinaryFiberIso_hom_incl
    (B : TopCat.{v}) (b : B) :
    (singularFiberIso (singularOrdinaryPathEvalOne B).hom b).hom ≫
        (Subcomplex.fiber
          (TopCat.toSSet.map (singularOrdinaryPathEvalOne B))
          (TopCat.toSSetObj₀Equiv.symm b)).ι =
      TopCat.toSSet.map (singularOrdinaryEndingPathIncl B b) := by
  simpa [singularOrdinaryEndingPathIncl] using
    (singularFiberIso_hom_ι
      (singularOrdinaryPathEvalOne B).hom b)

private noncomputable def singularEndingPathIso
    (B : TopCat.{v}) (b : B) :
    TopCat.toSSet.obj (singularTopEndingPath B b) ≅
      singularSimpEndingPath B b :=
  TopCat.toSSet.mapIso (singularTopEndingPathLiteralIso B b) ≪≫
    singularFiberIso (singularOrdinaryPathEvalOne B).hom b ≪≫
    singularEndingPathMapFiberIso B b

@[reassoc]
private theorem singularEndingPathIso_hom_incl
    (B : TopCat.{v}) (b : B) :
    (singularEndingPathIso B b).hom ≫
        singularSimpEndingPathIncl B b =
      TopCat.toSSet.map (singularTopEndingPathPath B b) ≫
        TopCat.toSSet.map (singularIntervalBridgeIso B).hom ≫
          (singularPathIso B).hom := by
  unfold singularEndingPathIso singularEndingPathMapFiberIso
  dsimp only
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [Subcomplex.mapFiberIso_hom_ι]
  rw [singularOrdinaryFiberIso_hom_incl_assoc]
  rw [← Functor.map_comp_assoc,
    singularTopEndingPathLiteralIso_hom_incl]
  rw [Functor.map_comp_assoc]

@[reassoc]
private theorem singularEndingPathIso_hom_evalZero
    (B : TopCat.{v}) (b : B) :
    (singularEndingPathIso B b).hom ≫
        singularSimpEndingPathEvalZero B b =
      TopCat.toSSet.map (singularTopEndingPathEvalZero B b) := by
  rw [singularSimpEndingPathEvalZero, ← Category.assoc,
    singularEndingPathIso_hom_incl]
  rw [Category.assoc, Category.assoc, singularPathIso_hom_evalZero]
  rw [← Functor.map_comp]
  rw [singularIntervalBridgeIso_hom_evalZero]
  rfl

private noncomputable def singularEndingPullbackMap
    {E B : TopCat.{v}} (p : E ⟶ B) (b : B) :
    pullback (TopCat.toSSet.map p)
        (TopCat.toSSet.map (singularTopEndingPathEvalZero B b)) ⟶
      pullback (TopCat.toSSet.map p)
        (singularSimpEndingPathEvalZero B b) :=
  pullback.map
    (TopCat.toSSet.map p)
    (TopCat.toSSet.map (singularTopEndingPathEvalZero B b))
    (TopCat.toSSet.map p)
    (singularSimpEndingPathEvalZero B b)
    (𝟙 _) (singularEndingPathIso B b).hom (𝟙 _)
    (by simp)
    (by
      simpa using (singularEndingPathIso_hom_evalZero B b).symm)

private noncomputable def singularEndingPullbackIso
    {E B : TopCat.{v}} (p : E ⟶ B) (b : B) :
    pullback (TopCat.toSSet.map p)
        (TopCat.toSSet.map (singularTopEndingPathEvalZero B b)) ≅
      pullback (TopCat.toSSet.map p)
        (singularSimpEndingPathEvalZero B b) := by
  let _ : IsIso (singularEndingPullbackMap p b) := by
    dsimp [singularEndingPullbackMap]
    infer_instance
  exact asIso (singularEndingPullbackMap p b)

@[reassoc (attr := simp)]
private theorem singularEndingPullbackIso_hom_fst
    {E B : TopCat.{v}} (p : E ⟶ B) (b : B) :
    (singularEndingPullbackIso p b).hom ≫
        pullback.fst (TopCat.toSSet.map p)
          (singularSimpEndingPathEvalZero B b) =
      pullback.fst (TopCat.toSSet.map p)
        (TopCat.toSSet.map (singularTopEndingPathEvalZero B b)) := by
  change singularEndingPullbackMap p b ≫
      pullback.fst (TopCat.toSSet.map p)
        (singularSimpEndingPathEvalZero B b) = _
  simp only [singularEndingPullbackMap, pullback.lift_fst,
    Category.comp_id]

@[reassoc (attr := simp)]
private theorem singularEndingPullbackIso_hom_snd
    {E B : TopCat.{v}} (p : E ⟶ B) (b : B) :
    (singularEndingPullbackIso p b).hom ≫
        pullback.snd (TopCat.toSSet.map p)
          (singularSimpEndingPathEvalZero B b) =
      pullback.snd (TopCat.toSSet.map p)
          (TopCat.toSSet.map (singularTopEndingPathEvalZero B b)) ≫
        (singularEndingPathIso B b).hom := by
  change singularEndingPullbackMap p b ≫
      pullback.snd (TopCat.toSSet.map p)
        (singularSimpEndingPathEvalZero B b) = _
  simp only [singularEndingPullbackMap, pullback.lift_snd]

private theorem singularTensorLeftIsoProd_hom_fst
    (A C : SSet.{v}) :
    (CartesianMonoidalCategory.tensorLeftIsoProd A).hom.app C ≫
        Limits.prod.fst =
      SemiCartesianMonoidalCategory.fst A C :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct A C)
    (limit.isLimit _) ⟨WalkingPair.left⟩

private theorem singularTensorLeftIsoProd_hom_snd
    (A C : SSet.{v}) :
    (CartesianMonoidalCategory.tensorLeftIsoProd A).hom.app C ≫
        Limits.prod.snd =
      SemiCartesianMonoidalCategory.snd A C :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct A C)
    (limit.isLimit _) ⟨WalkingPair.right⟩

private noncomputable def singularCoreEndpointPair (Y : SSet.{v}) :
    pathSpace Y ⟶ Y ⨯ Y :=
  evalPair ≫ (CartesianMonoidalCategory.tensorLeftIsoProd Y).hom.app Y

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private theorem singularCoreEndpointPair_fst (Y : SSet.{v}) :
    singularCoreEndpointPair Y ≫ Limits.prod.fst = eval₀ := by
  rw [singularCoreEndpointPair, Category.assoc,
    singularTensorLeftIsoProd_hom_fst]
  exact evalPair_fst

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private theorem singularCoreEndpointPair_snd (Y : SSet.{v}) :
    singularCoreEndpointPair Y ≫ Limits.prod.snd = eval₁ := by
  rw [singularCoreEndpointPair, Category.assoc,
    singularTensorLeftIsoProd_hom_snd]
  exact evalPair_snd

private noncomputable abbrev singularCoreEndingPath
    (Y : SSet.{v}) (y : Y _⦋0⦌) : SSet.{v} :=
  Subcomplex.fiber (eval₁ : pathSpace Y ⟶ Y) y

private noncomputable abbrev singularCoreEndingPathIncl
    (Y : SSet.{v}) (y : Y _⦋0⦌) :
    singularCoreEndingPath Y y ⟶ pathSpace Y :=
  (Subcomplex.fiber (eval₁ : pathSpace Y ⟶ Y) y).ι

private noncomputable abbrev singularCoreEndingPathEvalZero
    (Y : SSet.{v}) (y : Y _⦋0⦌) :
    singularCoreEndingPath Y y ⟶ Y :=
  singularCoreEndingPathIncl Y y ≫ eval₀

private noncomputable def singularCoreFiberToEndingPath
    {X Y : SSet.{v}} (f : X ⟶ Y) (y : Y _⦋0⦌) :
    pathHomotopyFiber f y ⟶ singularCoreEndingPath Y y :=
  Subcomplex.lift (pathHomotopyFiberPath f y) (by
    rw [Subcomplex.range_le_fiber_iff]
    exact pathHomotopyFiberPath_evalOne f y)

@[reassoc (attr := simp)]
private theorem singularCoreFiberToEndingPath_incl
    {X Y : SSet.{v}} (f : X ⟶ Y) (y : Y _⦋0⦌) :
    singularCoreFiberToEndingPath f y ≫
        singularCoreEndingPathIncl Y y =
      pathHomotopyFiberPath f y := by
  rw [singularCoreFiberToEndingPath, Subcomplex.lift_ι]

@[reassoc]
private theorem singularCoreFiberToEndingPath_evalZero
    {X Y : SSet.{v}} (f : X ⟶ Y) (y : Y _⦋0⦌) :
    singularCoreFiberToEndingPath f y ≫
        singularCoreEndingPathEvalZero Y y =
      pathHomotopyFiberToTotal f y ≫ f := by
  simp [singularCoreEndingPathEvalZero, Category.assoc,
    pathHomotopyFiberPath_evalZero]

set_option backward.isDefEq.respectTransparency false in
private theorem singularCoreFiber_isPullback_endingPath
    {X Y : SSet.{v}} (f : X ⟶ Y) (y : Y _⦋0⦌) :
    IsPullback (pathHomotopyFiberToTotal f y)
      (singularCoreFiberToEndingPath f y) f
      (singularCoreEndingPathEvalZero Y y) := by
  have hw := (singularCoreFiberToEndingPath_evalZero f y).symm
  have hcompat (s : PullbackCone f
      (singularCoreEndingPathEvalZero Y y)) :
      Limits.prod.lift s.fst
            (SSet.stdSimplex.isTerminalObj₀.from _) ≫
          Limits.prod.map f
            (SSet.const (X := (Δ[0] : SSet.{v})) y) =
        (s.snd ≫ singularCoreEndingPathIncl Y y) ≫
          singularCoreEndpointPair Y := by
    apply Limits.prod.hom_ext
    · calc
        (Limits.prod.lift s.fst
              (SSet.stdSimplex.isTerminalObj₀.from _) ≫
            Limits.prod.map f (SSet.const y)) ≫ Limits.prod.fst =
          s.fst ≫ f := by simp
        _ = s.snd ≫ singularCoreEndingPathEvalZero Y y := s.condition
        _ = ((s.snd ≫ singularCoreEndingPathIncl Y y) ≫
              singularCoreEndpointPair Y) ≫ Limits.prod.fst := by
          dsimp only [singularCoreEndingPathEvalZero]
          calc
            s.snd ≫ singularCoreEndingPathIncl Y y ≫ eval₀ =
                (s.snd ≫ singularCoreEndingPathIncl Y y) ≫
                  (singularCoreEndpointPair Y ≫ Limits.prod.fst) := by
              rw [singularCoreEndpointPair_fst]
              exact (Category.assoc _ _ _).symm
            _ = ((s.snd ≫ singularCoreEndingPathIncl Y y) ≫
                singularCoreEndpointPair Y) ≫ Limits.prod.fst :=
              (Category.assoc _ _ _).symm
    · calc
        (Limits.prod.lift s.fst
              (SSet.stdSimplex.isTerminalObj₀.from _) ≫
            Limits.prod.map f (SSet.const y)) ≫ Limits.prod.snd =
          SSet.const y := by simp
        _ = ((s.snd ≫ singularCoreEndingPathIncl Y y) ≫
              singularCoreEndpointPair Y) ≫ Limits.prod.snd := by
          calc
            SSet.const y =
                (s.snd ≫ singularCoreEndingPathIncl Y y) ≫ eval₁ := by
              rw [Category.assoc, singularCoreEndingPathIncl,
                Subcomplex.fiber_ι_comp]
              simp
            _ = (s.snd ≫ singularCoreEndingPathIncl Y y) ≫
                (singularCoreEndpointPair Y ≫ Limits.prod.snd) := by
              rw [singularCoreEndpointPair_snd]
            _ = ((s.snd ≫ singularCoreEndingPathIncl Y y) ≫
                singularCoreEndpointPair Y) ≫ Limits.prod.snd :=
              (Category.assoc _ _ _).symm
  refine { w := hw, isLimit' := ?_ }
  refine ⟨PullbackCone.IsLimit.mk
    (singularCoreFiberToEndingPath_evalZero f y).symm
    (fun s => pullback.lift
      (Limits.prod.lift s.fst
        (SSet.stdSimplex.isTerminalObj₀.from _))
      (s.snd ≫ singularCoreEndingPathIncl Y y) (hcompat s))
    (fun s => by
      rw [pathHomotopyFiberToTotal, ← Category.assoc,
        pullback.lift_fst]
      simp)
    (fun s => by
      apply (cancel_mono (singularCoreEndingPathIncl Y y)).mp
      rw [Category.assoc, singularCoreFiberToEndingPath_incl,
        pullback.lift_snd])
    (fun s m h₁ h₂ => by
      apply pullback.hom_ext
      · apply Limits.prod.hom_ext
        · calc
            (m ≫ pullback.fst
                (Limits.prod.map f
                  (SSet.const (X := (Δ[0] : SSet.{v})) y))
                (singularCoreEndpointPair Y)) ≫ Limits.prod.fst =
                m ≫ pathHomotopyFiberToTotal f y := by rfl
            _ = s.fst := h₁
            _ = (pullback.lift
                  (Limits.prod.lift s.fst
                    (SSet.stdSimplex.isTerminalObj₀.from _))
                  (s.snd ≫ singularCoreEndingPathIncl Y y) (hcompat s) ≫
                pullback.fst
                  (Limits.prod.map f
                    (SSet.const (X := (Δ[0] : SSet.{v})) y))
                  (singularCoreEndpointPair Y)) ≫ Limits.prod.fst := by
              rw [pullback.lift_fst, Limits.prod.lift_fst]
        · apply SSet.stdSimplex.isTerminalObj₀.hom_ext
      · have h := congrArg
          (fun k => k ≫ singularCoreEndingPathIncl Y y) h₂
        calc
          m ≫ pullback.snd
                (Limits.prod.map f
                  (SSet.const (X := (Δ[0] : SSet.{v})) y))
                (singularCoreEndpointPair Y) =
              m ≫ pathHomotopyFiberPath f y := by rfl
          _ = s.snd ≫ singularCoreEndingPathIncl Y y := by
            simpa [Category.assoc] using h
          _ = pullback.lift
                (Limits.prod.lift s.fst
                  (SSet.stdSimplex.isTerminalObj₀.from _))
                (s.snd ≫ singularCoreEndingPathIncl Y y) (hcompat s) ≫
              pullback.snd
                (Limits.prod.map f
                  (SSet.const (X := (Δ[0] : SSet.{v})) y))
                (singularCoreEndpointPair Y) := by
            rw [pullback.lift_snd])⟩

private noncomputable def singularCoreEndingPullbackIso
    {X Y : SSet.{v}} (f : X ⟶ Y) (y : Y _⦋0⦌) :
    pathHomotopyFiber f y ≅
      pullback f (singularCoreEndingPathEvalZero Y y) :=
  (singularCoreFiber_isPullback_endingPath f y).isoPullback

@[reassoc]
private theorem singularCoreEndingPullbackIso_inv_toTotal
    {X Y : SSet.{v}} (f : X ⟶ Y) (y : Y _⦋0⦌) :
    (singularCoreEndingPullbackIso f y).inv ≫
        pathHomotopyFiberToTotal f y =
      pullback.fst f (singularCoreEndingPathEvalZero Y y) :=
  (singularCoreFiber_isPullback_endingPath f y).isoPullback_inv_fst

@[reassoc]
private theorem singularCoreEndingPullbackIso_inv_toEnding
    {X Y : SSet.{v}} (f : X ⟶ Y) (y : Y _⦋0⦌) :
    (singularCoreEndingPullbackIso f y).inv ≫
        singularCoreFiberToEndingPath f y =
      pullback.snd f (singularCoreEndingPathEvalZero Y y) :=
  (singularCoreFiber_isPullback_endingPath f y).isoPullback_inv_snd

@[reassoc]
private theorem singularCoreEndingPullbackIso_inv_path
    {X Y : SSet.{v}} (f : X ⟶ Y) (y : Y _⦋0⦌) :
    (singularCoreEndingPullbackIso f y).inv ≫
        pathHomotopyFiberPath f y =
      pullback.snd f (singularCoreEndingPathEvalZero Y y) ≫
        singularCoreEndingPathIncl Y y := by
  rw [← singularCoreFiberToEndingPath_incl,
    ← Category.assoc, singularCoreEndingPullbackIso_inv_toEnding]

private noncomputable def singularHomotopyFiberPreservedPullbackIso
    {E B : TopCat.{v}} (p : E ⟶ B) (b : B) :
    TopCat.toSSet.obj (TopCat.homotopyFiber p b) ≅
      pullback (TopCat.toSSet.map p)
        (TopCat.toSSet.map (singularTopEndingPathEvalZero B b)) :=
  TopCat.toSSet.mapIso (singularHomotopyFiberEndingPullbackIso p b) ≪≫
    PreservesPullback.iso TopCat.toSSet p
      (singularTopEndingPathEvalZero B b)

@[reassoc (attr := simp)]
private theorem singularHomotopyFiberPreservedPullbackIso_hom_fst
    {E B : TopCat.{v}} (p : E ⟶ B) (b : B) :
    (singularHomotopyFiberPreservedPullbackIso p b).hom ≫
        pullback.fst (TopCat.toSSet.map p)
          (TopCat.toSSet.map (singularTopEndingPathEvalZero B b)) =
      TopCat.toSSet.map (TopCat.homotopyFiberToTotal p b) := by
  simp only [singularHomotopyFiberPreservedPullbackIso,
    Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    PreservesPullback.iso_hom_fst]
  rw [← Functor.map_comp,
    singularHomotopyFiberEndingPullbackIso_hom_fst]

@[reassoc (attr := simp)]
private theorem singularHomotopyFiberPreservedPullbackIso_hom_snd
    {E B : TopCat.{v}} (p : E ⟶ B) (b : B) :
    (singularHomotopyFiberPreservedPullbackIso p b).hom ≫
        pullback.snd (TopCat.toSSet.map p)
          (TopCat.toSSet.map (singularTopEndingPathEvalZero B b)) =
      TopCat.toSSet.map (singularHomotopyFiberToEndingPath p b) := by
  simp only [singularHomotopyFiberPreservedPullbackIso,
    Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    PreservesPullback.iso_hom_snd]
  rw [← Functor.map_comp,
    singularHomotopyFiberEndingPullbackIso_hom_snd]

/-- The singular simplicial set of the compact-open homotopy fiber is
canonically isomorphic to the explicit simplicial path homotopy fiber. -/
noncomputable def singularPathHomotopyFiberIso
    {E B : TopCat.{v}} (p : E ⟶ B) (b : B) :
    TopCat.toSSet.obj (TopCat.homotopyFiber p b) ≅
      pathHomotopyFiber (TopCat.toSSet.map p)
        (TopCat.toSSetObj₀Equiv.symm b) :=
  singularHomotopyFiberPreservedPullbackIso p b ≪≫
    singularEndingPullbackIso p b ≪≫
    (singularCoreEndingPullbackIso (TopCat.toSSet.map p)
      (TopCat.toSSetObj₀Equiv.symm b)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The forward singular homotopy-fiber isomorphism retains the total-space
projection. -/
@[reassoc]
theorem singularPathHomotopyFiberIso_hom_toTotal
    {E B : TopCat.{v}} (p : E ⟶ B) (b : B) :
    (singularPathHomotopyFiberIso p b).hom ≫
        pathHomotopyFiberToTotal (TopCat.toSSet.map p)
          (TopCat.toSSetObj₀Equiv.symm b) =
      TopCat.toSSet.map (TopCat.homotopyFiberToTotal p b) := by
  simp only [singularPathHomotopyFiberIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc]
  rw [singularCoreEndingPullbackIso_inv_toTotal]
  change
    ((singularHomotopyFiberPreservedPullbackIso p b).hom ≫
      (singularEndingPullbackIso p b).hom) ≫
        pullback.fst (TopCat.toSSet.map p)
          (singularSimpEndingPathEvalZero B b) = _
  rw [Category.assoc, singularEndingPullbackIso_hom_fst]
  rw [singularHomotopyFiberPreservedPullbackIso_hom_fst]

set_option backward.isDefEq.respectTransparency false in
/-- The forward singular homotopy-fiber isomorphism retains the complete
path, through the canonical lifted-interval compact-open bridge. -/
@[reassoc]
theorem singularPathHomotopyFiberIso_hom_path
    {E B : TopCat.{v}} (p : E ⟶ B) (b : B) :
    (singularPathHomotopyFiberIso p b).hom ≫
        pathHomotopyFiberPath (TopCat.toSSet.map p)
          (TopCat.toSSetObj₀Equiv.symm b) =
      TopCat.toSSet.map (TopCat.homotopyFiberPath p b) ≫
        TopCat.toSSet.map
          (TopCat.isoOfHomeo
            (Homeomorph.arrowCongr TopCat.I.homeomorph
              (Homeomorph.refl B))).hom ≫
          (singularPathIso B).hom := by
  simp only [singularPathHomotopyFiberIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc]
  rw [singularCoreEndingPullbackIso_inv_path]
  change
    (((singularHomotopyFiberPreservedPullbackIso p b).hom ≫
      (singularEndingPullbackIso p b).hom) ≫
        pullback.snd (TopCat.toSSet.map p)
          (singularSimpEndingPathEvalZero B b)) ≫
      singularSimpEndingPathIncl B b = _
  simp only [Category.assoc]
  rw [singularEndingPullbackIso_hom_snd_assoc]
  rw [singularEndingPathIso_hom_incl]
  rw [singularHomotopyFiberPreservedPullbackIso_hom_snd_assoc]
  rw [← Functor.map_comp_assoc,
    singularHomotopyFiberToEndingPath_path]
  rfl

end SSet
