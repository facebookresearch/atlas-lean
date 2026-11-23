/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularFiberIso
public import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularLoopComparison
public import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularPathComparisonIso

/-!
# Singular comparisons for based paths and loops are isomorphisms

The singular/free-path isomorphism restricts through the initial-endpoint
fiber to based paths and then through the final-endpoint fiber to loops.  The
forward legs are exactly the existing `singularBasedPathComparison` and
`singularLoopComparison`, so the loop isomorphism inherits their strict
naturality with respect to literal continuous postcomposition.

Only the endpoint-fiber restrictions and same-universe strict naturality are
provided.  This file makes no weak-equivalence, homotopy-group shift,
weakly-pointed preservation, spectrum, or Q/S claim.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial Topology

universe u

namespace SSet

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

private noncomputable def intervalContinuousMapEvalZero
    (X : Type u) [TopologicalSpace X] : C(C(unitInterval, X), X) where
  toFun gamma := gamma 0
  continuous_toFun := continuous_eval_const 0

private noncomputable def intervalBasedPathEvalOne
    (X : Type u) [TopologicalSpace X] (x : X) :
    C({gamma : C(unitInterval, X) // gamma 0 = x}, X) where
  toFun gamma := gamma.1 1
  continuous_toFun := continuous_eval_const 1 |>.comp continuous_subtype_val

private noncomputable def intervalBasedPathIncl
    (X : Type u) [TopologicalSpace X] (x : X) :
    C({gamma : C(unitInterval, X) // gamma 0 = x}, C(unitInterval, X)) where
  toFun gamma := gamma.1
  continuous_toFun := continuous_subtype_val

private noncomputable def loopToIntervalBasedPath
    (X : Type u) [TopologicalSpace X] (x : X) :
    C(LoopSpace X x, {gamma : C(unitInterval, X) // gamma 0 = x}) where
  toFun gamma := ⟨gamma.toContinuousMap, gamma.source⟩
  continuous_toFun := Continuous.subtype_mk continuous_induced_dom _

/-- The singular simplicial set of compact-open paths starting at `x` is
canonically isomorphic to the simplicial based-path space of `Sing X`. -/
noncomputable def singularBasedPathIso
    (X : Type u) [TopologicalSpace X] (x : X) :
    TopCat.toSSet.obj
        (TopCat.of {gamma : C(unitInterval, X) // gamma 0 = x}) ≅
      SSet.basedPath (TopCat.toSSet.obj (TopCat.of X))
        (TopCat.toSSetObj₀Equiv.symm x) := by
  let eFree := SSet.singularPathIso X
  let eBase := Iso.refl (TopCat.toSSet.obj (TopCat.of X))
  have hc : eFree.hom ≫
        (SSet.eval₀ : SSet.pathSpace
            (TopCat.toSSet.obj (TopCat.of X)) ⟶
          TopCat.toSSet.obj (TopCat.of X)) =
      TopCat.toSSet.map
          (TopCat.ofHom (intervalContinuousMapEvalZero X)) ≫
        eBase.hom := by
    change singularPathComparison X ≫ SSet.eval₀ =
      TopCat.toSSet.map (TopCat.intervalContinuousMapEvalAt X 0) ≫ 𝟙 _
    rw [Category.comp_id, SSet.singularPathComparison_eval₀]
  let eFiber := SSet.Subcomplex.mapFiberIso
    (y := TopCat.toSSetObj₀Equiv.symm x)
    (y' := TopCat.toSSetObj₀Equiv.symm x)
    eFree eBase hc
    (rfl : eBase.hom.app _ (TopCat.toSSetObj₀Equiv.symm x) =
      TopCat.toSSetObj₀Equiv.symm x)
  exact SSet.singularFiberIso
      (intervalContinuousMapEvalZero X) x ≪≫ eFiber

set_option backward.isDefEq.respectTransparency false in
/-- The forward based-path isomorphism is exactly the reviewed based-path
comparison map. -/
@[simp]
theorem singularBasedPathIso_hom
    (X : Type u) [TopologicalSpace X] (x : X) :
    (singularBasedPathIso X x).hom =
      singularBasedPathComparison X x := by
  let _ : Mono (basedPathIncl
      (TopCat.toSSet.obj (TopCat.of X))
      (TopCat.toSSetObj₀Equiv.symm x)) :=
    inferInstanceAs
      (Mono ((Subcomplex.fiber
        (SSet.eval₀ : SSet.pathSpace
          (TopCat.toSSet.obj (TopCat.of X)) ⟶
            TopCat.toSSet.obj (TopCat.of X))
        (TopCat.toSSetObj₀Equiv.symm x)).ι))
  apply (cancel_mono (basedPathIncl
    (TopCat.toSSet.obj (TopCat.of X))
    (TopCat.toSSetObj₀Equiv.symm x))).mp
  unfold singularBasedPathIso
  with_unfolding_all
    simp only [intervalContinuousMapEvalZero, Iso.trans_hom, Category.assoc]
  erw [Subcomplex.mapFiberIso_hom_ι]
  rw [← Category.assoc, singularFiberIso_hom_ι]
  change TopCat.toSSet.map (TopCat.ofHom (intervalBasedPathIncl X x)) ≫
      singularPathComparison X = _
  simpa only [intervalBasedPathIncl, singularPathIso] using
    (singularBasedPathComparison_ι X x).symm

set_option backward.isDefEq.respectTransparency false in
private theorem singularBasedPathIso_hom_proj
    (X : Type u) [TopologicalSpace X] (x : X) :
    (singularBasedPathIso X x).hom ≫
        basedPathProj (TopCat.toSSet.obj (TopCat.of X))
          (TopCat.toSSetObj₀Equiv.symm x) =
      TopCat.toSSet.map
        (TopCat.ofHom (intervalBasedPathEvalOne X x)) := by
  rw [singularBasedPathIso_hom]
  change singularBasedPathComparison X x ≫
      (basedPathIncl (TopCat.toSSet.obj (TopCat.of X))
          (TopCat.toSSetObj₀Equiv.symm x) ≫ SSet.eval₁) = _
  rw [← Category.assoc, singularBasedPathComparison_ι,
    Category.assoc, singularPathComparison_eval₁]
  rw [← TopCat.toSSet.map_comp]
  congr 1

/-- A topological loop is canonically the nested strict fiber of evaluation
at `0` followed by evaluation at `1`. -/
noncomputable def loopNestedHomeomorph
    (X : Type u) [TopologicalSpace X] (x : X) :
    LoopSpace X x ≃ₜ
      {gamma : {p : C(unitInterval, X) // p 0 = x} // gamma.1 1 = x} where
  toFun gamma := ⟨⟨gamma.toContinuousMap, gamma.source⟩, gamma.target⟩
  invFun gamma := Path.mk gamma.1.1 gamma.1.2 gamma.2
  left_inv gamma := by
    apply _root_.Path.ext
    rfl
  right_inv gamma := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_induced_dom
  continuous_invFun := by
    exact continuous_induced_rng.mpr
      (continuous_subtype_val.comp continuous_subtype_val)

private noncomputable def singularLoopNestedIso
    (X : Type u) [TopologicalSpace X] (x : X) :
    TopCat.toSSet.obj (TopCat.of (LoopSpace X x)) ≅
      TopCat.toSSet.obj
        (TopCat.of
          {gamma : {p : C(unitInterval, X) // p 0 = x} //
            gamma.1 1 = x}) :=
  TopCat.toSSet.mapIso
    (TopCat.isoOfHomeo (loopNestedHomeomorph X x))

set_option backward.isDefEq.respectTransparency false in
private theorem singularLoopNestedIso_hom_comp_subspaceIncl
    (X : Type u) [TopologicalSpace X] (x : X) :
    (singularLoopNestedIso X x).hom ≫
        TopCat.toSSet.map
          (AlgebraicTopology.subspaceIncl
            (X := TopCat.of
              {gamma : C(unitInterval, X) // gamma 0 = x})
            (Set.ofPred fun gamma :
              {p : C(unitInterval, X) // p 0 = x} =>
                ({ toFun := fun p => p.1 1
                   continuous_toFun :=
                    continuous_eval_const 1 |>.comp continuous_subtype_val } :
                  C({p : C(unitInterval, X) // p 0 = x}, X)) gamma = x)) =
      TopCat.toSSet.map
        (TopCat.ofHom (loopToIntervalBasedPath X x)) := by
  unfold singularLoopNestedIso
  rw [Functor.mapIso_hom]
  have hTop :
      (TopCat.isoOfHomeo (loopNestedHomeomorph X x)).hom ≫
          AlgebraicTopology.subspaceIncl
          (X := TopCat.of
            {gamma : C(unitInterval, X) // gamma 0 = x})
          (Set.ofPred fun gamma :
            {p : C(unitInterval, X) // p 0 = x} =>
              ({ toFun := fun p => p.1 1
                 continuous_toFun :=
                  continuous_eval_const 1 |>.comp continuous_subtype_val } :
                C({p : C(unitInterval, X) // p 0 = x}, X)) gamma = x) =
        TopCat.ofHom (loopToIntervalBasedPath X x) := by
    apply TopCat.hom_ext
    ext gamma
    rfl
  rw [← TopCat.toSSet.map_comp, hTop]

/-- The singular simplicial set of the topological loop space is canonically
isomorphic to the strict simplicial loop space of `Sing X`. -/
noncomputable def singularLoopIso
    (X : Type u) [TopologicalSpace X] (x : X) :
    TopCat.toSSet.obj (TopCat.of (LoopSpace X x)) ≅
      SSet.loopSpace (TopCat.toSSet.obj (TopCat.of X))
        (TopCat.toSSetObj₀Equiv.symm x) := by
  let eBased := singularBasedPathIso X x
  let eBase := Iso.refl (TopCat.toSSet.obj (TopCat.of X))
  have hc : eBased.hom ≫
        basedPathProj (TopCat.toSSet.obj (TopCat.of X))
          (TopCat.toSSetObj₀Equiv.symm x) =
      TopCat.toSSet.map
          (TopCat.ofHom (intervalBasedPathEvalOne X x)) ≫
        eBase.hom := by
    change (singularBasedPathIso X x).hom ≫
        basedPathProj (TopCat.toSSet.obj (TopCat.of X))
          (TopCat.toSSetObj₀Equiv.symm x) =
      TopCat.toSSet.map
        (TopCat.ofHom (intervalBasedPathEvalOne X x)) ≫ 𝟙 _
    rw [Category.comp_id, singularBasedPathIso_hom_proj]
  let eFiber := SSet.Subcomplex.mapFiberIso
    (y := TopCat.toSSetObj₀Equiv.symm x)
    (y' := TopCat.toSSetObj₀Equiv.symm x)
    eBased eBase hc
    (rfl : eBase.hom.app _ (TopCat.toSSetObj₀Equiv.symm x) =
      TopCat.toSSetObj₀Equiv.symm x)
  exact singularLoopNestedIso X x ≪≫
    SSet.singularFiberIso (intervalBasedPathEvalOne X x) x ≪≫ eFiber

set_option backward.isDefEq.respectTransparency false in
/-- The forward loop isomorphism is exactly the reviewed strict loop
comparison map. -/
@[simp]
theorem singularLoopIso_hom
    (X : Type u) [TopologicalSpace X] (x : X) :
    (singularLoopIso X x).hom = singularLoopComparison X x := by
  let _ : Mono (loopSpaceIncl
      (TopCat.toSSet.obj (TopCat.of X))
      (TopCat.toSSetObj₀Equiv.symm x)) :=
    inferInstanceAs
      (Mono ((Subcomplex.fiber
        (basedPathProj (TopCat.toSSet.obj (TopCat.of X))
          (TopCat.toSSetObj₀Equiv.symm x))
        (TopCat.toSSetObj₀Equiv.symm x)).ι))
  apply (cancel_mono (loopSpaceIncl
    (TopCat.toSSet.obj (TopCat.of X))
    (TopCat.toSSetObj₀Equiv.symm x))).mp
  unfold singularLoopIso
  with_unfolding_all
    simp only [intervalBasedPathEvalOne, Iso.trans_hom, Category.assoc]
  erw [Subcomplex.mapFiberIso_hom_ι]
  slice_lhs 2 3 => rw [singularFiberIso_hom_ι]
  slice_lhs 1 2 => rw [singularLoopNestedIso_hom_comp_subspaceIncl]
  rw [singularBasedPathIso_hom]
  simpa only [loopToIntervalBasedPath] using
    (singularLoopComparison_ι X x).symm

/-- Strict naturality of the forward singular-loop isomorphism. -/
theorem singularLoopIso_hom_naturality
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    TopCat.toSSet.map
          (TopCat.ofHom (ContinuousMap.strictLoopMap f x)) ≫
        (singularLoopIso Y (f x)).hom =
      (singularLoopIso X x).hom ≫
        SSet.loopSpaceMap
          (x := TopCat.toSSetObj₀Equiv.symm x)
          (y := TopCat.toSSetObj₀Equiv.symm (f x))
          (TopCat.toSSet.map (TopCat.ofHom f)) (by rfl) := by
  rw [singularLoopIso_hom, singularLoopIso_hom]
  exact singularLoopComparison_naturality f x

/-- Strict naturality of the inverse singular-loop isomorphism, with the
forced opposite orientation. -/
theorem singularLoopIso_inv_naturality
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    SSet.loopSpaceMap
          (x := TopCat.toSSetObj₀Equiv.symm x)
          (y := TopCat.toSSetObj₀Equiv.symm (f x))
          (TopCat.toSSet.map (TopCat.ofHom f)) (by rfl) ≫
        (singularLoopIso Y (f x)).inv =
      (singularLoopIso X x).inv ≫
        TopCat.toSSet.map
          (TopCat.ofHom (ContinuousMap.strictLoopMap f x)) := by
  rw [← cancel_epi (singularLoopIso X x).hom]
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← singularLoopIso_hom_naturality,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SSet
