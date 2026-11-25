/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.IteratedSplitPullback
public import MathlibExt.Analysis.CStarAlgebra.ContinuousMap.IntervalGluing

/-!
# Matching paths after finite alpha iteration

The carrier is the literal pullback of the iterated endpoint maps on
`alpha^n C([0,1], B)`.  The gluing homomorphism is obtained from the actual
base gluing map and the proved iterated split-pullback equivalence.

This file contains data and endpoint laws only. It defines no homotopy
relation, Setoid, class, stage transition, product, direct limit, flattening,
or alpha/continuous-map comparison.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace AsymptoticAlgebra

universe uB uX uY uZ

attribute [local instance] cStarAlgebra

/-- The endpoint map on the nth literal alpha iterate of the interval
coefficient algebra. -/
@[no_expose]
def endpointHom (n : ℕ) (t : unitInterval)
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    IteratedAsymptoticAlgebra n C(unitInterval, B) →⋆ₙₐ[ℂ]
      IteratedAsymptoticAlgebra n B :=
  IteratedAsymptoticAlgebra.map n
    (ContinuousMap.IntervalGluing.evalAt B t)

/-- The iterated endpoint map is the direct finite-alpha map of evaluation. -/
theorem endpointHom_eq (n : ℕ) (t : unitInterval)
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    endpointHom n t B =
      IteratedAsymptoticAlgebra.map n
        (ContinuousMap.IntervalGluing.evalAt B t) := by
  rfl

/-- Literal matching paths at stage n. -/
abbrev IteratedMatchingPaths (n : ℕ)
    (B : Type uB) [NonUnitalCStarAlgebra B] :=
  NonUnitalCStarPullback.Pullback
    (endpointHom n 1 B) (endpointHom n 0 B)

private theorem evalAt_zero_comp_constantHom
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    (ContinuousMap.IntervalGluing.evalAt B 0).comp
        (ContinuousMap.IntervalGluing.constantHom B) =
      NonUnitalStarAlgHom.id ℂ B := by
  apply NonUnitalStarAlgHom.ext
  intro b
  rfl

/-- Iterating alpha carries the actual base matching-path pullback to the
literal pullback of the iterated endpoint maps. -/
@[no_expose]
noncomputable def iteratedMatchingPathsEquiv (n : ℕ)
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    IteratedAsymptoticAlgebra n
        (ContinuousMap.IntervalGluing.MatchingPaths B) ≃⋆ₐ[ℂ]
      IteratedMatchingPaths n B :=
  iteratedSplitPullbackEquiv n
    (ContinuousMap.IntervalGluing.evalAt B 1)
    (ContinuousMap.IntervalGluing.evalAt B 0)
    (ContinuousMap.IntervalGluing.constantHom B)
    (evalAt_zero_comp_constantHom B)

/-- Genuine iterated matching-path gluing into
`alpha^n C([0,1], B)`. -/
@[no_expose]
noncomputable def glueHomN (n : ℕ)
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    IteratedMatchingPaths n B →⋆ₙₐ[ℂ]
      IteratedAsymptoticAlgebra n C(unitInterval, B) :=
  (IteratedAsymptoticAlgebra.map n
    (ContinuousMap.IntervalGluing.glueHom (B := B))).comp
      (iteratedMatchingPathsEquiv n B).symm.toNonUnitalStarAlgHom

private theorem evalAt_zero_comp_glueHom
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    (ContinuousMap.IntervalGluing.evalAt B 0).comp
        (ContinuousMap.IntervalGluing.glueHom (B := B)) =
      (ContinuousMap.IntervalGluing.evalAt B 0).comp
        (NonUnitalCStarPullback.fstHom
          (ContinuousMap.IntervalGluing.evalAt B 1)
          (ContinuousMap.IntervalGluing.evalAt B 0)) := by
  apply NonUnitalStarAlgHom.ext
  intro p
  change ContinuousMap.IntervalGluing.glueHom p 0 = p.1.1 0
  exact ContinuousMap.IntervalGluing.glueHom_zero p

private theorem evalAt_one_comp_glueHom
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    (ContinuousMap.IntervalGluing.evalAt B 1).comp
        (ContinuousMap.IntervalGluing.glueHom (B := B)) =
      (ContinuousMap.IntervalGluing.evalAt B 1).comp
        (NonUnitalCStarPullback.sndHom
          (ContinuousMap.IntervalGluing.evalAt B 1)
          (ContinuousMap.IntervalGluing.evalAt B 0)) := by
  apply NonUnitalStarAlgHom.ext
  intro p
  change ContinuousMap.IntervalGluing.glueHom p 1 = p.1.2 1
  exact ContinuousMap.IntervalGluing.glueHom_one p

private theorem comp_symm_eq_of_comp_eq
    {X : Type uX} {Y : Type uY} {Z : Type uZ}
    [NonUnitalCStarAlgebra X] [NonUnitalCStarAlgebra Y]
    [NonUnitalCStarAlgebra Z]
    (e : X ≃⋆ₐ[ℂ] Y) (p : Y →⋆ₙₐ[ℂ] Z) (q : X →⋆ₙₐ[ℂ] Z)
    (h : p.comp e.toNonUnitalStarAlgHom = q) :
    q.comp e.symm.toNonUnitalStarAlgHom = p := by
  apply NonUnitalStarAlgHom.ext
  intro y
  change q (e.symm y) = p y
  have hy := DFunLike.congr_fun h (e.symm y)
  change p (e (e.symm y)) = q (e.symm y) at hy
  exact hy.symm.trans (congrArg p (e.apply_symm_apply y))

private theorem map_fst_comp_matchingEquiv_symm (n : ℕ)
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    (IteratedAsymptoticAlgebra.map n
      (NonUnitalCStarPullback.fstHom
        (ContinuousMap.IntervalGluing.evalAt B 1)
        (ContinuousMap.IntervalGluing.evalAt B 0))).comp
        (iteratedMatchingPathsEquiv n B).symm.toNonUnitalStarAlgHom =
      NonUnitalCStarPullback.fstHom
        (endpointHom n 1 B) (endpointHom n 0 B) := by
  exact comp_symm_eq_of_comp_eq
    (iteratedMatchingPathsEquiv n B)
    (NonUnitalCStarPullback.fstHom
      (endpointHom n 1 B) (endpointHom n 0 B))
    (IteratedAsymptoticAlgebra.map n
      (NonUnitalCStarPullback.fstHom
        (ContinuousMap.IntervalGluing.evalAt B 1)
        (ContinuousMap.IntervalGluing.evalAt B 0)))
    (fstHom_comp_iteratedSplitPullbackEquiv n
      (ContinuousMap.IntervalGluing.evalAt B 1)
      (ContinuousMap.IntervalGluing.evalAt B 0)
      (ContinuousMap.IntervalGluing.constantHom B)
      (evalAt_zero_comp_constantHom B))

private theorem map_snd_comp_matchingEquiv_symm (n : ℕ)
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    (IteratedAsymptoticAlgebra.map n
      (NonUnitalCStarPullback.sndHom
        (ContinuousMap.IntervalGluing.evalAt B 1)
        (ContinuousMap.IntervalGluing.evalAt B 0))).comp
        (iteratedMatchingPathsEquiv n B).symm.toNonUnitalStarAlgHom =
      NonUnitalCStarPullback.sndHom
        (endpointHom n 1 B) (endpointHom n 0 B) := by
  exact comp_symm_eq_of_comp_eq
    (iteratedMatchingPathsEquiv n B)
    (NonUnitalCStarPullback.sndHom
      (endpointHom n 1 B) (endpointHom n 0 B))
    (IteratedAsymptoticAlgebra.map n
      (NonUnitalCStarPullback.sndHom
        (ContinuousMap.IntervalGluing.evalAt B 1)
        (ContinuousMap.IntervalGluing.evalAt B 0)))
    (sndHom_comp_iteratedSplitPullbackEquiv n
      (ContinuousMap.IntervalGluing.evalAt B 1)
      (ContinuousMap.IntervalGluing.evalAt B 0)
      (ContinuousMap.IntervalGluing.constantHom B)
      (evalAt_zero_comp_constantHom B))

/-- Evaluation at zero after iterated gluing is evaluation at zero on the
first matching path. -/
theorem endpointHom_zero_comp_glueHomN (n : ℕ)
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    (endpointHom n 0 B).comp (glueHomN n B) =
      (endpointHom n 0 B).comp
        (NonUnitalCStarPullback.fstHom
          (endpointHom n 1 B) (endpointHom n 0 B)) := by
  unfold endpointHom glueHomN
  rw [← NonUnitalStarAlgHom.comp_assoc,
    ← IteratedAsymptoticAlgebra.map_comp,
    evalAt_zero_comp_glueHom,
    IteratedAsymptoticAlgebra.map_comp,
    NonUnitalStarAlgHom.comp_assoc,
    map_fst_comp_matchingEquiv_symm]
  rfl

/-- Evaluation at one after iterated gluing is evaluation at one on the
second matching path. -/
theorem endpointHom_one_comp_glueHomN (n : ℕ)
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    (endpointHom n 1 B).comp (glueHomN n B) =
      (endpointHom n 1 B).comp
        (NonUnitalCStarPullback.sndHom
          (endpointHom n 1 B) (endpointHom n 0 B)) := by
  unfold endpointHom glueHomN
  rw [← NonUnitalStarAlgHom.comp_assoc,
    ← IteratedAsymptoticAlgebra.map_comp,
    evalAt_one_comp_glueHom,
    IteratedAsymptoticAlgebra.map_comp,
    NonUnitalStarAlgHom.comp_assoc,
    map_snd_comp_matchingEquiv_symm]
  rfl


end AsymptoticAlgebra
