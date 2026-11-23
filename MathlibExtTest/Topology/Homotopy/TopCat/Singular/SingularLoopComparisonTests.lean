/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularLoopComparison

/-!
# Singular based-path and loop comparison clients

These tests pin both endpoint equations, their interval orientations, the
literal based-path and loop fiber maps, the reflexive loop, and exact strict
naturality.  They exercise degrees zero and one and universes zero and one.

No inverse comparison, comparison isomorphism, weak-equivalence result,
weakly-pointed preservation theorem, or Q/S specialization is asserted.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory Simplicial Opposite
open scoped Simplicial Topology

universe u

namespace SSet

/-- The initial simplicial vertex is the topological interval endpoint zero. -/
example :
    SSet.stdSimplex.δ (1 : Fin 2) ≫ SSet.stdSimplex.toSSetObjI.{u} =
      SSet.const (TopCat.toSSetObj₀Equiv.symm (0 : TopCat.I.{u})) :=
  SSet.stdSimplex.δ_one_toSSetObjI

/-- The final simplicial vertex is the topological interval endpoint one. -/
example :
    SSet.stdSimplex.δ (0 : Fin 2) ≫ SSet.stdSimplex.toSSetObjI.{u} =
      SSet.const (TopCat.toSSetObj₀Equiv.symm (1 : TopCat.I.{u})) :=
  SSet.stdSimplex.δ_zero_toSSetObjI

/-- Exact initial-endpoint equation in a symbolic universe. -/
example (X : Type u) [TopologicalSpace X] :
    singularPathComparison X ≫
        (eval₀ : pathSpace (TopCat.toSSet.obj (TopCat.of X)) ⟶
          TopCat.toSSet.obj (TopCat.of X)) =
      TopCat.toSSet.map (TopCat.intervalContinuousMapEvalAt X 0) :=
  singularPathComparison_eval₀ X

/-- Exact final-endpoint equation in a symbolic universe. -/
example (X : Type u) [TopologicalSpace X] :
    singularPathComparison X ≫
        (eval₁ : pathSpace (TopCat.toSSet.obj (TopCat.of X)) ⟶
          TopCat.toSSet.obj (TopCat.of X)) =
      TopCat.toSSet.map (TopCat.intervalContinuousMapEvalAt X 1) :=
  singularPathComparison_eval₁ X

/-- Degree-zero component client for the initial endpoint. -/
example (X : Type u) [TopologicalSpace X] :
    (singularPathComparison X ≫
        (eval₀ : pathSpace (TopCat.toSSet.obj (TopCat.of X)) ⟶
          TopCat.toSSet.obj (TopCat.of X))).app
            (op (SimplexCategory.mk 0)) =
      (TopCat.toSSet.map
        (TopCat.intervalContinuousMapEvalAt X 0)).app
          (op (SimplexCategory.mk 0)) :=
  congrArg (fun q => q.app (op (SimplexCategory.mk 0)))
    (singularPathComparison_eval₀ X)

/-- Degree-one component client for the final endpoint. -/
example (X : Type u) [TopologicalSpace X] :
    (singularPathComparison X ≫
        (eval₁ : pathSpace (TopCat.toSSet.obj (TopCat.of X)) ⟶
          TopCat.toSSet.obj (TopCat.of X))).app
            (op (SimplexCategory.mk 1)) =
      (TopCat.toSSet.map
        (TopCat.intervalContinuousMapEvalAt X 1)).app
          (op (SimplexCategory.mk 1)) :=
  congrArg (fun q => q.app (op (SimplexCategory.mk 1)))
    (singularPathComparison_eval₁ X)

/-- The comparison restricts to the literal compact-open based-path subtype. -/
example (X : Type u) [TopologicalSpace X] (x : X) :
    TopCat.toSSet.obj
        (TopCat.of { gamma : C(unitInterval, X) // gamma 0 = x }) ⟶
      SSet.basedPath (TopCat.toSSet.obj (TopCat.of X))
        (TopCat.toSSetObj₀Equiv.symm x) :=
  singularBasedPathComparison X x

/-- Carrier equation for the based-path fiber lift. -/
example (X : Type u) [TopologicalSpace X] (x : X) :
    singularBasedPathComparison X x ≫
        basedPathIncl (TopCat.toSSet.obj (TopCat.of X))
          (TopCat.toSSetObj₀Equiv.symm x) =
      TopCat.toSSet.map
          (TopCat.ofHom
            { toFun := fun gamma :
                  { gamma : C(unitInterval, X) // gamma 0 = x } => gamma.1
              continuous_toFun := continuous_subtype_val }) ≫
        singularPathComparison X :=
  singularBasedPathComparison_ι X x

/-- The loop comparison lands in the two-endpoint simplicial fiber. -/
example (X : Type u) [TopologicalSpace X] (x : X) :
    TopCat.toSSet.obj (TopCat.of (LoopSpace X x)) ⟶
      SSet.loopSpace (TopCat.toSSet.obj (TopCat.of X))
        (TopCat.toSSetObj₀Equiv.symm x) :=
  singularLoopComparison X x

/-- Carrier equation for the loop fiber lift. -/
example (X : Type u) [TopologicalSpace X] (x : X) :
    singularLoopComparison X x ≫
        loopSpaceIncl (TopCat.toSSet.obj (TopCat.of X))
          (TopCat.toSSetObj₀Equiv.symm x) =
      TopCat.toSSet.map
          (TopCat.ofHom
            { toFun := fun gamma : LoopSpace X x =>
                ⟨gamma.toContinuousMap, gamma.source⟩
              continuous_toFun :=
                Continuous.subtype_mk continuous_induced_dom _ }) ≫
        singularBasedPathComparison X x :=
  singularLoopComparison_ι X x

/-- Degree-zero client of the loop comparison itself. -/
example (X : Type u) [TopologicalSpace X] (x : X) :
    (TopCat.toSSet.obj (TopCat.of (LoopSpace X x))).obj
          (op (SimplexCategory.mk 0)) →
        (SSet.loopSpace (TopCat.toSSet.obj (TopCat.of X))
          (TopCat.toSSetObj₀Equiv.symm x)).obj
            (op (SimplexCategory.mk 0)) :=
  (singularLoopComparison X x).app (op (SimplexCategory.mk 0))

/-- Degree-one client of the loop comparison itself. -/
example (X : Type u) [TopologicalSpace X] (x : X) :
    (TopCat.toSSet.obj (TopCat.of (LoopSpace X x))).obj
          (op (SimplexCategory.mk 1)) →
        (SSet.loopSpace (TopCat.toSSet.obj (TopCat.of X))
          (TopCat.toSSetObj₀Equiv.symm x)).obj
            (op (SimplexCategory.mk 1)) :=
  (singularLoopComparison X x).app (op (SimplexCategory.mk 1))

/-- The reflexive topological loop maps to the distinguished simplicial loop. -/
example (X : Type u) [TopologicalSpace X] (x : X) :
    (singularLoopComparison X x).app (op (SimplexCategory.mk 0))
        (TopCat.toSSetObj₀Equiv.symm (Path.refl x)) =
      Subcomplex.fiber.basePoint
        (basedPathPoint (TopCat.toSSet.obj (TopCat.of X))
          (TopCat.toSSetObj₀Equiv.symm x))
        (basedPathProj_basedPathPoint
          (TopCat.toSSet.obj (TopCat.of X))
          (TopCat.toSSetObj₀Equiv.symm x)) :=
  singularLoopComparison_refl X x

/-- Exact strict naturality for an arbitrary continuous map. -/
example {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    TopCat.toSSet.map
          (TopCat.ofHom (ContinuousMap.strictLoopMap f x)) ≫
        singularLoopComparison Y (f x) =
      singularLoopComparison X x ≫
        SSet.loopSpaceMap
          (x := TopCat.toSSetObj₀Equiv.symm x)
          (y := TopCat.toSSetObj₀Equiv.symm (f x))
          (TopCat.toSSet.map (TopCat.ofHom f))
          (by rfl) :=
  singularLoopComparison_naturality f x

/-- Identity is a direct specialization of arbitrary-map strict naturality. -/
example (X : Type u) [TopologicalSpace X] (x : X) :
    TopCat.toSSet.map
          (TopCat.ofHom
            (ContinuousMap.strictLoopMap (ContinuousMap.id X) x)) ≫
        singularLoopComparison X x =
      singularLoopComparison X x ≫
        SSet.loopSpaceMap
          (x := TopCat.toSSetObj₀Equiv.symm x)
          (y := TopCat.toSSetObj₀Equiv.symm x)
          (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.id X)))
          (by rfl) :=
  singularLoopComparison_naturality (ContinuousMap.id X) x

/-- Explicit universe-zero based-path client. -/
example (X : Type) [TopologicalSpace X] (x : X) :
    TopCat.toSSet.obj
        (TopCat.of { gamma : C(unitInterval, X) // gamma 0 = x }) ⟶
      SSet.basedPath (TopCat.toSSet.obj (TopCat.of X))
        (TopCat.toSSetObj₀Equiv.symm x) :=
  singularBasedPathComparison X x

/-- Explicit universe-zero loop client. -/
example (X : Type) [TopologicalSpace X] (x : X) :
    TopCat.toSSet.obj (TopCat.of (LoopSpace X x)) ⟶
      SSet.loopSpace (TopCat.toSSet.obj (TopCat.of X))
        (TopCat.toSSetObj₀Equiv.symm x) :=
  singularLoopComparison X x

/-- Explicit universe-one based-path client. -/
example (X : Type 1) [TopologicalSpace X] (x : X) :
    TopCat.toSSet.obj
        (TopCat.of { gamma : C(unitInterval, X) // gamma 0 = x }) ⟶
      SSet.basedPath (TopCat.toSSet.obj (TopCat.of X))
        (TopCat.toSSetObj₀Equiv.symm x) :=
  singularBasedPathComparison X x

/-- Explicit universe-one loop client. -/
example (X : Type 1) [TopologicalSpace X] (x : X) :
    TopCat.toSSet.obj (TopCat.of (LoopSpace X x)) ⟶
      SSet.loopSpace (TopCat.toSSet.obj (TopCat.of X))
        (TopCat.toSSetObj₀Equiv.symm x) :=
  singularLoopComparison X x

#guard_msgs (error, substring := true) in
#check SSet.singularLoopIso

#guard_msgs (error, substring := true) in
#check SSet.singularLoopComparisonInv

#guard_msgs (error, substring := true) in
#check SSet.singularLoopComparison_mem_W

#guard_msgs (error, substring := true) in
#check SSet.weaklyPointedSingularLoopComparison

#guard_msgs (error, substring := true) in
#check SSet.singularLoopComparison_Q

#guard_msgs (error, substring := true) in
#check SSet.intervalBasedPathIncl

#guard_msgs (error, substring := true) in
#check SSet.loopToIntervalBasedPath

#guard_msgs (error, substring := true) in
#synth TopCat.toSSet.{0}.Braided

#print axioms TopCat.intervalContinuousMapEvalAt
#print axioms TopCat.intervalContinuousMapEvalAt_apply
#print axioms SSet.singularPathComparison_eval₀
#print axioms SSet.singularPathComparison_eval₁
#print axioms SSet.singularBasedPathComparison
#print axioms SSet.singularBasedPathComparison_ι
#print axioms SSet.singularBasedPathComparison_ι_assoc
#print axioms SSet.singularLoopComparison
#print axioms SSet.singularLoopComparison_ι
#print axioms SSet.singularLoopComparison_ι_assoc
#print axioms SSet.singularLoopComparison_refl
#print axioms SSet.singularLoopComparison_naturality

end SSet
