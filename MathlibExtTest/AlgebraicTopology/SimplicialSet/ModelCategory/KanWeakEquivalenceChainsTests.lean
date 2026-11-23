/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanWeakEquivalenceChains
import MathlibExt.AlgebraicTopology.SimplicialSet.NormalizedFunctor
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Data.Matrix.Mul

/-!
# Tests for chain invariance of Kan weak equivalences

The matrix covers the exact generic signatures, degree zero, identities,
isomorphisms, empty and disconnected Kan complexes, independent universes,
noncommutative coefficients, and reuse of coefficient naturality.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex Limits
open scoped Simplicial

universe w v u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory
namespace KanWeakEquivalenceChainsTests

section PublicContract

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCoproducts.{w} C] [CategoryWithHomology C]
  {X Y : SSet.{w}} {f : X ⟶ Y} (A : C)

example (hf : SSet.KanComplex.W f) :
    QuasiIso (SSet.chainComplexMap f A) :=
  hf.quasiIso_chainComplexMap A

example (hf : SSet.KanComplex.W f) :
    QuasiIso (SSet.normalizedChainComplexMap f A) :=
  hf.quasiIso_normalizedChainComplexMap A

/-- The theorem includes degree zero, rather than only positive homotopy
groups. -/
example (hf : SSet.KanComplex.W f) :
    QuasiIsoAt (SSet.chainComplexMap f A) 0 := by
  let _ : QuasiIso (SSet.chainComplexMap f A) :=
    hf.quasiIso_chainComplexMap A
  infer_instance

end PublicContract

section IdentityAndIsomorphism

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCoproducts.{w} C] [CategoryWithHomology C]

example (X : SSet.{w}) [SSet.KanComplex X] (A : C) :
    QuasiIso (SSet.chainComplexMap (𝟙 X) A) :=
  SSet.KanComplex.W.quasiIso_chainComplexMap SSet.KanComplex.W.id A

example {X Y : SSet.{w}} [SSet.KanComplex X] [SSet.KanComplex Y]
    (e : X ≅ Y) (A : C) :
    QuasiIso (SSet.normalizedChainComplexMap e.hom A) :=
  (SSet.KanComplex.W.ofIso e).quasiIso_normalizedChainComplexMap A

end IdentityAndIsomorphism

section DeltaZero

private theorem deltaZeroKanComplex :
    SSet.KanComplex (Δ[0] : SSet.{w}) := by
  rw [SSet.KanComplex.iff]
  intro n i _ _
  refine ⟨SSet.stdSimplex.isTerminalObj₀.from _, ?_⟩
  intro j hj
  exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCoproducts.{w} C] [CategoryWithHomology C]

example (A : C) :
    QuasiIsoAt
      (SSet.normalizedChainComplexMap (𝟙 (Δ[0] : SSet.{w})) A) 0 := by
  let _ : SSet.KanComplex (Δ[0] : SSet.{w}) := deltaZeroKanComplex
  let _ : QuasiIso
      (SSet.normalizedChainComplexMap (𝟙 (Δ[0] : SSet.{w})) A) :=
    SSet.KanComplex.W.quasiIso_normalizedChainComplexMap
      SSet.KanComplex.W.id A
  infer_instance

end DeltaZero

section EmptyAndDisconnected

private noncomputable abbrev emptySingular : SSet.{1} :=
  TopCat.toSSet.obj (TopCat.of (ULift.{1} Empty))

private noncomputable abbrev twoPointSingular : SSet.{1} :=
  TopCat.toSSet.obj (TopCat.of (ULift.{1} (Fin 2)))

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCoproducts.{1} C] [CategoryWithHomology C]

example (A : C) :
    QuasiIso (SSet.chainComplexMap (𝟙 emptySingular) A) := by
  let _ : SSet.KanComplex emptySingular := TopCat.toSSet_obj_kanComplex _
  exact SSet.KanComplex.W.quasiIso_chainComplexMap SSet.KanComplex.W.id A

example (A : C) :
    QuasiIso
      (SSet.normalizedChainComplexMap (𝟙 twoPointSingular) A) := by
  let _ : SSet.KanComplex twoPointSingular := TopCat.toSSet_obj_kanComplex _
  exact SSet.KanComplex.W.quasiIso_normalizedChainComplexMap
    SSet.KanComplex.W.id A

end EmptyAndDisconnected

section Coefficients

private abbrev MatrixRing := Matrix (Fin 2) (Fin 2) ℤ

example : True := by
  fail_if_success let _ : CommRing MatrixRing := inferInstance
  trivial

/-- Zero coefficients are supported, but the theorem still consumes the Kan
weak-equivalence premise and gives no converse. -/
example {R : Type u} [Ring R] {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : SSet.KanComplex.W f) :
    QuasiIso
      (SSet.normalizedChainComplexMap f (⊥_ (ModuleCat.{u} R))) :=
  hf.quasiIso_normalizedChainComplexMap (⊥_ (ModuleCat.{u} R))

example {X Y : SSet.{0}} {f : X ⟶ Y} (hf : SSet.KanComplex.W f) :
    QuasiIso
      (SSet.chainComplexMap f (ModuleCat.of MatrixRing MatrixRing)) :=
  hf.quasiIso_chainComplexMap (ModuleCat.of MatrixRing MatrixRing)

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCoproducts.{w} C]

/-- The coefficient-object naturality square is the canonical interface. -/
example {A B : C} (a : A ⟶ B) {X Y : SSet.{w}} (f : X ⟶ Y) :
    SSet.chainComplexMap f A ≫
        ((SSet.chainComplexFunctor C).map a).app Y =
      ((SSet.chainComplexFunctor C).map a).app X ≫
        SSet.chainComplexMap f B :=
  ((SSet.chainComplexFunctor C).map a).naturality f

example {A B : C} (a : A ⟶ B) {X Y : SSet.{w}} (f : X ⟶ Y) :
    SSet.normalizedChainComplexMap f A ≫
        ((SSet.normalizedChainComplexFunctor (C := C)).map a).app Y =
      ((SSet.normalizedChainComplexFunctor (C := C)).map a).app X ≫
        SSet.normalizedChainComplexMap f B :=
  ((SSet.normalizedChainComplexFunctor (C := C)).map a).naturality f

end Coefficients

section ExplicitUniverses

example {C : Type 1} [Category.{1} C] [Preadditive C]
    [HasCoproducts.{1} C] [CategoryWithHomology C]
    {X Y : SSet.{1}} {f : X ⟶ Y} (hf : SSet.KanComplex.W f) (A : C) :
    QuasiIso (SSet.normalizedChainComplexMap f A) :=
  hf.quasiIso_normalizedChainComplexMap A

example {C : Type} [Category C] [Preadditive C]
    [HasCoproducts.{0} C] [CategoryWithHomology C]
    {X Y : SSet.{0}} {f : X ⟶ Y} (hf : SSet.KanComplex.W f) (A : C) :
    QuasiIso (SSet.chainComplexMap f A) :=
  hf.quasiIso_chainComplexMap A

end ExplicitUniverses

#print axioms SSet.KanComplex.W.quasiIso_chainComplexMap
#print axioms SSet.KanComplex.W.quasiIso_normalizedChainComplexMap

end KanWeakEquivalenceChainsTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory
