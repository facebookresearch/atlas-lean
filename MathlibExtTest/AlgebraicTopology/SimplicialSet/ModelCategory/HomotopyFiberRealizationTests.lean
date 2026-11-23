/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyFiberRealization

/-!
# Simplicial homotopy-fiber realization tests

These clients pin the literal endpoint-pair carrier, the realized full-path
comparison, its exact fibration premise, universe polymorphism, and the
opposite-endpoint strict-pullback falsifier.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Simplicial
  MorphismProperty
open scoped Simplicial TopCat.modelCategory

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory

section ScopeOffBefore

#guard_msgs (error, substring := true) in
#synth ModelCategory SSet.{u}

#guard_msgs (error, substring := true) in
#synth IsRightProper SSet.{u}

end ScopeOffBefore

section SymbolicUniverse

open scoped SSet.modelCategoryQuillen

variable {X Y : SSet.{u}} (f : X ⟶ Y)
  (y : Y.obj (Opposite.op (SimplexCategory.mk 0)))

example : SSet.toTop.obj (SSet.pathSpace Y) ⟶
    TopCat.pathObject (SSet.toTop.obj Y) :=
  SSet.pathSpaceRealizationComparison Y

example : SSet.pathSpaceRealizationComparison Y ≫
      TopCat.pathEvalZero (SSet.toTop.obj Y) =
    SSet.toTop.map (SSet.eval₀ : SSet.pathSpace Y ⟶ Y) :=
  SSet.pathSpaceRealizationComparison_evalZero Y

example : SSet.pathSpaceRealizationComparison Y ≫
      TopCat.pathEvalOne (SSet.toTop.obj Y) =
    SSet.toTop.map (SSet.eval₁ : SSet.pathSpace Y ⟶ Y) :=
  SSet.pathSpaceRealizationComparison_evalOne Y

example : SSet.toTop.map (SSet.constPath Y) ≫
      SSet.pathSpaceRealizationComparison Y =
    TopCat.pathConstant (SSet.toTop.obj Y) :=
  SSet.constPath_pathSpaceRealizationComparison Y

example : SSet.{u} := SSet.pathHomotopyFiber f y

example : SSet.pathHomotopyFiber f y ⟶ X :=
  SSet.pathHomotopyFiberToTotal f y

example : SSet.pathHomotopyFiber f y ⟶ SSet.pathSpace Y :=
  SSet.pathHomotopyFiberPath f y

example : SSet.pathHomotopyFiberPath f y ≫ SSet.eval₀ =
    SSet.pathHomotopyFiberToTotal f y ≫ f :=
  SSet.pathHomotopyFiberPath_evalZero f y

example : SSet.pathHomotopyFiberPath f y ≫ SSet.eval₁ =
    SSet.const (X := SSet.pathHomotopyFiber f y) y :=
  SSet.pathHomotopyFiberPath_evalOne f y

example : SSet.toTop.obj (SSet.pathHomotopyFiber f y) ⟶
    TopCat.homotopyFiber (SSet.toTop.map f) (SSet.realizedVertex y) :=
  SSet.pathHomotopyFiberRealizationComparison f y

example : SSet.pathHomotopyFiberRealizationComparison f y ≫
      TopCat.homotopyFiberToTotal
        (SSet.toTop.map f) (SSet.realizedVertex y) =
    SSet.toTop.map (SSet.pathHomotopyFiberToTotal f y) :=
  SSet.pathHomotopyFiberRealizationComparison_toTotal f y

example : SSet.pathHomotopyFiberRealizationComparison f y ≫
      TopCat.homotopyFiberPath
        (SSet.toTop.map f) (SSet.realizedVertex y) =
    SSet.toTop.map (SSet.pathHomotopyFiberPath f y) ≫
      SSet.pathSpaceRealizationComparison Y :=
  SSet.pathHomotopyFiberRealizationComparison_path f y

example [Fibration f] : TopCat.weakHomotopyEquivalences
    (SSet.pathHomotopyFiberRealizationComparison f y) :=
  SSet.pathHomotopyFiberRealizationComparison_mem_weakHomotopyEquivalences f y

end SymbolicUniverse

section UniverseOne

open scoped SSet.modelCategoryQuillen

variable {X Y : SSet.{1}} (f : X ⟶ Y)
  (y : Y.obj (Opposite.op (SimplexCategory.mk 0)))

example : SSet.toTop.obj (SSet.pathSpace Y) ⟶
    TopCat.pathObject (SSet.toTop.obj Y) :=
  SSet.pathSpaceRealizationComparison Y

example : SSet.pathSpaceRealizationComparison Y ≫
      TopCat.pathEvalZero (SSet.toTop.obj Y) = SSet.toTop.map SSet.eval₀ :=
  SSet.pathSpaceRealizationComparison_evalZero Y

example : SSet.pathSpaceRealizationComparison Y ≫
      TopCat.pathEvalOne (SSet.toTop.obj Y) = SSet.toTop.map SSet.eval₁ :=
  SSet.pathSpaceRealizationComparison_evalOne Y

example : SSet.toTop.map (SSet.constPath Y) ≫
      SSet.pathSpaceRealizationComparison Y =
    TopCat.pathConstant (SSet.toTop.obj Y) :=
  SSet.constPath_pathSpaceRealizationComparison Y

example : SSet.{1} := SSet.pathHomotopyFiber f y
example : SSet.pathHomotopyFiber f y ⟶ X :=
  SSet.pathHomotopyFiberToTotal f y
example : SSet.pathHomotopyFiber f y ⟶ SSet.pathSpace Y :=
  SSet.pathHomotopyFiberPath f y

example : SSet.pathHomotopyFiberPath f y ≫ SSet.eval₀ =
    SSet.pathHomotopyFiberToTotal f y ≫ f :=
  SSet.pathHomotopyFiberPath_evalZero f y

example : SSet.pathHomotopyFiberPath f y ≫ SSet.eval₁ =
    SSet.const y := SSet.pathHomotopyFiberPath_evalOne f y

example : SSet.toTop.obj (SSet.pathHomotopyFiber f y) ⟶
    TopCat.homotopyFiber (SSet.toTop.map f) (SSet.realizedVertex y) :=
  SSet.pathHomotopyFiberRealizationComparison f y

example : SSet.pathHomotopyFiberRealizationComparison f y ≫
      TopCat.homotopyFiberToTotal
        (SSet.toTop.map f) (SSet.realizedVertex y) =
    SSet.toTop.map (SSet.pathHomotopyFiberToTotal f y) :=
  SSet.pathHomotopyFiberRealizationComparison_toTotal f y

example : SSet.pathHomotopyFiberRealizationComparison f y ≫
      TopCat.homotopyFiberPath
        (SSet.toTop.map f) (SSet.realizedVertex y) =
    SSet.toTop.map (SSet.pathHomotopyFiberPath f y) ≫
      SSet.pathSpaceRealizationComparison Y :=
  SSet.pathHomotopyFiberRealizationComparison_path f y

example [Fibration f] : TopCat.weakHomotopyEquivalences
    (SSet.pathHomotopyFiberRealizationComparison f y) :=
  SSet.pathHomotopyFiberRealizationComparison_mem_weakHomotopyEquivalences f y

end UniverseOne

section UniverseZero

open scoped SSet.modelCategoryQuillen

variable {X Y : SSet.{0}} (f : X ⟶ Y)
  (y : Y.obj (Opposite.op (SimplexCategory.mk 0)))

example : SSet.toTop.obj (SSet.pathSpace Y) ⟶
    TopCat.pathObject (SSet.toTop.obj Y) :=
  SSet.pathSpaceRealizationComparison Y

example : SSet.pathSpaceRealizationComparison Y ≫
      TopCat.pathEvalZero (SSet.toTop.obj Y) = SSet.toTop.map SSet.eval₀ :=
  SSet.pathSpaceRealizationComparison_evalZero Y

example : SSet.pathSpaceRealizationComparison Y ≫
      TopCat.pathEvalOne (SSet.toTop.obj Y) = SSet.toTop.map SSet.eval₁ :=
  SSet.pathSpaceRealizationComparison_evalOne Y

example : SSet.toTop.map (SSet.constPath Y) ≫
      SSet.pathSpaceRealizationComparison Y =
    TopCat.pathConstant (SSet.toTop.obj Y) :=
  SSet.constPath_pathSpaceRealizationComparison Y

example : SSet.{0} := SSet.pathHomotopyFiber f y
example : SSet.pathHomotopyFiber f y ⟶ X :=
  SSet.pathHomotopyFiberToTotal f y
example : SSet.pathHomotopyFiber f y ⟶ SSet.pathSpace Y :=
  SSet.pathHomotopyFiberPath f y

example : SSet.pathHomotopyFiberPath f y ≫ SSet.eval₀ =
    SSet.pathHomotopyFiberToTotal f y ≫ f :=
  SSet.pathHomotopyFiberPath_evalZero f y

example : SSet.pathHomotopyFiberPath f y ≫ SSet.eval₁ =
    SSet.const y := SSet.pathHomotopyFiberPath_evalOne f y

example : SSet.toTop.obj (SSet.pathHomotopyFiber f y) ⟶
    TopCat.homotopyFiber (SSet.toTop.map f) (SSet.realizedVertex y) :=
  SSet.pathHomotopyFiberRealizationComparison f y

example : SSet.pathHomotopyFiberRealizationComparison f y ≫
      TopCat.homotopyFiberToTotal
        (SSet.toTop.map f) (SSet.realizedVertex y) =
    SSet.toTop.map (SSet.pathHomotopyFiberToTotal f y) :=
  SSet.pathHomotopyFiberRealizationComparison_toTotal f y

example : SSet.pathHomotopyFiberRealizationComparison f y ≫
      TopCat.homotopyFiberPath
        (SSet.toTop.map f) (SSet.realizedVertex y) =
    SSet.toTop.map (SSet.pathHomotopyFiberPath f y) ≫
      SSet.pathSpaceRealizationComparison Y :=
  SSet.pathHomotopyFiberRealizationComparison_path f y

example [Fibration f] : TopCat.weakHomotopyEquivalences
    (SSet.pathHomotopyFiberRealizationComparison f y) :=
  SSet.pathHomotopyFiberRealizationComparison_mem_weakHomotopyEquivalences f y

end UniverseZero

section IdentityAndTerminal

open scoped SSet.modelCategoryQuillen

example : TopCat.weakHomotopyEquivalences
    (SSet.pathHomotopyFiberRealizationComparison
      (𝟙 (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{u}))
      (SSet.stdSimplex.obj₀Equiv.{u}.symm 0)) :=
  SSet.pathHomotopyFiberRealizationComparison_mem_weakHomotopyEquivalences
    (𝟙 (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{u}))
    (SSet.stdSimplex.obj₀Equiv.{u}.symm 0)

example : True := by
  fail_if_success
    let _ : SSet.KanComplex
      (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{u}) := inferInstance
  trivial

example : TopCat.weakHomotopyEquivalences
    (SSet.pathHomotopyFiberRealizationComparison
      (𝟙 (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{u}))
      (SSet.stdSimplex.obj₀Equiv.{u}.symm 0)) :=
  SSet.pathHomotopyFiberRealizationComparison_mem_weakHomotopyEquivalences
    (𝟙 (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{u}))
    (SSet.stdSimplex.obj₀Equiv.{u}.symm 0)

end IdentityAndTerminal

section WeakBaseChange

open scoped SSet.modelCategoryQuillen

variable {A C A' C' : SSet.{u}} {q : A ⟶ C} {q' : A' ⟶ C'}
variable (l : A ⟶ A') (h : C ⟶ C') (hq : q ≫ h = l ≫ q')
variable {c : C _⦋0⦌} {c' : C' _⦋0⦌} (hc : h.app _ c = c')
variable [SSet.KanComplex C] [SSet.KanComplex C']
variable [IsRightProper SSet.{u}]
variable [HasFunctorialFactorization
  (trivialCofibrations SSet.{u}) (fibrations SSet.{u})]
variable (hl : SSet.realizationWeakEquivalences l)
variable (hh : SSet.realizationWeakEquivalences h)

example : SSet.realizationWeakEquivalences
    (SSet.pathHomotopyFiberMap l h hq hc) :=
  SSet.pathHomotopyFiberMap_mem_realizationWeakEquivalences
    l h hq hc hl hh

example : SSet.realizationWeakEquivalences
    (SSet.pathHomotopyFiberMap
      (f := q) (f' := q) (𝟙 A) (𝟙 C) (by simp)
      (b := c) (b' := c) rfl) := by
  apply SSet.pathHomotopyFiberMap_mem_realizationWeakEquivalences
  · exact SSet.realizationWeakEquivalences.id_mem A
  · exact SSet.realizationWeakEquivalences.id_mem C

#check @SSet.pathHomotopyFiberMap_mem_realizationWeakEquivalences.{1}
#check @SSet.pathHomotopyFiberMap_mem_realizationWeakEquivalences.{0}

end WeakBaseChange

section MissingKanSource

open scoped SSet.modelCategoryQuillen
variable {A C A' C' : SSet.{u}} {q : A ⟶ C} {q' : A' ⟶ C'}
variable (l : A ⟶ A') (h : C ⟶ C') (hq : q ≫ h = l ≫ q')
variable {c : C _⦋0⦌} {c' : C' _⦋0⦌} (hc : h.app _ c = c')
variable [SSet.KanComplex C'] [IsRightProper SSet.{u}]
variable [HasFunctorialFactorization
  (trivialCofibrations SSet.{u}) (fibrations SSet.{u})]
variable (hl : SSet.realizationWeakEquivalences l)
variable (hh : SSet.realizationWeakEquivalences h)

#guard_msgs (error, substring := true) in
example : SSet.realizationWeakEquivalences
    (SSet.pathHomotopyFiberMap l h hq hc) :=
  SSet.pathHomotopyFiberMap_mem_realizationWeakEquivalences
    l h hq hc hl hh

end MissingKanSource

section MissingKanTarget

open scoped SSet.modelCategoryQuillen
variable {A C A' C' : SSet.{u}} {q : A ⟶ C} {q' : A' ⟶ C'}
variable (l : A ⟶ A') (h : C ⟶ C') (hq : q ≫ h = l ≫ q')
variable {c : C _⦋0⦌} {c' : C' _⦋0⦌} (hc : h.app _ c = c')
variable [SSet.KanComplex C] [IsRightProper SSet.{u}]
variable [HasFunctorialFactorization
  (trivialCofibrations SSet.{u}) (fibrations SSet.{u})]
variable (hl : SSet.realizationWeakEquivalences l)
variable (hh : SSet.realizationWeakEquivalences h)

#guard_msgs (error, substring := true) in
example : SSet.realizationWeakEquivalences
    (SSet.pathHomotopyFiberMap l h hq hc) :=
  SSet.pathHomotopyFiberMap_mem_realizationWeakEquivalences
    l h hq hc hl hh

end MissingKanTarget

section MissingRightProper

open scoped SSet.modelCategoryQuillen
variable {A C A' C' : SSet.{u}} {q : A ⟶ C} {q' : A' ⟶ C'}
variable (l : A ⟶ A') (h : C ⟶ C') (hq : q ≫ h = l ≫ q')
variable {c : C _⦋0⦌} {c' : C' _⦋0⦌} (hc : h.app _ c = c')
variable [SSet.KanComplex C] [SSet.KanComplex C']
variable [HasFunctorialFactorization
  (trivialCofibrations SSet.{u}) (fibrations SSet.{u})]
variable (hl : SSet.realizationWeakEquivalences l)
variable (hh : SSet.realizationWeakEquivalences h)

#guard_msgs (error, substring := true) in
example : SSet.realizationWeakEquivalences
    (SSet.pathHomotopyFiberMap l h hq hc) :=
  SSet.pathHomotopyFiberMap_mem_realizationWeakEquivalences
    l h hq hc hl hh

end MissingRightProper

section MissingFactorization

open scoped SSet.modelCategoryQuillen
variable {A C A' C' : SSet.{u}} {q : A ⟶ C} {q' : A' ⟶ C'}
variable (l : A ⟶ A') (h : C ⟶ C') (hq : q ≫ h = l ≫ q')
variable {c : C _⦋0⦌} {c' : C' _⦋0⦌} (hc : h.app _ c = c')
variable [SSet.KanComplex C] [SSet.KanComplex C']
variable [IsRightProper SSet.{u}]
variable (hl : SSet.realizationWeakEquivalences l)
variable (hh : SSet.realizationWeakEquivalences h)

#guard_msgs (error, substring := true) in
example : SSet.realizationWeakEquivalences
    (SSet.pathHomotopyFiberMap l h hq hc) :=
  SSet.pathHomotopyFiberMap_mem_realizationWeakEquivalences
    l h hq hc hl hh

end MissingFactorization

section MissingSquare

open scoped SSet.modelCategoryQuillen
variable {A C A' C' : SSet.{u}} {q : A ⟶ C} {q' : A' ⟶ C'}
variable (l : A ⟶ A') (h : C ⟶ C')
variable {c : C _⦋0⦌} {c' : C' _⦋0⦌} (hc : h.app _ c = c')
variable [SSet.KanComplex C] [SSet.KanComplex C']
variable [IsRightProper SSet.{u}]
variable [HasFunctorialFactorization
  (trivialCofibrations SSet.{u}) (fibrations SSet.{u})]
variable (hl : SSet.realizationWeakEquivalences l)
variable (hh : SSet.realizationWeakEquivalences h)

#guard_msgs (error, substring := true) in
example : True := by
  have _ := SSet.pathHomotopyFiberMap_mem_realizationWeakEquivalences
    (q := q) (q' := q') l h (hc := hc) hl hh
  trivial

end MissingSquare

section MissingVertex

open scoped SSet.modelCategoryQuillen
variable {A C A' C' : SSet.{u}} {q : A ⟶ C} {q' : A' ⟶ C'}
variable (l : A ⟶ A') (h : C ⟶ C') (hq : q ≫ h = l ≫ q')
variable {c : C _⦋0⦌} {c' : C' _⦋0⦌}
variable [SSet.KanComplex C] [SSet.KanComplex C']
variable [IsRightProper SSet.{u}]
variable [HasFunctorialFactorization
  (trivialCofibrations SSet.{u}) (fibrations SSet.{u})]
variable (hl : SSet.realizationWeakEquivalences l)
variable (hh : SSet.realizationWeakEquivalences h)

#guard_msgs (error, substring := true) in
example : True := by
  have _ := SSet.pathHomotopyFiberMap_mem_realizationWeakEquivalences
    l h hq (c := c) (c' := c') (hl := hl) (hh := hh)
  trivial

end MissingVertex

section MissingWeakTotal

open scoped SSet.modelCategoryQuillen
variable {A C A' C' : SSet.{u}} {q : A ⟶ C} {q' : A' ⟶ C'}
variable (l : A ⟶ A') (h : C ⟶ C') (hq : q ≫ h = l ≫ q')
variable {c : C _⦋0⦌} {c' : C' _⦋0⦌} (hc : h.app _ c = c')
variable [SSet.KanComplex C] [SSet.KanComplex C']
variable [IsRightProper SSet.{u}]
variable [HasFunctorialFactorization
  (trivialCofibrations SSet.{u}) (fibrations SSet.{u})]
variable (hh : SSet.realizationWeakEquivalences h)

#guard_msgs (error, substring := true) in
example : SSet.realizationWeakEquivalences
    (SSet.pathHomotopyFiberMap l h hq hc) := by
  exact SSet.pathHomotopyFiberMap_mem_realizationWeakEquivalences
    l h hq hc (hh := hh)

end MissingWeakTotal

section MissingWeakBase

open scoped SSet.modelCategoryQuillen
variable {A C A' C' : SSet.{u}} {q : A ⟶ C} {q' : A' ⟶ C'}
variable (l : A ⟶ A') (h : C ⟶ C') (hq : q ≫ h = l ≫ q')
variable {c : C _⦋0⦌} {c' : C' _⦋0⦌} (hc : h.app _ c = c')
variable [SSet.KanComplex C] [SSet.KanComplex C']
variable [IsRightProper SSet.{u}]
variable [HasFunctorialFactorization
  (trivialCofibrations SSet.{u}) (fibrations SSet.{u})]
variable (hl : SSet.realizationWeakEquivalences l)

#guard_msgs (error, substring := true) in
example : SSet.realizationWeakEquivalences
    (SSet.pathHomotopyFiberMap l h hq hc) := by
  exact SSet.pathHomotopyFiberMap_mem_realizationWeakEquivalences
    l h hq hc hl

end MissingWeakBase

section NonidentityWeakBaseChange

open scoped SSet.modelCategoryQuillen

private abbrev intervalSingSource : SSet.{0} :=
  TopCat.toSSet.obj TopCat.I.{0}

private abbrev intervalSingTarget : SSet.{0} :=
  TopCat.toSSet.obj (TopCat.of unitInterval)

private noncomputable def intervalSingIso :
    intervalSingSource ≅ intervalSingTarget :=
  TopCat.toSSet.mapIso
    (TopCat.isoOfHomeo TopCat.I.homeomorph)

private noncomputable def intervalSingSourceZero :
    intervalSingSource _⦋0⦌ :=
  TopCat.toSSetObj₀Equiv.symm (0 : TopCat.I.{0})

variable [IsRightProper SSet.{0}]
variable [HasFunctorialFactorization
  (trivialCofibrations SSet.{0}) (fibrations SSet.{0})]

example : SSet.realizationWeakEquivalences
    (SSet.pathHomotopyFiberMap
      (f := 𝟙 intervalSingSource)
      (f' := 𝟙 intervalSingTarget)
      (intervalSingIso).hom (intervalSingIso).hom (by simp)
      (b := intervalSingSourceZero)
      (b' := (intervalSingIso).hom.app _ intervalSingSourceZero)
      rfl) := by
  let _ : SSet.KanComplex intervalSingSource :=
    TopCat.toSSet_obj_kanComplex TopCat.I.{0}
  let _ : SSet.KanComplex intervalSingTarget :=
    TopCat.toSSet_obj_kanComplex (TopCat.of unitInterval : TopCat.{0})
  apply SSet.pathHomotopyFiberMap_mem_realizationWeakEquivalences
  · exact SSet.realizationWeakEquivalences.of_isIso _
  · exact SSet.realizationWeakEquivalences.of_isIso _

end NonidentityWeakBaseChange

section ScopeTeardown

#guard_msgs (error, substring := true) in
#synth ModelCategory SSet.{u}

#guard_msgs (error, substring := true) in
#synth IsRightProper SSet.{u}

end ScopeTeardown

section OppositeEndpoints

private def intervalZero : TopCat.of PUnit.{u + 1} ⟶ TopCat.I.{u} :=
  TopCat.const 0

private def intervalOne : TopCat.of PUnit.{u + 1} ⟶ TopCat.I.{u} :=
  TopCat.const 1

example : IsEmpty ↑(pullback intervalZero.{u} intervalOne.{u} : TopCat.{u}) := by
  constructor
  intro z
  have h := ConcreteCategory.congr_hom
    (pullback.condition :
      pullback.fst intervalZero.{u} intervalOne.{u} ≫ intervalZero.{u} =
        pullback.snd intervalZero.{u} intervalOne.{u} ≫ intervalOne.{u}) z
  change (0 : TopCat.I.{u}) = 1 at h
  have hreal : (0 : ℝ) = 1 :=
    congrArg (fun t : TopCat.I.{u} =>
      ((TopCat.I.homeomorph t : Set.Icc (0 : ℝ) 1) : ℝ)) h
  exact zero_ne_one hreal

example : Nonempty
    (TopCat.homotopyFiber intervalZero.{u} (1 : TopCat.I.{u})) := by
  let q : TopCat.of PUnit.{u + 1} ⟶
      TopCat.homotopyFiber intervalZero.{u} (1 : TopCat.I.{u}) :=
    pullback.lift
      (Limits.prod.lift (𝟙 _) (𝟙 _))
      (TopCat.const (ContinuousMap.id TopCat.I.{u}))
      (by
        apply Limits.prod.hom_ext
        · simp [TopCat.pathEndpoints]
          apply ConcreteCategory.hom_ext
          intro z
          rfl
        · simp [TopCat.pathEndpoints]
          apply ConcreteCategory.hom_ext
          intro z
          rfl)
  exact ⟨q PUnit.unit⟩

example : True := by
  fail_if_success
    have _ : Fibration intervalZero.{u} := inferInstance
  trivial

end OppositeEndpoints

section Falsifiers

variable {X Y : SSet.{u}} (f : X ⟶ Y)
  (y : Y.obj (Opposite.op (SimplexCategory.mk 0)))

example : True := by
  fail_if_success
    exact SSet.pathHomotopyFiberRealizationComparison_mem_weakHomotopyEquivalences f y
  fail_if_success
    let _ : Fibration (SSet.eval₀ : SSet.pathSpace Y ⟶ Y) := inferInstance
  fail_if_success
    let _ : Fibration (SSet.eval₁ : SSet.pathSpace Y ⟶ Y) := inferInstance
  fail_if_success
    let _ := SSet.pathEndpointPair
  fail_if_success
    let _ := SSet.constPath_eq_curry_snd
  fail_if_success
    let _ := SSet.pathSpaceEvaluationHomotopy
  fail_if_success
    let _ := SSet.baseChangeEndpointPair
  fail_if_success
    let _ := SSet.pathFiberCospan
  fail_if_success
    let _ := SSet.pathFiberCospanMap
  fail_if_success
    let _ := SSet.limitMap_pathFiberCospanMap
  fail_if_success
    let _ := SSet.pathSpaceMap_mem_realizationWeakEquivalences
  fail_if_success
    let _ := SSet.pathHomotopyFiberRealizationComparison_homeomorph
  fail_if_success
    let _ := SSet.pathHomotopyFiberRealizationComparison_isHomeomorph
  fail_if_success
    let _ := SSet.pathHomotopyFiberRealizationComparison_quasifibration
  fail_if_success
    let _ := SSet.bkPointFiberComparison_mem_weakHomotopyEquivalences
  fail_if_success
    let _ := SSet.pathHomotopyFiberQuillenB
  fail_if_success
    let _ := SSet.pathHomotopyFiber_principalBundle
  fail_if_success
    let _ := SSet.pathHomotopyFiber_delooping
  trivial

end Falsifiers

#check SSet.pathSpaceRealizationComparison
#check SSet.pathSpaceRealizationComparison_evalZero
#check SSet.pathSpaceRealizationComparison_evalOne
#check SSet.constPath_pathSpaceRealizationComparison
#check SSet.pathHomotopyFiberRealizationComparison
#check SSet.pathHomotopyFiberRealizationComparison_toTotal
#check SSet.pathHomotopyFiberRealizationComparison_path
#check SSet.pathHomotopyFiberRealizationComparison_mem_weakHomotopyEquivalences
#check SSet.pathHomotopyFiberMap_mem_realizationWeakEquivalences

#print axioms SSet.pathSpaceRealizationComparison
#print axioms SSet.pathSpaceRealizationComparison_evalZero
#print axioms SSet.pathSpaceRealizationComparison_evalOne
#print axioms SSet.constPath_pathSpaceRealizationComparison
#print axioms SSet.pathHomotopyFiberRealizationComparison
#print axioms SSet.pathHomotopyFiberRealizationComparison_toTotal
#print axioms SSet.pathHomotopyFiberRealizationComparison_path
#print axioms SSet.pathHomotopyFiberRealizationComparison_mem_weakHomotopyEquivalences
#print axioms SSet.pathHomotopyFiberMap_mem_realizationWeakEquivalences

end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory
