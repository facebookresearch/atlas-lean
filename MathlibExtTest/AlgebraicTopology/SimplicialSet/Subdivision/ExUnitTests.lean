/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.ExUnit

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SubdivisionAnodyne
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
# Owner tests for the one-step Ex unit

The clients exercise the four public declarations, reconstruct the private
prefix-chain argument independently, and keep the one-step Kan, isomorphism,
strict-double-unit, Barratt-factor, and generic-replacement overclaims absent.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.Subdivision
namespace ExUnitTests

section PublicSurface

example : Functor.id (SSet.{u}) ⟶ SSet.ex.{u} :=
  SSet.exUnit

example (X : SSet.{u}) :
    (SSet.sdExAdjunction.homEquiv X X).symm
        (SSet.exUnit.app X) =
      SSet.lastVertex.app X :=
  SSet.exUnit_mate X

example (X : SSet.{1}) :
    (SSet.sdExAdjunction.homEquiv X X).symm
        (SSet.exUnit.app X) =
      SSet.lastVertex.app X :=
  SSet.exUnit_mate X

example (X : SSet.{0}) :
    (SSet.sdExAdjunction.homEquiv X X).symm
        (SSet.exUnit.app X) =
      SSet.lastVertex.app X :=
  SSet.exUnit_mate X

example {X Y : SSet.{u}} (f : X ⟶ Y) :
    f ≫ SSet.exUnit.app Y =
      SSet.exUnit.app X ≫ SSet.ex.map f :=
  SSet.exUnit.naturality f

example (X : SSet.{u}) : Mono (SSet.exUnit.app X) :=
  SSet.exUnit_app_mono X

example (X : SSet.{1}) : Mono (SSet.exUnit.app X) :=
  SSet.exUnit_app_mono X

example (X : SSet.{0}) : Mono (SSet.exUnit.app X) :=
  SSet.exUnit_app_mono X

example (X : SSet.{u}) :
    SSet.realizationWeakEquivalences (SSet.exUnit.app X) :=
  SSet.exUnit_app_mem_realizationWeakEquivalences X

example (X : SSet.{1}) :
    SSet.realizationWeakEquivalences (SSet.exUnit.app X) :=
  SSet.exUnit_app_mem_realizationWeakEquivalences X

example (X : SSet.{0}) :
    SSet.realizationWeakEquivalences (SSet.exUnit.app X) :=
  SSet.exUnit_app_mem_realizationWeakEquivalences X

end PublicSurface

section PublicComponentConsequences

private theorem exUnitComponentInjective
    (X : SSet.{u}) (n : SimplexCategory) :
    Function.Injective
      ((SSet.exUnit.app X).app (Opposite.op n)) := by
  exact (mono_iff_injective _).mp
    ((NatTrans.mono_iff_mono_app (SSet.exUnit.app X)).mp
      (SSet.exUnit_app_mono X) (Opposite.op n))

example : Function.Injective
    ((SSet.exUnit.app (Δ[0] : SSet.{u})).app
      (Opposite.op ⦋0⦌)) :=
  exUnitComponentInjective (Δ[0] : SSet.{u}) ⦋0⦌

example : Function.Injective
    ((SSet.exUnit.app (Δ[1] : SSet.{u})).app
      (Opposite.op ⦋1⦌)) :=
  exUnitComponentInjective (Δ[1] : SSet.{u}) ⦋1⦌

example : Function.Injective
    ((SSet.exUnit.app (Δ[2] : SSet.{u})).app
      (Opposite.op ⦋2⦌)) :=
  exUnitComponentInjective (Δ[2] : SSet.{u}) ⦋2⦌

example : SSet.realizationWeakEquivalences
    (SSet.exUnit.app (Δ[0] : SSet.{u})) :=
  SSet.exUnit_app_mem_realizationWeakEquivalences _

example : SSet.realizationWeakEquivalences
    (SSet.exUnit.app (Δ[1] : SSet.{u})) :=
  SSet.exUnit_app_mem_realizationWeakEquivalences _

example : SSet.realizationWeakEquivalences
    (SSet.exUnit.app (Δ[2] : SSet.{u})) :=
  SSet.exUnit_app_mem_realizationWeakEquivalences _

end PublicComponentConsequences

section IndependentPrefixChain

private def testPrefixFace (n : SimplexCategory)
    (j : Fin (n.len + 1)) :
    PartialOrder.NonemptyFiniteChains
      (ULift.{u} (Fin (n.len + 1))) where
  finset := Finset.univ.filter (fun i => i.down ≤ j)
  nonempty := ⟨ULift.up j, by simp⟩
  comparable _ _ := le_total _ _

private def testPrefixFaceOrderHom (n : SimplexCategory) :
    Fin (n.len + 1) →o
      PartialOrder.NonemptyFiniteChains
        (ULift.{u} (Fin (n.len + 1))) where
  toFun := testPrefixFace n
  monotone' i j hij x hx := by
    simp only [testPrefixFace, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx ⊢
    exact hx.trans hij

private def testPrefixChain (n : SimplexCategory) :
    (SimplexCategory.sd.{u}.obj n).obj (Opposite.op n) :=
  (testPrefixFaceOrderHom n).monotone.functor

private theorem testSdChainLastPrefixFace (n : SimplexCategory)
    (j : Fin (n.len + 1)) :
    SimplexCategory.sdChainLast n (testPrefixFace n j) =
      ULift.up j := by
  unfold SimplexCategory.sdChainLast testPrefixFace
  rw [Finset.max'_eq_iff]
  constructor
  · simp
  · intro b hb
    change b.down ≤ j
    simpa only [Finset.mem_filter, Finset.mem_univ,
      true_and] using hb

private noncomputable def testRawPrefixSection
    (n : SimplexCategory)
    (z : (SimplexCategory.sd.{u}.obj n) _⦋n.len⦌) :
    SSet.stdSimplex.obj n ⟶ SimplexCategory.sd.obj n :=
  SSet.yonedaEquiv.{u}.symm z

private theorem testRawPrefixSection_retraction
    (n : SimplexCategory)
    (z : (SimplexCategory.sd.{u}.obj n) _⦋n.len⦌)
    (hz : ∀ i : Fin (n.len + 1),
      SimplexCategory.sdChainLast n (z.obj i) = ULift.up i) :
    testRawPrefixSection n z ≫
        SimplexCategory.lastVertex.app n =
      𝟙 _ := by
  apply SSet.yonedaEquiv.{u}.injective
  rw [SSet.yonedaEquiv_comp]
  have hsec := Equiv.apply_symm_apply SSet.yonedaEquiv.{u} z
  simp only [testRawPrefixSection]
  rw [hsec]
  apply SSet.stdSimplex.ext
  intro i
  change SSet.stdSimplex.objEquiv.{u}
      ((SimplexCategory.lastVertex.app n).app _ z) i =
    SSet.stdSimplex.objEquiv.{u}
      (SSet.yonedaEquiv.{u}
        (𝟙 (SSet.stdSimplex.obj n))) i
  rw [SimplexCategory.lastVertex_app_objEquiv_apply,
    SSet.stdSimplex.objEquiv_yonedaEquiv_id.{u}]
  exact congrArg ULift.down (hz i)

private noncomputable def testRawLastVertexSection
    (n : SimplexCategory) :
    SSet.stdSimplex.obj n ⟶ SimplexCategory.sd.obj n :=
  testRawPrefixSection n (testPrefixChain n)

private theorem testRawLastVertexSection_comp (n : SimplexCategory) :
    testRawLastVertexSection n ≫
        SimplexCategory.lastVertex.app n =
      𝟙 _ := by
  apply testRawPrefixSection_retraction n (testPrefixChain n)
  intro i
  change SimplexCategory.sdChainLast n
    (testPrefixFace n i) = ULift.up i
  exact testSdChainLastPrefixFace n i

example :
    testRawLastVertexSection (⦋0⦌ : SimplexCategory) ≫
        SimplexCategory.lastVertex.app ⦋0⦌ =
      𝟙 _ :=
  testRawLastVertexSection_comp ⦋0⦌

example :
    testRawLastVertexSection (⦋1⦌ : SimplexCategory) ≫
        SimplexCategory.lastVertex.app ⦋1⦌ =
      𝟙 _ :=
  testRawLastVertexSection_comp ⦋1⦌

example :
    testRawLastVertexSection (⦋2⦌ : SimplexCategory) ≫
        SimplexCategory.lastVertex.app ⦋2⦌ =
      𝟙 _ :=
  testRawLastVertexSection_comp ⦋2⦌

end IndependentPrefixChain

section VertexBijection

private theorem testExUnitAppDown
    (X : SSet.{u}) {n : SimplexCategory}
    (x : X.obj (Opposite.op n)) :
    ULift.down ((SSet.exUnit.app X).app (Opposite.op n) x) =
      SimplexCategory.lastVertex.app n ≫
        SSet.yonedaEquiv.symm x := by
  let α := SSet.stdSimplex.{u}.leftKanExtensionUnit
    SimplexCategory.sd.{u}
  have hα : SSet.sd.{u}.IsLeftKanExtension α := by
    change (SSet.stdSimplex.{u}.leftKanExtension
      SimplexCategory.sd.{u}).IsLeftKanExtension
        (SSet.stdSimplex.{u}.leftKanExtensionUnit
          SimplexCategory.sd.{u})
    infer_instance
  have happ :=
    @Presheaf.uliftYonedaAdjunction_homEquiv_app.{0, 0, u, 0, u + 1}
      SimplexCategory _ (SSet.{u}) _ SimplexCategory.sd.{u} _
      SSet.sd.{u} α hα X X (SSet.lastVertex.app X)
      (Opposite.op n) x
  have happ' :
      (SSet.exUnit.app X).app (Opposite.op n) x =
        ULift.up
          (SSet.stdSimplex.sdIso.inv.app n ≫
            SSet.sd.map (SSet.yonedaEquiv.symm x) ≫
            SSet.lastVertex.app X) := by
    simpa only [SSet.exUnit, α, SSet.sdExAdjunction,
      SSet.ex, SSet.sd, SSet.yonedaEquiv] using! happ
  have hdown := congrArg ULift.down happ'
  rw [SSet.lastVertex.naturality] at hdown
  rw [← Category.assoc, SSet.lastVertex_fac] at hdown
  exact hdown

private theorem zeroChain_eq
    (A B : PartialOrder.NonemptyFiniteChains
      (ULift.{u} (Fin 1))) :
    A = B := by
  apply PartialOrder.NonemptyFiniteChains.ext
  exact A.nonempty.eq_singleton_default.trans
    B.nonempty.eq_singleton_default.symm

private instance sdZeroObjSubsingleton (d : SimplexCategoryᵒᵖ) :
    Subsingleton ((SimplexCategory.sd.{u}.obj ⦋0⦌).obj d) where
  allEq _F _G :=
    CategoryTheory.Functor.ext
      (fun i => zeroChain_eq (_F.obj i) (_G.obj i))
      (fun _ _ _ => Subsingleton.elim _ _)

private theorem lastVertex_comp_testRawSection_zero :
    SimplexCategory.lastVertex.app (⦋0⦌ : SimplexCategory) ≫
        testRawLastVertexSection (⦋0⦌ : SimplexCategory) =
      𝟙 _ := by
  ext d z
  exact Subsingleton.elim _ _

private theorem exUnitVertexSurjective (X : SSet.{u}) :
    Function.Surjective
      ((SSet.exUnit.app X).app (Opposite.op ⦋0⦌)) := by
  intro y
  let x : X _⦋0⦌ :=
    SSet.yonedaEquiv
      (testRawLastVertexSection (⦋0⦌ : SimplexCategory) ≫
        ULift.down y)
  refine ⟨x, ?_⟩
  apply ULift.down_injective
  rw [testExUnitAppDown]
  simp only [x, Equiv.symm_apply_apply]
  rw [← Category.assoc, lastVertex_comp_testRawSection_zero,
    Category.id_comp]

private theorem exUnitVertexBijective (X : SSet.{u}) :
    Function.Bijective
      ((SSet.exUnit.app X).app (Opposite.op ⦋0⦌)) :=
  ⟨exUnitComponentInjective X ⦋0⦌,
    exUnitVertexSurjective X⟩

example : Function.Bijective
    ((SSet.exUnit.app (Δ[0] : SSet.{u})).app
      (Opposite.op ⦋0⦌)) :=
  exUnitVertexBijective (Δ[0] : SSet.{u})

example : Function.Bijective
    ((SSet.exUnit.app (Δ[1] : SSet.{u})).app
      (Opposite.op ⦋0⦌)) :=
  exUnitVertexBijective (Δ[1] : SSet.{u})

example : Function.Bijective
    ((SSet.exUnit.app (Δ[2] : SSet.{u})).app
      (Opposite.op ⦋0⦌)) :=
  exUnitVertexBijective (Δ[2] : SSet.{u})

end VertexBijection

section BoundaryInputs

private abbrev emptySSet : SSet.{u} :=
  ((⊥ : SSet.Subcomplex (Δ[0] : SSet.{u})) : SSet.{u})

private abbrev twoPointSSet : SSet :=
  (Functor.const SimplexCategoryᵒᵖ).obj (Fin 2)

private noncomputable abbrev collapsedBoundaryTwoSphere : SSet.{u} :=
  pushout (SSet.boundary.{u} 2).ι
    (terminal.from (SSet.boundary.{u} 2 : SSet.{u}))

example : Mono (SSet.exUnit.app emptySSet.{u}) :=
  SSet.exUnit_app_mono _

example : SSet.realizationWeakEquivalences
    (SSet.exUnit.app emptySSet.{u}) :=
  SSet.exUnit_app_mem_realizationWeakEquivalences _

example : Mono (SSet.exUnit.app twoPointSSet) :=
  SSet.exUnit_app_mono _

example : SSet.realizationWeakEquivalences
    (SSet.exUnit.app twoPointSSet) :=
  SSet.exUnit_app_mem_realizationWeakEquivalences _

example : Mono (SSet.exUnit.app SSet.S1) :=
  SSet.exUnit_app_mono _

example : SSet.realizationWeakEquivalences
    (SSet.exUnit.app SSet.S1) :=
  SSet.exUnit_app_mem_realizationWeakEquivalences _

example : Mono
    (SSet.exUnit.app collapsedBoundaryTwoSphere.{u}) :=
  SSet.exUnit_app_mono _

example : SSet.realizationWeakEquivalences
    (SSet.exUnit.app collapsedBoundaryTwoSphere.{u}) :=
  SSet.exUnit_app_mem_realizationWeakEquivalences _

example :
    (SSet.exUnit.app twoPointSSet).app
        (Opposite.op ⦋0⦌) (0 : Fin 2) ≠
      (SSet.exUnit.app twoPointSSet).app
        (Opposite.op ⦋0⦌) (1 : Fin 2) := by
  apply (exUnitComponentInjective twoPointSSet ⦋0⦌).ne
  exact (show (0 : Fin 2) ≠ 1 by decide)

end BoundaryInputs

section KanPreservationOnly

private noncomputable def exTerminalIsTerminal :
    IsTerminal (SSet.ex.obj (⊤_ SSet.{u})) := by
  refine IsTerminal.ofUniqueHom
    (fun Z => (SSet.sdExAdjunction.homEquiv Z (⊤_ SSet.{u}))
      (terminal.from (SSet.sd.obj Z))) ?_
  intro Z f
  apply (SSet.sdExAdjunction.homEquiv Z (⊤_ SSet.{u})).symm.injective
  exact Subsingleton.elim _ _

example (X : SSet.{u}) [SSet.KanComplex X] :
    SSet.KanComplex (SSet.ex.obj X) := by
  have hFib : Fibration (SSet.ex.map (terminal.from X)) :=
    inferInstance
  exact (isFibrant_iff_of_isTerminal
    (SSet.ex.map (terminal.from X)) exTerminalIsTerminal).2 hFib

end KanPreservationOnly

section NegativeInstances

example (_X : SSet.{u}) : True := by
  fail_if_success
    let _ : Mono (SSet.exUnit.app _X) := inferInstance
  fail_if_success
    let _ : IsIso (SSet.exUnit.app _X) := inferInstance
  fail_if_success
    let _ : WeakEquivalence (SSet.exUnit.app _X) := inferInstance
  fail_if_success
    let _ : SSet.KanComplex (SSet.ex.obj _X) := inferInstance
  trivial

end NegativeInstances

section PrivateBoundary

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.exUnit_app_down

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.rawLastVertexSection

example (X : SSet.{0}) :
    SSet.realizationWeakEquivalences (SSet.lastVertex.app X) :=
  SSet.lastVertex_app_mem_realizationWeakEquivalences X

example (X : SSet.{1}) :
    SSet.realizationWeakEquivalences (SSet.lastVertex.app X) :=
  SSet.lastVertex_app_mem_realizationWeakEquivalences X

#print axioms SSet.lastVertex_app_mem_realizationWeakEquivalences

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.exUnit_ex_homotopy

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.exUnit_ex_eq

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.exUnit_barrattFactor

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.exUnit_eq_fibrantReplacement

end PrivateBoundary

#print axioms SSet.exUnit
#print axioms SSet.exUnit_mate
#print axioms SSet.exUnit_app_mono
#print axioms SSet.exUnit_app_mem_realizationWeakEquivalences

end ExUnitTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet.Subdivision

end
