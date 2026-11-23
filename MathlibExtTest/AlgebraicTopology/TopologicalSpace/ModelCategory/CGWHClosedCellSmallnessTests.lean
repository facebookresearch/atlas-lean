/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHClosedCellSmallness

/-!
# Tests for CGWH closed-cell smallness
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MorphismProperty
open HomotopicalAlgebra Topology
open scoped Simplicial

#check CGWH.instIsCardinalForSmallObjectArgumentRealizedBoundaryInclusions
#check CGWH.instHasSmallObjectArgumentRealizedBoundaryInclusions
#check CGWH.instIsCardinalForSmallObjectArgumentRealizedHornInclusions
#check CGWH.instHasSmallObjectArgumentRealizedHornInclusions
#check CGWH.realizedBoundaryInclusions_rlp_llp
#check CGWH.realizedHornInclusions_rlp_llp
#check CompactlyGenerated.uWeakHausdorffSpace_of_retract

namespace MathlibExtTest.CGWHClosedCellSmallness

noncomputable local instance :
    Fact realizedGeneratorCardinal.{v}.IsRegular :=
  ⟨isRegular_realizedGeneratorCardinal.{v}⟩

noncomputable local instance :
    OrderBot realizedGeneratorCardinal.{v}.ord.ToType :=
  haveI : Nonempty realizedGeneratorCardinal.{v}.ord.ToType :=
    Ordinal.nonempty_toType_iff.mpr
      (by simpa using isRegular_realizedGeneratorCardinal.{v}.ne_zero)
  WellFoundedLT.toOrderBot realizedGeneratorCardinal.{v}.ord.ToType

section Instances

#synth MorphismProperty.IsCardinalForSmallObjectArgument.{v}
  CGWH.realizedBoundaryInclusions.{u, v} realizedGeneratorCardinal.{v}
#synth MorphismProperty.HasSmallObjectArgument.{v}
  CGWH.realizedBoundaryInclusions.{u, v}
#synth MorphismProperty.IsCardinalForSmallObjectArgument.{v}
  CGWH.realizedHornInclusions.{u, v} realizedGeneratorCardinal.{v}
#synth MorphismProperty.HasSmallObjectArgument.{v}
  CGWH.realizedHornInclusions.{u, v}

example : MorphismProperty.IsCardinalForSmallObjectArgument.{0}
    CGWH.realizedBoundaryInclusions.{0, 0}
      realizedGeneratorCardinal.{0} := inferInstance
example : MorphismProperty.IsCardinalForSmallObjectArgument.{1}
    CGWH.realizedBoundaryInclusions.{1, 1}
      realizedGeneratorCardinal.{1} := inferInstance
example : MorphismProperty.IsCardinalForSmallObjectArgument.{1}
    CGWH.realizedBoundaryInclusions.{0, 1}
      realizedGeneratorCardinal.{1} := inferInstance
example : MorphismProperty.IsCardinalForSmallObjectArgument.{0}
    CGWH.realizedBoundaryInclusions.{1, 0}
      realizedGeneratorCardinal.{0} := inferInstance

example : MorphismProperty.IsCardinalForSmallObjectArgument.{0}
    CGWH.realizedHornInclusions.{0, 0}
      realizedGeneratorCardinal.{0} := inferInstance
example : MorphismProperty.IsCardinalForSmallObjectArgument.{1}
    CGWH.realizedHornInclusions.{1, 1}
      realizedGeneratorCardinal.{1} := inferInstance
example : MorphismProperty.IsCardinalForSmallObjectArgument.{1}
    CGWH.realizedHornInclusions.{0, 1}
      realizedGeneratorCardinal.{1} := inferInstance
example : MorphismProperty.IsCardinalForSmallObjectArgument.{0}
    CGWH.realizedHornInclusions.{1, 0}
      realizedGeneratorCardinal.{0} := inferInstance

end Instances

section GeneratorDimensions

example : CGWH.realizedBoundaryInclusions.{u, v}
    (CGWH.realizedBoundaryInclusion 0) :=
  CGWH.boundary_mem_realizedBoundaryInclusions 0

example (n : ℕ) : CGWH.realizedBoundaryInclusions.{u, v}
    (CGWH.realizedBoundaryInclusion n) :=
  CGWH.boundary_mem_realizedBoundaryInclusions n

example (i : Fin 2) : CGWH.realizedHornInclusions.{u, v}
    (CGWH.realizedHornInclusion 0 i) :=
  CGWH.horn_mem_realizedHornInclusions 0 i

example (i : Fin 5) : CGWH.realizedHornInclusions.{u, v}
    (CGWH.realizedHornInclusion 3 i) :=
  CGWH.horn_mem_realizedHornInclusions 3 i

example (n : ℕ) (i : Fin (n + 2)) :
    CGWH.realizedHornInclusions.{u, v}
      (CGWH.realizedHornInclusion n i) :=
  CGWH.horn_mem_realizedHornInclusions n i

#guard_msgs (error, substring := true) in
example (n : ℕ) (i : Fin (n + 1)) :
    CGWH.realizedHornInclusions.{u, v}
      (CGWH.realizedHornInclusion n i) := by
  exact CGWH.horn_mem_realizedHornInclusions n i

end GeneratorDimensions

section ExactCardinalPreservation

variable {A B X Y : CGWH.{u, v}}
variable (i : A ⟶ B) (f : X ⟶ Y)

example (hi : CGWH.realizedBoundaryInclusions.{u, v} i)
    (c : RelativeCellComplex.{v}
      (fun (_ : realizedGeneratorCardinal.{v}.ord.ToType) =>
        CGWH.realizedBoundaryInclusions.{u, v}.homFamily) f) :
    PreservesColimit c.F (coyoneda.obj (Opposite.op A)) :=
  SmallObject.preservesColimit CGWH.realizedBoundaryInclusions.{u, v}
    realizedGeneratorCardinal.{v} i hi f c

example (hi : CGWH.realizedHornInclusions.{u, v} i)
    (c : RelativeCellComplex.{v}
      (fun (_ : realizedGeneratorCardinal.{v}.ord.ToType) =>
        CGWH.realizedHornInclusions.{u, v}.homFamily) f) :
    PreservesColimit c.F (coyoneda.obj (Opposite.op A)) :=
  SmallObject.preservesColimit CGWH.realizedHornInclusions.{u, v}
    realizedGeneratorCardinal.{v} i hi f c

end ExactCardinalPreservation

section GeneratedLeftClasses

variable {X Y : CGWH.{u, v}} (f : X ⟶ Y)

example (hf : CGWH.realizedBoundaryInclusions.{u, v}.rlp.llp f) :
    CompactlyGenerated.realizedBoundaryInclusions.{u, v}.rlp.llp
      (CGWH.cgwhToCompactlyGenerated.map f) := by
  rw [CGWH.realizedBoundaryInclusions_rlp_llp] at hf
  exact hf

example (hf : CompactlyGenerated.realizedBoundaryInclusions.{u, v}.rlp.llp
    (CGWH.cgwhToCompactlyGenerated.map f)) :
    CGWH.realizedBoundaryInclusions.{u, v}.rlp.llp f := by
  rw [CGWH.realizedBoundaryInclusions_rlp_llp]
  exact hf

example (hf : CGWH.realizedHornInclusions.{u, v}.rlp.llp f) :
    CompactlyGenerated.realizedHornInclusions.{u, v}.rlp.llp
      (CGWH.cgwhToCompactlyGenerated.map f) := by
  rw [CGWH.realizedHornInclusions_rlp_llp] at hf
  exact hf

example (hf : CompactlyGenerated.realizedHornInclusions.{u, v}.rlp.llp
    (CGWH.cgwhToCompactlyGenerated.map f)) :
    CGWH.realizedHornInclusions.{u, v}.rlp.llp f := by
  rw [CGWH.realizedHornInclusions_rlp_llp]
  exact hf

end GeneratedLeftClasses

section StoredTopMap

variable (P : MorphismProperty CGWH.{u, v})
variable {X Y : CGWH.{u, v}} {f : X ⟶ Y}

example (a : AttachCells.{v} P.homFamily f) :
    coproducts.{v} P a.m := by
  let A : a.ι → CGWH.{u, v} := fun i => (a.π i).1.left
  let B : a.ι → CGWH.{u, v} := fun i => (a.π i).1.right
  apply colimitsOfShape_le_coproducts P a.ι
  refine colimitsOfShape.mk' (Discrete.functor A) (Discrete.functor B)
    a.cofan₁ a.cofan₂ a.isColimit₁ a.isColimit₂
    (Discrete.natTrans (fun i => (a.π i.as).1.hom))
    (fun i => (a.π i.as).2) a.m ?_
  intro i
  change a.cofan₁.inj i.as ≫ a.m =
    (a.π i.as).1.hom ≫ a.cofan₂.inj i.as
  exact a.hm i.as

end StoredTopMap

section PublicMappedInterfaces

variable {I : Type v} (Z : I → CGWH.{u, v}) (i : I)

example :
    Sigma.ι (fun k => CGWH.cgwhToCompactlyGenerated.obj (Z k)) i ≫
        (CGWH.coproductComparisonToCompactlyGeneratedIso Z).hom =
      CGWH.cgwhToCompactlyGenerated.map (Sigma.ι Z i) :=
  CGWH.coproductComparisonToCompactlyGeneratedIso_hom_ι Z i

variable {A B C D : CGWH.{u, v}}
variable {g₁ : A ⟶ B} {m : A ⟶ C} {s : B ⟶ D} {g₂ : C ⟶ D}

example (sq : IsPushout g₁ m s g₂)
    (hm : IsClosedEmbedding (CGWH.cgwhToTop.map m).hom) :
    IsPushout (CGWH.cgwhToCompactlyGenerated.map g₁)
      (CGWH.cgwhToCompactlyGenerated.map m)
      (CGWH.cgwhToCompactlyGenerated.map s)
      (CGWH.cgwhToCompactlyGenerated.map g₂) := by
  let _ : PreservesColimit (span m g₁)
      CGWH.cgwhToCompactlyGenerated :=
    CGWH.preservesPushout_of_isClosedEmbedding m g₁ hm
  let _ : PreservesColimit (span g₁ m)
      CGWH.cgwhToCompactlyGenerated :=
    preservesPushout_symmetry CGWH.cgwhToCompactlyGenerated m g₁
  exact sq.map CGWH.cgwhToCompactlyGenerated

end PublicMappedInterfaces

section TransfiniteInterface

variable {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J]
  [WellFoundedLT J]
variable {X Y : CGWH.{u, v}} {f : X ⟶ Y}

example (c : CategoryTheory.TransfiniteCompositionOfShape J f)
    (hSucc : ∀ (a : J) (_ha : ¬ IsMax a), Function.Injective
      (CGWH.cgwhToCompactlyGenerated.map
        (c.F.map (homOfLE (Order.le_succ a)))).hom) :
    CategoryTheory.TransfiniteCompositionOfShape J
      (CGWH.cgwhToCompactlyGenerated.map f) :=
  c.mapCgwhToCompactlyGeneratedOfInjective hSucc

example {X Y : CGWH.{u, 0}} {f : X ⟶ Y}
    (c : CategoryTheory.TransfiniteCompositionOfShape (WithTop ℕ) f)
    (hSucc : ∀ (a : WithTop ℕ) (_ha : ¬ IsMax a), Function.Injective
      (CGWH.cgwhToCompactlyGenerated.map
        (c.F.map (homOfLE (Order.le_succ a)))).hom) :
    CategoryTheory.TransfiniteCompositionOfShape (WithTop ℕ)
      (CGWH.cgwhToCompactlyGenerated.map f) :=
  c.mapCgwhToCompactlyGeneratedOfInjective hSucc

end TransfiniteInterface

section Retracts

example (X : CompactlyGenerated.{u, v}) [UWeakHausdorffSpace.{u} X] :
    UWeakHausdorffSpace.{u} X :=
  CompactlyGenerated.uWeakHausdorffSpace_of_retract
    { i := 𝟙 X, r := 𝟙 X }

example {X Y : CompactlyGenerated.{u, v}} (e : X ≅ Y)
    [UWeakHausdorffSpace.{u} Y] : UWeakHausdorffSpace.{u} X :=
  CompactlyGenerated.uWeakHausdorffSpace_of_retract
    { i := e.hom, r := e.inv }

example (X : CGWH.{u, v}) : UWeakHausdorffSpace.{u}
    (CGWH.cgwhToCompactlyGenerated.obj X) := by
  let F : ULift.{v} Bool → CGWH.{u, v} := fun _ => X
  let R : (∐ F) ⟶ X := Sigma.desc (fun _ => 𝟙 X)
  let h : CategoryTheory.Retract
      (CGWH.cgwhToCompactlyGenerated.obj X)
      (CGWH.cgwhToCompactlyGenerated.obj (∐ F)) :=
    { i := CGWH.cgwhToCompactlyGenerated.map (Sigma.ι F (ULift.up false))
      r := CGWH.cgwhToCompactlyGenerated.map R
      retract := by
        rw [← CGWH.cgwhToCompactlyGenerated.map_comp]
        rw [← CGWH.cgwhToCompactlyGenerated.map_id]
        exact CGWH.cgwhToCompactlyGenerated.congr_map (by simp [R]) }
  let _ : UWeakHausdorffSpace.{u}
      (CGWH.cgwhToCompactlyGenerated.obj (∐ F)) :=
    (∐ F).is_weakHausdorff
  exact CompactlyGenerated.uWeakHausdorffSpace_of_retract h

end Retracts

section NegativeSurface

example : True := by
  fail_if_success
    let _ : PreservesColimits CGWH.cgwhToCompactlyGenerated := inferInstance
  fail_if_success
    let _ : CreatesColimits CGWH.cgwhToCompactlyGenerated := inferInstance
  trivial

#guard_msgs (error, substring := true) in
#check CGWH.modelCategory

#guard_msgs (error, substring := true) in
#check CGWH.cofibrantGenerationData

#guard_msgs (error, substring := true) in
#check CGWH.mapAttachCells

#guard_msgs (error, substring := true) in
#check CGWH.mapRelativeCellComplex

#guard_msgs (error, substring := true) in
#check CGWH.mapPushoutsCoproducts

#guard_msgs (error, substring := true) in
#check CGWH.preservesColimitRelativeCellComplex

#guard_msgs (error, substring := true) in
#check CGWH.isCardinalForSmallObjectArgument_of_closedCells

#guard_msgs (error, substring := true) in
#check CGWH.rlp_llp_eq_inverseImage_of_closedCells

end NegativeSurface

#print CGWH.instIsCardinalForSmallObjectArgumentRealizedBoundaryInclusions
#print CGWH.instHasSmallObjectArgumentRealizedBoundaryInclusions
#print CGWH.instIsCardinalForSmallObjectArgumentRealizedHornInclusions
#print CGWH.instHasSmallObjectArgumentRealizedHornInclusions

#print axioms CGWH.instIsCardinalForSmallObjectArgumentRealizedBoundaryInclusions
#print axioms CGWH.instHasSmallObjectArgumentRealizedBoundaryInclusions
#print axioms CGWH.instIsCardinalForSmallObjectArgumentRealizedHornInclusions
#print axioms CGWH.instHasSmallObjectArgumentRealizedHornInclusions
#print axioms CGWH.realizedBoundaryInclusions_rlp_llp
#print axioms CGWH.realizedHornInclusions_rlp_llp
#print axioms CompactlyGenerated.uWeakHausdorffSpace_of_retract

end MathlibExtTest.CGWHClosedCellSmallness
