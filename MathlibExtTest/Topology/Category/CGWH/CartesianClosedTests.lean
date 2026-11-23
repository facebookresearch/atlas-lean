/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.CartesianClosed

/-!
# Tests for the cartesian closed structure on CGWH

These clients pin the mixed-universe native mapping object, its fixed-point
evaluation maps, the selected tensor/internal-Hom adjunction, and the scoped
generic self-enrichment boundary.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Topology MonoidalCategory

namespace MathlibExtTest.Topology.Category.CGWH.CartesianClosedTests

section PublicSurface

variable (A B Y : CGWH.{u, v})

example : CGWH.{u, v} := CGWH.internalHom A B

example : UWeakHausdorffSpace.{u} (CGWH.internalHom A B) :=
  CGWH.internalHom_isWeakHausdorff A B

example : CGWH.{u, v} ⥤ CGWH.{u, v} := CGWH.internalHomFunctor A

example : tensorLeft A ⊣ CGWH.internalHomFunctor A :=
  CGWH.internalHomAdjunction A

example : Function.Bijective (CGWH.prodComparisonToTop A Y) :=
  CGWH.prodComparisonToTop_bijective A Y

example : (ihom A).obj B = CGWH.internalHom A B :=
  CGWH.ihom_obj_eq_internalHom A B

example :
    CGWH.cgwhToTop.obj (CGWH.internalHom A B) ⟶
      TopCat.of (ContinuousMapGeneratedBy
        CompactlyGenerated.compactHausProbes.{u} A B) :=
  CGWH.internalHomToRawGenerated A B

example (h : CGWH.internalHom A B) (a : A) :
    CGWH.internalHomToRawGenerated A B h a =
      (WithGeneratedByTopology.equiv
        (X := CompactlyGenerated.compactHausProbes.{u})
        (Y := ContinuousMapGeneratedBy
          CompactlyGenerated.compactHausProbes.{u} A B) h :
        ContinuousMapGeneratedBy
          CompactlyGenerated.compactHausProbes.{u} A B) a :=
  rfl

example : (inferInstance : CartesianMonoidalCategory CGWH.{u, v}) =
    CGWH.instCartesianMonoidalCategory := rfl

example : (inferInstance : MonoidalClosed CGWH.{u, v}) =
    CGWH.instMonoidalClosed := rfl

end PublicSurface

section CarrierCharacteristics

variable (A B Y : CGWH.{u, v})

example (z : (A ⊗ CGWH.internalHom A B : CGWH.{u, v})) :
    (ihom.ev A).app B z =
      (WithGeneratedByTopology.equiv
        (X := CompactlyGenerated.compactHausProbes.{u})
        (Y := ContinuousMapGeneratedBy
          CompactlyGenerated.compactHausProbes.{u} A B)
        (CartesianMonoidalCategory.snd A (CGWH.internalHom A B) z) :
          ContinuousMapGeneratedBy
            CompactlyGenerated.compactHausProbes.{u} A B)
        (CartesianMonoidalCategory.fst A (CGWH.internalHom A B) z) := by
  rw [CGWH.internalHom_ev_apply]

example (f : A ⊗ Y ⟶ B) (z : (A ⊗ Y : CGWH.{u, v})) :
    (WithGeneratedByTopology.equiv
      (X := CompactlyGenerated.compactHausProbes.{u})
      (Y := ContinuousMapGeneratedBy
        CompactlyGenerated.compactHausProbes.{u} A B)
      (MonoidalClosed.curry f
        (CartesianMonoidalCategory.snd A Y z)) :
        ContinuousMapGeneratedBy
          CompactlyGenerated.compactHausProbes.{u} A B)
      (CartesianMonoidalCategory.fst A Y z) =
    f z := by
  rw [CGWH.internalHom_curry_apply]

example (z : (A ⊗ Y : CGWH.{u, v})) :
    (WithGeneratedByTopology.equiv
      (X := CompactlyGenerated.compactHausProbes.{u})
      (Y := ContinuousMapGeneratedBy
        CompactlyGenerated.compactHausProbes.{u} A Y)
      (MonoidalClosed.curry (CartesianMonoidalCategory.snd A Y)
        (CartesianMonoidalCategory.snd A Y z)) :
        ContinuousMapGeneratedBy
          CompactlyGenerated.compactHausProbes.{u} A Y)
      (CartesianMonoidalCategory.fst A Y z) =
    CartesianMonoidalCategory.snd A Y z := by
  rw [CGWH.internalHom_curry_apply]

example : True := by
  fail_if_success
    have _h : ∀ z : (A ⊗ CGWH.internalHom A B : CGWH.{u, v}),
        (ihom.ev A).app B z =
          (WithGeneratedByTopology.equiv
            (X := CompactlyGenerated.compactHausProbes.{u})
            (Y := ContinuousMapGeneratedBy
              CompactlyGenerated.compactHausProbes.{u} A B)
            (CartesianMonoidalCategory.fst A (CGWH.internalHom A B) z) :
              ContinuousMapGeneratedBy
                CompactlyGenerated.compactHausProbes.{u} A B)
            (CartesianMonoidalCategory.snd A (CGWH.internalHom A B) z) :=
      fun z ↦ CGWH.internalHom_ev_apply A B z
  trivial

end CarrierCharacteristics

section FixedEvaluation

variable (A B : CGWH.{u, v}) (a : A)

example : C(CGWH.internalHom A B, B) := by
  let P := CompactlyGenerated.compactHausProbes.{u}
  let pointProbe : CompHaus.{u} := CompHaus.of PUnit.{u + 1}
  let constA : C(pointProbe, A) := ⟨fun _ ↦ a, continuous_const⟩
  let raw : C(CGWH.internalHom A B,
      ContinuousMapGeneratedBy P A B) :=
    ConcreteCategory.hom (C := TopCat.{v})
      (CGWH.internalHomToRawGenerated A B)
  let pre : C(ContinuousMapGeneratedBy P A B, C(pointProbe, B)) :=
    ⟨ContinuousMapGeneratedBy.precomp (X := P) constA,
      ContinuousMapGeneratedBy.continuous_precomp (X := P) constA⟩
  let ev : C(C(pointProbe, B), B) :=
    ⟨fun f ↦ f PUnit.unit, continuous_eval_const PUnit.unit⟩
  exact ev.comp (pre.comp raw)

example : True := by
  fail_if_success
    let _ : LocallyCompactSpace A := inferInstance
  fail_if_success
    let _ : T2Space A := inferInstance
  trivial

end FixedEvaluation

section ClosedCoherence

variable (A B C : CGWH.{u, v})

example : Closed A := inferInstance
example : (tensorLeft A).IsLeftAdjoint := inferInstance
example : (ihom A).IsRightAdjoint := inferInstance
example : PreservesColimits (tensorLeft A) := inferInstance
example : PreservesColimits (tensorRight A) := inferInstance

example (f : A ⊗ B ⟶ C) :
    MonoidalClosed.uncurry (MonoidalClosed.curry f) = f :=
  MonoidalClosed.uncurry_curry f

example (g : B ⟶ (ihom A).obj C) :
    MonoidalClosed.curry (MonoidalClosed.uncurry g) = g :=
  MonoidalClosed.curry_uncurry g

example {B' : CGWH.{u, v}} (f : B' ⟶ B) (g : A ⊗ B ⟶ C) :
    MonoidalClosed.curry (A ◁ f ≫ g) =
      f ≫ MonoidalClosed.curry g :=
  MonoidalClosed.curry_natural_left f g

example {C' : CGWH.{u, v}} (f : A ⊗ B ⟶ C) (g : C ⟶ C') :
    MonoidalClosed.curry (f ≫ g) =
      MonoidalClosed.curry f ≫ (ihom A).map g :=
  MonoidalClosed.curry_natural_right f g

end ClosedCoherence

section UniverseMatrix

#check CGWH.internalHom.{0, 0}
#check CGWH.internalHom_isWeakHausdorff.{0, 0}
#check CGWH.internalHomFunctor.{0, 0}
#check CGWH.internalHomAdjunction.{0, 0}
#check CGWH.ihom_obj_eq_internalHom.{0, 0}
#check CGWH.internalHomToRawGenerated.{0, 0}
#check CGWH.internalHom_ev_apply.{0, 0}
#check CGWH.internalHom_curry_apply.{0, 0}
#check CGWH.instMonoidalClosed.{0, 0}

#check CGWH.internalHom.{1, 1}
#check CGWH.internalHom_isWeakHausdorff.{1, 1}
#check CGWH.internalHomFunctor.{1, 1}
#check CGWH.internalHomAdjunction.{1, 1}
#check CGWH.ihom_obj_eq_internalHom.{1, 1}
#check CGWH.internalHomToRawGenerated.{1, 1}
#check CGWH.internalHom_ev_apply.{1, 1}
#check CGWH.internalHom_curry_apply.{1, 1}
#check CGWH.instMonoidalClosed.{1, 1}

#check CGWH.internalHom.{0, 1}
#check CGWH.internalHom_isWeakHausdorff.{0, 1}
#check CGWH.internalHomFunctor.{0, 1}
#check CGWH.internalHomAdjunction.{0, 1}
#check CGWH.ihom_obj_eq_internalHom.{0, 1}
#check CGWH.internalHomToRawGenerated.{0, 1}
#check CGWH.internalHom_ev_apply.{0, 1}
#check CGWH.internalHom_curry_apply.{0, 1}
#check CGWH.instMonoidalClosed.{0, 1}

#check CGWH.internalHom.{1, 0}
#check CGWH.internalHom_isWeakHausdorff.{1, 0}
#check CGWH.internalHomFunctor.{1, 0}
#check CGWH.internalHomAdjunction.{1, 0}
#check CGWH.ihom_obj_eq_internalHom.{1, 0}
#check CGWH.internalHomToRawGenerated.{1, 0}
#check CGWH.internalHom_ev_apply.{1, 0}
#check CGWH.internalHom_curry_apply.{1, 0}
#check CGWH.instMonoidalClosed.{1, 0}

#check CGWH.internalHom.{u, v}
#check CGWH.internalHom_isWeakHausdorff.{u, v}
#check CGWH.internalHomFunctor.{u, v}
#check CGWH.internalHomAdjunction.{u, v}
#check CGWH.ihom_obj_eq_internalHom.{u, v}
#check CGWH.internalHomToRawGenerated.{u, v}
#check CGWH.internalHom_ev_apply.{u, v}
#check CGWH.internalHom_curry_apply.{u, v}
#check CGWH.instMonoidalClosed.{u, v}

end UniverseMatrix

section EnrichmentOff

example : True := by
  fail_if_success
    let _ : EnrichedCategory CGWH.{u, v} CGWH.{u, v} := inferInstance
  fail_if_success
    let _ : EnrichedOrdinaryCategory CGWH.{u, v} CGWH.{u, v} :=
      inferInstance
  trivial

end EnrichmentOff

section EnrichmentOn

open scoped MonoidalClosed

variable (A B C : CGWH.{u, v})

example : EnrichedCategory CGWH.{u, v} CGWH.{u, v} := inferInstance
example : EnrichedOrdinaryCategory CGWH.{u, v} CGWH.{u, v} :=
  inferInstance
example : EnrichedCategory.Hom A B = (ihom A).obj B :=
  MonoidalClosed.enrichedCategorySelf_hom A B
example : eId CGWH.{u, v} A = MonoidalClosed.id A :=
  MonoidalClosed.enrichedCategorySelf_id A
example : eComp CGWH.{u, v} A B C = MonoidalClosed.comp A B C :=
  MonoidalClosed.enrichedCategorySelf_comp A B C

end EnrichmentOn

section EnrichmentTeardown

example : True := by
  fail_if_success
    let _ : EnrichedCategory CGWH.{u, v} CGWH.{u, v} := inferInstance
  fail_if_success
    let _ : EnrichedOrdinaryCategory CGWH.{u, v} CGWH.{u, v} :=
      inferInstance
  trivial

end EnrichmentTeardown

section NoSecondClosedDictionary

attribute [-instance] CGWH.instMonoidalClosed

example : True := by
  fail_if_success
    let _ : MonoidalClosed CGWH.{u, v} := inferInstance
  trivial

end NoSecondClosedDictionary

section Nonclaims

#guard_msgs (error, substring := true) in
#check CGWH.internalHomToCompactOpen

#guard_msgs (error, substring := true) in
#check CGWH.generatedMapHomeomorphCompactOpen

#check @CGWH.tensorEquivProd.{u, v}

example (A Y : CGWH.{u, v}) :
    (A ⊗ Y : CGWH.{u, v}) ≃ (A × Y) :=
  CGWH.tensorEquivProd A Y

example (A Y : CGWH.{u, v}) (z : (A ⊗ Y : CGWH.{u, v})) :
    (CGWH.tensorEquivProd A Y z).1 =
      CartesianMonoidalCategory.fst A Y z :=
  CGWH.tensorEquivProd_apply_fst A Y z

example (A Y : CGWH.{u, v}) (z : (A ⊗ Y : CGWH.{u, v})) :
    (CGWH.tensorEquivProd A Y z).2 =
      CartesianMonoidalCategory.snd A Y z :=
  CGWH.tensorEquivProd_apply_snd A Y z

/-- error: Unknown constant `CGWH.curryHom` -/
#guard_msgs in
#check CGWH.curryHom

/-- error: Unknown constant `CGWH.uncurryHom` -/
#guard_msgs in
#check CGWH.uncurryHom

example : True := by
  fail_if_success
    let _ : MonoidalClosed TopCat.{v} := inferInstance
  trivial

end Nonclaims

#print axioms CGWH.internalHom
#print axioms CGWH.internalHom_isWeakHausdorff
#print axioms CGWH.internalHomFunctor
#print axioms CGWH.internalHomAdjunction
#print axioms CGWH.ihom_obj_eq_internalHom
#print axioms CGWH.internalHomToRawGenerated
#print axioms CGWH.internalHom_ev_apply
#print axioms CGWH.internalHom_curry_apply
#print axioms CGWH.instMonoidalClosed

end MathlibExtTest.Topology.Category.CGWH.CartesianClosedTests
