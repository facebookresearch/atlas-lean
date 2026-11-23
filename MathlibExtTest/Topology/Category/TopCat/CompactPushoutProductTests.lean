/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.CompactPushoutProduct

/-!
# Compact pushout-product consumers

Public-only clients for global and open-restricted compact TopCat pushouts
after product with an arbitrary factor.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

namespace MathlibExtTest.Topology.Category.TopCat.CompactPushoutProductTests

universe u

section PublicAPI

example {F X₁ X₂ X₃ X₄ : TopCat.{u}}
    [CompactSpace X₂] [CompactSpace X₃] [T2Space X₄]
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
    {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    (h : IsPushout t l r b) :
    IsPushout (prod.map t (𝟙 F)) (prod.map l (𝟙 F))
      (prod.map r (𝟙 F)) (prod.map b (𝟙 F)) :=
  TopCat.isPushout_prodMap_right_of_isPushout_of_compact_to_t2 h

example (P : TopCat.RestrictedPushout.{u})
    [CompactSpace P.X₂] [CompactSpace P.X₃] [T2Space P.X₄]
    (hU : IsOpen P.U) (F : TopCat.{u}) :
    IsPushout (prod.map P.tU (𝟙 F)) (prod.map P.lU (𝟙 F))
      (prod.map P.rU (𝟙 F)) (prod.map P.bU (𝟙 F)) :=
  P.isPushout_prodMap_right_of_compact_to_t2 hU F

example (_F : TopCat.{u}) : True := by
  fail_if_success
    have _ : LocallyCompactSpace _F := inferInstance
  trivial

end PublicAPI

section NoninjectivePushout

private abbrev A : TopCat.{0} := TopCat.of (Fin 2)
private abbrev B : TopCat.{0} := TopCat.of PUnit

private def collapse : A ⟶ B :=
  TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩

private theorem collapse_not_injective : ¬Function.Injective collapse := by
  intro h
  have h01 : (0 : Fin 2) = 1 := h rfl
  norm_num at h01

private theorem collapsePushout :
    IsPushout collapse (𝟙 A) (𝟙 B) collapse :=
  IsPushout.id_vert collapse

example (F : TopCat.{0}) :
    IsPushout (prod.map collapse (𝟙 F))
      (prod.map (𝟙 A) (𝟙 F))
      (prod.map (𝟙 B) (𝟙 F))
      (prod.map collapse (𝟙 F)) :=
  TopCat.isPushout_prodMap_right_of_isPushout_of_compact_to_t2
    collapsePushout

private abbrev emptyRestricted : TopCat.RestrictedPushout.{0} :=
  TopCat.RestrictedPushout.of collapsePushout (∅ : Set B)

private abbrev fullRestricted : TopCat.RestrictedPushout.{0} :=
  TopCat.RestrictedPushout.of collapsePushout (Set.univ : Set B)

example (F : TopCat.{0}) :
    IsPushout (prod.map emptyRestricted.tU (𝟙 F))
      (prod.map emptyRestricted.lU (𝟙 F))
      (prod.map emptyRestricted.rU (𝟙 F))
      (prod.map emptyRestricted.bU (𝟙 F)) := by
  let _ : CompactSpace emptyRestricted.X₂ := by
    change CompactSpace B
    infer_instance
  let _ : CompactSpace emptyRestricted.X₃ := by
    change CompactSpace A
    infer_instance
  let _ : T2Space emptyRestricted.X₄ := by
    change T2Space B
    infer_instance
  exact emptyRestricted.isPushout_prodMap_right_of_compact_to_t2
    isOpen_empty F

example (F : TopCat.{0}) :
    IsPushout (prod.map fullRestricted.tU (𝟙 F))
      (prod.map fullRestricted.lU (𝟙 F))
      (prod.map fullRestricted.rU (𝟙 F))
      (prod.map fullRestricted.bU (𝟙 F)) := by
  let _ : CompactSpace fullRestricted.X₂ := by
    change CompactSpace B
    infer_instance
  let _ : CompactSpace fullRestricted.X₃ := by
    change CompactSpace A
    infer_instance
  let _ : T2Space fullRestricted.X₄ := by
    change T2Space B
    infer_instance
  exact fullRestricted.isPushout_prodMap_right_of_compact_to_t2
    isOpen_univ F

end NoninjectivePushout

#print axioms TopCat.isPushout_prodMap_right_of_isPushout_of_compact_to_t2
#print axioms TopCat.RestrictedPushout.isPushout_prodMap_right_of_compact_to_t2

end MathlibExtTest.Topology.Category.TopCat.CompactPushoutProductTests
