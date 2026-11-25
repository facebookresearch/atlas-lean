/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.Ext.ShortExactClasses
public import Mathlib.Algebra.Homology.ShortComplex.Pullback
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Short exact representatives of Ext¹

An injective presentation and its cokernel define the connecting class.
Pullback along a morphism to that cokernel represents each Ext¹ class.
The representative law follows from naturality of `extClass`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe e v u

namespace CategoryTheory.ShortExactSequence.WithEndpoints

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{e} C]

/-- The literal pair represents its Ext class after the
proved endpoint normalization. -/
theorem extClass_mk_native (S : ShortComplex C) (hS : S.ShortExact) :
    extClass (mk S.f S.g S.zero hS) = hS.extClass := by
  let E := mk S.f S.g S.zero hS
  have h := ShortComplex.ShortExact.extClass_naturality
    E.complex_shortExact hS E.complexIso.hom
  change (extClass E).comp (Abelian.Ext.mk₀ (𝟙 S.X₁)) (add_zero 1) =
    (Abelian.Ext.mk₀ (𝟙 S.X₃)).comp hS.extClass (zero_add 1) at h
  simpa only [Abelian.Ext.comp_mk₀_id, Abelian.Ext.mk₀_id_comp] using h

variable [EnoughInjectives C] (X Y : C)

/-- Every degree-one Ext value has an short exact representative
with these literal endpoints. -/
theorem extClass_surjective :
    Function.Surjective (extClass : WithEndpoints X Y → Abelian.Ext.{e} X Y 1) := by
  intro z
  let S := ShortComplex.mk (Injective.ι Y)
    (cokernel.π (Injective.ι Y)) (cokernel.condition (Injective.ι Y))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (Injective.ι Y)) }
  obtain ⟨a, ha⟩ := Abelian.Ext.covariant_sequence_exact₁ X hS z
    (Abelian.Ext.eq_zero_of_injective _) (rfl : 0 + 1 = 1)
  let f : X ⟶ S.X₃ := Abelian.Ext.homEquiv₀ a
  have ha' :
      (Abelian.Ext.mk₀ f).comp hS.extClass (rfl : 0 + 1 = 1) = z := by
    change (Abelian.Ext.mk₀ (Abelian.Ext.homEquiv₀ a)).comp hS.extClass
      (rfl : 0 + 1 = 1) = z
    rw [Abelian.Ext.mk₀_homEquiv₀_apply]
    exact ha
  let T := S.pull f
  have hT : T.ShortExact := hS.pull f
  let φ : T ⟶ S :=
    { τ₁ := 𝟙 _
      τ₂ := pullback.snd f S.g
      τ₃ := f
      comm₁₂ := by simp [T]
      comm₂₃ := (pullback.condition (f := f) (g := S.g)).symm }
  have hnat := ShortComplex.ShortExact.extClass_naturality hT hS φ
  dsimp only [φ] at hnat
  refine ⟨mk T.f T.g T.zero hT, ?_⟩
  rw [extClass_mk_native]
  calc
    hT.extClass = (Abelian.Ext.mk₀ f).comp hS.extClass (rfl : 0 + 1 = 1) := by
      simpa only [Abelian.Ext.comp_mk₀_id] using hnat
    _ = z := ha'

/-- An extension chosen from the proved pullback representation. -/
def ofExtOne (z : Abelian.Ext.{e} X Y 1) : WithEndpoints X Y :=
  Classical.choose (extClass_surjective X Y z)

@[simp]
theorem extClass_ofExtOne (z : Abelian.Ext.{e} X Y 1) :
    extClass (ofExtOne X Y z) = z :=
  Classical.choose_spec (extClass_surjective X Y z)

/-- The quotient class map of extensions is surjective onto Ext-one. -/
theorem classifyingMap_surjective :
    Function.Surjective (classifyingMap : Classes X Y → Abelian.Ext.{e} X Y 1) := by
  intro z
  exact ⟨classOf (ofExtOne X Y z), extClass_ofExtOne X Y z⟩

end CategoryTheory.ShortExactSequence.WithEndpoints
