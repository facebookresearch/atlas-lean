/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.ExactCategory.Basic
public import MathlibExt.CategoryTheory.Waldhausen.Basic

/-!
# Waldhausen data of a Quillen exact category

Let C be a preadditive Quillen exact category with a zero object and binary
biproducts. Its standard Waldhausen cofibration and weak-equivalence data
take admissible monomorphisms as cofibrations and isomorphisms as weak
equivalences. Pushouts along admissible monomorphisms supply the
cofibration-pushout axiom.

For a short complex A —i→ B —q→ Q, admissible exactness is equivalent
to being a cofibration sequence in this structure: i is an admissible
monomorphism and q presents the pushout of i along A → 0.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory.ExactCategory

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]

/-- Let C be a preadditive Quillen exact category with a zero object
and binary biproducts.

The standard Waldhausen cofibration, weak-equivalence and pushout data with admissible monomorphisms
as cofibrations and isomorphisms as weak equivalences. -/
@[instance_reducible]
def waldhausenCategory : WaldhausenCategoryWithoutGluing C where
  cofibrations := admissibleMonosOf C IsAdmissibleExact
  weakEquivalences := MorphismProperty.isomorphisms C
  cofibrations_isMultiplicative := inferInstance
  cofibrations_respectsIso := inferInstance
  weakEquivalences_isMultiplicative := inferInstance
  weakEquivalences_respectsIso := inferInstance
  zero_isCofibration _ f := IsAdmissibleMono.fromZero f
  cofibration_pushout {X Y} i hi X' f := admissibleMono_pushout X Y i hi X' f

/-- Let C be a preadditive Quillen exact category with a zero object
and binary biproducts.

The cofibrations in the standard Waldhausen data are exactly the admissible monomorphisms of the
given exact structure. -/
@[simp]
lemma waldhausenCategory_cofibrations :
    (waldhausenCategory C).cofibrations = admissibleMonosOf C IsAdmissibleExact :=
  rfl

/-- Let C be a preadditive Quillen exact category with a zero object
and binary biproducts.

The weak equivalences in the standard Waldhausen data are exactly the isomorphisms in C. -/
@[simp]
lemma waldhausenCategory_weakEquivalences :
    (waldhausenCategory C).weakEquivalences = MorphismProperty.isomorphisms C :=
  rfl

noncomputable section Bridge

variable {C}

private def pushoutCoconeOfCokernelCofork {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (w : f ≫ g = 0) : PushoutCocone (0 : X ⟶ (0 : C)) f :=
  PushoutCocone.mk (0 : (0 : C) ⟶ Z) g (by simp [w])

private def isColimitPushoutOfIsColimitCokernel {X Y Z : C} (f : X ⟶ Y)
    (g : Y ⟶ Z) (w : f ≫ g = 0) (hc : IsColimit (CokernelCofork.ofπ g w)) :
    IsColimit (pushoutCoconeOfCokernelCofork f g w) := by
  let t := pushoutCoconeOfCokernelCofork f g w
  refine PushoutCocone.IsColimit.mk (eq := t.condition) ?_ ?_ ?_ ?_
  · intro s
    have h_f_s_inr_zero : f ≫ s.inr = 0 := by
      have h_left : (0 : X ⟶ (0 : C)) ≫ s.inl = 0 := by simp
      calc f ≫ s.inr = (0 : X ⟶ (0 : C)) ≫ s.inl := s.condition.symm
        _ = 0 := h_left
    exact hc.desc (CokernelCofork.ofπ s.inr h_f_s_inr_zero)
  · intro s
    have h_f_s_inr_zero : f ≫ s.inr = 0 := by
      have h_left : (0 : X ⟶ (0 : C)) ≫ s.inl = 0 := by simp
      calc f ≫ s.inr = (0 : X ⟶ (0 : C)) ≫ s.inl := s.condition.symm
        _ = 0 := h_left
    change (0 : (0 : C) ⟶ Z) ≫ hc.desc (CokernelCofork.ofπ s.inr h_f_s_inr_zero) = s.inl
    have h_zero : (0 : (0 : C) ⟶ Z) ≫ hc.desc (CokernelCofork.ofπ s.inr h_f_s_inr_zero) =
        (0 : (0 : C) ⟶ s.pt) := by simp
    have h_s_inl : s.inl = (0 : (0 : C) ⟶ s.pt) :=
      (isZero_zero C).eq_of_src _ _
    rw [h_zero, h_s_inl]
  · intro s
    have h_f_s_inr_zero : f ≫ s.inr = 0 := by
      have h_left : (0 : X ⟶ (0 : C)) ≫ s.inl = 0 := by simp
      calc f ≫ s.inr = (0 : X ⟶ (0 : C)) ≫ s.inl := s.condition.symm
        _ = 0 := h_left
    change g ≫ hc.desc (CokernelCofork.ofπ s.inr h_f_s_inr_zero) = s.inr
    exact hc.fac (CokernelCofork.ofπ s.inr h_f_s_inr_zero) WalkingParallelPair.one
  · intro s m hm_inl hm_inr
    have h_f_s_inr_zero : f ≫ s.inr = 0 := by
      have h_left : (0 : X ⟶ (0 : C)) ≫ s.inl = 0 := by simp
      calc f ≫ s.inr = (0 : X ⟶ (0 : C)) ≫ s.inl := s.condition.symm
        _ = 0 := h_left
    have h_m : g ≫ m = s.inr := by
      have hm_inr' : t.inr ≫ m = s.inr := hm_inr
      change g ≫ m = s.inr at hm_inr'
      exact hm_inr'
    have h_uniq : m = hc.desc (CokernelCofork.ofπ s.inr h_f_s_inr_zero) := by
      apply Cofork.IsColimit.hom_ext hc
      calc g ≫ m = s.inr := h_m
        _ = g ≫ hc.desc (CokernelCofork.ofπ s.inr h_f_s_inr_zero) :=
            (hc.fac (CokernelCofork.ofπ s.inr h_f_s_inr_zero) WalkingParallelPair.one).symm
    exact h_uniq

private def isColimitCokernelOfIsPushout {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ (0 : C)) (q : (0 : C) ⟶ Z) (hPush : IsPushout h f q g)
    (w : f ≫ g = 0) : IsColimit (CokernelCofork.ofπ g w) := by
  refine CokernelCofork.IsColimit.ofπ g w ?_ ?_ ?_
  · intro W g' eq'
    have hw : h ≫ (0 : (0 : C) ⟶ W) = f ≫ g' := by simp [eq']
    exact hPush.desc (0 : (0 : C) ⟶ W) g' hw
  · intro W g' eq'
    have hw : h ≫ (0 : (0 : C) ⟶ W) = f ≫ g' := by simp [eq']
    exact hPush.inr_desc (0 : (0 : C) ⟶ W) g' hw
  · intro W g' eq' m hm
    have hw : h ≫ (0 : (0 : C) ⟶ W) = f ≫ g' := by simp [eq']
    have h_desc_inr : g ≫ hPush.desc (0 : (0 : C) ⟶ W) g' hw = g' :=
      hPush.inr_desc (0 : (0 : C) ⟶ W) g' hw
    have h_desc_inl : q ≫ hPush.desc (0 : (0 : C) ⟶ W) g' hw = (0 : (0 : C) ⟶ W) :=
      hPush.inl_desc (0 : (0 : C) ⟶ W) g' hw
    have hm_inr_eq : g ≫ m = g ≫ hPush.desc (0 : (0 : C) ⟶ W) g' hw := by
      calc g ≫ m = g' := hm
        _ = g ≫ hPush.desc (0 : (0 : C) ⟶ W) g' hw := h_desc_inr.symm
    have hqm : q ≫ m = (0 : (0 : C) ⟶ W) := by
      have hq0 : q = (0 : (0 : C) ⟶ Z) := (isZero_zero C).eq_of_src _ _
      rw [hq0]
      simp
    have hm_inl_eq : q ≫ m = q ≫ hPush.desc (0 : (0 : C) ⟶ W) g' hw := by
      calc q ≫ m = (0 : (0 : C) ⟶ W) := hqm
        _ = q ≫ hPush.desc (0 : (0 : C) ⟶ W) g' hw := h_desc_inl.symm
    exact hPush.hom_ext hm_inl_eq hm_inr_eq

/-- Let C be a preadditive Quillen exact category with a zero object
and binary biproducts.

If a short complex A —i→ B —q→ Q is admissible exact, then it is a cofibration sequence in the
standard Waldhausen structure, with q the pushout quotient along A → 0. -/
theorem isCofibrationSequence_of_isAdmissibleExact {S : ShortComplex C}
    (hS : IsAdmissibleExact S) :
    @IsCofibrationSequence C _ _ (waldhausenCategory C) S.X₁ S.X₂ S.X₃ S.f S.g := by
  have hc := isColimit_cokernelCofork_of_isAdmissibleExact hS
  have hp := isColimitPushoutOfIsColimitCokernel S.f S.g S.zero hc
  have hPush : IsPushout (0 : S.X₁ ⟶ (0 : C)) S.f (0 : (0 : C) ⟶ S.X₃) S.g :=
    IsPushout.of_isColimit hp
  exact ⟨isAdmissibleMono_f hS, (0 : S.X₁ ⟶ (0 : C)), (0 : (0 : C) ⟶ S.X₃), hPush⟩

/-- Let C be a preadditive Quillen exact category with a zero object
and binary biproducts.

If a short complex A —i→ B —q→ Q is a cofibration sequence in the standard Waldhausen structure,
then it is admissible exact in C. -/
theorem isAdmissibleExact_of_isCofibrationSequence {S : ShortComplex C}
    (hSeq : @IsCofibrationSequence C _ _ (waldhausenCategory C) S.X₁ S.X₂ S.X₃ S.f S.g) :
    IsAdmissibleExact S := by
  obtain ⟨hf, h, q, hPush⟩ := hSeq
  have hcS : IsColimit (CokernelCofork.ofπ S.g S.zero) :=
    isColimitCokernelOfIsPushout S.f S.g h q hPush S.zero
  exact isAdmissibleExact_of_isAdmissibleMono_isColimit hf hcS

/-- Let C be a preadditive Quillen exact category with a zero object
and binary biproducts.

For a short complex A —i→ B —q→ Q, admissible exactness is equivalent to being a cofibration
sequence in the standard Waldhausen structure. -/
theorem isAdmissibleExact_iff_isCofibrationSequence {S : ShortComplex C} :
    IsAdmissibleExact S ↔
      @IsCofibrationSequence C _ _ (waldhausenCategory C) S.X₁ S.X₂ S.X₃ S.f S.g :=
  ⟨isCofibrationSequence_of_isAdmissibleExact,
    isAdmissibleExact_of_isCofibrationSequence⟩

end Bridge

end CategoryTheory.ExactCategory
