/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.RightMappingBrown
public import MathlibExt.AlgebraicTopology.ModelCategory.FibrantBrownPathComparison

/-!
# Right full faithfulness of the actual categorical-fibration factor

The genuine Brown factorization supplies a trivial-fibration retraction
and a whole good path-object comparison between the two original factor
maps. Its two true trivial-fibration endpoints and two-out-of-three give
right-mapping weakness at every individual vertex of the intermediate
object. The original map need not already be a categorical equivalence.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra Opposite
open scoped Simplicial

namespace SSet.JoyalDwyerKan

attribute [local instance] JoyalSSet.modelCategory

private theorem cofibrant (A : JoyalSSet.{u}) : IsCofibrant A := by
  rw [isCofibrant_iff_of_isInitial (initial.to A) initialIsInitial, cofibration_iff]
  change JoyalSSet.modelCategory.categoryWithCofibrations.cofibrations (initial.to A)
  rw [JoyalSSet.modelCategory_cofibrations]
  have hI : IsInitial (JoyalSSet.forget.obj (⊥_ JoyalSSet.{u})) :=
    (initialIsInitial : IsInitial (⊥_ JoyalSSet.{u})).isInitialObj JoyalSSet.forget _
  let _ : Mono (JoyalSSet.forget.map (initial.to A)) := hI.mono_from _
  exact JoyalSSet.forget.mono_of_mono_map inferInstance

private theorem raw_weak {A B : JoyalSSet.{u}} (g : A ⟶ B) [WeakEquivalence g] :
    categoricalEquivalences (JoyalSSet.forget.map g) := by
  have h := (weakEquivalence_iff g).mp inferInstance
  change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences g at h
  rw [JoyalSSet.modelCategory_weakEquivalences] at h
  exact h

/-- Right full faithfulness passes to the actual categorical-fibration factor at every original intermediate
  vertex, using the genuine Brown retraction and good path object. -/
theorem fibrantBrownFactorization_fullyFaithful {X Y : SSet.{u}} [Quasicategory X]
    [Quasicategory Y] (f : X ⟶ Y)
    (h : FibrantBrownFactorization (JoyalSSet.ofSSet.map f))
    (hf : dwyerKanFullyFaithful f) : dwyerKanFullyFaithful (JoyalSSet.forget.map h.p) := by
  let _ : IsFibrant (JoyalSSet.ofSSet.obj X) :=
    (JoyalSSet.isFibrant_iff_quasicategory _).mpr (show Quasicategory X from inferInstance)
  let _ : IsFibrant (JoyalSSet.ofSSet.obj Y) :=
    (JoyalSSet.isFibrant_iff_quasicategory _).mpr (show Quasicategory Y from inferInstance)
  let _ : IsFibrant h.Z := isFibrant_of_fibration h.r
  let _ : Quasicategory (JoyalSSet.forget.obj h.Z) :=
    (JoyalSSet.isFibrant_iff_quasicategory h.Z).mp (show IsFibrant h.Z from inferInstance)
  let _ : IsCofibrant h.Z := cofibrant h.Z
  obtain ⟨P, hP, h₀, h₁, q, hq₀, hq₁⟩ :=
    FibrantBrownFactorization.exists_good_pathComparison (JoyalSSet.ofSSet.map f) h
  let _ : P.IsGood := hP
  let _ : Quasicategory (JoyalSSet.forget.obj P.P) :=
    (JoyalSSet.isFibrant_iff_quasicategory P.P).mp (show IsFibrant P.P from inferInstance)
  let _ : WeakEquivalence P.p₀ := ((mem_trivialFibrations_iff (f := P.p₀)).mp h₀).2
  let _ : WeakEquivalence P.p₁ := ((mem_trivialFibrations_iff (f := P.p₁)).mp h₁).2
  let r : JoyalSSet.forget.obj h.Z ⟶ X := JoyalSSet.forget.map h.r
  let a : JoyalSSet.forget.obj h.Z ⟶ JoyalSSet.forget.obj P.P := JoyalSSet.forget.map q
  let p₀ : JoyalSSet.forget.obj P.P ⟶ Y := JoyalSSet.forget.map P.p₀
  let p₁ : JoyalSSet.forget.obj P.P ⟶ Y := JoyalSSet.forget.map P.p₁
  have hrCat : categoricalEquivalences r := raw_weak h.r
  have h₀Cat : categoricalEquivalences p₀ := raw_weak P.p₀
  have h₁Cat : categoricalEquivalences p₁ := raw_weak P.p₁
  have ha₀ : a ≫ p₀ = r ≫ f := by
    exact (JoyalSSet.forget.map_comp _ _).symm.trans
      ((congrArg (fun g => JoyalSSet.forget.map g) hq₀).trans
        (JoyalSSet.forget.map_comp _ _))
  have ha₁ : a ≫ p₁ = JoyalSSet.forget.map h.p :=
    (JoyalSSet.forget.map_comp _ _).symm.trans
      (congrArg (fun g => JoyalSSet.forget.map g) hq₁)
  intro x y
  have hr : realizationWeakEquivalences (mappingSpaceRight.map (JoyalSSet.forget.obj h.Z) x y r) :=
    hrCat.rightMappingSpaceMap_weak x y
  have hrf : realizationWeakEquivalences (mappingSpaceRight.map (JoyalSSet.forget.obj h.Z) x y (r ≫ f)) := by
    rw [mappingSpaceRight.map_comp]
    exact realizationWeakEquivalences.comp_mem _ _ hr (hf (x ≫ r) (y ≫ r))
  have h₀w : realizationWeakEquivalences
      (mappingSpaceRight.map (JoyalSSet.forget.obj P.P) (x ≫ a) (y ≫ a) p₀) :=
    h₀Cat.rightMappingSpaceMap_weak (x ≫ a) (y ≫ a)
  have h₁w : realizationWeakEquivalences
      (mappingSpaceRight.map (JoyalSSet.forget.obj P.P) (x ≫ a) (y ≫ a) p₁) :=
    h₁Cat.rightMappingSpaceMap_weak (x ≫ a) (y ≫ a)
  have ha₀w : realizationWeakEquivalences (mappingSpaceRight.map (JoyalSSet.forget.obj h.Z) x y (a ≫ p₀)) := by
    rw [ha₀]
    exact hrf
  rw [mappingSpaceRight.map_comp] at ha₀w
  have haw : realizationWeakEquivalences (mappingSpaceRight.map (JoyalSSet.forget.obj h.Z) x y a) :=
    realizationWeakEquivalences.of_postcomp _ _ h₀w ha₀w
  have ha₁w : realizationWeakEquivalences (mappingSpaceRight.map (JoyalSSet.forget.obj h.Z) x y (a ≫ p₁)) := by
    rw [mappingSpaceRight.map_comp]
    exact realizationWeakEquivalences.comp_mem _ _ haw h₁w
  rwa [ha₁] at ha₁w

end SSet.JoyalDwyerKan
