/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BoundedIndImageModels
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Bounded proper image from finite amplitude

The native triangulated proper image preserves boundedness under its
actual finite-amplitude condition, by induction on the amplitude of a
bounded complex along the canonical t-structure.

Source: D'Agnolo--Kashiwara1311.2374v2, Section2 conventions,
Sections3.3--3.4 and4.1--4.4, especially Proposition4.1.5.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.EnhancedConvolutionSourceRequests

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.Pretriangulated
open MathlibExt.AlgebraicGeometry.CompactSupportIndSheaves
open MathlibExt.AlgebraicGeometry.IndSheafPushforwardModels
open MathlibExt.AlgebraicGeometry.BoundedIndImageModels

local instance requestAbelianPreadditive (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X] : Preadditive (IndSheaf k X) := Abelian.toPreadditive

attribute [local instance] HasDerivedCategory.standard

/-- Boundedness transfers along isomorphisms of the derived category. -/
private theorem isBounded_of_iso (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X] {K L : IndDerived k X} (hK : IsBounded k X K)
    (e : K ≅ L) : IsBounded k X L := by
  obtain ⟨a, b, h⟩ := hK
  exact ⟨a, b, fun n hn => (h n hn).of_iso
    ((DerivedCategory.homologyFunctor (IndSheaf k X) n).mapIso e).symm⟩

/-- The middle object of a distinguished triangle with bounded ends is bounded. -/
private theorem isBounded_of_distinguished (k : Type) [Field k] (Y : TopCat.{0})
    [CompactSheafSource k Y] (T : Triangle (IndDerived k Y))
    (hT : T ∈ distTriang (IndDerived k Y)) (h₁ : IsBounded k Y T.obj₁)
    (h₃ : IsBounded k Y T.obj₃) : IsBounded k Y T.obj₂ := by
  obtain ⟨a₁, b₁, h₁⟩ := h₁
  obtain ⟨a₃, b₃, h₃⟩ := h₃
  refine ⟨min a₁ a₃, max b₁ b₃, fun n hn => ?_⟩
  have hX₁ : IsZero ((DerivedCategory.homologyFunctor (IndSheaf k Y) n).obj T.obj₁) := by
    apply h₁
    rcases hn with hn | hn
    · exact Or.inl (lt_of_lt_of_le hn (min_le_left a₁ a₃))
    · exact Or.inr (lt_of_le_of_lt (le_max_left b₁ b₃) hn)
  have hX₃ : IsZero ((DerivedCategory.homologyFunctor (IndSheaf k Y) n).obj T.obj₃) := by
    apply h₃
    rcases hn with hn | hn
    · exact Or.inl (lt_of_lt_of_le hn (min_le_right a₁ a₃))
    · exact Or.inr (lt_of_le_of_lt (le_max_right b₁ b₃) hn)
  exact (DerivedCategory.HomologySequence.exact₂ T hT n).isZero_of_both_isZero hX₁ hX₃

/-- The proper image of a stalk complex is bounded by the amplitude condition. -/
private theorem isBounded_map_single (k : Type) [Field k] (X Y : TopCat.{0})
    [CompactSheafSource k X] [CompactSheafSource k Y] (f : X ⟶ Y)
    (P : CompactPushforwardSource k f) (D : IndPushforwardSource k f P)
    [(indProperImage k f P D).Additive] (E : DerivedIndPushforwardSource k f P D)
    [(derivedIndProperImage k f P D E).CommShift ℤ]
    (h : FiniteProperImageAmplitude k f P D E) (c : ℤ) (K₀ : IndSheaf k X) :
    IsBounded k Y ((derivedIndProperImage k f P D E).obj
      ((DerivedCategory.singleFunctor (IndSheaf k X) c).obj K₀)) := by
  obtain ⟨a, b, hamp⟩ := h
  refine ⟨a + c, b + c, fun n hn => ?_⟩
  have h0 : IsZero ((DerivedCategory.homologyFunctor (IndSheaf k Y) (-c + n)).obj
      ((derivedIndProperImage k f P D E).obj
        ((DerivedCategory.singleFunctor (IndSheaf k X) 0).obj K₀))) := by
    apply hamp
    rcases hn with hn | hn
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have e1 : (DerivedCategory.singleFunctor (IndSheaf k X) c).obj K₀ ≅
      ((DerivedCategory.singleFunctor (IndSheaf k X) 0).obj K₀)⟦-c⟧ :=
    ((DerivedCategory.singleFunctors (IndSheaf k X)).shiftIso (-c) c 0
      (neg_add_cancel c)).symm.app K₀
  have e2 := ((derivedIndProperImage k f P D E).commShiftIso (-c)).app
    ((DerivedCategory.singleFunctor (IndSheaf k X) 0).obj K₀)
  have e3 := ((DerivedCategory.homologyFunctor (IndSheaf k Y) 0).shiftIso
    (-c) n (-c + n) rfl).app
    ((derivedIndProperImage k f P D E).obj
      ((DerivedCategory.singleFunctor (IndSheaf k X) 0).obj K₀))
  simp only [DerivedCategory.shift_homologyFunctor] at e3
  exact h0.of_iso ((DerivedCategory.homologyFunctor (IndSheaf k Y) n).mapIso
    ((derivedIndProperImage k f P D E).mapIso e1 ≪≫ e2) ≪≫ e3)

/-- A complex of amplitude at most `m` maps to a bounded complex. -/
private theorem isBounded_of_isGE_of_isLE (k : Type) [Field k] (X Y : TopCat.{0})
    [CompactSheafSource k X] [CompactSheafSource k Y] (f : X ⟶ Y)
    (P : CompactPushforwardSource k f) (D : IndPushforwardSource k f P)
    [(indProperImage k f P D).Additive] (E : DerivedIndPushforwardSource k f P D)
    [(derivedIndProperImage k f P D E).CommShift ℤ]
    [(derivedIndProperImage k f P D E).IsTriangulated]
    (h : FiniteProperImageAmplitude k f P D E) (m : ℕ) (c : ℤ) (K : IndDerived k X)
    (hGE : K.IsGE c) (hLE : K.IsLE (c + m)) :
    IsBounded k Y ((derivedIndProperImage k f P D E).obj K) := by
  induction m generalizing c K with
  | zero =>
    have hLE' : K.IsLE c := by simpa using hLE
    obtain ⟨Y₀, ⟨e⟩⟩ :=
      DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K c
    exact isBounded_of_iso k Y (isBounded_map_single k X Y f P D E h c Y₀)
      (((derivedIndProperImage k f P D E).mapIso e).symm)
  | succ m ih =>
    obtain ⟨A, B, hAle, hBge, g₁, g₂, g₃, hT⟩ :=
      DerivedCategory.TStructure.t.exists_triangle K c (c + 1) rfl
    have hBge' : B.IsGE (c + 1) :=
      (DerivedCategory.TStructure.t.ge_iff_isGE B (c + 1)).mp hBge
    have hAge : A.IsGE c := by
      rw [DerivedCategory.isGE_iff]
      intro i hi
      have hX₁ : IsZero
          ((DerivedCategory.homologyFunctor (IndSheaf k X) (i - 1)).obj B) :=
        (DerivedCategory.isGE_iff B (c + 1)).mp hBge' (i - 1) (by omega)
      have hX₃ : IsZero ((DerivedCategory.homologyFunctor (IndSheaf k X) i).obj K) :=
        (DerivedCategory.isGE_iff K c).mp hGE i hi
      exact (DerivedCategory.HomologySequence.exact₁ (Triangle.mk g₁ g₂ g₃) hT
        (i - 1) i (sub_add_cancel i 1)).isZero_of_both_isZero hX₁ hX₃
    have hAle' : A.IsLE c :=
      (DerivedCategory.TStructure.t.le_iff_isLE A c).mp hAle
    obtain ⟨Y₀, ⟨eA⟩⟩ :=
      DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE A c
    have hFA : IsBounded k Y ((derivedIndProperImage k f P D E).obj A) :=
      isBounded_of_iso k Y (isBounded_map_single k X Y f P D E h c Y₀)
        (((derivedIndProperImage k f P D E).mapIso eA).symm)
    have hBle' : B.IsLE (c + 1 + m) := by
      rw [DerivedCategory.isLE_iff]
      intro i hi
      have hX₁ : IsZero ((DerivedCategory.homologyFunctor (IndSheaf k X) i).obj K) :=
        (DerivedCategory.isLE_iff K _).mp hLE i (by omega)
      have hX₃ : IsZero
          ((DerivedCategory.homologyFunctor (IndSheaf k X) (i + 1)).obj A) :=
        (DerivedCategory.isLE_iff A c).mp hAle' (i + 1) (by omega)
      exact (DerivedCategory.HomologySequence.exact₃ (Triangle.mk g₁ g₂ g₃) hT
        i (i + 1) rfl).isZero_of_both_isZero hX₁ hX₃
    have hFB : IsBounded k Y ((derivedIndProperImage k f P D E).obj B) :=
      ih (c + 1) B hBge' hBle'
    have hT' := (derivedIndProperImage k f P D E).map_distinguished
      (Triangle.mk g₁ g₂ g₃) hT
    exact isBounded_of_distinguished k Y _ hT' hFA hFB

/-- The same native triangulated proper image preserves boundedness under its actual
finite-amplitude condition. -/
theorem actual_bounded_proper_image_of_finite_amplitude (k : Type) [Field k]
    (X Y : TopCat.{0}) [CompactSheafSource k X] [CompactSheafSource k Y]
    (f : X ⟶ Y) (P : CompactPushforwardSource k f) (D : IndPushforwardSource k f P)
    [(indProperImage k f P D).Additive] (E : DerivedIndPushforwardSource k f P D)
    [(derivedIndProperImage k f P D E).CommShift ℤ]
    [(derivedIndProperImage k f P D E).IsTriangulated]
    (h : FiniteProperImageAmplitude k f P D E) : BoundedProperImageSource k f P D E := by
  refine ⟨fun K => ?_⟩
  obtain ⟨c, d, hKb⟩ := K.property
  rcases le_total c d with hcd | hcd
  · have hdc : c + (((d - c).toNat : ℕ) : ℤ) = d := by
      rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ d - c)]
      omega
    have hGEd : K.obj.IsGE c :=
      (DerivedCategory.isGE_iff K.obj c).mpr fun i hi => hKb i (Or.inl hi)
    have hLEd : K.obj.IsLE (c + (((d - c).toNat : ℕ) : ℤ)) := by
      rw [hdc]
      exact (DerivedCategory.isLE_iff K.obj d).mpr fun i hi => hKb i (Or.inr hi)
    exact isBounded_of_isGE_of_isLE k X Y f P D E h _ c K.obj hGEd hLEd
  · have hGEd : K.obj.IsGE d :=
      (DerivedCategory.isGE_iff K.obj d).mpr fun i hi => hKb i (Or.inl (by omega))
    have hLEd : K.obj.IsLE (d + (((0 : ℕ)) : ℤ)) := by
      simpa using (DerivedCategory.isLE_iff K.obj d).mpr fun i hi => hKb i (Or.inr hi)
    exact isBounded_of_isGE_of_isLE k X Y f P D E h 0 d K.obj hGEd hLEd

end WantedExt.AlgebraicGeometry.EnhancedConvolutionSourceRequests
