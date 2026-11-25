/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationFunctor

/-!
# Comparing complete and finite horizontal-filtration stages

At a nonnegative integer index, the complete `EInt`-indexed horizontal
filtration is canonically isomorphic to the original natural-number stage.
This file packages the carrier equality as an isomorphism and proves that it
intertwines inclusions into the total complex, bicomplex maps, and increasing
the filtration index.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- A nonnegative complete-filtration stage, canonically identified with its
finite natural-number stage. -/
noncomputable def horizontalCompleteFilteredTotalComplexFiniteIso
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (a : ℤ) (ha : 0 ≤ a) :
    horizontalCompleteFilteredTotalComplex K (a : EInt) ≅
      horizontalFilteredTotalComplex K a.toNat :=
  eqToIso (horizontalCompleteFilteredTotalComplex_coe_of_nonneg K a ha)

/-- The complete-to-finite stage isomorphism preserves the inclusion into
the total complex. -/
@[reassoc (attr := simp)]
theorem horizontalCompleteFilteredTotalComplexFiniteIso_hom_toTotal
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (a : ℤ) (ha : 0 ≤ a) :
    (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom ≫
        horizontalFilteredTotalComplexToTotal K a.toNat =
      horizontalCompleteFilteredTotalToTotal K (a : EInt) := by
  let U := horizontalCompleteFilteredTotalMonoOver K (a : EInt)
  let V := (horizontalTotalFiltration K).toMonoOver.obj a.toNat
  have hMono : U = V := by
    dsimp only [U, V, horizontalCompleteFilteredTotalMonoOver,
      WithBotTop.rec_coe]
    rw [ite_eq_left ha]
  let hObj : U.obj.left = V.obj.left :=
    congrArg (fun Z => Z.obj.left) hMono
  have arrow_transport : ∀ (X Y : MonoOver
      (K.total (ComplexShape.down ℕ))) (h : X = Y),
      eqToHom (congrArg (fun Z => Z.obj.left) h) ≫ Y.arrow = X.arrow := by
    intro X Y h
    cases h
    simp
  have hArrow : eqToHom hObj ≫ V.arrow = U.arrow :=
    arrow_transport U V hMono
  change eqToHom
      (horizontalCompleteFilteredTotalComplex_coe_of_nonneg K a ha) ≫
        horizontalFilteredTotalComplexToTotal K a.toNat = U.arrow
  have hEq :
      horizontalCompleteFilteredTotalComplex_coe_of_nonneg K a ha = hObj :=
    Subsingleton.elim _ _
  rw [hEq]
  exact hArrow

/-- The complete-to-finite stage isomorphisms are natural in the
bicomplex. -/
theorem horizontalCompleteFilteredTotalComplexFiniteIso_naturality
    (f : K ⟶ L) (a : ℤ) (ha : 0 ≤ a) :
    (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom ≫
        horizontalFilteredTotalComplexMapOfBicomplex f a.toNat =
      horizontalCompleteFilteredTotalComplexMapOfBicomplex f (a : EInt) ≫
        (horizontalCompleteFilteredTotalComplexFiniteIso L a ha).hom := by
  apply (cancel_mono
    (horizontalFilteredTotalComplexToTotal L a.toNat)).1
  calc
    ((horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom ≫
          horizontalFilteredTotalComplexMapOfBicomplex f a.toNat) ≫
        horizontalFilteredTotalComplexToTotal L a.toNat =
      (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom ≫
        (horizontalFilteredTotalComplexMapOfBicomplex f a.toNat ≫
          horizontalFilteredTotalComplexToTotal L a.toNat) :=
      Category.assoc _ _ _
    _ = (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom ≫
        (horizontalFilteredTotalComplexToTotal K a.toNat ≫
          total.map f (ComplexShape.down ℕ)) := by
      rw [horizontalFilteredTotalComplexMapOfBicomplex_toTotal]
    _ = ((horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom ≫
          horizontalFilteredTotalComplexToTotal K a.toNat) ≫
        total.map f (ComplexShape.down ℕ) :=
      (Category.assoc _ _ _).symm
    _ = horizontalCompleteFilteredTotalToTotal K (a : EInt) ≫
        total.map f (ComplexShape.down ℕ) := by
      rw [horizontalCompleteFilteredTotalComplexFiniteIso_hom_toTotal]
    _ = horizontalCompleteFilteredTotalComplexMapOfBicomplex f (a : EInt) ≫
        horizontalCompleteFilteredTotalToTotal L (a : EInt) := by
      rw [horizontalCompleteFilteredTotalComplexMapOfBicomplex_toTotal]
    _ = horizontalCompleteFilteredTotalComplexMapOfBicomplex f (a : EInt) ≫
        ((horizontalCompleteFilteredTotalComplexFiniteIso L a ha).hom ≫
          horizontalFilteredTotalComplexToTotal L a.toNat) := by
      rw [horizontalCompleteFilteredTotalComplexFiniteIso_hom_toTotal]
    _ = (horizontalCompleteFilteredTotalComplexMapOfBicomplex f (a : EInt) ≫
          (horizontalCompleteFilteredTotalComplexFiniteIso L a ha).hom) ≫
        horizontalFilteredTotalComplexToTotal L a.toNat :=
      (Category.assoc _ _ _).symm

/-- The complete-to-finite stage isomorphisms intertwine transitions between
nonnegative finite indices. -/
theorem horizontalCompleteFilteredTotalComplexFiniteIso_transition
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (a b : ℤ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom ≫
        horizontalFilteredTotalComplexMap K (Int.toNat_le_toNat hab) =
      horizontalCompleteFilteredTotalMap K
          (WithBotTop.coe_monotone hab) ≫
        (horizontalCompleteFilteredTotalComplexFiniteIso K b
          (ha.trans hab)).hom := by
  apply (cancel_mono
    (horizontalFilteredTotalComplexToTotal K b.toNat)).1
  calc
    ((horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom ≫
          horizontalFilteredTotalComplexMap K
            (Int.toNat_le_toNat hab)) ≫
        horizontalFilteredTotalComplexToTotal K b.toNat =
      (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom ≫
        (horizontalFilteredTotalComplexMap K
            (Int.toNat_le_toNat hab) ≫
          horizontalFilteredTotalComplexToTotal K b.toNat) :=
      Category.assoc _ _ _
    _ = (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom ≫
        horizontalFilteredTotalComplexToTotal K a.toNat := by
      rw [horizontalFilteredTotalComplexMap_toTotal]
    _ = horizontalCompleteFilteredTotalToTotal K (a : EInt) :=
      horizontalCompleteFilteredTotalComplexFiniteIso_hom_toTotal K a ha
    _ = horizontalCompleteFilteredTotalMap K
          (WithBotTop.coe_monotone hab) ≫
        horizontalCompleteFilteredTotalToTotal K (b : EInt) := by
      rw [horizontalCompleteFilteredTotalMap_toTotal]
    _ = horizontalCompleteFilteredTotalMap K
          (WithBotTop.coe_monotone hab) ≫
        ((horizontalCompleteFilteredTotalComplexFiniteIso K b
            (ha.trans hab)).hom ≫
          horizontalFilteredTotalComplexToTotal K b.toNat) := by
      rw [horizontalCompleteFilteredTotalComplexFiniteIso_hom_toTotal]
    _ = (horizontalCompleteFilteredTotalMap K
            (WithBotTop.coe_monotone hab) ≫
          (horizontalCompleteFilteredTotalComplexFiniteIso K b
            (ha.trans hab)).hom) ≫
        horizontalFilteredTotalComplexToTotal K b.toNat :=
      (Category.assoc _ _ _).symm

end HomologicalComplex₂

end
