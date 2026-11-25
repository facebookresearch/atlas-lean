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

public import MathlibExt.KTheory.Waldhausen.K0.Basic
public import MathlibExt.KTheory.Waldhausen.K0.Functor
public import MathlibExt.KTheory.Exact.K0.Basic
public import MathlibExt.KTheory.Exact.K0.Functor
public import MathlibExt.CategoryTheory.Waldhausen.Exact
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# `K₀` comparison for the exact-category Waldhausen structure

For a Quillen exact category `C`, the standard Waldhausen structure
`ExactCategory.waldhausenCategory C` has cofibrations the admissible
monomorphisms and weak equivalences the isomorphisms. Its Waldhausen
`K₀` coincides with the algebraic `K₀` via the canonical isomorphism
induced by the identity on `Skeleton C`.

## Main definitions

* `WaldhausenKTheory.K0.toExact` — `AddCommGrp` map
  `K₀(ExactCategory.waldhausenCategory C) →+ K₀(C)` for the exact structure.
* `WaldhausenKTheory.K0.fromExact` — the inverse.
* `WaldhausenKTheory.K0.exactIso` — the `AddCommGrpCat` isomorphism.
* `WaldhausenKTheory.K0.toExact_naturality` — hom-side naturality for additive
  exact functors across universes.

## Implementation notes

Both maps are defined by the two existing universal properties
`WaldhausenKTheory.K0.lift` and `AlgebraicKTheory.K0.lift` on local
generator maps `Skeleton C → K₀` (`s ↦ [fromSkeleton.obj s]`). For
`fromExact` the admissibility exact hypothesis is turned into a
cofibration sequence by
`ExactCategory.isCofibrationSequence_of_isAdmissibleExact`. For
`toExact` weak equivalences are isomorphisms via
`MorphismProperty.isomorphisms.iff` and cofiber additivity is reduced to
admissible exactness using `IsCofibrationSequence.comp_eq_zero` and
`ExactCategory.isAdmissibleExact_of_isCofibrationSequence`.
Skeleton bookkeeping uses `fromSkeleton` and
`fromSkeletonToSkeletonIso`.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe v u v' u'

namespace WaldhausenKTheory

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- `K₀` comparison map from the exact Waldhausen structure to the algebraic `K₀`. -/
noncomputable def K0.toExact :
    @WaldhausenKTheory.K0 C _ _ (ExactCategory.waldhausenCategory C) →+
      AlgebraicKTheory.K0 C := by
  let φ : Skeleton C → AlgebraicKTheory.K0 C :=
    fun s => AlgebraicKTheory.K0.mk ((fromSkeleton C).obj s)
  have h_we :
      ∀ {X Y : C} (f : X ⟶ Y),
        @IsWeakEquivalence C _ _ (ExactCategory.waldhausenCategory C) X Y f →
          φ (toSkeleton X) = φ (toSkeleton Y) := by
    intro X Y f hf
    have hf' : (MorphismProperty.isomorphisms C) f := hf
    have hIso : IsIso f :=
      (MorphismProperty.isomorphisms.iff (C := C) f).mp hf'
    have e : X ≅ Y := asIso f
    have h1 :
        AlgebraicKTheory.K0.mk ((fromSkeleton C).obj (toSkeleton X)) =
          AlgebraicKTheory.K0.mk X :=
      AlgebraicKTheory.K0.mk_congr_of_iso (fromSkeletonToSkeletonIso X)
    have h2 :
        AlgebraicKTheory.K0.mk ((fromSkeleton C).obj (toSkeleton Y)) =
          AlgebraicKTheory.K0.mk Y :=
      AlgebraicKTheory.K0.mk_congr_of_iso (fromSkeletonToSkeletonIso Y)
    have h3 : AlgebraicKTheory.K0.mk X = AlgebraicKTheory.K0.mk Y :=
      AlgebraicKTheory.K0.mk_congr_of_iso e
    change
      AlgebraicKTheory.K0.mk ((fromSkeleton C).obj (toSkeleton X)) =
        AlgebraicKTheory.K0.mk ((fromSkeleton C).obj (toSkeleton Y))
    rw [h1, h2, h3]
  have h_cofib :
      ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
        @IsCofibrationSequence C _ _
          (ExactCategory.waldhausenCategory C) X Y Z f g →
          φ (toSkeleton Y) = φ (toSkeleton X) + φ (toSkeleton Z) := by
    intro X Y Z f g hSeq
    have w : f ≫ g = 0 :=
      @IsCofibrationSequence.comp_eq_zero C _ _
        (ExactCategory.waldhausenCategory C) _ X Y Z f g hSeq
    let S : ShortComplex C := ShortComplex.mk f g w
    have hS : ExactCategory.IsAdmissibleExact S :=
      ExactCategory.isAdmissibleExact_of_isCofibrationSequence (S := S) hSeq
    have hAdd : AlgebraicKTheory.K0.mk S.X₂ =
        AlgebraicKTheory.K0.mk S.X₁ + AlgebraicKTheory.K0.mk S.X₃ :=
      AlgebraicKTheory.K0.mk_eq_of_admissibleExact hS
    have hY :
        AlgebraicKTheory.K0.mk ((fromSkeleton C).obj (toSkeleton Y)) =
          AlgebraicKTheory.K0.mk Y :=
      AlgebraicKTheory.K0.mk_congr_of_iso (fromSkeletonToSkeletonIso Y)
    have hX :
        AlgebraicKTheory.K0.mk ((fromSkeleton C).obj (toSkeleton X)) =
          AlgebraicKTheory.K0.mk X :=
      AlgebraicKTheory.K0.mk_congr_of_iso (fromSkeletonToSkeletonIso X)
    have hZ :
        AlgebraicKTheory.K0.mk ((fromSkeleton C).obj (toSkeleton Z)) =
          AlgebraicKTheory.K0.mk Z :=
      AlgebraicKTheory.K0.mk_congr_of_iso (fromSkeletonToSkeletonIso Z)
    have hAdd' : AlgebraicKTheory.K0.mk Y =
        AlgebraicKTheory.K0.mk X + AlgebraicKTheory.K0.mk Z := by
      simpa [S] using hAdd
    change
      AlgebraicKTheory.K0.mk ((fromSkeleton C).obj (toSkeleton Y)) =
        AlgebraicKTheory.K0.mk ((fromSkeleton C).obj (toSkeleton X)) +
          AlgebraicKTheory.K0.mk ((fromSkeleton C).obj (toSkeleton Z))
    rw [hY, hX, hZ, hAdd']
  refine @WaldhausenKTheory.K0.lift C _ _ (ExactCategory.waldhausenCategory C)
    (AlgebraicKTheory.K0 C) _ φ h_we h_cofib

/-- The inverse comparison from the algebraic `K₀` to the exact Waldhausen `K₀`. -/
noncomputable def K0.fromExact :
    AlgebraicKTheory.K0 C →+
      @WaldhausenKTheory.K0 C _ _ (ExactCategory.waldhausenCategory C) := by
  let φ : Skeleton C →
      @WaldhausenKTheory.K0 C _ _ (ExactCategory.waldhausenCategory C) :=
    fun s =>
      @WaldhausenKTheory.K0.mk C _ _
        (ExactCategory.waldhausenCategory C) ((fromSkeleton C).obj s)
  have hφ :
      ∀ (S : ShortComplex C),
        ExactCategory.IsAdmissibleExact S →
          φ (toSkeleton S.X₂) = φ (toSkeleton S.X₁) + φ (toSkeleton S.X₃) := by
    intro S hS
    have hSeq :
        @IsCofibrationSequence C _ _
          (ExactCategory.waldhausenCategory C) S.X₁ S.X₂ S.X₃ S.f S.g :=
      ExactCategory.isCofibrationSequence_of_isAdmissibleExact hS
    have hAdd :
        @WaldhausenKTheory.K0.mk C _ _
            (ExactCategory.waldhausenCategory C) S.X₂ =
          @WaldhausenKTheory.K0.mk C _ _
              (ExactCategory.waldhausenCategory C) S.X₁ +
            @WaldhausenKTheory.K0.mk C _ _
              (ExactCategory.waldhausenCategory C) S.X₃ :=
      @WaldhausenKTheory.K0.mk_eq_of_cofibrationSequence C _ _
        (ExactCategory.waldhausenCategory C) _ _ _ _ _ hSeq
    have h1 :
        @WaldhausenKTheory.K0.mk C _ _
            (ExactCategory.waldhausenCategory C)
            ((fromSkeleton C).obj (toSkeleton S.X₂)) =
          @WaldhausenKTheory.K0.mk C _ _
            (ExactCategory.waldhausenCategory C) S.X₂ :=
      @WaldhausenKTheory.K0.mk_eq_of_iso C _ _
        (ExactCategory.waldhausenCategory C) _ _
        (fromSkeletonToSkeletonIso S.X₂)
    have h2 :
        @WaldhausenKTheory.K0.mk C _ _
            (ExactCategory.waldhausenCategory C)
            ((fromSkeleton C).obj (toSkeleton S.X₁)) =
          @WaldhausenKTheory.K0.mk C _ _
            (ExactCategory.waldhausenCategory C) S.X₁ :=
      @WaldhausenKTheory.K0.mk_eq_of_iso C _ _
        (ExactCategory.waldhausenCategory C) _ _
        (fromSkeletonToSkeletonIso S.X₁)
    have h3 :
        @WaldhausenKTheory.K0.mk C _ _
            (ExactCategory.waldhausenCategory C)
            ((fromSkeleton C).obj (toSkeleton S.X₃)) =
          @WaldhausenKTheory.K0.mk C _ _
            (ExactCategory.waldhausenCategory C) S.X₃ :=
      @WaldhausenKTheory.K0.mk_eq_of_iso C _ _
        (ExactCategory.waldhausenCategory C) _ _
        (fromSkeletonToSkeletonIso S.X₃)
    change
      @WaldhausenKTheory.K0.mk C _ _
          (ExactCategory.waldhausenCategory C)
          ((fromSkeleton C).obj (toSkeleton S.X₂)) =
        @WaldhausenKTheory.K0.mk C _ _
            (ExactCategory.waldhausenCategory C)
            ((fromSkeleton C).obj (toSkeleton S.X₁)) +
          @WaldhausenKTheory.K0.mk C _ _
            (ExactCategory.waldhausenCategory C)
            ((fromSkeleton C).obj (toSkeleton S.X₃))
    rw [h1, h2, h3, hAdd]
  exact AlgebraicKTheory.K0.lift (φ := φ) (hφ := hφ)

@[simp]
lemma K0.toExact_mk (X : C) :
    @K0.toExact C _ _ _ _ _ (@K0.mk C _ _
        (ExactCategory.waldhausenCategory C) X) =
      AlgebraicKTheory.K0.mk X := by
  have h : @K0.toExact C _ _ _ _ _ (@K0.mk C _ _
      (ExactCategory.waldhausenCategory C) X) =
      AlgebraicKTheory.K0.mk ((fromSkeleton C).obj (toSkeleton X)) := by
    simp only [K0.toExact, WaldhausenKTheory.K0.lift_mk]
  rw [h, AlgebraicKTheory.K0.mk_congr_of_iso (fromSkeletonToSkeletonIso X)]

@[simp]
lemma K0.fromExact_mk (X : C) :
    @K0.fromExact C _ _ _ _ _ (AlgebraicKTheory.K0.mk X) =
      @K0.mk C _ _ (ExactCategory.waldhausenCategory C) X := by
  have h : @K0.fromExact C _ _ _ _ _ (AlgebraicKTheory.K0.mk X) =
      @WaldhausenKTheory.K0.mk C _ _ (ExactCategory.waldhausenCategory C)
        ((fromSkeleton C).obj (toSkeleton X)) := by
    simp only [K0.fromExact, AlgebraicKTheory.K0.lift_mk]
  rw [h, @WaldhausenKTheory.K0.mk_eq_of_iso C _ _
    (ExactCategory.waldhausenCategory C) _ _ (fromSkeletonToSkeletonIso X)]

/-- Canonical `AddCommGrpCat` isomorphism between the exact Waldhausen `K₀`
and the algebraic `K₀`. -/
noncomputable def K0.exactIso :
    AddCommGrpCat.of (@WaldhausenKTheory.K0 C _ _
        (ExactCategory.waldhausenCategory C)) ≅
      AddCommGrpCat.of (AlgebraicKTheory.K0 C) where
  hom := AddCommGrpCat.ofHom (K0.toExact C)
  inv := AddCommGrpCat.ofHom (K0.fromExact C)
  hom_inv_id := by
    ext : 1
    dsimp
    apply @WaldhausenKTheory.K0.hom_ext C _ _
      (ExactCategory.waldhausenCategory C)
      (@WaldhausenKTheory.K0 C _ _
        (ExactCategory.waldhausenCategory C)) _
    intro X
    simp [K0.toExact_mk, K0.fromExact_mk]
  inv_hom_id := by
    ext : 1
    dsimp
    apply AlgebraicKTheory.K0.hom_ext (C := C)
    intro X
    simp [K0.toExact_mk, K0.fromExact_mk]

/-- Hom-side naturality of `K0.toExact` for an additive exact functor. -/
theorem K0.toExact_naturality {D : Type u'} [Category.{v'} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
    (F : C ⥤ D) [F.Additive] [F.IsExact] :
    (K0.toExact D).comp (K0.map F) =
      (AlgebraicKTheory.K0.map F).comp (K0.toExact C) := by
  apply @WaldhausenKTheory.K0.hom_ext C _ _ (ExactCategory.waldhausenCategory C)
  intro X
  simp [WaldhausenKTheory.K0.map_mk, WaldhausenKTheory.K0.toExact_mk,
    AlgebraicKTheory.K0.map_mk]

end WaldhausenKTheory
