/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberRelativeCofiberCriterion
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberRelativeZeroFunctorFamilies
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenFunctoriality
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.Zero

/-!
# Genuine relative stage admission with all original corners

A finite diagram of extensions is a genuine relative stage precisely
when all three original evaluations are stages and every original first
triple map retains its relative cofibration corner. This criterion admits
the whole original zero-source and zero-quotient functor diagrams.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction.CofiberSequenceCategory

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The original three evaluated stages jointly admit the whole genuine
relative stage when every original first triple map retains its relative corner. -/
theorem isStage_relative_iff_evaluations (n : ℕ) (A : Ar n ⥤ CofiberSequenceCategory C) :
    (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
      IsStage n A) ↔
      (∀ k : Fin 3, IsStage n (A ⋙ ((forget C) ⋙ (evaluation (Fin 3) C).obj k))) ∧
        ∀ (i j l : Fin (n + 1)) (hij : i ≤ j) (hjl : j ≤ l),
          relativeCofibrations C (A.map (horiz hij hjl)) := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  constructor
  · intro hA
    refine ⟨?_, ?_⟩
    · intro k
      exact (evaluationIsRelativeWaldhausenExact C k).isStage_postcomp n A hA
    · intro i j l hij hjl
      exact (isCofibration_relativeWaldhausenCategory_iff C (A.map (horiz hij hjl))).mp
        (hA.cofiber_triple hij hjl).1
  · rintro ⟨hRows, hCorners⟩
    refine { diag_isZero := ?_, cofiber_triple := ?_ }
    · intro i
      apply IsZero.of_full_of_faithful_of_isZero (forget C)
      exact Functor.isZero _ (fun k => (hRows k).diag_isZero i)
    · intro i j l hij hjl
      apply (isCofiberSequence_relative_iff_evaluations C
        (A.map (horiz hij hjl)) (A.map (vert hij hjl))).mpr
      refine ⟨hCorners i j l hij hjl, ?_⟩
      intro k
      exact (hRows k).cofiber_triple hij hjl

/-- Every original zero-source diagram Z-to-G-to-G is a genuine relative
stage when Z is pointwise zero and G is the original finite stage diagram. -/
theorem isStage_zeroSourceFunctorSequence (n : ℕ) (Z G : Ar n ⥤ C)
    (hZ : ∀ x : Ar n, IsZero (Z.obj x)) (hG : IsStage n G) :
    letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
    IsStage n (zeroSourceFunctorSequence C Z G hZ) := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  apply (isStage_relative_iff_evaluations C n (zeroSourceFunctorSequence C Z G hZ)).mpr
  refine ⟨?_, ?_⟩
  · intro k
    fin_cases k
    · change IsStage n (zeroSourceFunctorSequence C Z G hZ ⋙ source C)
      rw [zeroSourceFunctorSequence_source]
      exact isStage_of_pointwise_zero C Z hZ
    · change IsStage n (zeroSourceFunctorSequence C Z G hZ ⋙ middle C)
      rw [zeroSourceFunctorSequence_middle]
      exact hG
    · change IsStage n (zeroSourceFunctorSequence C Z G hZ ⋙ quotient C)
      rw [zeroSourceFunctorSequence_quotient]
      exact hG
  · intro i j l hij hjl
    exact zeroSourceFunctorSequence_map_relativeCofibration C Z G hZ (horiz hij hjl)
      (hG.cofiber_triple hij hjl).1

/-- Every original zero-quotient diagram G-to-G-to-Z is a genuine relative
stage when Z is pointwise zero and G is the original finite stage diagram. -/
theorem isStage_zeroQuotientFunctorSequence (n : ℕ) (Z G : Ar n ⥤ C)
    (hZ : ∀ x : Ar n, IsZero (Z.obj x)) (hG : IsStage n G) :
    letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
    IsStage n (zeroQuotientFunctorSequence C Z G hZ) := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  apply (isStage_relative_iff_evaluations C n (zeroQuotientFunctorSequence C Z G hZ)).mpr
  refine ⟨?_, ?_⟩
  · intro k
    fin_cases k
    · change IsStage n (zeroQuotientFunctorSequence C Z G hZ ⋙ source C)
      rw [zeroQuotientFunctorSequence_source]
      exact hG
    · change IsStage n (zeroQuotientFunctorSequence C Z G hZ ⋙ middle C)
      rw [zeroQuotientFunctorSequence_middle]
      exact hG
    · change IsStage n (zeroQuotientFunctorSequence C Z G hZ ⋙ quotient C)
      rw [zeroQuotientFunctorSequence_quotient]
      exact isStage_of_pointwise_zero C Z hZ
  · intro i j l hij hjl
    exact zeroQuotientFunctorSequence_map_relativeCofibration C Z G hZ (horiz hij hjl)
      (hG.cofiber_triple hij hjl).1

end CategoryTheory.Waldhausen.SConstruction.CofiberSequenceCategory
