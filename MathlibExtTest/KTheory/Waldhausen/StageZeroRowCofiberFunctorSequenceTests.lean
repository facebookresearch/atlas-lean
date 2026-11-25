/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageZeroRowCofiberFunctorSequence

/-!
# Clients for the full original zero-row cofiber functor sequence

The original evaluations and their actual horizontal/vertical maps earn
the complete base condition. The same certificate enters the original
prior-stage functors and full relative transpose. Equal endpoints, degree
zero and the actual shifted-operator successor are retained.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial ZeroObject

universe u v

namespace MathlibExtTest.KTheory.Waldhausen.StageZeroRowCofiberFunctorSequenceTests

open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.SConstruction
open CategoryTheory.Waldhausen.SConstruction.StageZeroRowCofiber

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The original chosen zero value on every tested general finite stage. -/
local instance originalStageZero (n : ℕ) : HasZeroObject (Stage C n) :=
  generalStageHasZeroObject C n

/-- The original general Waldhausen value on every tested finite stage. -/
local instance originalStageWaldhausen (n : ℕ) : WaldhausenCategoryWithoutGluing (Stage C n) :=
  generalStageWaldhausenCategory C n

/-- The original relative value on the tested scalar cofiber category. -/
local instance originalRelativeWaldhausen : WaldhausenCategoryWithoutGluing
    (CofiberSequenceCategory C) :=
  CofiberSequenceCategory.relativeWaldhausenCategory C

/-- The chosen zero value on every tested prior stage of the original source stage. -/
local instance originalPriorStageZero (n k : ℕ) : HasZeroObject (Stage (Stage C n) k) :=
  generalStageHasZeroObject (Stage C n) k

/-- The original general value on every tested prior stage of the original source stage. -/
local instance originalPriorStageWaldhausen (n k : ℕ) :
    WaldhausenCategoryWithoutGluing (Stage (Stage C n) k) :=
      generalStageWaldhausenCategory (Stage C n) k

/-- The chosen zero value on each tested prior stage of the scalar cofiber category. -/
local instance originalRelativeStageZero (k : ℕ) :
    HasZeroObject (Stage (CofiberSequenceCategory C) k) :=
  generalStageHasZeroObject (CofiberSequenceCategory C) k

/-- The original general value on each tested prior stage of the scalar cofiber category. -/
local instance originalRelativeStageWaldhausen (k : ℕ) :
    WaldhausenCategoryWithoutGluing (Stage (CofiberSequenceCategory C) k) :=
  generalStageWaldhausenCategory (CofiberSequenceCategory C) k

/-- The original relative value over each tested target prior-stage category. -/
local instance originalStageRelativeWaldhausen (k : ℕ) :
    WaldhausenCategoryWithoutGluing (CofiberSequenceCategory (Stage C k)) :=
  CofiberSequenceCategory.relativeWaldhausenCategory (Stage C k)

/-- All original zero-row pairs give the full SAME original evaluation sequence. -/
theorem originalFullCertificate (n : ℕ) {i j : Fin (n + 1)} (hij : i ≤ j) :
    IsWaldhausenCofiberFunctorSequence
      (eval C n (interval 0 i (Fin.zero_le _))) (eval C n (interval 0 j (Fin.zero_le _)))
      (eval C n (interval i j hij)) (inclusion C n hij) (projection C n hij) :=
  certificate C n hij

/-- Every actual original object retains its complete original cofiber triangle. -/
theorem originalObjectwise (n : ℕ) {i j : Fin (n + 1)} (hij : i ≤ j) (A : Stage C n) :
    IsCofiberSequence (A.zeroRowPairMap hij) (A.obj.map (vert (Fin.zero_le i) hij)) := by
  simpa only [rowFunctor_obj, quotientFunctor_obj, inclusion_app, projection_app] using
    objectwise C n hij A

/-- The actual original stock base descent is earned from the genuine source stage corner. -/
theorem originalBaseDescent (n : ℕ) {i j : Fin (n + 1)} (hij : i ≤ j)
    {A B : Stage C n} (φ : A ⟶ B) (hφ : IsCofibration φ) :
    letI : HasPushout ((inclusion C n hij).app A) ((rowFunctor C n i).map φ) := by
      obtain ⟨_, _, _, hP, _⟩ := WaldhausenCategoryWithoutGluing.cofibration_pushout
        (C := C) ((inclusion C n hij).app A) (objectwise C n hij A).1
        ((rowFunctor C n i).obj B) ((rowFunctor C n i).map φ)
      exact hP.flip.hasPushout
    IsCofibration (pushout.desc ((rowFunctor C n j).map φ) ((inclusion C n hij).app B)
      ((inclusion C n hij).naturality φ).symm) :=
  baseCofibration C n hij φ hφ

/-- The whole stock lift has internally earned original relative exactness. -/
theorem originalLiftExact (n : ℕ) {i j : Fin (n + 1)} (hij : i ≤ j) :
    (lift C n hij).IsWaldhausenExact := lift_isWaldhausenExact C n hij

/-- The SAME three original functors and SAME postwhiskered arrows enter every prior stage. -/
theorem originalPriorCertificate (n k : ℕ) {i j : Fin (n + 1)} (hij : i ≤ j) :
    let H := certificate C n hij
    IsWaldhausenCofiberFunctorSequence (H.sourceExact.mapStage k)
      (H.middleExact.mapStage k) (H.quotientExact.mapStage k)
      (H.sourceExact.mapStageNatTrans H.middleExact (inclusion C n hij) k)
      (H.middleExact.mapStageNatTrans H.quotientExact (projection C n hij) k) :=
  (certificate C n hij).mapStage k

/-- The prior-stage lift is the same actual stage lift followed by the full original transpose. -/
theorem originalPriorLift (n k : ℕ) {i j : Fin (n + 1)} (hij : i ≤ j) :
    (certificate C n hij).stageLift k =
      (certificate C n hij).lift_isWaldhausenExact.mapStage k ⋙
        CofiberSequenceCategory.relativeStageTranspose C k := rfl

/-- Every prior interval retains the actual original inner zero-row pair coefficient. -/
theorem originalPriorFirstCoefficient (n k : ℕ) {i j : Fin (n + 1)} (hij : i ≤ j)
    (A : Stage (Stage C n) k) (x : Ar k) :
    let H := certificate C n hij
    ((H.sourceExact.mapStageNatTrans H.middleExact (inclusion C n hij) k).app A).hom.app x =
      (A.obj.obj x).zeroRowPairMap hij := by
  exact ((certificate C n hij).mapStage_firstArrow_app k A x).trans
    (inclusion_app C n hij (A.obj.obj x))

/-- Every original prior simplex operator commutes with the SAME full relative cofiber lift. -/
theorem originalPriorOperator (n : ℕ) {i j : Fin (n + 1)} (hij : i ≤ j)
    {a b : SimplexCategory} (f : a ⟶ b) :
    reindexStage (C := Stage C n) f ⋙ (certificate C n hij).stageLift a.len =
      (certificate C n hij).stageLift b.len ⋙ CofiberSequenceCategory.mapOfWaldhausenExact
        (reindexStage (C := C) f) (reindexStage_general_isWaldhausenExact C f) :=
  (certificate C n hij).stageLift_reindex f

/-- A shifted operator retains the actual original `A01 → A0j → A1j` sequence. -/
theorem originalShiftedCertificate {a b : SimplexCategory} (α : a ⟶ b) :
    IsWaldhausenCofiberFunctorSequence
      (rowFunctor C (b.len + 1) (StageFirstQuotient.firstIndex b.len))
      (rowFunctor C (b.len + 1) (shiftedIndex α))
      (quotientFunctor C (b.len + 1) (first_le_shiftedIndex α))
      (inclusion C (b.len + 1) (first_le_shiftedIndex α))
      (projection C (b.len + 1) (first_le_shiftedIndex α)) :=
  shiftedCertificate C α

/-- Equal endpoints retain the actual original diagonal quotient. -/
theorem originalEqualEndpoints (n : ℕ) (i : Fin (n + 1)) :
    IsWaldhausenCofiberFunctorSequence (rowFunctor C n i) (rowFunctor C n i)
      (quotientFunctor C n (le_refl i)) (inclusion C n (le_refl i))
      (projection C n (le_refl i)) := equalEndpoints C n i

/-- Degree zero keeps the original zero-stage carrier and its genuine diagonal interval. -/
theorem originalDegreeZero :
    IsWaldhausenCofiberFunctorSequence (rowFunctor C 0 0) (rowFunctor C 0 0)
      (quotientFunctor C 0 (le_refl (0 : Fin 1)))
      (inclusion C 0 (le_refl (0 : Fin 1))) (projection C 0 (le_refl (0 : Fin 1))) := degreeZero C

end MathlibExtTest.KTheory.Waldhausen.StageZeroRowCofiberFunctorSequenceTests

end
