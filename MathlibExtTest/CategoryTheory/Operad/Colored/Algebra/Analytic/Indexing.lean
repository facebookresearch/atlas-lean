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

import MathlibExt.CategoryTheory.Operad.Colored.Algebra.Analytic.Indexing

/-!
# Focused O7G analytic-indexing public-contract packet

Executable examples pinning the most important stable public contracts of the
fixed-output analytic-indexing layer: a genuinely multi-color swap relabelling
at the combined-family level; the inner-carrier and outer-collection component
formulas; factors-level mixed naturality; the finite-tensor summand component
formulas and summand mixed naturality; and full/faithful inclusion of
fixed-output profiles into colored profiles.

Only downstream-relevant indexing endpoints are exercised, at separated
universes for the color type, target category, and hom universe. No `rfl`
constructor/accessor, identity law, or private scaffolding is tested.
-/

open CategoryTheory
open CategoryTheory.Operad

namespace MathlibExtTest.Operad.Colored.Algebra.Analytic.IndexingTests

/-- Two-input profile with distinct input colors `0`, `1` and distinct output `2`. -/
private def profileP : AnalyticIndex (Fin 3) 2 :=
  AnalyticIndex.ofFin (Fin.cases (0 : Fin 3) (fun _ => (1 : Fin 3)) : Fin 2 → Fin 3)

/-- Same input colors in swapped order. -/
private def profileQ : AnalyticIndex (Fin 3) 2 :=
  AnalyticIndex.ofFin (Fin.cases (1 : Fin 3) (fun _ => (0 : Fin 3)) : Fin 2 → Fin 3)

/-- Nonidentity color-preserving swap between the two multi-color profiles. -/
private def swapProfile : profileP.toColoredProfile ⟶ profileQ.toColoredProfile where
  inputEquiv := (Equiv.swap (0 : Fin 2) (1 : Fin 2) : Fin 2 ≃ Fin 2)
  inputColor_eq := fun i => by
    induction i using Fin.cases with
    | zero => decide
    | succ i =>
      induction i using Fin.cases with
      | zero => decide
      | succ i => exact Fin.elim0 i
  outputColor_eq := rfl

-- O7G-1: the swap relabelling exchanges the two carrier slots of the combined family.
example (O : ColoredSymmetricCollection (Fin 3) Type) (A : Fin 3 → Type) :
    ((analyticFactors (d := 2) O A).map swapProfile).equiv
      (some (0 : Fin 2)) = some (1 : Fin 2) := by
  change (Equiv.optionCongr (Equiv.swap (0 : Fin 2) (1 : Fin 2) : Fin 2 ≃ Fin 2))
    (some (0 : Fin 2)) = some (1 : Fin 2)
  decide

section SeparatedUniverses

universe uCol uMor uObj

variable {Color : Type uCol} {V : Type uObj} [Category.{uMor} V]
variable {d : Color}

-- O7G-2: a pointwise carrier map acts on an inner carrier slot of the combined family.
example (O : ColoredSymmetricCollection Color V)
    {A B : Color → V} (φ : ∀ c, A c ⟶ B c)
    (P : AnalyticIndex Color d) (i : P.inputs) :
    ((analyticFactorsCarrierMap (d := d) O φ).app P).hom
        (analyticFactorsInnerIndex O A P i) = φ (P.inputColor i) :=
  analyticFactorsCarrierMap_app_inner O φ P i

-- O7G-3: a collection map acts on the outer operation slot of the combined family.
example (A : Color → V)
    {O O' : ColoredSymmetricCollection Color V} (α : O ⟶ O')
    (P : AnalyticIndex Color d) :
    ((analyticFactorsCollectionMap (d := d) A α).app P).hom
        (analyticFactorsOuterIndex O A P) = α.app P.toColoredProfile :=
  analyticFactorsCollectionMap_app_outer A α P

-- O7G-4: collection and carrier maps commute at the combined-family level.
example (A : Color → V) {B : Color → V}
    {O O' : ColoredSymmetricCollection Color V} (α : O ⟶ O')
    (φ : ∀ c, A c ⟶ B c) :
    analyticFactorsCollectionMap (d := d) A α ≫
        analyticFactorsCarrierMap (d := d) O' φ =
      analyticFactorsCarrierMap (d := d) O φ ≫
        analyticFactorsCollectionMap (d := d) B α :=
  analyticFactorsCollectionCarrier_mixed A α φ

-- O7G-5: the summand carrier component is the tensor of the combined-family component.
example [FiniteTensor V] (O : ColoredSymmetricCollection Color V)
    {A B : Color → V} (φ : ∀ c, A c ⟶ B c) (P : AnalyticIndex Color d) :
    (analyticSummandCarrierMap (d := d) O φ).app P =
      (FiniteTensor.tensor (V := V)).map
        ((analyticFactorsCarrierMap (d := d) O φ).app P) :=
  analyticSummandCarrierMap_app O φ P

-- O7G-6: the summand collection component is the tensor of the combined-family component.
example [FiniteTensor V] (A : Color → V)
    {O O' : ColoredSymmetricCollection Color V} (α : O ⟶ O')
    (P : AnalyticIndex Color d) :
    (analyticSummandCollectionMap (d := d) A α).app P =
      (FiniteTensor.tensor (V := V)).map
        ((analyticFactorsCollectionMap (d := d) A α).app P) :=
  analyticSummandCollectionMap_app A α P

-- O7G-7: collection and carrier maps commute at the analytic-summand level.
example [FiniteTensor V] (A : Color → V) {B : Color → V}
    {O O' : ColoredSymmetricCollection Color V} (α : O ⟶ O')
    (φ : ∀ c, A c ⟶ B c) :
    analyticSummandCollectionMap (d := d) A α ≫
        analyticSummandCarrierMap (d := d) O' φ =
      analyticSummandCarrierMap (d := d) O φ ≫
        analyticSummandCollectionMap (d := d) B α :=
  analyticSummandCollectionCarrier_mixed A α φ

-- O7G-8: fixed-output profiles include fully and faithfully into colored profiles.
example (d : Color) :
    Functor.Full (analyticToProfileFunctor Color d) ∧
      Functor.Faithful (analyticToProfileFunctor Color d) :=
  ⟨inferInstance, inferInstance⟩

end SeparatedUniverses

end MathlibExtTest.Operad.Colored.Algebra.Analytic.IndexingTests
