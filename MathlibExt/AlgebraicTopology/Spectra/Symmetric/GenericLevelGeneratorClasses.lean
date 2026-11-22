/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.GenericLevelGeneratorCopowers
import MathlibExt.AlgebraicTopology.ModelCategory.TensorPowerGeneratorMaps
import MathlibExt.CategoryTheory.MorphismProperty.WeakFactorizationSystem

/-!
# Actual symmetric free-generator coefficient classes

The complete evaluated free functors are compared to the original finite
coefficient copowers. Cofibrancy of T and the actual degree-zero unitors
give both base map classes on every component and on every operator Hom.
-/

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.MonoidalCategory.TensorPower
open CategoryTheory.MorphismProperty

namespace CategoryTheory.Spectra.Symmetric.LevelGenerators

local notation "I" => Operad.SmallFinBijGroupoid
local notation "card" => Operad.SmallFinBijGroupoid.card

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalClosed V] [HasColimitsOfSize.{0, 0} V]

omit [SymmetricCategory V] [MonoidalClosed V] in
/-- The original coproduct map retains any coproduct-stable coefficient map class. -/
theorem residualCopower_map_mem (P : MorphismProperty V) [P.IsStableUnderCoproducts.{0}]
    (T : V) {n m : ℕ} (h : n ≤ m) {X Y : V} (f : X ⟶ Y)
    (hf : P (tensorPowObj T (m - n) ◁ f)) : P ((residualCopower T h).map f) := by
  let Q := Operad.SmallFinBijGroupoid.cardCosetIndex n m h
  let τ : Discrete.functor (fun _ : Q => tensorPowObj T (m - n) ⊗ X) ⟶
      Discrete.functor (fun _ : Q => tensorPowObj T (m - n) ⊗ Y) :=
    Discrete.natTrans (fun _ => tensorPowObj T (m - n) ◁ f)
  change P (colimMap τ)
  exact MorphismProperty.colimMap (W := P) τ (fun _ => hf)

omit [MonoidalCategory V] [SymmetricCategory V] [MonoidalClosed V] [HasColimitsOfSize.{0, 0} V] in
/-- A whole natural functor comparison preserves the original evaluated arrow class. -/
theorem map_mem_of_comparison (P : MorphismProperty V) [P.RespectsIso]
    {F G : V ⥤ V} (e : F ≅ G) {X Y : V} (f : X ⟶ Y) (hf : P (G.map f)) : P (F.map f) :=
  (P.arrow_mk_iso_iff (((Functor.mapArrowFunctor V V).mapIso e).app (Arrow.mk f))).mpr hf

/-- Every actual genuine evaluated free map is the complete original operator Hom tensor arrow. -/
theorem operatorFreeEvaluation_map (T : V) (n m : ℕ) {X Y : V} (f : X ⟶ Y) :
    (operatorFreeEvaluation T n m).map f = f ▷ OperatorCoend.Hom T (card n) (card m) :=
  genericSphereOperatorFreeAt_map T (card n) (card m) f

variable [ModelCategory V] [IsClosedSymmetricMonoidalModelCategory V]

omit [IsClosedSymmetricMonoidalModelCategory V] in
/-- The actual original below-degree ordinary evaluated free map is a trivial cofibration. -/
theorem ordinaryBelow_trivialCofibration (T : V) {n m : ℕ} (h : m < n)
    {X Y : V} (f : X ⟶ Y) : trivialCofibrations V ((ordinaryFreeEvaluation T n m).map f) := by
  apply map_mem_of_comparison (trivialCofibrations V) (ordinaryBelowIso T h) f
  change trivialCofibrations V (𝟙 (⊥_ V))
  exact ⟨(cofibration_iff _).mp (by infer_instance), (weakEquivalence_iff _).mp (by infer_instance)⟩

omit [IsClosedSymmetricMonoidalModelCategory V] in
/-- The original degree-zero coefficient uses its unitors; neither T nor the tensor unit must be cofibrant. -/
theorem ordinary_diagonal_cofibration (T : V) (n : ℕ) {X Y : V} (f : X ⟶ Y)
    (hf : cofibrations V f) : cofibrations V ((ordinaryFreeEvaluation T n n).map f) := by
  let _ : (cofibrations V).IsStableUnderCoproducts.{0} :=
    IsStableUnderCoproducts.of_llp_eq (cofibrations V) (trivialFibrations V) (trivialFibrations_llp V)
  apply map_mem_of_comparison (cofibrations V) (ordinaryCopowerIso T (le_refl n)) f
  apply residualCopower_map_mem (cofibrations V) T (le_refl n) f
  rw [Nat.sub_self]
  exact ((cofibrations V).arrow_mk_iso_iff (TensorPowerGeneratorMaps.leftUnitArrowIso f)).mpr hf

omit [IsClosedSymmetricMonoidalModelCategory V] in
/-- The original degree-zero acyclic coefficient uses only the actual unitors and finite coproduct closure. -/
theorem ordinary_diagonal_trivialCofibration (T : V) (n : ℕ) {X Y : V} (f : X ⟶ Y)
    (hf : trivialCofibrations V f) : trivialCofibrations V ((ordinaryFreeEvaluation T n n).map f) := by
  let _ : (trivialCofibrations V).IsStableUnderCoproducts.{0} :=
    IsStableUnderCoproducts.of_llp_eq (trivialCofibrations V) (fibrations V) (fibrations_llp V)
  apply map_mem_of_comparison (trivialCofibrations V) (ordinaryCopowerIso T (le_refl n)) f
  apply residualCopower_map_mem (trivialCofibrations V) T (le_refl n) f
  rw [Nat.sub_self]
  exact ((trivialCofibrations V).arrow_mk_iso_iff (TensorPowerGeneratorMaps.leftUnitArrowIso f)).mpr hf

/-- Every original ordinary evaluated free cofibration has the actual finite residual-power coefficient class. -/
theorem ordinary_cofibration (T : V) [IsCofibrant T] (n m : ℕ) {X Y : V} (f : X ⟶ Y)
    (hf : cofibrations V f) : cofibrations V ((ordinaryFreeEvaluation T n m).map f) := by
  by_cases h : n ≤ m
  · let _ : (cofibrations V).IsStableUnderCoproducts.{0} :=
      IsStableUnderCoproducts.of_llp_eq (cofibrations V) (trivialFibrations V) (trivialFibrations_llp V)
    apply map_mem_of_comparison (cofibrations V) (ordinaryCopowerIso T h) f
    exact residualCopower_map_mem (cofibrations V) T h f
      (TensorPowerGeneratorMaps.left_cofibration T (m - n) f hf)
  · exact (ordinaryBelow_trivialCofibration T (Nat.lt_of_not_ge h) f).1

/-- Every original ordinary evaluated free trivial cofibration retains its exact coefficient class. -/
theorem ordinary_trivialCofibration (T : V) [IsCofibrant T] (n m : ℕ) {X Y : V} (f : X ⟶ Y)
    (hf : trivialCofibrations V f) : trivialCofibrations V ((ordinaryFreeEvaluation T n m).map f) := by
  by_cases h : n ≤ m
  · let _ : (trivialCofibrations V).IsStableUnderCoproducts.{0} :=
      IsStableUnderCoproducts.of_llp_eq (trivialCofibrations V) (fibrations V) (fibrations_llp V)
    apply map_mem_of_comparison (trivialCofibrations V) (ordinaryCopowerIso T h) f
    exact residualCopower_map_mem (trivialCofibrations V) T h f
      (TensorPowerGeneratorMaps.left_trivialCofibration T (m - n) f hf)
  · exact ordinaryBelow_trivialCofibration T (Nat.lt_of_not_ge h) f

/-- Every actual genuine evaluated free cofibration is in the same original base class. -/
theorem operator_cofibration (T : V) [IsCofibrant T] (n m : ℕ) {X Y : V} (f : X ⟶ Y)
    (hf : cofibrations V f) : cofibrations V ((operatorFreeEvaluation T n m).map f) :=
  map_mem_of_comparison (cofibrations V) (operatorOrdinaryIso T n m) f (ordinary_cofibration T n m f hf)

/-- Every actual genuine evaluated free trivial cofibration is in the same original base class. -/
theorem operator_trivialCofibration (T : V) [IsCofibrant T] (n m : ℕ) {X Y : V} (f : X ⟶ Y)
    (hf : trivialCofibrations V f) : trivialCofibrations V ((operatorFreeEvaluation T n m).map f) :=
  map_mem_of_comparison (trivialCofibrations V) (operatorOrdinaryIso T n m) f
    (ordinary_trivialCofibration T n m f hf)

/-- All original finite indices retain the complete cofibration operator-Hom tensor bound. -/
theorem homTensor_cofibration (T : V) [IsCofibrant T] (a b : I) {X Y : V} (f : X ⟶ Y)
    (hf : cofibrations V f) : cofibrations V (f ▷ OperatorCoend.Hom T a b) := by
  rcases a with ⟨⟨n⟩⟩
  rcases b with ⟨⟨m⟩⟩
  exact (operatorFreeEvaluation_map T n m f) ▸ operator_cofibration T n m f hf

/-- All original finite indices retain the complete trivial-cofibration operator-Hom tensor bound. -/
theorem homTensor_trivialCofibration (T : V) [IsCofibrant T] (a b : I) {X Y : V} (f : X ⟶ Y)
    (hf : trivialCofibrations V f) : trivialCofibrations V (f ▷ OperatorCoend.Hom T a b) := by
  rcases a with ⟨⟨n⟩⟩
  rcases b with ⟨⟨m⟩⟩
  exact (operatorFreeEvaluation_map T n m f) ▸ operator_trivialCofibration T n m f hf

end CategoryTheory.Spectra.Symmetric.LevelGenerators
