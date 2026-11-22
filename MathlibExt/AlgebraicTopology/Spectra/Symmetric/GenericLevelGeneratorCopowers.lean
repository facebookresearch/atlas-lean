/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.ModuleOperatorFreeEvaluation
import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FinBijDecomposition
import MathlibExt.CategoryTheory.Operad.FinBijBlockSubgroup

/-!
# Actual evaluated generic sphere free spectra

The original complement action and both complete free/evaluation comparisons
identify each level with its actual finite orbit copower. Below the generating
degree the same original evaluated free functor is initial.
-/

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory.TensorPower

namespace CategoryTheory.Spectra.Symmetric.LevelGenerators

local notation "I" => Operad.SmallFinBijGroupoid
local notation "card" => Operad.SmallFinBijGroupoid.card

open Operad.SmallFinBijGroupoid

/-- The original complement-action orbit index is finite at every cardinal pair. -/
theorem finiteCardCosetIndex {n m : ℕ} (h : n ≤ m) : Finite (cardCosetIndex n m h) := by
  let R := card (m - n)
  let N := card n
  let M := card m
  let E := R ⊗ N ≅ M
  let _ : MulAction (Aut R) E := blockMulAction R N M
  let _ : Finite (Aut M) := Finite.of_equiv (Equiv.Perm (Fin m)) (finAutEquiv M).symm.toEquiv
  let b : R ⊗ N ≅ M := cardBlockSumIso (Nat.sub_add_cancel h)
  let _ : Finite E := Finite.of_equiv (Aut M) (blockIsoEquivAut R N M b).symm
  change Finite (MulAction.orbitRel.Quotient (Aut R) E)
  infer_instance

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalClosed V] [HasColimitsOfSize.{0, 0} V]

/-- The literal original ordinary free spectrum followed by its original evaluation. -/
abbrev ordinaryFreeEvaluation (T : V) (n m : ℕ) : V ⥤ V :=
  genericSpectrumFreeAt T (card n) ⋙ genericSpectrumEvaluation T (card m)

/-- The actual genuine operator free spectrum followed by its original evaluation. -/
abbrev operatorFreeEvaluation (T : V) (n m : ℕ) : V ⥤ V :=
  genericSphereOperatorFreeAt T (card n) ⋙ genericSphereOperatorEvaluation T (card m)

/-- The original finite orbit copower of the actual residual tensor-power coefficient. -/
abbrev residualCopower (T : V) {n m : ℕ} (h : n ≤ m) : V ⥤ V :=
  tensorLeft (tensorPowObj T (m - n)) ⋙ sigmaConst ⋙
    (CategoryTheory.evaluation (Type 0) V).obj (cardCosetIndex n m h)

/-- The entire original ordinary evaluated free functor is the original complement-action colimit. -/
def ordinaryInducedIso (T : V) {n m : ℕ} (h : n ≤ m) :
    ordinaryFreeEvaluation T n m ≅ cardInducedFunctor (genericSphereDayMonoid T).X n m h :=
  Mod.dayFreeAtCardInducedIso (genericSphereDayMonoid T).X h

/-- The actual ordinary free/evaluation functor is its finite residual-power orbit copower. -/
def ordinaryCopowerIso (T : V) {n m : ℕ} (h : n ≤ m) :
    ordinaryFreeEvaluation T n m ≅ residualCopower T h :=
  ordinaryInducedIso T h ≪≫ cardInducedCosetCopowerIso (genericSphereDayMonoid T).X h

/-- Below the original generating degree, the same ordinary evaluated free functor is initial. -/
def ordinaryBelowIso (T : V) {n m : ℕ} (h : m < n) :
    ordinaryFreeEvaluation T n m ≅ (Functor.const V).obj (⊥_ V) :=
  Mod.dayFreeAtCardBelowIso (genericSphereDayMonoid T).X h

/-- Both original free and evaluation comparisons retain the entire genuine-to-ordinary functor. -/
def operatorOrdinaryIso (T : V) (n m : ℕ) :
    operatorFreeEvaluation T n m ≅ ordinaryFreeEvaluation T n m :=
  Functor.isoWhiskerRight (genericSphereModuleOperatorFreeIso T (card n)).symm
      (genericSphereOperatorEvaluation T (card m)) ≪≫
    Functor.associator (genericSpectrumFreeAt T (card n))
      (genericSphereModuleOperatorEquivalence T).functor (genericSphereOperatorEvaluation T (card m)) ≪≫
    Functor.isoWhiskerLeft (genericSpectrumFreeAt T (card n))
      (genericSphereModuleOperatorEvaluationIso T (card m))

/-- The actual genuine operator evaluated free functor is the same finite residual-power copower. -/
def operatorCopowerIso (T : V) {n m : ℕ} (h : n ≤ m) :
    operatorFreeEvaluation T n m ≅ residualCopower T h :=
  operatorOrdinaryIso T n m ≪≫ ordinaryCopowerIso T h

/-- Below the original degree, the actual genuine operator evaluated free functor is initial. -/
def operatorBelowIso (T : V) {n m : ℕ} (h : m < n) :
    operatorFreeEvaluation T n m ≅ (Functor.const V).obj (⊥_ V) :=
  operatorOrdinaryIso T n m ≪≫ ordinaryBelowIso T h

omit [SymmetricCategory V] [MonoidalClosed V] in
/-- Each original coefficient object is retained on every summand of the residual copower. -/
theorem residualCopower_obj (T : V) {n m : ℕ} (h : n ≤ m) (X : V) :
    (residualCopower T h).obj X = ∐ fun _ : cardCosetIndex n m h => tensorPowObj T (m - n) ⊗ X := rfl

omit [SymmetricCategory V] [MonoidalClosed V] in
/-- Every original coefficient map is retained in the actual residual copower map function. -/
theorem residualCopower_map (T : V) {n m : ℕ} (h : n ≤ m) {X Y : V} (f : X ⟶ Y) :
    (residualCopower T h).map f =
      Limits.Sigma.map (fun _ : cardCosetIndex n m h => tensorPowObj T (m - n) ◁ f) :=
  rfl

end CategoryTheory.Spectra.Symmetric.LevelGenerators
