/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.FreeActions.ResidualMaps
public import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.Sources.PrettySmall
public import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.Sources.ChosenActionModels

/-!
# Actual chosen-action free J coefficients are couniversal weak equivalences

The original chosen J_n maps are underlying trivial cofibrations. Their
arbitrary original R residual tensors are couniversal by genuine h-monoidality.
The actual paired-orbit copower arrow comparison transfers that property to
every original evaluated free map, without a cofibrancy condition on R or the
base tensor unit.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe w v u

open CategoryTheory Limits MorphismProperty MonoidalCategory MonObj BraidedCategory
open CategoryTheory.MonoidalCategory
open CategoryTheory.Operad.SmallFinBijGroupoid
open scoped CategoryTheory.MonObj MonoidalClosed

namespace HomotopicalAlgebra.PositiveLevelModel.Chosen

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [ModelCategory C] [HasColimitsOfSize.{w, w} C] [HasLimitsOfSize.{w, w} C]

local instance cellsBaseSmallColimits : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, w, w} C

variable (models : ChosenActionModels.{w} C) (small : PrettySmallSource.{w} C) (hm : HMonoidality C)

omit [SymmetricCategory C] [MonoidalClosed C] [HasLimitsOfSize.{w, w} C] in
/-- Every original chosen J_n map is genuinely trivial on the underlying original coefficient object. -/
theorem J_underlying_trivial (n : ℕ) {A B : degreeActionCategory (C := C) n} (j : A ⟶ B) (hj : models.J n j) :
    trivialCofibrations C (j.app (SingleObj.star (Equiv.Perm (Fin n)))) := by
  let _ : ModelCategory (degreeActionCategory (C := C) n) := models.model n
  have hJ : models.J n ≤ trivialCofibrations (degreeActionCategory (C := C) n) := by
    have hl := (models.J n).le_llp_rlp
    rw [models.J_rlp n] at hl
    change models.J n ≤ (fibrations (degreeActionCategory (C := C) n)).llp at hl
    rwa [fibrations_llp] at hl
  have he := hJ j hj
  have hc := models.underlying_cofibrations_le n j he.1
  have hw : (weakEquivalences C).functorCategory (degreeActionIndex n) j := (models.weak_eq n) ▸ he.2
  exact ⟨hc _, hw _⟩

include small in
omit [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C] in
/-- The source auxiliary compact generators supply actual global couniversal weak copower closure. -/
theorem couniversal_coproducts : (couniversalWeakEquivalences C).IsStableUnderCoproducts.{0} := by
  let _ : (couniversalWeakEquivalences C).IsStableUnderTransfiniteComposition.{w} := small.couniversal_transfinite
  let _ : (couniversalWeakEquivalences C).IsStableUnderTransfiniteComposition.{0} :=
    IsStableUnderTransfiniteComposition.shrink₀ _
  exact isStableUnderCoproducts_of_cobase_transfinite _

variable (R : DayFunctor I C) [MonObj R]

include hm in
omit [MonoidalClosed C] [HasLimitsOfSize.{w, w} C] [MonObj R] in
/-- Every original residual R tensor of an original chosen J map is couniversal, with arbitrary coefficient R_k. -/
theorem residual_J_couniversal (n k : ℕ) {A B : degreeActionCategory (C := C) n}
    (j : A ⟶ B) (hj : models.J n j) :
    couniversalWeakEquivalences C (R.functor.obj (card k) ◁ j.app (SingleObj.star (Equiv.Perm (Fin n)))) := by
  let _ : IsLeftProper C := hm.isLeftProper
  have ht := hm.trivialCofibration_tensor (j.app (SingleObj.star (Equiv.Perm (Fin n))))
    (J_underlying_trivial models n j hj) (R.functor.obj (card k))
  have hu := acyclicHCofibrations_le_couniversalWeakEquivalences _ ht
  let e : Arrow.mk (j.app (SingleObj.star (Equiv.Perm (Fin n))) ▷ R.functor.obj (card k)) ≅
      Arrow.mk (R.functor.obj (card k) ◁ j.app (SingleObj.star (Equiv.Perm (Fin n)))) :=
    Arrow.isoMk (β_ _ _) (β_ _ _) (braiding_naturality_left _ _).symm
  exact ((couniversalWeakEquivalences C).arrow_iso_iff e).mp hu

include small hm in
/-- Every actual original chosen-action free J arrow is couniversal at every original degree. -/
theorem freeJ_evaluation_couniversal (n m : ℕ) {A B : degreeActionCategory (C := C) n}
    (j : A ⟶ B) (hj : models.J n j) :
    couniversalWeakEquivalences C ((CategoryTheory.Mod.dayEvaluation R (card m)).map ((degreeActionFreeAt R n).map j))
        := by
  let _ : (couniversalWeakEquivalences C).IsStableUnderCoproducts.{0} := couniversal_coproducts small
  let _ : MulAction (pairedBlockGroup n m) (pairedBlockAlphabet n m) := pairedBlockAction n m
  let Q := MulAction.orbitRel.Quotient (pairedBlockGroup n m) (pairedBlockAlphabet n m)
  let tau : Discrete.functor (fun _ : Q => R.functor.obj (card (m - n)) ⊗ A.obj (SingleObj.star (Equiv.Perm (Fin n)))) ⟶
      Discrete.functor (fun _ : Q => R.functor.obj (card (m - n)) ⊗ B.obj (SingleObj.star (Equiv.Perm (Fin n)))) :=
    Discrete.natTrans (fun _ => R.functor.obj (card (m - n)) ◁ j.app (SingleObj.star (Equiv.Perm (Fin n))))
  have ht : couniversalWeakEquivalences C (colimMap tau) :=
    MorphismProperty.colimMap tau (fun _ => residual_J_couniversal models hm R n (m - n) j hj)
  exact ((couniversalWeakEquivalences C).arrow_iso_iff (actionResidualCopowerArrowIso R n m j)).mpr ht

end HomotopicalAlgebra.PositiveLevelModel.Chosen
