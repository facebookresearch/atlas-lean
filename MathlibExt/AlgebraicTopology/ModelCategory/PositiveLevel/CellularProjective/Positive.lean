/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.CellularProjective.Model
public import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.Basic

/-!
# The actual positive and ordinary projective R-module models

Both model dictionaries are constructed on the original R-module carrier from
the same original I/J and cellular source data. Positive tests retain exactly
the degrees n>0. The actual positive cofibration class is the constructed
ordinary class intersected with isomorphisms of the original zero evaluation.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe w v u

open CategoryTheory Limits MorphismProperty MonoidalCategory MonObj
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj MonoidalClosed

namespace HomotopicalAlgebra.PositiveLevelModel.CellularProjective

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [ModelCategory C] [IsClosedSymmetricMonoidalModelCategory C]
  [HasColimitsOfSize.{w, w} C] [HasLimitsOfSize.{0, 0} C] [LocallySmall.{w} C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (h : CellularSource d)

local instance positiveBaseSmallColimits : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, w, w} C

variable (R : DayFunctor I C) [MonObj R]
  (hR : ∀ n : ℕ, IsCofibrant (R.functor.obj (CategoryTheory.Operad.SmallFinBijGroupoid.card n)))

/-- The actual ordinary model on the same original R-module carrier, including degree zero. -/
@[instance_reducible]
def ordinaryModelCategory : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) :=
  sourceModelCategory d h R hR (fun n : ℕ => n)

/-- The actual positive model on the same original R-module carrier, with exactly the positive free generators. -/
@[instance_reducible]
def positiveModelCategory : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) :=
  sourceModelCategory d h R hR (fun n : ℕ+ => n)

/-- The actual positive weak class uses only the original positive degree tests. -/
theorem positive_weakEquivalences_eq :
    let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := positiveModelCategory d h R hR
    weakEquivalences (CategoryTheory.Mod (DayFunctor I C) R) = positiveProperty R (weakEquivalences C) :=
  source_weakEquivalences_eq d h R hR (fun n : ℕ+ => n)

/-- The actual positive fibrations have the unrestricted zero component and all original positive base tests. -/
theorem positive_fibrations_eq :
    let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := positiveModelCategory d h R hR
    fibrations (CategoryTheory.Mod (DayFunctor I C) R) = positiveProperty R (fibrations C) :=
  source_fibrations_eq d h R hR (fun n : ℕ+ => n)

/-- The complete actual positive trivial-fibration class retains the positive base intersection. -/
theorem positive_trivialFibrations_eq :
    let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := positiveModelCategory d h R hR
    trivialFibrations (CategoryTheory.Mod (DayFunctor I C) R) = positiveProperty R (trivialFibrations C) :=
  source_trivialFibrations_eq d h R hR (fun n : ℕ+ => n)

/-- Actual positive cofibrations retain all original positive free I arrows. -/
theorem positive_cofibrations_eq_generators :
    let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := positiveModelCategory d h R hR
    cofibrations (CategoryTheory.Mod (DayFunctor I C) R) = (positiveGenerators R d.I).rlp.llp :=
  source_cofibrations_eq d h R hR (fun n : ℕ+ => n)

/-- Actual positive trivial cofibrations retain all original positive free J arrows. -/
theorem positive_trivialCofibrations_eq_generators :
    let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := positiveModelCategory d h R hR
    trivialCofibrations (CategoryTheory.Mod (DayFunctor I C) R) = (positiveGenerators R d.J).rlp.llp :=
  source_trivialCofibrations_eq d h R hR (fun n : ℕ+ => n)

/-- The complete exact source rule compares the two actual constructed models on the same original carrier. -/
theorem positive_cofibrations_eq_ordinary_zero :
    let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := positiveModelCategory d h R hR
    cofibrations (CategoryTheory.Mod (DayFunctor I C) R) =
      (ordinaryModelCategory d h R hR).categoryWithCofibrations.cofibrations ⊓ zeroIsomorphisms R := by
  let e := cellularModuleGenerationRank d h
  let _ : Fact e.cardinal.IsRegular := e.regular
  let _ : OrderBot e.cardinal.ord.ToType := e.orderBot
  let _ : (positiveGenerators R d.I).IsCardinalForSmallObjectArgument e.cardinal :=
    projectiveI_eligible d h R hR (fun n : ℕ+ => n) e
  let _ : PreservesColimitsOfSize.{w, w} (zeroEvaluation R) := moduleEvaluationPreservesColimits R _
  let _ : PreservesWellOrderContinuousOfShape e.cardinal.ord.ToType (zeroEvaluation R) :=
    { preservesColimitsOfShape := fun _ _ => inferInstance }
  change (positiveGenerators R d.I).rlp.llp = (ordinaryGenerators R d.I).rlp.llp ⊓ zeroIsomorphisms R
  exact positiveGeneratedLeft_eq_ordinary_inf_zero R d.I e.cardinal

/-- Positive weak equivalences are tested at every and only original degree n>0. -/
theorem positive_weakEquivalence_iff
    {X Y : CategoryTheory.Mod (DayFunctor I C) R} (f : X ⟶ Y) :
    let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := positiveModelCategory d h R hR
    weakEquivalences (CategoryTheory.Mod (DayFunctor I C) R) f ↔
      ∀ n : ℕ, 0 < n → weakEquivalences C ((CategoryTheory.Mod.dayEvaluation R
          (CategoryTheory.Operad.SmallFinBijGroupoid.card n)).map f) := by
  let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := positiveModelCategory d h R hR
  change weakEquivalences (CategoryTheory.Mod (DayFunctor I C) R) f ↔ _
  rw [positive_weakEquivalences_eq d h R hR]
  exact positiveProperty_iff R _ f

/-- Positive fibrations leave degree zero unrestricted and test every original positive degree. -/
theorem positive_fibration_iff
    {X Y : CategoryTheory.Mod (DayFunctor I C) R} (f : X ⟶ Y) :
    let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := positiveModelCategory d h R hR
    fibrations (CategoryTheory.Mod (DayFunctor I C) R) f ↔
      ∀ n : ℕ, 0 < n → fibrations C ((CategoryTheory.Mod.dayEvaluation R (CategoryTheory.Operad.SmallFinBijGroupoid.card
          n)).map f) := by
  let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := positiveModelCategory d h R hR
  change fibrations (CategoryTheory.Mod (DayFunctor I C) R) f ↔ _
  rw [positive_fibrations_eq d h R hR]
  exact positiveProperty_iff R _ f

/-- Every original positive free/evaluation pair is Quillen for the actual positive model. -/
theorem positive_freeEvaluation_isQuillenAdjunction (n : ℕ) (hn : 0 < n) :
    let _ : ModelCategory (CategoryTheory.Mod (DayFunctor I C) R) := positiveModelCategory d h R hR
    (CategoryTheory.Mod.dayFreeAtEvaluationAdjunction R (CategoryTheory.Operad.SmallFinBijGroupoid.card
        n)).IsQuillenAdjunction :=
  source_freeEvaluation_isQuillenAdjunction d h R hR (fun n : ℕ+ => n) ⟨n, hn⟩

/-- The actual complete positive I small-object factorization value. -/
abbrev positiveCofibrantFactorizationData := sourceCofibrantFactorizationData d h R hR (fun n : ℕ+ => n)

/-- The actual complete positive J small-object factorization value. -/
abbrev positiveFibrantFactorizationData := sourceFibrantFactorizationData d h R hR (fun n : ℕ+ => n)

end HomotopicalAlgebra.PositiveLevelModel.CellularProjective
