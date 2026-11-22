/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.Chosen.CellHistories
import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.Chosen.Quillen
import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.CellularProjective.CellHistories
import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.CellularProjective.FiniteGroupQuillen
import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.FreeActions.UnitZero
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantSmashFlatness.Base
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.Basic

/-!
# Both full original sufficient sources for the positive level spectrum model

The first source is an actual tractable base with a genuine auxiliary compact
model and actual chosen tractable finite-action models. The second source is
the original cellular, quasitractable, strongly admissibly generated base,
using the existing projective finite-group models and actual cofibrant R_n.
All model outputs have the original symmetric spectrum carrier of an arbitrary
commutative Day monoid. No tensor unit cofibrancy or ordinary stability is asserted.
-/

set_option autoImplicit false
noncomputable section
universe w ν v u

open CategoryTheory Limits MorphismProperty MonoidalCategory MonObj
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj MonoidalClosed

namespace HomotopicalAlgebra.PositiveLevelModel

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

/-- The original quasitractable condition on the actual two generating source families. -/
structure QuasitractableSource : Prop where
  I_cofibrant_sources (i : d.I.toSet) : IsCofibrant i.1.left
  J_cofibrant_sources (j : d.J.toSet) : IsCofibrant j.1.left

variable [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [HasColimitsOfSize.{w, w} C] [HasLimitsOfSize.{w, w} C]

local instance contractBaseSmallColimits : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, w, w} C
local instance contractBaseSmallLimits : HasLimitsOfSize.{0, 0} C := hasLimitsOfSizeShrink.{0, 0, w, w} C
/-- The canonical Day structure on the existing symmetric sequence carrier. -/
local instance contractDayMonoidal : MonoidalCategory (DayFunctor I C) := inferInstance
/-- The original Day braiding used by the arbitrary commutative monoid R. -/
local instance contractDayBraided : BraidedCategory (DayFunctor I C) := inferInstance

/-- The full first original base alternative, with literal chosen-action induction and genuine auxiliary model. -/
structure PrettySmallChosenSource where
  monoidal_model : IsClosedSymmetricMonoidalModelCategory C
  locally_presentable : IsLocallyPresentable.{w} C
  quasitractable : QuasitractableSource d
  h_monoidal : HMonoidality C
  flat : PushoutProductLe (weakEquivalences C) (cofibrations C) (weakEquivalences C)
  /-- The genuine auxiliary model with the original compact generating endpoints. -/
  prettySmall : PrettySmallSource.{w} C
  /-- The actual tractable finite action models and original induction maps. -/
  chosenActions : ChosenActionModels.{w} C

variable (R : CommMon (SymmetricSequence C))

/-- The full second original alternative, including both compact endpoints of the genuine arbitrary coefficient orbit
cells. -/
structure CellularProjectiveSource : Prop where
  monoidal_model : IsClosedSymmetricMonoidalModelCategory C
  cellular : CellularSource d
  quasitractable : QuasitractableSource d
  h_monoidal : HMonoidality C
  flat : PushoutProductLe (weakEquivalences C) (cofibrations C) (weakEquivalences C)
  strongly_admissibly_generated : OperadicAcyclicCells.StrongAdmissibleGeneration.{w, ν} C d.I
  levels_cofibrant (n : ℕ) : IsCofibrant (R.X.functor.obj (CategoryTheory.Operad.SmallFinBijGroupoid.card n))

/-- The full first source constructs the actual ordinary model on the original arbitrary commutative R-module spectrum
carrier. -/
@[instance_reducible]
def firstCaseOrdinaryModelCategory (source : PrettySmallChosenSource d) : ModelCategory (SymmetricSpectrum R) := by
  let _ : IsLocallyPresentable.{w} C := source.locally_presentable
  exact Chosen.ordinaryModelCategory source.chosenActions source.prettySmall source.h_monoidal R.X

/-- The full first source constructs the actual positive model, with both genuine original free-family arguments. -/
@[instance_reducible]
def firstCasePositiveModelCategory (source : PrettySmallChosenSource d) : ModelCategory (SymmetricSpectrum R) := by
  let _ : IsLocallyPresentable.{w} C := source.locally_presentable
  exact Chosen.positiveModelCategory source.chosenActions source.prettySmall source.h_monoidal R.X

/-- The full second source constructs the corresponding actual ordinary projective spectrum model. -/
@[instance_reducible]
def secondCaseOrdinaryModelCategory (source : CellularProjectiveSource.{w, ν} d R) : ModelCategory (SymmetricSpectrum R)
    := by
  let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
  let _ : IsClosedSymmetricMonoidalModelCategory C := source.monoidal_model
  exact CellularProjective.ordinaryModelCategory d source.cellular R.X source.levels_cofibrant

/-- The full second source constructs the actual positive model without local presentability or pretty smallness. -/
@[instance_reducible]
def secondCasePositiveModelCategory (source : CellularProjectiveSource.{w, ν} d R) : ModelCategory (SymmetricSpectrum R)
    := by
  let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
  let _ : IsClosedSymmetricMonoidalModelCategory C := source.monoidal_model
  exact CellularProjective.positiveModelCategory d source.cellular R.X source.levels_cofibrant

/-- The first full source returns its actual original positive free I small object factor value. -/
def firstCaseCofibrantFactorizationData (source : PrettySmallChosenSource d) :
    let _ : ModelCategory (SymmetricSpectrum R) := firstCasePositiveModelCategory d R source
    FunctorialFactorizationData (cofibrations (SymmetricSpectrum R)) (trivialFibrations (SymmetricSpectrum R)) := by
  let _ : IsLocallyPresentable.{w} C := source.locally_presentable
  exact Chosen.positiveCofibrantFactorizationData source.chosenActions source.prettySmall source.h_monoidal R.X

/-- The first full source returns the original positive free J value at the same actual common rank. -/
def firstCaseFibrantFactorizationData (source : PrettySmallChosenSource d) :
    let _ : ModelCategory (SymmetricSpectrum R) := firstCasePositiveModelCategory d R source
    FunctorialFactorizationData (trivialCofibrations (SymmetricSpectrum R)) (fibrations (SymmetricSpectrum R)) := by
  let _ : IsLocallyPresentable.{w} C := source.locally_presentable
  exact Chosen.positiveFibrantFactorizationData source.chosenActions source.prettySmall source.h_monoidal R.X

/-- The second full source returns its actual original positive free I value without any presentability premise. -/
def secondCaseCofibrantFactorizationData (source : CellularProjectiveSource.{w, ν} d R) :
    let _ : ModelCategory (SymmetricSpectrum R) := secondCasePositiveModelCategory d R source
    FunctorialFactorizationData (cofibrations (SymmetricSpectrum R)) (trivialFibrations (SymmetricSpectrum R)) := by
  let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
  let _ : IsClosedSymmetricMonoidalModelCategory C := source.monoidal_model
  exact CellularProjective.positiveCofibrantFactorizationData d source.cellular R.X source.levels_cofibrant

/-- The second full source returns its actual original positive free J value at the same source-produced rank. -/
def secondCaseFibrantFactorizationData (source : CellularProjectiveSource.{w, ν} d R) :
    let _ : ModelCategory (SymmetricSpectrum R) := secondCasePositiveModelCategory d R source
    FunctorialFactorizationData (trivialCofibrations (SymmetricSpectrum R)) (fibrations (SymmetricSpectrum R)) := by
  let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
  let _ : IsClosedSymmetricMonoidalModelCategory C := source.monoidal_model
  exact CellularProjective.positiveFibrantFactorizationData d source.cellular R.X source.levels_cofibrant

/-- The first full source retains the exact actual ordinary cofibration and degree zero isomorphism rule. -/
theorem firstCase_cofibrations_eq_ordinary_zero (source : PrettySmallChosenSource d) :
    let _ : ModelCategory (SymmetricSpectrum R) := firstCasePositiveModelCategory d R source
    cofibrations (SymmetricSpectrum R) =
      (firstCaseOrdinaryModelCategory d R source).categoryWithCofibrations.cofibrations ⊓ zeroIsomorphisms R.X := by
  let _ : IsLocallyPresentable.{w} C := source.locally_presentable
  exact Chosen.positive_cofibrations_eq_ordinary_zero source.chosenActions source.prettySmall source.h_monoidal R.X

/-- The second full source retains that same exact rule on its two actually constructed models. -/
theorem secondCase_cofibrations_eq_ordinary_zero (source : CellularProjectiveSource.{w, ν} d R) :
    let _ : ModelCategory (SymmetricSpectrum R) := secondCasePositiveModelCategory d R source
    cofibrations (SymmetricSpectrum R) =
      (secondCaseOrdinaryModelCategory d R source).categoryWithCofibrations.cofibrations ⊓ zeroIsomorphisms R.X := by
  let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
  let _ : IsClosedSymmetricMonoidalModelCategory C := source.monoidal_model
  exact CellularProjective.positive_cofibrations_eq_ordinary_zero d source.cellular R.X source.levels_cofibrant

/-- All five positive classes of the first full source are the original underlying weak tests and chosen finite-action
lifting tests. -/
theorem firstCase_five_classes (source : PrettySmallChosenSource d) :
    let _ : ModelCategory (SymmetricSpectrum R) := firstCasePositiveModelCategory d R source
    weakEquivalences (SymmetricSpectrum R) = Chosen.levelWeak R.X true ∧
      cofibrations (SymmetricSpectrum R) = (actionGenerators R.X true source.chosenActions.I).rlp.llp ∧
      fibrations (SymmetricSpectrum R) = Chosen.levelFibrations source.chosenActions R.X true ∧
      trivialFibrations (SymmetricSpectrum R) = (actionGenerators R.X true source.chosenActions.I).rlp ∧
      trivialCofibrations (SymmetricSpectrum R) = (actionGenerators R.X true source.chosenActions.J).rlp.llp := by
  let _ : IsLocallyPresentable.{w} C := source.locally_presentable
  exact ⟨Chosen.source_weakEquivalences_eq source.chosenActions source.prettySmall source.h_monoidal R.X true,
    Chosen.source_cofibrations_eq source.chosenActions source.prettySmall source.h_monoidal R.X true,
    Chosen.source_fibrations_eq source.chosenActions source.prettySmall source.h_monoidal R.X true,
    Chosen.source_trivialFibrations_eq source.chosenActions source.prettySmall source.h_monoidal R.X true,
    Chosen.source_trivialCofibrations_eq source.chosenActions source.prettySmall source.h_monoidal R.X true⟩

/-- All five classes of the full second source retain the original positive free I/J and underlying positive
evaluations. -/
theorem secondCase_five_classes (source : CellularProjectiveSource.{w, ν} d R) :
    let _ : ModelCategory (SymmetricSpectrum R) := secondCasePositiveModelCategory d R source
    weakEquivalences (SymmetricSpectrum R) = positiveProperty R.X (weakEquivalences C) ∧
      cofibrations (SymmetricSpectrum R) = (positiveGenerators R.X d.I).rlp.llp ∧
      fibrations (SymmetricSpectrum R) = positiveProperty R.X (fibrations C) ∧
      trivialFibrations (SymmetricSpectrum R) = positiveProperty R.X (trivialFibrations C) ∧
      trivialCofibrations (SymmetricSpectrum R) = (positiveGenerators R.X d.J).rlp.llp := by
  let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
  let _ : IsClosedSymmetricMonoidalModelCategory C := source.monoidal_model
  exact ⟨CellularProjective.positive_weakEquivalences_eq d source.cellular R.X source.levels_cofibrant,
    CellularProjective.positive_cofibrations_eq_generators d source.cellular R.X source.levels_cofibrant,
    CellularProjective.positive_fibrations_eq d source.cellular R.X source.levels_cofibrant,
    CellularProjective.positive_trivialFibrations_eq d source.cellular R.X source.levels_cofibrant,
    CellularProjective.positive_trivialCofibrations_eq_generators d source.cellular R.X source.levels_cofibrant⟩

/-- Every original base free/evaluation pair in n>0 is Quillen under the full first source alternative. -/
theorem firstCase_baseFreeEvaluation_isQuillenAdjunction (source : PrettySmallChosenSource d)
    (n : ℕ) (hn : 0 < n) :
    let _ : ModelCategory (SymmetricSpectrum R) := firstCasePositiveModelCategory d R source
    (CategoryTheory.Mod.dayFreeAtEvaluationAdjunction R.X (CategoryTheory.Operad.SmallFinBijGroupoid.card
        n)).IsQuillenAdjunction := by
  let _ : IsLocallyPresentable.{w} C := source.locally_presentable
  exact Chosen.positive_baseFreeEvaluation_isQuillenAdjunction source.chosenActions source.prettySmall
      source.h_monoidal R.X n hn

/-- Every original finite-action free/evaluation pair at n>0 is Quillen under the full first source alternative. -/
theorem firstCase_actionFreeEvaluation_isQuillenAdjunction (source : PrettySmallChosenSource d)
    (n : ℕ) (hn : 0 < n) :
    let _ : ModelCategory (SymmetricSpectrum R) := firstCasePositiveModelCategory d R source
    let _ : ModelCategory (degreeActionCategory (C := C) n) := source.chosenActions.model n
    (degreeActionAdjunction R.X n).IsQuillenAdjunction := by
  let _ : IsLocallyPresentable.{w} C := source.locally_presentable
  exact Chosen.positive_freeEvaluation_isQuillenAdjunction source.chosenActions source.prettySmall source.h_monoidal
      R.X n hn

/-- Every original positive base free/evaluation pair is Quillen under the full second source alternative. -/
theorem secondCase_baseFreeEvaluation_isQuillenAdjunction (source : CellularProjectiveSource.{w, ν} d R)
    (n : ℕ) (hn : 0 < n) :
    let _ : ModelCategory (SymmetricSpectrum R) := secondCasePositiveModelCategory d R source
    (CategoryTheory.Mod.dayFreeAtEvaluationAdjunction R.X (CategoryTheory.Operad.SmallFinBijGroupoid.card
        n)).IsQuillenAdjunction := by
  let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
  let _ : IsClosedSymmetricMonoidalModelCategory C := source.monoidal_model
  exact CellularProjective.positive_freeEvaluation_isQuillenAdjunction d source.cellular R.X source.levels_cofibrant n
      hn

/-- Every genuine positive projective finite-action pair is Quillen for the same actual second-source model. -/
theorem secondCase_actionFreeEvaluation_isQuillenAdjunction (source : CellularProjectiveSource.{w, ν} d R)
    (n : ℕ) (hn : 0 < n) :
    let _ : ModelCategory (SymmetricSpectrum R) := secondCasePositiveModelCategory d R source
    let _ : ModelCategory (degreeActionCategory (C := C) n) := finiteGroupModelCategory d n
    (degreeActionAdjunction R.X n).IsQuillenAdjunction := by
  let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
  let _ : IsClosedSymmetricMonoidalModelCategory C := source.monoidal_model
  exact CellularProjective.positive_actionFreeEvaluation_isQuillenAdjunction d source.cellular R.X
      source.levels_cofibrant n hn

end HomotopicalAlgebra.PositiveLevelModel
