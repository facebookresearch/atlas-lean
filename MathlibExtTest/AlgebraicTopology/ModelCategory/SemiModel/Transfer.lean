/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.SemiModel.Basic
public import MathlibExt.AlgebraicTopology.ModelCategory.SemiModel.Transfer
import all MathlibExt.AlgebraicTopology.ModelCategory.SemiModel.Basic
import all MathlibExt.AlgebraicTopology.ModelCategory.SemiModel.Transfer
import Batteries.Tactic.Lint

/-!
# Full original-variable clients for the source-restricted semi-model transfer

The source model, actual adjunction, original I/J families, both different
source-smallness contracts and the original initial-object input are retained.
Both trivial-cofibration/fibration assertions explicitly require intrinsic
cofibrancy of the original algebra source.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe w uC vC uD vD

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open CategoryTheory.SmallObject HomotopicalAlgebra.SemiModel

namespace SemiModelFullSourceClient

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [HasInitial D]
  [HasLimitsOfSize.{w, w} D] [HasColimitsOfSize.{w, w} D] [LocallySmall.{w} D]
  (F : C ⥤ D) (U : D ⥤ C) (adj : F ⊣ U)
  (I J : MorphismProperty C) [I.IsSmall.{w}] [J.IsSmall.{w}]
  (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
  [PreservesNonemptyOrdinalColimits.{w} U]
  (criterion : FreeCellPushoutCriterion.{w} F U)
  (hInitial : IsCofibrant (U.obj (⊥_ D)))
  (hSourceI : UniformRelativeSourceSmallness.{w} (freeGenerators F I))
  (hSourceJ : UniformRelativeSourceSmallnessOnSources.{w}
    (freeGenerators F J) (fun X => IsCofibrant (U.obj X)))

/-- The actual source data constructs the complete transfer rather than supplying its output fields. -/
def originalTransfer : CofibrantlyGeneratedSemiModelTransfer F U I J hSourceI hSourceJ :=
  cofibrantlyGeneratedSemiModelTransfer F U adj I J hI hJ criterion hInitial hSourceI hSourceJ

local notation "t" => originalTransfer F U adj I J hI hJ criterion hInitial hSourceI hSourceJ

example {X Y : D} (f : X ⟶ Y) :
    (t).semiModel.weakEquivalences f ↔ weakEquivalences C (U.map f) := by
  rw [(t).weak_eq]
  rfl

example {X Y : D} (f : X ⟶ Y) :
    (t).semiModel.fibrations f ↔ fibrations C (U.map f) := by
  rw [(t).fibrations_eq]
  rfl

example {X Y : D} (f : X ⟶ Y) :
    MapFactorizationData (t).semiModel.cofibrations (t).semiModel.trivialFibrations f :=
  (t).semiModel.cofibrationFactorization.factorizationData f

example {X Y : D} (f : X ⟶ Y) (hX : (t).semiModel.IsCofibrant X) :
    MapFactorizationData (t).semiModel.trivialCofibrations (t).semiModel.fibrations f :=
  (t).semiModel.trivialCofibrationFactorization.factorizationData f hX

example {X Y A B : D} (f : X ⟶ Y) (p : A ⟶ B)
    (hX : (t).semiModel.IsCofibrant X) (hf : (t).semiModel.trivialCofibrations f)
    (hp : (t).semiModel.fibrations p) : HasLiftingProperty f p :=
  (t).semiModel.trivialCofibration_lifting f p hX hf hp

example {X Y A B : D} (f : X ⟶ Y) (p : A ⟶ B)
    (hf : (t).semiModel.cofibrations f) (hp : (t).semiModel.trivialFibrations p) :
    HasLiftingProperty f p := (t).semiModel.cofibration_lifting f p hf hp

example (X : D) (hX : (t).semiModel.IsCofibrant X) : IsCofibrant (U.obj X) :=
  (t).underlyingCofibrant X hX

example {X Y : D} (f : X ⟶ Y) (hX : (t).semiModel.IsCofibrant X)
    (hf : (t).semiModel.cofibrations f) : cofibrations C (U.map f) :=
  (t).underlyingCofibration f hX hf

example : (freeGenerators F I).rlp = (t).semiModel.trivialFibrations := (t).I_rlp

example : (freeGenerators F J).rlp = (t).semiModel.fibrations := (t).J_rlp

example (a b : Arrow D) (φ : a ⟶ b) :
    (t).semiModel.trivialCofibrationFactorization.i.app a ≫
      (t).semiModel.trivialCofibrationFactorization.mapZ φ =
    φ.left ≫ (t).semiModel.trivialCofibrationFactorization.i.app b :=
  (t).semiModel.trivialCofibrationFactorization.i_mapZ φ

example (a b : Arrow D) (φ : a ⟶ b) :
    (t).semiModel.trivialCofibrationFactorization.mapZ φ ≫
      (t).semiModel.trivialCofibrationFactorization.p.app b =
    (t).semiModel.trivialCofibrationFactorization.p.app a ≫ φ.right :=
  (t).semiModel.trivialCofibrationFactorization.mapZ_p φ

local instance : Fact (t).cardinal.IsRegular := (t).regular
/-- Use the same original bottom stored by the generated cardinal. -/
local instance originalOrdinalBottom : OrderBot (t).cardinal.ord.ToType := (t).orderBot

example (p : (freeGenerators F J).toSet)
    (H : (t).cardinal.ord.ToType ⥤ D) [H.IsWellOrderContinuous]
    (hH : ∀ j, ¬ IsMax j → relativeCellMaps.{w} (freeGenerators F J)
      (H.map (homOfLE (Order.le_succ j))))
    (hUnderlying : ∀ j, ¬ IsMax j → IsCofibrant (U.obj (H.obj j))) :
    PreservesColimit H (coyoneda.obj (Opposite.op p.1.left)) :=
  UniformRelativeSourceSmallnessOnSources.sourceBound_spec hSourceJ p (t).cardinal
    ((t).sourceJ_bounds p) H hH hUnderlying

end SemiModelFullSourceClient

#print axioms HomotopicalAlgebra.SemiModel.cofibrantlyGeneratedSemiModelTransfer
#print axioms HomotopicalAlgebra.SemiModel.semiModelCategoryAtCardinal
#print axioms HomotopicalAlgebra.SemiModel.rawJ_projectionFibration
#print axioms HomotopicalAlgebra.SemiModel.rawJ_underlyingTrivialCofibration
#print axioms HomotopicalAlgebra.SemiModel.trivialCofibration_liftingAtCardinal
#print axioms HomotopicalAlgebra.SemiModel.cofibrantSource_underlying
#print axioms HomotopicalAlgebra.SemiModel.cofibration_underlying_of_cofibrantSource

#lint only unusedArguments in MathlibExt.AlgebraicTopology.ModelCategory.SemiModel.Basic
#lint+ in MathlibExt.AlgebraicTopology.ModelCategory.SemiModel.Basic
#lint only unusedArguments in MathlibExt.AlgebraicTopology.ModelCategory.SemiModel.Transfer
#lint+ in MathlibExt.AlgebraicTopology.ModelCategory.SemiModel.Transfer
