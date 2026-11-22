/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.SourceIteration
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.StabilizationTransformation
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.StableHomotopy.IntegerGroups
import MathlibExt.AlgebraicTopology.Spectra.Sequential.OrderedLoop.EvaluationAssociation
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.DiagonalHomotopy
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.IntegerColimitNormalization
import MathlibExt.Algebra.Category.Grp.FilteredSourceTypeColimit
import
  MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.LoopTailAllPointComparison
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalTelescopeOmegaHomRetract
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalOmegaTargetPreservation

/-!
# Original Symmetric source criterion for signed integer homotopy maps

The actual finite-bijection labels, sphere coefficients, native function functor,
input coaugmentation, mapping-cylinder telescope and chosen colimits are retained.
The permutation correction compares original input diagrams before transporting
their homotopy-group quotient maps. The final criterion is conditional only on
the displayed equality of the original one-step lambda coordinate with its
native structure transpose. Neither input endpoint is assumed Omega, and no
level-weak telescope-map or detector outcome is supplied.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory BraidedCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport.Sequential
open NativeOmegaRecovery
open PointedCGWH.SequentialSpectrum.OrderedLoop.EvaluationAssociationGeometry
open HomotopicalAlgebra.EnrichedProjective.Native.LoopTailAllPointComparison
open scoped MonoidalClosed CGWH.modelCategory

namespace PointedCGWH.Spectra.OriginalSymmetricPiStarOmegaTests

attribute [local instance] MonoidalClosed.enrichedCategorySelf
  MonoidalClosed.enrichedOrdinaryCategorySelf
  PointedCGWH.EnrichedMapping.hasSmallLimits
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal

attribute [local irreducible] CategoryTheory.Mod.internalHom
  NativeSymmetricR.functor NativeSymmetricLambda.coaugmentation

/-- The complete original native symmetric carrier, with both independent universes. -/
abbrev Carrier := Actual.SymmetricCarrier.{u, v}
/-- Every original finite-bijection label remains in the full indexing groupoid. -/
abbrev Index := Operad.SmallFinBijGroupoid
/-- The original full sphere sequence supplies every coefficient degree and map. -/
abbrev coefficient := PointedCGWH.sphereSequence.{u, v}
/-- The complete original native first-free function functor retains all input arrows. -/
abbrev R : Carrier.{u, v} ⥤ Carrier.{u, v} := NativeSymmetricR.functor.{u, v}
/-- The full original native coaugmentation is retained before any input component. -/
abbrev eta : 𝟭 Carrier.{u, v} ⟶ R.{u, v} := NativeSymmetricLambda.coaugmentation.{u, v}

/-- The full original underlying prespectrum uses the actual enriched restriction. -/
abbrev j : Carrier.{u, v} ⥤ PointedCGWH.SequentialSpectrum.{u, v} :=
  Actual.SymmetricIntegerHomotopy.underlyingSequential

/-- The original sequence retains all its finite-bijection maps. -/
abbrev bare (X : Carrier.{u, v}) : Index ⥤ PointedCGWH.{u, v} :=
  ((PointedCGWH.symmetricSequenceRestriction.{u, v}).obj X).functor

/-- Every original natural degree is the original Symmetric operator object. -/
abbrev index (m : ℕ) : PointedCGWH.SymmetricOperatorIndex.{u, v} := symmetricDegree m

/-- The original degree evaluation keeps both objects and complete native arrows. -/
abbrev level (m : ℕ) : Carrier.{u, v} ⥤ PointedCGWH.{u, v} := evaluation (index m)

/-- The actual input restriction preserves the entire original evaluation functor. -/
theorem j_level (m : ℕ) : j.{u, v} ⋙ PointedCGWH.SequentialSpectrum.evaluation m = level m := by
  refine CategoryTheory.Functor.ext
    (F := j.{u, v} ⋙ PointedCGWH.SequentialSpectrum.evaluation m)
    (G := level.{u, v} m) (fun X => rfl) (h_map := ?_)
  intro X Y f
  change PointedCGWH.SequentialSpectrum.levelMap (j.map f) m =
    eqToHom rfl ≫ component f (index m) ≫ eqToHom rfl
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using
    Actual.SymmetricIntegerHomotopy.underlying_map f m

/-- The actual original function/free comparison supplies every next-level loop chart. -/
abbrev stepEvaluation (m : ℕ) : R.{u, v} ⋙ level m ≅ level (m + 1) ⋙ PointedCGWH.loop :=
  NativeSymmetricR.levelComparison m

/-- Original loop powers and the generic powers have the same entire functors. -/
theorem loopPower_same (n : ℕ) :
    PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower.{u, v} n =
      Functor.Iteration.iterate PointedCGWH.loop n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun F => F ⋙ PointedCGWH.loop) ih

/-- Both loop-count maps retain those original complete functor equalities. -/
def loopComparison (n : ℕ) :
    PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower.{u, v} n ≅
      Functor.Iteration.iterate PointedCGWH.loop n := eqToIso (loopPower_same n)

/-- The actual arithmetic map reassociates the original next Symmetric degree. -/
def lowerCast (n m : ℕ) : finiteIndex (m + (n + 1)) ≅ finiteIndex (m + n + 1) :=
  eqToIso (congrArg finiteIndex (Nat.add_assoc m n 1).symm)

/-- The original coefficient-first degree has its actual original arithmetic map. -/
def upperCast (n m : ℕ) : finiteIndex 1 ⊗ finiteIndex (m + n) ≅ finiteIndex (m + (n + 1)) :=
  eqToIso (congrArg finiteIndex ((Nat.add_comm 1 (m + n)).trans (Nat.add_assoc m n 1)))

/-- The complete original permutation moves each added coordinate ahead of the fixed level. -/
def ell : ∀ n m : ℕ, finiteIndex (m + n) ≅ finiteIndex (m + n) :=
  Nat.rec (fun m => Iso.refl (finiteIndex m))
    (fun n previous m => lowerCast n m ≪≫
      (β_ (finiteIndex 1) (finiteIndex (m + n))).symm ≪≫
        (tensorLeft (finiteIndex 1)).mapIso (previous m) ≪≫ upperCast n m)

/-- The forward permutation retains its original block braid and both degree casts. -/
private theorem blockCancellation {C : Type*} [Category C] {A B D : C}
    (l : A ≅ B) (b : D ≅ B) (c : D ≅ D) (u : D ≅ A) :
    b.hom ≫ l.inv ≫ (l ≪≫ b.symm ≪≫ c ≪≫ u).hom = c.hom ≫ u.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]

theorem ell_successor_label (n m : ℕ) :
    (β_ (finiteIndex 1) (finiteIndex (m + n))).hom ≫ (lowerCast n m).inv ≫
        (ell (n + 1) m).hom =
      finiteIndex 1 ◁ (ell n m).hom ≫ (upperCast n m).hom := by
  exact blockCancellation (lowerCast n m)
    (β_ (finiteIndex 1) (finiteIndex (m + n)))
    ((tensorLeft (finiteIndex 1)).mapIso (ell n m)) (upperCast n m)

/-- Every original permutation value is natural for every complete native input arrow. -/
def indexValueNatIso (n m : ℕ) : level.{u, v} (m + n) ≅ level (m + n) :=
  NatIso.ofComponents (fun X => (bare X).mapIso (ell n m)) (fun f =>
    NativeSymmetricShiftUnit.ordinaryMap_naturality f (ell n m).hom)

/-- Every original labelled action is transposed at its actual sphere coefficient. -/
def labelledAdjoint (X : Carrier.{u, v}) (a n k : Index) (f : a ⊗ n ⟶ k) :
    (bare X).obj n ⟶ (ihom (coefficient.functor.obj a)).obj ((bare X).obj k) :=
  MonoidalClosed.curry (PointedCGWH.SymmetricModulePresentation.reconstructedArrowAction X a n k f)

/-- Every full source-index map is retained by the same original coefficient transpose. -/
theorem labelledAdjoint_source (X : Carrier.{u, v}) (a n n' k : Index)
    (f : n ⟶ n') (g : a ⊗ n' ⟶ k) :
    (bare X).map f ≫ labelledAdjoint X a n' k g =
      labelledAdjoint X a n k ((a ◁ f) ≫ g) := by
  unfold labelledAdjoint
  rw [← MonoidalClosed.curry_natural_left]
  exact congrArg MonoidalClosed.curry
    (PointedCGWH.SymmetricModulePresentation.reconstructedArrowAction_input X a n n' k f g)

/-- The complete original target-index map is retained by its whole internal Hom image. -/
theorem labelledAdjoint_target (X : Carrier.{u, v}) (a n k l : Index)
    (f : a ⊗ n ⟶ k) (g : k ⟶ l) :
    labelledAdjoint X a n k f ≫ (ihom (coefficient.functor.obj a)).map ((bare X).map g) =
      labelledAdjoint X a n l (f ≫ g) := by
  unfold labelledAdjoint
  rw [← MonoidalClosed.curry_natural_right]
  exact congrArg MonoidalClosed.curry
    (PointedCGWH.SymmetricModulePresentation.reconstructedArrowAction_target X a n k l f g)

/-- The unchanged original full-family Omega map has exactly its original labelled transpose. -/
theorem omegaMap_eq_labelledAdjoint (X : Carrier.{u, v}) (n a : Index) :
    NativeSymmetricDelooping.omegaMap X n a =
      labelledAdjoint X a n (n ⊗ a) (β_ a n).hom := by
  apply MonoidalClosed.uncurry_injective
  exact (NativeSymmetricDelooping.omegaMap_uncurry X n a).trans
    (MonoidalClosed.uncurry_curry
      (PointedCGWH.SymmetricModulePresentation.reconstructedArrowAction X a n (n ⊗ a)
        (β_ a n).hom)).symm

/-- The actual native family and the original coordinate use the same full adjoint. -/
theorem omegaMap_eq_symmetricAdjoint (X : Carrier.{u, v}) (n a : Index) :
    NativeSymmetricDelooping.omegaMap X n a = symmetricAdjoint X n a := rfl

/-- The entire original block label keeps both original source and target permutation actions. -/
theorem ell_step_adjoint (X : Carrier.{u, v}) (n m : ℕ) :
    NativeSymmetricDelooping.omegaMap X (finiteIndex (m + n)) (finiteIndex 1) ≫
        (ihom (coefficient.functor.obj (finiteIndex 1))).map
          ((bare X).map ((lowerCast n m).inv ≫ (ell (n + 1) m).hom)) =
      (bare X).map (ell n m).hom ≫
        labelledAdjoint X (finiteIndex 1) (finiteIndex (m + n))
          (finiteIndex (m + (n + 1))) (upperCast n m).hom := by
  rw [omegaMap_eq_labelledAdjoint]
  have hTarget := labelledAdjoint_target X (finiteIndex 1) (finiteIndex (m + n))
    (finiteIndex (m + n + 1)) (finiteIndex (m + (n + 1)))
    (β_ (finiteIndex 1) (finiteIndex (m + n))).hom
    ((lowerCast n m).inv ≫ (ell (n + 1) m).hom)
  have hLabel := congrArg
    (labelledAdjoint X (finiteIndex 1) (finiteIndex (m + n)) (finiteIndex (m + (n + 1))))
    (ell_successor_label n m)
  exact hTarget.trans (hLabel.trans (labelledAdjoint_source X (finiteIndex 1)
    (finiteIndex (m + n)) (finiteIndex (m + n)) (finiteIndex (m + (n + 1)))
    (ell n m).hom (upperCast n m).hom).symm)

/-- The actual original index point has the same complete original sequence value map. -/
theorem indexMap_original (X : Carrier.{u, v}) {n k : Index} (e : n ≅ k) :
    indexMap X (symmetricIndexIso.{u, v} e).hom = (bare X).map e.hom := by
  unfold indexMap
  rw [symmetricIndexIso_hom]
  change (eHomEquiv PointedCGWH.{u, v}).symm
    ((PointedCGWH.basedDiscreteIncl.{u, v, 0} (n ⟶ k) e.hom ≫
      PointedCGWH.symmetricIndexInclusion.{u, v}.map
        ((PointedCGWH.copowerRestriction.{u, v, 0} Index).obj n)
        ((PointedCGWH.copowerRestriction.{u, v, 0} Index).obj k)) ≫
      X.toEnrichedFunctor.map (PointedCGWH.symmetricOperatorObj.{u, v} n)
        (PointedCGWH.symmetricOperatorObj.{u, v} k)) = _
  exact (congrArg (eHomEquiv PointedCGWH.{u, v}).symm (Category.assoc _ _ _)).trans
    (PointedCGWH.symmetricSequenceRestriction_map X e.hom).symm

/-- The actual circle-to-power-one map retains its original coefficient unitor. -/
theorem circleToPowerOne_original :
    circleToPowerOneIso.{u, v}.hom = NativeSymmetricDelooping.firstCoefficientIso.{u, v}.inv :=
  rfl

/-- The original first coefficient gives both complete scalar internal-Hom maps. -/
def firstScalarIso (Z : PointedCGWH.{u, v}) :
    (ihom (coefficient.functor.obj (finiteIndex 1))).obj Z ≅ PointedCGWH.loop.obj Z :=
  coefficientPreIso NativeSymmetricDelooping.firstCoefficientIso.symm Z

/-- The original forward scalar map is exactly precomposition with the first coefficient inverse. -/
theorem firstScalarIso_hom (Z : PointedCGWH.{u, v}) :
    (firstScalarIso Z).hom =
      (MonoidalClosed.pre NativeSymmetricDelooping.firstCoefficientIso.inv).app Z := rfl

/-- The actual original successor permutation cancels the native coefficient-first braid. -/
theorem successorTarget_label (n : ℕ) :
    (β_ (finiteIndex 1) (finiteIndex n)).hom ≫ (successorTargetPermutation n).hom =
      eqToHom (congrArg finiteIndex (Nat.add_comm 1 n)) :=
  Iso.hom_inv_id_assoc (β_ (finiteIndex 1) (finiteIndex n)) _

set_option backward.isDefEq.respectTransparency false in
/-- The actual sequential restriction keeps the original full coefficient and permutation. -/
theorem sequentialAdjoint_label (X : Carrier.{u, v}) (n : ℕ) :
    sequentialAdjoint (j.obj X) n =
      labelledAdjoint X (finiteIndex 1) (finiteIndex n) (finiteIndex (n + 1))
        (eqToHom (congrArg finiteIndex (Nat.add_comm 1 n))) ≫
          (firstScalarIso ((bare X).obj (finiteIndex (n + 1)))).hom := by
  let S : PointedCGWH.{u, v} := coefficient.{u, v}.functor.obj (finiteIndex 1)
  let Z := (bare X).obj (finiteIndex (n + 1))
  let t := (bare X).map (successorTargetPermutation n).hom
  let c := (firstScalarIso Z).hom
  let w := NativeSymmetricDelooping.omegaMap X (finiteIndex n) (finiteIndex 1)
  have hValue := indexMap_original X (successorTargetPermutation n)
  have hv : (successorValueIso X n).hom = t :=
    (indexValueIso_hom X (successorIndexIso n)).trans hValue
  have hc : (firstScalarIso (X.toEnrichedFunctor.obj (symmetricDegree (n + 1)))).hom = c := rfl
  have hw : NativeSymmetricDelooping.omegaMap X (finiteIndex n) (finiteIndex 1) = w := rfl
  have hNative := sequentialSymmetric_adjoint n X
  have hFormula : sequentialAdjoint (j.obj X) n = w ≫ (ihom S).map t ≫ c := by
    simpa only [oneStepComparisonIso, Iso.trans_hom, Functor.mapIso_hom,
      coefficientPreIso, circleToPowerOne_original, hv,
      ← omegaMap_eq_symmetricAdjoint, ← firstScalarIso_hom, hc, hw, S, coefficient]
      using hNative
  have hTarget := labelledAdjoint_target X (finiteIndex 1) (finiteIndex n)
    (finiteIndex n ⊗ finiteIndex 1) (finiteIndex (n + 1))
    (β_ (finiteIndex 1) (finiteIndex n)).hom (successorTargetPermutation n).hom
  have hW := omegaMap_eq_labelledAdjoint X (finiteIndex n) (finiteIndex 1)
  have hLabel := congrArg (labelledAdjoint X (finiteIndex 1) (finiteIndex n)
    (finiteIndex (n + 1))) (successorTarget_label n)
  exact hFormula.trans
    ((Category.assoc w ((ihom S).map t) c).symm.trans
      (congrArg (fun f => f ≫ c)
        ((congrArg (fun f => f ≫ (ihom S).map t) hW).trans (hTarget.trans hLabel))))

/-- Both original degree casts retain their whole coefficient-first successor label. -/
theorem successorCast_label (n m : ℕ) :
    eqToHom (congrArg finiteIndex (Nat.add_comm 1 (m + n))) ≫ (lowerCast n m).inv =
      (upperCast n m).hom := by
  exact eqToHom_trans (congrArg finiteIndex (Nat.add_comm 1 (m + n)))
    (congrArg finiteIndex (Nat.add_assoc m n 1))

/-- The actual j successor retains its whole native level arithmetic map. -/
theorem sequentialAdjoint_sourceCast (X : Carrier.{u, v}) (n m : ℕ) :
    sequentialAdjoint (j.obj X) (m + n) ≫
        PointedCGWH.loop.map ((bare X).map (lowerCast n m).inv) =
      labelledAdjoint X (finiteIndex 1) (finiteIndex (m + n))
        (finiteIndex (m + (n + 1))) (upperCast n m).hom ≫
          (firstScalarIso ((bare X).obj (finiteIndex (m + (n + 1))))).hom := by
  let S : PointedCGWH.{u, v} := coefficient.{u, v}.functor.obj (finiteIndex 1)
  let Z := (bare X).obj (finiteIndex (m + n + 1))
  let T := (bare X).obj (finiteIndex (m + (n + 1)))
  let g := (bare X).map (lowerCast n m).inv
  let cZ := (firstScalarIso Z).hom
  let cT := (firstScalarIso T).hom
  let a := labelledAdjoint X (finiteIndex 1) (finiteIndex (m + n))
    (finiteIndex (m + n + 1)) (eqToHom (congrArg finiteIndex (Nat.add_comm 1 (m + n))))
  have hFirst := congrArg (fun h => h ≫ PointedCGWH.loop.map g)
    (sequentialAdjoint_label X (m + n))
  have hPre := (MonoidalClosed.pre NativeSymmetricDelooping.firstCoefficientIso.inv).naturality g
  have hTarget := labelledAdjoint_target X (finiteIndex 1) (finiteIndex (m + n))
    (finiteIndex (m + n + 1)) (finiteIndex (m + (n + 1)))
    (eqToHom (congrArg finiteIndex (Nat.add_comm 1 (m + n)))) (lowerCast n m).inv
  have hLabel := congrArg (labelledAdjoint X (finiteIndex 1) (finiteIndex (m + n))
    (finiteIndex (m + (n + 1)))) (successorCast_label n m)
  exact hFirst.trans ((Category.assoc a cZ (PointedCGWH.loop.map g)).trans
    ((congrArg (fun h => a ≫ h) hPre.symm).trans
      ((Category.assoc a ((ihom S).map g) cT).symm.trans
        (congrArg (fun h => h ≫ cT) (hTarget.trans hLabel)))))

/-- This is the actual original coaugmentation in its original one-step evaluation chart. -/
abbrev originalCoordinate (m : ℕ) : level.{u, v} m ⟶ level (m + 1) ⋙ PointedCGWH.loop :=
  Functor.CoaugmentationEvaluation.coordinate PointedCGWH.loop level stepEvaluation eta m

/-- Every actual coordinate retains the whole original lambda and its original free comparison. -/
theorem originalCoordinate_app (m : ℕ) (X : Carrier.{u, v}) :
    (originalCoordinate m).app X =
      (level m).map (eta.app X) ≫ (stepEvaluation m).hom.app X :=
  Functor.CoaugmentationEvaluation.coordinate_app PointedCGWH.loop level stepEvaluation eta m X

/-- Every full actual R input iterate retains its original source-ordered evaluation maps. -/
def nativeEvaluation (n m : ℕ) :
    Functor.Iteration.iterate R.{u, v} n ⋙ level m ≅
      level (m + n) ⋙ Functor.Iteration.iterate PointedCGWH.loop n :=
  Functor.CoaugmentationEvaluation.comparison R PointedCGWH.loop level stepEvaluation n m

/-- The entire original loop prefix retains the same loop-count equality. -/
def loopPrefix (n : ℕ) : Functor.Iteration.iterate PointedCGWH.loop.{u, v} (n + 1) ≅
    PointedCGWH.loop ⋙ Functor.Iteration.iterate PointedCGWH.loop n :=
  Functor.Iteration.iteratePrefixIso PointedCGWH.loop n

/-- The original native prefix retains the whole loop equality and original level cast. -/
def nativePrefix (n m : ℕ) :
    (level.{u, v} (m + n + 1) ⋙ PointedCGWH.loop) ⋙
        Functor.Iteration.iterate PointedCGWH.loop n ≅
      level (m + (n + 1)) ⋙ Functor.Iteration.iterate PointedCGWH.loop (n + 1) :=
  Functor.CoaugmentationEvaluation.evaluationTail PointedCGWH.loop level n m

universe uC vC uD vD

private theorem sourceEvaluation_input_expanded
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (F : C ⥤ C) (L : D ⥤ D) (E : ℕ → C ⥤ D)
    (e : ∀ m, F ⋙ E m ≅ E (m + 1) ⋙ L) (η : 𝟭 C ⟶ F) (n m : ℕ) (X : C) :
    (E m).map ((Functor.Iteration.inputTransition η n).app X) ≫
        (Functor.CoaugmentationEvaluation.comparison F L E e (n + 1) m).hom.app X =
      (Functor.CoaugmentationEvaluation.comparison F L E e n m).hom.app X ≫
        (Functor.Iteration.iterate L n).map
          ((Functor.CoaugmentationEvaluation.coordinate L E e η (m + n)).app X) ≫
            (Functor.CoaugmentationEvaluation.evaluationTail L E n m).hom.app X :=
  (Functor.CoaugmentationEvaluation.inputTransition_square L E e η n m X).trans
    (congrArg (fun f => (Functor.CoaugmentationEvaluation.comparison F L E e n m).hom.app X ≫ f)
      (Functor.CoaugmentationEvaluation.diagonalTransition_app L E e η n m X))

theorem nativeEvaluation_input (X : Carrier.{u, v}) (n m : ℕ) :
    (level m).map ((Functor.Iteration.inputTransition eta n).app X) ≫
        (nativeEvaluation (n + 1) m).hom.app X =
      (nativeEvaluation n m).hom.app X ≫
        (Functor.Iteration.iterate PointedCGWH.loop n).map ((originalCoordinate (m + n)).app X) ≫
          (nativePrefix n m).hom.app X :=
  sourceEvaluation_input_expanded R PointedCGWH.loop level stepEvaluation eta n m X

/-- The complete actual level transport is the original arithmetic equality map. -/
theorem lowerCast_value (X : Carrier.{u, v}) (n m : ℕ) :
    (bare X).map (lowerCast n m).inv =
      eqToHom (congrArg (bare X).obj (congrArg finiteIndex (Nat.add_assoc m n 1))) :=
  eqToHom_map (bare X) (congrArg finiteIndex (Nat.add_assoc m n 1))

private theorem evaluationTail_hom_app
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (L : D ⥤ D) (E : ℕ → C ⥤ D) (n m : ℕ) (X : C) :
    (Functor.CoaugmentationEvaluation.evaluationTail L E n m).hom.app X =
      (Functor.Iteration.iteratePrefixIso L n).inv.app ((E (m + n + 1)).obj X) ≫
        (Functor.Iteration.iterate L (n + 1)).map
          ((eqToIso (congrArg E (Nat.add_assoc m n 1))).hom.app X) := by
  simp only [Functor.CoaugmentationEvaluation.evaluationTail,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp]

/-- Every actual degree transport is the full original ordinary index map. -/
theorem levelCast_hom (X : Carrier.{u, v}) {n k : ℕ} (h : n = k) :
    (eqToIso (congrArg level.{u, v} h)).hom.app X =
      (bare X).map (eqToHom (congrArg finiteIndex h)) := by
  cases h
  change 𝟙 ((bare X).obj (finiteIndex n)) = (bare X).map (𝟙 (finiteIndex n))
  exact ((bare X).map_id (finiteIndex n)).symm

/-- The native prefix retains its original loop-count map and complete original degree cast. -/
theorem nativePrefix_hom (X : Carrier.{u, v}) (n m : ℕ) :
    (nativePrefix n m).hom.app X =
      (loopPrefix n).inv.app ((bare X).obj (finiteIndex (m + n + 1))) ≫
        (Functor.Iteration.iterate PointedCGWH.loop (n + 1)).map
          ((bare X).map (lowerCast n m).inv) := by
  have hc := levelCast_hom X (Nat.add_assoc m n 1)
  exact (evaluationTail_hom_app PointedCGWH.loop level n m X).trans
    (congrArg (fun f => (loopPrefix n).inv.app ((bare X).obj (finiteIndex (m + n + 1))) ≫
      (Functor.Iteration.iterate PointedCGWH.loop (n + 1)).map f) hc)

private theorem composeMapSquares {C : Type uC} [Category.{vC} C]
    {A B D E F G : C} (u : A ⟶ B) (a : A ⟶ D) (a' : B ⟶ E)
    (v : D ⟶ E) (b : D ⟶ F) (b' : E ⟶ G) (w : F ⟶ G)
    (h1 : u ≫ a' = a ≫ v) (h2 : v ≫ b' = b ≫ w) :
    u ≫ (a' ≫ b') = (a ≫ b) ≫ w :=
  (Category.assoc u a' b').symm.trans
    ((congrArg (fun h => h ≫ b') h1).trans
      ((Category.assoc a v b').trans
        ((congrArg (fun h => a ≫ h) h2).trans (Category.assoc a b w).symm)))

/-- The complete original sequential evaluation keeps the same loop-count functor after actual j. -/
def sequentialEvaluation (n m : ℕ) :
    j.{u, v} ⋙ (PointedCGWH.SequentialSpectrum.OrderedLoop.iterate n ⋙
      PointedCGWH.SequentialSpectrum.evaluation m) ≅
        level (m + n) ⋙ Functor.Iteration.iterate PointedCGWH.loop n :=
  NatIso.ofComponents
    (fun X =>
      (PointedCGWH.SequentialSpectrum.OrderedLoop.iterationEvaluationIso n m).app (j.obj X) ≪≫
      (loopComparison n).app ((bare X).obj (finiteIndex (m + n))))
    (fun {X Y} f => by
      let P := PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower.{u, v} n
      let Q := Functor.Iteration.iterate PointedCGWH.loop.{u, v} n
      let a :=
        (PointedCGWH.SequentialSpectrum.OrderedLoop.iterationEvaluationIso n m).hom.app (j.obj X)
      let a' :=
        (PointedCGWH.SequentialSpectrum.OrderedLoop.iterationEvaluationIso n m).hom.app (j.obj Y)
      let g := (level (m + n)).map f
      have hOld :=
        (PointedCGWH.SequentialSpectrum.OrderedLoop.iterationEvaluationIso n m).hom.naturality
        (j.map f)
      have hMap : PointedCGWH.SequentialSpectrum.levelMap (j.map f) (m + n) = g :=
        Actual.SymmetricIntegerHomotopy.underlying_map f (m + n)
      have h1 := hOld.trans (congrArg (fun g => a ≫ P.map g) hMap)
      have h2 := (loopComparison n).hom.naturality g
      exact composeMapSquares
        (PointedCGWH.SequentialSpectrum.levelMap
          ((PointedCGWH.SequentialSpectrum.OrderedLoop.iterate n).map (j.map f)) m)
        a a' (P.map g) ((loopComparison n).hom.app ((bare X).obj (finiteIndex (m + n))))
        ((loopComparison n).hom.app ((bare Y).obj (finiteIndex (m + n)))) (Q.map g) h1 h2)

/-- Every original forward sequential component retains both complete original maps. -/
theorem sequentialEvaluation_hom (X : Carrier.{u, v}) (n m : ℕ) :
    (sequentialEvaluation n m).hom.app X =
      (PointedCGWH.SequentialSpectrum.OrderedLoop.iterationEvaluationIso n m).hom.app (j.obj X) ≫
        (loopComparison n).hom.app ((bare X).obj (finiteIndex (m + n))) := rfl

/-- Both evaluated native maps retain the actual original finite permutation. -/
def correctedEvaluation (n m : ℕ) :
    Functor.Iteration.iterate R.{u, v} n ⋙ level m ≅
      level (m + n) ⋙ Functor.Iteration.iterate PointedCGWH.loop n :=
  nativeEvaluation n m ≪≫ Functor.isoWhiskerRight (indexValueNatIso n m)
    (Functor.Iteration.iterate PointedCGWH.loop n)

/-- Each actual forward native comparison retains its original map and permutation image. -/
theorem correctedEvaluation_hom (X : Carrier.{u, v}) (n m : ℕ) :
    (correctedEvaluation n m).hom.app X =
      (nativeEvaluation n m).hom.app X ≫
        (Functor.Iteration.iterate PointedCGWH.loop n).map ((bare X).map (ell n m).hom) := rfl

/-- Both complete evaluated stages keep the original R, sequential restriction and permutations. -/
def stagePointedNatIso (n m : ℕ) :
    Functor.Iteration.iterate R.{u, v} n ⋙ level m ≅
      j ⋙ (PointedCGWH.SequentialSpectrum.OrderedLoop.iterate n ⋙
        PointedCGWH.SequentialSpectrum.evaluation m) :=
  correctedEvaluation n m ≪≫ (sequentialEvaluation n m).symm

/-- Every full stage retains the original evaluated map and the original inverse sequential map. -/
theorem stagePointedNatIso_hom (X : Carrier.{u, v}) (n m : ℕ) :
    (stagePointedNatIso n m).hom.app X =
      ((correctedEvaluation n m).app X ≪≫ ((sequentialEvaluation n m).app X).symm).hom := rfl

/-- The original prefix has its whole original loop image of the native arithmetic map. -/
theorem nativePrefix_hom_alternate (X : Carrier.{u, v}) (n m : ℕ) :
    (nativePrefix n m).hom.app X =
      (Functor.Iteration.iterate PointedCGWH.loop n).map
          (PointedCGWH.loop.map ((bare X).map (lowerCast n m).inv)) ≫
        (loopPrefix n).inv.app ((bare X).obj (finiteIndex (m + (n + 1)))) :=
  (nativePrefix_hom X n m).trans
    ((loopPrefix n).inv.naturality ((bare X).map (lowerCast n m).inv)).symm

private theorem equalityWord2 {C : Type uC} [Category.{vC} C] {A B D E : C}
    (p : A = B) (q : B = E) (r : A = D) (s : D = E) :
    eqToHom p ≫ eqToHom q = eqToHom r ≫ eqToHom s := by
  simp only [eqToHom_trans]

/-- Both original prefix directions keep the same original loop-count and degree transports. -/
theorem prefixLoopComparison_hom (X : Carrier.{u, v}) (n m : ℕ) :
    (loopComparison n).hom.app
        (PointedCGWH.loop.obj ((bare X).obj (finiteIndex (m + n + 1)))) ≫
      (nativePrefix n m).hom.app X =
    (evaluationPrefixTargetNatIso n m).hom.app
        (j.obj X) ≫
      (loopComparison (n + 1)).hom.app ((bare X).obj (finiteIndex (m + (n + 1)))) := by
  let Q := Functor.Iteration.iterate PointedCGWH.loop.{u, v} (n + 1)
  let Z := (bare X).obj (finiteIndex (m + n + 1))
  let T := (bare X).obj (finiteIndex (m + (n + 1)))
  let hLevel := congrArg (bare X).obj (congrArg finiteIndex (Nat.add_assoc m n 1))
  let pCount := Functor.congr_obj (Functor.Iteration.iterate_succ_prefix PointedCGWH.loop n).symm Z
  let pIndex := congrArg Q.obj hLevel
  let p0 := Functor.congr_obj (loopPower_same n) (PointedCGWH.loop.obj Z)
  let ps := Functor.congr_obj
    (evaluationPrefixTargetFunctorEq n m)
      (j.obj X)
  let p1 := Functor.congr_obj (loopPower_same (n + 1)) T
  have hCount : (loopPrefix n).inv.app Z = eqToHom pCount :=
    eqToHom_app (Functor.Iteration.iterate_succ_prefix PointedCGWH.loop n).symm Z
  have hIndex : Q.map ((bare X).map (lowerCast n m).inv) = eqToHom pIndex :=
    (congrArg Q.map (lowerCast_value X n m)).trans (eqToHom_map Q hLevel)
  have hNative : (nativePrefix n m).hom.app X = eqToHom (pCount.trans pIndex) :=
    (nativePrefix_hom X n m).trans
      ((congrArg₂ (fun f g => f ≫ g) hCount hIndex).trans (eqToHom_trans pCount pIndex))
  have hSource : (loopComparison n).hom.app (PointedCGWH.loop.obj Z) = eqToHom p0 :=
    eqToHom_app (loopPower_same n) (PointedCGWH.loop.obj Z)
  have hSeq :
      (evaluationPrefixTargetNatIso n m).hom.app
        (j.obj X) = eqToHom ps :=
    eqToHom_app
      (evaluationPrefixTargetFunctorEq n m)
        (j.obj X)
  have hTarget : (loopComparison (n + 1)).hom.app T = eqToHom p1 :=
    eqToHom_app (loopPower_same (n + 1)) T
  exact (congrArg₂ (fun f g => f ≫ g) hSource hNative).trans
    ((equalityWord2 p0 (pCount.trans pIndex) ps p1).trans
      (congrArg₂ (fun f g => f ≫ g) hSeq hTarget).symm)

private theorem transportEvaluationSquare {C : Type uC} [Category.{vC} C]
    {A B D E F G H K : C} (u : A ⟶ B) (a : A ⟶ D) (a' : B ⟶ E)
    (b : D ⟶ F) (t : F ⟶ E) (i : D ⟶ G) (i' : F ⟶ H) (j' : E ⟶ K)
    (b' : G ⟶ H) (t' : H ⟶ K)
    (h0 : u ≫ a' = (a ≫ b) ≫ t) (h1 : b ≫ i' = i ≫ b') (h2 : t ≫ j' = i' ≫ t') :
    u ≫ (a' ≫ j') = (a ≫ i) ≫ b' ≫ t' := by
  calc
    _ = (u ≫ a') ≫ j' := (Category.assoc _ _ _).symm
    _ = ((a ≫ b) ≫ t) ≫ j' := congrArg (fun h => h ≫ j') h0
    _ = a ≫ b ≫ (t ≫ j') := by simp only [Category.assoc]
    _ = a ≫ b ≫ (i' ≫ t') := congrArg (fun h => a ≫ b ≫ h) h2
    _ = (a ≫ (b ≫ i')) ≫ t' := by simp only [Category.assoc]
    _ = (a ≫ (i ≫ b')) ≫ t' := congrArg (fun h => (a ≫ h) ≫ t') h1
    _ = _ := by simp only [Category.assoc]

/-- The actual sequential input transition retains the original full evaluated prefix word. -/
theorem sequentialInput_evaluation (X : Carrier.{u, v}) (n m : ℕ) :
    PointedCGWH.SequentialSpectrum.levelMap
        ((PointedCGWH.SequentialSpectrum.OrderedLoop.iterateUnit n).app (j.obj X)) m ≫
      (sequentialEvaluation (n + 1) m).hom.app X =
    (sequentialEvaluation n m).hom.app X ≫
      (Functor.Iteration.iterate PointedCGWH.loop n).map ((j.obj X).adjointStructureMap (m + n)) ≫
        (nativePrefix n m).hom.app X := by
  let u := PointedCGWH.SequentialSpectrum.levelMap
    ((PointedCGWH.SequentialSpectrum.OrderedLoop.iterateUnit n).app (j.obj X)) m
  let b := (j.obj X).adjointStructureMap (m + n)
  let Z := (bare X).obj (finiteIndex (m + n))
  let L := PointedCGWH.loop.obj ((bare X).obj (finiteIndex (m + n + 1)))
  let T := (bare X).obj (finiteIndex (m + (n + 1)))
  let a :=
        (PointedCGWH.SequentialSpectrum.OrderedLoop.iterationEvaluationIso n m).hom.app (j.obj X)
  let a' :=
    (PointedCGWH.SequentialSpectrum.OrderedLoop.iterationEvaluationIso (n + 1) m).hom.app (j.obj X)
  let t :=
    (evaluationPrefixTargetNatIso n m).hom.app
      (j.obj X)
  have h0 :=
    iterateUnit_evaluation_prefix_square
      n m (j.obj X)
  have h1 := (loopComparison n).hom.naturality b
  have h2 := (prefixLoopComparison_hom X n m).symm
  have h := transportEvaluationSquare u a a'
    ((PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower n).map b) t
    ((loopComparison n).hom.app Z) ((loopComparison n).hom.app L)
    ((loopComparison (n + 1)).hom.app T)
    ((Functor.Iteration.iterate PointedCGWH.loop n).map b) ((nativePrefix n m).hom.app X) h0 h1 h2
  exact (congrArg (fun a' => u ≫ a') (sequentialEvaluation_hom X (n + 1) m)).trans
    (h.trans (congrArg (fun a => a ≫ (Functor.Iteration.iterate PointedCGWH.loop n).map b ≫
      (nativePrefix n m).hom.app X) (sequentialEvaluation_hom X n m).symm))

section OriginalSourceEquation

variable (hSource : ∀ (X : Carrier.{u, v}) (m : ℕ),
  (originalCoordinate m).app X =
    NativeSymmetricDelooping.omegaMap X (finiteIndex m) (finiteIndex 1) ≫
      (firstScalarIso ((bare X).obj (finiteIndex (m + 1)))).hom)

include hSource in
/-- The precise original source equality gives the complete actual sequential successor square. -/
theorem originalCoordinate_ell_successor (X : Carrier.{u, v}) (n m : ℕ) :
    (originalCoordinate (m + n)).app X ≫
        PointedCGWH.loop.map ((bare X).map
          ((lowerCast n m).inv ≫ (ell (n + 1) m).hom)) =
      (bare X).map (ell n m).hom ≫ sequentialAdjoint (j.obj X) (m + n) ≫
        PointedCGWH.loop.map ((bare X).map (lowerCast n m).inv) := by
  let S : PointedCGWH.{u, v} := coefficient.{u, v}.functor.obj (finiteIndex 1)
  let Z := (bare X).obj (finiteIndex (m + n + 1))
  let T := (bare X).obj (finiteIndex (m + (n + 1)))
  let g := (bare X).map ((lowerCast n m).inv ≫ (ell (n + 1) m).hom)
  let cZ := (firstScalarIso Z).hom
  let cT := (firstScalarIso T).hom
  let w := NativeSymmetricDelooping.omegaMap X (finiteIndex (m + n)) (finiteIndex 1)
  let e := (bare X).map (ell n m).hom
  let a := labelledAdjoint X (finiteIndex 1) (finiteIndex (m + n))
    (finiteIndex (m + (n + 1))) (upperCast n m).hom
  have hInput := congrArg (fun h => h ≫ PointedCGWH.loop.map g) (hSource X (m + n))
  have hPre := (MonoidalClosed.pre NativeSymmetricDelooping.firstCoefficientIso.inv).naturality g
  have hEll := ell_step_adjoint X n m
  have hSeq := sequentialAdjoint_sourceCast X n m
  exact hInput.trans ((Category.assoc w cZ (PointedCGWH.loop.map g)).trans
    ((congrArg (fun h => w ≫ h) hPre.symm).trans
      ((Category.assoc w ((ihom S).map g) cT).symm.trans
        ((congrArg (fun h => h ≫ cT) hEll).trans
          ((Category.assoc e a cT).trans (congrArg (fun h => e ≫ h) hSeq.symm))))))

private theorem mapPrefixSquare {C : Type uC} [Category.{vC} C]
    (L P Q : C ⥤ C) (i : L ⋙ P ≅ Q) {A D T : C}
    (η b : A ⟶ L.obj D) (e : A ⟶ A) (c : D ⟶ T) (d : T ⟶ T)
    (h : η ≫ L.map (c ≫ d) = e ≫ b ≫ L.map c) :
    P.map η ≫ P.map (L.map c) ≫ i.hom.app T ≫ Q.map d =
      P.map e ≫ P.map b ≫ P.map (L.map c) ≫ i.hom.app T := by
  have hi := i.hom.naturality d
  change P.map (L.map d) ≫ i.hom.app T = i.hom.app T ≫ Q.map d at hi
  calc
    _ = P.map η ≫ P.map (L.map c) ≫ P.map (L.map d) ≫ i.hom.app T := by
      rw [hi]
    _ = P.map (η ≫ L.map (c ≫ d)) ≫ i.hom.app T := by
      rw [L.map_comp, P.map_comp, P.map_comp]
      simp only [Category.assoc]
    _ = P.map (e ≫ b ≫ L.map c) ≫ i.hom.app T := congrArg (fun f => P.map f ≫ i.hom.app T) h
    _ = _ := by rw [P.map_comp, P.map_comp]; simp only [Category.assoc]

include hSource in
/-- The actual source equality carries each original prefix through its finite permutation. -/
theorem correctedPrefix_evaluation (X : Carrier.{u, v}) (n m : ℕ) :
    (Functor.Iteration.iterate PointedCGWH.loop n).map ((originalCoordinate (m + n)).app X) ≫
      (nativePrefix n m).hom.app X ≫
        (Functor.Iteration.iterate PointedCGWH.loop (n + 1)).map
          ((bare X).map (ell (n + 1) m).hom) =
    (Functor.Iteration.iterate PointedCGWH.loop n).map ((bare X).map (ell n m).hom) ≫
      (Functor.Iteration.iterate PointedCGWH.loop n).map ((j.obj X).adjointStructureMap (m + n)) ≫
        (nativePrefix n m).hom.app X := by
  let P := Functor.Iteration.iterate PointedCGWH.loop.{u, v} n
  let Q := Functor.Iteration.iterate PointedCGWH.loop.{u, v} (n + 1)
  let η := (originalCoordinate (m + n)).app X
  let b := (j.obj X).adjointStructureMap (m + n)
  let e := (bare X).map (ell n m).hom
  let c := (bare X).map (lowerCast n m).inv
  let d := (bare X).map (ell (n + 1) m).hom
  have hBare : (bare X).map ((lowerCast n m).inv ≫ (ell (n + 1) m).hom) = c ≫ d :=
    (bare X).map_comp _ _
  have hOriginal := originalCoordinate_ell_successor hSource X n m
  have hSeq := sequential_adjoint_eq (m + n) (j.obj X)
  have hPoint : η ≫ PointedCGWH.loop.map (c ≫ d) = e ≫ b ≫ PointedCGWH.loop.map c :=
    (congrArg (fun g => η ≫ PointedCGWH.loop.map g) hBare).symm.trans
      (hOriginal.trans (congrArg (fun b => e ≫ b ≫ PointedCGWH.loop.map c) hSeq))
  have h := mapPrefixSquare PointedCGWH.loop P Q (loopPrefix n).symm η b e c d hPoint
  have hPrefix := nativePrefix_hom_alternate X n m
  have hLeft := congrArg (fun p => P.map η ≫ p ≫ Q.map d) hPrefix
  have hRight := congrArg (fun p => P.map e ≫ P.map b ≫ p) hPrefix
  exact hLeft.trans (h.trans hRight.symm)

private theorem correctEvaluationSquare {C : Type uC} [Category.{vC} C]
    {A B D E F : C} (u : A ⟶ B) (a : A ⟶ D) (a' : B ⟶ E)
    (η : D ⟶ F) (p : F ⟶ E) (e : D ⟶ D) (e' : E ⟶ E) (b : D ⟶ F)
    (h0 : u ≫ a' = a ≫ η ≫ p) (h1 : η ≫ p ≫ e' = e ≫ b ≫ p) :
    u ≫ (a' ≫ e') = (a ≫ e) ≫ b ≫ p := by
  calc
    _ = (u ≫ a') ≫ e' := (Category.assoc _ _ _).symm
    _ = (a ≫ η ≫ p) ≫ e' := congrArg (fun h => h ≫ e') h0
    _ = a ≫ (η ≫ p ≫ e') := by simp only [Category.assoc]
    _ = a ≫ (e ≫ b ≫ p) := congrArg (fun h => a ≫ h) h1
    _ = _ := by simp only [Category.assoc]

private theorem stageComparisonSquare {C : Type uC} [Category.{vC} C]
    {A B D E F G : C} (a : A ≅ D) (a' : B ≅ E) (b : F ≅ D) (b' : G ≅ E)
    (u : A ⟶ B) (v : F ⟶ G) (w : D ⟶ E)
    (hA : u ≫ a'.hom = a.hom ≫ w) (hB : v ≫ b'.hom = b.hom ≫ w) :
    u ≫ (a' ≪≫ b'.symm).hom = (a ≪≫ b.symm).hom ≫ v := by
  have hInv : w ≫ b'.inv = b.inv ≫ v := (CommSq.vert_inv (g := b) (h := b') ⟨hB⟩).w
  exact (Category.assoc u a'.hom b'.inv).symm.trans
    ((congrArg (fun h => h ≫ b'.inv) hA).trans
      ((Category.assoc a.hom w b'.inv).trans
        ((congrArg (fun h => a.hom ≫ h) hInv).trans (Category.assoc a.hom b.inv v).symm)))

include hSource in
/-- Every corrected native evaluation retains the original input coaugmentation and j transition. -/
theorem correctedEvaluation_input (X : Carrier.{u, v}) (n m : ℕ) :
    (level m).map ((Functor.Iteration.inputTransition eta n).app X) ≫
        (correctedEvaluation (n + 1) m).hom.app X =
      (correctedEvaluation n m).hom.app X ≫
        (Functor.Iteration.iterate PointedCGWH.loop n).map ((j.obj X).adjointStructureMap (m + n)) ≫
          (nativePrefix n m).hom.app X := by
  let u := (level m).map ((Functor.Iteration.inputTransition eta n).app X)
  let a := (nativeEvaluation n m).hom.app X
  let a' := (nativeEvaluation (n + 1) m).hom.app X
  let e := (Functor.Iteration.iterate PointedCGWH.loop n).map ((bare X).map (ell n m).hom)
  let e' := (Functor.Iteration.iterate PointedCGWH.loop (n + 1)).map
          ((bare X).map (ell (n + 1) m).hom)
  let b := (Functor.Iteration.iterate PointedCGWH.loop n).map
    ((j.obj X).adjointStructureMap (m + n))
  let p := (nativePrefix n m).hom.app X
  let η := (Functor.Iteration.iterate PointedCGWH.loop n).map ((originalCoordinate (m + n)).app X)
  have h0 := nativeEvaluation_input X n m
  have h1 := correctedPrefix_evaluation hSource X n m
  have h := correctEvaluationSquare u a a' η p e e' b h0 h1
  exact (congrArg (fun a' => u ≫ a') (correctedEvaluation_hom X (n + 1) m)).trans
    (h.trans (congrArg (fun a => a ≫ b ≫ p) (correctedEvaluation_hom X n m).symm))

include hSource in
/-- The full actual R input stage compares with the same original sequential stage. -/
theorem stagePointedNatIso_transition (X : Carrier.{u, v}) (n m : ℕ) :
    (level m).map ((Functor.Iteration.inputTransition eta n).app X) ≫
        (stagePointedNatIso (n + 1) m).hom.app X =
      (stagePointedNatIso n m).hom.app X ≫ PointedCGWH.SequentialSpectrum.levelMap
        ((PointedCGWH.SequentialSpectrum.OrderedLoop.iterateUnit n).app (j.obj X)) m := by
  let A := (correctedEvaluation n m).app X
  let A' := (correctedEvaluation (n + 1) m).app X
  let B := (sequentialEvaluation n m).app X
  let B' := (sequentialEvaluation (n + 1) m).app X
  let u := (level m).map ((Functor.Iteration.inputTransition eta n).app X)
  let v := PointedCGWH.SequentialSpectrum.levelMap
    ((PointedCGWH.SequentialSpectrum.OrderedLoop.iterateUnit n).app (j.obj X)) m
  let w := (Functor.Iteration.iterate PointedCGWH.loop n).map
    ((j.obj X).adjointStructureMap (m + n)) ≫
    (nativePrefix n m).hom.app X
  have hA : u ≫ A'.hom = A.hom ≫ w := correctedEvaluation_input hSource X n m
  have hB : v ≫ B'.hom = B.hom ≫ w := sequentialInput_evaluation X n m
  have h := stageComparisonSquare A A' B B' u v w hA hB
  exact (congrArg (fun a' => u ≫ a') (stagePointedNatIso_hom X (n + 1) m)).trans
    (h.trans (congrArg (fun a => a ≫ v) (stagePointedNatIso_hom X n m).symm))

open PointedCGWH.SequentialSpectrum.MappingTelescope.StageIterationHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.IntegerColimitNormalization

private theorem postInputDiagram_succ
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {F : C ⥤ C} (η : 𝟭 C ⟶ F) (L : C ⥤ D) (X : C) (n : ℕ) :
    ((Functor.Iteration.inputDiagramFunctor η ⋙
      (Functor.whiskeringRight ℕ C D).obj L).obj X).map (homOfLE (Nat.le_add_right n 1)) =
        L.map ((Functor.Iteration.inputTransition η n).app X) :=
  congrArg L.map (Functor.Iteration.inputDiagram_map_succ η X n)

private theorem postInputDiagram_map_app
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {F : C ⥤ C} (η : 𝟭 C ⟶ F) (L : C ⥤ D) {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    ((Functor.Iteration.inputDiagramFunctor η ⋙
      (Functor.whiskeringRight ℕ C D).obj L).map f).app n =
        L.map ((Functor.Iteration.iterate F n).map f) := rfl

/-- The complete original native input diagram uses the actual R and original lambda. -/
def nativePointedDiagramFunctor (m : ℕ) : Carrier.{u, v} ⥤ (ℕ ⥤ PointedCGWH.{u, v}) :=
  Functor.Iteration.inputDiagramFunctor (C := Carrier.{u, v}) (F := R.{u, v}) eta ⋙
    (Functor.whiskeringRight ℕ Carrier.{u, v} PointedCGWH.{u, v}).obj (level m)

/-- The actual j restriction is followed by its same original sequential input diagram. -/
def sequentialPointedDiagramFunctor (m : ℕ) : Carrier.{u, v} ⥤ (ℕ ⥤ PointedCGWH.{u, v}) :=
  j ⋙ levelIterationDiagramFunctor m

/-- Every actual native successor is the original R^n(lambda_X) with its canonical association. -/
theorem nativePointedDiagramFunctor_succ (X : Carrier.{u, v}) (m n : ℕ) :
    ((nativePointedDiagramFunctor m).obj X).map (homOfLE (Nat.le_add_right n 1)) =
      (level m).map ((Functor.Iteration.inputTransition eta n).app X) :=
  postInputDiagram_succ eta (level m) X n

/-- Every actual native diagram component is the original complete iterated input map. -/
theorem nativePointedDiagramFunctor_map_app {X Y : Carrier.{u, v}} (f : X ⟶ Y) (m n : ℕ) :
    ((nativePointedDiagramFunctor m).map f).app n =
      (level m).map ((Functor.Iteration.iterate R n).map f) :=
  postInputDiagram_map_app eta (level m) f n

/-- The original sequential successor retains the same original complete iterate-unit arrow. -/
theorem sequentialPointedDiagramFunctor_succ (X : Carrier.{u, v}) (m n : ℕ) :
    ((sequentialPointedDiagramFunctor m).obj X).map (homOfLE (Nat.le_add_right n 1)) =
      PointedCGWH.SequentialSpectrum.levelMap
        ((PointedCGWH.SequentialSpectrum.OrderedLoop.iterateUnit n).app (j.obj X)) m :=
  congrArg (PointedCGWH.SequentialSpectrum.evaluation m).map
    (PointedCGWH.SequentialSpectrum.OrderedLoop.iterationDiagram_map_succ (j.obj X) n)

/-- Every original sequential input-map component is the original actual j iterate. -/
theorem sequentialPointedDiagramFunctor_map_app {X Y : Carrier.{u, v}}
    (f : X ⟶ Y) (m n : ℕ) :
    ((sequentialPointedDiagramFunctor m).map f).app n =
      PointedCGWH.SequentialSpectrum.levelMap
        ((PointedCGWH.SequentialSpectrum.OrderedLoop.iterate n).map (j.map f)) m := rfl

include hSource in
/-- Every finite-index map uses the original full stage comparison and actual source square. -/
def pointedDiagramHom (X : Carrier.{u, v}) (m : ℕ) :
    (nativePointedDiagramFunctor m).obj X ⟶ (sequentialPointedDiagramFunctor m).obj X :=
  NatTrans.ofSequence (fun n => (stagePointedNatIso n m).hom.app X) (fun n => by
    have hNative := congrArg (fun f => f ≫ (stagePointedNatIso (n + 1) m).hom.app X)
      (nativePointedDiagramFunctor_succ X m n)
    have hSeq := congrArg (fun f => (stagePointedNatIso n m).hom.app X ≫ f)
      (sequentialPointedDiagramFunctor_succ X m n).symm
    exact hNative.trans ((stagePointedNatIso_transition hSource X n m).trans hSeq))

include hSource in
/-- Every full diagram component retains the same original stage map. -/
theorem pointedDiagramHom_app (X : Carrier.{u, v}) (m n : ℕ) :
    (pointedDiagramHom hSource X m).app n = (stagePointedNatIso n m).hom.app X := rfl

include hSource in
/-- The original diagram comparison is natural for every whole native input arrow. -/
def pointedDiagramNatTrans (m : ℕ) : nativePointedDiagramFunctor.{u, v} m ⟶
    sequentialPointedDiagramFunctor m where
  app X := pointedDiagramHom hSource X m
  naturality _ _ f := by
    apply NatTrans.ext
    funext n
    simp only [NatTrans.comp_app, pointedDiagramHom_app,
      nativePointedDiagramFunctor_map_app, sequentialPointedDiagramFunctor_map_app]
    exact (stagePointedNatIso n m).hom.naturality f

universe uJ vJ

private def natIsoWithGivenHom {J : Type uJ} [Category.{vJ} J]
    {C : Type uC} [Category.{vC} C] {F G : J ⥤ C}
    (e : ∀ X, F.obj X ≅ G.obj X) (t : F ⟶ G) (ht : ∀ X, t.app X = (e X).hom) : F ≅ G :=
  NatIso.ofComponents e (fun {X Y} f =>
    (congrArg (fun a => F.map f ≫ a) (ht Y).symm).trans
      ((t.naturality f).trans (congrArg (fun a => a ≫ G.map f) (ht X))))

private theorem natIsoWithGivenHom_hom {J : Type uJ} [Category.{vJ} J]
    {C : Type uC} [Category.{vC} C] {F G : J ⥤ C}
    (e : ∀ X, F.obj X ≅ G.obj X) (t : F ⟶ G) (ht : ∀ X, t.app X = (e X).hom) :
    (natIsoWithGivenHom e t ht).hom = t := by
  apply NatTrans.ext
  funext X
  exact (ht X).symm

include hSource in
/-- Both actual diagram maps retain the original stage maps at this complete native input. -/
def pointedDiagramIso (X : Carrier.{u, v}) (m : ℕ) :
    (nativePointedDiagramFunctor m).obj X ≅ (sequentialPointedDiagramFunctor m).obj X :=
  natIsoWithGivenHom
    (F := (nativePointedDiagramFunctor m).obj X)
    (G := (sequentialPointedDiagramFunctor m).obj X)
    (fun n => (stagePointedNatIso n m).app X)
    (pointedDiagramHom hSource X m) (fun n => pointedDiagramHom_app hSource X m n)

include hSource in
/-- The whole original forward diagram map is the same actual native source transformation. -/
theorem pointedDiagramIso_hom (X : Carrier.{u, v}) (m : ℕ) :
    (pointedDiagramIso hSource X m).hom = pointedDiagramHom hSource X m :=
  natIsoWithGivenHom_hom
    (F := (nativePointedDiagramFunctor m).obj X)
    (G := (sequentialPointedDiagramFunctor m).obj X)
    (fun n => (stagePointedNatIso n m).app X)
    (pointedDiagramHom hSource X m) (fun n => pointedDiagramHom_app hSource X m n)

include hSource in
/-- Both actual maps compare the complete original native and sequential input diagrams. -/
def pointedDiagramNatIso (m : ℕ) : nativePointedDiagramFunctor.{u, v} m ≅
    sequentialPointedDiagramFunctor m :=
  natIsoWithGivenHom (fun X => pointedDiagramIso hSource X m)
    (pointedDiagramNatTrans hSource m) (fun X => (pointedDiagramIso_hom hSource X m).symm)

/-- Every raw group uses the positive group functor on the same actual original lambda diagram. -/
def nativeGroupDiagramFunctor (m k : ℕ) : Carrier.{u, v} ⥤ (ℕ ⥤ GrpCat.{v}) :=
  nativePointedDiagramFunctor m ⋙
    (Functor.whiskeringRight ℕ PointedCGWH.{u, v} GrpCat.{v}).obj (PointedCGWH.piNPositiveFunctor k)

include hSource in
/-- Both original positive-group diagram maps retain the same entire input j restriction. -/
def nativeGroupDiagramNatIso (m k : ℕ) : nativeGroupDiagramFunctor.{u, v} m k ≅
    j ⋙ groupIterationDiagramFunctor m k :=
  Functor.isoWhiskerRight (pointedDiagramNatIso hSource m)
    ((Functor.whiskeringRight ℕ PointedCGWH.{u, v} GrpCat.{v}).obj
      (PointedCGWH.piNPositiveFunctor k)) ≪≫
      Functor.associator j (levelIterationDiagramFunctor m)
        ((Functor.whiskeringRight ℕ PointedCGWH.{u, v} GrpCat.{v}).obj
      (PointedCGWH.piNPositiveFunctor k))

include hSource in
/-- Every complete original lambda stage keeps the original changing-degree group diagram. -/
def nativeGroupDiagonalNatIso (m k : ℕ) : nativeGroupDiagramFunctor.{u, v} m k ≅
    j ⋙ diagonalDiagramFunctor m k :=
  nativeGroupDiagramNatIso hSource m k ≪≫ Functor.isoWhiskerLeft j (iterationDiagonalNatIso m k)

/-- The actual raw Type colimit retains every original input map and every positive degree. -/
def rawTypeColimitFunctor (m k : ℕ) : Carrier.{u, v} ⥤ Type v :=
  nativePointedDiagramFunctor m ⋙
    (Functor.whiskeringRight ℕ PointedCGWH.{u, v} (Type v)).obj
      (PointedCGWH.piNFunctor (k + 1)) ⋙ colim

/-- The same actual lambda group diagram has its original chosen filtered group quotient. -/
def rawGroupColimitFunctor (m k : ℕ) : Carrier.{u, v} ⥤ GrpCat.{v} :=
  nativeGroupDiagramFunctor m k ⋙ GrpCat.FilteredColimits.colimitFunctor

include hSource in
/-- Both genuine group quotient maps reach the actual original signed integer functor. -/
def rawIntegerGroupNatIso (m k : ℕ) : rawGroupColimitFunctor.{u, v} m k ≅
    j ⋙ integerStablePiFunctor (integerDegree m k) :=
  Functor.isoWhiskerRight (nativeGroupDiagonalNatIso hSource m k)
      GrpCat.FilteredColimits.colimitFunctor ≪≫
    Functor.associator j (diagonalDiagramFunctor m k) GrpCat.FilteredColimits.colimitFunctor ≪≫
      Functor.isoWhiskerLeft j (integerColimitNatIso m k)

/-- The genuine original group/Type comparison gives both same chosen quotient maps. -/
def rawTypeGroupColimitNatIso (m k : ℕ) : rawTypeColimitFunctor.{u, v} m k ≅
    rawGroupColimitFunctor m k ⋙ forget GrpCat.{v} :=
  NatIso.ofComponents
    (fun X => GrpCat.FilteredColimits.sourceTypeColimitIso
      (PointedCGWH.piNPositiveFunctor k) (PointedCGWH.piNFunctor (k + 1))
      (PointedCGWH.LoopPowerAtPoints.positiveForgetComparison k)
        ((nativePointedDiagramFunctor m).obj X))
    (fun f => GrpCat.FilteredColimits.sourceTypeColimitIso_hom_naturality
      (PointedCGWH.piNPositiveFunctor k) (PointedCGWH.piNFunctor (k + 1))
      (PointedCGWH.LoopPowerAtPoints.positiveForgetComparison k)
        ((nativePointedDiagramFunctor m).map f))

/-- Every original raw Type leg reaches its same actual original positive-group quotient leg. -/
theorem rawTypeGroupColimitNatIso_hom_leg (X : Carrier.{u, v}) (m k n : ℕ) :
    colimit.ι (((nativePointedDiagramFunctor m).obj X) ⋙ PointedCGWH.piNFunctor (k + 1)) n ≫
        (rawTypeGroupColimitNatIso m k).hom.app X =
      (PointedCGWH.LoopPowerAtPoints.positiveForgetComparison k).inv.app
          (((nativePointedDiagramFunctor m).obj X).obj n) ≫
        (forget GrpCat.{v}).map
          ((GrpCat.FilteredColimits.colimitCocone
            (((nativePointedDiagramFunctor m).obj X) ⋙
              PointedCGWH.piNPositiveFunctor k)).ι.app n) :=
  GrpCat.FilteredColimits.sourceTypeColimitIso_ι_hom
    (PointedCGWH.piNPositiveFunctor k) (PointedCGWH.piNFunctor (k + 1))
    (PointedCGWH.LoopPowerAtPoints.positiveForgetComparison k)
    ((nativePointedDiagramFunctor m).obj X) n

/-- Every inverse original group leg returns through the same actual original source comparison. -/
theorem rawTypeGroupColimitNatIso_inv_leg (X : Carrier.{u, v}) (m k n : ℕ) :
    (forget GrpCat.{v}).map
        ((GrpCat.FilteredColimits.colimitCocone
          (((nativePointedDiagramFunctor m).obj X) ⋙ PointedCGWH.piNPositiveFunctor k)).ι.app n) ≫
      (rawTypeGroupColimitNatIso m k).inv.app X =
    (PointedCGWH.LoopPowerAtPoints.positiveForgetComparison k).hom.app
        (((nativePointedDiagramFunctor m).obj X).obj n) ≫
      colimit.ι (((nativePointedDiagramFunctor m).obj X) ⋙ PointedCGWH.piNFunctor (k + 1)) n :=
  GrpCat.FilteredColimits.sourceTypeColimitIso_ι_inv
    (PointedCGWH.piNPositiveFunctor k) (PointedCGWH.piNFunctor (k + 1))
    (PointedCGWH.LoopPowerAtPoints.positiveForgetComparison k)
    ((nativePointedDiagramFunctor m).obj X) n

include hSource in
/-- Both actual raw Type quotient maps retain the original signed integer group comparison. -/
def rawIntegerTypeNatIso (m k : ℕ) : rawTypeColimitFunctor.{u, v} m k ≅
    (j ⋙ integerStablePiFunctor (integerDegree m k)) ⋙ forget GrpCat.{v} :=
  rawTypeGroupColimitNatIso m k ≪≫
    Functor.isoWhiskerRight (rawIntegerGroupNatIso hSource m k) (forget GrpCat.{v})

include hSource in
/-- Every signed raw comparison retains its original leg and actual integer quotient map. -/
theorem rawIntegerTypeNatIso_hom_leg (X : Carrier.{u, v}) (m k n : ℕ) :
    colimit.ι (((nativePointedDiagramFunctor m).obj X) ⋙ PointedCGWH.piNFunctor (k + 1)) n ≫
        (rawIntegerTypeNatIso hSource m k).hom.app X =
      (PointedCGWH.LoopPowerAtPoints.positiveForgetComparison k).inv.app
          (((nativePointedDiagramFunctor m).obj X).obj n) ≫
        (forget GrpCat.{v}).map
          (((GrpCat.FilteredColimits.colimitCocone
            (((nativePointedDiagramFunctor m).obj X) ⋙ PointedCGWH.piNPositiveFunctor k)).ι.app n) ≫
              (rawIntegerGroupNatIso hSource m k).hom.app X) := by
  let a := colimit.ι (((nativePointedDiagramFunctor m).obj X) ⋙ PointedCGWH.piNFunctor (k + 1)) n
  let b := (rawTypeGroupColimitNatIso m k).hom.app X
  let c := (rawIntegerGroupNatIso hSource m k).hom.app X
  let e := (PointedCGWH.LoopPowerAtPoints.positiveForgetComparison k).inv.app
    (((nativePointedDiagramFunctor m).obj X).obj n)
  let l := (GrpCat.FilteredColimits.colimitCocone
    (((nativePointedDiagramFunctor m).obj X) ⋙ PointedCGWH.piNPositiveFunctor k)).ι.app n
  change a ≫ (b ≫ (forget GrpCat.{v}).map c) = e ≫ (forget GrpCat.{v}).map (l ≫ c)
  exact (Category.assoc a b ((forget GrpCat.{v}).map c)).symm.trans
    ((congrArg (fun f => f ≫ (forget GrpCat.{v}).map c)
      (rawTypeGroupColimitNatIso_hom_leg X m k n)).trans
      ((Category.assoc e ((forget GrpCat.{v}).map l) ((forget GrpCat.{v}).map c)).trans
        (congrArg (fun f => e ≫ f) ((forget GrpCat.{v}).map_comp l c).symm)))

/-- The original next-level predecessor has the literal signed integer degree k-m. -/
theorem predecessorIntegerDegree (m k : ℕ) : integerDegree (m + 1) k = (k : ℤ) - (m : ℤ) := by
  simp only [integerDegree, Nat.cast_add, Nat.cast_one]
  omega

include hSource in
/-- Both complete original predecessor quotient maps reach the same actual signed native functor. -/
def rawPredecessorTypeColimitNatIso (m k : ℕ) : rawTypeColimitFunctor.{u, v} (m + 1) k ≅
    Actual.SymmetricIntegerHomotopy.integerPiFunctor ((k : ℤ) - (m : ℤ)) ⋙ forget GrpCat.{v} :=
  rawIntegerTypeNatIso hSource (m + 1) k ≪≫
    eqToIso (congrArg (fun q =>
      Actual.SymmetricIntegerHomotopy.integerPiFunctor.{u, v} q ⋙ forget GrpCat.{v})
      (predecessorIntegerDegree m k))

/-- The full original raw predecessor map is the same actual Type-colimit input map. -/
def rawPiColimitMap {X Y : Carrier.{u, v}} (f : X ⟶ Y) (m k : ℕ) :
    (rawTypeColimitFunctor (m + 1) k).obj X ⟶ (rawTypeColimitFunctor (m + 1) k).obj Y :=
  colim.map (Functor.whiskerRight
    (Functor.whiskerRight (Functor.Iteration.inputDiagramMap eta f) (level (m + 1)))
    (PointedCGWH.piNFunctor (k + 1)))

/-- Every complete raw functor map retains the original actual input coaugmentation diagram. -/
theorem rawTypeColimitFunctor_map {X Y : Carrier.{u, v}} (f : X ⟶ Y) (m k : ℕ) :
    (rawTypeColimitFunctor (m + 1) k).map f = rawPiColimitMap f m k := rfl

include hSource in
/-- All original input arrows commute with the complete signed predecessor comparison. -/
theorem rawPredecessorTypeColimitNatIso_hom_naturality {X Y : Carrier.{u, v}}
    (f : X ⟶ Y) (m k : ℕ) :
    rawPiColimitMap f m k ≫ (rawPredecessorTypeColimitNatIso hSource m k).hom.app Y =
      (rawPredecessorTypeColimitNatIso hSource m k).hom.app X ≫
        (forget GrpCat.{v}).map
          ((Actual.SymmetricIntegerHomotopy.integerPiFunctor ((k : ℤ) - (m : ℤ))).map f) :=
  (rawPredecessorTypeColimitNatIso hSource m k).hom.naturality f

include hSource in
/-- The complete original inverse comparison retains the same actual input arrow. -/
theorem rawPredecessorTypeColimitNatIso_inv_naturality {X Y : Carrier.{u, v}}
    (f : X ⟶ Y) (m k : ℕ) :
    (forget GrpCat.{v}).map
        ((Actual.SymmetricIntegerHomotopy.integerPiFunctor ((k : ℤ) - (m : ℤ))).map f) ≫
      (rawPredecessorTypeColimitNatIso hSource m k).inv.app Y =
        (rawPredecessorTypeColimitNatIso hSource m k).inv.app X ≫ rawPiColimitMap f m k :=
  (rawPredecessorTypeColimitNatIso hSource m k).inv.naturality f

include hSource in
/-- Actual signed integer isomorphisms prove all original raw predecessor Type isomorphisms. -/
theorem rawPiColimitMap_isIso_of_integer_of_sourceEquation {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (hPi : ∀ q : ℤ, IsIso ((Actual.SymmetricIntegerHomotopy.integerPiFunctor q).map f))
    (m k : ℕ) : IsIso (rawPiColimitMap f m k) := by
  let _ := hPi ((k : ℤ) - (m : ℤ))
  let g := (forget GrpCat.{v}).map
    ((Actual.SymmetricIntegerHomotopy.integerPiFunctor ((k : ℤ) - (m : ℤ))).map f)
  have hg : IsIso g := by infer_instance
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (Arrow.isoMk ((rawPredecessorTypeColimitNatIso hSource m k).app X).symm
      ((rawPredecessorTypeColimitNatIso hSource m k).app Y).symm
      (rawPredecessorTypeColimitNatIso_inv_naturality hSource f m k).symm)).mp hg

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The actual original function functor preserves every original projective level weak map. -/
theorem originalR_preservesWeak {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (hf : weakEquivalences Carrier.{u, v} f) : weakEquivalences Carrier.{u, v} (R.map f) :=
  NativeSymmetricR.SourceIteration.functor_map_mem_weak f hf

private theorem nativeUnit_weak_of_coordinates
    {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
    (d : ℕ → I) (hd : Function.Surjective d)
    {F : EnrichedFunctorCat PointedCGWH.{u, v} I ⥤
      EnrichedFunctorCat PointedCGWH.{u, v} I}
    (η : 𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} I) ⟶ F)
    (e : ∀ m : ℕ, F ⋙ evaluation (d m) ≅ evaluation (d (m + 1)) ⋙ PointedCGWH.loop)
    (c : ∀ m : ℕ, evaluation (V := PointedCGWH.{u, v}) (d m) ⟶
      evaluation (d (m + 1)) ⋙ PointedCGWH.loop)
    (hc : ∀ (E : EnrichedFunctorCat PointedCGWH.{u, v} I) (m : ℕ),
      (c m).app E = (evaluation (d m)).map (η.app E) ≫ (e m).hom.app E)
    (E : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (hW : ∀ m : ℕ, weakEquivalences PointedCGWH.{u, v} ((c m).app E)) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) (η.app E) := by
  apply (PointedCGWH.EnrichedCoaugmentationTelescope.weakEquivalences_iff_components
    (η.app E)).mpr
  intro a
  obtain ⟨m, rfl⟩ := hd a
  let W := weakEquivalences PointedCGWH.{u, v}
  have hw : W ((evaluation (d m)).map (η.app E) ≫ (e m).hom.app E) :=
    (hc E m) ▸ hW m
  have hPoint : W (component (η.app E) (d m)) :=
    W.of_postcomp _ _ (W.of_isIso ((e m).hom.app E)) hw
  exact ((HomotopicalAlgebra.weakEquivalence_iff _).symm.trans
    ((PointedCGWH.weakEquivalence_iff _).trans
      (CGWH.modelCategory.weakEquivalence_iff _))).mp hPoint

include hSource in
omit B in
/-- The original coefficient and original Omega hypothesis prove the actual coordinate weak. -/
theorem originalCoordinate_weak (E : Carrier.{u, v})
    (hE : NativeK.IsOmega Actual.symmetricFamily E) (m : ℕ) :
    weakEquivalences PointedCGWH.{u, v} ((originalCoordinate m).app E) := by
  let W := weakEquivalences PointedCGWH.{u, v}
  let c := (firstScalarIso ((bare E).obj (finiteIndex (m + 1)))).hom
  have hw : W (NativeSymmetricDelooping.omegaMap E (finiteIndex m) (finiteIndex 1) ≫ c) :=
    W.comp_mem _ _ (hE (finiteIndex m, finiteIndex 1)) (W.of_isIso c)
  exact (hSource E m).symm ▸ hw

include hSource in
/-- The exact source equality proves weakness of the same original lambda at every Omega target. -/
theorem originalLambda_weak (E : Carrier.{u, v}) (hE : NativeK.IsOmega Actual.symmetricFamily E) :
    weakEquivalences Carrier.{u, v} (eta.app E) :=
  nativeUnit_weak_of_coordinates index
    symmetricIndex_surjective
    eta stepEvaluation originalCoordinate (fun E m => originalCoordinate_app m E)
    E (fun m => originalCoordinate_weak hSource E hE m)

/-- This is the actual original mapping-cylinder telescope functor of the native lambda. -/
abbrev originalTelescope : Carrier.{u, v} ⥤ Carrier.{u, v} :=
  PointedCGWH.EnrichedCoaugmentationTelescope.telescopeFunctor eta

/-- Its original stage-zero unit is the same chosen original colimit leg. -/
abbrev originalUnit : 𝟭 Carrier.{u, v} ⟶ originalTelescope :=
  PointedCGWH.EnrichedCoaugmentationTelescope.unit eta

include hSource in
/-- The same actual original unit is level weak at every original full-family Omega target. -/
theorem originalTargetUnit_weak (E : Carrier.{u, v})
    (hE : NativeK.IsOmega Actual.symmetricFamily E) :
    weakEquivalences Carrier.{u, v} (originalUnit.app E) :=
  PointedCGWH.EnrichedCoaugmentationTelescope.unit_mem_weak_of_preserves eta
    (fun f hf => originalR_preservesWeak f hf) E (originalLambda_weak hSource E hE)

include hSource in
/-- Every original Omega target retains its whole Omega family on the same actual telescope. -/
theorem originalTelescope_isOmega (E : Carrier.{u, v})
    (hE : NativeK.IsOmega Actual.symmetricFamily E) :
    NativeK.IsOmega Actual.symmetricFamily (originalTelescope.obj E) :=
  OriginalOmegaTargetPreservation.telescope_isOmega Actual.symmetricFamily eta
    (fun f hf => originalR_preservesWeak f hf) E hE (originalLambda_weak hSource E hE)

include hSource in
/-- All original integer maps detect the level class of the same actual R/lambda telescope. -/
theorem originalTelescopeMap_weak_of_integer_of_sourceEquation {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (hPi : ∀ q : ℤ, IsIso ((Actual.SymmetricIntegerHomotopy.integerPiFunctor q).map f)) :
    weakEquivalences Carrier.{u, v} (originalTelescope.map f) :=
  telescopeMap_weak_of_raw_colimit_isIso
    index eta stepEvaluation
    symmetricIndex_surjective
    f (fun m k => rawPiColimitMap_isIso_of_integer_of_sourceEquation hSource f hPi m k)

include hSource in
/-- The original Hom retraction retains both units and only inverts the target unit. -/
theorem originalPrecomp_bijective_of_sourceEquation {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (hPi : ∀ q : ℤ, IsIso ((Actual.SymmetricIntegerHomotopy.integerPiFunctor q).map f))
    (E : Carrier.{u, v}) (hE : NativeK.IsOmega Actual.symmetricFamily E) :
    Function.Bijective (fun g : (toHomotopyCategory Carrier.{u, v}).obj Y ⟶
      (toHomotopyCategory Carrier.{u, v}).obj E =>
        (toHomotopyCategory Carrier.{u, v}).map f ≫ g) := by
  let hF : ∀ ⦃A D : Carrier.{u, v}⦄ (g : A ⟶ D),
      weakEquivalences Carrier.{u, v} g → weakEquivalences Carrier.{u, v} (R.map g) :=
    fun ⦃A D⦄ g hg => originalR_preservesWeak (X := A) (Y := D) g hg
  exact OriginalTelescopeOmegaHomRetract.originalPrecomp_bijective
    (I := PointedCGWH.SymmetricOperatorIndex.{u, v}) (F := R.{u, v}) eta hF f
    (originalTelescopeMap_weak_of_integer_of_sourceEquation hSource f hPi) E
    (originalLambda_weak hSource E hE)

include hSource in
/-- The precise original source equation supplies all original Omega tests on every native arrow. -/
theorem integerIsos_imply_omegaTests_of_sourceEquation {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (hPi : ∀ q : ℤ, IsIso ((Actual.SymmetricIntegerHomotopy.integerPiFunctor q).map f)) :
    NativeK.omegaTests Actual.symmetricFamily f :=
  fun E hE => originalPrecomp_bijective_of_sourceEquation hSource f hPi E hE

end OriginalSourceEquation

end PointedCGWH.Spectra.OriginalSymmetricPiStarOmegaTests
