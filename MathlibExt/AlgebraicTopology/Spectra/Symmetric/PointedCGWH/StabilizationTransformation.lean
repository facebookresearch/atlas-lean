/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.ShiftOmega
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.LabelTransformation
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.Omega
import MathlibExt.CategoryTheory.Monoidal.Closed.CoefficientShuffleNaturality

/-!
# The stabilization transformation to shifted loops

The adjoints of the symmetric spectrum structure maps assemble into a natural
transformation from a spectrum to its shifted sphere cotensor. Compatibility
with every coefficient label follows from the sphere tensorator and braiding
identities. For a spectrum satisfying the full symmetric Omega condition,
this transformation is a weak equivalence in the level model structure.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory BraidedCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CGWH.modelCategory

namespace NativeOmegaRecovery.NativeSymmetricDelooping

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev J := PointedCGWH.SymmetricOperatorIndex.{u, v}
private abbrev Carrier := EnrichedFunctorCat V.{u, v} J.{u, v}
private abbrev S := PointedCGWH.sphereSequence.{u, v}
attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal

open PointedCGWH.SymmetricModulePresentation
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK

private def coefficientMu (r a : I) :
    S.{u, v}.functor.obj r ⊗ S.{u, v}.functor.obj a ⟶
      S.{u, v}.functor.obj (r ⊗ a) :=
  PointedCGWH.sphereCopowerLaxData.{u, v}.mu
    ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj r)
    ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj a)

/-- The complete original sphere tensorator retains its coefficient and index block swap. -/
theorem coefficientMu_comm (r a : I) :
    (β_ (S.{u, v}.functor.obj r) (S.{u, v}.functor.obj a)).hom ≫
        coefficientMu a r ≫ S.{u, v}.functor.map (β_ a r).hom = coefficientMu r a := by
  exact PointedCGWH.sphereSequence_mul_app_permutation r a

/-- The two original action composition labels differ by exactly the sphere block swap. -/
theorem exchangeLabel (r a n k : I) (f : a ⊗ n ⟶ k) :
    (α_ a r n).hom ≫ (a ◁ (β_ r n).hom) ≫
        PointedCGWH.SymmetricShift.label r n k a f =
      ((β_ a r).hom ▷ n) ≫ (α_ r a n).hom ≫ (r ◁ f) ≫ (β_ r k).hom := by
  simp only [PointedCGWH.SymmetricShift.label, tensorHom_id]
  rw [braiding_naturality_right r f]
  rw [braiding_tensor_right_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc,
    SymmetricCategory.symmetry, id_whiskerRight, Category.id_comp]

private theorem scalar_action_exchange
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    (R A X Y Z U W T : C)
    (μ : R ⊗ A ⟶ U) (ν : A ⊗ R ⟶ W) (s : W ⟶ U)
    (p : U ⊗ X ⟶ T) (q : W ⊗ X ⟶ T)
    (f : A ⊗ X ⟶ Y) (rN : R ⊗ X ⟶ Z) (rK : R ⊗ Y ⟶ T) (g : A ⊗ Z ⟶ T)
    (hL : (μ ▷ X) ≫ p = (α_ R A X).hom ≫ (R ◁ f) ≫ rK)
    (hR : (ν ▷ X) ≫ q = (α_ A R X).hom ≫ (A ◁ rN) ≫ g)
    (hs : (β_ R A).hom ≫ ν ≫ s = μ) (hq : q = (s ▷ X) ≫ p) :
    (R ◁ f) ≫ rK = NativeOmegaPreparation.CoefficientShuffle.map R A X ≫ (A ◁ rN) ≫ g := by
  have hc := congrArg (fun z : R ⊗ A ⟶ U => (z ▷ X) ≫ p) hs
  simp only [comp_whiskerRight, Category.assoc] at hc
  apply (cancel_epi (α_ R A X).hom).1
  simp only [NativeOmegaPreparation.CoefficientShuffle.map, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [← hL, ← hR, hq]
  exact hc.symm

/-- Every original labelled action commutes with the complete right-degree structure action. -/
theorem action_exchange (E : Carrier.{u, v}) (r a n k : I) (f : a ⊗ n ⟶ k) :
    (S.{u, v}.functor.obj r ◁ reconstructedArrowAction E a n k f) ≫
        reconstructedArrowAction E r k (k ⊗ r) (β_ r k).hom =
      NativeOmegaPreparation.CoefficientShuffle.map
          (S.{u, v}.functor.obj r) (S.{u, v}.functor.obj a)
          (E.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} n)) ≫
        (S.{u, v}.functor.obj a ◁
          reconstructedArrowAction E r n (n ⊗ r) (β_ r n).hom) ≫
        reconstructedArrowAction E a (n ⊗ r) (k ⊗ r)
          (PointedCGWH.SymmetricShift.label r n k a f) := by
  let R := S.{u, v}.functor.obj r
  let A := S.{u, v}.functor.obj a
  let X := E.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} n)
  let l : (r ⊗ a) ⊗ n ⟶ k ⊗ r :=
    (α_ r a n).hom ≫ (r ◁ f) ≫ (β_ r k).hom
  let h : (a ⊗ r) ⊗ n ⟶ k ⊗ r :=
    (α_ a r n).hom ≫ (a ◁ (β_ r n).hom) ≫
      PointedCGWH.SymmetricShift.label r n k a f
  let p := reconstructedArrowAction E (r ⊗ a) n (k ⊗ r) l
  let q := reconstructedArrowAction E (a ⊗ r) n (k ⊗ r) h
  have hL := reconstructedArrowAction_comp E a r n k (k ⊗ r) f (β_ r k).hom
  have hR := reconstructedArrowAction_comp E r a n (n ⊗ r) (k ⊗ r)
    (β_ r n).hom (PointedCGWH.SymmetricShift.label r n k a f)
  simp only [id_tensorHom] at hL hR
  have hCoefficient := reconstructedArrowAction_coefficient E (β_ a r).hom n (k ⊗ r) l
  have hLabel : ((β_ a r).hom ▷ n) ≫ l = h := (exchangeLabel r a n k f).symm
  have hq : q = (S.{u, v}.functor.map (β_ a r).hom ▷ X) ≫ p := by
    simp only [tensorHom_id] at hCoefficient
    rw [hLabel] at hCoefficient
    exact hCoefficient.symm
  exact scalar_action_exchange R A X
    (E.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} k))
    (E.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} (n ⊗ r)))
    (S.{u, v}.functor.obj (r ⊗ a)) (S.{u, v}.functor.obj (a ⊗ r))
    (E.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} (k ⊗ r)))
    (coefficientMu r a) (coefficientMu a r) (S.{u, v}.functor.map (β_ a r).hom) p q
    (reconstructedArrowAction E a n k f)
    (reconstructedArrowAction E r n (n ⊗ r) (β_ r n).hom)
    (reconstructedArrowAction E r k (k ⊗ r) (β_ r k).hom)
    (reconstructedArrowAction E a (n ⊗ r) (k ⊗ r)
      (PointedCGWH.SymmetricShift.label r n k a f))
    hL hR (coefficientMu_comm r a) hq

/-- The actual original full-family transpose, with its native endpoints explicit. -/
def omegaMap (E : Carrier.{u, v}) (n r : I) :
    E.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} n) ⟶
      (ihom (S.{u, v}.functor.obj r)).obj
        (E.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} (n ⊗ r))) :=
  CurrentFree.adjoint (PointedCGWH.symmetricOperatorObj.{u, v} n)
    (PointedCGWH.symmetricOperatorObj.{u, v} (n ⊗ r)) (S.{u, v}.functor.obj r)
    (Actual.symmetricNu.{u, v} n r) E

/-- Uncurrying is the unchanged original full native stabilization action. -/
theorem omegaMap_uncurry (E : Carrier.{u, v}) (n r : I) :
    MonoidalClosed.uncurry (omegaMap E n r) =
      reconstructedArrowAction E r n (n ⊗ r) (β_ r n).hom := by
  exact (CurrentFree.adjoint_uncurry _ _ _ _ E).trans
    (CurrentFree.action_operatorGenerator_eq_reconstructed E r n (n ⊗ r) (β_ r n).hom)

private theorem coefficient_curry_square
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
    (M A X X' Y Y' : C) (f : A ⊗ X ⟶ Y) (g : A ⊗ X' ⟶ Y')
    (p : X ⟶ (ihom M).obj X') (q : Y ⟶ (ihom M).obj Y')
    (h : (M ◁ f) ≫ MonoidalClosed.uncurry q =
      NativeOmegaPreparation.CoefficientShuffle.map M A X ≫
        (A ◁ MonoidalClosed.uncurry p) ≫ g) :
    f ≫ q = (A ◁ p) ≫ MonoidalClosed.curry
      (NativeOmegaPreparation.CoefficientShuffle.map M A ((ihom M).obj X') ≫
        (A ◁ (ihom.ev M).app X') ≫ g) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry]
  rw [reassoc_of% NativeOmegaPreparation.CoefficientShuffle.naturality_third M A p]
  simp only [← whiskerLeft_comp_assoc]
  rw [← MonoidalClosed.uncurry_eq]
  exact h

/-- Every coefficient label is natural for the original stabilization transpose. -/
theorem omegaMap_label_square (E : Carrier.{u, v}) (r a n k : I) (f : a ⊗ n ⟶ k) :
    reconstructedArrowAction E a n k f ≫ omegaMap E k r =
      (S.{u, v}.functor.obj a ◁ omegaMap E n r) ≫
        reconstructedArrowAction
          (cotensorObject (S.{u, v}.functor.obj r)
            ((PointedCGWH.SymmetricShift.functor.{u, v} r).obj E)) a n k f := by
  rw [NativeOmegaPreparation.NativeSymmetricShiftCotensorAction.cotensor_arrow,
    NativeOmegaPreparation.NativeSymmetricShiftCotensorAction.shift_arrow]
  exact coefficient_curry_square
    (S.{u, v}.functor.obj r) (S.{u, v}.functor.obj a)
    (E.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} n))
    (E.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} (n ⊗ r)))
    (E.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} k))
    (E.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} (k ⊗ r)))
    (reconstructedArrowAction E a n k f)
    (reconstructedArrowAction E a (n ⊗ r) (k ⊗ r)
      (PointedCGWH.SymmetricShift.label r n k a f))
    (omegaMap E n r) (omegaMap E k r) (by
      rw [omegaMap_uncurry, omegaMap_uncurry]
      exact action_exchange E r a n k f)

/-- The genuine complete right-shift scalar loop functor. -/
def shiftedLoop (r : I) : Carrier.{u, v} ⥤ Carrier.{u, v} :=
  PointedCGWH.SymmetricShift.functor.{u, v} r ⋙ cotensor (S.{u, v}.functor.obj r)

/-- The complete enriched map is constructed from every original stabilization component. -/
def comparison (r : I) (E : Carrier.{u, v}) : E ⟶ (shiftedLoop r).obj E :=
  NativeSymmetricLabelTransformation.transformation E _
    (fun x => omegaMap E (show I from x.asIndex) r) (by
      intro a n k f
      exact omegaMap_label_square E r a n k f)

/-- Every component is precisely the literal original full-family native adjoint. -/
theorem comparison_component (r : I) (E : Carrier.{u, v}) (n : I) :
    component (comparison r E) (PointedCGWH.symmetricOperatorObj.{u, v} n) =
      CurrentFree.adjoint (PointedCGWH.symmetricOperatorObj.{u, v} n)
        (PointedCGWH.symmetricOperatorObj.{u, v} (n ⊗ r)) (S.{u, v}.functor.obj r)
        (Actual.symmetricNu.{u, v} n r) E := by
  unfold comparison
  exact NativeSymmetricLabelTransformation.transformation_component _ _ _ _ _

/-- The whole shifted scalar-loop functor keeps every actual transformation component. -/
theorem shiftedLoop_map_component (r : I) {E E' : Carrier.{u, v}} (t : E ⟶ E') (n : I) :
    component ((shiftedLoop r).map t) (PointedCGWH.symmetricOperatorObj.{u, v} n) =
      (ihom (S.{u, v}.functor.obj r)).map
        (component t (PointedCGWH.symmetricOperatorObj.{u, v} (n ⊗ r))) := by
  exact (cotensorMap_component (S.{u, v}.functor.obj r)
    ((PointedCGWH.SymmetricShift.functor.{u, v} r).map t) _).trans
      (congrArg (fun q => (ihom (S.{u, v}.functor.obj r)).map q)
        (PointedCGWH.SymmetricShift.functor_map_component r n t))

private theorem index_surjective (x : J.{u, v}) :
    ∃ n : I, PointedCGWH.symmetricOperatorObj.{u, v} n = x := by
  rcases x with ⟨n⟩
  exact ⟨(show I from n), rfl⟩

/-- The original map is natural in every complete native transformation. -/
theorem comparison_naturality (r : I) {E E' : Carrier.{u, v}} (t : E ⟶ E') :
    t ≫ comparison r E' = comparison r E ≫ (shiftedLoop r).map t := by
  apply hom_ext
  intro x
  obtain ⟨n, rfl⟩ := index_surjective x
  rw [component_comp, component_comp, comparison_component, comparison_component,
    shiftedLoop_map_component]
  exact CurrentFree.adjoint_naturality _ _ _ _ t

/-- The unchanged original stabilization maps form a whole natural transformation. -/
def comparisonNat (r : I) : 𝟭 Carrier.{u, v} ⟶ shiftedLoop r where
  app := comparison r
  naturality _ _ t := comparison_naturality r t

/-- Each level is weak for an original full-family Omega spectrum. -/
theorem comparison_level_weak (r : I) (E : Carrier.{u, v})
    (hE : Actual.SymmetricIsOmega E) (n : I) :
    weakEquivalences V.{u, v}
      (component (comparison r E) (PointedCGWH.symmetricOperatorObj.{u, v} n)) := by
  rw [comparison_component]
  exact hE (n, r)

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The entire original comparison is weak in the actual native level model. -/
theorem comparison_weak (r : I) (E : Carrier.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    weakEquivalences Carrier.{u, v} (comparison r E) := by
  rw [HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq]
  apply (HomotopicalAlgebra.EvaluationTransfer.evaluationProperty_iff
    (fun x : J.{u, v} => evaluation (V := V.{u, v}) x) (weakEquivalences V.{u, v}) _).2
  intro x
  obtain ⟨n, rfl⟩ := index_surjective x
  exact comparison_level_weak r E hE n

end NativeOmegaRecovery.NativeSymmetricDelooping
