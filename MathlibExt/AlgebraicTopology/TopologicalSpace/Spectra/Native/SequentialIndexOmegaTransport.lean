/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialIndexStabilizationTransport
import MathlibExt.CategoryTheory.Enriched.EnrichedAdjunctionValue
import MathlibExt.CategoryTheory.Enriched.RestrictionInversePair
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown
import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying

/-!
# Full original sphere-power Omega transport

The original sequential higher Hom action is recovered from the original
ordered successor iteration. The actual closed currying isomorphisms and
Brown's lemma prove the higher weak tests. The symmetric comparison retains
the genuine target block permutations at every dimension, including zero.
The original one-step sequential K family is unchanged.
-/

set_option autoImplicit false
noncomputable section
universe u v uV vV

open CategoryTheory Limits MonoidalCategory MonoidalClosed BraidedCategory
open HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open CategoryTheory.Spectra CategoryTheory.Spectra.SpectrumIndexMaps
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport
open scoped CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport.Sequential

attribute [local instance] PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal MonoidalClosed.enrichedCategorySelf
  MonoidalClosed.enrichedOrdinaryCategorySelf
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

local notation "I" => Operad.SmallFinBijGroupoid

private theorem curry_composite {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
    [MonoidalClosed V]
    (P K A B C : V) (f : K ⊗ A ⟶ B) (g : P ⊗ B ⟶ C) :
    curry ((α_ P K A).hom ≫ (P ◁ f) ≫ g) ≫ (ihomCurryIso P K C).hom =
      curry f ≫ (ihom K).map (curry g) := by
  let h : (P ⊗ K) ⊗ A ⟶ C := (α_ P K A).hom ≫ (P ◁ f) ≫ g
  have hh : uncurry (uncurry (curry h ≫ ihomCurry P K C)) =
      (α_ P K A).inv ≫ h := by
    simp only [uncurry_natural_left, uncurry_uncurry_ihomCurry]
    rw [associator_inv_naturality_right_assoc, whiskerLeft_curry_ihom_ev_app]
  apply uncurry_injective
  apply uncurry_injective
  change uncurry (uncurry (curry h ≫ ihomCurry P K C)) = _
  rw [hh]
  simp only [h, Iso.inv_hom_id_assoc]
  rw [uncurry_natural_right, uncurry_curry, uncurry_natural_left, uncurry_curry]

section Model

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalClosed V] [ModelCategory V] [IsClosedSymmetricMonoidalModelCategory V]
  [∀ Y : V, IsFibrant Y]

private theorem ihom_weak (K : V) [IsCofibrant K] {A B : V} (f : A ⟶ B)
    (hf : weakEquivalences V f) : weakEquivalences V ((ihom K).map f) := by
  let _ := ihomAdjunction_isQuillenAdjunction_of_isCofibrant K
  let _ : WeakEquivalence f := (HomotopicalAlgebra.weakEquivalence_iff f).mpr hf
  exact (HomotopicalAlgebra.weakEquivalence_iff _).mp
    (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant (adj := ihom.adjunction K) f)

private theorem iteratedAdjoint_weak (K : V) [IsCofibrant K]
    (X : CategoryTheory.SequentialSpectrum V K)
    (hX : ∀ n, weakEquivalences V (curry (X.structureMap n))) (p n : ℕ) :
    weakEquivalences V (curry (CategoryTheory.SequentialSpectrum.iteratedStructureMap X p n)) := by
  induction p generalizing n with
  | zero =>
    let d : X.level n ⟶ X.level (0 + n) := eqToHom (congrArg X.level (Nat.zero_add n).symm)
    have hu : curry (λ_ (X.level n)).hom = unitNatIso.hom.app (X.level n) := by
      apply uncurry_injective
      rw [uncurry_curry, EnrichedAdjunctionHom.UnitValue.unitNatIso_hom_uncurry]
    have h0 : curry (CategoryTheory.SequentialSpectrum.iteratedStructureMap X 0 n) =
        unitNatIso.hom.app (X.level n) ≫ (ihom (𝟙_ V)).map d :=
      (congrArg curry (CategoryTheory.SequentialSpectrum.iteratedStructureMap_zero X n)).trans
        ((curry_natural_right (λ_ (X.level n)).hom d).trans
          (congrArg (fun f => f ≫ (ihom (𝟙_ V)).map d) hu))
    have hw := (weakEquivalences V).comp_mem _ _
      ((weakEquivalences V).of_isIso (unitNatIso.hom.app (X.level n)))
      ((weakEquivalences V).of_isIso ((ihom (𝟙_ V)).map d))
    exact h0.symm ▸ hw
  | succ p ih =>
    let P := TensorPower.tensorPowObj K p
    let A := X.level n
    let B := X.level (n + 1)
    let C := X.level (p + (n + 1))
    let f : K ⊗ A ⟶ B := X.structureMap n
    let g : P ⊗ B ⟶ C := CategoryTheory.SequentialSpectrum.iteratedStructureMap X p (n + 1)
    let h : (P ⊗ K) ⊗ A ⟶ C := (α_ P K A).hom ≫ (P ◁ f) ≫ g
    let e := ihomCurryIso P K C
    have he : weakEquivalences V e.hom := (weakEquivalences V).of_isIso _
    have hc : curry h ≫ e.hom = curry f ≫ (ihom K).map (curry g) :=
      curry_composite P K A B C f g
    have hr : weakEquivalences V (curry h ≫ e.hom) := by
      rw [hc]
      exact (weakEquivalences V).comp_mem _ _ (hX n) (ihom_weak K (curry g) (ih (n + 1)))
    have hh := (weakEquivalences V).of_postcomp (curry h) e.hom he hr
    let d : C ⟶ X.level ((p + 1) + n) := eqToHom (congrArg X.level
      ((Nat.add_succ p n).trans (Nat.succ_add p n).symm))
    have hb : CategoryTheory.SequentialSpectrum.iteratedStructureMap X (p + 1) n = h ≫ d := by
      rw [CategoryTheory.SequentialSpectrum.iteratedStructureMap_succ]
      simp only [h, f, g, P, A, B, C, d, id_tensorHom, Category.assoc]
      rfl
    have hj : curry (CategoryTheory.SequentialSpectrum.iteratedStructureMap X (p + 1) n) =
        curry h ≫ (ihom (P ⊗ K)).map d :=
      (congrArg curry hb).trans (curry_natural_right h d)
    have hw := (weakEquivalences V).comp_mem _ _ hh
      ((weakEquivalences V).of_isIso ((ihom (P ⊗ K)).map d))
    exact hj.symm ▸ hw

end Model


/-- Every original finite-bijection index is recovered from its actual dimension. -/
theorem finiteIndex_of_len (n : I) : finiteIndex n.of.len = n := rfl

/-- The real target block permutation and original degree cast at every sphere power. -/
def orderedTargetPermutation (n a : ℕ) :
    finiteIndex n ⊗ finiteIndex a ≅ finiteIndex (n + a) :=
  (β_ (finiteIndex a) (finiteIndex n)).symm ≪≫
    eqToIso (show finiteIndex a ⊗ finiteIndex n = finiteIndex (n + a) from
      congrArg finiteIndex (Nat.add_comm a n))

private theorem orderedTargetPermutation_factor (n a : ℕ) :
    (β_ (finiteIndex a) (finiteIndex n)).hom ≫ (orderedTargetPermutation n a).hom =
      eqToHom (show finiteIndex a ⊗ finiteIndex n = finiteIndex (n + a) from
        congrArg finiteIndex (Nat.add_comm a n)) :=
  Iso.hom_inv_id_assoc (β_ (finiteIndex a) (finiteIndex n)) _

/-- The entire original symmetric target-index isomorphism at every original dimension pair. -/
def orderedIndexIso (n a : ℕ) := symmetricIndexIso.{u, v} (orderedTargetPermutation n a)

/-- The original sequential enriched Hom is the original degree-difference sphere power. -/
def sequentialPowerIso (n a : ℕ) :
    (sequentialDegree.{u, v} n ⟶[PointedCGWH.{u, v}] sequentialDegree.{u, v} (n + a)) ≅
      TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} a :=
  eqToIso ((CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom_of_le
    PointedCGWH.sphereOne.{u, v} (sequentialDegree n) (sequentialDegree (n + a))
    (show n ≤ n + a from Nat.le_add_right n a)).trans
      (congrArg (TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v})
        (Nat.add_sub_cancel_left n a)))

/-- Full sequential Hom transport retains the original ordered sphere generator at every power. -/
theorem sequentialPower_inclusion_map (n a : ℕ) :
    (sequentialPowerIso.{u, v} n a).inv ≫
        sequentialSymmetricOperatorHomMap.{u, v} (sequentialDegree n) (sequentialDegree (n + a)) =
      orderedSymmetricOperatorHom.{u, v} n (n + a) a (Nat.add_comm a n) := by
  let K := PointedCGWH.sphereOne.{u, v}
  let i := sequentialDegree.{u, v} n
  let j := sequentialDegree.{u, v} (n + a)
  let d := (n + a) - n
  have hd : d = a := Nat.add_sub_cancel_left n a
  have hij : i.degree ≤ j.degree := Nat.le_add_right n a
  let H := i ⟶[PointedCGWH.{u, v}] j
  let P := TensorPower.tensorPowObj K d
  let Q := TensorPower.tensorPowObj K a
  let Z := symmetricDegree.{u, v} n ⟶[PointedCGWH.{u, v}] symmetricDegree.{u, v} (n + a)
  let eH : H = P := CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom_of_le K i j hij
  let eP : P = Q := congrArg (TensorPower.tensorPowObj K) hd
  let s : Q ⟶ H := (sequentialPowerIso n a).inv
  let q : H ⟶ P := eqToHom eH
  let t : P ⟶ Q := eqToHom eP
  let m : H ⟶ Z := sequentialSymmetricOperatorHomMap i j
  let g : P ⟶ Z := orderedSymmetricOperatorHom n (n + a) d (Nat.sub_add_cancel hij)
  let z : Q ⟶ Z := orderedSymmetricOperatorHom n (n + a) a (Nat.add_comm a n)
  have hm : m = q ≫ g := sequentialSymmetricOperatorHomMap_of_le i j hij
  have hg : g = t ≫ z := (orderedSymmetricOperatorHom_cast
    n (n + a) d a hd (Nat.sub_add_cancel hij) (Nat.add_comm a n)).symm
  have hs : s = eqToHom (eH.trans eP).symm := rfl
  have hCast : s ≫ q ≫ t = 𝟙 Q := by
    rw [hs]
    rw [eqToHom_trans, eqToHom_trans]
    rfl
  change s ≫ m = z
  rw [hm, hg, ← Category.assoc q t z, ← Category.assoc s (q ≫ t) z, hCast, Category.id_comp]

/-- The actual native inclusion, followed by the real target permutation, is the original
ordered generator. -/
theorem ordered_inclusion_factor (n a : ℕ) :
    Actual.symmetricNu.{u, v} (finiteIndex n) (finiteIndex a) ≫
        eHomWhiskerLeft PointedCGWH.{u, v}
          (ForgetEnrichment.of PointedCGWH.{u, v} (symmetricDegree n)) (orderedIndexIso n a).hom =
      orderedSymmetricOperatorHom.{u, v} n (n + a) a (Nat.add_comm a n) := by
  let N := finiteIndex n
  let A := finiteIndex a
  let B := N ⊗ A
  let C := finiteIndex (n + a)
  let S := PointedCGWH.sphereSequence.{u, v}.functor.obj A
  let H := PointedCGWH.symmetricOperatorObj.{u, v} N ⟶[PointedCGWH.{u, v}]
    PointedCGWH.symmetricOperatorObj.{u, v} B
  let E : S ⟶ H := Actual.symmetricNu N A
  let p := symmetricIndexPoint.{u, v} B C (orderedTargetPermutation n a).hom
  have ht : E ≫ eHomWhiskerLeft PointedCGWH.{u, v}
      (ForgetEnrichment.of PointedCGWH.{u, v} (PointedCGWH.symmetricOperatorObj N))
      (orderedIndexIso n a).hom =
      (ρ_ S).inv ≫ (E ⊗ₘ p) ≫
        eComp PointedCGWH.{u, v} (PointedCGWH.symmetricOperatorObj N)
          (PointedCGWH.symmetricOperatorObj B) (PointedCGWH.symmetricOperatorObj C) := by
    change E ≫ (ρ_ H).inv ≫ (H ◁ p) ≫ _ = _
    rw [rightUnitor_inv_naturality_assoc]
    simp only [tensorHom_def, Category.assoc]
    rfl
  have hg := generator_postcomposition A N B C (β_ A N).hom (orderedTargetPermutation n a).hom
  have hf := congrArg (fun f : A ⊗ N ⟶ C =>
    PointedCGWH.SymmetricModulePresentation.operatorGenerator A N C f)
      (orderedTargetPermutation_factor n a)
  exact ht.trans (hg.trans hf)

/-- The entire actual coefficient-first higher sequential transpose. -/
def sequentialPowerAdjoint (X : PointedCGWH.SequentialSpectrum.{u, v}) (n a : ℕ) :
    X.toEnrichedFunctor.obj (sequentialDegree n) ⟶
      (ihom (TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} a)).obj
        (X.toEnrichedFunctor.obj (sequentialDegree (n + a))) :=
  CurrentFree.adjoint (sequentialDegree n) (sequentialDegree (n + a))
    (TensorPower.tensorPowObj PointedCGWH.sphereOne a) (sequentialPowerIso n a).inv X

/-- The complete higher transpose target isomorphism is the real native target-index action. -/
def powerComparisonIso (X : Actual.SymmetricCarrier.{u, v}) (n a : ℕ) :=
  (ihom (TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} a)).mapIso
    (indexValueIso X (orderedIndexIso n a))

/-- Each original higher sequential transpose is the native full-family transpose through
the actual target isomorphism. -/
theorem sequentialPowerSymmetric_adjoint (X : Actual.SymmetricCarrier.{u, v}) (n a : ℕ) :
    sequentialPowerAdjoint
        ((restriction sequentialSymmetricOperatorIndexFunctor.{u, v}).obj X) n a =
      symmetricAdjoint X (finiteIndex n) (finiteIndex a) ≫ (powerComparisonIso X n a).hom := by
  let P := TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} a
  have hD : (sequentialPowerIso n a).inv ≫
      sequentialSymmetricOperatorHomMap.{u, v} (sequentialDegree n) (sequentialDegree (n + a)) =
      (Iso.refl P).hom ≫ Actual.symmetricNu (finiteIndex n) (finiteIndex a) ≫
        eHomWhiskerLeft PointedCGWH.{u, v}
          (ForgetEnrichment.of PointedCGWH.{u, v} (symmetricDegree n))
          (orderedIndexIso n a).hom := by
    exact (sequentialPower_inclusion_map n a).trans (ordered_inclusion_factor n a).symm
  have h := restriction_adjoint_comparison sequentialSymmetricOperatorIndexFunctor
    (sequentialDegree n) (sequentialDegree (n + a))
    (PointedCGWH.symmetricOperatorObj.{u, v} (finiteIndex n ⊗ finiteIndex a))
    (Iso.refl P) (orderedIndexIso n a) (sequentialPowerIso n a).inv
    (Actual.symmetricNu (finiteIndex n) (finiteIndex a)) hD X
  dsimp only [coefficientPreIso, Iso.refl_hom] at h
  rw [MonoidalClosed.pre_id, NatTrans.id_app, Category.comp_id] at h
  exact h

/-- Every original full-family weak test is equivalent to its complete higher sequential
Hom test. -/
theorem sequentialPowerSymmetric_weak_adjoint_iff (X : Actual.SymmetricCarrier.{u, v}) (n a : ℕ) :
    weakEquivalences PointedCGWH.{u, v}
      (sequentialPowerAdjoint
        ((restriction sequentialSymmetricOperatorIndexFunctor.{u, v}).obj X) n a) ↔
    weakEquivalences PointedCGWH.{u, v} (symmetricAdjoint X (finiteIndex n) (finiteIndex a)) := by
  let e := powerComparisonIso X n a
  have he : weakEquivalences PointedCGWH.{u, v} e.hom :=
    (weakEquivalences PointedCGWH.{u, v}).of_isIso _
  rw [sequentialPowerSymmetric_adjoint]
  constructor
  · intro h
    exact (weakEquivalences PointedCGWH.{u, v}).of_postcomp _ _ he h
  · intro h
    exact (weakEquivalences PointedCGWH.{u, v}).comp_mem _ _ h he

/-- The full forward sequential Hom is the original degree-difference coefficient. -/
def sequentialForwardIso (n k : ℕ) (h : n ≤ k) :
    (sequentialDegree.{u, v} n ⟶[PointedCGWH.{u, v}] sequentialDegree.{u, v} k) ≅
      TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} (k - n) :=
  eqToIso (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom_of_le
    PointedCGWH.sphereOne.{u, v} (sequentialDegree n) (sequentialDegree k) h)

/-- The complete native forward Hom action is the original ordered successor iteration. -/
theorem sequentialForward_action (X : PointedCGWH.SequentialSpectrum.{u, v})
    (n k : ℕ) (h : n ≤ k) :
    let Y := CategoryTheory.SequentialSpectrum.EnrichedPresentation.fromEnrichedFunctor
      PointedCGWH.sphereOne.{u, v} X
    CurrentFree.action (sequentialDegree n) (sequentialDegree k)
        (TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} (k - n))
        (sequentialForwardIso n k h).inv X =
      CategoryTheory.SequentialSpectrum.iteratedStructureMap Y (k - n) n ≫
        eqToHom (congrArg Y.level (Nat.sub_add_cancel h)) := by
  dsimp only
  let K := PointedCGWH.sphereOne.{u, v}
  let i := sequentialDegree.{u, v} n
  let j := sequentialDegree.{u, v} k
  let Y := CategoryTheory.SequentialSpectrum.EnrichedPresentation.fromEnrichedFunctor K X
  let A := X.toEnrichedFunctor.obj i
  let B := X.toEnrichedFunctor.obj j
  let H := i ⟶[PointedCGWH.{u, v}] j
  let P := TensorPower.tensorPowObj K (k - n)
  let e : H ≅ P := sequentialForwardIso n k h
  let q : H ⟶ P := e.hom
  let s : P ⟶ H := e.inv
  let f : A ⊗ H ⟶ B := MonoidalClosed.uncurry (X.toEnrichedFunctor.map i j)
  let t : P ⊗ A ⟶ B :=
    CategoryTheory.SequentialSpectrum.iteratedStructureMap Y (k - n) n ≫
      eqToHom (congrArg Y.level (Nat.sub_add_cancel h))
  have hr : f = CategoryTheory.SequentialSpectrum.EnrichedPresentation.spectrumAction Y i j :=
    (eq_of_heq
      (CategoryTheory.SequentialSpectrum.EnrichedPresentation.higher_action_recovery K X i j)).symm
  have hs : f = (A ◁ q) ≫ (β_ A P).hom ≫ t := by
    let hH : H = P := CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom_of_le K i j h
    have hx : CategoryTheory.SequentialSpectrum.EnrichedPresentation.spectrumAction Y i j =
        eqToHom (congrArg (fun Z : PointedCGWH.{u, v} => A ⊗ Z) hH) ≫ (β_ A P).hom ≫ t :=
      CategoryTheory.SequentialSpectrum.EnrichedPresentation.spectrumAction_of_le Y i j h
    have hcast : eqToHom (congrArg (fun Z : PointedCGWH.{u, v} => A ⊗ Z) hH) = A ◁ q :=
      (whiskerLeft_eqToHom A hH).symm
    exact hr.trans (hx.trans (congrArg (fun f => f ≫ (β_ A P).hom ≫ t) hcast))
  change (s ▷ A) ≫ (β_ A H).inv ≫ f = t
  rw [hs]
  rw [braiding_inv_naturality_left_assoc, ← whiskerLeft_comp_assoc,
    e.inv_hom_id, whiskerLeft_id, Category.id_comp, Iso.inv_hom_id_assoc]

/-- The entire original forward Hom transpose of an Omega spectrum is weak at every degree pair. -/
theorem sequentialForward_adjoint_weak (X : PointedCGWH.SequentialSpectrum.{u, v})
    (hX : X.IsOmega) (n k : ℕ) (h : n ≤ k) :
    weakEquivalences PointedCGWH.{u, v}
      (CurrentFree.adjoint (sequentialDegree n) (sequentialDegree k)
        (TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} (k - n))
        (sequentialForwardIso n k h).inv X) := by
  let K := PointedCGWH.sphereOne.{u, v}
  let Y := CategoryTheory.SequentialSpectrum.EnrichedPresentation.fromEnrichedFunctor K X
  let _ : IsCofibrant K := PointedCGWH.modelCategory.sphereOne_isCofibrant
  let _ : ∀ Z : PointedCGWH.{u, v}, IsFibrant Z := PointedCGWH.modelCategory.allObjectsFibrant
  have hY : ∀ m, weakEquivalences PointedCGWH.{u, v} (MonoidalClosed.curry (Y.structureMap m)) := by
    intro m
    change weakEquivalences PointedCGWH.{u, v}
      (PointedCGWH.SequentialSpectrum.adjointStructureMap X m)
    exact ((HomotopicalAlgebra.weakEquivalence_iff _).symm.trans
      ((PointedCGWH.weakEquivalence_iff _).trans
        (CGWH.modelCategory.weakEquivalence_iff _))).mpr (hX m)
  let f := CategoryTheory.SequentialSpectrum.iteratedStructureMap Y (k - n) n
  let d : Y.level ((k - n) + n) ⟶ Y.level k := eqToHom (congrArg Y.level (Nat.sub_add_cancel h))
  have hf : weakEquivalences PointedCGWH.{u, v} (MonoidalClosed.curry f) :=
    iteratedAdjoint_weak K Y hY (k - n) n
  have hd : weakEquivalences PointedCGWH.{u, v}
      ((ihom (TensorPower.tensorPowObj K (k - n))).map d) :=
    (weakEquivalences PointedCGWH.{u, v}).of_isIso _
  have ht : CurrentFree.adjoint (sequentialDegree n) (sequentialDegree k)
      (TensorPower.tensorPowObj K (k - n)) (sequentialForwardIso n k h).inv X =
      MonoidalClosed.curry f ≫ (ihom (TensorPower.tensorPowObj K (k - n))).map d :=
    (congrArg MonoidalClosed.curry (sequentialForward_action X n k h)).trans
      (MonoidalClosed.curry_natural_right f d)
  exact ht.symm ▸ (weakEquivalences PointedCGWH.{u, v}).comp_mem _ _ hf hd

/-- The original full higher-power transpose is weak, derived from the original one-circle
Omega maps. -/
theorem sequentialPowerAdjoint_weak (X : PointedCGWH.SequentialSpectrum.{u, v})
    (hX : X.IsOmega) (n a : ℕ) :
    weakEquivalences PointedCGWH.{u, v} (sequentialPowerAdjoint X n a) := by
  let K := PointedCGWH.sphereOne.{u, v}
  let i := sequentialDegree.{u, v} n
  let j := sequentialDegree.{u, v} (n + a)
  let P := TensorPower.tensorPowObj K a
  let T := TensorPower.tensorPowObj K ((n + a) - n)
  let H := i ⟶[PointedCGWH.{u, v}] j
  let hnk : n ≤ n + a := Nat.le_add_right n a
  let e : P ≅ T := eqToIso (congrArg (TensorPower.tensorPowObj K)
    (Nat.add_sub_cancel_left n a).symm)
  let D : T ⟶ H := (sequentialForwardIso n (n + a) hnk).inv
  let f := CurrentFree.adjoint i j T D X
  let hHT : H = T := CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom_of_le K i j hnk
  let hTP : T = P := congrArg (TensorPower.tensorPowObj K) (Nat.add_sub_cancel_left n a)
  have hf : weakEquivalences PointedCGWH.{u, v} f :=
    sequentialForward_adjoint_weak X hX n (n + a) hnk
  have hd : (sequentialPowerIso n a).inv = e.hom ≫ D := by
    change eqToHom (hHT.trans hTP).symm = eqToHom hTP.symm ≫ eqToHom hHT.symm
    rw [eqToHom_trans]
  have hp : CurrentFree.adjoint i j P (e.hom ≫ D) X =
      f ≫ (coefficientPreIso e (X.toEnrichedFunctor.obj j)).hom := by
    apply MonoidalClosed.uncurry_injective
    change MonoidalClosed.uncurry (CurrentFree.adjoint i j P (e.hom ≫ D) X) =
      MonoidalClosed.uncurry (CurrentFree.adjoint i j T D X ≫
        (MonoidalClosed.pre e.hom).app (X.toEnrichedFunctor.obj j))
    rw [MonoidalClosed.uncurry_pre_app, CurrentFree.adjoint_uncurry, CurrentFree.adjoint_uncurry]
    unfold CurrentFree.action
    rw [comp_whiskerRight]
    simp only [Category.assoc]
  have ht : sequentialPowerAdjoint X n a =
      f ≫ (coefficientPreIso e (X.toEnrichedFunctor.obj j)).hom :=
    (congrArg (fun d : P ⟶ H => CurrentFree.adjoint i j P d X) hd).trans hp
  have he : weakEquivalences PointedCGWH.{u, v}
      (coefficientPreIso e (X.toEnrichedFunctor.obj j)).hom :=
    (weakEquivalences PointedCGWH.{u, v}).of_isIso _
  exact ht.symm ▸ (weakEquivalences PointedCGWH.{u, v}).comp_mem _ _ hf he

/-- Original sequential forgetting and the complete original symmetric Omega family agree. -/
theorem sequentialSymmetric_isOmega_iff (X : Actual.SymmetricCarrier.{u, v}) :
    PointedCGWH.SequentialSpectrum.IsOmega
        ((restriction sequentialSymmetricOperatorIndexFunctor.{u, v}).obj X) ↔
      NativeK.IsOmega Actual.symmetricFamily.{u, v} X := by
  constructor
  · intro h na
    rcases na with ⟨⟨⟨n⟩⟩, ⟨⟨a⟩⟩⟩
    exact (sequentialPowerSymmetric_weak_adjoint_iff X n a).mp
      (sequentialPowerAdjoint_weak
        ((restriction sequentialSymmetricOperatorIndexFunctor.{u, v}).obj X) h n a)
  · intro h
    exact sequentialSymmetric_isOmega_of_isOmega X h

/-- The original structure-map source forgetting has the same complete original Omega predicate. -/
theorem symmetricSource_isOmega_iff (X : Actual.SymmetricCarrier.{u, v}) :
    PointedCGWH.SequentialSpectrum.IsOmega ((symmetricToSequentialSourceForget.{u, v}).obj X) ↔
      NativeK.IsOmega Actual.symmetricFamily.{u, v} X := by
  rw [symmetricToSequentialSourceForget_eq_restriction]
  exact sequentialSymmetric_isOmega_iff X

/-- The genuine composite of both full index maps identifies the complete original
orthogonal Omega family. -/
theorem sequentialOrthogonal_isOmega_iff (X : Actual.OrthogonalCarrier.{u, v}) :
    PointedCGWH.SequentialSpectrum.IsOmega
        ((restriction sequentialOrthogonalOperatorIndexFunctor.{u, v}).obj X) ↔
      NativeK.IsOmega Actual.orthogonalFamily.{u, v} X := by
  rw [sequentialOrthogonalOperatorIndexFunctor, ← RestrictionInversePair.restriction_comp]
  exact (sequentialSymmetric_isOmega_iff
    ((restriction symmetricOrthogonalOperatorIndexFunctor.{u, v}).obj X)).trans
      (symmetricOrthogonal_isOmega_iff X)

end HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport.Sequential
