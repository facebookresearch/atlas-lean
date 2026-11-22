/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.IndexStabilizationTransport
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Sequential.Omega
import MathlibExt.CategoryTheory.Enriched.Ordinary.MapHomWhisker

/-!
# Actual sequential index stabilization transport

The original one-circle successor inclusion is compared with the native symmetric
inclusion through the circle-to-power-one unitor and the actual target index
permutation. Every restriction identity uses the complete enriched Hom map.
The original sequential and full symmetric families remain fixed.
-/

set_option autoImplicit false
noncomputable section
universe u v uA uV vV

open CategoryTheory Limits MonoidalCategory BraidedCategory
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport
open CategoryTheory.Spectra CategoryTheory.Spectra.SpectrumIndexMaps
open scoped CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport.Sequential

attribute [local instance] PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal MonoidalClosed.enrichedCategorySelf
  MonoidalClosed.enrichedOrdinaryCategorySelf
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

local notation "I" => Operad.SmallFinBijGroupoid

section Action

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]

/-- The actual ordinary map induced by a full native enriched functor. -/
def indexMap (X : EnrichedFunctorCat PointedCGWH.{u, v} A) {b c : A}
    (q : ForgetEnrichment.of PointedCGWH.{u, v} b ⟶
      ForgetEnrichment.of PointedCGWH.{u, v} c) :
    X.toEnrichedFunctor.obj b ⟶ X.toEnrichedFunctor.obj c :=
  (eHomEquiv PointedCGWH.{u, v}).symm
    (ForgetEnrichment.homTo PointedCGWH.{u, v} q ≫ X.toEnrichedFunctor.map b c)

/-- The entire coefficient-first action commutes with actual target-index postcomposition. -/
theorem action_postcompose (a b c : A) (K : PointedCGWH.{u, v})
    (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    (q : ForgetEnrichment.of PointedCGWH.{u, v} b ⟶
      ForgetEnrichment.of PointedCGWH.{u, v} c)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    CurrentFree.action a c K
        (D ≫ eHomWhiskerLeft PointedCGWH.{u, v}
          (ForgetEnrichment.of PointedCGWH.{u, v} a) q) X =
      CurrentFree.action a b K D X ≫ indexMap X q := by
  let d : (a ⟶[PointedCGWH.{u, v}] b) ⟶ (a ⟶[PointedCGWH.{u, v}] c) :=
    eHomWhiskerLeft PointedCGWH.{u, v}
    (ForgetEnrichment.of PointedCGWH.{u, v} a) q
  have h : d ≫ X.toEnrichedFunctor.map a c =
      X.toEnrichedFunctor.map a b ≫ (ihom (X.toEnrichedFunctor.obj a)).map (indexMap X q) :=
    EnrichedFunctor.map_postcompose X.toEnrichedFunctor a b c
      (ForgetEnrichment.homTo PointedCGWH.{u, v} q)
  unfold CurrentFree.action
  change (D ≫ d) ▷ X.toEnrichedFunctor.obj a ≫
      (β_ (X.toEnrichedFunctor.obj a) (a ⟶[PointedCGWH.{u, v}] c)).inv ≫
        MonoidalClosed.uncurry (X.toEnrichedFunctor.map a c) = _
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  rw [braiding_inv_naturality_left_assoc, ← MonoidalClosed.uncurry_natural_left]
  rw [h, MonoidalClosed.uncurry_natural_right]

/-- The full original transpose commutes with actual target-index postcomposition. -/
theorem adjoint_postcompose (a b c : A) (K : PointedCGWH.{u, v})
    (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    (q : ForgetEnrichment.of PointedCGWH.{u, v} b ⟶
      ForgetEnrichment.of PointedCGWH.{u, v} c)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    CurrentFree.adjoint a c K
        (D ≫ eHomWhiskerLeft PointedCGWH.{u, v}
          (ForgetEnrichment.of PointedCGWH.{u, v} a) q) X =
      CurrentFree.adjoint a b K D X ≫ (ihom K).map (indexMap X q) := by
  unfold CurrentFree.adjoint
  rw [action_postcompose, MonoidalClosed.curry_natural_right]

private theorem adjoint_coefficient (a b : A) {S T : PointedCGWH.{u, v}} (c : S ⟶ T)
    (D : T ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    CurrentFree.adjoint a b S (c ≫ D) X =
      CurrentFree.adjoint a b T D X ≫ (MonoidalClosed.pre c).app
        (X.toEnrichedFunctor.obj b) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_pre_app, CurrentFree.adjoint_uncurry,
    CurrentFree.adjoint_uncurry]
  unfold CurrentFree.action
  rw [comp_whiskerRight]
  simp only [Category.assoc]

end Action


/-- The entire ordinary index action is the genuine forgotten enriched functor. -/
def indexValueFunctor {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    ForgetEnrichment PointedCGWH.{u, v} A ⥤ PointedCGWH.{u, v} :=
  X.toEnrichedFunctor.forget ⋙ ForgetEnrichment.equivFunctor PointedCGWH.{u, v} PointedCGWH.{u, v}

/-- Each complete native index map agrees with that actual ordinary functor map. -/
theorem indexValueFunctor_map {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) {b c : A}
    (q : ForgetEnrichment.of PointedCGWH.{u, v} b ⟶
      ForgetEnrichment.of PointedCGWH.{u, v} c) :
    (indexValueFunctor X).map q = indexMap X q := rfl

/-- A genuine index isomorphism induces a genuine value isomorphism of the full functor. -/
def indexValueIso {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) {b c : A}
    (e : ForgetEnrichment.of PointedCGWH.{u, v} b ≅
      ForgetEnrichment.of PointedCGWH.{u, v} c) :
    X.toEnrichedFunctor.obj b ≅ X.toEnrichedFunctor.obj c :=
  (indexValueFunctor X).mapIso e

/-- The forward value isomorphism uses the actual forward index map. -/
theorem indexValueIso_hom {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) {b c : A}
    (e : ForgetEnrichment.of PointedCGWH.{u, v} b ≅
      ForgetEnrichment.of PointedCGWH.{u, v} c) :
    (indexValueIso X e).hom = indexMap X e.hom := rfl

/-- The inverse value isomorphism uses the original inverse index map. -/
theorem indexValueIso_inv {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) {b c : A}
    (e : ForgetEnrichment.of PointedCGWH.{u, v} b ≅
      ForgetEnrichment.of PointedCGWH.{u, v} c) :
    (indexValueIso X e).inv = indexMap X e.inv := rfl

/-- Precomposition by a coefficient isomorphism keeps both actual complete internal Hom maps. -/
def coefficientPreIso {S T : PointedCGWH.{u, v}} (e : S ≅ T) (Y : PointedCGWH.{u, v}) :
    (ihom T).obj Y ≅ (ihom S).obj Y where
  hom := (MonoidalClosed.pre e.hom).app Y
  inv := (MonoidalClosed.pre e.inv).app Y
  hom_inv_id := by
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, e.inv_hom_id,
      MonoidalClosed.pre_id, NatTrans.id_app]
  inv_hom_id := by
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, e.hom_inv_id,
      MonoidalClosed.pre_id, NatTrans.id_app]

/-- The full restriction transpose is transported by derived coefficient and target-index maps. -/
theorem restriction_adjoint_comparison {A B : Type}
    [EnrichedCategory PointedCGWH.{u, v} A] [EnrichedCategory PointedCGWH.{u, v} B]
    (j : EnrichedFunctor PointedCGWH.{u, v} A B) (a b : A) (c : B)
    {S T : PointedCGWH.{u, v}} (e : S ≅ T)
    (q : ForgetEnrichment.of PointedCGWH.{u, v} c ≅
      ForgetEnrichment.of PointedCGWH.{u, v} (j.obj b))
    (D : S ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    (E : T ⟶ (j.obj a ⟶[PointedCGWH.{u, v}] c))
    (h : D ≫ j.map a b = e.hom ≫ E ≫ eHomWhiskerLeft PointedCGWH.{u, v}
      (ForgetEnrichment.of PointedCGWH.{u, v} (j.obj a)) q.hom)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} B) :
    CurrentFree.adjoint a b S D ((restriction j).obj X) =
      CurrentFree.adjoint (j.obj a) c T E X ≫
        (ihom T).map (indexMap X q.hom) ≫
          (coefficientPreIso e (X.toEnrichedFunctor.obj (j.obj b))).hom := by
  let P : T ⟶ (j.obj a ⟶[PointedCGWH.{u, v}] j.obj b) :=
    E ≫ eHomWhiskerLeft PointedCGWH.{u, v}
      (ForgetEnrichment.of PointedCGWH.{u, v} (j.obj a)) q.hom
  have hD : D ≫ j.map a b = e.hom ≫ P := h
  have hr := restriction_adjoint j a b S D X
  have hd := congrArg
    (fun d : S ⟶ (j.obj a ⟶[PointedCGWH.{u, v}] j.obj b) =>
      CurrentFree.adjoint (j.obj a) (j.obj b) S d X) hD
  have hc := adjoint_coefficient (j.obj a) (j.obj b) e.hom P X
  have ht := adjoint_postcompose (j.obj a) c (j.obj b) T E q.hom X
  exact hr.trans (hd.trans (hc.trans
    ((congrArg (fun d => d ≫ (MonoidalClosed.pre e.hom).app
        (X.toEnrichedFunctor.obj (j.obj b))) ht).trans (Category.assoc _ _ _))))

private theorem coefficient_postcompose {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
    (a b c : A) (S : PointedCGWH.{u, v}) (D : S ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    (q : ForgetEnrichment.of PointedCGWH.{u, v} b ⟶
      ForgetEnrichment.of PointedCGWH.{u, v} c) :
    (ρ_ S).inv ≫ (D ⊗ₘ ForgetEnrichment.homTo PointedCGWH.{u, v} q) ≫
        eComp PointedCGWH.{u, v} a b c =
      D ≫ eHomWhiskerLeft PointedCGWH.{u, v} (ForgetEnrichment.of PointedCGWH.{u, v} a) q := by
  change _ = D ≫ (ρ_ (a ⟶[PointedCGWH.{u, v}] b)).inv ≫
    (a ⟶[PointedCGWH.{u, v}] b) ◁ ForgetEnrichment.homTo PointedCGWH.{u, v} q ≫
      eComp PointedCGWH.{u, v} a b c
  rw [rightUnitor_inv_naturality_assoc]
  simp only [tensorHom_def, Category.assoc]

private theorem generator_coefficient (a n k : I) (f : a ⊗ n ⟶ k) :
    PointedCGWH.SymmetricModulePresentation.operatorGenerator.{u, v} a n k f =
    Enriched.SphereOperator.coefficientHom
      (PointedCGWH.copowerUnderlyingMonoidalData.{u, v, 0} I)
      PointedCGWH.sphereCopowerEnrichedFunctor.{u, v}
      ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj n)
      ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj k)
      ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj a)
      ((PointedCGWH.copowerRestriction.{u, v, 0} I).map f) := by
  rfl

/-- The actual tensor-unit index point of the native symmetric operator category. -/
def symmetricIndexPoint (n k : I) (g : n ⟶ k) :
    𝟙_ PointedCGWH.{u, v} ⟶ (PointedCGWH.symmetricOperatorObj.{u, v} n ⟶[PointedCGWH.{u, v}]
      PointedCGWH.symmetricOperatorObj.{u, v} k) :=
  eHomEquiv PointedCGWH.{u, v}
      ((PointedCGWH.copowerRestriction.{u, v, 0} I).map g) ≫
    Enriched.SphereOperator.indexHom (PointedCGWH.copowerUnderlyingMonoidalData.{u, v, 0} I)
      PointedCGWH.sphereCopowerEnrichedFunctor.{u, v} PointedCGWH.sphereCopowerLaxData.{u, v}
      ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj n)
      ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj k)

private theorem nativeComposition (n k l : I) :
    eComp PointedCGWH.{u, v} (PointedCGWH.symmetricOperatorObj n)
        (PointedCGWH.symmetricOperatorObj k) (PointedCGWH.symmetricOperatorObj l) =
    Enriched.SphereOperator.composition
      (PointedCGWH.copowerUnderlyingMonoidalData.{u, v, 0} I)
      PointedCGWH.sphereCopowerEnrichedFunctor.{u, v} PointedCGWH.sphereCopowerLaxData.{u, v}
      ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj n)
      ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj k)
      ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj l) := rfl

/-- Entire coefficient generators postcompose by the genuine native index action. -/
theorem generator_postcomposition (a n k l : I) (f : a ⊗ n ⟶ k) (g : k ⟶ l) :
    (ρ_ (PointedCGWH.sphereSequence.{u, v}.functor.obj a)).inv ≫
      (PointedCGWH.SymmetricModulePresentation.operatorGenerator a n k f ⊗ₘ
        symmetricIndexPoint k l g) ≫
      eComp PointedCGWH.{u, v} (PointedCGWH.symmetricOperatorObj n)
        (PointedCGWH.symmetricOperatorObj k) (PointedCGWH.symmetricOperatorObj l) =
    PointedCGWH.SymmetricModulePresentation.operatorGenerator a n l (f ≫ g) := by
  let R := PointedCGWH.copowerRestriction.{u, v, 0} I
  let d := PointedCGWH.copowerUnderlyingMonoidalData.{u, v, 0} I
  let S := PointedCGWH.sphereCopowerEnrichedFunctor.{u, v}
  let L := PointedCGWH.sphereCopowerLaxData.{u, v}
  let C := PointedCGWH.sphereSequence.{u, v}.functor.obj a
  let H := PointedCGWH.symmetricOperatorObj.{u, v} n ⟶[PointedCGWH.{u, v}]
    PointedCGWH.symmetricOperatorObj.{u, v} k
  let H' := PointedCGWH.symmetricOperatorObj.{u, v} k ⟶[PointedCGWH.{u, v}]
    PointedCGWH.symmetricOperatorObj.{u, v} l
  let H'' := PointedCGWH.symmetricOperatorObj.{u, v} n ⟶[PointedCGWH.{u, v}]
    PointedCGWH.symmetricOperatorObj.{u, v} l
  let gf : C ⟶ H := PointedCGWH.SymmetricModulePresentation.operatorGenerator a n k f
  let g'f : C ⟶ H := Enriched.SphereOperator.coefficientHom d S
    (R.obj n) (R.obj k) (R.obj a) (R.map f)
  let pg : 𝟙_ PointedCGWH.{u, v} ⟶ H' := symmetricIndexPoint k l g
  let cp : H ⊗ H' ⟶ H'' := Enriched.SphereOperator.composition d S L
    (R.obj n) (R.obj k) (R.obj l)
  have hg : gf = g'f := generator_coefficient a n k f
  have h := Enriched.SphereOperator.coefficientHom_postcompose d S L
    (R.obj n) (R.obj k) (R.obj l) (R.obj a) (R.map f) (R.map g)
  have hf : Enriched.SphereOperator.coefficientHom d S (R.obj n) (R.obj l) (R.obj a)
      (R.map f ≫ R.map g) =
      Enriched.SphereOperator.coefficientHom d S (R.obj n) (R.obj l) (R.obj a) (R.map (f ≫ g)) :=
    congrArg
      (fun t : R.obj (a ⊗ n) ⟶ R.obj l =>
        Enriched.SphereOperator.coefficientHom d S (R.obj n) (R.obj l) (R.obj a) t)
      (R.map_comp f g).symm
  have h0 : (ρ_ C).inv ≫ (g'f ⊗ₘ pg) ≫ cp =
      Enriched.SphereOperator.coefficientHom d S (R.obj n) (R.obj l) (R.obj a)
        (R.map (f ≫ g)) := h.trans hf
  exact (congrArg (fun c : H ⊗ H' ⟶ H'' => (ρ_ C).inv ≫ (gf ⊗ₘ pg) ≫ c)
      (nativeComposition n k l)).trans
    ((congrArg (fun f : C ⟶ H => (ρ_ C).inv ≫ (f ⊗ₘ pg) ≫ cp) hg).trans
      (h0.trans (generator_coefficient a n l (f ≫ g)).symm))

/-- The actual native operator isomorphism induced by an original finite-index isomorphism. -/
def symmetricIndexIso {n k : I} (e : n ≅ k) :
    ForgetEnrichment.of PointedCGWH.{u, v} (PointedCGWH.symmetricOperatorObj.{u, v} n) ≅
      ForgetEnrichment.of PointedCGWH.{u, v} (PointedCGWH.symmetricOperatorObj.{u, v} k) := by
  let R := PointedCGWH.copowerRestriction.{u, v, 0} I
  let d := PointedCGWH.copowerUnderlyingMonoidalData.{u, v, 0} I
  let S := PointedCGWH.sphereCopowerEnrichedFunctor.{u, v}
  let L := PointedCGWH.sphereCopowerLaxData.{u, v}
  let G := ForgetEnrichment.equivInverse PointedCGWH.{u, v}
    (PointedCGWH.CopowerUnderlying.{u, v, 0} I) ⋙
      (Enriched.SphereOperator.indexUnitFunctor d S L).forget
  exact G.mapIso (R.mapIso e)

/-- The forward index point is obtained from the original finite-index map. -/
theorem symmetricIndexIso_hom {n k : I} (e : n ≅ k) :
    ForgetEnrichment.homTo PointedCGWH.{u, v} (symmetricIndexIso.{u, v} e).hom =
      symmetricIndexPoint n k e.hom := by
  rfl

/-- The inverse index point retains the inverse original finite-index map. -/
theorem symmetricIndexIso_inv {n k : I} (e : n ≅ k) :
    ForgetEnrichment.homTo PointedCGWH.{u, v} (symmetricIndexIso.{u, v} e).inv =
      symmetricIndexPoint k n e.inv := by
  rfl

/-- The actual finite index of a natural-number degree. -/
abbrev finiteIndex (n : ℕ) : I := ⟨FintypeCat.Skeleton.mk n⟩

/-- The inverse original block braid followed by the original successor-degree cast. -/
def successorTargetPermutation (n : ℕ) : finiteIndex n ⊗ finiteIndex 1 ≅ finiteIndex (n + 1) :=
  (β_ (finiteIndex 1) (finiteIndex n)).symm ≪≫
    eqToIso (show finiteIndex 1 ⊗ finiteIndex n = finiteIndex (n + 1) from
      congrArg finiteIndex (Nat.add_comm 1 n))

private theorem successorTargetPermutation_factor (n : ℕ) :
    (β_ (finiteIndex 1) (finiteIndex n)).hom ≫ (successorTargetPermutation n).hom =
      eqToHom (show finiteIndex 1 ⊗ finiteIndex n = finiteIndex (n + 1) from
        congrArg finiteIndex (Nat.add_comm 1 n)) := by
  exact Iso.hom_inv_id_assoc (β_ (finiteIndex 1) (finiteIndex n)) _

/-- The original sequential successor inclusion, with its coefficient unitor
and target permutation. -/
theorem sequential_inclusion (n : ℕ) :
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso
      PointedCGWH.sphereOne.{u, v} n).inv ≫
      CategoryTheory.Spectra.SpectrumIndexMaps.sequentialSymmetricOperatorHomMap.{u, v}
        (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne n)
        (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne (n + 1)) =
    (λ_ PointedCGWH.sphereOne.{u, v}).inv ≫
      (ρ_ (PointedCGWH.sphereSequence.{u, v}.functor.obj (finiteIndex 1))).inv ≫
      (HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.symmetricNu
        (finiteIndex n) (finiteIndex 1) ⊗ₘ
          symmetricIndexPoint (finiteIndex n ⊗ finiteIndex 1) (finiteIndex (n + 1))
            (successorTargetPermutation n).hom) ≫
      eComp PointedCGWH.{u, v} (PointedCGWH.symmetricOperatorObj (finiteIndex n))
        (PointedCGWH.symmetricOperatorObj (finiteIndex n ⊗ finiteIndex 1))
        (PointedCGWH.symmetricOperatorObj (finiteIndex (n + 1))) := by
  let N := finiteIndex n
  let A := finiteIndex 1
  let K := finiteIndex (n + 1)
  let T := N ⊗ A
  let S := PointedCGWH.sphereSequence.{u, v}.functor.obj A
  let H := PointedCGWH.symmetricOperatorObj.{u, v} N ⟶[PointedCGWH.{u, v}]
    PointedCGWH.symmetricOperatorObj.{u, v} K
  let p : S ⟶ H := CategoryTheory.Spectra.SpectrumIndexMaps.orderedSymmetricOperatorHom
    n (n + 1) 1 (Nat.add_comm 1 n)
  let q : S ⟶ H := (ρ_ S).inv ≫
    (PointedCGWH.SymmetricModulePresentation.operatorGenerator A N T (β_ A N).hom ⊗ₘ
      symmetricIndexPoint T K (successorTargetPermutation n).hom) ≫
      eComp PointedCGWH.{u, v} (PointedCGWH.symmetricOperatorObj N)
        (PointedCGWH.symmetricOperatorObj T) (PointedCGWH.symmetricOperatorObj K)
  have hp : q = p :=
    (generator_postcomposition A N T K (β_ A N).hom (successorTargetPermutation n).hom).trans
      (congrArg (fun f : A ⊗ N ⟶ K =>
        PointedCGWH.SymmetricModulePresentation.operatorGenerator A N K f)
        (successorTargetPermutation_factor n))
  have hs :=
    CategoryTheory.Spectra.SpectrumIndexMaps.sequentialSymmetricOperatorHomMap_successor.{u, v} n
  exact hs.trans (congrArg (fun f : S ⟶ H => (λ_ PointedCGWH.sphereOne.{u, v}).inv ≫ f) hp.symm)


/-- The actual finite index corresponding to the original sequential degree. -/
abbrev symmetricDegree (n : ℕ) := PointedCGWH.symmetricOperatorObj.{u, v} (finiteIndex n)

/-- The original sequential degree, with its native enriched Hom. -/
abbrev sequentialDegree (n : ℕ) :=
  CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne.{u, v} n

/-- The original circle is compared to the original degree-one power by the left unitor. -/
def circleToPowerOneIso : PointedCGWH.sphereOne.{u, v} ≅
    PointedCGWH.sphereSequence.{u, v}.functor.obj (finiteIndex 1) :=
  (λ_ PointedCGWH.sphereOne.{u, v}).symm

/-- The genuine target operator isomorphism retains the actual inverse block permutation. -/
def successorIndexIso (n : ℕ) := symmetricIndexIso.{u, v} (successorTargetPermutation n)

/-- Every native spectrum acts on that entire genuine target index isomorphism. -/
def successorValueIso (X : Actual.SymmetricCarrier.{u, v}) (n : ℕ) :=
  indexValueIso X (successorIndexIso n)

/-- The original inclusion factors through the actual coefficient and target isomorphisms. -/
theorem sequential_inclusion_factor (n : ℕ) :
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso
      PointedCGWH.sphereOne.{u, v} n).inv ≫
        sequentialSymmetricOperatorHomMap.{u, v} (sequentialDegree n) (sequentialDegree (n + 1)) =
      circleToPowerOneIso.hom ≫ Actual.symmetricNu.{u, v} (finiteIndex n) (finiteIndex 1) ≫
        eHomWhiskerLeft PointedCGWH.{u, v}
          (ForgetEnrichment.of PointedCGWH.{u, v} (symmetricDegree n))
          (successorIndexIso n).hom := by
  have h := coefficient_postcompose (symmetricDegree n)
    (PointedCGWH.symmetricOperatorObj.{u, v} (finiteIndex n ⊗ finiteIndex 1))
    (symmetricDegree (n + 1))
    (PointedCGWH.sphereSequence.{u, v}.functor.obj (finiteIndex 1))
    (Actual.symmetricNu.{u, v} (finiteIndex n) (finiteIndex 1)) (successorIndexIso n).hom
  exact (sequential_inclusion n).trans
    (congrArg (fun f => circleToPowerOneIso.hom ≫ f) h)

/-- The adjoint target comparison contains the real target permutation and coefficient unitor. -/
def oneStepComparisonIso (X : Actual.SymmetricCarrier.{u, v}) (n : ℕ) :
    (ihom (PointedCGWH.sphereSequence.{u, v}.functor.obj (finiteIndex 1))).obj
      (X.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v}
        (finiteIndex n ⊗ finiteIndex 1))) ≅
    (ihom PointedCGWH.sphereOne.{u, v}).obj
      (X.toEnrichedFunctor.obj (symmetricDegree (n + 1))) :=
  (ihom (PointedCGWH.sphereSequence.{u, v}.functor.obj (finiteIndex 1))).mapIso
    (successorValueIso X n) ≪≫
      coefficientPreIso circleToPowerOneIso (X.toEnrichedFunctor.obj (symmetricDegree (n + 1)))

/-- The original sequential family transpose, with its complete source Hom exposed. -/
abbrev sequentialAdjoint (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    X.toEnrichedFunctor.obj (sequentialDegree n) ⟶
      (ihom PointedCGWH.sphereOne.{u, v}).obj
        (X.toEnrichedFunctor.obj (sequentialDegree (n + 1))) :=
  CurrentFree.adjoint (sequentialDegree n) (sequentialDegree (n + 1)) PointedCGWH.sphereOne
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso
      PointedCGWH.sphereOne n).inv X

/-- The unchanged symmetric family transpose at every complete original block label. -/
abbrev symmetricAdjoint (X : Actual.SymmetricCarrier.{u, v}) (n a : I) :
    X.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj n) ⟶
      (ihom (PointedCGWH.sphereSequence.{u, v}.functor.obj a)).obj
        (X.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj (n ⊗ a))) :=
  CurrentFree.adjoint (PointedCGWH.symmetricOperatorObj n)
    (PointedCGWH.symmetricOperatorObj (n ⊗ a))
    (PointedCGWH.sphereSequence.{u, v}.functor.obj a) (Actual.symmetricNu n a) X

/-- Every raw sequential transpose is the unchanged original native family value. -/
theorem sequentialAdjoint_eq_native (X : PointedCGWH.SequentialSpectrum.{u, v}) (n : ℕ) :
    sequentialAdjoint X n =
      NativeK.adjoint PointedCGWH.SequentialSpectrum.StableK.stabilizationFamily.{u, v} n X := rfl

/-- The raw symmetric transpose is the same unchanged original full-family value. -/
theorem symmetricAdjoint_eq_native (X : Actual.SymmetricCarrier.{u, v}) (n a : I) :
    symmetricAdjoint X n a = NativeK.adjoint Actual.symmetricFamily.{u, v} (n, a) X := rfl

/-- Every original sequential transpose restricts through the complete actual Hom map. -/
theorem sequentialSymmetric_adjoint (n : ℕ) (X : Actual.SymmetricCarrier.{u, v}) :
    sequentialAdjoint ((restriction sequentialSymmetricOperatorIndexFunctor.{u, v}).obj X) n =
      symmetricAdjoint X (finiteIndex n) (finiteIndex 1) ≫
        (oneStepComparisonIso X n).hom := by
  exact restriction_adjoint_comparison sequentialSymmetricOperatorIndexFunctor
    (sequentialDegree n) (sequentialDegree (n + 1))
    (PointedCGWH.symmetricOperatorObj.{u, v} (finiteIndex n ⊗ finiteIndex 1))
    circleToPowerOneIso (successorIndexIso n)
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso
      PointedCGWH.sphereOne n).inv
    (Actual.symmetricNu (finiteIndex n) (finiteIndex 1)) (sequential_inclusion_factor n) X

/-- Each original one-step weak test is transported by the complete actual target isomorphism. -/
theorem sequentialSymmetric_weak_adjoint_iff (n : ℕ) (X : Actual.SymmetricCarrier.{u, v}) :
    weakEquivalences PointedCGWH.{u, v}
      (NativeK.adjoint PointedCGWH.SequentialSpectrum.StableK.stabilizationFamily.{u, v} n
        ((restriction sequentialSymmetricOperatorIndexFunctor.{u, v}).obj X)) ↔
    weakEquivalences PointedCGWH.{u, v}
      (NativeK.adjoint Actual.symmetricFamily.{u, v} (finiteIndex n, finiteIndex 1) X) := by
  let e := oneStepComparisonIso X n
  let _ : IsIso e.hom := e.isIso_hom
  have he : weakEquivalences PointedCGWH.{u, v} e.hom :=
    (weakEquivalences PointedCGWH.{u, v}).of_isIso e.hom
  change weakEquivalences PointedCGWH.{u, v}
    (sequentialAdjoint ((restriction sequentialSymmetricOperatorIndexFunctor.{u, v}).obj X) n) ↔ _
  rw [sequentialSymmetric_adjoint]
  constructor
  · intro h
    exact (weakEquivalences PointedCGWH.{u, v}).of_postcomp _ _ he h
  · intro h
    exact (weakEquivalences PointedCGWH.{u, v}).comp_mem _ _ h he

/-- The original native sequential transpose is the original circle structure transpose. -/
theorem sequential_adjoint_eq (n : ℕ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    sequentialAdjoint X n =
      X.adjointStructureMap n := by
  change MonoidalClosed.curry (CurrentFree.action (sequentialDegree n) (sequentialDegree (n + 1))
    PointedCGWH.sphereOne
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHomSuccessorIso
      PointedCGWH.sphereOne n).inv X) =
      MonoidalClosed.curry (CategoryTheory.Spectra.Sequential.structureMap X n)
  congr 1
  unfold CurrentFree.action CategoryTheory.Spectra.Sequential.structureMap
  rw [tensorHom_id]
  rfl

/-- Both original sequential Omega predicates use every unchanged successor map. -/
theorem sequential_isOmega_iff (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    NativeK.IsOmega PointedCGWH.SequentialSpectrum.StableK.stabilizationFamily.{u, v} X ↔
      X.IsOmega := by
  change (∀ n, weakEquivalences PointedCGWH.{u, v} (sequentialAdjoint X n)) ↔
    ∀ n, CGWH.weakHomotopyEquivalences
      (PointedCGWH.SequentialSpectrum.adjointStructureMap X n).right
  apply forall_congr'
  intro n
  rw [sequential_adjoint_eq]
  exact (HomotopicalAlgebra.weakEquivalence_iff _).symm.trans
    ((PointedCGWH.weakEquivalence_iff _).trans (CGWH.modelCategory.weakEquivalence_iff _))

/-- Source forgetting identifies all sequential Omega tests with the original symmetric
one-step tests. -/
theorem sequentialSymmetric_isOmega_iff_oneStep (X : Actual.SymmetricCarrier.{u, v}) :
    PointedCGWH.SequentialSpectrum.IsOmega
      ((restriction sequentialSymmetricOperatorIndexFunctor.{u, v}).obj X) ↔
      ∀ n : ℕ, weakEquivalences PointedCGWH.{u, v}
        (NativeK.adjoint Actual.symmetricFamily.{u, v} (finiteIndex n, finiteIndex 1) X) := by
  rw [← sequential_isOmega_iff]
  exact forall_congr' (fun n => sequentialSymmetric_weak_adjoint_iff n X)

/-- Every original full-family symmetric Omega spectrum forgets to an actual sequential
Omega spectrum. -/
theorem sequentialSymmetric_isOmega_of_isOmega (X : Actual.SymmetricCarrier.{u, v})
    (hX : NativeK.IsOmega Actual.symmetricFamily.{u, v} X) :
    PointedCGWH.SequentialSpectrum.IsOmega
      ((restriction sequentialSymmetricOperatorIndexFunctor.{u, v}).obj X) :=
  (sequentialSymmetric_isOmega_iff_oneStep X).mpr (fun n => hX (finiteIndex n, finiteIndex 1))

end HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport.Sequential
