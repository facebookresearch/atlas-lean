/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FreeEvaluation
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FreeComponents
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FreeComponentsBelow
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FreeComponentsDiagonal
import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Original block-quotient levels of the canonical native free spectra

The native free/evaluation pair retains the actual original Day component
isomorphisms. These formulas cover all degree comparisons, the original
complement normalization and each coefficient arrow. Both ends of every free
arrow are compared by the same level isomorphisms.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.Operad.SmallFinBijGroupoid
open scoped MonoidalClosed CategoryTheory.MonObj

namespace PointedCGWH.SymmetricSpectrum

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal sphereSequenceMonObj
  sphereSequenceIsCommMonObj

/-- Native evaluation of the source module presentation keeps its literal level. -/
def moduleEvaluationComparison (n : I) :
    toModule.{u, v} ⋙ Mod.dayEvaluation sphereSequence.{u, v} n ≅ evaluation n :=
  NatIso.ofComponents (fun F => Iso.refl (F.X.functor.obj n)) (by
    intro F G f
    change (toModule.map f).hom.natTrans.app n ≫ 𝟙 _ =
      𝟙 _ ≫ EnrichedFunctorCat.component f (symmetricOperatorObj.{u, v} n)
    have h := (congrArg (fun z => z.natTrans.app n) (toModule_hom f)).trans (hom_app f n)
    exact (Category.comp_id _).trans (h.trans (Category.id_comp _).symm))

/-- The entire original Day free/evaluation functor identifies the native evaluated free. -/
def originalFreeLevelComparison (r n : I) :
    Mod.dayFreeAt sphereSequence.{u, v} r ⋙ Mod.dayEvaluation sphereSequence.{u, v} n ≅
      freeAt r ⋙ evaluation n :=
  Functor.isoWhiskerRight (freeModuleComparison r) (Mod.dayEvaluation sphereSequence.{u, v} n) ≪≫
    Functor.associator (freeAt r) toModule (Mod.dayEvaluation sphereSequence.{u, v} n) ≪≫
      Functor.isoWhiskerLeft (freeAt r) (moduleEvaluationComparison n)

/-- Its complete forward level map is the actual free-module comparison component. -/
theorem originalFreeLevelComparison_hom (r n : I) (M : V.{u, v}) :
    (originalFreeLevelComparison r n).hom.app M =
      ((freeModuleComparison r).hom.app M).hom.natTrans.app n := by
  change ((freeModuleComparison r).hom.app M).hom.natTrans.app n ≫
    𝟙 _ ≫ 𝟙 _ = _
  rw [Category.comp_id, Category.comp_id]

/-- Its complete inverse level map is the same original inverse free-module component. -/
theorem originalFreeLevelComparison_inv (r n : I) (M : V.{u, v}) :
    (originalFreeLevelComparison r n).inv.app M =
      ((freeModuleComparison r).inv.app M).hom.natTrans.app n := by
  change (𝟙 _ ≫ 𝟙 _) ≫
    ((freeModuleComparison r).inv.app M).hom.natTrans.app n = _
  rw [Category.id_comp, Category.id_comp]

/-- The full native upper-degree free spectrum uses the original balanced smash functor. -/
def freeAtCardBalancedIso {r n : ℕ} (h : r ≤ n) :
    freeAt.{u, v} (card r) ⋙ evaluation (card n) ≅
      nativeCardInducedFunctor sphereSequence.{u, v} h :=
  (originalFreeLevelComparison (card r) (card n)).symm ≪≫
    dayFreeAtCardNativeIso sphereSequence.{u, v} h

/-- The original degree-zero complement gives the same whole native diagonal functor. -/
def freeAtCardDiagonalIso (n : ℕ) :
    freeAt.{u, v} (card n) ⋙ evaluation (card n) ≅
      tensorLeft (basedDiscreteObj.{u, v, 0} (Aut (card n))) :=
  (originalFreeLevelComparison (card n) (card n)).symm ≪≫
    nativeSphereFreeAtCardDiagonalIso n

/-- Below the generating degree, every native free level is initial. -/
def freeAtCardBelowIsInitial {r n : ℕ} (h : n < r) (M : V.{u, v}) :
    IsInitial ((freeAt (card r) ⋙ evaluation (card n)).obj M) :=
  (dayFreeAtCardNativeBelowIso_isInitial sphereSequence.{u, v} h M).ofIso
    ((originalFreeLevelComparison (card r) (card n)).app M)

/-- The native free arrow retains both original balanced coefficient endpoints. -/
def freeAtCardBalancedArrowIso {r n : ℕ} (h : r ≤ n)
    {M N : V.{u, v}} (f : M ⟶ N) :
    Arrow.mk ((evaluation (card n)).map ((freeAt (card r)).map f)) ≅
      Arrow.mk ((nativeCardInducedFunctor sphereSequence.{u, v} h).map f) :=
  Arrow.isoOfNatIso (freeAtCardBalancedIso h) (Arrow.mk f)

/-- Every isomorphism-invariant evaluated class retains the original whole balanced free arrow. -/
theorem freeAtCardBalanced_property_iff (P : MorphismProperty V.{u, v}) [P.RespectsIso]
    {r n : ℕ} (h : r ≤ n) {M N : V.{u, v}} (f : M ⟶ N) :
    P ((evaluation (card n)).map ((freeAt (card r)).map f)) ↔
      P ((nativeCardInducedFunctor sphereSequence.{u, v} h).map f) :=
  P.arrow_mk_iso_iff (freeAtCardBalancedArrowIso h f)

/-- All diagonal coefficient arrows retain their actual discrete smash arrow. -/
def freeAtCardDiagonalArrowIso (n : ℕ) {M N : V.{u, v}} (f : M ⟶ N) :
    Arrow.mk ((evaluation (card n)).map ((freeAt (card n)).map f)) ≅
      Arrow.mk (basedDiscreteObj.{u, v, 0} (Aut (card n)) ◁ f) :=
  Arrow.isoOfNatIso (freeAtCardDiagonalIso n) (Arrow.mk f)

/-- Upper-degree coefficient arrows keep both of the actual source/target comparison maps. -/
theorem freeAtCardBalanced_naturality {r n : ℕ} (h : r ≤ n)
    {M N : V.{u, v}} (f : M ⟶ N) :
    (hom ((freeAt (card r)).map f)).natTrans.app (card n) ≫
        (freeAtCardBalancedIso h).hom.app N =
      (freeAtCardBalancedIso h).hom.app M ≫
        (nativeCardInducedFunctor sphereSequence.{u, v} h).map f := by
  rw [← evaluation_map]
  exact (freeAtCardBalancedIso h).hom.naturality f

/-- Both complete inverse level maps keep the same original coefficient square. -/
theorem freeAtCardBalanced_inv_naturality {r n : ℕ} (h : r ≤ n)
    {M N : V.{u, v}} (f : M ⟶ N) :
    (nativeCardInducedFunctor sphereSequence.{u, v} h).map f ≫
        (freeAtCardBalancedIso h).inv.app N =
      (freeAtCardBalancedIso h).inv.app M ≫
        (hom ((freeAt (card r)).map f)).natTrans.app (card n) := by
  rw [← evaluation_map]
  exact (freeAtCardBalancedIso h).inv.naturality f

/-- Every original permutation is retained by the entire source/native free comparison. -/
theorem originalFreeLevelComparison_permutation (r : I) (M : V.{u, v})
    {n k : I} (g : n ⟶ k) :
    ((Mod.dayFreeAt sphereSequence.{u, v} r).obj M).X.functor.map g ≫
        (originalFreeLevelComparison r k).hom.app M =
      (originalFreeLevelComparison r n).hom.app M ≫ ((freeAt r).obj M).X.functor.map g := by
  rw [originalFreeLevelComparison_hom, originalFreeLevelComparison_hom]
  exact ((freeModuleComparison r).hom.app M).hom.natTrans.naturality g

/-- The complete inverse source/native comparison retains that same permutation square. -/
theorem originalFreeLevelComparison_inv_permutation (r : I) (M : V.{u, v})
    {n k : I} (g : n ⟶ k) :
    ((freeAt r).obj M).X.functor.map g ≫
        (originalFreeLevelComparison r k).inv.app M =
      (originalFreeLevelComparison r n).inv.app M ≫
        ((Mod.dayFreeAt sphereSequence.{u, v} r).obj M).X.functor.map g := by
  rw [originalFreeLevelComparison_inv, originalFreeLevelComparison_inv]
  exact ((freeModuleComparison r).inv.app M).hom.natTrans.naturality g

/-- The entire original Day free block generator, before native carrier comparison. -/
def originalFreeAtCardBlockGenerator {r n : ℕ} (M : V.{u, v})
    (d : BlockDecomposition (card r) (card n)) :
    sphereSequence.{u, v}.functor.obj d.left ⊗ M ⟶
      ((Mod.dayFreeAt sphereSequence.{u, v} (card r)).obj M).X.functor.obj (card n) :=
  let G := (DayFunctor.equiv I V.{u, v}).symm.functor.obj
    ((evaluationLeftAdjoint V.{u, v} (card r)).obj M)
  (𝟙 (sphereSequence.{u, v}.functor.obj d.left) ⊗ₘ
      Sigma.ι (fun _ : card r ⟶ card r => M) (𝟙 (card r))) ≫
    (DayFunctor.η sphereSequence.{u, v} G).app (d.left, card r) ≫
    (sphereSequence.{u, v} ⊗ G).functor.map d.hom ≫
    (eqToHom (Mod.free_obj sphereSequence.{u, v} G).symm).natTrans.app (card n)

/-- Every complete original block generator has its native free-spectrum source leg. -/
def freeAtCardBlockGenerator {r n : ℕ} (M : V.{u, v})
    (d : BlockDecomposition (card r) (card n)) :
    sphereSequence.{u, v}.functor.obj d.left ⊗ M ⟶
      ((freeAt (card r)).obj M).X.functor.obj (card n) :=
  originalFreeAtCardBlockGenerator M d ≫
    (originalFreeLevelComparison (card r) (card n)).hom.app M

private theorem generatorComparison_cancel {C : Type*} [Category C]
    {W X Y Z : C} (g : W ⟶ X) (e : X ≅ Y) (h : X ⟶ Z) :
    (g ≫ e.hom) ≫ (e.inv ≫ h) = g ≫ h := by
  rw [Category.assoc, e.hom_inv_id_assoc]

/-- The native free block generator retains the original complement isomorphism and quotient leg. -/
theorem freeAtCardBlockGenerator_balanced {r n : ℕ} (h : r ≤ n) (M : V.{u, v})
    (d : BlockDecomposition (card r) (card n)) :
    freeAtCardBlockGenerator M d ≫ (freeAtCardBalancedIso h).hom.app M =
      (sphereSequence.{u, v}.functor.map (cardComplementIso h d).inv ⊗ₘ 𝟙 M) ≫
        nativeBalancedGenerator.{u, v, 0, 0}
          (Aut (card (n - r))) (Aut (card n))
          (sphereSequence.{u, v}.functor.obj (card (n - r)) ⊗ M)
          (blockCoefficientAction sphereSequence.{u, v} (card (n - r)) M)
          (blockAutHom (card (n - r)) (card r) (card n)
            (cardBlockSumIso (Nat.sub_add_cancel h)))
          (blockIsoEquivAut (card (n - r)) (card r) (card n)
            (cardBlockSumIso (Nat.sub_add_cancel h)) (cardNormalizedBlock h d)) := by
  let gen := originalFreeAtCardBlockGenerator M d
  let e := (originalFreeLevelComparison (card r) (card n)).app M
  let b := (dayFreeAtCardNativeIso sphereSequence.{u, v} h).hom.app M
  have hc := generatorComparison_cancel gen e b
  have hOld := dayFreeAtCardNativeIso_generator sphereSequence.{u, v} h M d
  change gen ≫ b = _ at hOld
  change (gen ≫ e.hom) ≫ (e.inv ≫ b) = _
  exact hc.trans hOld

end PointedCGWH.SymmetricSpectrum
