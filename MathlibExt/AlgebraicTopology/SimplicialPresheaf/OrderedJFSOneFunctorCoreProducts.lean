/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OrderedJFSOneFunctorNativeCore
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.CoreProductComparison
import MathlibExt.AlgebraicTopology.ModelCategory.IsFibrant
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Product compatibility of original one-fold functor cores

The full functor-object right adjoint preserves the original binary product.
The actual core's R comparison is weak on genuine local targets. Their
composite is the core functor's original product comparison, with both
original projections and its original replacement-unit square.
-/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped SSet.modelCategoryQuillen
open SimplicialPresheaf.InjectiveKan SimplicialPresheaf.OriginalLocalDerived

namespace SimplicialPresheaf.OrderedJFS.OneFunctor.Core

private local instance sourceLocallySmall : LocallySmall.{u} (FinitePowerSite.Source 1) :=
  @CategoryTheory.locallySmall_of_univLE _ _ UnivLE.zero

/-- The actual core preserves the full functor object's binary products up to scalar weakness. -/
theorem coreProduct_weak (A Z V : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z) (hV : isOriginalLocalFibrant family.{u} V) :
    SSet.realizationWeakEquivalences (prodComparison (coreFunctor A) Z V) := by
  let _ : PreservesLimits (objectFunctor A) := (adjunction A).rightAdjoint_preservesLimits
  change SSet.realizationWeakEquivalences
    (prodComparison (objectFunctor A ⋙ TransferredCoreReplacements.rReplacement family.{u}
      (ConstantEvaluation.zeroTuple 1)) Z V)
  rw [prodComparison_comp]
  exact SSet.realizationWeakEquivalences.comp_mem _ _
    (SSet.realizationWeakEquivalences.of_isIso
      ((TransferredCoreReplacements.rReplacement family.{u} (ConstantEvaluation.zeroTuple 1)).map
        (prodComparison (objectFunctor A) Z V)))
    (SimplicialPresheaf.CoreProducts.coreComparison_weak family.{u}
      (ConstantEvaluation.zeroTuple 1) (object A Z) (object A V)
      (object_localFibrant A Z hZ) (object_localFibrant A V hV))

/-- The original first product projection is evaluated through the same core functor. -/
@[reassoc] theorem coreProduct_fst (A Z V : Original.{u} 1) :
    prodComparison (coreFunctor A) Z V ≫ prod.fst =
      (coreFunctor A).map (prod.fst : Z ⨯ V ⟶ Z) :=
  prodComparison_fst _ _ _

/-- The original second product projection retains the other target component. -/
@[reassoc] theorem coreProduct_snd (A Z V : Original.{u} 1) :
    prodComparison (coreFunctor A) Z V ≫ prod.snd =
      (coreFunctor A).map (prod.snd : Z ⨯ V ⟶ V) :=
  prodComparison_snd _ _ _

/-- The product comparison retains the original evaluated R-units and full target product. -/
theorem coreProduct_unit (A Z V : Original.{u} 1) :
    (coreUnit A).app (Z ⨯ V) ≫ prodComparison (coreFunctor A) Z V =
      prodComparison (rawCoreFunctor A) Z V ≫
        prod.map ((coreUnit A).app Z) ((coreUnit A).app V) :=
  prodComparison_natural_of_natTrans (coreUnit A)

/-- Product comparisons are natural on the same original two target maps. -/
theorem coreProduct_natural (A : Original.{u} 1) {Z V Z' V' : Original.{u} 1}
    (f : Z ⟶ Z') (g : V ⟶ V') :
    (coreFunctor A).map (prod.map f g) ≫ prodComparison (coreFunctor A) Z' V' =
      prodComparison (coreFunctor A) Z V ≫
        prod.map ((coreFunctor A).map f) ((coreFunctor A).map g) :=
  prodComparison_natural (coreFunctor A) f g

/-- The first genuine product projection has the same localized derived-end interpretation. -/
theorem mappingIso_product_fst (A Z V : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z) (hV : isOriginalLocalFibrant family.{u} V) :
    scalarHo.map ((coreFunctor A).map (prod.fst : Z ⨯ V ⟶ Z)) ≫ (mappingIso A Z hZ).hom =
      (mappingIso A (Z ⨯ V) (SimplicialPresheaf.CoreProducts.product_localFibrant family.{u}
        Z V hZ hV)).hom ≫ scalarHo.map (localDerivedPostcomp family.{u} A prod.fst) :=
  mappingIso_target A (SimplicialPresheaf.CoreProducts.product_localFibrant family.{u}
    Z V hZ hV) hZ prod.fst

/-- The second original product projection retains its corresponding derived-end map. -/
theorem mappingIso_product_snd (A Z V : Original.{u} 1)
    (hZ : isOriginalLocalFibrant family.{u} Z) (hV : isOriginalLocalFibrant family.{u} V) :
    scalarHo.map ((coreFunctor A).map (prod.snd : Z ⨯ V ⟶ V)) ≫ (mappingIso A V hV).hom =
      (mappingIso A (Z ⨯ V) (SimplicialPresheaf.CoreProducts.product_localFibrant family.{u}
        Z V hZ hV)).hom ≫ scalarHo.map (localDerivedPostcomp family.{u} A prod.snd) :=
  mappingIso_target A (SimplicialPresheaf.CoreProducts.product_localFibrant family.{u}
    Z V hZ hV) hV prod.snd

/-- The literal zero core is Kan for a genuinely local target, before the original R is applied. -/
theorem rawCore_isKan (A Z : Original.{u} 1) (hZ : isOriginalLocalFibrant family.{u} Z) :
    SSet.KanComplex ((rawCoreFunctor A).obj Z) :=
  ConstantEvaluation.evaluation_isFibrant family.{u} (ConstantEvaluation.zeroIsTerminal 1)
    (object A Z) (object_localFibrant A Z hZ)

private def emptyProductTerminal (Z : Fin 0 → Original.{u} 1) : IsTerminal (∏ᶜ Z) :=
  IsTerminal.ofUniqueHom (fun _ => Pi.lift fun i => Fin.elim0 i)
    (fun _ _ => by apply Pi.hom_ext; intro i; exact Fin.elim0 i)

/-- Every chosen finite product remains a genuine original-local-fibrant target, including zero factors. -/
theorem finiteProduct_localFibrant (n : ℕ) (Z : Fin n → Original.{u} 1)
    (hZ : ∀ i, isOriginalLocalFibrant family.{u} (Z i)) :
    isOriginalLocalFibrant family.{u} (∏ᶜ Z) := by
  let d := originalLocalSmithData family.{u}
  let _ : ModelCategory (Original.{u} 1) := d.model
  induction n with
  | zero =>
      exact d.isFibrant_iff _ |>.mp (isFibrant_of_iso
        ((emptyProductTerminal Z).uniqueUpToIso terminalIsTerminal).symm
        (d.isFibrant_iff _ |>.mpr (SimplicialPresheaf.CoreProducts.terminal_localFibrant family.{u})))
  | succ n ih =>
      have ht := ih (fun i => Z i.succ) (fun i => hZ i.succ)
      have hp := SimplicialPresheaf.CoreProducts.product_localFibrant family.{u}
        (Z 0) (∏ᶜ (fun i : Fin n => Z i.succ)) (hZ 0) ht
      exact d.isFibrant_iff _ |>.mp (isFibrant_of_iso (Pi.finSuccProductIso n Z).symm
        (d.isFibrant_iff _ |>.mpr hp))

/-- The entire finite comparison retains every original evaluated R-unit. -/
theorem coreFiniteProduct_unit (A : Original.{u} 1) (n : ℕ) (Z : Fin n → Original.{u} 1) :
    (coreUnit A).app (∏ᶜ Z) ≫ piComparison (coreFunctor A) Z =
      piComparison (rawCoreFunctor A) Z ≫ Limits.Pi.map (fun i => (coreUnit A).app (Z i)) := by
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, piComparison_comp_π, Limits.Pi.map_π]
  rw [← Category.assoc, piComparison_comp_π]
  exact ((coreUnit A).naturality (Pi.π Z i)).symm

/-- The actual chosen finite product comparison is weak for arbitrary local factors and value universe. -/
theorem coreFiniteProduct_weak (A : Original.{u} 1) (n : ℕ) (Z : Fin n → Original.{u} 1)
    (hZ : ∀ i, isOriginalLocalFibrant family.{u} (Z i)) :
    SSet.realizationWeakEquivalences (piComparison (coreFunctor A) Z) := by
  let _ : PreservesLimits (objectFunctor A) := (adjunction A).rightAdjoint_preservesLimits
  let _ : ∀ i, SSet.KanComplex ((rawCoreFunctor A).obj (Z i)) := fun i => rawCore_isKan A (Z i) (hZ i)
  let _ : ∀ i, SSet.KanComplex ((coreFunctor A).obj (Z i)) := fun i => core_isKan A (Z i)
  have hPi := SSet.OriginalFiniteKanProducts.realizationWeakEquivalence_finPiMap n
    (fun i => (rawCoreFunctor A).obj (Z i)) (fun i => (coreFunctor A).obj (Z i))
    (fun i => (coreUnit A).app (Z i)) (fun i => coreUnit_weak A (Z i) (hZ i))
  apply SSet.realizationWeakEquivalences.of_precomp _ _
    (coreUnit_weak A (∏ᶜ Z) (finiteProduct_localFibrant n Z hZ))
  rw [coreFiniteProduct_unit]
  exact SSet.realizationWeakEquivalences.comp_mem _ _
    (SSet.realizationWeakEquivalences.of_isIso (piComparison (rawCoreFunctor A) Z)) hPi

/-- Every finite-product projection has its original derived-end interpretation. -/
theorem mappingIso_finiteProduct_π (A : Original.{u} 1) (n : ℕ) (Z : Fin n → Original.{u} 1)
    (hZ : ∀ i, isOriginalLocalFibrant family.{u} (Z i)) (i : Fin n) :
    scalarHo.map ((coreFunctor A).map (Pi.π Z i)) ≫ (mappingIso A (Z i) (hZ i)).hom =
      (mappingIso A (∏ᶜ Z) (finiteProduct_localFibrant n Z hZ)).hom ≫
        scalarHo.map (localDerivedPostcomp family.{u} A (Pi.π Z i)) :=
  mappingIso_target A (finiteProduct_localFibrant n Z hZ) (hZ i) (Pi.π Z i)

/-- The original zero-factor law uses the same actual terminal target and replacement unit. -/
theorem coreTerminal_weak (A : Original.{u} 1) :
    SSet.realizationWeakEquivalences (terminalComparison (coreFunctor A)) := by
  let _ : PreservesLimits (objectFunctor A) := (adjunction A).rightAdjoint_preservesLimits
  apply SSet.realizationWeakEquivalences.of_precomp _ _
    (coreUnit_weak A (⊤_ (Original.{u} 1))
      (SimplicialPresheaf.CoreProducts.terminal_localFibrant family.{u}))
  have h : (coreUnit A).app (⊤_ (Original.{u} 1)) ≫ terminalComparison (coreFunctor A) =
      terminalComparison (rawCoreFunctor A) := terminal.hom_ext _ _
  rw [h]
  exact SSet.realizationWeakEquivalences.of_isIso _

end SimplicialPresheaf.OrderedJFS.OneFunctor.Core
