/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OperatorHomCopower
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorRightTensor
public import MathlibExt.CategoryTheory.Enriched.Limits.SphereOperatorCoendProofFamilies
public import MathlibExt.CategoryTheory.Enriched.CoendCharacteristicEquationTransport
public import MathlibExt.CategoryTheory.Enriched.Limits.SphereOperatorCoendCharacteristic
public import MathlibExt.CategoryTheory.Enriched.CoendGeneratorEquationTransport
public import MathlibExt.CategoryTheory.Functor.ColimitHomFamilyFunctions
public import MathlibExt.CategoryTheory.Functor.ColimitGeneratorSourceTransport
public import MathlibExt.CategoryTheory.Enriched.FunctorFullLawTransport
public import MathlibExt.CategoryTheory.Enriched.FunctorCompositionFieldTransport

/-!
# Actual symmetric operator index shifts and diagram restriction

The original block-label extension and native block-colimit descent agree with
the full weighted-coend shift. Existing enriched-functor fields supply its full
identity and composition proofs. Restriction retains the original operator
objects, complete Hom maps and every diagram component.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Enriched CategoryTheory.Functor
open scoped MonoidalClosed

namespace PointedCGWH

namespace SymmetricShift

open PointedCGWH
open PointedCGWH.SymmetricModulePresentation
open PointedCGWH.SymmetricOperatorHom
open CategoryTheory.Operad.SmallFinBijGroupoid

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

attribute [local instance] PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal
  CategoryTheory.Operad.SmallFinBijGroupoid.instMonoidalCategory
  CategoryTheory.Operad.SmallFinBijGroupoid.instSymmetricCategory

/-- The original full block label is extended by the identity of the final source block. -/
def label (r n k a : I) (f : a ⊗ n ⟶ k) : a ⊗ (n ⊗ r) ⟶ k ⊗ r :=
  (α_ a n r).inv ≫ (f ⊗ₘ 𝟙 r)

/-- Every coefficient map preserves the complete original shifted block label. -/
theorem label_coefficient (r n k : I) {a b : I} (p : a ⟶ b) (f : b ⊗ n ⟶ k) :
    (p ⊗ₘ 𝟙 (n ⊗ r)) ≫ label r n k b f =
      label r n k a ((p ⊗ₘ 𝟙 n) ≫ f) := by
  have hn : (p ⊗ₘ 𝟙 (n ⊗ r)) ≫ (α_ b n r).inv =
      (α_ a n r).inv ≫ ((p ⊗ₘ 𝟙 n) ⊗ₘ 𝟙 r) := by
    simpa only [id_tensorHom_id] using
      associator_inv_naturality p (𝟙 n) (𝟙 r)
  unfold label
  rw [← Category.assoc, hn, Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]

/-- The actual original unit label is preserved by the full final-block extension. -/
theorem label_unit (r n : I) :
    label r n n (𝟙_ I) (λ_ n).hom = (λ_ (n ⊗ r)).hom := by
  unfold label
  monoidal

/-- The original coefficient-first composition label is preserved before coend descent. -/
theorem label_composition (r a b n k l : I)
    (f : a ⊗ n ⟶ k) (g : b ⊗ k ⟶ l) :
    label r n l (b ⊗ a) ((α_ b a n).hom ≫ (𝟙 b ⊗ₘ f) ≫ g) =
      (α_ b a (n ⊗ r)).hom ≫ (𝟙 b ⊗ₘ label r n k a f) ≫ label r k l b g := by
  have hNatural : b ◁ (f ▷ r) ≫ (α_ b k r).inv =
      (α_ b (a ⊗ n) r).inv ≫ ((b ◁ f) ▷ r) := by
    simpa only [id_tensorHom, tensorHom_id] using
      associator_inv_naturality (𝟙 b) f (𝟙 r)
  have hCoherence : (α_ b a (n ⊗ r)).hom ≫ b ◁ (α_ a n r).inv ≫
      (α_ b (a ⊗ n) r).inv =
    (α_ (b ⊗ a) n r).inv ≫ ((α_ b a n).hom ▷ r) := by
    monoidal
  calc
    _ = (α_ (b ⊗ a) n r).inv ≫ ((α_ b a n).hom ▷ r) ≫
        ((b ◁ f) ▷ r) ≫ (g ▷ r) := by
      simp only [label, tensorHom_id, id_tensorHom, comp_whiskerRight]
    _ = (α_ b a (n ⊗ r)).hom ≫ b ◁ (α_ a n r).inv ≫
        (α_ b (a ⊗ n) r).inv ≫ ((b ◁ f) ▷ r) ≫ (g ▷ r) := by
      simpa only [Category.assoc] using
        congrArg (fun z => z ≫ ((b ◁ f) ▷ r) ≫ (g ▷ r)) hCoherence.symm
    _ = (α_ b a (n ⊗ r)).hom ≫ b ◁ (α_ a n r).inv ≫
        b ◁ (f ▷ r) ≫ (α_ b k r).inv ≫ (g ▷ r) := by
      simpa only [Category.assoc] using
        congrArg (fun z => (α_ b a (n ⊗ r)).hom ≫
          b ◁ (α_ a n r).inv ≫ z ≫ (g ▷ r)) hNatural.symm
    _ = _ := by
      simp only [label, tensorHom_id, id_tensorHom, MonoidalCategory.whiskerLeft_comp,
        Category.assoc]

/-- The full original block category maps to the actual final-block shifted block category. -/
def blockFunctor (r n k : I) : BlockDecomposition n k ⥤
    BlockDecomposition (n ⊗ r) (k ⊗ r) where
  obj d := CostructuredArrow.mk (label r n k d.left d.hom)
  map q := CostructuredArrow.homMk q.left (by
    have hOriginal := CostructuredArrow.w q
    change (q.left ▷ n) ≫ _ = _ at hOriginal
    change (q.left ⊗ₘ 𝟙 (n ⊗ r)) ≫ label r n k _ _ = label r n k _ _
    rw [label_coefficient]
    apply congrArg (label r n k _)
    exact (congrArg (fun z => z ≫ _) (tensorHom_id q.left n)).trans hOriginal)
  map_id d := by
    apply CostructuredArrow.hom_ext
    rfl
  map_comp q q' := by
    apply CostructuredArrow.hom_ext
    rfl

/-- Every complete shifted coefficient leg is the actual native original coend generator. -/
def nativeCocone (r n k : I) : Cocone (blockDiagram.{u, v} n k) where
  pt := nativeHom.{u, v} (n ⊗ r) (k ⊗ r)
  ι :=
    { app := fun d => operatorGenerator d.left (n ⊗ r) (k ⊗ r)
        (label r n k d.left d.hom)
      naturality := by
        intro d e q
        have hw : (q.left ⊗ₘ 𝟙 n) ≫ e.hom = d.hom :=
          (congrArg (fun z => z ≫ e.hom) (tensorHom_id q.left n)).trans
            (CostructuredArrow.w q)
        change sphere.{u, v}.map q.left ≫
            operatorGenerator e.left (n ⊗ r) (k ⊗ r)
              (label r n k e.left e.hom) = _ ≫ 𝟙 _
        rw [operatorGenerator_coefficient, label_coefficient, hw, Category.comp_id] }

/-- The complete shifted cocone descends to the actual original block-colimit carrier. -/
def descent (r n k : I) :
    colimit (blockDiagram.{u, v} n k) ⟶ nativeHom.{u, v} (n ⊗ r) (k ⊗ r) :=
  colimit.desc (blockDiagram n k) (nativeCocone r n k)

/-- Every original block leg retains exactly its original shifted sphere generator. -/
theorem descent_generator (r n k a : I) (f : a ⊗ n ⟶ k) :
    colimit.ι (blockDiagram.{u, v} n k) (CostructuredArrow.mk f) ≫
        descent.{u, v} r n k =
      operatorGenerator.{u, v} a (n ⊗ r) (k ⊗ r) (label r n k a f) :=
  colimit.ι_desc (nativeCocone.{u, v} r n k) (CostructuredArrow.mk f)

/-- The entire native Hom shift descends the original block colimit after its genuine coend Iso. -/
def hom (r n k : I) : nativeHom.{u, v} n k ⟶ nativeHom.{u, v} (n ⊗ r) (k ⊗ r) :=
  nativeToBlock.{u, v} n k ≫ descent r n k

/-- The entire construction uses the actual original coend comparison forward function. -/
theorem hom_original_iso_function :
    (hom.{u, v} : ∀ r n k : I, nativeHom n k ⟶ nativeHom (n ⊗ r) (k ⊗ r)) =
      fun r n k => (nativeToBlockIso.{u, v} n k).hom ≫
        descent r n k :=
  congrArg (fun Φ => fun (r n k : I) => Φ n k ≫ descent r n k)
      nativeToBlockIso_forward_function.symm

/-- The whole original Hom/coefficient generator keeps its complete shifted descent function. -/
theorem hom_coend_generator_function :
    (fun (r n k : I) (a : CopowerUnderlying.{u, v, 0} I) =>
      Enriched.weightedCoend.ι (nativeWeight.{u, v} n k)
        sphereCopowerEnrichedFunctor.{u, v} a ≫ hom.{u, v} r n k) =
      fun (r n k : I) (a : CopowerUnderlying.{u, v, 0} I) =>
        blockLeg.{u, v} n k (show I from a) ≫ descent.{u, v} r n k := by
  have hWhole :
      (fun (r n k : I) (a : CopowerUnderlying.{u, v, 0} I) =>
        (Enriched.weightedCoend.ι (nativeWeight.{u, v} n k)
          sphereCopowerEnrichedFunctor.{u, v} a ≫ nativeToBlock.{u, v} n k) ≫
            descent.{u, v} r n k) =
      fun (r n k : I) (a : CopowerUnderlying.{u, v, 0} I) =>
        blockLeg.{u, v} n k (show I from a) ≫ descent.{u, v} r n k :=
    congrArg (fun Φ => fun (r n k : I) (a : CopowerUnderlying.{u, v, 0} I) =>
      Φ n k a ≫ descent.{u, v} r n k) nativeToBlock_coend_generator_function.{u, v}
  have hAssoc :
      (fun (r n k : I) (a : CopowerUnderlying.{u, v, 0} I) =>
        Enriched.weightedCoend.ι (nativeWeight.{u, v} n k)
          sphereCopowerEnrichedFunctor.{u, v} a ≫ hom.{u, v} r n k) =
      (fun (r n k : I) (a : CopowerUnderlying.{u, v, 0} I) =>
        (Enriched.weightedCoend.ι (nativeWeight.{u, v} n k)
          sphereCopowerEnrichedFunctor.{u, v} a ≫ nativeToBlock.{u, v} n k) ≫
            descent.{u, v} r n k) := by
    funext r n k a
    exact (Category.assoc
      (Enriched.weightedCoend.ι (nativeWeight.{u, v} n k)
        sphereCopowerEnrichedFunctor.{u, v} a)
      (nativeToBlock.{u, v} n k) (descent.{u, v} r n k)).symm
  exact hAssoc.trans hWhole

/-- The complete original labelled-generator function is the actual full coend insertion. -/
theorem original_generator_function_value :
    operatorGenerator.{u, v} =
      fun (a n k : I) (f : a ⊗ n ⟶ k) =>
        discreteSmashIncl.{u, v, 0} (a ⊗ n ⟶ k) (sphere.{u, v}.obj a) f ≫
          Enriched.weightedCoend.ι (nativeWeight.{u, v} n k)
            sphereCopowerEnrichedFunctor.{u, v} ((copowerRestriction.{u, v, 0} I).obj a) :=
  rfl

/-- The complete original block leg preserves every labelled source generator after descent. -/
theorem blockLeg_descent_generator (r n k a : I) (f : a ⊗ n ⟶ k) :
    discreteSmashIncl.{u, v, 0} (a ⊗ n ⟶ k) (sphere.{u, v}.obj a) f ≫
        (blockLeg.{u, v} n k a ≫ descent.{u, v} r n k) =
      operatorGenerator.{u, v} a (n ⊗ r) (k ⊗ r) (label r n k a f) := by
  let A : PointedCGWH.{u, v} := sphere.{u, v}.obj a
  let P : PointedCGWH.{u, v} := basedDiscreteObj.{u, v, 0} (a ⊗ n ⟶ k) ⊗ A
  let j : A ⟶ P := discreteSmashIncl.{u, v, 0} (a ⊗ n ⟶ k) A f
  have hBlock : j ≫ blockLeg.{u, v} n k a =
      colimit.ι (blockDiagram.{u, v} n k) (CostructuredArrow.mk f) :=
    blockLeg_generator.{u, v} n k a f
  exact (Category.assoc j (blockLeg.{u, v} n k a) (descent.{u, v} r n k)).symm.trans
    ((congrArg (fun z => z ≫ descent.{u, v} r n k) hBlock).trans
      (descent_generator.{u, v} r n k a f))

/-- Every full original sphere generator retains the exact source-extended original index map. -/
private def nativeGenerator (a n k : I) (f : a ⊗ n ⟶ k) :
    sphere.{u, v}.obj a ⟶ nativeHom.{u, v} n k := operatorGenerator.{u, v} a n k f

private theorem nativeGenerator_original_function :
    (nativeGenerator.{u, v} : ∀ a n k : I, (a ⊗ n ⟶ k) →
      (sphere.{u, v}.obj a ⟶ nativeHom.{u, v} n k)) = operatorGenerator.{u, v} := rfl

private theorem nativeGenerator_toBlock (n k a : I) (f : a ⊗ n ⟶ k) :
    nativeGenerator.{u, v} a n k f ≫ nativeToBlock.{u, v} n k =
      colimit.ι (blockDiagram.{u, v} n k) (CostructuredArrow.mk f) :=
  nativeToBlock_generator.{u, v} n k a f

private theorem nativeGenerator_shift (r n k a : I) (f : a ⊗ n ⟶ k) :
    nativeGenerator.{u, v} a n k f ≫ hom.{u, v} r n k =
      operatorGenerator.{u, v} a (n ⊗ r) (k ⊗ r) (label r n k a f) := by
  change nativeGenerator.{u, v} a n k f ≫
    (nativeToBlock.{u, v} n k ≫ descent.{u, v} r n k) = _
  rw [← Category.assoc, nativeGenerator_toBlock]
  exact descent_generator.{u, v} r n k a f

/-- The actual original generator has its complete shifted value on the native Hom carrier. -/
theorem hom_generator (r n k a : I) (f : a ⊗ n ⟶ k) :
    let γ : ∀ a₀ n₀ k₀ : I, (a₀ ⊗ n₀ ⟶ k₀) →
      (sphere.{u, v}.obj a₀ ⟶ nativeHom.{u, v} n₀ k₀) := operatorGenerator.{u, v}
    γ a n k f ≫ hom.{u, v} r n k =
      (operatorGenerator.{u, v} a (n ⊗ r) (k ⊗ r) (label r n k a f) :
        sphere.{u, v}.obj a ⟶ nativeHom.{u, v} (n ⊗ r) (k ⊗ r)) := by
  intro γ
  have hG : (nativeGenerator.{u, v} : ∀ a₀ n₀ k₀ : I, (a₀ ⊗ n₀ ⟶ k₀) →
      (sphere.{u, v}.obj a₀ ⟶ nativeHom.{u, v} n₀ k₀)) = γ :=
    nativeGenerator_original_function.{u, v}
  have hL := congrArg
    (fun (Φ : ∀ a₀ n₀ k₀ : I, (a₀ ⊗ n₀ ⟶ k₀) →
      (sphere.{u, v}.obj a₀ ⟶ nativeHom.{u, v} n₀ k₀)) =>
        Φ a n k f ≫ hom.{u, v} r n k)
    hG.symm
  exact hL.trans (nativeGenerator_shift.{u, v} r n k a f)



set_option backward.isDefEq.respectTransparency false in
/-- Evaluate the proved general coend algorithm on the exact original native
copower, sphere and all-pair coend data for comparison of the whole functions. -/
def coendHom (r n k : I) : nativeHom.{u, v} n k ⟶ nativeHom.{u, v} (n ⊗ r) (k ⊗ r) :=
  GenericRightTensor.hom (copowerUnderlyingMonoidalData.{u, v, 0} I)
    sphereCopowerEnrichedFunctor.{u, v}
    ((copowerRestriction.{u, v, 0} I).obj r)
    ((copowerRestriction.{u, v, 0} I).obj n)
    ((copowerRestriction.{u, v, 0} I).obj k)

set_option backward.isDefEq.respectTransparency false in
/-- The final-factor ordinary label on the native copower is the actual
restriction of the original complete block label. -/
theorem coend_label_original (r n k a : I) (f : a ⊗ n ⟶ k) :
    GenericRightTensor.label
        ((copowerRestriction.{u, v, 0} I).obj r)
        ((copowerRestriction.{u, v, 0} I).obj n)
        ((copowerRestriction.{u, v, 0} I).obj k)
        ((copowerRestriction.{u, v, 0} I).obj a)
        ((copowerRestriction.{u, v, 0} I).map f) =
      (copowerRestriction.{u, v, 0} I).map (label r n k a f) := by
  let R := copowerRestriction.{u, v, 0} I
  have ht : R.map f ▷ R.obj r = R.map (f ⊗ₘ 𝟙 r) := by
    rw [← tensorHom_id]
    have h := copowerUnderlyingMonoidal_tensor_original.{u, v, 0} I f (𝟙 r)
    rw [R.map_id] at h
    exact h
  change R.map (α_ a n r).inv ≫ (R.map f ▷ R.obj r) = R.map (label r n k a f)
  rw [ht, ← R.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The complete native weight-point functions use the original restricted
ordinary labels, before any coefficient or coend Hom input is applied. -/
theorem coendWeight_point_function :
    (fun (r n k a : I) (f : a ⊗ n ⟶ k) =>
      basedDiscreteIncl.{u, v, 0} (a ⊗ n ⟶ k) f ≫
        GenericRightTensor.weightShiftMap (copowerUnderlyingMonoidalData.{u, v, 0} I)
          ((copowerRestriction.{u, v, 0} I).obj r)
          ((copowerRestriction.{u, v, 0} I).obj n)
          ((copowerRestriction.{u, v, 0} I).obj k)
          ((copowerRestriction.{u, v, 0} I).obj a)) =
      fun (r n k a : I) (f : a ⊗ n ⟶ k) =>
        basedDiscreteIncl.{u, v, 0} (a ⊗ (n ⊗ r) ⟶ k ⊗ r) (label r n k a f) := by
  let R := copowerRestriction.{u, v, 0} I
  let d := copowerUnderlyingMonoidalData.{u, v, 0} I
  have h := congrArg
    (fun Φ => fun (r n k a : I) (f : a ⊗ n ⟶ k) =>
      Φ (R.obj r) (R.obj n) (R.obj k) (R.obj a) (R.map f))
    (GenericRightTensor.weightShiftMap_point_function d)
  funext r n k a f
  have h₀ := congrArg (fun Φ => Φ r n k a f) h
  dsimp only at h₀
  rw [coend_label_original] at h₀
  change basedDiscreteIncl (a ⊗ n ⟶ k) f ≫
      GenericRightTensor.weightShiftMap d (R.obj r) (R.obj n) (R.obj k) (R.obj a) =
    basedDiscreteIncl (a ⊗ (n ⊗ r) ⟶ k ⊗ r) (label r n k a f) at h₀
  exact h₀

set_option backward.isDefEq.respectTransparency false in
/-- The whole native enriched weight-map function is the original based
discrete map of the complete final-block label function. -/
theorem coendWeight_original_function :
    (fun (r n k a : I) =>
      GenericRightTensor.weightShiftMap (copowerUnderlyingMonoidalData.{u, v, 0} I)
        ((copowerRestriction.{u, v, 0} I).obj r)
        ((copowerRestriction.{u, v, 0} I).obj n)
        ((copowerRestriction.{u, v, 0} I).obj k)
        ((copowerRestriction.{u, v, 0} I).obj a)) =
      fun (r n k a : I) =>
        basedDiscreteFunctor.{u, v, 0}.map (↾fun f : a ⊗ n ⟶ k => label r n k a f) := by
  funext r n k a
  apply (basedDiscreteCofanIsColimit.{u, v, 0} (a ⊗ n ⟶ k)).hom_ext
  intro f
  exact (congrArg (fun Φ => Φ r n k a f.as) coendWeight_point_function).trans
    (basedDiscreteIncl_naturality.{u, v, 0} (fun f : a ⊗ n ⟶ k => label r n k a f) f.as).symm

end SymmetricShift

namespace SymmetricShift

open PointedCGWH
open PointedCGWH.SymmetricModulePresentation
open PointedCGWH.SymmetricOperatorHom
open CategoryTheory.Operad.SmallFinBijGroupoid

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

attribute [local instance] PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal
  CategoryTheory.Operad.SmallFinBijGroupoid.instMonoidalCategory
  CategoryTheory.Operad.SmallFinBijGroupoid.instSymmetricCategory
  MonoidalClosed.enrichedCategorySelf

/-- The literal original copower wrapper, with its universes explicit. -/
abbrev originalCopower : Type := CopowerUnderlying.{u, v, 0} I

/-- The actual original enriched monoidal data, with no new data choice. -/
abbrev originalData : EnrichedMonoidalCategoryData PointedCGWH.{u, v}
    originalCopower.{u, v} := copowerUnderlyingMonoidalData.{u, v, 0} I

/-- The entire original sphere coefficient functor. -/
abbrev originalSphere : EnrichedFunctor PointedCGWH.{u, v}
    originalCopower.{u, v} PointedCGWH.{u, v} := sphereCopowerEnrichedFunctor.{u, v}

/-- The entire original named native relation-coproduct proof family. -/
theorem originalRelationProofFamily : CoendProofFamilies.RelationFamily originalData.{u, v}
  originalSphere.{u, v} :=
  PointedCGWH.symmetricOperatorRelationCoproduct.{u, v}

/-- The entire original named native object-coproduct proof family. -/
theorem originalObjectProofFamily : CoendProofFamilies.ObjectFamily originalData.{u, v}
  originalSphere.{u, v} :=
  PointedCGWH.symmetricOperatorObjectCoproduct.{u, v}

/-- The original coequalizer witnesses retain the explicit original coproduct families. -/
theorem originalCoequalizerProofFamily : CoendProofFamilies.CoequalizerFamily originalData.{u,
  v} originalSphere.{u, v}
    originalRelationProofFamily.{u, v} originalObjectProofFamily.{u, v} :=
  PointedCGWH.symmetricOperatorCoequalizer.{u, v}

/-- The complete native constructor law holds before any original index is substituted. -/
theorem originalCharacteristic_constructor_function :
    (fun r n k a : originalCopower.{u, v} =>
      CoendProofFamilies.insertionFunction originalData.{u, v} originalSphere.{u, v}
        originalRelationProofFamily
        originalObjectProofFamily originalCoequalizerProofFamily n k a ≫
      CoendProofFamilies.homFunction originalData.{u, v} originalSphere.{u, v}
        originalRelationProofFamily
        originalObjectProofFamily originalCoequalizerProofFamily r n k) =
      fun r n k a : originalCopower.{u, v} => (GenericRightTensor.weightShiftMap
        originalData.{u, v} r n k a ⊗ₘ 𝟙 (originalSphere.{u, v}.obj a)) ≫
        CoendProofFamilies.insertionFunction originalData.{u, v} originalSphere.{u, v}
          originalRelationProofFamily
          originalObjectProofFamily originalCoequalizerProofFamily (n ⊗ r) (k ⊗ r) a :=
  CoendProofFamilies.hom_characteristic_function originalData.{u, v} originalSphere.{u, v}
    originalRelationProofFamily
    originalObjectProofFamily originalCoequalizerProofFamily

/-- The whole original native Hom-object function uses these exact constructor witnesses. -/
theorem originalCoend_object_function :
    (fun n k : I => CoendProofFamilies.coend originalData.{u, v} originalSphere.{u, v}
      originalRelationProofFamily
      originalObjectProofFamily originalCoequalizerProofFamily
      ((copowerRestriction.{u, v, 0} I).obj n) ((copowerRestriction.{u, v, 0} I).obj k)) =
      nativeHom.{u, v} := rfl

/-- The complete original insertion function uses the same actual object and coequalizer. -/
theorem originalInsertion_constructor_function :
    (fun n k a : I => CoendProofFamilies.insertionFunction originalData.{u, v}
      originalSphere.{u, v} originalRelationProofFamily
      originalObjectProofFamily originalCoequalizerProofFamily
      ((copowerRestriction.{u, v, 0} I).obj n) ((copowerRestriction.{u, v, 0} I).obj k)
      ((copowerRestriction.{u, v, 0} I).obj a)) =
      fun n k a : I => Enriched.weightedCoend.ι (nativeWeight.{u, v} n k) originalSphere.{u, v}
        ((copowerRestriction.{u, v, 0} I).obj a) := rfl

/-- The whole native coend shift is the original function with these constructor proofs. -/
theorem originalHom_constructor_function :
    (coendHom.{u, v} : ∀ r n k : I, nativeHom n k ⟶ nativeHom (n ⊗ r) (k ⊗ r)) =
      fun r n k : I => CoendProofFamilies.homFunction originalData.{u, v} originalSphere.{u, v}
        originalRelationProofFamily
        originalObjectProofFamily originalCoequalizerProofFamily
        ((copowerRestriction.{u, v, 0} I).obj r) ((copowerRestriction.{u, v, 0} I).obj n)
        ((copowerRestriction.{u, v, 0} I).obj k) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The restriction object function keeps every original object literally. -/
theorem originalRestriction_object_function :
    ((copowerRestriction.{u, v, 0} I).obj : I → originalCopower.{u, v}) =
      fun a : I => (show originalCopower.{u, v} from a) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The full native tensor-object function is the actual original tensor-object restriction. -/
theorem originalRestriction_tensor_object_function :
    (fun n r : I => ((copowerRestriction.{u, v, 0} I).obj n) ⊗
      ((copowerRestriction.{u, v, 0} I).obj r)) =
      fun n r : I => (copowerRestriction.{u, v, 0} I).obj (n ⊗ r) := rfl



/-- The literal complete original restriction object function. -/
abbrev originalObjectMap : I → originalCopower.{u, v} :=
  (copowerRestriction.{u, v, 0} I).obj

/-- The entire original source weight object function. -/
abbrev originalSourceWeight :=
  GenericCoendCharacteristic.sourceWeight (V := PointedCGWH.{u, v}) originalObjectMap.{u, v}

/-- The whole original target weight object function. -/
abbrev originalTargetWeight :=
  GenericCoendCharacteristic.targetWeight (V := PointedCGWH.{u, v})
    originalObjectMap.{u, v} originalObjectMap.{u, v}

/-- The full unchanged coefficient object function. -/
abbrev originalCoefficient : I → PointedCGWH.{u, v} := sphere.{u, v}.obj

/-- The actual enriched coefficient object projection is the whole original
sphere object function. -/
theorem originalCoefficient_sphere_function :
    GenericCoendCharacteristic.coefficient originalSphere.{u, v} originalObjectMap.{u, v} =
      originalCoefficient.{u, v} := rfl

/-- The actual original target Hom-object function. -/
abbrev originalTargetObject : I → I → I → PointedCGWH.{u, v} :=
  fun r n k => nativeHom.{u, v} (n ⊗ r) (k ⊗ r)

/-- The exact whole source constructor function under the original object restriction. -/
abbrev constructorSourceObject :=
  GenericCoendCharacteristic.sourceObject originalData.{u, v} originalSphere.{u, v}
    originalRelationProofFamily originalObjectProofFamily originalCoequalizerProofFamily
    originalObjectMap.{u, v}

/-- The complete original shifted target coend constructor. -/
abbrev constructorTargetObject :=
  GenericCoendCharacteristic.targetObject originalData.{u, v} originalSphere.{u, v}
    originalRelationProofFamily originalObjectProofFamily originalCoequalizerProofFamily
    originalObjectMap.{u, v} originalObjectMap.{u, v}

/-- The entire actual source insertion on the original native Hom objects. -/
def originalSourceInsertion :
    CoendEquationTransport.SourceInsertion originalSourceWeight.{u, v}
      originalCoefficient.{u, v} nativeHom.{u, v} :=
  fun n k a => Enriched.weightedCoend.ι (nativeWeight.{u, v} n k) originalSphere.{u, v}
    (originalObjectMap.{u, v} a)

/-- The entire actual target insertion on the original shifted native Hom objects. -/
def originalTargetInsertion :
    CoendEquationTransport.TargetInsertion originalTargetWeight.{u, v}
      originalCoefficient.{u, v} originalTargetObject.{u, v} :=
  fun r n k a => Enriched.weightedCoend.ι (nativeWeight.{u, v} (n ⊗ r) (k ⊗ r))
    originalSphere.{u, v} (originalObjectMap.{u, v} a)

/-- The whole original coend Hom-map function with both original object families. -/
abbrev originalHomMap :
    CoendEquationTransport.HomMap nativeHom.{u, v} originalTargetObject.{u, v} := coendHom.{u, v}

/-- The complete generic weight map on the actual original native weight objects. -/
abbrev originalWeightMap :
    CoendEquationTransport.WeightMap originalSourceWeight.{u, v} originalTargetWeight.{u, v} :=
  GenericCoendCharacteristic.weightMap originalData.{u, v}
    originalObjectMap.{u, v} originalObjectMap.{u, v}

/-- The entire original based-discrete block-label map. -/
def originalLabelWeightMap :
    CoendEquationTransport.WeightMap originalSourceWeight.{u, v} originalTargetWeight.{u, v} :=
  fun r n k a =>
    basedDiscreteFunctor.{u, v, 0}.map (↾fun f : a ⊗ n ⟶ k => label r n k a f)

set_option backward.isDefEq.respectTransparency false in
/-- The exact original source objects equal the complete source constructor function. -/
theorem originalSource_constructor_object_function :
    nativeHom.{u, v} = constructorSourceObject.{u, v} := originalCoend_object_function.{u, v}.symm

set_option backward.isDefEq.respectTransparency false in
/-- The actual entire target object function is the original shifted coend constructor. -/
theorem originalTarget_constructor_object_function :
    originalTargetObject.{u, v} = constructorTargetObject.{u, v} := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Both complete source-insertion functions retain the exact original coend witnesses. -/
theorem originalSource_constructor_insertion_heq :
    HEq originalSourceInsertion.{u, v}
      (GenericCoendCharacteristic.sourceInsertion originalData.{u, v} originalSphere.{u, v}
        originalRelationProofFamily originalObjectProofFamily originalCoequalizerProofFamily
        originalObjectMap.{u, v}) := HEq.rfl

set_option backward.isDefEq.respectTransparency false in
/-- Both whole target-insertion functions retain the same original shifted coend witnesses. -/
theorem originalTarget_constructor_insertion_heq :
    HEq originalTargetInsertion.{u, v}
      (GenericCoendCharacteristic.targetInsertion originalData.{u, v} originalSphere.{u, v}
        originalRelationProofFamily originalObjectProofFamily originalCoequalizerProofFamily
        originalObjectMap.{u, v} originalObjectMap.{u, v}) := HEq.rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual entire native Hom-map function is the full original reindexed constructor. -/
theorem originalHom_constructor_map_heq :
    HEq originalHomMap.{u, v}
      (GenericCoendCharacteristic.homMap originalData.{u, v} originalSphere.{u, v}
        originalRelationProofFamily originalObjectProofFamily originalCoequalizerProofFamily
        originalObjectMap.{u, v} originalObjectMap.{u, v}) := HEq.rfl

set_option backward.isDefEq.respectTransparency false in
/-- The whole native weight map is the original full block-label map before coend insertion. -/
theorem originalWeight_label_map_function :
    originalWeightMap.{u, v} = originalLabelWeightMap.{u, v} :=
  coendWeight_original_function.{u, v}


set_option backward.isDefEq.respectTransparency false in
/-- The actual complete native equation type equals the proved original
constructor equation type through the checked whole object/function identities. -/
theorem originalCharacteristic_condition_constructor_type_eq :
    CoendEquationTransport.Condition originalSourceInsertion.{u, v}
      originalTargetInsertion.{u, v} originalHomMap.{u, v} originalWeightMap.{u, v} =
    CoendEquationTransport.Condition
      (GenericCoendCharacteristic.sourceInsertion originalData.{u, v} originalSphere.{u, v}
        originalRelationProofFamily originalObjectProofFamily originalCoequalizerProofFamily
        originalObjectMap.{u, v})
      (GenericCoendCharacteristic.targetInsertion originalData.{u, v} originalSphere.{u, v}
        originalRelationProofFamily originalObjectProofFamily originalCoequalizerProofFamily
        originalObjectMap.{u, v} originalObjectMap.{u, v})
      (GenericCoendCharacteristic.homMap originalData.{u, v} originalSphere.{u, v}
        originalRelationProofFamily originalObjectProofFamily originalCoequalizerProofFamily
        originalObjectMap.{u, v} originalObjectMap.{u, v})
      (GenericCoendCharacteristic.weightMap originalData.{u, v}
        originalObjectMap.{u, v} originalObjectMap.{u, v}) :=
  CoendEquationTransport.condition_eq originalSourceInsertion
    (GenericCoendCharacteristic.sourceInsertion originalData originalSphere
      originalRelationProofFamily originalObjectProofFamily originalCoequalizerProofFamily
      originalObjectMap)
    originalTargetInsertion
    (GenericCoendCharacteristic.targetInsertion originalData originalSphere
      originalRelationProofFamily originalObjectProofFamily originalCoequalizerProofFamily
      originalObjectMap originalObjectMap)
    originalHomMap
    (GenericCoendCharacteristic.homMap originalData originalSphere originalRelationProofFamily
      originalObjectProofFamily originalCoequalizerProofFamily originalObjectMap originalObjectMap)
    originalWeightMap
    (GenericCoendCharacteristic.weightMap originalData originalObjectMap originalObjectMap)
    originalSource_constructor_object_function originalTarget_constructor_object_function
    originalSource_constructor_insertion_heq originalTarget_constructor_insertion_heq
    originalHom_constructor_map_heq rfl

set_option backward.isDefEq.respectTransparency false in
/-- The exact complete original native equation is proved by its full
constructor-family transport, before any coend input or native coefficient is applied. -/
theorem originalCharacteristic_condition_proof :
    CoendEquationTransport.Condition originalSourceInsertion.{u, v}
      originalTargetInsertion.{u, v} originalHomMap.{u, v} originalWeightMap.{u, v} :=
  Eq.mpr originalCharacteristic_condition_constructor_type_eq.{u, v}
    (GenericCoendCharacteristic.condition_proof originalData.{u, v} originalSphere.{u, v}
      originalRelationProofFamily originalObjectProofFamily originalCoequalizerProofFamily
      originalObjectMap.{u, v} originalObjectMap.{u, v})

set_option backward.isDefEq.respectTransparency false in
/-- The actual entire original label-map equality identifies the full native equation type. -/
theorem originalCharacteristic_condition_label_type_eq :
    CoendEquationTransport.Condition originalSourceInsertion.{u, v}
      originalTargetInsertion.{u, v} originalHomMap.{u, v} originalWeightMap.{u, v} =
    CoendEquationTransport.Condition originalSourceInsertion.{u, v}
      originalTargetInsertion.{u, v} originalHomMap.{u, v} originalLabelWeightMap.{u, v} :=
  congrArg
    (CoendEquationTransport.Condition originalSourceInsertion.{u, v}
      originalTargetInsertion.{u, v} originalHomMap.{u, v})
    originalWeight_label_map_function.{u, v}

set_option backward.isDefEq.respectTransparency false in
/-- The complete original label characteristic is proved on the actual native functions. -/
theorem originalCharacteristic_label_condition_proof :
    CoendEquationTransport.Condition originalSourceInsertion.{u, v}
      originalTargetInsertion.{u, v} originalHomMap.{u, v} originalLabelWeightMap.{u, v} :=
  Eq.mp originalCharacteristic_condition_label_type_eq.{u, v}
    originalCharacteristic_condition_proof.{u, v}

set_option backward.isDefEq.respectTransparency false in
/-- The full original native coend characteristic is the equality of the
complete original source and target composite functions. These retain every
original index, label, coefficient and native coend insertion. -/
theorem coendHom_ι_original_function :
    CoendEquationTransport.sourceComposite originalSourceInsertion.{u, v} originalHomMap.{u, v} =
      CoendEquationTransport.targetComposite originalTargetInsertion.{u, v}
        originalLabelWeightMap.{u, v} :=
  originalCharacteristic_label_condition_proof.{u, v}


/-- All original full source labels, without changing their ordinary arrow type. -/
abbrev originalLabelFamily : I → I → I → Type := fun n k a => a ⊗ n ⟶ k

/-- Every complete original discrete-smash coefficient inclusion. -/
def originalSourceCoefficient :
    CoendGeneratorTransport.SourceCoefficient (E := originalLabelFamily)
      (W := originalSourceWeight.{u, v}) (T := originalCoefficient.{u, v}) :=
  fun n k a f => discreteSmashIncl.{u, v, 0} (a ⊗ n ⟶ k) (sphere.{u, v}.obj a) f

/-- Every whole shifted original coefficient inclusion at its exact original block label. -/
def originalTargetCoefficient :
    CoendGeneratorTransport.TargetCoefficient (E := originalLabelFamily)
      (W' := originalTargetWeight.{u, v}) (T := originalCoefficient.{u, v}) :=
  fun r n k a f => discreteSmashIncl.{u, v, 0}
    (a ⊗ (n ⊗ r) ⟶ k ⊗ r) (sphere.{u, v}.obj a) (label r n k a f)

/-- The complete actual original operator-generator function. -/
def originalSourceGenerator :
    CoendGeneratorTransport.SourceGenerator (E := originalLabelFamily)
      (T := originalCoefficient.{u, v}) (M := nativeHom.{u, v}) :=
  fun n k a f => operatorGenerator.{u, v} a n k f

/-- The entire original target-generator function, preserving all source labels. -/
def originalTargetGenerator :
    CoendGeneratorTransport.TargetGenerator (E := originalLabelFamily)
      (T := originalCoefficient.{u, v}) (N := originalTargetObject.{u, v}) :=
  fun r n k a f => operatorGenerator.{u, v} a (n ⊗ r) (k ⊗ r) (label r n k a f)

set_option backward.isDefEq.respectTransparency false in
/-- The source-generator function is the actual complete original coefficient/coend insertion. -/
theorem originalSource_generator_value_function :
    originalSourceGenerator.{u, v} =
      CoendGeneratorTransport.sourceGenerator originalSourceCoefficient.{u, v}
        originalSourceInsertion.{u, v} := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The whole target-generator function is the exact shifted original
coefficient/coend insertion. -/
theorem originalTarget_generator_value_function :
    originalTargetGenerator.{u, v} =
      CoendGeneratorTransport.targetGenerator originalTargetCoefficient.{u, v}
        originalTargetInsertion.{u, v} := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Complete original coefficient-label naturality is proved before any
native Hom or coend argument is supplied. -/
theorem originalCoefficient_label_condition_proof :
    CoendGeneratorTransport.CoefficientCondition originalSourceCoefficient.{u, v}
      originalTargetCoefficient.{u, v} originalLabelWeightMap.{u, v} := by
  funext r n k a f
  let A : PointedCGWH.{u, v} := sphere.{u, v}.obj a
  let E : Type := a ⊗ n ⟶ k
  let E' : Type := a ⊗ (n ⊗ r) ⟶ k ⊗ r
  let q : basedDiscreteObj.{u, v, 0} E ⟶ basedDiscreteObj.{u, v, 0} E' :=
    basedDiscreteFunctor.{u, v, 0}.map (↾fun f : E => label r n k a f)
  have hIncl : basedDiscreteIncl.{u, v, 0} E f ≫ q =
      basedDiscreteIncl.{u, v, 0} E' (label r n k a f) :=
    basedDiscreteIncl_naturality.{u, v, 0} (fun f : E => label r n k a f) f
  change discreteSmashIncl.{u, v, 0} E A f ≫ (q ▷ A) =
    discreteSmashIncl.{u, v, 0} E' A (label r n k a f)
  simp only [discreteSmashIncl, Category.assoc]
  rw [← tensorHom_id, tensorHom_comp_tensorHom, hIncl, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The complete original generator equation type equals its fixed
coefficient/coend constructor equation type through whole generator identities. -/
theorem originalGenerator_condition_constructor_type_eq :
    CoendGeneratorTransport.Condition originalSourceGenerator.{u, v}
      originalTargetGenerator.{u, v} originalHomMap.{u, v} =
    CoendGeneratorTransport.Condition
      (CoendGeneratorTransport.sourceGenerator originalSourceCoefficient.{u, v}
        originalSourceInsertion.{u, v})
      (CoendGeneratorTransport.targetGenerator originalTargetCoefficient.{u, v}
        originalTargetInsertion.{u, v}) originalHomMap.{u, v} :=
  CoendGeneratorTransport.condition_eq originalSourceGenerator
    (CoendGeneratorTransport.sourceGenerator originalSourceCoefficient originalSourceInsertion)
    originalTargetGenerator
    (CoendGeneratorTransport.targetGenerator originalTargetCoefficient originalTargetInsertion)
    originalHomMap originalSource_generator_value_function originalTarget_generator_value_function

set_option backward.isDefEq.respectTransparency false in
/-- The actual complete native generator equation follows from the checked
whole coend characteristic and whole original coefficient-label naturality. -/
theorem originalGenerator_condition_proof :
    CoendGeneratorTransport.Condition originalSourceGenerator.{u, v}
      originalTargetGenerator.{u, v} originalHomMap.{u, v} :=
  Eq.mpr originalGenerator_condition_constructor_type_eq.{u, v}
    (CoendGeneratorTransport.condition_of_characteristic originalSourceCoefficient.{u, v}
      originalTargetCoefficient originalSourceInsertion originalTargetInsertion originalHomMap
      originalLabelWeightMap originalCharacteristic_label_condition_proof
      originalCoefficient_label_condition_proof)

set_option backward.isDefEq.respectTransparency false in
/-- The entire actual original generator/Hom-map functions agree on every
original source label and sphere coefficient before native application. -/
theorem coendHom_generator_original_function :
    CoendGeneratorTransport.homComposite originalSourceGenerator.{u, v} originalHomMap.{u, v} =
      originalTargetGenerator.{u, v} := originalGenerator_condition_proof.{u, v}


/-- The complete original source block-diagram family. -/
abbrev originalBlockDiagram := blockDiagram.{u, v}

/-- The exact original block-Iso family on the complete native source objects. -/
abbrev originalBlockIsos := nativeToBlockIso.{u, v}

/-- The entire original shifted generator cocone family. -/
private abbrev originalBlockCocones := nativeCocone.{u, v}

/-- The whole original block-colimit descent function. -/
abbrev originalBlockDescent :
    ∀ r n k : I, colimit (blockDiagram.{u, v} n k) ⟶ originalTargetObject.{u, v} r n k :=
  descent.{u, v}

/-- The original coefficient object of each actual block decomposition. -/
def originalBlockCoefficient : ∀ n k : I, BlockDecomposition n k → I :=
  fun _n _k a => a.left

/-- Every complete original block label is retained in its actual ordinary arrow type. -/
def originalBlockLabel : ∀ n k : I, ∀ a : BlockDecomposition n k,
    originalLabelFamily n k (originalBlockCoefficient n k a) := fun _n _k a => a.hom

/-- The complete original source-generator function on the actual block diagrams. -/
def originalBlockSourceGenerator :
    ColimitHomFamily.SourceGenerator originalBlockDiagram.{u, v} (M := nativeHom.{u, v}) :=
  CoendGeneratorTransport.restrictSource originalBlockCoefficient originalBlockLabel
    originalSourceGenerator.{u, v}

/-- The full actual shifted target-generator function on every original block diagram. -/
def originalBlockTargetGenerator :
    ColimitHomFamily.TargetGenerator originalBlockDiagram.{u, v}
      (N := originalTargetObject.{u, v}) :=
  CoendGeneratorTransport.restrictTarget originalBlockCoefficient originalBlockLabel
    originalTargetGenerator.{u, v}

set_option backward.isDefEq.respectTransparency false in
/-- Every original diagram source object is the actual original coefficient object function. -/
theorem originalBlock_source_object_function :
    (fun (n k : I) (a : BlockDecomposition n k) => (originalBlockDiagram.{u, v} n k).obj a) =
      fun (n k : I) (a : BlockDecomposition n k) =>
        originalCoefficient.{u, v} (originalBlockCoefficient n k a) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The complete inverse-leg function equals the original full source-generator function. -/
theorem originalBlock_inverse_generator_function :
    ColimitHomFamily.inverseLegs originalBlockDiagram.{u, v} originalBlockIsos.{u, v} =
      originalBlockSourceGenerator.{u, v} := by
  have h := congrArg
    (fun (Φ : ∀ n k : I,
      colimit (blockDiagram.{u, v} n k) ⟶ nativeHom.{u, v} n k) =>
      fun (n k : I) (a : BlockDecomposition n k) =>
        colimit.ι (blockDiagram.{u, v} n k) a ≫ Φ n k)
    nativeToBlockIso_inverse_function
  exact h.trans blockToNative_generator_function

set_option backward.isDefEq.respectTransparency false in
/-- The full original cocone descent has its complete actual shifted-generator characteristic. -/
theorem originalBlock_descent_generator_function :
    ColimitHomFamily.targetLegs originalBlockDiagram.{u, v} originalBlockDescent.{u, v} =
      originalBlockTargetGenerator.{u, v} :=
  ColimitHomFamily.coconeDesc_legs_function originalBlockDiagram.{u, v} originalBlockCocones.{u, v}

/-- The complete original coefficient-source object function on block diagrams. -/
abbrev originalBlockCoefficientObjects :=
  BlockGeneratorSourceTransport.restrictedObjects (T := originalCoefficient.{u, v})
    originalBlockCoefficient

/-- The whole source generator on its actual coefficient-source object function. -/
abbrev originalBlockCoefficientSourceGenerator :=
  CoendGeneratorTransport.restrictSource originalBlockCoefficient originalBlockLabel
    originalSourceGenerator.{u, v}

/-- Every full target generator on the same original coefficient-source function. -/
abbrev originalBlockCoefficientTargetGenerator :=
  CoendGeneratorTransport.restrictTarget originalBlockCoefficient originalBlockLabel
    originalTargetGenerator.{u, v}

set_option backward.isDefEq.respectTransparency false in
/-- The actual complete diagram/source generator is the original coefficient-source generator. -/
theorem originalBlock_source_generator_object_heq :
    HEq originalBlockSourceGenerator.{u, v} originalBlockCoefficientSourceGenerator.{u, v} :=
      HEq.rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual entire diagram/target generator is the original coefficient-source
target generator. -/
theorem originalBlock_target_generator_object_heq :
    HEq originalBlockTargetGenerator.{u, v} originalBlockCoefficientTargetGenerator.{u, v} :=
      HEq.rfl

set_option backward.isDefEq.respectTransparency false in
/-- Whole original source-object and generator identities identify the exact block equation type. -/
theorem originalBlock_source_generator_condition_type_eq :
    BlockGeneratorSourceTransport.Condition (O :=
      BlockGeneratorSourceTransport.diagramObjects originalBlockDiagram.{u, v})
      originalBlockSourceGenerator.{u, v} originalBlockTargetGenerator.{u, v}
        originalHomMap.{u, v} =
    BlockGeneratorSourceTransport.Condition (O := originalBlockCoefficientObjects.{u, v})
      originalBlockCoefficientSourceGenerator.{u, v} originalBlockCoefficientTargetGenerator.{u, v}
      originalHomMap.{u, v} :=
  BlockGeneratorSourceTransport.condition_type_eq originalBlockSourceGenerator
    originalBlockCoefficientSourceGenerator originalBlockTargetGenerator
    originalBlockCoefficientTargetGenerator originalHomMap originalBlock_source_object_function
    originalBlock_source_generator_object_heq originalBlock_target_generator_object_heq

set_option backward.isDefEq.respectTransparency false in
/-- The complete actual block-generator equation holds at the original coefficient source family. -/
theorem originalBlock_coefficient_generator_condition_proof :
    BlockGeneratorSourceTransport.Condition (O := originalBlockCoefficientObjects.{u, v})
      originalBlockCoefficientSourceGenerator.{u, v} originalBlockCoefficientTargetGenerator.{u, v}
      originalHomMap.{u, v} :=
  Eq.mpr
    (BlockGeneratorSourceTransport.restricted_condition_type_eq
      (C := PointedCGWH.{u, v}) (J := I) (R := I) (E := originalLabelFamily)
      (T := originalCoefficient.{u, v}) (M := nativeHom.{u, v})
      (N := originalTargetObject.{u, v}) (D := BlockDecomposition)
      originalBlockCoefficient originalBlockLabel originalSourceGenerator originalTargetGenerator
      originalHomMap)
    (CoendGeneratorTransport.restricted_condition_function
      (V := PointedCGWH.{u, v}) (J := I) (R := I) (E := originalLabelFamily)
      (T := originalCoefficient.{u, v}) (M := nativeHom.{u, v})
      (N := originalTargetObject.{u, v}) (D := BlockDecomposition)
      originalBlockCoefficient originalBlockLabel originalSourceGenerator originalTargetGenerator
      originalHomMap originalGenerator_condition_proof)

set_option backward.isDefEq.respectTransparency false in
/-- The actual whole native coend map preserves every full original block generator. -/
theorem originalBlock_coend_generator_function :
    ColimitHomFamily.generatorAfter originalBlockDiagram.{u, v}
      originalBlockSourceGenerator.{u, v} originalHomMap.{u, v} =
      originalBlockTargetGenerator.{u, v} :=
  Eq.mp (BlockGeneratorSourceTransport.colimit_condition_type_eq originalBlockDiagram.{u, v}
    originalBlockSourceGenerator originalBlockTargetGenerator originalHomMap)
    (Eq.mpr originalBlock_source_generator_condition_type_eq.{u, v}
      originalBlock_coefficient_generator_condition_proof.{u, v})


set_option backward.isDefEq.respectTransparency false in
/-- The entire original Iso-forward/descent function is the actual original Hom shift. -/
theorem originalBlock_forward_descent_function :
    ColimitHomFamily.isoForwardDescent originalBlockDiagram.{u, v} originalBlockIsos.{u, v}
      originalBlockDescent.{u, v} = hom.{u, v} := hom_original_iso_function.{u, v}.symm


set_option backward.isDefEq.respectTransparency false in
/-- The entire actual native coend Hom-map function is the original
nativeToBlock/descent function, proved through its full original block Iso. -/
theorem coendHom_original_function_via_block_iso :
    (coendHom.{u, v} : ∀ r n k : I,
      nativeHom n k ⟶ nativeHom (n ⊗ r) (k ⊗ r)) = hom.{u, v} := by
  have hAfter := originalBlock_coend_generator_function.{u, v}.trans
    originalBlock_descent_generator_function.{u, v}.symm
  have hFunction := ColimitHomFamily.hom_eq_of_full_generators originalBlockDiagram.{u, v}
    originalBlockIsos.{u, v} originalBlockSourceGenerator.{u, v} originalHomMap.{u, v}
    originalBlockDescent.{u, v} originalBlock_inverse_generator_function.{u, v} hAfter
  exact hFunction.trans originalBlock_forward_descent_function.{u, v}


set_option backward.isDefEq.respectTransparency false in
/-- For proof transport use the already constructed generic shift on the
literal original native operator index, sphere and all-pair coend data. -/
abbrev originalGenericShiftForProof (r : I) :
    EnrichedFunctor PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v}
      SymmetricOperatorIndex.{u, v} :=
  GenericRightTensor.indexShift originalData.{u, v} originalSphere.{u, v}
    sphereCopowerLaxData.{u, v} (originalObjectMap.{u, v} r)

set_option backward.isDefEq.respectTransparency false in
/-- The whole proved generic shift object function is the literal original final-block algorithm. -/
theorem originalGenericShift_object_function :
    (fun r : I => (originalGenericShiftForProof.{u, v} r).obj) =
      fun (r : I) (X : SymmetricOperatorIndex.{u, v}) =>
        symmetricOperatorObj.{u, v} ((show I from X.asIndex) ⊗ r) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The complete generic native Hom-map function is the entire original block-descent Hom
  function. -/
theorem originalGenericShift_nativeHom_function :
    (fun r n k : I => (originalGenericShiftForProof.{u, v} r).map
      (symmetricOperatorObj.{u, v} n) (symmetricOperatorObj.{u, v} k)) = hom.{u, v} := by
  have h : (fun r n k : I => (originalGenericShiftForProof.{u, v} r).map
      (symmetricOperatorObj.{u, v} n) (symmetricOperatorObj.{u, v} k)) = coendHom.{u, v} := rfl
  exact h.trans coendHom_original_function_via_block_iso.{u, v}

set_option backward.isDefEq.respectTransparency false in
/-- Every complete generic index map is the full original native Hom map
before any actual operator object is supplied. -/
theorem originalGenericShift_fullHom_function :
    (fun (r : I) (X Y : SymmetricOperatorIndex.{u, v}) =>
      (originalGenericShiftForProof.{u, v} r).map X Y) =
      fun (r : I) (X Y : SymmetricOperatorIndex.{u, v}) =>
        hom.{u, v} r (show I from X.asIndex) (show I from Y.asIndex) := by
  funext r X Y
  exact congrArg
    (fun Φ => Φ r (show I from X.asIndex) (show I from Y.asIndex))
    originalGenericShift_nativeHom_function.{u, v}


/-- The complete literal original final-block object algorithm. -/
def originalShiftObjects (r : I) (X : SymmetricOperatorIndex.{u, v}) :
    SymmetricOperatorIndex.{u, v} :=
  symmetricOperatorObj.{u, v} ((show I from X.asIndex) ⊗ r)

/-- The actual full original Hom-map algorithm on those literal shifted objects. -/
def originalShiftMaps : EnrichedFunctorFullLawTransport.Maps (V := PointedCGWH.{u, v})
    originalShiftObjects.{u, v} :=
  fun (r : I) (X Y : SymmetricOperatorIndex.{u, v}) =>
    hom.{u, v} r (show I from X.asIndex) (show I from Y.asIndex)

set_option backward.isDefEq.respectTransparency false in
/-- The actual whole functor-object fields are the complete original object algorithm. -/
theorem originalShift_functor_object_function :
    EnrichedFunctorFullLawTransport.functorObjects originalGenericShiftForProof.{u, v} =
      originalShiftObjects.{u, v} := originalGenericShift_object_function.{u, v}

set_option backward.isDefEq.respectTransparency false in
/-- The full original index Hom-map fields are the complete proved generic shift fields. -/
theorem originalShift_functor_map_heq :
    HEq (EnrichedFunctorFullLawTransport.functorMaps originalGenericShiftForProof.{u, v})
      originalShiftMaps.{u, v} := heq_of_eq originalGenericShift_fullHom_function.{u, v}

set_option backward.isDefEq.respectTransparency false in
/-- Whole original object and map identities identify the full enriched identity equation type. -/
theorem originalShift_identity_condition_type_eq :
    EnrichedFunctorFullLawTransport.IdentityCondition
      (EnrichedFunctorFullLawTransport.functorObjects originalGenericShiftForProof.{u, v})
      (EnrichedFunctorFullLawTransport.functorMaps originalGenericShiftForProof.{u, v}) =
    EnrichedFunctorFullLawTransport.IdentityCondition originalShiftObjects.{u, v}
      originalShiftMaps.{u, v} :=
  EnrichedFunctorFullLawTransport.identity_condition_type_eq
    (EnrichedFunctorFullLawTransport.functorMaps originalGenericShiftForProof)
    originalShiftMaps originalShift_functor_object_function originalShift_functor_map_heq

set_option backward.isDefEq.respectTransparency false in
/-- Both full original Hom factors and all object/map fields identify
the exact complete enriched composition equation type. -/
theorem originalShift_composition_condition_type_eq :
    EnrichedFunctorFullLawTransport.CompositionCondition
      (EnrichedFunctorFullLawTransport.functorObjects originalGenericShiftForProof.{u, v})
      (EnrichedFunctorFullLawTransport.functorMaps originalGenericShiftForProof.{u, v}) =
    EnrichedFunctorFullLawTransport.CompositionCondition originalShiftObjects.{u, v}
      originalShiftMaps.{u, v} :=
  EnrichedFunctorFullLawTransport.composition_condition_type_eq
    (EnrichedFunctorFullLawTransport.functorMaps originalGenericShiftForProof)
    originalShiftMaps originalShift_functor_object_function originalShift_functor_map_heq

set_option backward.isDefEq.respectTransparency false in
/-- The entire actual original enriched identity function is preserved by
the original native final-block map, with no identity law assumed. -/
theorem originalShift_identity_condition_proof :
    EnrichedFunctorFullLawTransport.IdentityCondition originalShiftObjects.{u, v}
      originalShiftMaps.{u, v} :=
  Eq.mp originalShift_identity_condition_type_eq.{u, v}
    (EnrichedFunctorFullLawTransport.identity_condition_of_functors
      originalGenericShiftForProof.{u, v})

set_option backward.isDefEq.respectTransparency false in
/-- The actual complete original enriched composition function is preserved,
retaining both full native Hom factors and no incoming composition law. -/
theorem originalShift_composition_condition_proof :
    EnrichedFunctorFullLawTransport.CompositionCondition originalShiftObjects.{u, v}
      originalShiftMaps.{u, v} :=
  Eq.mp originalShift_composition_condition_type_eq.{u, v}
    (EnrichedFunctorFullLawTransport.composition_condition_of_functors
      originalGenericShiftForProof.{u, v})

set_option backward.isDefEq.respectTransparency false in
/-- The actual whole fields identify the complete existing identity proof-field TYPE. -/
theorem originalShift_identity_proof_field_type_eq :
    EnrichedFunctorProofFieldTransport.IdentityFields
      (EnrichedFunctorFullLawTransport.functorObjects originalGenericShiftForProof.{u, v})
      (EnrichedFunctorFullLawTransport.functorMaps originalGenericShiftForProof.{u, v}) =
    EnrichedFunctorProofFieldTransport.IdentityFields originalShiftObjects.{u, v}
      originalShiftMaps.{u, v} :=
  EnrichedFunctorProofFieldTransport.identity_fields_type_eq
    (EnrichedFunctorFullLawTransport.functorMaps originalGenericShiftForProof)
    originalShiftMaps originalShift_functor_object_function originalShift_functor_map_heq

set_option backward.isDefEq.respectTransparency false in
/-- All actual original identity proof fields are transported before object application. -/
theorem originalShift_identity_proof_field_function :
    EnrichedFunctorProofFieldTransport.IdentityFields originalShiftObjects.{u, v}
      originalShiftMaps.{u, v} :=
  Eq.mp originalShift_identity_proof_field_type_eq.{u, v}
    (EnrichedFunctorProofFieldTransport.identity_fields_of_functors
      originalGenericShiftForProof.{u, v})

set_option backward.isDefEq.respectTransparency false in
/-- Whole original fields identify the entire existing composition proof-function TYPE. -/
theorem originalShift_composition_proof_field_type_eq :
    EnrichedFunctorProofFieldTransport.CompositionFields
      (EnrichedFunctorFullLawTransport.functorObjects originalGenericShiftForProof.{u, v})
      (EnrichedFunctorFullLawTransport.functorMaps originalGenericShiftForProof.{u, v}) =
    EnrichedFunctorProofFieldTransport.CompositionFields originalShiftObjects.{u, v}
      originalShiftMaps.{u, v} :=
  EnrichedFunctorProofFieldTransport.composition_fields_type_eq
    (EnrichedFunctorFullLawTransport.functorMaps originalGenericShiftForProof)
    originalShiftMaps originalShift_functor_object_function originalShift_functor_map_heq

set_option backward.isDefEq.respectTransparency false in
/-- The same complete original composition proof fields precede native inputs. -/
theorem originalShift_composition_proof_field_function :
    EnrichedFunctorProofFieldTransport.CompositionFields originalShiftObjects.{u, v}
      originalShiftMaps.{u, v} :=
  Eq.mp originalShift_composition_proof_field_type_eq.{u, v}
    (EnrichedFunctorProofFieldTransport.composition_fields_of_functors
      originalGenericShiftForProof.{u, v})

/-- The complete native composition of symmetric operator Hom objects. -/
def nativeComposition (n k l : I) :
    nativeHom.{u, v} n k ⊗ nativeHom.{u, v} k l ⟶ nativeHom.{u, v} n l :=
  Enriched.SphereOperator.composition (copowerUnderlyingMonoidalData.{u, v, 0} I)
    sphereCopowerEnrichedFunctor.{u, v} sphereCopowerLaxData.{u, v}
    ((copowerRestriction.{u, v, 0} I).obj n)
    ((copowerRestriction.{u, v, 0} I).obj k)
    ((copowerRestriction.{u, v, 0} I).obj l)

private theorem nativeComposition_original_function :
    (nativeComposition.{u, v} : ∀ n k l : I,
      nativeHom.{u, v} n k ⊗ nativeHom.{u, v} k l ⟶ nativeHom.{u, v} n l) =
      fun n k l : I => eComp PointedCGWH.{u, v}
        (symmetricOperatorObj.{u, v} n) (symmetricOperatorObj.{u, v} k)
        (symmetricOperatorObj.{u, v} l) := rfl


/-- The actual whole native source Hom-object function. -/
def originalNativeShiftHomObjects :
    FullShiftCompositionEquationTransport.HomObjects (V := PointedCGWH.{u, v}) (J := I) :=
  fun n k => nativeHom.{u, v} n k

/-- All exact native Hom targets of the original final-block algorithm. -/
def originalNativeShiftTargetHomObjects :
    FullShiftCompositionEquationTransport.TargetHomObjects
      (V := PointedCGWH.{u, v}) (J := I) (R := I) :=
  fun r n k => nativeHom.{u, v} (n ⊗ r) (k ⊗ r)

/-- The entire actual native Hom-map function on those original object fields. -/
def originalNativeShiftMapFields : FullShiftCompositionEquationTransport.Maps
    originalNativeShiftHomObjects.{u, v} originalNativeShiftTargetHomObjects.{u, v} :=
  hom.{u, v}

/-- The complete original target composition fields under the final-block function. -/
def originalNativeShiftTargetCompositionFields :
    FullShiftCompositionEquationTransport.TargetComposition
      originalNativeShiftTargetHomObjects.{u, v} :=
  fun r n k l => nativeComposition.{u, v} (n ⊗ r) (k ⊗ r) (l ⊗ r)

set_option backward.isDefEq.respectTransparency false in
/-- The full represented enriched source Hom-object function is the original native function. -/
theorem originalNativeComposition_source_objects_function :
    FullShiftCompositionEquationTransport.sourceHomObjects
      (V := PointedCGWH.{u, v}) symmetricOperatorObj.{u, v} =
      originalNativeShiftHomObjects.{u, v} := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every full represented target Hom-object field is the literal original native target. -/
theorem originalNativeComposition_target_objects_function :
    FullShiftCompositionEquationTransport.targetHomObjects
      (V := PointedCGWH.{u, v}) symmetricOperatorObj.{u, v} originalShiftObjects.{u, v} =
      originalNativeShiftTargetHomObjects.{u, v} := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Both entire native Hom-map fields are the same actual original function. -/
theorem originalNativeComposition_map_fields_heq :
    HEq (FullShiftCompositionEquationTransport.maps symmetricOperatorObj.{u, v}
      originalShiftObjects.{u, v} originalShiftMaps.{u, v})
      originalNativeShiftMapFields.{u, v} := HEq.rfl

set_option backward.isDefEq.respectTransparency false in
/-- The whole original source composition field identifies the actual enriched field. -/
theorem originalNativeComposition_source_fields_heq :
    HEq (FullShiftCompositionEquationTransport.sourceComposition
      (V := PointedCGWH.{u, v}) symmetricOperatorObj.{u, v}) nativeComposition.{u, v} :=
  heq_of_eq nativeComposition_original_function.{u, v}.symm

set_option backward.isDefEq.respectTransparency false in
/-- All original target composition fields are identified before any operator input. -/
theorem originalNativeComposition_target_fields_heq :
    HEq (FullShiftCompositionEquationTransport.targetComposition
      (V := PointedCGWH.{u, v}) symmetricOperatorObj.{u, v} originalShiftObjects.{u, v})
      originalNativeShiftTargetCompositionFields.{u, v} :=
  heq_of_eq (congrArg
    (fun (Φ : ∀ n k l : I,
        nativeHom.{u, v} n k ⊗ nativeHom.{u, v} k l ⟶ nativeHom.{u, v} n l) =>
      fun r n k l : I => Φ (n ⊗ r) (k ⊗ r) (l ⊗ r))
    nativeComposition_original_function.{u, v}.symm)

set_option backward.isDefEq.respectTransparency false in
/-- The entire native composition equation TYPE is transported through actual full fields. -/
theorem originalNativeComposition_condition_type_eq :
    FullShiftCompositionEquationTransport.Condition
      (FullShiftCompositionEquationTransport.maps symmetricOperatorObj.{u, v}
        originalShiftObjects.{u, v} originalShiftMaps.{u, v})
      (FullShiftCompositionEquationTransport.sourceComposition
        (V := PointedCGWH.{u, v}) symmetricOperatorObj.{u, v})
      (FullShiftCompositionEquationTransport.targetComposition
        (V := PointedCGWH.{u, v}) symmetricOperatorObj.{u, v} originalShiftObjects.{u, v}) =
    FullShiftCompositionEquationTransport.Condition originalNativeShiftMapFields.{u, v}
      nativeComposition.{u, v} originalNativeShiftTargetCompositionFields.{u, v} :=
  FullShiftCompositionEquationTransport.condition_type_eq
    (FullShiftCompositionEquationTransport.maps symmetricOperatorObj originalShiftObjects
      originalShiftMaps) originalNativeShiftMapFields
    (FullShiftCompositionEquationTransport.sourceComposition
      (V := PointedCGWH.{u, v}) symmetricOperatorObj) nativeComposition
    (FullShiftCompositionEquationTransport.targetComposition
      (V := PointedCGWH.{u, v}) symmetricOperatorObj originalShiftObjects)
    originalNativeShiftTargetCompositionFields
    originalNativeComposition_source_objects_function
    originalNativeComposition_target_objects_function originalNativeComposition_map_fields_heq
    originalNativeComposition_source_fields_heq originalNativeComposition_target_fields_heq

set_option backward.isDefEq.respectTransparency false in
/-- The complete original native composition function is proved before its operator inputs. -/
theorem originalNativeComposition_condition_proof :
    FullShiftCompositionEquationTransport.Condition originalNativeShiftMapFields.{u, v}
      nativeComposition.{u, v} originalNativeShiftTargetCompositionFields.{u, v} :=
  Eq.mp originalNativeComposition_condition_type_eq.{u, v}
    (FullShiftCompositionEquationTransport.restricted_condition_proof
      symmetricOperatorObj.{u, v} originalShiftObjects.{u, v} originalShiftMaps.{u, v}
      originalShift_composition_condition_proof.{u, v})

set_option backward.isDefEq.respectTransparency false in
/-- The whole actual native composition equation supplies its complete dependent proof fields. -/
theorem originalNativeComposition_proof_field_function :
    FullShiftCompositionEquationTransport.ProofFields originalNativeShiftMapFields.{u, v}
      nativeComposition.{u, v} originalNativeShiftTargetCompositionFields.{u, v} :=
  FullShiftCompositionEquationTransport.proof_fields_of_condition
    originalNativeShiftMapFields.{u, v} nativeComposition.{u, v}
    originalNativeShiftTargetCompositionFields.{u, v}
    originalNativeComposition_condition_proof.{u, v}

/-- Extend the final block by the actual enriched Hom map, with both original operator laws. -/
def indexShift (r : I) :
    EnrichedFunctor PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v}
      SymmetricOperatorIndex.{u, v} where
  obj := originalShiftObjects.{u, v} r
  map := originalShiftMaps.{u, v} r
  map_id := originalShift_identity_proof_field_function.{u, v} r
  map_comp := originalShift_composition_proof_field_function.{u, v} r

/-- The whole native operator shift is literal enriched restriction along that actual index map. -/
def functor (r : I) :
    EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v} ⥤
      EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v} :=
  EnrichedFunctorCat.restriction (indexShift.{u, v} r)

/-- Every level is the original operator-functor value at the final-block shifted object. -/
theorem functor_obj (r n : I)
    (E : EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v}) :
    ((functor.{u, v} r).obj E).toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} n) =
      E.toEnrichedFunctor.obj (symmetricOperatorObj.{u, v} (n ⊗ r)) := rfl

/-- Every full original Hom action is its actual coend shift followed by the original action. -/
theorem functor_fullHom (r n k : I)
    (E : EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v}) :
    ((functor.{u, v} r).obj E).toEnrichedFunctor.map
        (symmetricOperatorObj.{u, v} n) (symmetricOperatorObj.{u, v} k) =
      hom.{u, v} r n k ≫ E.toEnrichedFunctor.map
        (symmetricOperatorObj.{u, v} (n ⊗ r)) (symmetricOperatorObj.{u, v} (k ⊗ r)) := rfl

/-- Every entire native transformation keeps its original shifted level component. -/
theorem functor_map_component (r n : I)
    {E E' : EnrichedFunctorCat PointedCGWH.{u, v} SymmetricOperatorIndex.{u, v}}
    (f : E ⟶ E') :
    component ((functor.{u, v} r).map f) (symmetricOperatorObj.{u, v} n) =
      component f (symmetricOperatorObj.{u, v} (n ⊗ r)) :=
  EnrichedFunctorCat.restrictionMap_component (indexShift.{u, v} r) f _

/-- Forgetting the point acts on the entire proved original composition function. -/
theorem originalNativeComposition_underlying_function :
    (fun r n k l : I =>
      ((FullShiftCompositionEquationTransport.sourceComposite
        originalNativeShiftMapFields.{u, v} nativeComposition.{u, v}) r n k l).right) =
    fun r n k l : I =>
      ((FullShiftCompositionEquationTransport.targetComposite
        originalNativeShiftMapFields.{u, v}
        originalNativeShiftTargetCompositionFields.{u, v}) r n k l).right :=
  congrArg
    (fun (Φ : ∀ r n k l : I,
        originalNativeShiftHomObjects.{u, v} n k ⊗ originalNativeShiftHomObjects.{u, v} k l ⟶
          originalNativeShiftTargetHomObjects.{u, v} r n l) =>
      fun r n k l : I => (Φ r n k l).right)
    originalNativeComposition_condition_proof.{u, v}

/-- Apply only the already compiled full original native proof-field function. -/
private theorem nativeComposition_shift (r n k l : I) :
    nativeComposition.{u, v} n k l ≫ hom.{u, v} r n l =
      (hom.{u, v} r n k ⊗ₘ hom.{u, v} r k l) ≫
        nativeComposition.{u, v} (n ⊗ r) (k ⊗ r) (l ⊗ r) := by
  apply CategoryTheory.Under.UnderMorphism.ext
  exact congrFun (congrFun (congrFun (congrFun
    originalNativeComposition_underlying_function.{u, v} r) n) k) l

/-- The actual original operator shift preserves the complete enriched composition function. -/
theorem hom_composition (r n k l : I) :
    let c : ∀ n₀ k₀ l₀ : I,
      nativeHom.{u, v} n₀ k₀ ⊗ nativeHom.{u, v} k₀ l₀ ⟶ nativeHom.{u, v} n₀ l₀ :=
      fun n₀ k₀ l₀ => eComp PointedCGWH.{u, v}
        (symmetricOperatorObj.{u, v} n₀) (symmetricOperatorObj.{u, v} k₀)
        (symmetricOperatorObj.{u, v} l₀)
    c n k l ≫ hom.{u, v} r n l =
      (hom.{u, v} r n k ⊗ₘ hom.{u, v} r k l) ≫ c (n ⊗ r) (k ⊗ r) (l ⊗ r) := by
  intro c
  have hOriginal : (nativeComposition.{u, v} : ∀ n₀ k₀ l₀ : I,
      nativeHom.{u, v} n₀ k₀ ⊗ nativeHom.{u, v} k₀ l₀ ⟶ nativeHom.{u, v} n₀ l₀) = c :=
    nativeComposition_original_function
  have hLeft := congrArg
    (fun (φ : ∀ n₀ k₀ l₀ : I,
      nativeHom.{u, v} n₀ k₀ ⊗ nativeHom.{u, v} k₀ l₀ ⟶ nativeHom.{u, v} n₀ l₀) =>
      φ n k l ≫ hom.{u, v} r n l) hOriginal.symm
  have hRight := congrArg
    (fun (φ : ∀ n₀ k₀ l₀ : I,
      nativeHom.{u, v} n₀ k₀ ⊗ nativeHom.{u, v} k₀ l₀ ⟶ nativeHom.{u, v} n₀ l₀) =>
      (hom.{u, v} r n k ⊗ₘ hom.{u, v} r k l) ≫ φ (n ⊗ r) (k ⊗ r) (l ⊗ r)) hOriginal
  exact hLeft.trans ((nativeComposition_shift.{u, v} r n k l).trans hRight)


end SymmetricShift
end PointedCGWH
