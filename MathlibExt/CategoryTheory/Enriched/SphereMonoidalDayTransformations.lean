/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.Functor
public import MathlibExt.CategoryTheory.Enriched.GradedYoneda

/-!
# Original sphere unit and tensorator as genuine enriched transformations

The stored enriched tensorator naturality gives the whole product-Hom
naturality equation. The original unit is extended by the literal graded
Yoneda supplier. These genuine transformations supply the native Day unit
and multiplication arrows before the remaining Day monoid laws are proved.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.SphereOperator

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)

attribute [local instance] Enriched.prodCategory

/-- The actual stored tensorator law is natural on the entire enriched product Hom. -/
theorem tensorator_full_naturality (a b : I × I) :
    MonoidalClosed.uncurry ((S.externalTensor S).map a b) ≫ L.mu b.1 b.2 =
      (L.mu a.1 a.2 ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry ((d.tensorEnrichedFunctor.comp V S).map a b) := by
  let E := S.externalTensor S
  let J := d.tensorEnrichedFunctor.comp V S
  let p := L.mu a.1 a.2
  let q := L.mu b.1 b.2
  let H : V := a ⟶[V] b
  let e := S.map a.1 b.1 ⊗ₘ S.map a.2 b.2
  let t := (MonoidalClosed.enrichedMonoidalCategoryDataSelf V).tensorMap
    (S.obj a.1) (S.obj b.1) (S.obj a.2) (S.obj b.2)
  let j := d.tensorMap a.1 b.1 a.2 b.2
  let u := S.map (a.1 ⊗ a.2) (b.1 ⊗ b.2)
  have hEValue : E.map a b = e ≫ t := rfl
  have hJValue : J.map a b = j ≫ u := rfl
  have hE : E.map a b ≫ eHomWhiskerLeft V (E.obj a) q =
      e ≫ t ≫ eHomWhiskerLeft V (E.obj a) q :=
    (congrArg (fun z => z ≫ eHomWhiskerLeft V (E.obj a) q) hEValue).trans
      (Category.assoc e t (eHomWhiskerLeft V (E.obj a) q))
  have hJ : J.map a b ≫ eHomWhiskerRight V p (J.obj b) =
      j ≫ u ≫ eHomWhiskerRight V p (J.obj b) :=
    (congrArg (fun z => z ≫ eHomWhiskerRight V p (J.obj b)) hJValue).trans
      (Category.assoc j u (eHomWhiskerRight V p (J.obj b)))
  have hMaps : E.map a b ≫ eHomWhiskerLeft V (E.obj a) q =
      J.map a b ≫ eHomWhiskerRight V p (J.obj b) :=
    hE.trans ((L.mu_naturality a.1 b.1 a.2 b.2).trans hJ.symm)
  have hLeft : MonoidalClosed.uncurry (E.map a b ≫ eHomWhiskerLeft V (E.obj a) q) =
      MonoidalClosed.uncurry (E.map a b) ≫ q :=
    (congrArg (fun z => MonoidalClosed.uncurry (E.map a b ≫ z))
      (MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft V (E.obj a) q)).trans
        (MonoidalClosed.uncurry_natural_right (E.map a b) q)
  have hRight : MonoidalClosed.uncurry (J.map a b ≫ eHomWhiskerRight V p (J.obj b)) =
      (p ⊗ₘ 𝟙 H) ≫ MonoidalClosed.uncurry (J.map a b) :=
    (congrArg (fun z => MonoidalClosed.uncurry (J.map a b ≫ z))
      (MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight V p (J.obj b))).trans
        ((MonoidalClosed.uncurry_pre_app (J.obj b) (J.map a b) p).trans
          (congrArg (fun z => z ≫ MonoidalClosed.uncurry (J.map a b))
            (tensorHom_id p H)).symm)
  exact hLeft.symm.trans ((congrArg MonoidalClosed.uncurry hMaps).trans hRight)

/-- The original tensorator is a genuine full product-enriched transformation. -/
def tensoratorTransformation :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
      (S.externalTensor S) (d.tensorEnrichedFunctor.comp V S) :=
  GradedNatTrans.unitOfComponents (fun a => L.mu a.1 a.2)
    (tensorator_full_naturality d S L)

/-- Every actual tensorator component is the literal original selected mu. -/
theorem tensoratorTransformation_component (a : I × I) :
    (eHomEquiv V).symm ((tensoratorTransformation d S L).app a) = L.mu a.1 a.2 :=
  GradedNatTrans.unitOfComponents_component _ _ a

/-- The whole tensorator component function retains all original tensorator values. -/
theorem tensoratorTransformation_component_function :
    (fun a : I × I => (eHomEquiv V).symm ((tensoratorTransformation d S L).app a)) =
      (fun a : I × I => L.mu a.1 a.2) := by
  funext a
  exact tensoratorTransformation_component d S L a

/-- Extend the original unit by the actual original graded Yoneda supplier. -/
def sphereUnitTransformation :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
      (GradedYoneda.representable (V := V) (𝟙_ I)) S :=
  GradedYoneda.extend (𝟙_ I) S L.epsilon

/-- The complete unit value is the same literal graded Yoneda extension call. -/
theorem sphereUnitTransformation_eq_extend :
    sphereUnitTransformation d S L = GradedYoneda.extend (𝟙_ I) S L.epsilon := rfl

/-- Every entire unit component retains the original epsilon and full source Hom action. -/
theorem sphereUnitTransformation_component (k : I) :
    (eHomEquiv V).symm ((sphereUnitTransformation d S L).app k) =
      GradedYoneda.component (𝟙_ I) S L.epsilon k :=
  GradedYoneda.extend_component (𝟙_ I) S L.epsilon k

/-- The unit component at the enriched identity recovers the actual original epsilon. -/
theorem sphereUnitTransformation_evaluate :
    GradedYoneda.evaluate (𝟙_ I) S (sphereUnitTransformation d S L) = L.epsilon :=
  GradedYoneda.evaluate_extend (𝟙_ I) S L.epsilon

end CategoryTheory.Enriched.SphereOperator
