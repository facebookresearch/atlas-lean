/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OperatorRestriction

/-!
# Whole source and target naturality of the original operator action

The entire enriched composition equation and the original zero-coefficient
arrow formulas imply naturality on the whole Hom objects.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.Spectra.Symmetric.OperatorCoend

local notation "I" => Operad.SmallFinBijGroupoid

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [MonoidalClosed V]
  {T : V}

/-- The entire actual enriched map of a coend representation. -/
def representationMap (X : Representation T) (n k : I) :
    Hom T n k ⟶ (ihom (representationObject X n)).obj (representationObject X k) :=
  MonoidalClosed.curry (representationAction X n k)

/-- The true whole enriched composition law is inherited from the actual representation. -/
theorem representationMap_comp (X : Representation T) (n k l : I) :
    composition T n k l ≫ representationMap X n l =
      (representationMap X n k ⊗ₘ representationMap X k l) ≫
        MonoidalClosed.comp (representationObject X n) (representationObject X k) (representationObject X l) := by
  let _ : EnrichedCategory V I := enrichedCategory T
  exact X.toEnrichedFunctor.map_comp n k l

/-- The entire enriched map transposes to the original whole Hom action. -/
theorem representationMap_uncurry (X : Representation T) (n k : I) :
    MonoidalClosed.uncurry (representationMap X n k) = representationAction X n k :=
  MonoidalClosed.uncurry_curry _

/-- All original index maps decode by the original complete degree-zero coefficient. -/
theorem ordinaryDiagram_map_enriched (X : Representation T) {n k : I} (f : n ⟶ k) :
    MonoidalClosed.curry' ((ordinaryDiagram X).map f) = arrow T f ≫ representationMap X n k := by
  have h : (ordinaryDiagram X).map f =
      MonoidalClosed.uncurry' (arrow T f ≫ representationMap X n k) := by
    rw [MonoidalClosed.uncurry', MonoidalClosed.uncurry_natural_left, representationMap_uncurry]
    exact ordinaryDiagram_map X f
  exact (congrArg MonoidalClosed.curry' h).trans (MonoidalClosed.curry'_uncurry' _)

omit [MonoidalClosed V] in
/-- The whole original source Hom map is its complete enriched arrow-composition map. -/
theorem sourceMap_arrow_formula (T : V) {n k : I} (f : n ⟶ k) (l : I) :
    sourceMap T f l = (λ_ (Hom T k l)).inv ≫ (arrow T f ▷ Hom T k l) ≫ composition T n k l := by
  have h := congrArg (fun t => (λ_ (Hom T k l)).inv ≫ t) (arrow_composition_sourceMap T f l)
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h.symm

omit [MonoidalClosed V] in
/-- The whole original target Hom map is its complete enriched arrow-composition map. -/
theorem targetMap_arrow_formula (T : V) (n : I) {k l : I} (f : k ⟶ l) :
    targetMap T n f = (ρ_ (Hom T n k)).inv ≫ (Hom T n k ◁ arrow T f) ≫ composition T n k l := by
  have h := congrArg (fun t => (ρ_ (Hom T n k)).inv ≫ t) (composition_arrow_targetMap T n f)
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h.symm

/-- Every source index map is natural on the entire enriched map object. -/
theorem representationMap_source (X : Representation T) {n k : I} (f : n ⟶ k) (l : I) :
    sourceMap T f l ≫ representationMap X n l =
      representationMap X k l ≫ (MonoidalClosed.pre ((ordinaryDiagram X).map f)).app
        (representationObject X l) := by
  let H := Hom T k l
  let M := (ihom (representationObject X k)).obj (representationObject X l)
  let p := arrow T f ≫ representationMap X n k
  let r : representationObject X n ⟶ representationObject X k := (ordinaryDiagram X).map f
  have hPoint : MonoidalClosed.curry' r = p := ordinaryDiagram_map_enriched X f
  have hPair : (arrow T f ▷ H) ≫ (representationMap X n k ⊗ₘ representationMap X k l) =
      p ⊗ₘ representationMap X k l := whiskerRight_comp_tensorHom _ _ _
  have hUnit : (λ_ H).inv ≫ (p ⊗ₘ representationMap X k l) =
      representationMap X k l ≫ (λ_ M).inv ≫ (p ▷ M) := leftUnitor_inv_comp_tensorHom _ _
  have hWhisker : (λ_ M).inv ≫ (p ▷ M) ≫
      MonoidalClosed.comp (representationObject X n) (representationObject X k) (representationObject X l) =
      (MonoidalClosed.pre r).app (representationObject X l) := by
    rw [← hPoint, MonoidalClosed.curry'_whiskerRight_comp, Iso.inv_hom_id_assoc]
  rw [sourceMap_arrow_formula]
  simp only [Category.assoc]
  rw [representationMap_comp]
  slice_lhs 2 3 => rw [hPair]
  slice_lhs 1 2 => rw [hUnit]
  simp only [Category.assoc]
  slice_lhs 2 4 => exact hWhisker
  rfl

/-- Every target index map is natural on the entire enriched map object. -/
theorem representationMap_target (X : Representation T) (n : I) {k l : I} (f : k ⟶ l) :
    targetMap T n f ≫ representationMap X n l =
      representationMap X n k ≫ (ihom (representationObject X n)).map ((ordinaryDiagram X).map f) := by
  let H := Hom T n k
  let M := (ihom (representationObject X n)).obj (representationObject X k)
  let p := arrow T f ≫ representationMap X k l
  let r : representationObject X k ⟶ representationObject X l := (ordinaryDiagram X).map f
  have hPoint : MonoidalClosed.curry' r = p := ordinaryDiagram_map_enriched X f
  have hPair : (H ◁ arrow T f) ≫ (representationMap X n k ⊗ₘ representationMap X k l) =
      representationMap X n k ⊗ₘ p := whiskerLeft_comp_tensorHom _ _ _
  have hUnit : (ρ_ H).inv ≫ (representationMap X n k ⊗ₘ p) =
      representationMap X n k ≫ (ρ_ M).inv ≫ (M ◁ p) := rightUnitor_inv_comp_tensorHom _ _
  have hWhisker : (ρ_ M).inv ≫ (M ◁ p) ≫
      MonoidalClosed.comp (representationObject X n) (representationObject X k) (representationObject X l) =
      (ihom (representationObject X n)).map r := by
    rw [← hPoint, MonoidalClosed.whiskerLeft_curry'_comp, Iso.inv_hom_id_assoc]
  rw [targetMap_arrow_formula]
  simp only [Category.assoc]
  rw [representationMap_comp]
  slice_lhs 2 3 => rw [hPair]
  slice_lhs 1 2 => rw [hUnit]
  simp only [Category.assoc]
  slice_lhs 2 4 => exact hWhisker
  rfl

/-- Every source index map is natural on the entire genuine coend action. -/
theorem representationAction_source (X : Representation T) {n k : I} (f : n ⟶ k) (l : I) :
    ((ordinaryDiagram X).map f ▷ Hom T k l) ≫ representationAction X k l =
      (representationObject X n ◁ sourceMap T f l) ≫ representationAction X n l := by
  let r : representationObject X n ⟶ representationObject X k := (ordinaryDiagram X).map f
  have hn : sourceMap T f l ≫ representationMap X n l =
      representationMap X k l ≫ (MonoidalClosed.pre r).app (representationObject X l) :=
    representationMap_source X f l
  have h := congrArg MonoidalClosed.uncurry hn
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_pre_app,
    representationMap_uncurry, representationMap_uncurry] at h
  exact h.symm

/-- Every target index map is natural on the entire genuine coend action. -/
theorem representationAction_target (X : Representation T) (n : I) {k l : I} (f : k ⟶ l) :
    representationAction X n k ≫ (ordinaryDiagram X).map f =
      (representationObject X n ◁ targetMap T n f) ≫ representationAction X n l := by
  let r : representationObject X k ⟶ representationObject X l := (ordinaryDiagram X).map f
  have hn : targetMap T n f ≫ representationMap X n l =
      representationMap X n k ≫ (ihom (representationObject X n)).map r :=
    representationMap_target X n f
  have h := congrArg MonoidalClosed.uncurry hn
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_right,
    representationMap_uncurry, representationMap_uncurry] at h
  exact h.symm

end CategoryTheory.Spectra.Symmetric.OperatorCoend
