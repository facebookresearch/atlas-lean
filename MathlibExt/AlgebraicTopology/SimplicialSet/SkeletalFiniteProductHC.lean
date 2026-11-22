/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.SkeletalProductSharp
import MathlibExt.AlgebraicTopology.SimplicialSet.CompatiblePushoutHCTransport
import MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialDiagonalWeakEquivalence

/-!
# Homotopy-cartesian squares with finite simplex factors

Original HC squares with an actual finite simplex/boundary factor.

The ordinary weak comparison is multiplied by the finite factor using the
existing native theorem, then the actual product-pullback Iso identifies it
with the original product-square lift. Product Sharp is separately derived.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SSet.RezkSkeletalProduct
open SharpComparisonDraft RezkCompatiblePushout

/-- The actual chosen product-pullback Iso, with both ORIGINAL finite-factor coordinates. -/
def pullbackProductIso {X Y Z : SSet.{u}} (p : X ⟶ Z) (g : Y ⟶ Z) (K : SSet.{u}) :
    pullback p g ⨯ K ≅ pullback (prod.map p (𝟙 K)) (prod.map g (𝟙 K)) where
  hom := pullback.lift (prod.map (pullback.fst p g) (𝟙 K))
    (prod.map (pullback.snd p g) (𝟙 K)) (by
      apply prod.hom_ext
      · simpa only [Category.assoc, prod.map_fst, prod.map_fst_assoc] using
          congrArg (fun z => (prod.fst : pullback p g ⨯ K ⟶ pullback p g) ≫ z)
            (pullback.condition (f := p) (g := g))
      · simp)
  inv := prod.lift
    (pullback.lift (pullback.fst _ _ ≫ prod.fst) (pullback.snd _ _ ≫ prod.fst) (by
      simpa only [Category.assoc, prod.map_fst, prod.map_fst_assoc] using
        congrArg (fun z => z ≫ prod.fst)
          (pullback.condition (f := prod.map p (𝟙 K)) (g := prod.map g (𝟙 K)))))
    (pullback.fst _ _ ≫ prod.snd)
  hom_inv_id := by
    apply prod.hom_ext
    · apply pullback.hom_ext <;> simp [Category.assoc]
    · simp
  inv_hom_id := by
    apply pullback.hom_ext
    · apply prod.hom_ext <;> simp [Category.assoc]
    · apply prod.hom_ext
      · simp [Category.assoc]
      · simpa only [Category.assoc, prod.map_snd, prod.map_snd_assoc, Category.comp_id,
          Category.id_comp, prod.lift_snd, pullback.lift_snd] using
          congrArg (fun z => z ≫ prod.snd)
            (pullback.condition (f := prod.map p (𝟙 K)) (g := prod.map g (𝟙 K)))

/-- The actual original HC square stays HC with every finite cell factor,
including a simplex boundary. No product-HC or comparison-fibration outcome is supplied. -/
theorem finite_product_hc {A X B Y K : SSet.{u}}
    {f : A ⟶ X} {s : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
    (sq : CommSq f s p g) (hp : Sharp p) [K.Finite]
    (hc : WeakEquivalence (pullback.lift f s sq.w ≫ comparison p g)) :
    WeakEquivalence
      (pullback.lift (prod.map f (𝟙 K)) (prod.map s (𝟙 K)) (by
        apply prod.hom_ext
        · simpa only [Category.assoc, prod.map_fst, prod.map_fst_assoc] using
            congrArg (fun z => (prod.fst : A ⨯ K ⟶ A) ≫ z) sq.w
        · simp) ≫ comparison (prod.map p (𝟙 K)) (prod.map g (𝟙 K))) := by
  let c := pullback.lift f s sq.w
  have wc : WeakEquivalence c := (hc_iff_ordinaryLift_weak sq hp).mp hc
  have wprod : WeakEquivalence (prod.map c (𝟙 K)) := by
    apply (HomotopicalAlgebra.weakEquivalence_iff _).2
    exact realizationWeakEquivalences.prodMap_id_of_finite_right c
      ((HomotopicalAlgebra.weakEquivalence_iff _).1 wc)
  let e := pullbackProductIso p g K
  have fac : prod.map c (𝟙 K) ≫ e.hom =
      pullback.lift (prod.map f (𝟙 K)) (prod.map s (𝟙 K)) (by
        apply prod.hom_ext
        · simpa only [Category.assoc, prod.map_fst, prod.map_fst_assoc] using
            congrArg (fun z => (prod.fst : A ⨯ K ⟶ A) ≫ z) sq.w
        · simp) := by
    apply pullback.hom_ext <;> apply prod.hom_ext <;>
        simp [e, c, pullbackProductIso, Category.assoc]
  have ordinaryWeak : WeakEquivalence
      (pullback.lift (f := prod.map p (𝟙 K)) (g := prod.map g (𝟙 K))
        (prod.map f (𝟙 K)) (prod.map s (𝟙 K)) (by
        apply prod.hom_ext
        · simpa only [Category.assoc, prod.map_fst, prod.map_fst_assoc] using
            congrArg (fun z => (prod.fst : A ⨯ K ⟶ A) ≫ z) sq.w
        · simp)) := by
    let _ : WeakEquivalence (prod.map c (𝟙 K)) := wprod
    have hcomp : WeakEquivalence (prod.map c (𝟙 K) ≫ e.hom) := inferInstance
    exact fac ▸ hcomp
  let := ordinaryWeak
  let : WeakEquivalence (comparison (prod.map p (𝟙 K)) (prod.map g (𝟙 K))) :=
    product_map_sharp p K hp _ _
  infer_instance

end SSet.RezkSkeletalProduct
