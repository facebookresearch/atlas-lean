/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.Products
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Cartesian monoidal structure on compactly generated weak Hausdorff spaces

The chosen finite products from `CGWH.Products` determine the cartesian
monoidal structure on `CGWH`. The selected tensor has a canonical equivalence
of underlying carriers with the product of the two carriers. This is not a
homeomorphism statement and does not identify the tensor topology with the
ordinary product topology.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CGWH

/-- The cartesian monoidal structure selected by the native finite products. -/
noncomputable instance instCartesianMonoidalCategory :
    CartesianMonoidalCategory CGWH.{u, v} :=
  CartesianMonoidalCategory.ofHasFiniteProducts

/-- The canonical isomorphism from the selected cartesian tensor to the selected binary product.
This compares two categorical presentations of the same finite-product object; it does not
identify either topology with the ordinary product topology on carriers. -/
noncomputable abbrev tensorSelectedProductIso (A Y : CGWH.{u, v}) :
    A ⊗ Y ≅ A ⨯ Y :=
  (CartesianMonoidalCategory.tensorLeftIsoProd A).app Y

/-- The forward tensor-to-selected-product isomorphism preserves first projection. -/
@[reassoc]
theorem tensorSelectedProductIso_hom_fst (A Y : CGWH.{u, v}) :
    (tensorSelectedProductIso A Y).hom ≫ Limits.prod.fst =
      CartesianMonoidalCategory.fst A Y := by
  change (IsLimit.conePointUniqueUpToIso
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct A Y)
      (limit.isLimit (Limits.pair A Y))).hom ≫ Limits.prod.fst = _
  exact IsLimit.conePointUniqueUpToIso_hom_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct A Y)
    (limit.isLimit (Limits.pair A Y)) ⟨WalkingPair.left⟩

/-- The forward tensor-to-selected-product isomorphism preserves second projection. -/
@[reassoc]
theorem tensorSelectedProductIso_hom_snd (A Y : CGWH.{u, v}) :
    (tensorSelectedProductIso A Y).hom ≫ Limits.prod.snd =
      CartesianMonoidalCategory.snd A Y := by
  change (IsLimit.conePointUniqueUpToIso
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct A Y)
      (limit.isLimit (Limits.pair A Y))).hom ≫ Limits.prod.snd = _
  exact IsLimit.conePointUniqueUpToIso_hom_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct A Y)
    (limit.isLimit (Limits.pair A Y)) ⟨WalkingPair.right⟩

/-- The inverse selected-product-to-tensor isomorphism transports first projection back to the
selected product projection. -/
@[reassoc]
theorem tensorSelectedProductIso_inv_fst (A Y : CGWH.{u, v}) :
    (tensorSelectedProductIso A Y).inv ≫
        CartesianMonoidalCategory.fst A Y = Limits.prod.fst := by
  calc
    _ = (tensorSelectedProductIso A Y).inv ≫
        ((tensorSelectedProductIso A Y).hom ≫ Limits.prod.fst) :=
      congrArg ((tensorSelectedProductIso A Y).inv ≫ ·)
        (tensorSelectedProductIso_hom_fst A Y).symm
    _ = _ := (tensorSelectedProductIso A Y).inv_hom_id_assoc _

/-- The inverse selected-product-to-tensor isomorphism transports second projection back to the
selected product projection. -/
@[reassoc]
theorem tensorSelectedProductIso_inv_snd (A Y : CGWH.{u, v}) :
    (tensorSelectedProductIso A Y).inv ≫
        CartesianMonoidalCategory.snd A Y = Limits.prod.snd := by
  calc
    _ = (tensorSelectedProductIso A Y).inv ≫
        ((tensorSelectedProductIso A Y).hom ≫ Limits.prod.snd) :=
      congrArg ((tensorSelectedProductIso A Y).inv ≫ ·)
        (tensorSelectedProductIso_hom_snd A Y).symm
    _ = _ := (tensorSelectedProductIso A Y).inv_hom_id_assoc _

/-- The canonical equivalence between the carrier of the selected CGWH tensor and the product of
the two carriers.  This is only a carrier equivalence: it does not assert that the selected tensor
topology is the ordinary product topology, nor does it define a homeomorphism. -/
noncomputable abbrev tensorEquivProd (A Y : CGWH.{u, v}) :
    (A ⊗ Y : CGWH.{u, v}) ≃ (A × Y) := by
  let eTensor := tensorSelectedProductIso A Y
  let f : (A ⊗ Y : CGWH.{u, v}) → (A × Y) :=
    fun z => (CartesianMonoidalCategory.fst A Y z,
      CartesianMonoidalCategory.snd A Y z)
  let g : (A ⊗ Y : CGWH.{u, v}) → (A × Y) :=
    fun z => prodComparisonToTop A Y (cgwhToTop.map eTensor.hom z)
  have hFst : eTensor.hom ≫ (Limits.prod.fst : A ⨯ Y ⟶ A) =
      CartesianMonoidalCategory.fst A Y := by
    exact tensorSelectedProductIso_hom_fst A Y
  have hSnd : eTensor.hom ≫ (Limits.prod.snd : A ⨯ Y ⟶ Y) =
      CartesianMonoidalCategory.snd A Y := by
    exact tensorSelectedProductIso_hom_snd A Y
  have hfg : f = g := by
    funext z
    dsimp only [f, g]
    apply Prod.ext
    · dsimp only [Prod.fst]
      have hComparison :
          (prodComparisonToTop A Y (cgwhToTop.map eTensor.hom z)).1 =
            (Limits.prod.fst : A ⨯ Y ⟶ A) (eTensor.hom z) :=
        ConcreteCategory.congr_hom (prodComparisonToTop_fst A Y) _
      exact (hComparison.trans (ConcreteCategory.congr_hom hFst z)).symm
    · dsimp only [Prod.snd]
      have hComparison :
          (prodComparisonToTop A Y (cgwhToTop.map eTensor.hom z)).2 =
            (Limits.prod.snd : A ⨯ Y ⟶ Y) (eTensor.hom z) :=
        ConcreteCategory.congr_hom (prodComparisonToTop_snd A Y) _
      exact (hComparison.trans (ConcreteCategory.congr_hom hSnd z)).symm
  refine Equiv.ofBijective f ?_
  rw [hfg]
  exact (prodComparisonToTop_bijective A Y).comp
    (homeoOfIso eTensor).bijective

/-- The first coordinate of the canonical tensor carrier equivalence is the selected cartesian
first projection. -/
@[simp]
theorem tensorEquivProd_apply_fst (A Y : CGWH.{u, v})
    (z : (A ⊗ Y : CGWH.{u, v})) :
    (tensorEquivProd A Y z).1 =
      (CartesianMonoidalCategory.fst A Y) z :=
  rfl

/-- The second coordinate of the canonical tensor carrier equivalence is the selected cartesian
second projection. -/
@[simp]
theorem tensorEquivProd_apply_snd (A Y : CGWH.{u, v})
    (z : (A ⊗ Y : CGWH.{u, v})) :
    (tensorEquivProd A Y z).2 =
      (CartesianMonoidalCategory.snd A Y) z :=
  rfl

/-- The canonical tensor carrier equivalence is natural in both variables. -/
theorem tensorEquivProd_map {A Y A' Y' : CGWH.{u, v}}
    (f : A ⟶ A') (g : Y ⟶ Y') (z : (A ⊗ Y : CGWH.{u, v})) :
    tensorEquivProd A' Y' ((f ⊗ₘ g) z) =
      (f (tensorEquivProd A Y z).1, g (tensorEquivProd A Y z).2) := by
  apply Prod.ext
  · dsimp only [Prod.fst]
    rw [tensorEquivProd_apply_fst, tensorEquivProd_apply_fst]
    exact ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.tensorHom_fst f g) z
  · dsimp only [Prod.snd]
    rw [tensorEquivProd_apply_snd, tensorEquivProd_apply_snd]
    exact ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.tensorHom_snd f g) z

/-- The canonical tensor carrier equivalence agrees with the native product comparison. -/
theorem tensorEquivProd_eq_prodComparisonToTop (A B : CGWH.{u, v})
    (z : (A ⊗ B : CGWH.{u, v})) :
    tensorEquivProd A B z = prodComparisonToTop A B z := by
  apply Prod.ext
  · exact (ConcreteCategory.congr_hom (prodComparisonToTop_fst A B) z).symm
  · exact (ConcreteCategory.congr_hom (prodComparisonToTop_snd A B) z).symm

/-- The inverse canonical tensor carrier equivalence is natural in both variables. -/
theorem tensorEquivProd_symm_map {A B A' B' : CGWH.{u, v}}
    (f : A ⟶ A') (g : B ⟶ B') (a : A) (b : B) :
    (f ⊗ₘ g) ((tensorEquivProd A B).symm (a, b)) =
      (tensorEquivProd A' B').symm (f a, g b) := by
  apply (tensorEquivProd A' B').injective
  rw [(tensorEquivProd A' B').apply_symm_apply,
    tensorEquivProd_map, (tensorEquivProd A B).apply_symm_apply]

/-- The associator preserves the canonical tensor carrier equivalences. -/
theorem tensorEquivProd_associator (A B C : CGWH.{u, v})
    (z : ((A ⊗ B) ⊗ C : CGWH.{u, v})) :
    tensorEquivProd A (B ⊗ C) ((α_ A B C).hom z) =
      ((tensorEquivProd A B (tensorEquivProd (A ⊗ B) C z).1).1,
        (tensorEquivProd B C).symm
          ((tensorEquivProd A B (tensorEquivProd (A ⊗ B) C z).1).2,
            (tensorEquivProd (A ⊗ B) C z).2)) := by
  apply Prod.ext
  · change CartesianMonoidalCategory.fst A (B ⊗ C) ((α_ A B C).hom z) =
      CartesianMonoidalCategory.fst A B
        (CartesianMonoidalCategory.fst (A ⊗ B) C z)
    exact ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.associator_hom_fst A B C) z
  · apply (tensorEquivProd B C).injective
    rw [(tensorEquivProd B C).apply_symm_apply]
    apply Prod.ext
    · change CartesianMonoidalCategory.fst B C
          (CartesianMonoidalCategory.snd A (B ⊗ C) ((α_ A B C).hom z)) =
        CartesianMonoidalCategory.snd A B
          (CartesianMonoidalCategory.fst (A ⊗ B) C z)
      exact ConcreteCategory.congr_hom
        (CartesianMonoidalCategory.associator_hom_snd_fst A B C) z
    · change CartesianMonoidalCategory.snd B C
          (CartesianMonoidalCategory.snd A (B ⊗ C) ((α_ A B C).hom z)) =
        CartesianMonoidalCategory.snd (A ⊗ B) C z
      exact ConcreteCategory.congr_hom
        (CartesianMonoidalCategory.associator_hom_snd_snd A B C) z

/-- The associator carries canonical left-associated tensor points to right-associated ones. -/
theorem tensorEquivProd_symm_associator (A B C : CGWH.{u, v})
    (a : A) (b : B) (c : C) :
    (α_ A B C).hom
        ((tensorEquivProd (A ⊗ B) C).symm ((tensorEquivProd A B).symm (a, b), c)) =
      (tensorEquivProd A (B ⊗ C)).symm
        (a, (tensorEquivProd B C).symm (b, c)) := by
  apply (tensorEquivProd A (B ⊗ C)).injective
  rw [(tensorEquivProd A (B ⊗ C)).apply_symm_apply, tensorEquivProd_associator,
    (tensorEquivProd (A ⊗ B) C).apply_symm_apply,
    (tensorEquivProd A B).apply_symm_apply]

/-- Pair two points into the carrier of the chosen CGWH tensor. -/
noncomputable def tensorMk {A B : CGWH.{u, v}} (a : A) (b : B) :
    (A ⊗ B : CGWH.{u, v}) :=
  (tensorEquivProd A B).symm (a, b)

/-- The canonical tensor carrier equivalence recovers paired points.

Kept out of the simp set: it follows from `tensorMk_fst` and
`tensorMk_snd`, so tagging it would trip the simp normal-form linter. -/
theorem tensorEquivProd_tensorMk {A B : CGWH.{u, v}} (a : A) (b : B) :
    tensorEquivProd A B (tensorMk a b) = (a, b) :=
  (tensorEquivProd A B).apply_symm_apply (a, b)

/-- First projection of a paired tensor point. -/
@[simp]
theorem tensorMk_fst {A B : CGWH.{u, v}} (a : A) (b : B) :
    CartesianMonoidalCategory.fst A B (tensorMk a b) = a :=
  congrArg Prod.fst (tensorEquivProd_tensorMk a b)

/-- Second projection of a paired tensor point. -/
@[simp]
theorem tensorMk_snd {A B : CGWH.{u, v}} (a : A) (b : B) :
    CartesianMonoidalCategory.snd A B (tensorMk a b) = b :=
  congrArg Prod.snd (tensorEquivProd_tensorMk a b)

/-- Tensor maps preserve paired tensor points. -/
theorem tensorMk_map {A B A' B' : CGWH.{u, v}}
    (f : A ⟶ A') (g : B ⟶ B') (a : A) (b : B) :
    (f ⊗ₘ g) (tensorMk a b) = tensorMk (f a) (g b) :=
  tensorEquivProd_symm_map f g a b

/-- Right whiskering preserves paired tensor points. -/
theorem tensorMk_whiskerRight {A A' B : CGWH.{u, v}}
    (f : A ⟶ A') (a : A) (b : B) :
    (f ▷ B) (tensorMk a b) = tensorMk (f a) b := by
  apply (tensorEquivProd A' B).injective
  rw [tensorEquivProd_tensorMk]
  apply Prod.ext
  · rw [tensorEquivProd_apply_fst]
    have h := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerRight_fst f B) (tensorMk a b)
    simp only [ConcreteCategory.comp_apply, tensorMk_fst] at h
    exact h
  · rw [tensorEquivProd_apply_snd]
    have h := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.whiskerRight_snd f B) (tensorMk a b)
    simp only [ConcreteCategory.comp_apply, tensorMk_snd] at h
    exact h

/-- Every tensor point is the pairing of its two projections. -/
theorem tensorMk_fst_snd {A B : CGWH.{u, v}}
    (z : (A ⊗ B : CGWH.{u, v})) :
    tensorMk (CartesianMonoidalCategory.fst A B z)
        (CartesianMonoidalCategory.snd A B z) = z := by
  apply (tensorEquivProd A B).injective
  rw [tensorEquivProd_tensorMk]
  apply Prod.ext
  · rw [tensorEquivProd_apply_fst]
  · rw [tensorEquivProd_apply_snd]

/-- The inverse associator reassociates paired tensor points. -/
theorem associator_inv_tensorMk {A B C : CGWH.{u, v}}
    (a : A) (b : B) (c : C) :
    (α_ A B C).inv (tensorMk a (tensorMk b c))
      = tensorMk (tensorMk a b) c := by
  have h := tensorEquivProd_symm_associator A B C a b c
  have hinv : ∀ p, (α_ A B C).inv ((α_ A B C).hom p) = p :=
    fun p => ConcreteCategory.congr_hom (α_ A B C).hom_inv_id p
  have h2 := congrArg (α_ A B C).inv h
  rw [hinv] at h2
  exact h2.symm

end CGWH
