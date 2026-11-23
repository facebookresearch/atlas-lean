/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed source port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/Algebra/Homology/Monoidal/Braiding.lean
Only module/namespace paths are adapted for Atlas; source operations and hypotheses are retained.
-/

public import MathlibExt.CategoryTheory.DGSource.CochainTensorSummands
public import MathlibExt.CategoryTheory.DGSource.MonoidalPreadditive

/-!
# The Koszul braiding on cochain complexes

Mathlib's `HomologicalComplex.monoidalCategory`, instantiated at `ComplexShape.up ℤ` and its
`ComplexShape.TensorSigns`, makes `CochainComplex C ℤ` monoidal by totalizing the
degreewise tensor product.  It does not make it braided: Mathlib's `GradedObject.braidedCategory`
uses the braiding of the base category on each summand with no sign, and that map does not commute
with the totalized differential.

Here `C` is any braided monoidal preadditive category with a zero object and the
coproduct and tensor-preservation hypotheses of Mathlib's totalized monoidal structure.
When the coefficient braiding is symmetric, so is the Koszul braiding.

This file supplies the missing sign.  On the bidegree-`(p, q)` summand of `X ⊗ Y` the braiding is
`(-1)^{p * q}` times the braiding of `C`. For modules, this is `x ⊗ y ↦ (-1)^{|x| * |y|} y ⊗ x` on
homogeneous elements.  The sign is forced: the totalized differential carries `ComplexShape.up ℤ`'s
tensor signs `ε₁ = 1` and `ε₂ (p, q) = (-1)^p`, and the two Leibniz terms match after transposing
exactly when the summand map is scaled by `(-1)^{p * q}`.

## Main definitions

* `MathlibExt.DGSource.koszulBraidingSummand`: the bidegree component of the braiding.
* `MathlibExt.DGSource.koszulBraidingHom`, `MathlibExt.DGSource.koszulBraiding`: the braiding `X ⊗ Y ⟶ Y ⊗ X` of cochain
  complexes and the isomorphism it underlies.
* `MathlibExt.DGSource.koszulBraidedCategory` and `MathlibExt.DGSource.koszulSymmetricCategory`: the `BraidedCategory`
  and `SymmetricCategory` instances on `CochainComplex C ℤ`.

## Main results

* `MathlibExt.DGSource.koszulBraidingHom_naturality_left` and `MathlibExt.DGSource.koszulBraidingHom_naturality_right`:
  the braiding is natural in each factor.
* `MathlibExt.DGSource.koszulBraidingHom_hexagon_forward` and `MathlibExt.DGSource.koszulBraidingHom_hexagon_reverse`: the
  two hexagon identities.
* `MathlibExt.DGSource.koszulBraidingHom_comp`: the braiding is symmetric.
* `MathlibExt.DGSource.ι_tensorμ`: on a homogeneous summand, the middle-four interchange
  `MonoidalCategory.tensorμ` of cochain complexes is that of `C`, with the Koszul sign of
  the two factors it exchanges.

The two auxiliary equations `HomologicalComplex.whiskerLeft_eq_mapBifunctorMap` and
`HomologicalComplex.whiskerRight_eq_mapBifunctorMap` of
`MathlibExt/CategoryTheory/DGSource/CochainTensorSummands.lean`, which record that the whiskerings of
`CochainComplex C ℤ` are `HomologicalComplex.mapBifunctorMap`, are used throughout.

For module-valued complexes, this braiding supplies the signs in Hom-complex composition
and in the tensor product and opposite of differential graded categories.

## Implementation notes

The hypotheses are the graded-object tensor existence and preservation classes used by
Mathlib's `HomologicalComplex.monoidalCategory`. In particular, modules over a commutative
ring satisfy them through their closed symmetric monoidal structure.

## References

* The totalized monoidal structure `HomologicalComplex.monoidalCategory` in
  `Mathlib/Algebra/Homology/Monoidal.lean`, by Joël Riou and Kim Morrison, and the unsigned
  `GradedObject.Monoidal.braiding` of `Mathlib/CategoryTheory/GradedObject/Braiding.lean`, by
  Joël Riou.  This file adds the Koszul sign and the complex-level axioms; nothing is vendored.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1, for the sign
  convention.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace MathlibExt.DGSource

variable (C : Type*) [Category* C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasZeroObject C]
  [∀ (X Y : GradedObject ℤ C), GradedObject.HasTensor X Y]
  [∀ X, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X)]
  [∀ (X Y Z : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X Y Z]

section Braided

variable [BraidedCategory C]

/-- The bidegree-`(p, q)` component of the Koszul braiding `X ⊗ Y ⟶ Y ⊗ X`: the braiding of
`C` on the summand `X.X p ⊗ Y.X q`, carrying the Koszul sign `(-1)^{p * q}`. -/
noncomputable def koszulBraidingSummand (X Y : CochainComplex C ℤ) (p q j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = j) :
    X.X p ⊗ Y.X q ⟶ (Y ⊗ X).X j :=
  (p * q).negOnePow • ((β_ (X.X p) (Y.X q)).hom ≫
    HomologicalComplex.ιMapBifunctor Y X (curriedTensor C)
      (ComplexShape.up ℤ) q p j (by dsimp at h ⊢; omega))

/-- The bidegree component of the Koszul braiding is the coefficient braiding, followed by
the inclusion of the swapped summand, and scaled by `(-1)^(p*q)`. -/
lemma koszulBraidingSummand_def (X Y : CochainComplex C ℤ) (p q j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = j) :
    koszulBraidingSummand C X Y p q j h =
      (p * q).negOnePow • ((β_ (X.X p) (Y.X q)).hom ≫
        HomologicalComplex.ιMapBifunctor Y X (curriedTensor C)
          (ComplexShape.up ℤ) q p j (by dsimp at h ⊢; omega)) :=
  (rfl)

private lemma koszulBraidingSummand_comm (X Y : CochainComplex C ℤ)
    (p q j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = j) :
    koszulBraidingSummand C X Y p q j h ≫ (Y ⊗ X).d j (j + 1) =
      HomologicalComplex.ιMapBifunctor X Y (curriedTensor C)
          (ComplexShape.up ℤ) p q j h ≫ (X ⊗ Y).d j (j + 1) ≫
        HomologicalComplex.mapBifunctorDesc (koszulBraidingSummand C X Y · · (j + 1) ·) := by
  replace h : p + q = j := h
  have hdYX : (Y ⊗ X).d j (j + 1) =
      HomologicalComplex.mapBifunctor.D₁ Y X (curriedTensor C)
          (ComplexShape.up ℤ) j (j + 1) +
        HomologicalComplex.mapBifunctor.D₂ Y X (curriedTensor C)
          (ComplexShape.up ℤ) j (j + 1) :=
    HomologicalComplex.mapBifunctor.d_eq _ _ _ _ j (j + 1)
  have hdXY : (X ⊗ Y).d j (j + 1) =
      HomologicalComplex.mapBifunctor.D₁ X Y (curriedTensor C)
          (ComplexShape.up ℤ) j (j + 1) +
        HomologicalComplex.mapBifunctor.D₂ X Y (curriedTensor C)
          (ComplexShape.up ℤ) j (j + 1) :=
    HomologicalComplex.mapBifunctor.d_eq _ _ _ _ j (j + 1)
  rw [hdYX, hdXY, koszulBraidingSummand]
  simp only [Preadditive.comp_add, Preadditive.add_comp, Linear.units_smul_comp,
    Category.assoc, HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.ι_D₁_assoc, HomologicalComplex.mapBifunctor.ι_D₂_assoc]
  rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (ComplexShape.up_mk q (q + 1) rfl) p (j + 1) (by dsimp; omega),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ q
      (ComplexShape.up_mk p (p + 1) rfl) (j + 1) (by dsimp; omega),
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (ComplexShape.up_mk p (p + 1) rfl) q (j + 1) (by dsimp; omega),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ p
      (ComplexShape.up_mk q (q + 1) rfl) (j + 1) (by dsimp; omega)]
  simp only [ComplexShape.ε₁_def, ComplexShape.ε₂_def, ComplexShape.ε_up_ℤ, one_smul,
    curriedTensor_map_app, curriedTensor_obj_map,
    Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc,
    HomologicalComplex.ι_mapBifunctorDesc, koszulBraidingSummand, smul_smul]
  have hs₁ : ((p + 1) * q).negOnePow = (p * q).negOnePow * q.negOnePow := by
    rw [show (p + 1) * q = p * q + q by ring, Int.negOnePow_add]
  have hs₂ : p.negOnePow * (p * (q + 1)).negOnePow = (p * q).negOnePow := by
    rw [show p * (q + 1) = p * q + p by ring, Int.negOnePow_add, ← mul_assoc,
      mul_comm p.negOnePow (p * q).negOnePow, mul_assoc, ← Int.negOnePow_add,
      Int.negOnePow_even _ ⟨p, rfl⟩, mul_one]
  rw [hs₁, hs₂, ← BraidedCategory.braiding_naturality_left_assoc,
    ← BraidedCategory.braiding_naturality_right_assoc]
  exact add_comm _ _

/-- The Koszul braiding `X ⊗ Y ⟶ Y ⊗ X`. -/
noncomputable def koszulBraidingHom (X Y : CochainComplex C ℤ) :
    X ⊗ Y ⟶ Y ⊗ X where
  f j := HomologicalComplex.mapBifunctorDesc (koszulBraidingSummand C X Y · · j ·)
  comm' j j' hjj' := by
    replace hjj' : j + 1 = j' := hjj'
    subst hjj'
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    rw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
    exact koszulBraidingSummand_comm C X Y p q j h

private lemma koszulBraidingHom_f (X Y : CochainComplex C ℤ) (j : ℤ) :
    (koszulBraidingHom C X Y).f j =
      HomologicalComplex.mapBifunctorDesc (koszulBraidingSummand C X Y · · j ·) :=
  rfl

@[reassoc (attr := simp)]
lemma ι_koszulBraidingHom (X Y : CochainComplex C ℤ) (p q j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = j) :
    HomologicalComplex.ιMapBifunctor X Y (curriedTensor C)
        (ComplexShape.up ℤ) p q j h ≫ (koszulBraidingHom C X Y).f j =
      koszulBraidingSummand C X Y p q j h := by
  rw [koszulBraidingHom_f]
  apply HomologicalComplex.ι_mapBifunctorDesc

/-- The Koszul braiding is natural in the left-hand factor. -/
lemma koszulBraidingHom_naturality_left {X Y : CochainComplex C ℤ} (f : X ⟶ Y)
    (Z : CochainComplex C ℤ) :
    f ▷ Z ≫ koszulBraidingHom C Y Z = koszulBraidingHom C X Z ≫ Z ◁ f := by
  ext j : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.whiskerRight_eq_mapBifunctorMap,
    HomologicalComplex.whiskerLeft_eq_mapBifunctorMap]
  simp only [HomologicalComplex.ι_mapBifunctorMap_assoc, ι_koszulBraidingHom_assoc,
    ι_koszulBraidingHom, koszulBraidingSummand, HomologicalComplex.id_f,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Category.assoc,
    Linear.units_smul_comp, Linear.comp_units_smul, HomologicalComplex.ι_mapBifunctorMap]
  simp only [curriedTensor_map_app, curriedTensor_obj_map]
  rw [BraidedCategory.braiding_naturality_left_assoc]

/-- The Koszul braiding is natural in the right-hand factor. -/
lemma koszulBraidingHom_naturality_right (X : CochainComplex C ℤ)
    {Y Z : CochainComplex C ℤ} (f : Y ⟶ Z) :
    X ◁ f ≫ koszulBraidingHom C X Z = koszulBraidingHom C X Y ≫ f ▷ X := by
  ext j : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.whiskerLeft_eq_mapBifunctorMap,
    HomologicalComplex.whiskerRight_eq_mapBifunctorMap]
  simp only [HomologicalComplex.ι_mapBifunctorMap_assoc, ι_koszulBraidingHom_assoc,
    ι_koszulBraidingHom, koszulBraidingSummand, HomologicalComplex.id_f,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Category.assoc,
    Linear.units_smul_comp, Linear.comp_units_smul, HomologicalComplex.ι_mapBifunctorMap]
  simp only [curriedTensor_map_app, curriedTensor_obj_map]
  rw [BraidedCategory.braiding_naturality_right_assoc]

/- Composing a left whiskering into the braiding summand: the braiding of `C` is natural,
so a map into the second factor passes through it and becomes a right whiskering.  Stating this
with a general `g` avoids rewriting under the two different spellings (`⊗` and
`HomologicalComplex.mapBifunctor`) of a totalized tensor product. -/
@[reassoc]
private lemma whiskerLeft_comp_koszulBraidingSummand (X W : CochainComplex C ℤ)
    (A : C) (p m j : ℤ) (g : A ⟶ W.X m)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, m) = j) :
    (X.X p ◁ g) ≫ koszulBraidingSummand C X W p m j h =
      (p * m).negOnePow • ((β_ (X.X p) A).hom ≫ (g ▷ X.X p) ≫
        HomologicalComplex.ιMapBifunctor W X (curriedTensor C)
          (ComplexShape.up ℤ) m p j (by dsimp at h ⊢; omega)) := by
  rw [koszulBraidingSummand, Linear.comp_units_smul,
    BraidedCategory.braiding_naturality_right_assoc]

/- The counterpart of `whiskerLeft_comp_koszulBraidingSummand` for a right whiskering. -/
@[reassoc]
private lemma whiskerRight_comp_koszulBraidingSummand (W X : CochainComplex C ℤ)
    (A : C) (m p j : ℤ) (g : A ⟶ W.X m)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (m, p) = j) :
    (g ▷ X.X p) ≫ koszulBraidingSummand C W X m p j h =
      (m * p).negOnePow • ((β_ A (X.X p)).hom ≫ (X.X p ◁ g) ≫
        HomologicalComplex.ιMapBifunctor X W (curriedTensor C)
          (ComplexShape.up ℤ) p m j (by dsimp at h ⊢; omega)) := by
  rw [koszulBraidingSummand, Linear.comp_units_smul,
    BraidedCategory.braiding_naturality_left_assoc]

section Hexagon

variable (X Y Z : CochainComplex C ℤ)

/- `ComplexShape.r` at `ComplexShape.up ℤ` is addition of the three degrees; Mathlib has no named
specialization reducing it. -/
private lemma up_r_eq {p q r j : ℤ}
    (h : ComplexShape.r (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q, r) = j) : p + q + r = j := h

private lemma up_r_of {p q r j : ℤ} (h : p + q + r = j) :
    ComplexShape.r (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q, r) = j := h

private lemma ι₁₂_hexagon_forward_lhs (p q r j : ℤ)
    (h : ComplexShape.r (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q, r) = j) :
    HomologicalComplex.mapBifunctor₁₂.ι (curriedTensor C)
        (curriedTensor C) X Y Z (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        p q r j h ≫
      ((α_ X Y Z).hom ≫ koszulBraidingHom C X (Y ⊗ Z) ≫ (α_ Y Z X).hom).f j =
      (p * (q + r)).negOnePow • ((α_ (X.X p) (Y.X q) (Z.X r)).hom ≫
        (β_ (X.X p) (Y.X q ⊗ Z.X r)).hom ≫ (α_ (Y.X q) (Z.X r) (X.X p)).hom ≫
          HomologicalComplex.mapBifunctor₂₃.ι (curriedTensor C)
            (curriedTensor C) Y Z X (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ) q r p j (up_r_of (by have := up_r_eq h; omega))) := by
  have h' := up_r_eq h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.mapBifunctor₁₂.ι_eq_whiskerRight X Y Z p q r (p + q) j rfl h',
    Category.assoc,
    HomologicalComplex.ι_ι_associator_hom_assoc _ _ _ p q r (p + q) (q + r) j rfl rfl h'
      (by omega),
    ι_koszulBraidingHom_assoc,
    whiskerLeft_comp_koszulBraidingSummand_assoc C X (Y ⊗ Z) _ p (q + r) j
      (HomologicalComplex.ιTensorObj Y Z q r (q + r) rfl)]
  simp only [Linear.units_smul_comp, Category.assoc]
  rw [HomologicalComplex.ι_ι_associator_hom Y Z X q r p (q + r) (r + p) j rfl rfl (by omega)
    (by omega), Linear.comp_units_smul,
    ← HomologicalComplex.mapBifunctor₂₃.ι_eq_whiskerLeft Y Z X q r p (r + p) j rfl (by omega)]

private lemma ι₁₂_hexagon_forward_rhs (p q r j : ℤ)
    (h : ComplexShape.r (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q, r) = j) :
    HomologicalComplex.mapBifunctor₁₂.ι (curriedTensor C)
        (curriedTensor C) X Y Z (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        p q r j h ≫
      ((koszulBraidingHom C X Y ▷ Z) ≫ (α_ Y X Z).hom ≫
        (Y ◁ koszulBraidingHom C X Z)).f j =
      (p * (q + r)).negOnePow • (((β_ (X.X p) (Y.X q)).hom ▷ Z.X r) ≫
        (α_ (Y.X q) (X.X p) (Z.X r)).hom ≫ (Y.X q ◁ (β_ (X.X p) (Z.X r)).hom) ≫
          HomologicalComplex.mapBifunctor₂₃.ι (curriedTensor C)
            (curriedTensor C) Y Z X (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ) q r p j (up_r_of (by have := up_r_eq h; omega))) := by
  have h' := up_r_eq h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.mapBifunctor₁₂.ι_eq_whiskerRight X Y Z p q r (q + p) j (by omega)
      (by omega),
    Category.assoc, HomologicalComplex.whiskerRight_eq_mapBifunctorMap,
    HomologicalComplex.ι_mapBifunctorMap_assoc]
  simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [curriedTensor_map_app]
  rw [← MonoidalCategory.comp_whiskerRight_assoc, ι_koszulBraidingHom, koszulBraidingSummand,
    Units.smul_def, ← tensorHom_id, zsmul_tensorHom, tensorHom_id, ← Units.smul_def,
    MonoidalCategory.comp_whiskerRight,
    Linear.units_smul_comp, Category.assoc,
    HomologicalComplex.ι_ι_associator_hom_assoc Y X Z q p r (q + p) (p + r) j rfl rfl
      (by omega) (by omega),
    HomologicalComplex.whiskerLeft_eq_mapBifunctorMap, HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp]
  simp only [curriedTensor_obj_map]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, ι_koszulBraidingHom, koszulBraidingSummand,
    Units.smul_def (p * r).negOnePow, ← id_tensorHom, tensorHom_zsmul, id_tensorHom,
    ← Units.smul_def,
    MonoidalCategory.whiskerLeft_comp,
    Linear.units_smul_comp, Category.assoc,
    ← HomologicalComplex.mapBifunctor₂₃.ι_eq_whiskerLeft Y Z X q r p (p + r) j (by omega)
      (by omega),
    Linear.comp_units_smul, Linear.comp_units_smul, smul_smul, ← Int.negOnePow_add,
    show p * q + p * r = p * (q + r) by ring]

/-- **The first hexagon identity** for the Koszul braiding. -/
lemma koszulBraidingHom_hexagon_forward :
    (α_ X Y Z).hom ≫ koszulBraidingHom C X (Y ⊗ Z) ≫ (α_ Y Z X).hom =
      (koszulBraidingHom C X Y ▷ Z) ≫ (α_ Y X Z).hom ≫ (Y ◁ koszulBraidingHom C X Z) := by
  ext j : 1
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro p q r h
  rw [ι₁₂_hexagon_forward_lhs, ι₁₂_hexagon_forward_rhs]
  congr 1
  simp only [← Category.assoc]
  congr 1
  simp only [Category.assoc]
  exact BraidedCategory.hexagon_forward (X.X p) (Y.X q) (Z.X r)

end Hexagon

private noncomputable def koszulBraidingInv (X Y : CochainComplex C ℤ) : Y ⊗ X ⟶ X ⊗ Y :=
  letI := reverseBraiding C
  koszulBraidingHom C Y X

@[reassoc]
private lemma ι_koszulBraidingInv (X Y : CochainComplex C ℤ) (q p j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (q, p) = j) :
    HomologicalComplex.ιMapBifunctor Y X (curriedTensor C)
        (ComplexShape.up ℤ) q p j h ≫ (koszulBraidingInv C X Y).f j =
      (q * p).negOnePow • ((β_ (X.X p) (Y.X q)).inv ≫
        HomologicalComplex.ιMapBifunctor X Y (curriedTensor C)
          (ComplexShape.up ℤ) p q j (by dsimp at h ⊢; omega)) := by
  dsimp only [koszulBraidingInv]
  rw [ι_koszulBraidingHom, koszulBraidingSummand_def]
  -- Under `reverseBraiding C`, the braiding `β_ (Y.X q) (X.X p)` is `(β_ (X.X p) (Y.X q)).symm`.
  -- It sits in an instance argument, which `dsimp` unfolds only with `+instances`.
  dsimp +instances only [reverseBraiding, Iso.symm_hom]

private lemma koszulBraidingHom_comp_inv (X Y : CochainComplex C ℤ) :
    koszulBraidingHom C X Y ≫ koszulBraidingInv C X Y = 𝟙 _ := by
  ext j : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  rw [HomologicalComplex.comp_f, ← Category.assoc, ι_koszulBraidingHom,
    koszulBraidingSummand, Linear.units_smul_comp, Category.assoc,
    ι_koszulBraidingInv, Linear.comp_units_smul, smul_smul, Iso.hom_inv_id_assoc]
  rw [mul_comm q p, ← Int.negOnePow_add, Int.negOnePow_even _ ⟨p * q, rfl⟩, one_smul,
    HomologicalComplex.id_f]
  exact (Category.comp_id _).symm

/-- Reversing the coefficient braiding twice gives back the original braiding, so the inverse
Koszul braiding built from the reversed braiding, with the factors swapped, is the original
forward Koszul braiding. Both sides agree by definition. -/
private lemma koszulBraidingInv_reverseBraiding (X Y : CochainComplex C ℤ) :
    (letI := reverseBraiding C; koszulBraidingInv C Y X) = koszulBraidingHom C X Y :=
  rfl

/-- The Koszul braiding of two cochain complexes in a braided coefficient category. -/
noncomputable def koszulBraiding (X Y : CochainComplex C ℤ) : X ⊗ Y ≅ Y ⊗ X where
  hom := koszulBraidingHom C X Y
  inv := koszulBraidingInv C X Y
  hom_inv_id := koszulBraidingHom_comp_inv C X Y
  inv_hom_id := by
    -- `hom ≫ inv = 𝟙` for the reversed braiding and the swapped complexes is this identity, once
    -- its inverse is identified with the original forward map.
    have h := (letI := reverseBraiding C; koszulBraidingHom_comp_inv C Y X)
    rw [koszulBraidingInv_reverseBraiding] at h
    dsimp only [koszulBraidingInv]
    exact h

/-- The forward direction of the Koszul braiding isomorphism. -/
@[simp]
lemma koszulBraiding_hom (X Y : CochainComplex C ℤ) :
    (koszulBraiding C X Y).hom = koszulBraidingHom C X Y :=
  (rfl)

/-- On a homogeneous summand, the inverse Koszul braiding is the inverse coefficient braiding
multiplied by the same Koszul sign. -/
@[reassoc (attr := simp)]
lemma ι_koszulBraiding_inv (X Y : CochainComplex C ℤ) (q p j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (q, p) = j) :
    HomologicalComplex.ιMapBifunctor Y X (curriedTensor C)
        (ComplexShape.up ℤ) q p j h ≫ (koszulBraiding C X Y).inv.f j =
      (q * p).negOnePow • ((β_ (X.X p) (Y.X q)).inv ≫
        HomologicalComplex.ιMapBifunctor X Y (curriedTensor C)
          (ComplexShape.up ℤ) p q j (by dsimp at h ⊢; omega)) :=
  ι_koszulBraidingInv C X Y q p j h

variable [∀ X, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X)]
  [∀ (W X Y Z : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt W X Y Z]

/-- **The second hexagon identity** for the Koszul braiding. -/
lemma koszulBraidingHom_hexagon_reverse (X Y Z : CochainComplex C ℤ) :
    (α_ X Y Z).inv ≫ koszulBraidingHom C (X ⊗ Y) Z ≫ (α_ Z X Y).inv =
      (X ◁ koszulBraidingHom C Y Z) ≫ (α_ X Z Y).inv ≫ (koszulBraidingHom C X Z ▷ Y) := by
  apply (Iso.inv_eq_inv
      ((α_ X Y Z).symm ≪≫ koszulBraiding C (X ⊗ Y) Z ≪≫ (α_ Z X Y).symm)
      (whiskerLeftIso X (koszulBraiding C Y Z) ≪≫ (α_ X Z Y).symm ≪≫
        whiskerRightIso (koszulBraiding C X Z) Y)).1
  -- The forward hexagon for the inverse coefficient braiding is the inverse of this hexagon.
  let := reverseBraiding C
  simpa only [Iso.trans_inv, Iso.symm_inv, whiskerLeftIso_inv, whiskerRightIso_inv,
    koszulBraiding, koszulBraidingInv, Category.assoc] using
    koszulBraidingHom_hexagon_forward C Z X Y

/-- Cochain complexes in `C` form a braided monoidal category under the Koszul braiding: on the
summand `X^p ⊗ Y^q` of Mathlib's totalized tensor product it is `(-1)^(p * q)` times the
coefficient braiding of `X^p` and `Y^q`. For complexes of modules, whose coefficient braiding is
the tensor flip, this is `x ⊗ y ↦ (-1)^{|x| * |y|} y ⊗ x`. -/
noncomputable instance koszulBraidedCategory :
    BraidedCategory (CochainComplex C ℤ) where
  braiding X Y := koszulBraiding C X Y
  braiding_naturality_right X _ _ f := by
    simp only [koszulBraiding_hom]
    exact koszulBraidingHom_naturality_right C X f
  braiding_naturality_left f Z := by
    simp only [koszulBraiding_hom]
    exact koszulBraidingHom_naturality_left C f Z
  hexagon_forward X Y Z := by
    simp only [koszulBraiding_hom]
    exact koszulBraidingHom_hexagon_forward C X Y Z
  hexagon_reverse X Y Z := by
    simp only [koszulBraiding_hom]
    exact koszulBraidingHom_hexagon_reverse C X Y Z

/-- The braiding of the monoidal category `CochainComplex C ℤ` is the Koszul
braiding. -/
lemma braiding_eq_koszulBraiding (X Y : CochainComplex C ℤ) :
    β_ X Y = koszulBraiding C X Y :=
  (rfl)

section TensorMu

/-- **The middle-four interchange on a homogeneous summand.**  On the summand
`(X₁.X a ⊗ X₂.X b) ⊗ (Y₁.X c ⊗ Y₂.X d)` of `(X₁ ⊗ X₂) ⊗ (Y₁ ⊗ Y₂)`, the interchange
`MonoidalCategory.tensorμ` of cochain complexes is the interchange of the four coefficient objects,
landing
in the summand `(X₁.X a ⊗ Y₁.X c) ⊗ (X₂.X b ⊗ Y₂.X d)`, with the Koszul sign `(-1)^(b * c)` of
moving the degree-`b` factor past the degree-`c` factor. -/
@[reassoc]
lemma ι_tensorμ (X₁ X₂ Y₁ Y₂ : CochainComplex C ℤ) (a b c d ab cd n : ℤ)
    (hab : a + b = ab) (hcd : c + d = cd) (h : ab + cd = n) :
    (HomologicalComplex.ιTensorObj X₁ X₂ a b ab hab ⊗ₘ
        HomologicalComplex.ιTensorObj Y₁ Y₂ c d cd hcd) ≫
        HomologicalComplex.ιTensorObj (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) ab cd n h ≫
          (tensorμ X₁ X₂ Y₁ Y₂).f n =
      (b * c).negOnePow • (tensorμ (X₁.X a) (X₂.X b) (Y₁.X c) (Y₂.X d) ≫
        (HomologicalComplex.ιTensorObj X₁ Y₁ a c (a + c) rfl ⊗ₘ
          HomologicalComplex.ιTensorObj X₂ Y₂ b d (b + d) rfl) ≫
          HomologicalComplex.ιTensorObj (X₁ ⊗ Y₁) (X₂ ⊗ Y₂) (a + c) (b + d) n (by omega)) := by
  subst hab hcd
  -- Follow the summand through the five factors of `tensorμ`.  The codomain of `ιTensorObj` is
  -- spelled `(HomologicalComplex.tensorObj K L).X j` rather than `(K ⊗ L).X j`, so the
  -- associator steps match the whiskered inclusions only up to unfolding the monoidal structure.
  simp only [tensorμ, HomologicalComplex.comp_f, tensorHom_def', Category.assoc]
  erw [HomologicalComplex.ι_ι_associator_hom_assoc X₁ X₂ (Y₁ ⊗ Y₂) a b (c + d)
    (a + b) (b + (c + d)) n rfl rfl h (by omega), associator_naturality_right_assoc]
  rw [HomologicalComplex.ι_whiskerLeft_assoc,
    ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc, Category.assoc,
    HomologicalComplex.ι_ι_associator_inv X₂ Y₁ Y₂ b c d (b + c) (c + d) _ rfl rfl (by omega) rfl,
    HomologicalComplex.ι_whiskerLeft_assoc, ← whiskerLeft_comp_assoc, Category.assoc,
    Category.assoc, HomologicalComplex.ι_whiskerRight, ← comp_whiskerRight_assoc,
    braiding_eq_koszulBraiding, koszulBraiding_hom, ι_koszulBraidingHom,
    koszulBraidingSummand_def]
  -- Pull the Koszul sign out of the whiskerings; what remains is sign-free.
  simp only [Units.smul_def, ← tensorHom_id, ← id_tensorHom, zsmul_tensorHom, tensorHom_zsmul,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  simp only [tensorHom_id, id_tensorHom]
  congr 1
  rw [HomologicalComplex.ι_whiskerLeft_assoc, ← whiskerLeft_comp_assoc, comp_whiskerRight]
  simp only [Category.assoc]
  erw [HomologicalComplex.ι_ι_associator_hom Y₁ X₂ Y₂ c b d
    (b + c) (b + d) (b + (c + d)) (by omega) rfl (by omega) (by omega)]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [HomologicalComplex.ι_ι_associator_inv X₁ Y₁ (X₂ ⊗ Y₂) a c (b + d) (a + c) (b + (c + d)) n
    rfl (by omega) (by omega) (by omega), ← associator_inv_naturality_right_assoc]
  rfl

end TensorMu

end Braided

section Symmetric

variable [SymmetricCategory C]

/-- Over symmetric coefficients, the inverse Koszul braiding is the braiding of the swapped
complexes. -/
@[simp]
lemma koszulBraiding_inv (X Y : CochainComplex C ℤ) :
    (koszulBraiding C X Y).inv = koszulBraidingHom C Y X := by
  dsimp only [koszulBraiding, koszulBraidingInv]
  rw [SymmetricCategory.reverseBraiding_eq]

/-- Composing the Koszul braiding with the braiding of the swapped factors is the identity. -/
lemma koszulBraidingHom_comp (X Y : CochainComplex C ℤ) :
    koszulBraidingHom C X Y ≫ koszulBraidingHom C Y X = 𝟙 _ := by
  simpa only [koszulBraiding_hom, koszulBraiding_inv] using (koszulBraiding C X Y).hom_inv_id

variable [∀ X, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X)]
  [∀ (W X Y Z : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt W X Y Z]

/-- The Koszul braiding over symmetric coefficients is symmetric. -/
noncomputable instance koszulSymmetricCategory :
    SymmetricCategory (CochainComplex C ℤ) where
  symmetry X Y := by
    rw [braiding_eq_koszulBraiding, braiding_eq_koszulBraiding, koszulBraiding_hom,
      koszulBraiding_hom]
    exact koszulBraidingHom_comp C X Y

end Symmetric

end MathlibExt.DGSource
