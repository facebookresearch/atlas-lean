/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed source port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/Algebra/Homology/Monoidal/Summand.lean
Only module/namespace paths are adapted for Atlas; source operations and hypotheses are retained.
-/

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import MathlibExt.CategoryTheory.DGSource.CochainBifunctor

/-!
# The monoidal structure of homological complexes on homogeneous summands

Mathlib's `HomologicalComplex.monoidalCategory` totalizes the degreewise tensor product, so every
structural map of a monoidal category of homological complexes, such as
`CochainComplex (ModuleCat R) ℤ` or `ChainComplex C ℕ`, is assembled from maps on the homogeneous
summands `X.X p ⊗ Y.X q` of `X ⊗ Y`.  Mathlib states the component formulas for the auxiliary
constructions the monoidal structure is built from — `HomologicalComplex.mapBifunctorMap`,
`HomologicalComplex.leftUnitor'`, `HomologicalComplex.rightUnitor'` and
`HomologicalComplex.mapBifunctorAssociatorX` — but not for the whiskerings, `λ_`, `ρ_` and `α_`
themselves.  This file supplies that last step, so that a calculation on homogeneous summands
never has to unfold the monoidal structure.  The formulas hold verbatim for homological complexes
of any shape in any monoidal preadditive category, and are stated in that generality; only their
evaluation on pure tensors, `HomologicalComplex.ι_tensorHom_apply`, is specific to modules.
The curried tensor bifunctor on cochain complexes is also identified with `tensorObj` and
`tensorHom`, so consumers can use these formulas without unfolding the bifunctor.

## Main results

* `HomologicalComplex.ι_tensorHom`: the tensor product of two morphisms on a homogeneous summand.
* `HomologicalComplex.zero_tensorHom` and `HomologicalComplex.tensorHom_zero`: the tensor product
  of morphisms vanishes when either factor does.
* `HomologicalComplex.tensorHom_eq_mapBifunctorMap`: `⊗ₘ` of homological complexes is the
  totalization `HomologicalComplex.mapBifunctorMap` of the two morphisms.
* `HomologicalComplex.ι_whiskerLeft` and `HomologicalComplex.ι_whiskerRight`: the two whiskerings
  on a homogeneous summand.
* `HomologicalComplex.leftUnitor_inv_f` and `HomologicalComplex.rightUnitor_inv_f`: the degreewise
  components of the inverse unitors.
* `HomologicalComplex.mapBifunctor₁₂.ι_eq_whiskerRight` and
  `HomologicalComplex.mapBifunctor₂₃.ι_eq_whiskerLeft`: the inclusions of the summand
  `X.X p ⊗ Y.X q ⊗ Z.X r` into `(X ⊗ Y) ⊗ Z` and `X ⊗ (Y ⊗ Z)` via whiskered `ιTensorObj`.
* `HomologicalComplex.ι_ι_associator_hom` and `HomologicalComplex.ι_ι_associator_inv`: the
  associator and its inverse on the summand `X.X p ⊗ Y.X q ⊗ Z.X r`, with arbitrary intermediate
  degrees.

The analogous formula for the differential of a tensor product is
`HomologicalComplex.ι_tensorObj_d` in `MathlibExt/CategoryTheory/DGSource/CochainTensorDifferential.lean`.
-/

public section

open CategoryTheory Limits MonoidalCategory

universe v

namespace HomologicalComplex

section General

variable {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C]
  [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  {I : Type*} [AddMonoid I] {c : ComplexShape I} [c.TensorSigns] [DecidableEq I]

/-- The tensor product of two morphisms of homological complexes, restricted to a homogeneous
summand, is the tensor product of their components.  Mathlib states this only for
`HomologicalComplex.mapBifunctorMap`, by which `⊗ₘ` is defined. -/
@[reassoc]
lemma ι_tensorHom {K₁ K₂ L₁ L₂ : HomologicalComplex C c} (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
    [HasTensor K₁ K₂] [HasTensor L₁ L₂]
    (i₁ i₂ j : I) (h : i₁ + i₂ = j) :
    ιTensorObj K₁ K₂ i₁ i₂ j h ≫ (tensorHom f₁ f₂).f j =
      (f₁.f i₁ ⊗ₘ f₂.f i₂) ≫ ιTensorObj L₁ L₂ i₁ i₂ j h := by
  refine (ι_mapBifunctorMap _ _ _ _ _ _ _ _).trans ?_
  simp [tensorHom_def]

/-- The tensor product of homological complexes of the zero morphism with any morphism is zero. -/
lemma zero_tensorHom {K₁ K₂ L₁ L₂ : HomologicalComplex C c} (f₂ : K₂ ⟶ L₂)
    [HasTensor K₁ K₂] [HasTensor L₁ L₂] :
    tensorHom (0 : K₁ ⟶ L₁) f₂ = 0 :=
  mapBifunctorMap_zero_left (curriedTensor C) c K₁ L₁ f₂

/-- The tensor product of homological complexes of any morphism with the zero morphism is zero. -/
lemma tensorHom_zero {K₁ K₂ L₁ L₂ : HomologicalComplex C c} (f₁ : K₁ ⟶ L₁)
    [HasTensor K₁ K₂] [HasTensor L₁ L₂] :
    tensorHom f₁ (0 : K₂ ⟶ L₂) = 0 :=
  mapBifunctorMap_zero_right (curriedTensor C) c f₁ K₂ L₂

variable [HasZeroObject C] (c) [∀ (X₁ X₂ : GradedObject I C), GradedObject.HasTensor X₁ X₂]
  [∀ X₂, PreservesColimit (CategoryTheory.Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- In the monoidal category of homological complexes, `⊗ₘ` is the totalization of the two
morphisms.  Mathlib defines `HomologicalComplex.monoidalCategory` this way, but states no lemma
exposing it, so `HomologicalComplex.ι_tensorHom` does not apply to `⊗ₘ` without this rewrite. -/
lemma tensorHom_eq_mapBifunctorMap {K₁ K₂ L₁ L₂ : HomologicalComplex C c} (f₁ : K₁ ⟶ L₁)
    (f₂ : K₂ ⟶ L₂) :
    f₁ ⊗ₘ f₂ = mapBifunctorMap f₁ f₂ (curriedTensor C) c :=
  rfl

variable {c}

/-- Left whiskering of homological complexes is the totalization of the identity and
the given morphism.  Mathlib defines the monoidal structure on homological complexes through
`HomologicalComplex.mapBifunctorMap`, but states no component lemma for `◁`. -/
lemma whiskerLeft_eq_mapBifunctorMap (X : HomologicalComplex C c) {Y Z : HomologicalComplex C c}
    (g : Y ⟶ Z) :
    X ◁ g = mapBifunctorMap (𝟙 X) g (curriedTensor C) c :=
  rfl

/-- Right whiskering of homological complexes is the totalization of the given
morphism and the identity; the counterpart of
`HomologicalComplex.whiskerLeft_eq_mapBifunctorMap`. -/
lemma whiskerRight_eq_mapBifunctorMap {X Y : HomologicalComplex C c} (f : X ⟶ Y)
    (Z : HomologicalComplex C c) :
    f ▷ Z = mapBifunctorMap f (𝟙 Z) (curriedTensor C) c :=
  rfl

/-- Left whiskering of homological complexes, restricted to a homogeneous summand, is left
whiskering of the summand. -/
@[reassoc (attr := simp)]
lemma ι_whiskerLeft (X : HomologicalComplex C c)
    {Y Z : HomologicalComplex C c} (g : Y ⟶ Z) (p q j : I) (h : p + q = j) :
    ιTensorObj X Y p q j h ≫ (X ◁ g).f j = (X.X p ◁ g.f q) ≫ ιTensorObj X Z p q j h := by
  rw [whiskerLeft_eq_mapBifunctorMap, ι_tensorHom, id_f, id_tensorHom]

/-- Right whiskering of homological complexes, restricted to a homogeneous summand, is
right whiskering of the summand. -/
@[reassoc (attr := simp)]
lemma ι_whiskerRight {X Y : HomologicalComplex C c} (f : X ⟶ Y)
    (Z : HomologicalComplex C c) (p q j : I) (h : p + q = j) :
    ιTensorObj X Z p q j h ≫ (f ▷ Z).f j = (f.f p ▷ Z.X q) ≫ ιTensorObj Y Z p q j h := by
  rw [whiskerRight_eq_mapBifunctorMap, ι_tensorHom, id_f, tensorHom_id]

/-- The degreewise component of the inverse left unitor of homological complexes is the
component of the auxiliary graded isomorphism `HomologicalComplex.leftUnitor'`, whose value is
recorded by `HomologicalComplex.leftUnitor'_inv`. -/
lemma leftUnitor_inv_f (X : HomologicalComplex C c) (j : I) :
    (λ_ X).inv.f j = (leftUnitor' X).inv j := by
  dsimp only [MonoidalCategoryStruct.leftUnitor, monoidalCategoryStruct,
    monoidalCategory, leftUnitor, Iso.symm_inv]
  simp only [Hom.isoOfComponents_hom_f, CategoryTheory.Functor.mapIso_hom, Iso.symm_hom]
  rfl

/-- The degreewise component of the inverse right unitor of homological complexes is the
component of the auxiliary graded isomorphism `HomologicalComplex.rightUnitor'`, whose value is
recorded by `HomologicalComplex.rightUnitor'_inv`. -/
lemma rightUnitor_inv_f (X : HomologicalComplex C c) (j : I) :
    (ρ_ X).inv.f j = (rightUnitor' X).inv j := by
  dsimp only [MonoidalCategoryStruct.rightUnitor, monoidalCategoryStruct,
    monoidalCategory, rightUnitor, Iso.symm_inv]
  simp only [Hom.isoOfComponents_hom_f, CategoryTheory.Functor.mapIso_hom, Iso.symm_hom]
  rfl

/-- The inclusion `HomologicalComplex.mapBifunctor₁₂.ι` of the summand `X.X p ⊗ Y.X q ⊗ Z.X r`
into `(X ⊗ Y) ⊗ Z`, written with the monoidal whiskering and `HomologicalComplex.ιTensorObj`.
Mathlib's `HomologicalComplex.mapBifunctor₁₂.ι_eq` states it for the raw totalization. -/
@[reassoc]
lemma mapBifunctor₁₂.ι_eq_whiskerRight (X Y Z : HomologicalComplex C c) (p q r pq j : I)
    (hpq : p + q = pq) (h : pq + r = j) :
    mapBifunctor₁₂.ι (curriedTensor C) (curriedTensor C) X Y Z c c p q r j
        (by rw [← h, ← hpq]; rfl) =
      (ιTensorObj X Y p q pq hpq ▷ Z.X r) ≫ ιTensorObj (X ⊗ Y) Z pq r j h := by
  rw [mapBifunctor₁₂.ι_eq (curriedTensor C) (curriedTensor C) X Y Z c c p q r pq j hpq h]
  -- `(curriedTensor C).map f).app W` is `f ▷ W` and `ιMapBifunctor` is `ιTensorObj`, by definition.
  rfl

/-- The inclusion `HomologicalComplex.mapBifunctor₂₃.ι` of the summand `X.X p ⊗ Y.X q ⊗ Z.X r`
into `X ⊗ (Y ⊗ Z)`, written with the monoidal whiskering and `HomologicalComplex.ιTensorObj`.
Mathlib's `HomologicalComplex.mapBifunctor₂₃.ι_eq` states it for the raw totalization. -/
@[reassoc]
lemma mapBifunctor₂₃.ι_eq_whiskerLeft (X Y Z : HomologicalComplex C c) (p q r qr j : I)
    (hqr : q + r = qr) (h : p + qr = j) :
    mapBifunctor₂₃.ι (curriedTensor C) (curriedTensor C) X Y Z c c c p q r j
        (by rw [← h, ← hqr]; exact add_assoc p q r) =
      (X.X p ◁ ιTensorObj Y Z q r qr hqr) ≫ ιTensorObj X (Y ⊗ Z) p qr j h := by
  rw [mapBifunctor₂₃.ι_eq (curriedTensor C) (curriedTensor C) X Y Z c c c p q r qr j hqr h]
  -- `(curriedTensor C).obj W).map f` is `W ◁ f` and `ιMapBifunctor` is `ιTensorObj`, by definition.
  rfl

/-- The associator of homological complexes, restricted to the summand indexed by the
degrees `p`, `q` and `r`, is the associator of the three summands. The intermediate
degrees `pq` and `qr` may be any degrees equal to `p + q` and `q + r`. -/
@[reassoc]
lemma ι_ι_associator_hom (X Y Z : HomologicalComplex C c) (p q r pq qr j : I)
    (hpq : p + q = pq) (hqr : q + r = qr) (h : pq + r = j) (h' : p + qr = j) :
    (ιTensorObj X Y p q pq hpq ▷ Z.X r) ≫
        ιTensorObj (X ⊗ Y) Z pq r j h ≫ (α_ X Y Z).hom.f j =
      (α_ (X.X p) (Y.X q) (Z.X r)).hom ≫ (X.X p ◁ ιTensorObj Y Z q r qr hqr) ≫
        ιTensorObj X (Y ⊗ Z) p qr j h' := by
  rw [← Category.assoc, ← mapBifunctor₁₂.ι_eq_whiskerRight X Y Z p q r pq j hpq h,
    ← mapBifunctor₂₃.ι_eq_whiskerLeft X Y Z p q r qr j hqr h']
  -- Mathlib assembles the associator of homological complexes from
  -- `HomologicalComplex.mapBifunctorAssociatorX`, but states no component lemma for `α_`.
  have ha : (α_ X Y Z).hom.f j =
      (mapBifunctorAssociatorX (curriedAssociatorNatIso C) X Y Z c c c j).hom := rfl
  rw [ha]
  simp only [ι_mapBifunctorAssociatorX_hom, curriedAssociatorNatIso_hom_app_app_app]

/-- The inverse associator of homological complexes, restricted to a homogeneous
summand with arbitrary intermediate degrees, is the inverse associator of the three summands. -/
@[reassoc]
lemma ι_ι_associator_inv (X Y Z : HomologicalComplex C c)
    (p q r pq qr j : I) (hpq : p + q = pq) (hqr : q + r = qr) (h : pq + r = j)
    (h' : p + qr = j) :
    (X.X p ◁ ιTensorObj Y Z q r qr hqr) ≫ ιTensorObj X (Y ⊗ Z) p qr j h' ≫ (α_ X Y Z).inv.f j =
      (α_ (X.X p) (Y.X q) (Z.X r)).inv ≫ (ιTensorObj X Y p q pq hpq ▷ Z.X r) ≫
        ιTensorObj (X ⊗ Y) Z pq r j h := by
  rw [← cancel_epi (α_ (X.X p) (Y.X q) (Z.X r)).hom, Iso.hom_inv_id_assoc,
    ← ι_ι_associator_hom_assoc X Y Z p q r pq qr j hpq hqr h h', ← comp_f, Iso.hom_inv_id, id_f]
  -- `Category.comp_id` is stated for the identity of the codomain of `ιTensorObj`, which is
  -- spelled `(HomologicalComplex.tensorObj (X ⊗ Y) Z).X j` rather than `((X ⊗ Y) ⊗ Z).X j`.
  erw [Category.comp_id]

end General

section ComplexesOfModules

variable {R : Type v} [CommRing R]
variable {I : Type*} [AddMonoid I] {c : ComplexShape I} [c.TensorSigns] [DecidableEq I]

/-- The tensor product of two morphisms of homological complexes of modules on a pure tensor in a
homogeneous summand: the tensor product of the components. -/
lemma ι_tensorHom_apply {K₁ K₂ L₁ L₂ : HomologicalComplex (ModuleCat.{v} R) c} (f₁ : K₁ ⟶ L₁)
    (f₂ : K₂ ⟶ L₂) [HasTensor K₁ K₂] [HasTensor L₁ L₂] (i₁ i₂ j : I) (h : i₁ + i₂ = j)
    (a : K₁.X i₁) (b : K₂.X i₂) :
    (tensorHom f₁ f₂).f j ((ιTensorObj K₁ K₂ i₁ i₂ j h).hom (a ⊗ₜ[R] b)) =
      (ιTensorObj L₁ L₂ i₁ i₂ j h).hom (f₁.f i₁ a ⊗ₜ[R] f₂.f i₂ b) :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (ι_tensorHom f₁ f₂ i₁ i₂ j h)) (a ⊗ₜ[R] b)

end ComplexesOfModules

end HomologicalComplex

namespace CochainComplex

open HomologicalComplex

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [∀ K L : CochainComplex C ℤ, HasTensor K L]

/-- The curried tensor bifunctor on complexes computes the total tensor product. -/
@[simp]
theorem curriedTensor_map₂CochainComplex_obj_obj (K A : CochainComplex C ℤ) :
    ((curriedTensor C).map₂CochainComplex.obj K).obj A = tensorObj K A := rfl

/-- The curried tensor bifunctor acts in the right input by tensoring with an identity. -/
@[simp]
theorem curriedTensor_map₂CochainComplex_obj_map (K : CochainComplex C ℤ)
    {A B : CochainComplex C ℤ} (g : A ⟶ B) :
    ((curriedTensor C).map₂CochainComplex.obj K).map g = tensorHom (𝟙 K) g := rfl

/-- The curried tensor bifunctor acts in the left input by tensoring with an identity. -/
@[simp]
theorem curriedTensor_map₂CochainComplex_map_app {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (A : CochainComplex C ℤ) :
    ((curriedTensor C).map₂CochainComplex.map f).app A = tensorHom f (𝟙 A) := rfl

end CochainComplex
