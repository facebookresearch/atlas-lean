/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed source port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/Algebra/Homology/Monoidal/Summand.lean
Modification notice: the general tensor zero laws reuse
`MathlibExt.Algebra.Homology.TensorHomFunctoriality`. The remaining source
operations and hypotheses are retained.
-/

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import MathlibExt.Algebra.Homology.TensorHomFunctoriality
public import MathlibExt.CategoryTheory.DGSource.CochainBifunctor

/-!
# Tensor-complex structure maps on homogeneous summands

For complexes over a preadditive monoidal category with biadditive
tensor, the degree-`j` tensor object is the coproduct of `X_p ⊗ Y_q`
with `p+q=j`. Tensor maps and whiskerings act on these summands by
their component maps. When the coproduct-preservation conditions for
associativity and zero-object conditions hold, unitors and associators
are likewise computed from the base-category maps on the summands.
The formulas allow arbitrary additive index monoids and compatible
tensor signs; pure-tensor values specialize to modules over a
commutative ring. The curried tensor functor on integer cochain
complexes has the same tensor objects and maps.
-/

public section

open CategoryTheory Limits MonoidalCategory

universe v

namespace HomologicalComplex

section General

variable {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C]
  [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  {I : Type*} [AddMonoid I] {c : ComplexShape I} [c.TensorSigns] [DecidableEq I]

/-- Let `C` be preadditive and monoidal with biadditive tensor,
`I` an additive monoid with decidable equality, and `c` a complex
shape on `I` with compatible tensor signs. For maps `f₁ : K₁ → L₁`, `f₂ : K₂ → L₂` and existing
source and target tensors, the summand with `i₁+i₂=j` satisfies
`ι_K ≫ (f₁ ⊗ f₂)_j = (f₁,i₁ ⊗ f₂,i₂) ≫ ι_L`. -/
@[reassoc]
lemma ι_tensorHom {K₁ K₂ L₁ L₂ : HomologicalComplex C c} (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
    [HasTensor K₁ K₂] [HasTensor L₁ L₂]
    (i₁ i₂ j : I) (h : i₁ + i₂ = j) :
    ιTensorObj K₁ K₂ i₁ i₂ j h ≫ (tensorHom f₁ f₂).f j =
      (f₁.f i₁ ⊗ₘ f₂.f i₂) ≫ ιTensorObj L₁ L₂ i₁ i₂ j h := by
  refine (ι_mapBifunctorMap _ _ _ _ _ _ _ _).trans ?_
  simp [tensorHom_def]

variable [HasZeroObject C] (c) [∀ (X₁ X₂ : GradedObject I C), GradedObject.HasTensor X₁ X₂]
  [∀ X₂, PreservesColimit (CategoryTheory.Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- Let `C` be preadditive and monoidal with biadditive tensor,
`I` an additive monoid with decidable equality, and `c` a complex
shape on `I` with compatible tensor signs. Assume a zero object, all graded tensor coproducts, preservation
of the coproducts used in both associations of triple tensors, and
zero-object preservation by each functor `- ⊗ A`. For two complex maps, their monoidal tensor morphism is
exactly the totalized degreewise map of the curried tensor bifunctor. -/
lemma tensorHom_eq_mapBifunctorMap {K₁ K₂ L₁ L₂ : HomologicalComplex C c} (f₁ : K₁ ⟶ L₁)
    (f₂ : K₂ ⟶ L₂) :
    f₁ ⊗ₘ f₂ = mapBifunctorMap f₁ f₂ (curriedTensor C) c :=
  rfl

variable {c}

/-- Let `C` be preadditive and monoidal with biadditive tensor,
`I` an additive monoid with decidable equality, and `c` a complex
shape on `I` with compatible tensor signs. Assume a zero object, all graded tensor coproducts, preservation
of the coproducts used in both associations of triple tensors, and
zero-object preservation by each functor `- ⊗ A`. For a complex `X` and map `g : Y → Z`, left whiskering
`X ◁ g` is the total bifunctor map of `𝟙 X` and `g`. -/
lemma whiskerLeft_eq_mapBifunctorMap (X : HomologicalComplex C c) {Y Z : HomologicalComplex C c}
    (g : Y ⟶ Z) :
    X ◁ g = mapBifunctorMap (𝟙 X) g (curriedTensor C) c :=
  rfl

/-- Let `C` be preadditive and monoidal with biadditive tensor,
`I` an additive monoid with decidable equality, and `c` a complex
shape on `I` with compatible tensor signs. Assume a zero object, all graded tensor coproducts, preservation
of the coproducts used in both associations of triple tensors, and
zero-object preservation by each functor `- ⊗ A`. For a complex map `f : X → Y` and complex `Z`, right
whiskering `f ▷ Z` is the total bifunctor map of `f` and `𝟙 Z`. -/
lemma whiskerRight_eq_mapBifunctorMap {X Y : HomologicalComplex C c} (f : X ⟶ Y)
    (Z : HomologicalComplex C c) :
    f ▷ Z = mapBifunctorMap f (𝟙 Z) (curriedTensor C) c :=
  rfl

/-- Let `C` be preadditive and monoidal with biadditive tensor,
`I` an additive monoid with decidable equality, and `c` a complex
shape on `I` with compatible tensor signs. Assume a zero object, all graded tensor coproducts, preservation
of the coproducts used in both associations of triple tensors, and
zero-object preservation by each functor `- ⊗ A`. For `g : Y → Z` and `p+q=j`, the `(p,q)` summand of
`X ◁ g` is `X_p ◁ g_q` followed by the target summand inclusion. -/
@[reassoc (attr := simp)]
lemma ι_whiskerLeft (X : HomologicalComplex C c)
    {Y Z : HomologicalComplex C c} (g : Y ⟶ Z) (p q j : I) (h : p + q = j) :
    ιTensorObj X Y p q j h ≫ (X ◁ g).f j = (X.X p ◁ g.f q) ≫ ιTensorObj X Z p q j h := by
  rw [whiskerLeft_eq_mapBifunctorMap, ι_tensorHom, id_f, id_tensorHom]

/-- Let `C` be preadditive and monoidal with biadditive tensor,
`I` an additive monoid with decidable equality, and `c` a complex
shape on `I` with compatible tensor signs. Assume a zero object, all graded tensor coproducts, preservation
of the coproducts used in both associations of triple tensors, and
zero-object preservation by each functor `- ⊗ A`. For `f : X → Y` and `p+q=j`, the `(p,q)` summand of
`f ▷ Z` is `f_p ▷ Z_q` followed by the target summand inclusion. -/
@[reassoc (attr := simp)]
lemma ι_whiskerRight {X Y : HomologicalComplex C c} (f : X ⟶ Y)
    (Z : HomologicalComplex C c) (p q j : I) (h : p + q = j) :
    ιTensorObj X Z p q j h ≫ (f ▷ Z).f j = (f.f p ▷ Z.X q) ≫ ιTensorObj Y Z p q j h := by
  rw [whiskerRight_eq_mapBifunctorMap, ι_tensorHom, id_f, tensorHom_id]

/-- Let `C` be preadditive and monoidal with biadditive tensor,
`I` an additive monoid with decidable equality, and `c` a complex
shape on `I` with compatible tensor signs. Assume a zero object, all graded tensor coproducts, preservation
of the coproducts used in both associations of triple tensors, and
zero-object preservation by each functor `- ⊗ A`. In degree `j`, the inverse left unitor of `X` is the base
inverse unitor on `X_j`, followed by the degree-zero unit-coordinate
identification and the `(0,j)` tensor summand inclusion. -/
lemma leftUnitor_inv_f (X : HomologicalComplex C c) (j : I) :
    (λ_ X).inv.f j = (leftUnitor' X).inv j := by
  dsimp only [MonoidalCategoryStruct.leftUnitor, monoidalCategoryStruct,
    monoidalCategory, leftUnitor, Iso.symm_inv]
  simp only [Hom.isoOfComponents_hom_f, CategoryTheory.Functor.mapIso_hom, Iso.symm_hom]
  rfl

/-- Let `C` be preadditive and monoidal with biadditive tensor,
`I` an additive monoid with decidable equality, and `c` a complex
shape on `I` with compatible tensor signs. Assume a zero object, all graded tensor coproducts, preservation
of the coproducts used in both associations of triple tensors, and
zero-object preservation by each functor `- ⊗ A`. In degree `j`, the inverse right unitor of `X` is the base
inverse unitor on `X_j`, followed by the degree-zero unit-coordinate
identification and the `(j,0)` tensor summand inclusion. -/
lemma rightUnitor_inv_f (X : HomologicalComplex C c) (j : I) :
    (ρ_ X).inv.f j = (rightUnitor' X).inv j := by
  dsimp only [MonoidalCategoryStruct.rightUnitor, monoidalCategoryStruct,
    monoidalCategory, rightUnitor, Iso.symm_inv]
  simp only [Hom.isoOfComponents_hom_f, CategoryTheory.Functor.mapIso_hom, Iso.symm_hom]
  rfl

/-- Let `C` be preadditive and monoidal with biadditive tensor,
`I` an additive monoid with decidable equality, and `c` a complex
shape on `I` with compatible tensor signs. Assume a zero object, all graded tensor coproducts, preservation
of the coproducts used in both associations of triple tensors, and
zero-object preservation by each functor `- ⊗ A`. For `p+q=pq`, `pq+r=j`, the triple summand
`(X_p ⊗ Y_q) ⊗ Z_r` enters `((X ⊗ Y) ⊗ Z)_j` by tensoring
`ι_(p,q,pq)` on the right with `Z_r`, then applying `ι_(pq,r,j)`. -/
@[reassoc]
lemma mapBifunctor₁₂.ι_eq_whiskerRight (X Y Z : HomologicalComplex C c) (p q r pq j : I)
    (hpq : p + q = pq) (h : pq + r = j) :
    mapBifunctor₁₂.ι (curriedTensor C) (curriedTensor C) X Y Z c c p q r j
        (by rw [← h, ← hpq]; rfl) =
      (ιTensorObj X Y p q pq hpq ▷ Z.X r) ≫ ιTensorObj (X ⊗ Y) Z pq r j h := by
  rw [mapBifunctor₁₂.ι_eq (curriedTensor C) (curriedTensor C) X Y Z c c p q r pq j hpq h]
  -- `(curriedTensor C).map f).app W` is `f ▷ W` and `ιMapBifunctor` is `ιTensorObj`, by definition.
  rfl

/-- Let `C` be preadditive and monoidal with biadditive tensor,
`I` an additive monoid with decidable equality, and `c` a complex
shape on `I` with compatible tensor signs. Assume a zero object, all graded tensor coproducts, preservation
of the coproducts used in both associations of triple tensors, and
zero-object preservation by each functor `- ⊗ A`. For `q+r=qr`, `p+qr=j`, the triple summand
`X_p ⊗ (Y_q ⊗ Z_r)` enters `(X ⊗ (Y ⊗ Z))_j` by tensoring
`ι_(q,r,qr)` on the left with `X_p`, then applying `ι_(p,qr,j)`. -/
@[reassoc]
lemma mapBifunctor₂₃.ι_eq_whiskerLeft (X Y Z : HomologicalComplex C c) (p q r qr j : I)
    (hqr : q + r = qr) (h : p + qr = j) :
    mapBifunctor₂₃.ι (curriedTensor C) (curriedTensor C) X Y Z c c c p q r j
        (by rw [← h, ← hqr]; exact add_assoc p q r) =
      (X.X p ◁ ιTensorObj Y Z q r qr hqr) ≫ ιTensorObj X (Y ⊗ Z) p qr j h := by
  rw [mapBifunctor₂₃.ι_eq (curriedTensor C) (curriedTensor C) X Y Z c c c p q r qr j hqr h]
  -- `(curriedTensor C).obj W).map f` is `W ◁ f` and `ιMapBifunctor` is `ιTensorObj`, by definition.
  rfl

/-- Let `C` be preadditive and monoidal with biadditive tensor,
`I` an additive monoid with decidable equality, and `c` a complex
shape on `I` with compatible tensor signs. Assume a zero object, all graded tensor coproducts, preservation
of the coproducts used in both associations of triple tensors, and
zero-object preservation by each functor `- ⊗ A`. For `p+q=pq`, `q+r=qr`, `pq+r=j=p+qr`, the complex
associator sends the left-associated triple inclusion to the base
associator `α_(X_p,Y_q,Z_r)` followed by the right-associated inclusion.
The intermediate degrees `pq,qr` are arbitrary with those equalities. -/
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

/-- Let `C` be preadditive and monoidal with biadditive tensor,
`I` an additive monoid with decidable equality, and `c` a complex
shape on `I` with compatible tensor signs. Assume a zero object, all graded tensor coproducts, preservation
of the coproducts used in both associations of triple tensors, and
zero-object preservation by each functor `- ⊗ A`. For `p+q=pq`, `q+r=qr`, `pq+r=j=p+qr`, the inverse
complex associator sends the right-associated triple inclusion to
the inverse base associator followed by the left-associated inclusion. -/
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

/-- Let `R` be a commutative ring and consider module complexes of
shape `c` on an additive monoid with decidable equality and compatible
tensor signs. For maps `f₁ : K₁ → L₁`, `f₂ : K₂ → L₂` with the
displayed tensors existing, `i₁+i₂=j`, and `a ∈ K₁,i₁`, `b ∈ K₂,i₂`,
the tensor-complex map sends `ι_K(a ⊗ b)` to
`ι_L(f₁,i₁(a) ⊗ f₂,i₂(b))`. -/
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

/-- Let `C` be preadditive and monoidal with biadditive tensor,
and suppose tensor products exist for all integer cochain complexes
in `C`. The curried tensor bifunctor lifted to cochain complexes
has object at `(K,A)` equal to their total tensor complex `K ⊗ A`. -/
@[simp]
theorem curriedTensor_map₂CochainComplex_obj_obj (K A : CochainComplex C ℤ) :
    ((curriedTensor C).map₂CochainComplex.obj K).obj A = tensorObj K A := rfl

/-- Let `C` be preadditive and monoidal with biadditive tensor,
and suppose tensor products exist for all integer cochain complexes
in `C`. For a fixed cochain complex `K` and map `g : A → B`,
the right-variable map of the lifted curried tensor bifunctor is
`tensorHom(𝟙 K,g)`. -/
@[simp]
theorem curriedTensor_map₂CochainComplex_obj_map (K : CochainComplex C ℤ)
    {A B : CochainComplex C ℤ} (g : A ⟶ B) :
    ((curriedTensor C).map₂CochainComplex.obj K).map g = tensorHom (𝟙 K) g := rfl

/-- Let `C` be preadditive and monoidal with biadditive tensor,
and suppose tensor products exist for all integer cochain complexes
in `C`. For a cochain map `f : K → L` and complex `A`, the
left-variable component of the lifted curried tensor bifunctor is
`tensorHom(f,𝟙 A)`. -/
@[simp]
theorem curriedTensor_map₂CochainComplex_map_app {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (A : CochainComplex C ℤ) :
    ((curriedTensor C).map₂CochainComplex.map f).app A = tensorHom f (𝟙 A) := rfl

end CochainComplex
