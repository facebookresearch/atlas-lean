/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Additive

/-!
# Extension by zero commutes with functorial maps

Let F:C⥤D preserve zero morphisms, with zero objects in both categories.
Applying F before or after extension by zero along a shape embedding
produces canonically isomorphic complexes. The comparison is the identity
at each retained degree and the unique zero-object isomorphism elsewhere.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u₁ u₂ v₁ v₂ i j

namespace HomologicalComplex

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroObject C] [HasZeroObject D]
  {ι : Type i} {ι' : Type j} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (F : C ⥤ D) [F.PreservesZeroMorphisms]

/--
Let C,D have zero morphisms and zero objects, and let F:C⥤D preserve zero morphisms. Let K be
a complex of shape c on ι. Adjoin an isolated zero index ⊥ to ι: set E(K)_i=K_i and E(K)_⊥=0.
There is a component isomorphism θ_a:E(F(K))_a≅F(E(K)_a), the identity at a=i and the
canonical isomorphism 0_D≅F(0_C) at a=⊥.
-/
def extendMapComponentIso (K : HomologicalComplex C c) :
    ∀ a : Option ι, extend.X ((F.mapHomologicalComplex c).obj K) a ≅ F.obj (extend.X K a)
  | some _ => Iso.refl _
  | none => (Limits.isZero_zero D).iso (F.map_isZero (Limits.isZero_zero C))

/--
Let C,D have zero morphisms and zero objects, and let F:C⥤D preserve zero morphisms. Let K be
a complex of shape c on ι. On the index set ι with an adjoined zero index, let
θ_a:E(F(K))_a≅F(E(K)_a) be the canonical component comparisons. For any a,b they satisfy
θ_a.hom ≫ F(E(d_K)_{a,b}) = E(d_{F(K)})_{a,b} ≫ θ_b.hom; differentials touching the zero index
vanish.
-/
theorem extendMapComponentIso_d (K : HomologicalComplex C c) (a b : Option ι) :
    (extendMapComponentIso F K a).hom ≫ F.map (extend.d K a b) =
      extend.d ((F.mapHomologicalComplex c).obj K) a b ≫
        (extendMapComponentIso F K b).hom := by
  cases a with
  | none => exact (Limits.isZero_zero D).eq_of_src _ _
  | some a =>
    cases b with
    | none => exact (F.map_isZero (Limits.isZero_zero C)).eq_of_tgt _ _
    | some b =>
      change 𝟙 _ ≫ F.map (K.d a b) = F.map (K.d a b) ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]

/--
Let C,D have zero morphisms and zero objects, and let F:C⥤D preserve zero morphisms. Let K be
a complex of shape c on ι. For a shape embedding e:c→c', extending the mapped complex F(K) by
zero is canonically isomorphic to applying F to the extension of K: (F(K)).extend e ≅
F(K.extend e). The comparison is identity on retained terms and canonical on zero terms.
-/
def extendMapIso (e : c.Embedding c') (K : HomologicalComplex C c) :
    ((F.mapHomologicalComplex c).obj K).extend e ≅
      (F.mapHomologicalComplex c').obj (K.extend e) :=
  Hom.isoOfComponents (fun n => extendMapComponentIso F K (e.r n)) (by
    intro n m _
    exact extendMapComponentIso_d F K (e.r n) (e.r m))

/--
Let C,D have zero morphisms and zero objects, and let F:C⥤D preserve zero morphisms. Let K be
a complex of shape c on ι. Let e:c→c' and a:K→L be a complex morphism. For the comparisons
θ_K,θ_L between extension after F and F after extension, extend(F(a)) ≫ θ_L.hom = θ_K.hom ≫
F(extend(a)).
-/
@[reassoc]
theorem extendMapIso_naturality (e : c.Embedding c') {K L : HomologicalComplex C c} (a : K ⟶ L) :
    extendMap ((F.mapHomologicalComplex c).map a) e ≫ (extendMapIso F e L).hom =
      (extendMapIso F e K).hom ≫ (F.mapHomologicalComplex c').map (extendMap a e) := by
  apply Hom.ext
  funext n
  change extend.mapX ((F.mapHomologicalComplex c).map a) (e.r n) ≫
      (extendMapComponentIso F L (e.r n)).hom =
    (extendMapComponentIso F K (e.r n)).hom ≫ F.map (extend.mapX a (e.r n))
  cases e.r n with
  | none => exact (Limits.isZero_zero D).eq_of_src _ _
  | some i =>
    change F.map (a.f i) ≫ 𝟙 _ = 𝟙 _ ≫ F.map (a.f i)
    simp only [Category.comp_id, Category.id_comp]

end HomologicalComplex

namespace ComplexShape.Embedding

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroObject C] [HasZeroObject D]
  {ι : Type i} {ι' : Type j} {c : ComplexShape ι} {c' : ComplexShape ι'}

/--
Let C,D have zero morphisms and zero objects, let F:C⥤D preserve zero morphisms, and let
e:c→c' be a shape embedding. The functors that apply F then extend by zero and that extend by
zero then apply F are naturally isomorphic; their components are the canonical termwise
extension comparisons.
-/
def extendFunctorMapIso (e : c.Embedding c') (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    F.mapHomologicalComplex c ⋙ e.extendFunctor D ≅
      e.extendFunctor C ⋙ F.mapHomologicalComplex c' :=
  NatIso.ofComponents (fun K => HomologicalComplex.extendMapIso F e K) (by
    intro K L a
    exact HomologicalComplex.extendMapIso_naturality F e a)

end ComplexShape.Embedding

end
