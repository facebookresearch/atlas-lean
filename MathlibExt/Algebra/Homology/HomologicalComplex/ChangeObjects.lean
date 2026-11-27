/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Changing degreewise coordinates of a complex

For chosen isomorphisms e_i:K_i≅X_i, put the complex in the objects X_i
by conjugating its differentials as e_i^{-1} d_{ij} e_j. Complex maps
and complex-valued functors admit the same coordinate change, with
canonical natural isomorphisms to their original presentations.
-/

@[expose] public section

namespace HomologicalComplex

open CategoryTheory Category Limits

universe u v w

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {ι : Type w} {c : ComplexShape ι}
  (K : HomologicalComplex C c) {X : ι → C}

/--
Let C have zero morphisms, let K be a complex of shape c on ι, and choose objects Xᵢ with
isomorphisms eᵢ:Kᵢ≅Xᵢ. The complex in the new coordinates has term Xᵢ and differential eᵢ.inv
≫ K.d i j ≫ eⱼ.hom. The shape and square-zero laws are transported through the isomorphisms.
-/
def changeObjects (e : ∀ i, K.X i ≅ X i) : HomologicalComplex C c where
  X := X
  d i j := (e i).inv ≫ K.d i j ≫ (e j).hom
  shape i j h := by
    simp only [K.shape i j h, zero_comp, comp_zero]
  d_comp_d' i j k _ _ := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc (K.d i j) (K.d j k) (e k).hom, K.d_comp_d,
      zero_comp, comp_zero]

/--
Let C have zero morphisms, let K be a complex of shape c on ι, and choose objects Xᵢ with
isomorphisms eᵢ:Kᵢ≅Xᵢ. The transported complex has degree-i object exactly Xᵢ:
(K.changeObjects e).X i = X i.
-/
@[simp]
lemma changeObjects_X (e : ∀ i, K.X i ≅ X i) (i : ι) :
    (K.changeObjects e).X i = X i := rfl

/--
Let C have zero morphisms, let K be a complex of shape c on ι, and choose objects Xᵢ with
isomorphisms eᵢ:Kᵢ≅Xᵢ. For all i,j, the transported differential is (K.changeObjects e).d i j
= eᵢ.inv ≫ K.d i j ≫ eⱼ.hom : Xᵢ→Xⱼ.
-/
@[simp]
lemma changeObjects_d (e : ∀ i, K.X i ≅ X i) (i j : ι) :
    (K.changeObjects e).d i j = (e i).inv ≫ K.d i j ≫ (e j).hom := rfl

/--
Let C have zero morphisms, let K be a complex of shape c on ι, and choose objects Xᵢ with
isomorphisms eᵢ:Kᵢ≅Xᵢ. The component isomorphisms eᵢ assemble into an isomorphism of complexes
K≅K.changeObjects e.
-/
def changeObjectsIso (e : ∀ i, K.X i ≅ X i) : K ≅ K.changeObjects e :=
  Hom.isoOfComponents e (by
    intro i j _
    change (e i).hom ≫ (e i).inv ≫ K.d i j ≫ (e j).hom = K.d i j ≫ (e j).hom
    exact (e i).hom_inv_id_assoc (K.d i j ≫ (e j).hom))

/--
Let C have zero morphisms, let K be a complex of shape c on ι, and choose objects Xᵢ with
isomorphisms eᵢ:Kᵢ≅Xᵢ. The forward degree-i component of K≅K.changeObjects e is eᵢ.hom:Kᵢ→Xᵢ.
-/
@[simp]
lemma changeObjectsIso_hom_f (e : ∀ i, K.X i ≅ X i) (i : ι) :
    (K.changeObjectsIso e).hom.f i = (e i).hom := rfl

/--
Let C have zero morphisms, let K be a complex of shape c on ι, and choose objects Xᵢ with
isomorphisms eᵢ:Kᵢ≅Xᵢ. The inverse degree-i component of K≅K.changeObjects e is eᵢ.inv:Xᵢ→Kᵢ.
-/
@[simp]
lemma changeObjectsIso_inv_f (e : ∀ i, K.X i ≅ X i) (i : ι) :
    (K.changeObjectsIso e).inv.f i = (e i).inv := rfl

variable {K} {L M : HomologicalComplex C c} {Y Z : ι → C}

/--
Let K,L be c-complexes in a category C with zero morphisms, let φ:K→L, and choose eᵢ:Kᵢ≅Xᵢ and
fᵢ:Lᵢ≅Yᵢ. The induced map between the changed-coordinate complexes is the conjugate e^{-1} ≫ φ
≫ f. In degree i it is eᵢ.inv ≫ φ.f i ≫ fᵢ.hom.
-/
def changeObjectsMap (φ : K ⟶ L)
    (e : ∀ i, K.X i ≅ X i) (f : ∀ i, L.X i ≅ Y i) :
    K.changeObjects e ⟶ L.changeObjects f :=
  (K.changeObjectsIso e).inv ≫ φ ≫ (L.changeObjectsIso f).hom

/--
Let K,L be c-complexes in a category C with zero morphisms, let φ:K→L, and choose eᵢ:Kᵢ≅Xᵢ and
fᵢ:Lᵢ≅Yᵢ. Its degree-i component from Xᵢ to Yᵢ is eᵢ.inv ≫ φ.f i ≫ fᵢ.hom.
-/
@[simp]
lemma changeObjectsMap_f (φ : K ⟶ L)
    (e : ∀ i, K.X i ≅ X i) (f : ∀ i, L.X i ≅ Y i) (i : ι) :
    (changeObjectsMap φ e f).f i = (e i).inv ≫ φ.f i ≫ (f i).hom := rfl

/--
Let K,L be c-complexes in a category C with zero morphisms, let φ:K→L, and choose eᵢ:Kᵢ≅Xᵢ and
fᵢ:Lᵢ≅Yᵢ. The coordinate isomorphisms commute with φ: φ ≫ changeObjectsIso(L,f).hom =
changeObjectsIso(K,e).hom ≫ changeObjectsMap(φ,e,f).
-/
@[reassoc]
lemma changeObjectsIso_hom_naturality (φ : K ⟶ L)
    (e : ∀ i, K.X i ≅ X i) (f : ∀ i, L.X i ≅ Y i) :
    φ ≫ (L.changeObjectsIso f).hom =
      (K.changeObjectsIso e).hom ≫ changeObjectsMap φ e f := by
  simp only [changeObjectsMap, Iso.hom_inv_id_assoc]

/--
Let C have zero morphisms, let K be a complex of shape c on ι, and choose objects Xᵢ with
isomorphisms eᵢ:Kᵢ≅Xᵢ. The identity map of K becomes the identity of the changed-coordinate
complex: changeObjectsMap(1_K,e,e)=1_{K.changeObjects e}.
-/
@[simp]
lemma changeObjectsMap_id (e : ∀ i, K.X i ≅ X i) :
    changeObjectsMap (𝟙 K) e e = 𝟙 (K.changeObjects e) := by
  simp only [changeObjectsMap, Category.id_comp, Iso.inv_hom_id]

/--
Let φ:K→L and ψ:L→M be maps of c-complexes in a category C with zero morphisms, with chosen
coordinate isomorphisms eᵢ:Kᵢ≅Xᵢ, fᵢ:Lᵢ≅Yᵢ and gᵢ:Mᵢ≅Zᵢ. Changing coordinates preserves
composition: changeObjectsMap(φ≫ψ,e,g) = changeObjectsMap(φ,e,f) ≫ changeObjectsMap(ψ,f,g).
-/
lemma changeObjectsMap_comp (φ : K ⟶ L) (ψ : L ⟶ M)
    (e : ∀ i, K.X i ≅ X i) (f : ∀ i, L.X i ≅ Y i) (g : ∀ i, M.X i ≅ Z i) :
    changeObjectsMap (φ ≫ ψ) e g = changeObjectsMap φ e f ≫ changeObjectsMap ψ f g := by
  simp only [changeObjectsMap, Category.assoc, Iso.hom_inv_id_assoc]

section Functor

universe u' v'

variable {D : Type u'} [Category.{v'} D]
  (F : D ⥤ HomologicalComplex C c) (Y' : D → ι → C)
  (e : ∀ A i, (F.obj A).X i ≅ Y' A i)

/--
Let C have zero morphisms, let D be a category, and let F:D⥤Complexes(C,c). Choose objects
Y(A,i) and isomorphisms e(A,i):(F(A))ᵢ≅Y(A,i) for each A∈D and i∈ι. Changing the degree
objects of every F(A) to Y(A,i), and conjugating every map F(f) by e, defines a new
complex-valued functor on D.
-/
def changeObjectsFunctor : D ⥤ HomologicalComplex C c where
  obj A := (F.obj A).changeObjects (e A)
  map f := changeObjectsMap (F.map f) (e _) (e _)
  map_id A := by
    rw [F.map_id, changeObjectsMap_id]
  map_comp f g := by
    rw [F.map_comp]
    exact changeObjectsMap_comp (F.map f) (F.map g) (e _) (e _) (e _)

/--
Let C have zero morphisms, let D be a category, and let F:D⥤Complexes(C,c). Choose objects
Y(A,i) and isomorphisms e(A,i):(F(A))ᵢ≅Y(A,i) for each A∈D and i∈ι. The coordinate
isomorphisms e(A,i) give a natural isomorphism from F to the functor with degree objects
Y(A,i) and conjugated maps.
-/
def changeObjectsFunctorIso : F ≅ changeObjectsFunctor F Y' e :=
  NatIso.ofComponents (fun A => (F.obj A).changeObjectsIso (e A))
    (fun f => changeObjectsIso_hom_naturality (F.map f) (e _) (e _))

end Functor

end HomologicalComplex
