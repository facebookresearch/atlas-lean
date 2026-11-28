/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import MathlibExt.CategoryTheory.Monoidal.PreservesColimits

/-!
# Colimits of the full integer cochain tensor

Let R be a commutative ring in universe u. The ordinary convolution tensor of ℤ-indexed cochain
complexes has degree-n term ⊕_{p+q=n}K^p⊗_R L^q, over every integer pair. Its monoidal structure
uses the graded tensor coproducts, zero-object preservation in both coefficient variables, the
two triple-coproduct compatibility conditions, and fourfold tensor extensionality.

For fixed K, evaluation of K⊗(-) at n identifies with the coproduct of the degree-piece diagram
L↦(K^p⊗L^q)_{p+q=n}; the right tensor has pieces L^p⊗K^q. Evaluation and coefficient tensoring
preserve colimits, and the diagram coproduct functor does as well.

Consequently both full cochain tensor functors preserve colimits of any category J for which the
coefficient module category has J-colimits. The object and morphism universes of J are
independent of u.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CochainComplex

universe u v w

variable {R : Type u} [CommRing R]
variable [∀ X Y : GradedObject ℤ (ModuleCat.{u} R), GradedObject.HasTensor X Y]
variable [∀ X : ModuleCat.{u} R,
  PreservesColimit (Functor.empty.{0} (ModuleCat.{u} R))
    ((curriedTensor (ModuleCat.{u} R)).obj X)]
variable [∀ X : ModuleCat.{u} R,
  PreservesColimit (Functor.empty.{0} (ModuleCat.{u} R))
    ((curriedTensor (ModuleCat.{u} R)).flip.obj X)]
variable [∀ W X Y Z : GradedObject ℤ (ModuleCat.{u} R),
  GradedObject.HasTensor₄ObjExt W X Y Z]
variable [∀ X Y Z : GradedObject ℤ (ModuleCat.{u} R),
  GradedObject.HasGoodTensor₁₂Tensor X Y Z]
variable [∀ X Y Z : GradedObject ℤ (ModuleCat.{u} R),
  GradedObject.HasGoodTensorTensor₂₃ X Y Z]
/-- For n∈ℤ, the total-degree fibre of the two integer cochain shapes is the set I_n={(p,q)∈ℤ² |
p+q=n}. It indexes the full convolution coproduct in degree n, including negative p and q. -/
abbrev intTensorTotalFiber (n : ℤ) :=
  (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⁻¹' {n}

/-- Let R be a commutative ring in universe u and use R-module carriers in u. For a fixed ℤ-indexed
cochain complex K and n∈ℤ, the functor P^L_{K,n} sends L to the discrete diagram (p,q)↦K^p⊗_R
L^q for p+q=n. A cochain map f:L→M acts at that pair by id_{K^p}⊗f^q. -/
def tensorLeftIntDegreePieces (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ Discrete (intTensorTotalFiber n) ⥤ ModuleCat.{u} R where
  obj L :=
    { obj := fun ij => K.X ij.as.val.1 ⊗ L.X ij.as.val.2
      map := fun f => eqToHom (by rw [Discrete.eq_of_hom f]) }
  map f :=
    { app := fun ij => K.X ij.as.val.1 ◁ f.f ij.as.val.2
      naturality := by
        intro i j g
        have hij : i = j := Discrete.ext (Discrete.eq_of_hom g)
        subst j
        simp }

set_option backward.isDefEq.respectTransparency false in
/-- Let R be a commutative ring in universe u and use R-module carriers in u. Use the ℤ-indexed
cochain convolution tensor: all antidiagonal coproducts exist, coefficient tensoring preserves
zero objects in both variables and commutes with the coproducts in both triple
parenthesizations, and fourfold tensor inclusions determine maps. For K and n∈ℤ, there is a
natural isomorphism ev_n(K⊗(-))≅colim∘P^L_{K,n}. At L it identifies (K⊗L)^n with
⊕_{p+q=n}K^p⊗L^q, preserving each fibre coefficient. -/
def tensorLeftIntEvalIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    tensorLeft K ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) n ≅
      tensorLeftIntDegreePieces K n ⋙ colim :=
  NatIso.ofComponents (fun _ => eqToIso (by rfl)) (fun {X Y} f => by
    dsimp
    apply GradedObject.mapObj_ext
    rintro ⟨p, q⟩ hi
    simp only [Category.comp_id, Category.id_comp]
    erw [HomologicalComplex.ι_mapBifunctorMap]
    erw [colimit.ι_map]
    dsimp [tensorLeftIntDegreePieces]
    simp only [MonoidalCategory.id_whiskerRight, Category.id_comp]
    rfl)

/-- Let R be a commutative ring in universe u and use R-module carriers in u. For K a ℤ-indexed
cochain complex and n∈ℤ, P^R_{K,n} sends L to (p,q)↦L^p⊗_R K^q on the discrete fibre p+q=n. A
map f:L→M acts by f^p⊗id_{K^q}. -/
def tensorRightIntDegreePieces (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ Discrete (intTensorTotalFiber n) ⥤ ModuleCat.{u} R where
  obj L :=
    { obj := fun ij => L.X ij.as.val.1 ⊗ K.X ij.as.val.2
      map := fun f => eqToHom (by rw [Discrete.eq_of_hom f]) }
  map f :=
    { app := fun ij => f.f ij.as.val.1 ▷ K.X ij.as.val.2
      naturality := by
        intro i j g
        have hij : i = j := Discrete.ext (Discrete.eq_of_hom g)
        subst j
        simp }

set_option backward.isDefEq.respectTransparency false in
/-- Let R be a commutative ring in universe u and use R-module carriers in u. Use the ℤ-indexed
cochain convolution tensor: all antidiagonal coproducts exist, coefficient tensoring preserves
zero objects in both variables and commutes with the coproducts in both triple
parenthesizations, and fourfold tensor inclusions determine maps. For K and n∈ℤ,
ev_n((-)⊗K)≅colim∘P^R_{K,n} naturally. Its component at L identifies (L⊗K)^n with
⊕_{p+q=n}L^p⊗K^q in the given coefficient order. -/
def tensorRightIntEvalIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    tensorRight K ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) n ≅
      tensorRightIntDegreePieces K n ⋙ colim :=
  NatIso.ofComponents (fun _ => eqToIso (by rfl)) (fun {X Y} f => by
    dsimp
    apply GradedObject.mapObj_ext
    rintro ⟨p, q⟩ hi
    simp only [Category.comp_id, Category.id_comp]
    erw [HomologicalComplex.ι_mapBifunctorMap]
    erw [colimit.ι_map]
    dsimp [tensorRightIntDegreePieces]
    simp only [MonoidalCategory.whiskerLeft_id]
    rw [Category.id_comp]
    rfl)

variable (J : Type w) [Category.{v} J] [HasColimitsOfShape J (ModuleCat.{u} R)]

/-- Let R be a commutative ring in universe u and use R-module carriers in u. Let J be a category
with independent object/morphism universes w,v and suppose ModuleCat_u(R) has colimits of shape
J. For fixed K and n∈ℤ, the functor L↦(K^p⊗L^q)_{p+q=n} preserves J-colimits in the
fibre-diagram category. Its component functors are degree-q evaluation followed by tensoring
with K^p. -/
instance tensorLeftIntDegreePieces_preservesColimits
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    PreservesColimitsOfShape J (tensorLeftIntDegreePieces K n) :=
  preservesColimitsOfShape_of_evaluation _ J (fun i => by
    change PreservesColimitsOfShape J
      (HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) i.as.val.2 ⋙ tensorLeft (K.X i.as.val.1))
    infer_instance)

/-- Let R be a commutative ring in universe u and use R-module carriers in u. Use the ℤ-indexed
cochain convolution tensor: all antidiagonal coproducts exist, coefficient tensoring preserves
zero objects in both variables and commutes with the coproducts in both triple
parenthesizations, and fourfold tensor inclusions determine maps. Let J be a category with
independent object/morphism universes w,v and suppose ModuleCat_u(R) has colimits of shape J.
For every ℤ-indexed K, the functor K⊗(-) preserves J-colimits of cochain complexes. Each degree
is the full antidiagonal coproduct of coefficient tensor pieces. -/
instance tensorLeftInt_preservesColimits
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    PreservesColimitsOfShape J (tensorLeft K) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  apply preservesColimitsOfShape_of_natIso (tensorLeftIntEvalIso K n).symm

/-- Let R be a commutative ring in universe u and use R-module carriers in u. Let J be a category
with independent object/morphism universes w,v and suppose ModuleCat_u(R) has colimits of shape
J. For fixed K and n∈ℤ, the functor L↦(L^p⊗K^q)_{p+q=n} preserves J-colimits. Its component
functors are degree-p evaluation followed by tensoring on the right with K^q. -/
instance tensorRightIntDegreePieces_preservesColimits
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    PreservesColimitsOfShape J (tensorRightIntDegreePieces K n) :=
  preservesColimitsOfShape_of_evaluation _ J (fun i => by
    change PreservesColimitsOfShape J
      (HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) i.as.val.1 ⋙ tensorRight (K.X i.as.val.2))
    infer_instance)

/-- Let R be a commutative ring in universe u and use R-module carriers in u. Use the ℤ-indexed
cochain convolution tensor: all antidiagonal coproducts exist, coefficient tensoring preserves
zero objects in both variables and commutes with the coproducts in both triple
parenthesizations, and fourfold tensor inclusions determine maps. Let J be a category with
independent object/morphism universes w,v and suppose ModuleCat_u(R) has colimits of shape J.
For every ℤ-indexed K, (-)⊗K preserves J-colimits of cochain complexes, using all pieces L^p⊗K^q
with p+q=n in each degree. -/
instance tensorRightInt_preservesColimits
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    PreservesColimitsOfShape J (tensorRight K) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  apply preservesColimitsOfShape_of_natIso (tensorRightIntEvalIso K n).symm

end CochainComplex
