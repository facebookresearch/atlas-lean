/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney.ChainMap
public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney.Coassociativity
public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney.Coherence
public import Mathlib.Algebra.Homology.AlternatingConst

/-!
# Alexander–Whitney counits and the oplax alternating-face functor

Let C be a preadditive monoidal category with a zero object and finite coproducts, and tensoring
additive and finite-coproduct-preserving in both variables. The alternating-face complex of the
constant simplicial tensor unit has a canonical map ε to the chain tensor unit. Its degree-zero
component is identity and every positive-degree component is zero.

The Alexander–Whitney maps satisfy AW_{I,X}≫(ε⊗id)≫λ_{A(X)}=A(λ_X) and
AW_{X,I}≫(id⊗ε)≫ρ_{A(X)}=A(ρ_X). Together with naturality and associator coassociativity, these
give A an oplax monoidal structure with counit ε and tensor comparison AW. No invertibility of
the tensor comparison is assumed, and the category universes are independent.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Simplicial

namespace AlgebraicTopology.AlexanderWhitney

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.unusedSectionVars false

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  [(curriedTensor C).Additive]
  [∀ T : C, ((curriedTensor C).obj T).Additive]
  [∀ T : C, PreservesFiniteCoproducts ((curriedTensor C).obj T)]
  [∀ T : C, PreservesFiniteCoproducts ((curriedTensor C).flip.obj T)]

noncomputable local instance counitMonoidalCategoryChainComplexNat :
    MonoidalCategory (ChainComplex C ℕ) :=
  HomologicalComplex.monoidalCategory C (ComplexShape.down ℕ)

private lemma zero_whiskerRight' {A B D : C} :
    (0 : A ⟶ B) ▷ D = 0 := by
  have h := Functor.map_zero (curriedTensor C) (X := A) (Y := B)
  have h' := congrArg (fun a ↦ a.app D) h
  simpa only [curriedTensor_map_app, zero_app] using h'

private lemma whiskerLeft_zero' (A : C) {B D : C} :
    A ◁ (0 : B ⟶ D) = 0 := by
  change ((curriedTensor C).obj A).map (0 : B ⟶ D) = 0
  exact Functor.map_zero ((curriedTensor C).obj A) B D

/-- Let C be a preadditive monoidal category with independent object and morphism universes, a zero
object and finite coproducts. Assume tensoring in each variable is additive and preserves finite
coproducts. Write A for the alternating-face functor from simplicial objects to nonnegative
chain complexes. Let I be the simplicial tensor unit, constant at the tensor unit of C. This
counit ε:A(I)→I_chain is the canonical augmentation to the nonnegative chain tensor unit. It is
identity in degree zero and zero in positive degrees. -/
noncomputable def alternatingMapCounit :
    (AlgebraicTopology.alternatingFaceMapComplex C).obj
        (𝟙_ (SimplicialObject C)) ⟶
      𝟙_ (ChainComplex C ℕ) :=
  AlgebraicTopology.AlternatingFaceMapComplex.ε.app
    (SimplicialObject.Augmented.const.obj (𝟙_ C))

/-- Let C be a preadditive monoidal category with independent object and morphism universes, a zero
object and finite coproducts. Assume tensoring in each variable is additive and preserves finite
coproducts. Write A for the alternating-face functor from simplicial objects to nonnegative
chain complexes. The component ε_0 of ε:A(I_simp)→I_chain equals the identity of the tensor unit
of C under the canonical degree-zero identifications. -/
@[simp]
theorem alternatingMapCounit_f_zero :
    (alternatingMapCounit (C := C)).f 0 = 𝟙 _ := by
  simp [alternatingMapCounit]

/-- Let C be a preadditive monoidal category with independent object and morphism universes, a zero
object and finite coproducts. Assume tensoring in each variable is additive and preserves finite
coproducts. Write A for the alternating-face functor from simplicial objects to nonnegative
chain complexes. For n∈ℕ, the counit ε:A(I_simp)→I_chain has ε_{n+1}=0. The target chain tensor
unit is concentrated in degree zero. -/
@[simp]
theorem alternatingMapCounit_f_succ (n : ℕ) :
    (alternatingMapCounit (C := C)).f (n + 1) = 0 := by
  simp [alternatingMapCounit]

/-- Let C be a preadditive monoidal category with independent object and morphism universes, a zero
object and finite coproducts. Assume tensoring in each variable is additive and preserves finite
coproducts. Write A for the alternating-face functor from simplicial objects to nonnegative
chain complexes. For n∈ℕ with n≠0, the component ε_n of the tensor-unit augmentation
A(I_simp)→I_chain is zero. -/
theorem alternatingMapCounit_f_ne_zero (n : ℕ) (hn : n ≠ 0) :
    (alternatingMapCounit (C := C)).f n = 0 := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ n => exact alternatingMapCounit_f_succ n

private noncomputable def rightCounitTerm (X : SimplicialObject C) (n : ℕ)
    (p : Fin (n + 1)) :
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj
        (X ⊗ 𝟙_ (SimplicialObject C))).X n ⟶
      (HomologicalComplex.tensorObj
        ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
        (HomologicalComplex.tensorUnit C (ComplexShape.down ℕ))).X n :=
  let q := n - p.val
  have h : p.val + q = n := by omega
  (frontFace X h ⊗ₘ backFace (𝟙_ (SimplicialObject C)) h) ≫
    ((((AlgebraicTopology.alternatingFaceMapComplex C).obj X).X p.val) ◁
      (alternatingMapCounit (C := C)).f q) ≫
    HomologicalComplex.ιTensorObj
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
      (HomologicalComplex.tensorUnit C (ComplexShape.down ℕ))
      p.val q n h

private lemma rightCounitTerm_last_aux (X : SimplicialObject C)
    (n q : ℕ) (h : n + q = n) :
    (frontFace X h ⊗ₘ backFace (𝟙_ (SimplicialObject C)) h) ≫
        ((((AlgebraicTopology.alternatingFaceMapComplex C).obj X).X n) ◁
          (alternatingMapCounit (C := C)).f q) ≫
        HomologicalComplex.ιTensorObj
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
          (HomologicalComplex.tensorUnit C (ComplexShape.down ℕ))
          n q n h =
      HomologicalComplex.ιTensorObj
        ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
        (HomologicalComplex.tensorUnit C (ComplexShape.down ℕ))
        n 0 n (Nat.add_zero n) := by
  have hq : q = 0 := by omega
  subst q
  have hunit : backFace (𝟙_ (SimplicialObject C)) h = 𝟙 (𝟙_ C) := by
    dsimp only [backFace, SimplicialObject.δ₀Iter]
    rfl
  simp [hunit]

private lemma rightCounitTerm_last (X : SimplicialObject C) (n : ℕ) :
    rightCounitTerm X n (Fin.last n) =
      HomologicalComplex.ιTensorObj
        ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
        (HomologicalComplex.tensorUnit C (ComplexShape.down ℕ))
        n 0 n (Nat.add_zero n) := by
  rw [rightCounitTerm]
  exact rightCounitTerm_last_aux X n (n - n) (by omega)

private lemma rightCounitTerm_eq_zero (X : SimplicialObject C) (n : ℕ)
    (p : Fin (n + 1)) (hp : p ≠ Fin.last n) :
    rightCounitTerm X n p = 0 := by
  have hpne : p.val ≠ n := by
    intro h
    apply hp
    apply Fin.ext
    simpa using h
  have hp_lt : p.val < n := by omega
  have hq : n - p.val ≠ 0 := by omega
  rw [rightCounitTerm, alternatingMapCounit_f_ne_zero _ hq]
  simp only [whiskerLeft_zero', comp_zero, zero_comp]

/-- Let C be a preadditive monoidal category with independent object and morphism universes, a zero
object and finite coproducts. Assume tensoring in each variable is additive and preserves finite
coproducts. Write A for the alternating-face functor from simplicial objects to nonnegative
chain complexes. For a simplicial X, AW_{I,X}≫(ε⊗id_{A(X)})≫λ_{A(X)}=A(λ_X). The source is
A(I⊗X), and the target is A(X); the left unitor on each side is in its simplicial or chain
tensor category. -/
theorem alternatingMap_left_counit (X : SimplicialObject C) :
    alternatingMap (𝟙_ (SimplicialObject C)) X ≫
        HomologicalComplex.tensorHom (alternatingMapCounit (C := C)) (𝟙 _) ≫
        (HomologicalComplex.leftUnitor
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)).hom =
      (AlgebraicTopology.alternatingFaceMapComplex C).map (λ_ X).hom := by
  rw [← cancel_mono (HomologicalComplex.leftUnitor
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)).inv]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  ext n
  simp only [HomologicalComplex.comp_f, alternatingMap_f]
  rw [alternatingComponent, Preadditive.sum_comp]
  simp only [Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
  simp only [AlgebraicTopology.alternatingFaceMapComplex_map_f]
  change _ = (λ_ X).hom.app (Opposite.op (SimplexCategory.mk n)) ≫
    (HomologicalComplex.leftUnitor'
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)).inv n
  rw [HomologicalComplex.leftUnitor'_inv]
  simp only [Monoidal.tensorObj_obj, Monoidal.tensorUnit_obj,
    alternatingFaceMapComplex_obj_X, curriedTensor_obj_obj, curriedTensor_map_app,
    HomologicalComplex.id_f, curriedTensor_obj_map, whiskerLeft_id,
    Category.id_comp, Monoidal.leftUnitor_hom_app, ChainComplex.single₀_obj_zero,
    ChainComplex.single₀ObjXSelf, Iso.refl_inv, id_whiskerRight,
    Iso.hom_inv_id_assoc]
  rw [Fintype.sum_eq_single (0 : Fin (n + 1))]
  · have hback : backFace X (p := 0) (q := n) (n := n) (Nat.zero_add n) =
        𝟙 (X.obj (Opposite.op (SimplexCategory.mk n))) := by
      simpa only [backFace] using X.δ₀Iter_zero n
    simp [frontFace, hback]
    rfl
  · intro x hx
    rcases x with ⟨x, hxlt⟩
    have hxval : x ≠ 0 := by
      intro h
      apply hx
      apply Fin.ext
      simpa using h
    obtain ⟨y, hy⟩ := Nat.exists_eq_succ_of_ne_zero hxval
    subst x
    rw [alternatingMapCounit_f_succ]
    simp only [zero_whiskerRight', zero_comp, comp_zero]

/-- Let C be a preadditive monoidal category with independent object and morphism universes, a zero
object and finite coproducts. Assume tensoring in each variable is additive and preserves finite
coproducts. Write A for the alternating-face functor from simplicial objects to nonnegative
chain complexes. For a simplicial X, AW_{X,I}≫(id_{A(X)}⊗ε)≫ρ_{A(X)}=A(ρ_X). The source is
A(X⊗I), with the chain right unitor and the image of the simplicial right unitor giving the same
target map. -/
theorem alternatingMap_right_counit (X : SimplicialObject C) :
    alternatingMap X (𝟙_ (SimplicialObject C)) ≫
        HomologicalComplex.tensorHom (𝟙 _) (alternatingMapCounit (C := C)) ≫
        (HomologicalComplex.rightUnitor
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)).hom =
      (AlgebraicTopology.alternatingFaceMapComplex C).map (ρ_ X).hom := by
  rw [← cancel_mono (HomologicalComplex.rightUnitor
    ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)).inv]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  ext n
  simp only [HomologicalComplex.comp_f, alternatingMap_f]
  rw [alternatingComponent, Preadditive.sum_comp]
  simp only [Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
  simp only [AlgebraicTopology.alternatingFaceMapComplex_map_f]
  change _ = (ρ_ X).hom.app (Opposite.op (SimplexCategory.mk n)) ≫
    (HomologicalComplex.rightUnitor'
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)).inv n
  rw [HomologicalComplex.rightUnitor'_inv]
  simp only [Monoidal.tensorObj_obj, Monoidal.tensorUnit_obj,
    alternatingFaceMapComplex_obj_X, curriedTensor_obj_obj,
    HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
    curriedTensor_obj_map, Category.id_comp, Monoidal.rightUnitor_hom_app,
    ChainComplex.single₀_obj_zero, ChainComplex.single₀ObjXSelf, Iso.refl_inv,
    whiskerLeft_id, Iso.hom_inv_id_assoc]
  change (∑ p : Fin (n + 1), rightCounitTerm X n p) = _
  rw [Fintype.sum_eq_single (Fin.last n)]
  · exact rightCounitTerm_last X n
  · exact rightCounitTerm_eq_zero X n

private lemma chainTensorHom_id {K L : ChainComplex C ℕ} (f : K ⟶ L)
    (M : ChainComplex C ℕ) :
    HomologicalComplex.tensorHom f (𝟙 M) = f ▷ M := by
  exact MonoidalCategory.tensorHom_id f M

private lemma chainId_tensorHom (K : ChainComplex C ℕ)
    {L M : ChainComplex C ℕ} (f : L ⟶ M) :
    HomologicalComplex.tensorHom (𝟙 K) f = K ◁ f := by
  exact MonoidalCategory.id_tensorHom K f

/-- Let C be a preadditive monoidal category with independent object and morphism universes, a zero
object and finite coproducts. Assume tensoring in each variable is additive and preserves finite
coproducts. Write A for the alternating-face functor from simplicial objects to nonnegative
chain complexes. The functor A has an oplax monoidal structure whose unit map is
ε:A(I_simp)→I_chain and whose tensor map is AW_{X,Y}:A(X⊗Y)→A(X)⊗A(Y). Its axioms are the
two-variable naturality, associator coassociativity and left/right counit equations of those
maps. -/
noncomputable instance alternatingFaceMapComplexOplaxMonoidal :
    (AlgebraicTopology.alternatingFaceMapComplex C).OplaxMonoidal where
  η := alternatingMapCounit
  δ X Y := alternatingMap X Y
  δ_natural_left {X Y} f Z := by
    have h := (alternatingMap_naturality (C := C) f (𝟙 Z)).symm
    simp only [CategoryTheory.Functor.map_id] at h
    rw [chainTensorHom_id, MonoidalCategory.tensorHom_id] at h
    exact h
  δ_natural_right {X Y} W f := by
    have h := (alternatingMap_naturality (C := C) (𝟙 W) f).symm
    simp only [CategoryTheory.Functor.map_id] at h
    rw [chainId_tensorHom, MonoidalCategory.id_tensorHom] at h
    exact h
  oplax_associativity X Y Z := by
    have h := alternatingMap_assoc (C := C) X Y Z
    rw [chainTensorHom_id, chainId_tensorHom] at h
    exact h
  oplax_left_unitality X := by
    rw [← cancel_mono (λ_ ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)).hom]
    simp only [Iso.inv_hom_id, Category.assoc]
    rw [← chainTensorHom_id]
    change 𝟙 _ =
      (AlgebraicTopology.alternatingFaceMapComplex C).map (λ_ X).inv ≫
        alternatingMap (𝟙_ (SimplicialObject C)) X ≫
          HomologicalComplex.tensorHom alternatingMapCounit
            (𝟙 ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)) ≫
              (HomologicalComplex.leftUnitor
                ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)).hom
    have h := congrArg
      (fun t => (AlgebraicTopology.alternatingFaceMapComplex C).map (λ_ X).inv ≫ t)
      (alternatingMap_left_counit (C := C) X)
    rw [h]
    rw [← Functor.map_comp]
    simp
  oplax_right_unitality X := by
    rw [← cancel_mono (ρ_ ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)).hom]
    simp only [Iso.inv_hom_id, Category.assoc]
    rw [← chainId_tensorHom]
    change 𝟙 _ =
      (AlgebraicTopology.alternatingFaceMapComplex C).map (ρ_ X).inv ≫
        alternatingMap X (𝟙_ (SimplicialObject C)) ≫
          HomologicalComplex.tensorHom
            (𝟙 ((AlgebraicTopology.alternatingFaceMapComplex C).obj X))
            alternatingMapCounit ≫
              (HomologicalComplex.rightUnitor
                ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)).hom
    have h := congrArg
      (fun t => (AlgebraicTopology.alternatingFaceMapComplex C).map (ρ_ X).inv ≫ t)
      (alternatingMap_right_counit (C := C) X)
    rw [h]
    rw [← Functor.map_comp]
    simp

end AlgebraicTopology.AlexanderWhitney
