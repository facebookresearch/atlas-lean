/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Unbiased.OrderedTensor
public import MathlibExt.CategoryTheory.Monoidal.Unbiased.FiniteFamily
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.Data.Fin.Embedding
public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Sum
public import MathlibExt.CategoryTheory.Monoidal.SymmetricTensorPower
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Iso
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Fin
public import MathlibExt.CategoryTheory.Monoidal.Unbiased.FiniteTensor
public import Mathlib.CategoryTheory.Monoidal.Category
public import MathlibExt.CategoryTheory.Monoidal.Unbiased.FiniteTensorInterfaces
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import MathlibExt.CategoryTheory.Monoidal.TensorPowers

/-!
# SymmetricFiniteTensor

Coherent finite heterogeneous tensors constructed from binary symmetric monoidal structure.
-/

/- Source proof segment: FiniteTensorCarrier -/
section source_FiniteTensorCarrier
/-!
# The actual finite tensor carrier from a binary monoidal category

An arbitrary finite input family is enumerated by its original finite
index type and tensorized using the original binary product and unit.
Reindexing and flatten coherence are added separately.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

attribute [local instance] FintypeCat.fintype

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The original finite input count of a family. -/
noncomputable def arity (X : FiniteFamily C) : ℕ := Fintype.card X.index

/-- Enumerate the original finite inputs without changing the object universe. -/
noncomputable def enumeration (X : FiniteFamily C) : Fin (arity X) ≃ X.index :=
  (Fintype.equivFin X.index).symm

/-- The ordered family obtained from the original finite input enumeration. -/
noncomputable def orderedFamily (X : FiniteFamily C) : Fin (arity X) → C :=
  X.obj ∘ enumeration X

/-- Tensor all objects of the original finite family using the supplied binary tensor. -/
noncomputable def finiteObj (X : FiniteFamily C) : C := obj (orderedFamily X)

/-- The tensor of the original empty finite family is the original tensor unit. -/
@[simp] theorem finiteObj_empty : finiteObj (FiniteFamily.empty : FiniteFamily C) = 𝟙_ C := by
  have h : arity (FiniteFamily.empty : FiniteFamily C) = 0 := by
    unfold arity FiniteFamily.empty
    exact @Fintype.card_eq_zero Empty (@FintypeCat.fintype (FintypeCat.of Empty))
      (inferInstanceAs (IsEmpty Empty))
  exact obj_congr h (orderedFamily (FiniteFamily.empty : FiniteFamily C))
    (Fin.elim0 : Fin 0 → C) (fun i => (Fin.cast h i).elim0)

/-- The unary carrier uses the actual left unitor of its original object. -/
noncomputable def finiteSingletonIso (X : C) :
    finiteObj ((FiniteFamily.singleton (C := C)).obj X) ≅ X := by
  have h : arity ((FiniteFamily.singleton (C := C)).obj X) = 1 := by
    unfold arity FiniteFamily.singleton
    exact @Fintype.card_unique PUnit.{1} (inferInstanceAs (Unique PUnit.{1}))
      (@FintypeCat.fintype (FintypeCat.of PUnit.{1}))
  exact congrIso h (orderedFamily ((FiniteFamily.singleton (C := C)).obj X))
      (fun _ : Fin 1 => X) (fun _ => rfl) ≪≫ singletonIso (fun _ : Fin 1 => X)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FiniteTensorCarrier

/- Source proof segment: FiniteTensorFixedIndex -/
section source_FiniteTensorFixedIndex
/-!
# Fixed-index maps of the original finite tensor carrier

For a fixed original finite index, maps are tensorized componentwise
through the original enumeration. This gives the exact map readback
used by finite tensor colimit diagrams.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

attribute [local instance] FintypeCat.fintype

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The original finite tensor carrier on an explicitly fixed input type. -/
noncomputable def fixedIndexObj (I : FintypeCat.{0}) (X : I → C) : C :=
  obj (X ∘ (Fintype.equivFin I).symm)

/-- Tensor the actual component maps at one fixed original finite input type. -/
noncomputable def fixedIndexMap (I : FintypeCat.{0}) {X Y : I → C}
    (f : ∀ i, X i ⟶ Y i) : fixedIndexObj I X ⟶ fixedIndexObj I Y :=
  map (fun i => f ((Fintype.equivFin I).symm i))

/-- Fixed-index identities tensor to the original identity. -/
@[simp] theorem fixedIndexMap_id (I : FintypeCat.{0}) (X : I → C) :
    fixedIndexMap I (fun i => 𝟙 (X i)) = 𝟙 (fixedIndexObj I X) :=
  map_id (X ∘ (Fintype.equivFin I).symm)

/-- Fixed-index composites tensor to the composite of the original tensor maps. -/
theorem fixedIndexMap_comp (I : FintypeCat.{0}) {X Y Z : I → C}
    (f : ∀ i, X i ⟶ Y i) (g : ∀ i, Y i ⟶ Z i) :
    fixedIndexMap I (fun i => f i ≫ g i) = fixedIndexMap I f ≫ fixedIndexMap I g :=
  map_comp (fun i => f ((Fintype.equivFin I).symm i))
    (fun i => g ((Fintype.equivFin I).symm i))

/-- The original finite-family carrier at a fixed input type is exactly its ordered tensor. -/
theorem finiteObj_fixedIndex (I : FintypeCat.{0}) (X : I → C) :
    finiteObj (⟨I, X⟩ : FiniteFamily C) = fixedIndexObj I X := rfl

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FiniteTensorFixedIndex

/- Source proof segment: OrderedSymmetry -/
section source_OrderedSymmetry
/-!
# Heterogeneous adjacent tensor symmetries

The last two factors of a tensor can be interchanged using the supplied
braiding and associators. These maps are natural in every factor. Their
braid relation works with three different factors and an arbitrary prefix.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section Braided

variable [BraidedCategory C]

/-- Interchange the last two different tensor factors after an arbitrary prefix. -/
def swapLastIso (P X Y : C) : (P ⊗ X) ⊗ Y ≅ (P ⊗ Y) ⊗ X :=
  (α_ P X Y) ≪≫ whiskerLeftIso P (β_ X Y) ≪≫ (α_ P Y X).symm

/-- The adjacent interchange is natural in the prefix and in both factors. -/
@[reassoc] theorem swapLastIso_naturality {P X Y P' X' Y' : C}
    (f : P ⟶ P') (g : X ⟶ X') (h : Y ⟶ Y') :
    ((f ⊗ₘ g) ⊗ₘ h) ≫ (swapLastIso P' X' Y').hom =
      (swapLastIso P X Y).hom ≫ ((f ⊗ₘ h) ⊗ₘ g) := by
  have hb : (f ⊗ₘ (g ⊗ₘ h)) ≫ (P' ◁ (β_ X' Y').hom) =
      (P ◁ (β_ X Y).hom) ≫ (f ⊗ₘ (h ⊗ₘ g)) := by
    simpa only [← id_tensorHom, tensorHom_comp_tensorHom,
      Category.comp_id, Category.id_comp] using
      congrArg (f ⊗ₘ ·) (BraidedCategory.braiding_naturality g h)
  simp only [swapLastIso, Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom,
    Category.assoc]
  rw [associator_naturality_assoc]
  rw [← Category.assoc (f ⊗ₘ (g ⊗ₘ h)), hb]
  simp only [Category.assoc, associator_inv_naturality]

/-- Adjacent interchanges satisfy the braid relation after an arbitrary prefix. -/
theorem swapLastIso_braid (P X Y Z : C) :
    tensorIso (swapLastIso P X Y) (Iso.refl Z) ≪≫
        swapLastIso (P ⊗ Y) X Z ≪≫
        tensorIso (swapLastIso P Y Z) (Iso.refl X) =
      swapLastIso (P ⊗ X) Y Z ≪≫
        tensorIso (swapLastIso P X Z) (Iso.refl Y) ≪≫
        swapLastIso (P ⊗ Z) X Y := by
  let q (A B D : C) : ((P ⊗ A) ⊗ B) ⊗ D ≅ P ⊗ (A ⊗ (B ⊗ D)) :=
    (α_ (P ⊗ A) B D) ≪≫ α_ P A (B ⊗ D)
  let r₁₂ (A B D : C) : A ⊗ (B ⊗ D) ≅ B ⊗ (A ⊗ D) :=
    (α_ A B D).symm ≪≫ whiskerRightIso (β_ A B) D ≪≫ α_ B A D
  let r₂₃ (A B D : C) : A ⊗ (B ⊗ D) ≅ A ⊗ (D ⊗ B) :=
    whiskerLeftIso A (β_ B D)
  let Q {A B D A' B' D' : C} (t : A ⊗ (B ⊗ D) ≅ A' ⊗ (B' ⊗ D')) :=
    q A B D ≪≫ whiskerLeftIso P t ≪≫ (q A' B' D').symm
  have hQ {A B D A' B' D' A'' B'' D'' : C}
      (t : A ⊗ (B ⊗ D) ≅ A' ⊗ (B' ⊗ D'))
      (s : A' ⊗ (B' ⊗ D') ≅ A'' ⊗ (B'' ⊗ D'')) :
      Q (t ≪≫ s) = Q t ≪≫ Q s := by
    simp only [Q, whiskerLeftIso_trans, Iso.trans_assoc, Iso.symm_self_id_assoc]
  have h₁₂ (A B D : C) :
      Q (r₁₂ A B D) = tensorIso (swapLastIso P A B) (Iso.refl D) := by
    apply Iso.ext
    dsimp only [Q, q, r₁₂, swapLastIso]
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
      whiskerLeftIso_hom, whiskerRightIso_hom, tensorIso_hom, Iso.refl_hom]
    monoidal
  have h₂₃ (A B D : C) : Q (r₂₃ A B D) = swapLastIso (P ⊗ A) B D := by
    apply Iso.ext
    dsimp only [Q, q, r₂₃, swapLastIso]
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, whiskerLeftIso_hom]
    monoidal
  have hcore : r₁₂ X Y Z ≪≫ r₂₃ Y X Z ≪≫ r₁₂ Y Z X =
      r₂₃ X Y Z ≪≫ r₁₂ X Z Y ≪≫ r₂₃ Z X Y := by
    simpa only [r₁₂, r₂₃, Iso.trans_assoc] using BraidedCategory.yang_baxter_iso X Y Z
  have hh := congrArg Q hcore
  rw [hQ, hQ, hQ, hQ, h₁₂, h₂₃, h₁₂, h₂₃, h₁₂, h₂₃] at hh
  exact hh

end Braided

section Symmetric

variable [SymmetricCategory C]

/-- Repeating the adjacent interchange restores the original tensor. -/
theorem swapLastIso_involutive (P X Y : C) :
    swapLastIso P X Y ≪≫ swapLastIso P Y X = Iso.refl _ := by
  apply Iso.ext
  simp only [swapLastIso, Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom,
    Iso.refl_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← whiskerLeft_comp_assoc, SymmetricCategory.symmetry, whiskerLeft_id]
  simp only [Category.id_comp, Iso.hom_inv_id]

end Symmetric

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedSymmetry

/- Source proof segment: OrderedAdjacent -/
section source_OrderedAdjacent
/-!
# Actual adjacent permutations of heterogeneous finite tensors

The reindexing here is the actual adjacent transposition of the finite
input type. Its tensor map is recursively built from the original
braiding and binary associators, with all other factors retained.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The last adjacent transposition interchanges the last two objects
and fixes the entire initial tensor block. -/
theorem obj_swapLast {n : ℕ} (X : Fin (n + 2) → C) :
    obj (X ∘ Equiv.swap (Fin.last n).castSucc (Fin.last n).succ) =
      (obj (fun i : Fin n => X i.castSucc.castSucc) ⊗ X (Fin.last (n + 1))) ⊗
        X (Fin.last n).castSucc := by
  have hp : (fun i : Fin n =>
      X (Equiv.swap (Fin.last n).castSucc (Fin.last n).succ i.castSucc.castSucc)) =
      (fun i : Fin n => X i.castSucc.castSucc) := by
    funext i
    rw [Equiv.swap_apply_of_ne_of_ne]
    · exact fun h => Fin.castSucc_ne_last i ((Fin.castSucc_injective (n + 1)) h)
    · exact Fin.castSucc_ne_last i.castSucc
  change (obj (fun i : Fin n =>
      X (Equiv.swap (Fin.last n).castSucc (Fin.last n).succ i.castSucc.castSucc)) ⊗
      X (Equiv.swap (Fin.last n).castSucc (Fin.last n).succ (Fin.last n).castSucc)) ⊗
      X (Equiv.swap (Fin.last n).castSucc (Fin.last n).succ (Fin.last (n + 1))) = _
  rw [hp, Equiv.swap_apply_left]
  change (obj (fun i : Fin n => X i.castSucc.castSucc) ⊗ X (Fin.last (n + 1))) ⊗
    X (Equiv.swap (Fin.last n).castSucc (Fin.last n).succ (Fin.last n).succ) = _
  rw [Equiv.swap_apply_right]

/-- An adjacent transposition inside the initial block commutes with
adding the last factor. -/
theorem obj_swapLower {n : ℕ} (X : Fin (n + 2) → C) (j : Fin n) :
    obj (X ∘ Equiv.swap j.castSucc.castSucc j.castSucc.succ) =
      obj (Fin.init X ∘ Equiv.swap j.castSucc j.succ) ⊗ X (Fin.last (n + 1)) := by
  have hp : (fun i : Fin (n + 1) =>
      X (Equiv.swap j.castSucc.castSucc j.castSucc.succ i.castSucc)) =
      (Fin.init X ∘ Equiv.swap j.castSucc j.succ) := by
    funext i
    change X (Equiv.swap j.castSucc.castSucc j.castSucc.succ i.castSucc) =
      X (Equiv.swap j.castSucc j.succ i).castSucc
    rw [Fin.succ_castSucc]
    rw [(Fin.castSucc_injective (n + 1)).swap_apply]
  change obj (fun i : Fin (n + 1) =>
      X (Equiv.swap j.castSucc.castSucc j.castSucc.succ i.castSucc)) ⊗
      X (Equiv.swap j.castSucc.castSucc j.castSucc.succ (Fin.last (n + 1))) = _
  rw [hp, Equiv.swap_apply_of_ne_of_ne]
  · exact (Fin.castSucc_ne_last j.castSucc).symm
  · simpa only [Fin.succ_castSucc] using (Fin.castSucc_ne_last j.succ).symm

section Braided

variable [BraidedCategory C]

/-- The actual adjacent transposition on the tensor of an arbitrary
heterogeneous ordered input family. -/
def adjacentIso : {n : ℕ} → (X : Fin (n + 1) → C) → (i : Fin n) →
    obj X ≅ obj (X ∘ Equiv.swap i.castSucc i.succ)
  | 0, _, i => Fin.elim0 i
  | n + 1, X, i => Fin.lastCases
      (swapLastIso (obj (fun j : Fin n => X j.castSucc.castSucc))
          (X (Fin.last n).castSucc) (X (Fin.last (n + 1))) ≪≫
        eqToIso (obj_swapLast X).symm)
      (fun j => tensorIso (adjacentIso (Fin.init X) j) (Iso.refl (X (Fin.last (n + 1)))) ≪≫
        eqToIso (obj_swapLower X j).symm)
      i

/-- The last adjacent tensor map is the original prefix-adjusted braiding. -/
theorem adjacentIso_last_hom {n : ℕ} (X : Fin (n + 2) → C) :
    (adjacentIso X (Fin.last n)).hom =
      (swapLastIso (obj (fun j : Fin n => X j.castSucc.castSucc))
        (X (Fin.last n).castSucc) (X (Fin.last (n + 1)))).hom ≫
        eqToHom (obj_swapLast X).symm := by
  simp only [adjacentIso, Fin.lastCases_last]
  rfl

/-- A lower adjacent tensor map retains the last factor and tensors its
actual recursive transposition with the identity of that factor. -/
theorem adjacentIso_castSucc_hom {n : ℕ} (X : Fin (n + 2) → C) (j : Fin n) :
    (adjacentIso X j.castSucc).hom =
      ((adjacentIso (Fin.init X) j).hom ⊗ₘ 𝟙 (X (Fin.last (n + 1)))) ≫
        eqToHom (obj_swapLower X j).symm := by
  simp only [adjacentIso, Fin.lastCases_castSucc]
  rfl

end Braided

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedAdjacent

/- Source proof segment: OrderedFunctorShapes -/
section source_OrderedFunctorShapes
/-!
# Natural finite tensor reindexing shapes

These comparisons are equalities of actual functors, obtained from the
corresponding equalities of finite index maps. Thus their component
transport maps satisfy naturality for all component morphisms.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Successor decomposition of the actual heterogeneous tensor functor. -/
theorem functor_succ (n : ℕ) :
    functor C (n + 1) =
      ((Pi.comap (fun _ : Fin (n + 1) => C) Fin.castSucc ⋙ functor C n).prod'
        (Pi.eval (fun _ : Fin (n + 1) => C) (Fin.last n))) ⋙ tensor C := by
  rfl

omit [MonoidalCategory C] in
/-- A lower finite transposition commutes with restricting to the initial family. -/
theorem comap_swapLower_init {n : ℕ} (j : Fin n) :
    Pi.comap (fun _ : Fin (n + 2) => C)
        (Equiv.swap j.castSucc.castSucc j.castSucc.succ) ⋙
      Pi.comap (fun _ : Fin (n + 2) => C) Fin.castSucc =
    Pi.comap (fun _ : Fin (n + 2) => C) Fin.castSucc ⋙
      Pi.comap (fun _ : Fin (n + 1) => C) (Equiv.swap j.castSucc j.succ) := by
  have hi : (Equiv.swap j.castSucc.castSucc j.castSucc.succ) ∘ Fin.castSucc =
      Fin.castSucc ∘ (Equiv.swap j.castSucc j.succ) := by
    simpa only [Fin.succ_castSucc] using
      (Fin.castSucc_injective (n + 1)).swap_comp j.castSucc j.succ
  change Pi.comap (fun _ : Fin (n + 2) => C)
      ((Equiv.swap j.castSucc.castSucc j.castSucc.succ) ∘ Fin.castSucc) =
    Pi.comap (fun _ : Fin (n + 2) => C)
      (Fin.castSucc ∘ (Equiv.swap j.castSucc j.succ))
  rw [hi]

omit [MonoidalCategory C] in
/-- A lower finite transposition fixes evaluation at the last factor. -/
theorem comap_swapLower_last {n : ℕ} (j : Fin n) :
    Pi.comap (fun _ : Fin (n + 2) => C)
        (Equiv.swap j.castSucc.castSucc j.castSucc.succ) ⋙
      Pi.eval (fun _ : Fin (n + 2) => C) (Fin.last (n + 1)) =
    Pi.eval (fun _ : Fin (n + 2) => C) (Fin.last (n + 1)) := by
  have hi : Equiv.swap j.castSucc.castSucc j.castSucc.succ (Fin.last (n + 1)) =
      Fin.last (n + 1) := by
    apply Equiv.swap_apply_of_ne_of_ne
    · exact (Fin.castSucc_ne_last j.castSucc).symm
    · simpa only [Fin.succ_castSucc] using (Fin.castSucc_ne_last j.succ).symm
  change Pi.eval (fun _ : Fin (n + 2) => C)
      (Equiv.swap j.castSucc.castSucc j.castSucc.succ (Fin.last (n + 1))) = _
  rw [hi]

omit [MonoidalCategory C] in
/-- The last finite transposition fixes the entire initial family before its two slots. -/
theorem comap_swapLast_prefix (n : ℕ) :
    Pi.comap (fun _ : Fin (n + 2) => C)
        (Equiv.swap (Fin.last n).castSucc (Fin.last n).succ) ⋙
      Pi.comap (fun _ : Fin (n + 2) => C)
        (fun i : Fin n => i.castSucc.castSucc) =
    Pi.comap (fun _ : Fin (n + 2) => C)
      (fun i : Fin n => i.castSucc.castSucc) := by
  have hi : (Equiv.swap (Fin.last n).castSucc (Fin.last n).succ) ∘
      (fun i : Fin n => i.castSucc.castSucc) =
      (fun i : Fin n => i.castSucc.castSucc) := by
    funext i
    exact Equiv.swap_apply_of_ne_of_ne
      (fun h => Fin.castSucc_ne_last i ((Fin.castSucc_injective (n + 1)) h))
      (Fin.castSucc_ne_last i.castSucc)
  change Pi.comap (fun _ : Fin (n + 2) => C)
      ((Equiv.swap (Fin.last n).castSucc (Fin.last n).succ) ∘
        (fun i : Fin n => i.castSucc.castSucc)) = _
  rw [hi]

omit [MonoidalCategory C] in
/-- The last transposition sends evaluation at the penultimate slot to the last slot. -/
theorem comap_swapLast_penultimate (n : ℕ) :
    Pi.comap (fun _ : Fin (n + 2) => C)
        (Equiv.swap (Fin.last n).castSucc (Fin.last n).succ) ⋙
      Pi.eval (fun _ : Fin (n + 2) => C) (Fin.last n).castSucc =
    Pi.eval (fun _ : Fin (n + 2) => C) (Fin.last (n + 1)) := by
  change Pi.eval (fun _ : Fin (n + 2) => C)
      (Equiv.swap (Fin.last n).castSucc (Fin.last n).succ (Fin.last n).castSucc) = _
  rw [Equiv.swap_apply_left]
  rfl

omit [MonoidalCategory C] in
/-- The last transposition sends evaluation at the last slot to the penultimate slot. -/
theorem comap_swapLast_last (n : ℕ) :
    Pi.comap (fun _ : Fin (n + 2) => C)
        (Equiv.swap (Fin.last n).castSucc (Fin.last n).succ) ⋙
      Pi.eval (fun _ : Fin (n + 2) => C) (Fin.last (n + 1)) =
    Pi.eval (fun _ : Fin (n + 2) => C) (Fin.last n).castSucc := by
  change Pi.eval (fun _ : Fin (n + 2) => C)
      (Equiv.swap (Fin.last n).castSucc (Fin.last n).succ (Fin.last n).succ) = _
  rw [Equiv.swap_apply_right]

/-- Natural tensor decomposition for a transposition inside the initial block. -/
def lowerSwapShapeIso {n : ℕ} (j : Fin n) :
    Pi.comap (fun _ : Fin (n + 2) => C)
        (Equiv.swap j.castSucc.castSucc j.castSucc.succ) ⋙ functor C (n + 2) ≅
      (((Pi.comap (fun _ : Fin (n + 2) => C) Fin.castSucc ⋙
          Pi.comap (fun _ : Fin (n + 1) => C) (Equiv.swap j.castSucc j.succ)) ⋙
        functor C (n + 1)).prod'
        (Pi.eval (fun _ : Fin (n + 2) => C) (Fin.last (n + 1)))) ⋙ tensor C :=
  eqToIso (by
    change (((Pi.comap (fun _ : Fin (n + 2) => C)
          (Equiv.swap j.castSucc.castSucc j.castSucc.succ) ⋙
          Pi.comap (fun _ : Fin (n + 2) => C) Fin.castSucc) ⋙
        functor C (n + 1)).prod'
        (Pi.comap (fun _ : Fin (n + 2) => C)
          (Equiv.swap j.castSucc.castSucc j.castSucc.succ) ⋙
          Pi.eval (fun _ : Fin (n + 2) => C) (Fin.last (n + 1)))) ⋙ tensor C = _
    rw [comap_swapLower_init, comap_swapLower_last])

/-- Natural tensor decomposition for the transposition of the final two slots. -/
def lastSwapShapeIso (n : ℕ) :
    Pi.comap (fun _ : Fin (n + 2) => C)
        (Equiv.swap (Fin.last n).castSucc (Fin.last n).succ) ⋙ functor C (n + 2) ≅
      (((Pi.comap (fun _ : Fin (n + 2) => C)
          (fun i : Fin n => i.castSucc.castSucc) ⋙ functor C n).prod'
          (Pi.eval (fun _ : Fin (n + 2) => C) (Fin.last (n + 1)))) ⋙ tensor C).prod'
        (Pi.eval (fun _ : Fin (n + 2) => C) (Fin.last n).castSucc) ⋙ tensor C :=
  eqToIso (by
    change ((((Pi.comap (fun _ : Fin (n + 2) => C)
          (Equiv.swap (Fin.last n).castSucc (Fin.last n).succ) ⋙
          Pi.comap (fun _ : Fin (n + 2) => C)
            (fun i : Fin n => i.castSucc.castSucc)) ⋙ functor C n).prod'
          (Pi.comap (fun _ : Fin (n + 2) => C)
            (Equiv.swap (Fin.last n).castSucc (Fin.last n).succ) ⋙
            Pi.eval (fun _ : Fin (n + 2) => C) (Fin.last n).castSucc)) ⋙ tensor C).prod'
        (Pi.comap (fun _ : Fin (n + 2) => C)
          (Equiv.swap (Fin.last n).castSucc (Fin.last n).succ) ⋙
          Pi.eval (fun _ : Fin (n + 2) => C) (Fin.last (n + 1))) ⋙ tensor C = _
    rw [comap_swapLast_prefix, comap_swapLast_penultimate, comap_swapLast_last])

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedFunctorShapes

/- Source proof segment: OrderedAdjacentNaturality -/
section source_OrderedAdjacentNaturality
/-!
# Naturality of the actual adjacent finite tensor permutations

The transport maps in the recursive transposition construction are
components of equalities of actual finite tensor functors. Their
naturality combines with the original binary braiding naturality.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Inverse lower-transposition shape transports commute with all component maps. -/
@[reassoc] theorem map_swapLower_inv {n : ℕ} {X Y : Fin (n + 2) → C}
    (f : ∀ i, X i ⟶ Y i) (j : Fin n) :
    (map (fun i : Fin (n + 1) => f (Equiv.swap j.castSucc j.succ i).castSucc) ⊗ₘ
        f (Fin.last (n + 1))) ≫ eqToHom (obj_swapLower Y j).symm =
      eqToHom (obj_swapLower X j).symm ≫
        map (fun i => f (Equiv.swap j.castSucc.castSucc j.castSucc.succ i)) := by
  have h := (lowerSwapShapeIso (C := C) j).inv.naturality f
  simp only [lowerSwapShapeIso, eqToIso.inv, eqToHom_app] at h
  change (map (fun i : Fin (n + 1) => f (Equiv.swap j.castSucc j.succ i).castSucc) ⊗ₘ
      f (Fin.last (n + 1))) ≫ eqToHom (obj_swapLower Y j).symm =
    eqToHom (obj_swapLower X j).symm ≫
      map (fun i => f (Equiv.swap j.castSucc.castSucc j.castSucc.succ i)) at h
  exact h

/-- Inverse last-transposition shape transports commute with all component maps. -/
@[reassoc] theorem map_swapLast_inv {n : ℕ} {X Y : Fin (n + 2) → C}
    (f : ∀ i, X i ⟶ Y i) :
    ((map (fun i : Fin n => f i.castSucc.castSucc) ⊗ₘ f (Fin.last (n + 1))) ⊗ₘ
        f (Fin.last n).castSucc) ≫ eqToHom (obj_swapLast Y).symm =
      eqToHom (obj_swapLast X).symm ≫
        map (fun i => f (Equiv.swap (Fin.last n).castSucc (Fin.last n).succ i)) := by
  have h := (lastSwapShapeIso (C := C) n).inv.naturality f
  simp only [lastSwapShapeIso, eqToIso.inv, eqToHom_app] at h
  change ((map (fun i : Fin n => f i.castSucc.castSucc) ⊗ₘ f (Fin.last (n + 1))) ⊗ₘ
      f (Fin.last n).castSucc) ≫ eqToHom (obj_swapLast Y).symm =
    eqToHom (obj_swapLast X).symm ≫
      map (fun i => f (Equiv.swap (Fin.last n).castSucc (Fin.last n).succ i)) at h
  exact h

variable [BraidedCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The original adjacent finite transposition is natural in every actual input morphism. -/
@[reassoc] theorem adjacentIso_naturality : ∀ {n : ℕ} {X Y : Fin (n + 1) → C}
    (f : ∀ i, X i ⟶ Y i) (i : Fin n),
    map f ≫ (adjacentIso Y i).hom =
      (adjacentIso X i).hom ≫ map (fun j => f (Equiv.swap i.castSucc i.succ j))
  | 0, _, _, _, i => Fin.elim0 i
  | n + 1, X, Y, f, i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [adjacentIso_last_hom, adjacentIso_last_hom]
        change (((map (fun j : Fin n => f j.castSucc.castSucc) ⊗ₘ
            f (Fin.last n).castSucc) ⊗ₘ f (Fin.last (n + 1))) ≫
          (swapLastIso (obj (fun j : Fin n => Y j.castSucc.castSucc))
            (Y (Fin.last n).castSucc) (Y (Fin.last (n + 1)))).hom ≫
          eqToHom (obj_swapLast Y).symm) =
          ((swapLastIso (obj (fun j : Fin n => X j.castSucc.castSucc))
            (X (Fin.last n).castSucc) (X (Fin.last (n + 1)))).hom ≫
            eqToHom (obj_swapLast X).symm) ≫
            map (fun j => f (Equiv.swap (Fin.last n).castSucc (Fin.last n).succ j))
        rw [← Category.assoc, swapLastIso_naturality]
        rw [Category.assoc, map_swapLast_inv]
        simp only [Category.assoc]
      · rw [adjacentIso_castSucc_hom, adjacentIso_castSucc_hom]
        let f₀ : ∀ k : Fin (n + 1), (Fin.init X) k ⟶ (Fin.init Y) k :=
          fun k => f k.castSucc
        have hrec := adjacentIso_naturality (n := n) (X := Fin.init X)
          (Y := Fin.init Y) f₀ j
        have hfirst :
            (map f₀ ⊗ₘ f (Fin.last (n + 1))) ≫
                ((adjacentIso (Fin.init Y) j).hom ⊗ₘ 𝟙 (Y (Fin.last (n + 1)))) =
              ((adjacentIso (Fin.init X) j).hom ⊗ₘ 𝟙 (X (Fin.last (n + 1)))) ≫
                (map (fun k : Fin (n + 1) =>
                    f (Equiv.swap j.castSucc j.succ k).castSucc) ⊗ₘ
                  f (Fin.last (n + 1))) := by
          rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
            Category.comp_id, Category.id_comp]
          exact congrArg (· ⊗ₘ f (Fin.last (n + 1))) hrec
        change (map f₀ ⊗ₘ f (Fin.last (n + 1))) ≫
            ((adjacentIso (Fin.init Y) j).hom ⊗ₘ 𝟙 (Y (Fin.last (n + 1)))) ≫
            eqToHom (obj_swapLower Y j).symm =
            (((adjacentIso (Fin.init X) j).hom ⊗ₘ 𝟙 (X (Fin.last (n + 1)))) ≫
              eqToHom (obj_swapLower X j).symm) ≫
              map (fun k => f (Equiv.swap j.castSucc.castSucc j.castSucc.succ k))
        rw [← Category.assoc, hfirst, Category.assoc, map_swapLower_inv]
        simp only [Category.assoc]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedAdjacentNaturality

/- Source proof segment: OrderedAdjacentNatIso -/
section source_OrderedAdjacentNatIso
/-!
# Natural isomorphisms of the actual adjacent tensor permutations

These are the full natural transformations used as the adjacent
generators for the finite permutation action on heterogeneous tensors.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The actual adjacent transposition as a natural isomorphism of tensor functors. -/
def adjacentNatIso {n : ℕ} (i : Fin n) :
    functor C (n + 1) ≅
      Pi.comap (fun _ : Fin (n + 1) => C) (Equiv.swap i.castSucc i.succ) ⋙
        functor C (n + 1) :=
  NatIso.ofComponents (fun X => adjacentIso X i) (by
    intro X Y f
    exact adjacentIso_naturality f i)

/-- Forward natural-isomorphism components are exactly the original tensor transpositions. -/
theorem adjacentNatIso_hom_app {n : ℕ} (i : Fin n) (X : Fin (n + 1) → C) :
    (adjacentNatIso (C := C) i).hom.app X = (adjacentIso X i).hom := rfl

/-- Inverse natural-isomorphism components retain the actual inverse transposition maps. -/
theorem adjacentNatIso_inv_app {n : ℕ} (i : Fin n) (X : Fin (n + 1) → C) :
    (adjacentNatIso (C := C) i).inv.app X = (adjacentIso X i).inv := rfl

/-- The same actual adjacent generator in the inverse-reindexing convention of groups. -/
def adjacentInverseNatIso {n : ℕ} (i : Fin n) :
    functor C (n + 1) ≅
      Pi.comap (fun _ : Fin (n + 1) => C) (Equiv.swap i.castSucc i.succ).symm ⋙
        functor C (n + 1) := by
  simpa only [Equiv.symm_swap] using adjacentNatIso (C := C) i

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedAdjacentNatIso

/- Source proof segment: OrderedYoneda -/
section source_OrderedYoneda
/-!
# The sum of the ordered tensor representables

Tensor symmetries act on this genuine functor to types. The standard
automorphism group of the functor supplies a group in which finite
permutation relations can be checked and transported back by Yoneda.
No colimit in the original category is assumed here.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory Opposite

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The actual coproduct of all ordered tensor representables at a fixed arity. -/
def totalYoneda (n : ℕ) : Cᵒᵖ ⥤ Type (max u v) where
  obj P := Σ X : Fin n → C, P.unop ⟶ obj X
  map f := ↾fun z => ⟨z.1, f.unop ≫ z.2⟩
  map_id P := by
    apply ConcreteCategory.hom_ext
    rintro ⟨X, h⟩
    change (⟨X, (𝟙 P).unop ≫ h⟩ : Σ X : Fin n → C, P.unop ⟶ obj X) = ⟨X, h⟩
    simp only [unop_id, Category.id_comp]
  map_comp {P Q R} f g := by
    apply ConcreteCategory.hom_ext
    rintro ⟨X, h⟩
    change (⟨X, (f ≫ g).unop ≫ h⟩ : Σ X : Fin n → C, R.unop ⟶ obj X) =
      ⟨X, g.unop ≫ f.unop ≫ h⟩
    simp only [unop_comp, Category.assoc]

/-- A bijection of the actual index families and an isomorphism of each
tensor induce a bijection on the sum of the represented hom sets. -/
def totalHomEquiv {n : ℕ} (e : (Fin n → C) ≃ (Fin n → C))
    (a : ∀ X, obj X ≅ obj (e X)) (P : C) :
    (Σ X : Fin n → C, P ⟶ obj X) ≃ (Σ X : Fin n → C, P ⟶ obj X) :=
  Equiv.sigmaCongr e (fun X => Iso.homCongr (Iso.refl P) (a X))

/-- The represented-family bijection is natural in the represented source. -/
def totalYonedaIso {n : ℕ} (e : (Fin n → C) ≃ (Fin n → C))
    (a : ∀ X, obj X ≅ obj (e X)) : totalYoneda (C := C) n ≅ totalYoneda n :=
  NatIso.ofComponents (fun P => (totalHomEquiv e a P.unop).toIso) (by
    intro P Q f
    apply ConcreteCategory.hom_ext
    rintro ⟨X, h⟩
    change (⟨e X, 𝟙 Q.unop ≫ (f.unop ≫ h) ≫ (a X).hom⟩ :
      Σ X : Fin n → C, Q.unop ⟶ obj X) =
      ⟨e X, f.unop ≫ (𝟙 P.unop ≫ h ≫ (a X).hom)⟩
    simp only [Category.id_comp, Category.assoc])

/-- Forward evaluation retains the reindexed family and composes the
original hom with the supplied tensor isomorphism. -/
theorem totalYonedaIso_hom_apply {n : ℕ} (e : (Fin n → C) ≃ (Fin n → C))
    (a : ∀ X, obj X ≅ obj (e X)) (P : C) (X : Fin n → C) (h : P ⟶ obj X) :
    (totalYonedaIso e a).hom.app (op P) ⟨X, h⟩ = ⟨e X, h ≫ (a X).hom⟩ := by
  change (⟨e X, 𝟙 P ≫ h ≫ (a X).hom⟩ : Σ X : Fin n → C, P ⟶ obj X) = _
  rw [Category.id_comp]

/-- Composition of the represented-family automorphisms uses the
actual consecutive tensor isomorphisms and consecutive family bijections. -/
theorem totalYonedaIso_trans {n : ℕ} (e f : (Fin n → C) ≃ (Fin n → C))
    (a : ∀ X, obj X ≅ obj (e X)) (b : ∀ X, obj X ≅ obj (f X)) :
    totalYonedaIso e a ≪≫ totalYonedaIso f b =
      totalYonedaIso (e.trans f) (fun X => a X ≪≫ b (e X)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext P
  apply ConcreteCategory.hom_ext
  rintro ⟨X, h⟩
  change (totalYonedaIso f b).hom.app (op P.unop)
      ((totalYonedaIso e a).hom.app (op P.unop) ⟨X, h⟩) =
      (totalYonedaIso (e.trans f) (fun X => a X ≪≫ b (e X))).hom.app
        (op P.unop) ⟨X, h⟩
  rw [totalYonedaIso_hom_apply, totalYonedaIso_hom_apply, totalYonedaIso_hom_apply]
  change (⟨f (e X), (h ≫ (a X).hom) ≫ (b (e X)).hom⟩ :
    Σ X : Fin n → C, P.unop ⟶ obj X) =
    ⟨f (e X), h ≫ ((a X).hom ≫ (b (e X)).hom)⟩
  rw [Category.assoc]

/-- The identity family bijection and identity tensor maps give the
identity automorphism of the represented-family functor. -/
theorem totalYonedaIso_refl (n : ℕ) :
    totalYonedaIso (Equiv.refl (Fin n → C)) (fun X => Iso.refl (obj X)) =
      Iso.refl (totalYoneda (C := C) n) := by
  apply Iso.ext
  apply NatTrans.ext
  funext P
  apply ConcreteCategory.hom_ext
  rintro ⟨X, h⟩
  change (⟨X, 𝟙 P.unop ≫ h ≫ 𝟙 (obj X)⟩ :
    Σ X : Fin n → C, P.unop ⟶ obj X) = ⟨X, h⟩
  simp only [Category.id_comp, Category.comp_id]

/-- Equal family bijections and equal actual tensor maps give the
same represented-family automorphism. -/
theorem totalYonedaIso_ext {n : ℕ} {e f : (Fin n → C) ≃ (Fin n → C)}
    (he : e = f) (a : ∀ X, obj X ≅ obj (e X)) (b : ∀ X, obj X ≅ obj (f X))
    (ha : ∀ X, HEq (a X).hom (b X).hom) : totalYonedaIso e a = totalYonedaIso f b := by
  cases he
  have hab : a = b := by
    funext X
    exact Iso.ext (eq_of_heq (ha X))
  cases hab
  rfl

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedYoneda

/- Source proof segment: FamilyReindex -/
section source_FamilyReindex
/-!
# Actual permutation reindexing of finite object families

The inverse permutation convention agrees with multiplication in
automorphism groups. These maps reindex actual families and actual
component morphisms before any tensor comparison is supplied.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor.TensorReindexing

variable {C : Type u}

/-- Reindex an actual ordered family by the inverse input permutation. -/
def familyEquiv {n : ℕ} (e : Equiv.Perm (Fin n)) :
    (Fin n → C) ≃ (Fin n → C) where
  toFun X i := X (e.symm i)
  invFun X i := X (e i)
  left_inv X := by funext i; simp only [Equiv.symm_apply_apply]
  right_inv X := by funext i; simp only [Equiv.apply_symm_apply]

/-- Family reindexing retains the actual inverse permutation at every slot. -/
@[simp] theorem familyEquiv_apply {n : ℕ} (e : Equiv.Perm (Fin n))
    (X : Fin n → C) (i : Fin n) : familyEquiv e X i = X (e.symm i) := rfl

/-- The identity permutation leaves every actual family unchanged. -/
theorem familyEquiv_one (n : ℕ) :
    familyEquiv (C := C) (1 : Equiv.Perm (Fin n)) = Equiv.refl _ := by
  ext X i
  rfl

/-- Multiplication of input permutations reindexes families in the automorphism convention. -/
theorem familyEquiv_mul {n : ℕ} (e f : Equiv.Perm (Fin n)) :
    familyEquiv (C := C) (e * f) = (familyEquiv f).trans (familyEquiv e) := by
  ext X i
  rfl

/-- The inverse input permutation induces the inverse family bijection. -/
theorem familyEquiv_inv {n : ℕ} (e : Equiv.Perm (Fin n)) :
    familyEquiv (C := C) e⁻¹ = (familyEquiv e).symm := by
  ext X i
  rfl

variable [Category.{v} C]

/-- Reindex actual object families and their component morphisms by the inverse permutation. -/
def pull (C : Type u) [Category.{v} C] (n : ℕ) (e : Equiv.Perm (Fin n)) :
    (Fin n → C) ⥤ (Fin n → C) := Pi.comap (fun _ : Fin n => C) e.symm

/-- The family underlying the reindexing functor is the actual family bijection. -/
@[simp] theorem pull_obj {n : ℕ} (e : Equiv.Perm (Fin n)) (X : Fin n → C) :
    (pull C n e).obj X = familyEquiv e X := rfl

/-- Identity permutation reindexing is the identity functor. -/
theorem pull_one (n : ℕ) : pull C n (1 : Equiv.Perm (Fin n)) = 𝟭 (Fin n → C) := rfl

/-- Consecutive actual permutation reindexings compose in the inverse convention. -/
theorem pull_mul {n : ℕ} (e f : Equiv.Perm (Fin n)) :
    pull C n (e * f) = pull C n f ⋙ pull C n e := rfl

/-- Reindexing by the inverse permutation followed by the permutation cancels on all maps. -/
theorem pull_inv_comp {n : ℕ} (e : Equiv.Perm (Fin n)) :
    pull C n e⁻¹ ⋙ pull C n e = 𝟭 (Fin n → C) := by
  rw [← pull_mul, mul_inv_cancel, pull_one]

end CategoryTheory.MonoidalCategory.OrderedTensor.TensorReindexing
end
end source_FamilyReindex

/- Source proof segment: ReindexingRecord -/
section source_ReindexingRecord
/-!
# Natural isomorphisms of finite tensor reindexing

A reindexing retains its actual input permutation and a full natural
isomorphism of tensor functors. The represented-family encoding also
retains the permutation, so it is faithful for every ambient category.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory Opposite

/-- A permutation of finite inputs together with its full natural tensor comparison. -/
structure TensorReindexing (C : Type u) [Category.{v} C] [MonoidalCategory C] (n : ℕ) where
  /-- The actual input permutation. -/
  perm : Equiv.Perm (Fin n)
  /-- The natural comparison with inverse permutation reindexing. -/
  comparison : functor C n ≅ TensorReindexing.pull C n perm ⋙ functor C n

namespace TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {n : ℕ}

/-- Reindexings are determined by their actual permutation and all component homs. -/
@[ext] theorem ext {r s : TensorReindexing C n} (he : r.perm = s.perm)
    (ha : ∀ X, HEq (r.comparison.hom.app X) (s.comparison.hom.app X)) : r = s := by
  cases r with
  | mk e a =>
      cases s with
      | mk f b =>
          cases he
          have hab : a = b := by
            apply Iso.ext
            apply NatTrans.ext
            funext X
            exact eq_of_heq (ha X)
          cases hab
          rfl

/-- The identity permutation has the original identity natural tensor comparison. -/
def one (C : Type u) [Category.{v} C] [MonoidalCategory C] (n : ℕ) :
    TensorReindexing C n where
  perm := 1
  comparison := Iso.refl (functor C n)

/-- Multiply reindexings in the actual automorphism convention. -/
def mul (r s : TensorReindexing C n) : TensorReindexing C n where
  perm := r.perm * s.perm
  comparison := s.comparison ≪≫ Functor.isoWhiskerLeft (pull C n s.perm) r.comparison

/-- Identity evaluation is the original identity map of the actual finite tensor. -/
theorem one_comparison_hom (X : Fin n → C) :
    (one C n).comparison.hom.app X = 𝟙 (obj X) := rfl

/-- Multiplication evaluates as the actual consecutive tensor comparisons. -/
theorem mul_comparison_hom (r s : TensorReindexing C n) (X : Fin n → C) :
    (mul r s).comparison.hom.app X =
      s.comparison.hom.app X ≫ r.comparison.hom.app (familyEquiv s.perm X) := rfl

/-- The actual inverse tensor comparison, constructed by reindexing the inverse natural iso. -/
def inverse (r : TensorReindexing C n) : TensorReindexing C n where
  perm := r.perm⁻¹
  comparison :=
    (Functor.isoWhiskerLeft (pull C n r.perm⁻¹) r.comparison ≪≫
      eqToIso (show pull C n r.perm⁻¹ ⋙ (pull C n r.perm ⋙ functor C n) =
          functor C n from by
        change (pull C n r.perm⁻¹ ⋙ pull C n r.perm) ⋙ functor C n = functor C n
        rw [pull_inv_comp]
        rfl)).symm

/-- The faithful encoding retains the input permutation and the complete represented action. -/
def encode (r : TensorReindexing C n) :
    Equiv.Perm (Fin n) × Aut (totalYoneda (C := C) n) :=
  ⟨r.perm, Aut.of (totalYonedaIso (familyEquiv r.perm) (fun X => r.comparison.app X))⟩

/-- Forward evaluation of the encoding keeps the actual inverse-reindexed family. -/
theorem encode_apply (r : TensorReindexing C n) (P : C) (X : Fin n → C)
    (h : P ⟶ obj X) :
    (encode r).2.asIso.hom.app (op P) ⟨X, h⟩ =
      ⟨familyEquiv r.perm X, h ≫ r.comparison.hom.app X⟩ :=
  totalYonedaIso_hom_apply _ _ _ _ _

/-- The represented action and the retained input permutation determine the natural comparison. -/
theorem encode_injective : Function.Injective (encode (C := C) (n := n)) := by
  intro r s h
  have he := congrArg _root_.Prod.fst h
  change r.perm = s.perm at he
  apply ext he
  intro X
  have hh := congrArg (fun p => p.2.asIso.hom.app (op (obj X)) ⟨X, 𝟙 (obj X)⟩) h
  rw [encode_apply, encode_apply] at hh
  exact (heq_of_eq (Category.id_comp (r.comparison.hom.app X))).symm.trans
    ((Sigma.mk.inj_iff.mp hh).2.trans
      (heq_of_eq (Category.id_comp (s.comparison.hom.app X))))

end TensorReindexing

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ReindexingRecord

/- Source proof segment: ActualTensorGenerators -/
section source_ActualTensorGenerators
/-!
# The actual adjacent generator records of heterogeneous tensors

Each generator retains its original finite transposition and the full
natural comparison built from the original binary braiding.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The actual finite input transposition with its full original tensor natural isomorphism. -/
def tensorGenerator {n : ℕ} (i : Fin n) : TensorReindexing C (n + 1) where
  perm := Equiv.swap i.castSucc i.succ
  comparison := adjacentInverseNatIso i

/-- The generator's permutation field is the original adjacent finite transposition. -/
@[simp] theorem tensorGenerator_perm {n : ℕ} (i : Fin n) :
    (tensorGenerator (C := C) i).perm = Equiv.swap i.castSucc i.succ := rfl

/-- The generator comparison has the original adjacent tensor map. -/
theorem tensorGenerator_hom_app {n : ℕ} (i : Fin n) (X : Fin (n + 1) → C) :
    HEq ((tensorGenerator (C := C) i).comparison.hom.app X) (adjacentIso X i).hom := by
  simp only [tensorGenerator, adjacentInverseNatIso]
  rfl

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ActualTensorGenerators

/- Source proof segment: PrefixPermutation -/
section source_PrefixPermutation
/-!
# Original permutation extension fixing the final tensor slot

The permutation extension is Mathlib's actual extension through
`Fin.castSuccEmb`. Its forward and inverse maps retain the original
initial coordinates and fix the original last coordinate.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace CategoryTheory.MonoidalCategory.OrderedTensor.TensorReindexing

/-- Extend the actual finite permutation through the original initial-slot embedding. -/
noncomputable def extendPerm (n : ℕ) : Equiv.Perm (Fin n) →* Equiv.Perm (Fin (n + 1)) :=
  Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb

/-- Every original initial slot is sent to the original permuted initial slot. -/
@[simp] theorem extendPerm_castSucc {n : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) :
    extendPerm n e i.castSucc = (e i).castSucc :=
  Equiv.Perm.viaEmbedding_apply _ _ _

/-- The added final slot is fixed by the actual extension. -/
@[simp] theorem extendPerm_last {n : ℕ} (e : Equiv.Perm (Fin n)) :
    extendPerm n e (Fin.last n) = Fin.last n := by
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨i, hi⟩
  exact Fin.castSucc_ne_last i hi

/-- The inverse extension retains every original inverse-permuted initial slot. -/
@[simp] theorem extendPerm_inv_castSucc {n : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) :
    (extendPerm n e).symm i.castSucc = (e.symm i).castSucc := by
  change (extendPerm n e)⁻¹ i.castSucc = (e⁻¹ i).castSucc
  rw [← map_inv]
  exact extendPerm_castSucc _ _

/-- The actual inverse extension fixes the original added final slot. -/
@[simp] theorem extendPerm_inv_last {n : ℕ} (e : Equiv.Perm (Fin n)) :
    (extendPerm n e).symm (Fin.last n) = Fin.last n := by
  change (extendPerm n e)⁻¹ (Fin.last n) = Fin.last n
  rw [← map_inv]
  exact extendPerm_last _

variable {C : Type u}

/-- Initial reindexed objects are exactly the original inverse-reindexed initial family. -/
theorem familyEquiv_extend_initial {n : ℕ} (e : Equiv.Perm (Fin n))
    (X : Fin (n + 1) → C) :
    Fin.init (n := n) (familyEquiv (extendPerm n e) X) =
      familyEquiv e (Fin.init (n := n) X) := by
  funext i
  change X ((extendPerm n e).symm i.castSucc) = X ((e.symm i).castSucc)
  rw [extendPerm_inv_castSucc]

/-- The actual reindexed final object is the original final object. -/
theorem familyEquiv_extend_last {n : ℕ} (e : Equiv.Perm (Fin n))
    (X : Fin (n + 1) → C) : familyEquiv (extendPerm n e) X (Fin.last n) = X (Fin.last n) := by
  change X ((extendPerm n e).symm (Fin.last n)) = X (Fin.last n)
  rw [extendPerm_inv_last]

end CategoryTheory.MonoidalCategory.OrderedTensor.TensorReindexing
end
end source_PrefixPermutation

/- Source proof segment: PrefixComparison -/
section source_PrefixComparison
/-!
# Natural tensor comparison after adjoining one fixed final slot

The comparison tensors the actual initial-family comparison with the
identity of the actual final object. The target is identified with the
original extended permutation functor on both objects and all maps.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor.TensorReindexing

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {n : ℕ}

/-- The actual tensor of the reindexed initial-family tensor and the unchanged final object. -/
def prefixTarget (C : Type u) [Category.{v} C] [MonoidalCategory C] (n : ℕ)
    (e : Equiv.Perm (Fin n)) : (Fin (n + 1) → C) ⥤ C :=
  (((Pi.comap (fun _ : Fin (n + 1) => C) Fin.castSucc) ⋙ pull C n e ⋙ functor C n).prod'
    (Pi.eval (fun _ : Fin (n + 1) => C) (Fin.last n))) ⋙ tensor C

/-- The original extended-permutation tensor has the actual initial/final tensor factors. -/
theorem prefixTarget_obj_eq (e : Equiv.Perm (Fin n)) (X : Fin (n + 1) → C) :
    obj (familyEquiv (extendPerm n e) X) =
      obj (familyEquiv e (Fin.init (n := n) X)) ⊗ X (Fin.last n) := by
  rw [obj_succ]
  change obj (Fin.init (n := n) (familyEquiv (extendPerm n e) X)) ⊗
    familyEquiv (extendPerm n e) X (Fin.last n) = _
  rw [familyEquiv_extend_initial, familyEquiv_extend_last]

/-- The whole target functor, including every component-map action, is the original extension. -/
theorem prefixTarget_eq_pull (e : Equiv.Perm (Fin n)) :
    prefixTarget C n e = pull C (n + 1) (extendPerm n e) ⋙ functor C (n + 1) := by
  apply Functor.hext (fun X => (prefixTarget_obj_eq e X).symm)
  intro X Y f
  change HEq
    (map (fun i : Fin n => f (e.symm i).castSucc) ⊗ₘ f (Fin.last n))
    (map (fun i : Fin n => f ((extendPerm n e).symm i.castSucc)) ⊗ₘ
      f ((extendPerm n e).symm (Fin.last n)))
  have hi : (fun i : Fin n => (extendPerm n e).symm i.castSucc) =
      (fun i : Fin n => (e.symm i).castSucc) := by
    funext i
    exact extendPerm_inv_castSucc e i
  have aux (g h : Fin n → Fin (n + 1)) (k l : Fin (n + 1)) (hg : g = h) (hk : k = l) :
      HEq (map (fun i => f (g i)) ⊗ₘ f k) (map (fun i => f (h i)) ⊗ₘ f l) := by
    cases hg
    cases hk
    rfl
  exact aux _ _ _ _ hi.symm (extendPerm_inv_last e).symm

/-- Tensor the original initial-family natural comparison with the unchanged last-slot identity. -/
def prefixComparisonAux (r : TensorReindexing C n) :
    functor C (n + 1) ≅ prefixTarget C n r.perm :=
  NatIso.ofComponents (fun X =>
    tensorIso (r.comparison.app (Fin.init (n := n) X)) (Iso.refl (X (Fin.last n)))) (by
    intro X Y f
    let f0 : Fin.init (n := n) X ⟶ Fin.init (n := n) Y := fun i => f i.castSucc
    change ((functor C n).map f0 ⊗ₘ f (Fin.last n)) ≫
        (r.comparison.hom.app (Fin.init (n := n) Y) ⊗ₘ 𝟙 (Y (Fin.last n))) =
      (r.comparison.hom.app (Fin.init (n := n) X) ⊗ₘ 𝟙 (X (Fin.last n))) ≫
        ((pull C n r.perm ⋙ functor C n).map f0 ⊗ₘ f (Fin.last n))
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    simp only [Category.comp_id, Category.id_comp]
    exact congrArg (· ⊗ₘ f (Fin.last n))
      (r.comparison.hom.naturality f0))

/-- The original extended-permutation natural tensor comparison with its actual index transport. -/
noncomputable def prefixComparison (r : TensorReindexing C n) :
    functor C (n + 1) ≅ pull C (n + 1) (extendPerm n r.perm) ⋙ functor C (n + 1) :=
  prefixComparisonAux r ≪≫ eqToIso (prefixTarget_eq_pull r.perm)

/-- Adjoin a fixed final input slot using the actual natural tensor comparison. -/
noncomputable def extend (r : TensorReindexing C n) : TensorReindexing C (n + 1) where
  perm := extendPerm n r.perm
  comparison := prefixComparison r

/-- Extension retains the original permutation extension field. -/
@[simp] theorem extend_perm (r : TensorReindexing C n) :
    (extend r).perm = extendPerm n r.perm := rfl

/-- Extension evaluation tensors the original comparison with the original final identity. -/
theorem extend_hom_app (r : TensorReindexing C n) (X : Fin (n + 1) → C) :
    (extend r).comparison.hom.app X =
      (r.comparison.hom.app (Fin.init (n := n) X) ⊗ₘ 𝟙 (X (Fin.last n))) ≫
        eqToHom (Functor.congr_obj (prefixTarget_eq_pull r.perm) X) := by
  simp only [extend, prefixComparison, Iso.trans_hom, eqToIso.hom,
    NatTrans.comp_app, eqToHom_app]
  rfl

end CategoryTheory.MonoidalCategory.OrderedTensor.TensorReindexing
end
end source_PrefixComparison

/- Source proof segment: OrderedBoundaryShapes -/
section source_OrderedBoundaryShapes
/-!
# Exact index shapes at the final tensor transpositions

The initial family and final two slots are read directly from the
actual finite permutation. These statements hold for every type of
input objects and do not assume a tensor structure.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

variable {A : Type u}

/-- The last finite transposition fixes the entire family before its last two inputs. -/
theorem prefix_swapLast {n : ℕ} (X : Fin (n + 2) → A) :
    (fun i : Fin n =>
      (X ∘ Equiv.swap (Fin.last n).castSucc (Fin.last n).succ) i.castSucc.castSucc) =
      (fun i : Fin n => X i.castSucc.castSucc) := by
  funext i
  change X (Equiv.swap (Fin.last n).castSucc (Fin.last n).succ i.castSucc.castSucc) = _
  rw [Equiv.swap_apply_of_ne_of_ne]
  · exact fun h => Fin.castSucc_ne_last i ((Fin.castSucc_injective (n + 1)) h)
  · exact Fin.castSucc_ne_last i.castSucc

/-- The penultimate input after the final transposition is the original last input. -/
theorem penultimate_swapLast {n : ℕ} (X : Fin (n + 2) → A) :
    (X ∘ Equiv.swap (Fin.last n).castSucc (Fin.last n).succ) (Fin.last n).castSucc =
      X (Fin.last (n + 1)) := by
  change X (Equiv.swap (Fin.last n).castSucc (Fin.last n).succ (Fin.last n).castSucc) = _
  rw [Equiv.swap_apply_left]
  rfl

/-- The last input after the final transposition is the original penultimate input. -/
theorem last_swapLast {n : ℕ} (X : Fin (n + 2) → A) :
    (X ∘ Equiv.swap (Fin.last n).castSucc (Fin.last n).succ) (Fin.last (n + 1)) =
      X (Fin.last n).castSucc := by
  change X (Equiv.swap (Fin.last n).castSucc (Fin.last n).succ (Fin.last n).succ) = _
  rw [Equiv.swap_apply_right]

/-- The original finite transposition is an involution on the whole input family. -/
theorem family_swap_twice {n : ℕ} (X : Fin n → A) (i j : Fin n) :
    (X ∘ Equiv.swap i j) ∘ Equiv.swap i j = X := by
  funext k
  exact congrArg X (Equiv.swap_apply_self i j k)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedBoundaryShapes

/- Source proof segment: OrderedBoundaryMaps -/
section source_OrderedBoundaryMaps
/-!
# Original maps at the adjacent tensor boundaries

These readbacks remove only the exact equality transports of the
original finite input reindexing. The original binary braidings and
the identities on all retained factors remain explicit.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The last adjacent map retains exactly its original binary prefix braiding. -/
theorem lastMap_heq {n : ℕ} (X : Fin (n + 2) → C) :
    HEq (adjacentIso X (Fin.last n)).hom
      (swapLastIso (obj (fun j : Fin n => X j.castSucc.castSucc))
        (X (Fin.last n).castSucc) (X (Fin.last (n + 1)))).hom := by
  rw [adjacentIso_last_hom]
  exact comp_eqToHom_heq _ _

/-- A lower adjacent map tensors the actual recursive transposition with the identity. -/
theorem lowerMap_heq {n : ℕ} (X : Fin (n + 2) → C) (j : Fin n) :
    HEq (adjacentIso X j.castSucc).hom
      ((adjacentIso (Fin.init X) j).hom ⊗ₘ 𝟙 (X (Fin.last (n + 1)))) := by
  rw [adjacentIso_castSucc_hom]
  exact comp_eqToHom_heq _ _

omit [BraidedCategory C] in
/-- Tensoring equal transported maps retains their full original tensor map. -/
theorem tensorMapBoundary_heq {A B D E A' B' D' E' : C}
    (hA : A = A') (hB : B = B') (hD : D = D') (hE : E = E')
    {f : A ⟶ B} {g : D ⟶ E} {f' : A' ⟶ B'} {g' : D' ⟶ E'}
    (hf : HEq f f') (hg : HEq g g') : HEq (f ⊗ₘ g) (f' ⊗ₘ g') := by
  cases hA
  cases hB
  cases hD
  cases hE
  cases hf
  cases hg
  rfl

/-- The penultimate adjacent map is the original interchange of the
third-last and second-last factors, with the final factor retained. -/
theorem penultimateMap_heq {n : ℕ} (X : Fin (n + 3) → C) :
    HEq (adjacentIso X (Fin.last n).castSucc).hom
      ((swapLastIso (obj (fun j : Fin n => X j.castSucc.castSucc.castSucc))
        (X (Fin.last n).castSucc.castSucc) (X (Fin.last (n + 1)).castSucc)).hom ⊗ₘ
        𝟙 (X (Fin.last (n + 2)))) := by
  have h₁ := lowerMap_heq X (Fin.last n)
  have h₂ := lastMap_heq (Fin.init X)
  have hs : obj (Fin.init X) =
      (obj (fun j : Fin n => X j.castSucc.castSucc.castSucc) ⊗
        X (Fin.last n).castSucc.castSucc) ⊗ X (Fin.last (n + 1)).castSucc := rfl
  have ht := obj_swapLast (Fin.init X)
  exact h₁.trans (tensorMapBoundary_heq hs ht rfl rfl h₂ HEq.rfl)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedBoundaryMaps

/- Source proof segment: ActualTensorGeneratorExtension -/
section source_ActualTensorGeneratorExtension
/-!
# Prefix extension of the original adjacent tensor generators

The smaller original adjacent permutation and tensor map extend to
the actual lower adjacent generator with the final object retained.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory
open TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The original lower adjacent generator is exactly the constructed fixed-last extension. -/
theorem tensorGenerator_castSucc {n : ℕ} (j : Fin n) :
    tensorGenerator (C := C) j.castSucc = TensorReindexing.extend (tensorGenerator j) := by
  apply TensorReindexing.ext
  · change Equiv.swap j.castSucc.castSucc j.castSucc.succ =
      extendPerm (n + 1) (Equiv.swap j.castSucc j.succ)
    apply Equiv.ext
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [extendPerm_last, Equiv.swap_apply_of_ne_of_ne]
      · exact (Fin.castSucc_ne_last j.castSucc).symm
      · simpa only [Fin.succ_castSucc] using (Fin.castSucc_ne_last j.succ).symm
    · rw [extendPerm_castSucc, Fin.succ_castSucc,
        (Fin.castSucc_injective (n + 1)).swap_apply]
  · intro X
    have h₁ := tensorGenerator_hom_app j.castSucc X
    have h₂ := lowerMap_heq X j
    have h₃ : HEq
        ((tensorGenerator (C := C) j).comparison.hom.app (Fin.init X) ⊗ₘ
          𝟙 (X (Fin.last (n + 1))))
        ((adjacentIso (Fin.init X) j).hom ⊗ₘ 𝟙 (X (Fin.last (n + 1)))) := by
      exact tensorMapBoundary_heq rfl rfl rfl rfl (tensorGenerator_hom_app j (Fin.init X)) HEq.rfl
    have h₄ := comp_eqToHom_heq
      ((tensorGenerator (C := C) j).comparison.hom.app (Fin.init X) ⊗ₘ
        𝟙 (X (Fin.last (n + 1))))
      (Functor.congr_obj (prefixTarget_eq_pull (tensorGenerator (C := C) j).perm) X)
    rw [extend_hom_app]
    exact h₁.trans (h₂.trans (h₃.symm.trans h₄.symm))

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ActualTensorGeneratorExtension

/- Source proof segment: OrderedBoundarySquare -/
section source_OrderedBoundarySquare
/-!
# The original last tensor transposition is an involution

The square relation is proved on the original heterogeneous tensor
isomorphisms, with the exact equality of the double-reindexed input
family retained in the result.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The actual last finite tensor transposition is an involution, including its transports. -/
theorem adjacentIso_last_square {n : ℕ} (X : Fin (n + 2) → C) :
    adjacentIso X (Fin.last n) ≪≫
        adjacentIso (X ∘ Equiv.swap (Fin.last n).castSucc (Fin.last n).succ) (Fin.last n) =
      eqToIso (congrArg obj
        (family_swap_twice X (Fin.last n).castSucc (Fin.last n).succ).symm) := by
  let P := obj (fun j : Fin n => X j.castSucc.castSucc)
  let A := X (Fin.last n).castSucc
  let B := X (Fin.last (n + 1))
  let Y := X ∘ Equiv.swap (Fin.last n).castSucc (Fin.last n).succ
  have h₁ : HEq (adjacentIso X (Fin.last n)).hom (swapLastIso P A B).hom :=
    lastMap_heq X
  have h₂ : HEq (adjacentIso Y (Fin.last n)).hom (swapLastIso P B A).hom := by
    have h := lastMap_heq Y
    dsimp only [Y] at h
    rw [prefix_swapLast, penultimate_swapLast, last_swapLast] at h
    exact h
  have hX : obj X = (P ⊗ A) ⊗ B := rfl
  have hY : obj Y = (P ⊗ B) ⊗ A := obj_swapLast X
  have hYY : obj (Y ∘ Equiv.swap (Fin.last n).castSucc (Fin.last n).succ) =
      (P ⊗ A) ⊗ B :=
    (congrArg obj (family_swap_twice X (Fin.last n).castSucc (Fin.last n).succ)).trans hX
  have hh := heq_comp hX hY hYY h₁ h₂
  have hs := congrArg Iso.hom (swapLastIso_involutive P A B)
  change (swapLastIso P A B).hom ≫ (swapLastIso P B A).hom = 𝟙 ((P ⊗ A) ⊗ B) at hs
  have hi : HEq ((adjacentIso X (Fin.last n)).hom ≫ (adjacentIso Y (Fin.last n)).hom)
      (𝟙 (obj X)) := hh.trans (heq_of_eq hs)
  apply Iso.ext
  change (adjacentIso X (Fin.last n)).hom ≫ (adjacentIso Y (Fin.last n)).hom = _
  have hc := eqToHom_heq_id_dom (obj X)
    (obj (Y ∘ Equiv.swap (Fin.last n).castSucc (Fin.last n).succ))
    (congrArg obj (family_swap_twice X (Fin.last n).castSucc (Fin.last n).succ).symm)
  exact eq_of_heq (hi.trans hc.symm)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedBoundarySquare

/- Source proof segment: YonedaInverse -/
section source_YonedaInverse
/-!
# Inverse represented tensor-family isomorphisms

The inverse retains the actual inverse family bijection and the actual
inverse tensor comparison, including the equality transport back to
the specified family.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory Opposite

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {n : ℕ}

/-- The actual inverse fiber comparison, with its original family equality transport. -/
def inverseFamilyComparison (e : (Fin n → C) ≃ (Fin n → C))
    (a : ∀ X, obj X ≅ obj (e X)) (X : Fin n → C) : obj X ≅ obj (e.symm X) :=
  (eqToIso (congrArg obj (e.apply_symm_apply X))).symm ≪≫ (a (e.symm X)).symm

/-- The actual inverse represented hom bijection is induced by the inverse fiber comparisons. -/
theorem totalHomEquiv_symm (e : (Fin n → C) ≃ (Fin n → C))
    (a : ∀ X, obj X ≅ obj (e X)) (P : C) :
    (totalHomEquiv e a P).symm =
      totalHomEquiv e.symm (inverseFamilyComparison e a) P := by
  apply Equiv.ext
  rintro ⟨X, h⟩
  change (⟨e.symm X, 𝟙 P ≫ ((e.right_inv' X).symm ▸ h) ≫ (a (e.symm X)).inv⟩ :
      Σ X : Fin n → C, P ⟶ obj X) =
    ⟨e.symm X, 𝟙 P ≫ h ≫ (inverseFamilyComparison e a X).hom⟩
  have hc : ((e.right_inv' X).symm ▸ h) =
      h ≫ eqToHom (congrArg obj (e.apply_symm_apply X)).symm := by
    have hf : HEq ((e.right_inv' X).symm ▸ h) h :=
      eqRec_heq (φ := fun Y : Fin n → C => P ⟶ obj Y) (e.right_inv' X).symm h
    have hg : HEq (h ≫ eqToHom (congrArg obj (e.apply_symm_apply X)).symm) h :=
      comp_eqToHom_heq h _
    exact eq_of_heq (hf.trans hg.symm)
  rw [hc]
  simp only [inverseFamilyComparison, Iso.trans_hom, Iso.symm_hom, eqToIso.inv,
    Category.id_comp, Category.assoc]

/-- Inverting the complete represented action uses the actual inverse family and tensor maps. -/
theorem totalYonedaIso_inverse (e : (Fin n → C) ≃ (Fin n → C))
    (a : ∀ X, obj X ≅ obj (e X)) :
    totalYonedaIso e.symm (inverseFamilyComparison e a) = (totalYonedaIso e a).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext P
  apply ConcreteCategory.hom_ext
  intro z
  change totalHomEquiv e.symm (inverseFamilyComparison e a) P.unop z =
    (totalHomEquiv e a P.unop).symm z
  rw [totalHomEquiv_symm]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_YonedaInverse

/- Source proof segment: ReindexingGroup -/
section source_ReindexingGroup
/-!
# The group of natural finite tensor reindexings

The complete represented-family encoding is faithful and retains the
input permutation. Its original group operations therefore prove the
group laws of the constructed natural tensor comparisons.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor.TensorReindexing

open CategoryTheory MonoidalCategory Opposite

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {n : ℕ}

instance : One (TensorReindexing C n) := ⟨one C n⟩
instance : Mul (TensorReindexing C n) := ⟨mul⟩
instance : Inv (TensorReindexing C n) := ⟨inverse⟩

/-- The actual inverse comparison retains its original inverse tensor map and family transport. -/
theorem inverse_hom_app (r : TensorReindexing C n) (X : Fin n → C) :
    (inverse r).comparison.hom.app X =
      (inverseFamilyComparison (familyEquiv r.perm) (fun X => r.comparison.app X) X).hom := by
  simp only [inverse, Iso.trans_symm, Iso.trans_hom, Iso.symm_hom, eqToIso.inv,
    Functor.isoWhiskerLeft_inv, NatTrans.comp_app, eqToHom_app,
    inverseFamilyComparison]
  rfl

/-- The faithful encoding preserves the original identity comparison. -/
theorem encode_one : encode (one C n) = 1 := by
  apply _root_.Prod.ext
  · rfl
  · apply Aut.ext
    change totalYonedaIso (Equiv.refl (Fin n → C)) (fun X => Iso.refl (obj X)) =
      Iso.refl (totalYoneda (C := C) n)
    exact totalYonedaIso_refl n

/-- The faithful encoding preserves the actual consecutive natural tensor comparisons. -/
theorem encode_mul (r s : TensorReindexing C n) : encode (mul r s) = encode r * encode s := by
  apply _root_.Prod.ext
  · rfl
  · apply Aut.ext
    change totalYonedaIso (familyEquiv (r.perm * s.perm))
        (fun X => (mul r s).comparison.app X) =
      totalYonedaIso (familyEquiv s.perm) (fun X => s.comparison.app X) ≪≫
        totalYonedaIso (familyEquiv r.perm) (fun X => r.comparison.app X)
    calc
      totalYonedaIso (familyEquiv (r.perm * s.perm))
          (fun X => (mul r s).comparison.app X) =
        totalYonedaIso ((familyEquiv s.perm).trans (familyEquiv r.perm))
          (fun X => s.comparison.app X ≪≫ r.comparison.app (familyEquiv s.perm X)) :=
        totalYonedaIso_ext (familyEquiv_mul _ _) _ _ (fun _ => HEq.rfl)
      _ = _ := (totalYonedaIso_trans _ _ _ _).symm

/-- The faithful encoding preserves the actual inverse natural tensor comparison. -/
theorem encode_inverse (r : TensorReindexing C n) : encode (inverse r) = (encode r)⁻¹ := by
  apply _root_.Prod.ext
  · rfl
  · apply Aut.ext
    change totalYonedaIso (familyEquiv r.perm⁻¹)
        (fun X => (inverse r).comparison.app X) =
      (totalYonedaIso (familyEquiv r.perm) (fun X => r.comparison.app X)).symm
    calc
      totalYonedaIso (familyEquiv r.perm⁻¹)
          (fun X => (inverse r).comparison.app X) =
        totalYonedaIso (familyEquiv r.perm).symm
          (inverseFamilyComparison (familyEquiv r.perm) (fun X => r.comparison.app X)) :=
        totalYonedaIso_ext (familyEquiv_inv _) _ _
          (fun X => heq_of_eq (inverse_hom_app r X))
      _ = _ := totalYonedaIso_inverse _ _

/-- Construct the whole group from the faithful actual represented-family encoding. -/
@[instance_reducible] def groupStructure :
    Group (TensorReindexing C n) where
  mul := mul
  one := one C n
  inv := inverse
  mul_assoc r s t := encode_injective
    (show encode (mul (mul r s) t) = encode (mul r (mul s t)) from by
      rw [encode_mul, encode_mul, encode_mul, encode_mul, mul_assoc])
  one_mul r := encode_injective (show encode (mul (one C n) r) = encode r from by
    rw [encode_mul, encode_one, one_mul])
  mul_one r := encode_injective (show encode (mul r (one C n)) = encode r from by
    rw [encode_mul, encode_one, mul_one])
  inv_mul_cancel r := encode_injective (show encode (mul (inverse r) r) = encode (one C n) from by
    rw [encode_mul, encode_inverse, inv_mul_cancel, encode_one])

instance : Group (TensorReindexing C n) := groupStructure

/-- Instance multiplication has the original consecutive component-hom formula. -/
theorem mul_hom_app (r s : TensorReindexing C n) (X : Fin n → C) :
    (r * s).comparison.hom.app X =
      s.comparison.hom.app X ≫ r.comparison.hom.app (familyEquiv s.perm X) :=
  mul_comparison_hom r s X

/-- The group identity has the original identity tensor map at every family. -/
theorem one_hom_app (X : Fin n → C) :
    (1 : TensorReindexing C n).comparison.hom.app X = 𝟙 (obj X) :=
  one_comparison_hom X

/-- The represented-family encoding is the actual injective group homomorphism. -/
def encodeHom : TensorReindexing C n →*
    (Equiv.Perm (Fin n) × Aut (totalYoneda (C := C) n)) where
  toFun := encode
  map_one' := by
    change encode (one C n) = 1
    exact encode_one
  map_mul' r s := by
    change encode (mul r s) = encode r * encode s
    exact encode_mul r s

/-- The group homomorphism retaining the actual input permutation. -/
def permutationHom : TensorReindexing C n →* Equiv.Perm (Fin n) :=
  (MonoidHom.fst _ _).comp encodeHom

/-- Permutation projection is the original permutation field. -/
@[simp] theorem permutationHom_apply (r : TensorReindexing C n) :
    permutationHom r = r.perm := rfl

end CategoryTheory.MonoidalCategory.OrderedTensor.TensorReindexing
end
end source_ReindexingGroup

/- Source proof segment: ActualTensorGeneratorSquare -/
section source_ActualTensorGeneratorSquare
/-!
# The original adjacent tensor generator square in the actual reindexing group

The group comparison maps are the original finite tensor maps. The
square relation follows from the proved binary symmetry and its
explicit double-reindexing transport.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory
open TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The actual final adjacent tensor generator is an involution in the constructed group. -/
theorem tensorGenerator_last_square (n : ℕ) :
    tensorGenerator (C := C) (Fin.last n) * tensorGenerator (Fin.last n) = 1 := by
  apply TensorReindexing.ext
  · change Equiv.swap (Fin.last n).castSucc (Fin.last n).succ *
        Equiv.swap (Fin.last n).castSucc (Fin.last n).succ = 1
    exact Equiv.swap_mul_self _ _
  · intro X
    rw [mul_hom_app]
    change HEq
      ((tensorGenerator (C := C) (Fin.last n)).comparison.hom.app X ≫
        (tensorGenerator (Fin.last n)).comparison.hom.app
          (familyEquiv (Equiv.swap (Fin.last n).castSucc (Fin.last n).succ) X))
      (𝟙 (obj X))
    let i := Fin.last n
    let s := Equiv.swap i.castSucc i.succ
    have hfamily : familyEquiv s X = X ∘ s := by
      simp only [familyEquiv]
      rfl
    have h₁ := tensorGenerator_hom_app i X
    have h₂ := tensorGenerator_hom_app i (familyEquiv s X)
    rw [hfamily] at h₂
    have hsrc : obj X = obj X := rfl
    have hmid : obj (familyEquiv s X) = obj (X ∘ s) := congrArg obj hfamily
    have htarget : obj (familyEquiv s (familyEquiv s X)) = obj ((X ∘ s) ∘ s) := by
      rw [hfamily]
      exact congrArg obj (by simpa only [familyEquiv, Equiv.symm_swap] using
        (show familyEquiv s (X ∘ s) = (X ∘ s) ∘ s from rfl))
    have hh := heq_comp hsrc hmid htarget h₁ h₂
    have hs := congrArg Iso.hom (adjacentIso_last_square X)
    change (adjacentIso X i).hom ≫ (adjacentIso (X ∘ s) i).hom =
      eqToHom (congrArg obj (family_swap_twice X i.castSucc i.succ).symm) at hs
    have hi := eqToHom_heq_id_dom (obj X) (obj ((X ∘ s) ∘ s))
      (congrArg obj (family_swap_twice X i.castSucc i.succ).symm)
    exact hh.trans ((heq_of_eq hs).trans hi)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ActualTensorGeneratorSquare

/- Source proof segment: OrderedTripleShapes -/
section source_OrderedTripleShapes
/-!
# Exact three-slot input shapes of adjacent transpositions

These identities retain the full finite input family and distinguish
the last three input slots. They supply the original labelled tensor
words for the heterogeneous braid relation.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

variable {A : Type u}

/-- The initial family after the penultimate transposition is its original lower transposition. -/
theorem init_swapLower {n : ℕ} (X : Fin (n + 2) → A) (j : Fin n) :
    Fin.init (X ∘ Equiv.swap j.castSucc.castSucc j.castSucc.succ) =
      Fin.init X ∘ Equiv.swap j.castSucc j.succ := by
  funext i
  change X (Equiv.swap j.castSucc.castSucc j.castSucc.succ i.castSucc) =
    X (Equiv.swap j.castSucc j.succ i).castSucc
  rw [Fin.succ_castSucc, (Fin.castSucc_injective (n + 1)).swap_apply]

/-- A lower transposition fixes the original final input. -/
theorem last_swapLower {n : ℕ} (X : Fin (n + 2) → A) (j : Fin n) :
    (X ∘ Equiv.swap j.castSucc.castSucc j.castSucc.succ) (Fin.last (n + 1)) =
      X (Fin.last (n + 1)) := by
  change X (Equiv.swap j.castSucc.castSucc j.castSucc.succ (Fin.last (n + 1))) = _
  rw [Equiv.swap_apply_of_ne_of_ne]
  · exact (Fin.castSucc_ne_last j.castSucc).symm
  · simpa only [Fin.succ_castSucc] using (Fin.castSucc_ne_last j.succ).symm

/-- The initial family before the final three slots is retained by their penultimate swap. -/
theorem triplePrefix_swapPenultimate {n : ℕ} (X : Fin (n + 3) → A) :
    (fun i : Fin n =>
      (X ∘ Equiv.swap (Fin.last n).castSucc.castSucc (Fin.last n).castSucc.succ)
        i.castSucc.castSucc.castSucc) =
      (fun i : Fin n => X i.castSucc.castSucc.castSucc) := by
  have h := prefix_swapLast (Fin.init X)
  have hi := init_swapLower X (Fin.last n)
  change (fun i : Fin n =>
    Fin.init (X ∘ Equiv.swap (Fin.last n).castSucc.castSucc (Fin.last n).castSucc.succ)
      i.castSucc.castSucc) = _
  rw [hi]
  exact h

/-- The initial family before the final three slots is retained by their last swap. -/
theorem triplePrefix_swapLast {n : ℕ} (X : Fin (n + 3) → A) :
    (fun i : Fin n =>
      (X ∘ Equiv.swap (Fin.last (n + 1)).castSucc (Fin.last (n + 1)).succ)
        i.castSucc.castSucc.castSucc) =
      (fun i : Fin n => X i.castSucc.castSucc.castSucc) := by
  have h := congrArg (fun f : Fin (n + 1) → A => fun i : Fin n => f i.castSucc)
    (prefix_swapLast X)
  exact h

/-- The first of the final three slots after the penultimate swap is the original middle slot. -/
theorem tripleFirst_swapPenultimate {n : ℕ} (X : Fin (n + 3) → A) :
    (X ∘ Equiv.swap (Fin.last n).castSucc.castSucc (Fin.last n).castSucc.succ)
      (Fin.last n).castSucc.castSucc = X (Fin.last (n + 1)).castSucc := by
  change X (Equiv.swap _ _ (Fin.last n).castSucc.castSucc) = _
  rw [Equiv.swap_apply_left]
  rfl

/-- The middle of the final three slots after the penultimate swap is the original first slot. -/
theorem tripleMiddle_swapPenultimate {n : ℕ} (X : Fin (n + 3) → A) :
    (X ∘ Equiv.swap (Fin.last n).castSucc.castSucc (Fin.last n).castSucc.succ)
      (Fin.last (n + 1)).castSucc = X (Fin.last n).castSucc.castSucc := by
  change X (Equiv.swap _ _ (Fin.last n).castSucc.succ) = _
  rw [Equiv.swap_apply_right]

/-- The last of the final three slots is retained by the penultimate swap. -/
theorem tripleLast_swapPenultimate {n : ℕ} (X : Fin (n + 3) → A) :
    (X ∘ Equiv.swap (Fin.last n).castSucc.castSucc (Fin.last n).castSucc.succ)
      (Fin.last (n + 2)) = X (Fin.last (n + 2)) :=
  last_swapLower X (Fin.last n)

/-- The first of the final three slots is retained by the last swap. -/
theorem tripleFirst_swapLast {n : ℕ} (X : Fin (n + 3) → A) :
    (X ∘ Equiv.swap (Fin.last (n + 1)).castSucc (Fin.last (n + 1)).succ)
      (Fin.last n).castSucc.castSucc = X (Fin.last n).castSucc.castSucc := by
  change X (Equiv.swap _ _ (Fin.last n).castSucc.castSucc) = _
  rw [Equiv.swap_apply_of_ne_of_ne]
  · exact fun h => Fin.castSucc_ne_last (Fin.last n) ((Fin.castSucc_injective (n + 2)) h)
  · exact Fin.castSucc_ne_last (Fin.last n).castSucc

/-- The middle of the final three slots after the last swap is the original final slot. -/
theorem tripleMiddle_swapLast {n : ℕ} (X : Fin (n + 3) → A) :
    (X ∘ Equiv.swap (Fin.last (n + 1)).castSucc (Fin.last (n + 1)).succ)
      (Fin.last (n + 1)).castSucc = X (Fin.last (n + 2)) :=
  penultimate_swapLast X

/-- The last of the final three slots after the last swap is the original middle slot. -/
theorem tripleLast_swapLast {n : ℕ} (X : Fin (n + 3) → A) :
    (X ∘ Equiv.swap (Fin.last (n + 1)).castSucc (Fin.last (n + 1)).succ)
      (Fin.last (n + 2)) = X (Fin.last (n + 1)).castSucc :=
  last_swapLast X

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedTripleShapes

/- Source proof segment: OrderedBoundaryBraid -/
section source_OrderedBoundaryBraid
/-!
# The original heterogeneous tensor braid boundary

The actual final two adjacent finite transpositions satisfy their
three-map braid relation. The labelled input families and all original
binary tensor maps are retained.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The last original adjacent map on a three-slot suffix has its binary prefix form. -/
theorem tripleLastMap_heq {n : ℕ} (X : Fin (n + 3) → C) :
    HEq (adjacentIso X (Fin.last (n + 1))).hom
      (swapLastIso
        (obj (fun j : Fin n => X j.castSucc.castSucc.castSucc) ⊗
          X (Fin.last n).castSucc.castSucc)
        (X (Fin.last (n + 1)).castSucc) (X (Fin.last (n + 2)))).hom := by
  exact lastMap_heq X

set_option backward.isDefEq.respectTransparency false in
/-- The actual last two adjacent tensor transpositions satisfy the full braid relation. -/
theorem adjacentIso_boundary_braid {n : ℕ} (X : Fin (n + 3) → C) :
    HEq
      ((adjacentIso X (Fin.last n).castSucc).hom ≫
        (adjacentIso
          (X ∘ Equiv.swap (Fin.last n).castSucc.castSucc (Fin.last n).castSucc.succ)
          (Fin.last (n + 1))).hom ≫
        (adjacentIso
          ((X ∘ Equiv.swap (Fin.last n).castSucc.castSucc (Fin.last n).castSucc.succ) ∘
            Equiv.swap (Fin.last (n + 1)).castSucc (Fin.last (n + 1)).succ)
          (Fin.last n).castSucc).hom)
      ((adjacentIso X (Fin.last (n + 1))).hom ≫
        (adjacentIso
          (X ∘ Equiv.swap (Fin.last (n + 1)).castSucc (Fin.last (n + 1)).succ)
          (Fin.last n).castSucc).hom ≫
        (adjacentIso
          ((X ∘ Equiv.swap (Fin.last (n + 1)).castSucc (Fin.last (n + 1)).succ) ∘
            Equiv.swap (Fin.last n).castSucc.castSucc (Fin.last n).castSucc.succ)
          (Fin.last (n + 1))).hom) := by
  let P := obj (fun j : Fin n => X j.castSucc.castSucc.castSucc)
  let A := X (Fin.last n).castSucc.castSucc
  let B := X (Fin.last (n + 1)).castSucc
  let D := X (Fin.last (n + 2))
  let s := Equiv.swap (Fin.last n).castSucc.castSucc (Fin.last n).castSucc.succ
  let t := Equiv.swap (Fin.last (n + 1)).castSucc (Fin.last (n + 1)).succ
  have hs₀ : HEq (adjacentIso X (Fin.last n).castSucc).hom
      ((swapLastIso P A B).hom ⊗ₘ 𝟙 D) := penultimateMap_heq X
  have ht₀ : HEq (adjacentIso X (Fin.last (n + 1))).hom
      (swapLastIso (P ⊗ A) B D).hom := tripleLastMap_heq X
  have ht₁ : HEq (adjacentIso (X ∘ s) (Fin.last (n + 1))).hom
      (swapLastIso (P ⊗ B) A D).hom := by
    have h := tripleLastMap_heq (X ∘ s)
    dsimp only [s] at h
    rw [triplePrefix_swapPenultimate, tripleFirst_swapPenultimate,
      tripleMiddle_swapPenultimate, tripleLast_swapPenultimate] at h
    exact h
  have hs₁ : HEq (adjacentIso (X ∘ t) (Fin.last n).castSucc).hom
      ((swapLastIso P A D).hom ⊗ₘ 𝟙 B) := by
    have h := penultimateMap_heq (X ∘ t)
    dsimp only [t] at h
    rw [triplePrefix_swapLast, tripleFirst_swapLast,
      tripleMiddle_swapLast, tripleLast_swapLast] at h
    exact h
  have hs₂ : HEq (adjacentIso ((X ∘ s) ∘ t) (Fin.last n).castSucc).hom
      ((swapLastIso P B D).hom ⊗ₘ 𝟙 A) := by
    have h := penultimateMap_heq ((X ∘ s) ∘ t)
    dsimp only [s, t] at h
    rw [triplePrefix_swapLast, triplePrefix_swapPenultimate,
      tripleFirst_swapLast, tripleFirst_swapPenultimate,
      tripleMiddle_swapLast, tripleLast_swapPenultimate,
      tripleLast_swapLast, tripleMiddle_swapPenultimate] at h
    exact h
  have ht₂ : HEq (adjacentIso ((X ∘ t) ∘ s) (Fin.last (n + 1))).hom
      (swapLastIso (P ⊗ D) A B).hom := by
    have h := tripleLastMap_heq ((X ∘ t) ∘ s)
    dsimp only [s, t] at h
    rw [triplePrefix_swapPenultimate, triplePrefix_swapLast,
      tripleFirst_swapPenultimate, tripleMiddle_swapLast,
      tripleMiddle_swapPenultimate, tripleFirst_swapLast,
      tripleLast_swapPenultimate, tripleLast_swapLast] at h
    exact h
  have hX : obj X = ((P ⊗ A) ⊗ B) ⊗ D := rfl
  have hXs : obj (X ∘ s) = ((P ⊗ B) ⊗ A) ⊗ D := by
    change ((obj (fun j : Fin n => (X ∘ s) j.castSucc.castSucc.castSucc) ⊗
      (X ∘ s) (Fin.last n).castSucc.castSucc) ⊗
      (X ∘ s) (Fin.last (n + 1)).castSucc) ⊗ (X ∘ s) (Fin.last (n + 2)) = _
    dsimp only [s]
    rw [triplePrefix_swapPenultimate, tripleFirst_swapPenultimate,
      tripleMiddle_swapPenultimate, tripleLast_swapPenultimate]
  have hXt : obj (X ∘ t) = ((P ⊗ A) ⊗ D) ⊗ B := by
    change ((obj (fun j : Fin n => (X ∘ t) j.castSucc.castSucc.castSucc) ⊗
      (X ∘ t) (Fin.last n).castSucc.castSucc) ⊗
      (X ∘ t) (Fin.last (n + 1)).castSucc) ⊗ (X ∘ t) (Fin.last (n + 2)) = _
    dsimp only [t]
    rw [triplePrefix_swapLast, tripleFirst_swapLast,
      tripleMiddle_swapLast, tripleLast_swapLast]
  have hXst : obj ((X ∘ s) ∘ t) = ((P ⊗ B) ⊗ D) ⊗ A := by
    change ((obj (fun j : Fin n => ((X ∘ s) ∘ t) j.castSucc.castSucc.castSucc) ⊗
      ((X ∘ s) ∘ t) (Fin.last n).castSucc.castSucc) ⊗
      ((X ∘ s) ∘ t) (Fin.last (n + 1)).castSucc) ⊗
      ((X ∘ s) ∘ t) (Fin.last (n + 2)) = _
    dsimp only [s, t]
    rw [triplePrefix_swapLast, triplePrefix_swapPenultimate,
      tripleFirst_swapLast, tripleFirst_swapPenultimate,
      tripleMiddle_swapLast, tripleLast_swapPenultimate,
      tripleLast_swapLast, tripleMiddle_swapPenultimate]
  have hXts : obj ((X ∘ t) ∘ s) = ((P ⊗ D) ⊗ A) ⊗ B := by
    change ((obj (fun j : Fin n => ((X ∘ t) ∘ s) j.castSucc.castSucc.castSucc) ⊗
      ((X ∘ t) ∘ s) (Fin.last n).castSucc.castSucc) ⊗
      ((X ∘ t) ∘ s) (Fin.last (n + 1)).castSucc) ⊗
      ((X ∘ t) ∘ s) (Fin.last (n + 2)) = _
    dsimp only [s, t]
    rw [triplePrefix_swapPenultimate, triplePrefix_swapLast,
      tripleFirst_swapPenultimate, tripleMiddle_swapLast,
      tripleMiddle_swapPenultimate, tripleFirst_swapLast,
      tripleLast_swapPenultimate, tripleLast_swapLast]
  have hXsts : obj (((X ∘ s) ∘ t) ∘ s) = ((P ⊗ D) ⊗ B) ⊗ A := by
    change ((obj (fun j : Fin n => (((X ∘ s) ∘ t) ∘ s) j.castSucc.castSucc.castSucc) ⊗
      (((X ∘ s) ∘ t) ∘ s) (Fin.last n).castSucc.castSucc) ⊗
      (((X ∘ s) ∘ t) ∘ s) (Fin.last (n + 1)).castSucc) ⊗
      (((X ∘ s) ∘ t) ∘ s) (Fin.last (n + 2)) = _
    dsimp only [s, t]
    simp only [triplePrefix_swapPenultimate, triplePrefix_swapLast,
      tripleFirst_swapPenultimate, tripleFirst_swapLast,
      tripleMiddle_swapPenultimate, tripleMiddle_swapLast,
      tripleLast_swapPenultimate, tripleLast_swapLast, P, A, B, D]
  have hXtst : obj (((X ∘ t) ∘ s) ∘ t) = ((P ⊗ D) ⊗ B) ⊗ A := by
    change ((obj (fun j : Fin n => (((X ∘ t) ∘ s) ∘ t) j.castSucc.castSucc.castSucc) ⊗
      (((X ∘ t) ∘ s) ∘ t) (Fin.last n).castSucc.castSucc) ⊗
      (((X ∘ t) ∘ s) ∘ t) (Fin.last (n + 1)).castSucc) ⊗
      (((X ∘ t) ∘ s) ∘ t) (Fin.last (n + 2)) = _
    dsimp only [s, t]
    simp only [triplePrefix_swapPenultimate, triplePrefix_swapLast,
      tripleFirst_swapPenultimate, tripleFirst_swapLast,
      tripleMiddle_swapPenultimate, tripleMiddle_swapLast,
      tripleLast_swapPenultimate, tripleLast_swapLast, P, A, B, D]
  have hL := heq_comp hX hXs hXsts hs₀ (heq_comp hXs hXst hXsts ht₁ hs₂)
  have hR := heq_comp hX hXt hXtst ht₀ (heq_comp hXt hXts hXtst hs₁ ht₂)
  have hb := congrArg Iso.hom (swapLastIso_braid P A B D)
  change ((swapLastIso P A B).hom ⊗ₘ 𝟙 D) ≫
      (swapLastIso (P ⊗ B) A D).hom ≫ ((swapLastIso P B D).hom ⊗ₘ 𝟙 A) =
    (swapLastIso (P ⊗ A) B D).hom ≫ ((swapLastIso P A D).hom ⊗ₘ 𝟙 B) ≫
      (swapLastIso (P ⊗ D) A B).hom at hb
  exact hL.trans ((heq_of_eq hb).trans hR.symm)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedBoundaryBraid

/- Source proof segment: Relations -/
section source_Relations
/-!
# Adjacent transposition relations and descending chains

The normal form uses descending chains of actual adjacent generators.
Only their involution, braid, and distant commutation relations are used.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Equiv.Perm.AdjacentPresentation

variable {G : Type u} [Group G]

/-- The standard relations of adjacent transpositions. -/
structure Relations {n : ℕ} (s : Fin n → G) : Prop where
  /-- Each adjacent generator is an involution. -/
  square : ∀ i, s i * s i = 1
  /-- Neighboring generators satisfy the length-three braid relation. -/
  braid : ∀ i j, i.val + 1 = j.val → s i * s j * s i = s j * s i * s j
  /-- Generators separated by at least one other generator commute. -/
  distant : ∀ i j, i.val + 1 < j.val → s i * s j = s j * s i

/-- Remove the last generator from an ordered finite generator family. -/
def initial {n : ℕ} (s : Fin (n + 1) → G) : Fin n → G := fun i => s i.castSucc

/-- Adjacent transposition relations restrict to the initial generator family. -/
theorem Relations.initial {n : ℕ} {s : Fin (n + 1) → G} (hs : Relations s) :
    Relations (initial s) where
  square i := hs.square i.castSucc
  braid i j h := hs.braid i.castSucc j.castSucc h
  distant i j h := hs.distant i.castSucc j.castSucc h

/-- The subgroup generated by the supplied generator family. -/
abbrev generated {n : ℕ} (s : Fin n → G) : Subgroup G :=
  Subgroup.closure (Set.range s)

/-- Removing the last generator reduces the generated subgroup. -/
theorem initial_generated_le {n : ℕ} (s : Fin (n + 1) → G) :
    generated (initial s) ≤ generated s :=
  Subgroup.closure_mono (by
    rintro _ ⟨i, rfl⟩
    exact ⟨i.castSucc, rfl⟩)

/-- The descending chain `s_(n-1) ... s_k`; the last position indexes the empty chain. -/
def chain : {n : ℕ} → (Fin n → G) → Fin (n + 1) → G
  | 0, _, _ => 1
  | n + 1, s, k => Fin.lastCases 1
      (fun j => s (Fin.last n) * chain (initial s) j) k

/-- The chain at the last position is empty. -/
@[simp] theorem chain_last {n : ℕ} (s : Fin n → G) :
    chain s (Fin.last n) = 1 := by
  cases n <;> simp [chain]

/-- A nonempty chain begins with the actual last generator. -/
@[simp] theorem chain_castSucc {n : ℕ} (s : Fin (n + 1) → G) (k : Fin (n + 1)) :
    chain s k.castSucc = s (Fin.last n) * chain (initial s) k := by
  simp [chain]

/-- Every descending chain belongs to the subgroup generated by its factors. -/
theorem chain_mem : ∀ {n : ℕ} (s : Fin n → G) (k : Fin (n + 1)),
    chain s k ∈ generated s
  | 0, s, k => by
      change (1 : G) ∈ generated s
      exact (generated s).one_mem
  | n + 1, s, k => by
      refine Fin.lastCases ?_ (fun j => ?_) k
      · rw [chain_last]
        exact (generated s).one_mem
      · rw [chain_castSucc]
        exact (generated s).mul_mem (Subgroup.subset_closure ⟨Fin.last n, rfl⟩)
          (initial_generated_le s (chain_mem (initial s) j))

/-- The last generator commutes with the subgroup generated by all except the last two. -/
theorem last_commutes_lower {n : ℕ} {s : Fin (n + 2) → G} (hs : Relations s)
    {h : G} (hh : h ∈ generated (initial (initial s))) :
    s (Fin.last (n + 1)) * h = h * s (Fin.last (n + 1)) := by
  have hle : generated (initial (initial s)) ≤
      Subgroup.centralizer ({s (Fin.last (n + 1))} : Set G) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    obtain rfl : x = s (Fin.last (n + 1)) := Set.mem_singleton_iff.mp hx
    exact (hs.distant i.castSucc.castSucc (Fin.last (n + 1)) (by
      change i.val + 1 < n + 1
      exact Nat.succ_lt_succ i.isLt)).symm
  exact Subgroup.mem_centralizer_iff.mp (hle hh) _ (Set.mem_singleton _)

end Equiv.Perm.AdjacentPresentation
end
end source_Relations

/- Source proof segment: TypeA -/
section source_TypeA
/-!
# Type A generators and their actual permutation map

The adjacent-generator relations produce the canonical map from the
presented type A group to actual finite permutations. The inverse is
proved in the normal form module, rather than supplied as a premise.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Equiv.Perm.AdjacentPresentation

variable {G : Type u} [Group G]

/-- Adjacent transposition relations imply the original type A Coxeter relations. -/
theorem Relations.toLiftable {n : ℕ} {s : Fin n → G} (hs : Relations s) :
    (CoxeterMatrix.A n).IsLiftable s := by
  have cube (a b : G) (ha : a * a = 1) (hb : b * b = 1)
      (hab : a * b * a = b * a * b) : (a * b) ^ 3 = 1 := by
    calc
      (a * b) ^ 3 = (a * b * a) * (b * a * b) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = (b * a * b) * (b * a * b) := congrArg (· * (b * a * b)) hab
      _ = b * a * (b * b) * a * b := by simp only [mul_assoc]
      _ = b * (a * a) * b := by rw [hb]; simp only [mul_one, mul_assoc]
      _ = 1 := by rw [ha, mul_one, hb]
  intro i j
  change (s i * s j) ^ (if i = j then 1 else
    if j.val + 1 = i.val ∨ i.val + 1 = j.val then 3 else 2) = 1
  split_ifs with hij hadj
  · subst j
    simpa only [pow_one] using hs.square i
  · rcases hadj with h | h
    · exact cube (s i) (s j) (hs.square i) (hs.square j) (hs.braid j i h).symm
    · exact cube (s i) (s j) (hs.square i) (hs.square j) (hs.braid i j h)
  · have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hc : s j * s i = s i * s j := by
      by_cases hlt : i.val < j.val
      · exact (hs.distant i j (by omega)).symm
      · exact hs.distant j i (by omega)
    calc
      (s i * s j) ^ 2 = s i * (s j * s i) * s j := by
        simp only [pow_two, mul_assoc]
      _ = s i * (s i * s j) * s j := congrArg (fun x => s i * x * s j) hc
      _ = (s i * s i) * (s j * s j) := by simp only [mul_assoc]
      _ = 1 := by rw [hs.square, hs.square, one_mul]

/-- The actual presented type A group on `n` adjacent generators. -/
abbrev TypeAGroup (n : ℕ) := (CoxeterMatrix.A n).Group

/-- The original simple generator in the presented type A group. -/
abbrev simple (n : ℕ) : Fin n → TypeAGroup n := (CoxeterMatrix.A n).simple

/-- The simple generators satisfy involution, braid, and distant commutation. -/
theorem typeARelations (n : ℕ) : Relations (simple n) where
  square i := (CoxeterMatrix.A n).toCoxeterSystem.simple_mul_simple_self i
  braid i j h := by
    have hij : i ≠ j := by intro he; have := congrArg Fin.val he; omega
    have hM : CoxeterMatrix.A n i j = 3 := by
      simp [CoxeterMatrix.A, hij, h]
    have hMj : CoxeterMatrix.A n j i = 3 := by
      rw [(CoxeterMatrix.A n).symmetric]
      exact hM
    have hw := (CoxeterMatrix.A n).toCoxeterSystem.wordProd_braidWord_eq i j
    simpa [CoxeterSystem.braidWord, hM, hMj, CoxeterSystem.alternatingWord,
      CoxeterSystem.wordProd, mul_assoc] using hw.symm
  distant i j h := by
    have hij : i ≠ j := by intro he; have := congrArg Fin.val he; omega
    have hM : CoxeterMatrix.A n i j = 2 := by
      simp [CoxeterMatrix.A, hij, show ¬ (j.val + 1 = i.val ∨ i.val + 1 = j.val) by omega]
    have hMj : CoxeterMatrix.A n j i = 2 := by
      rw [(CoxeterMatrix.A n).symmetric]
      exact hM
    have hw := (CoxeterMatrix.A n).toCoxeterSystem.wordProd_braidWord_eq i j
    simpa [CoxeterSystem.braidWord, hM, hMj, CoxeterSystem.alternatingWord,
      CoxeterSystem.wordProd, mul_assoc] using hw

/-- Embed the lower-rank generators into the initial generators of the next rank. -/
def embed (n : ℕ) : TypeAGroup n →* TypeAGroup (n + 1) :=
  (CoxeterMatrix.A n).toCoxeterSystem.lift
    ⟨initial (simple (n + 1)), (typeARelations (n + 1)).initial.toLiftable⟩

/-- The rank embedding retains each original simple generator. -/
@[simp] theorem embed_simple (n : ℕ) (i : Fin n) :
    embed n (simple n i) = simple (n + 1) i.castSucc := by
  exact (CoxeterMatrix.A n).toCoxeterSystem.lift_apply_simple
    (typeARelations (n + 1)).initial.toLiftable i

/-- The actual adjacent transposition on a finite ordered set. -/
def adjacent (n : ℕ) (i : Fin n) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap i.castSucc i.succ

/-- Actual adjacent transpositions satisfy the original defining relations. -/
theorem adjacentRelations (n : ℕ) : Relations (adjacent n) where
  square i := Equiv.swap_mul_self _ _
  braid i j h := by
    have hmid : i.succ = j.castSucc := Fin.ext h
    have hab : i.castSucc ≠ j.castSucc := by
      intro he
      have hv := congrArg Fin.val he
      change i.val = j.val at hv
      omega
    have hac : i.castSucc ≠ j.succ := by
      intro he
      have hv := congrArg Fin.val he
      change i.val = j.val + 1 at hv
      omega
    have hcb : j.succ ≠ j.castSucc := by
      intro he
      have hv := congrArg Fin.val he
      change j.val + 1 = j.val at hv
      omega
    dsimp only [adjacent]
    rw [hmid]
    have hl := Equiv.swap_mul_swap_mul_swap
      (x := j.succ) (y := j.castSucc) (z := i.castSucc) hcb hac.symm
    rw [Equiv.swap_comm j.castSucc i.castSucc, Equiv.swap_comm j.succ j.castSucc] at hl
    have hr := Equiv.swap_mul_swap_mul_swap
      (x := i.castSucc) (y := j.castSucc) (z := j.succ) hab hac
    exact hl.trans ((Equiv.swap_comm i.castSucc j.succ).trans hr.symm)
  distant i j h := by
    have hca : j.castSucc ≠ i.castSucc := by
      intro he
      have hv := congrArg Fin.val he
      change j.val = i.val at hv
      omega
    have hcb : j.castSucc ≠ i.succ := by
      intro he
      have hv := congrArg Fin.val he
      change j.val = i.val + 1 at hv
      omega
    have hda : j.succ ≠ i.castSucc := by
      intro he
      have hv := congrArg Fin.val he
      change j.val + 1 = i.val at hv
      omega
    have hdb : j.succ ≠ i.succ := by
      intro he
      have hv := congrArg Fin.val he
      change j.val + 1 = i.val + 1 at hv
      omega
    dsimp only [adjacent]
    rw [Equiv.mul_swap_eq_swap_mul,
      Equiv.swap_apply_of_ne_of_ne hca hcb, Equiv.swap_apply_of_ne_of_ne hda hdb]

/-- The canonical map from the presented type A group to actual permutations. -/
def toPerm (n : ℕ) : TypeAGroup n →* Equiv.Perm (Fin (n + 1)) :=
  (CoxeterMatrix.A n).toCoxeterSystem.lift
    ⟨adjacent n, (adjacentRelations n).toLiftable⟩

/-- The canonical permutation map sends each generator to its actual adjacent swap. -/
@[simp] theorem toPerm_simple (n : ℕ) (i : Fin n) :
    toPerm n (simple n i) = adjacent n i := by
  exact (CoxeterMatrix.A n).toCoxeterSystem.lift_apply_simple
    (adjacentRelations n).toLiftable i

end Equiv.Perm.AdjacentPresentation
end
end source_TypeA

/- Source proof segment: NormalForm -/
section source_NormalForm
/-!
# Adjacent-generator coset steps

Right multiplication of a descending chain by an adjacent generator
returns a lower-rank factor times another descending chain. The proof
is uniform in the ambient group and includes the empty chain.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Equiv.Perm.AdjacentPresentation

variable {G : Type u} [Group G]

/-- Right multiplication by a generator has the lower-rank coset normal form. -/
theorem normalStep : ∀ (n : ℕ) (s : Fin (n + 1) → G), Relations s →
    ∀ (k : Fin (n + 2)) (i : Fin (n + 1)),
      ∃ (a : G) (k' : Fin (n + 2)), a ∈ generated (initial s) ∧
        chain s k * s i = a * chain s k' := by
  intro n
  induction n with
  | zero =>
      intro s hs k i
      obtain rfl : i = (0 : Fin 1) := Fin.eq_zero i
      cases k using Fin.lastCases with
      | last =>
          refine ⟨1, (0 : Fin 1).castSucc, (generated (initial s)).one_mem, ?_⟩
          rw [chain_last, chain_castSucc]
          change 1 * s 0 = 1 * (s 0 * 1)
          simp only [one_mul, mul_one]
      | cast p =>
          obtain rfl : p = Fin.last 0 := Fin.eq_zero p
          refine ⟨1, Fin.last 1, (generated (initial s)).one_mem, ?_⟩
          rw [chain_castSucc, chain_last, chain_last, mul_one, mul_one]
          exact hs.square 0
  | succ n ih =>
      intro s hs k i
      cases k using Fin.lastCases with
      | last =>
          cases i using Fin.lastCases with
          | last =>
              refine ⟨1, (Fin.last (n + 1)).castSucc,
                (generated (initial s)).one_mem, ?_⟩
              rw [chain_last, chain_castSucc, chain_last]
              simp only [one_mul, mul_one]
          | cast j =>
              refine ⟨s j.castSucc, Fin.last (n + 2),
                Subgroup.subset_closure ⟨j, rfl⟩, ?_⟩
              rw [chain_last]
              simp only [one_mul, mul_one]
      | cast p =>
          cases i using Fin.lastCases with
          | last =>
              cases p using Fin.lastCases with
              | last =>
                  refine ⟨1, Fin.last (n + 2),
                    (generated (initial s)).one_mem, ?_⟩
                  rw [chain_castSucc, chain_last, chain_last, mul_one, mul_one]
                  exact hs.square (Fin.last (n + 1))
              | cast q =>
                  let a := s (Fin.last (n + 1))
                  let b := s (Fin.last n).castSucc
                  let t := chain (initial (initial s)) q
                  have ht : a * t = t * a :=
                    last_commutes_lower hs (chain_mem (initial (initial s)) q)
                  have hb : a * b * a = b * a * b :=
                    (hs.braid (Fin.last n).castSucc (Fin.last (n + 1)) rfl).symm
                  refine ⟨b, q.castSucc.castSucc,
                    Subgroup.subset_closure ⟨Fin.last n, rfl⟩, ?_⟩
                  rw [chain_castSucc, chain_castSucc]
                  change (a * (b * t)) * a = b * (a * (b * t))
                  calc
                    (a * (b * t)) * a = (a * b) * (t * a) := by
                      simp only [mul_assoc]
                    _ = (a * b) * (a * t) := by rw [← ht]
                    _ = (a * b * a) * t := by simp only [mul_assoc]
                    _ = (b * a * b) * t := congrArg (· * t) hb
                    _ = b * (a * (b * t)) := by simp only [mul_assoc]
          | cast j =>
              obtain ⟨a, q, ha, hstep⟩ := ih (initial s) hs.initial p j
              have hc := last_commutes_lower hs ha
              refine ⟨a, q.castSucc, initial_generated_le (initial s) ha, ?_⟩
              rw [chain_castSucc, chain_castSucc]
              change (s (Fin.last (n + 1)) * chain (initial s) p) *
                  (initial s) j = a * (s (Fin.last (n + 1)) * chain (initial s) q)
              rw [mul_assoc, hstep, ← mul_assoc, hc, mul_assoc]

end Equiv.Perm.AdjacentPresentation
end
end source_NormalForm

/- Source proof segment: RankFinite -/
section source_RankFinite
/-!
# The type A normal form and cardinal bound

Every element is a lower-rank factor followed by a descending chain.
This constructs finiteness and the factorial cardinal bound, and proves
that the canonical map to the actual permutation group is bijective.
-/

@[expose] public section

set_option autoImplicit false

namespace Equiv.Perm.AdjacentPresentation

open scoped Nat

/-- The range of the rank embedding is exactly the initial generated subgroup. -/
theorem embed_range (n : ℕ) :
    (embed n).range = generated (initial (simple (n + 1))) := by
  have hgen : generated (simple n) = ⊤ :=
    (CoxeterMatrix.A n).toCoxeterSystem.subgroupClosure_range_simple
  have hsimple : (embed n : TypeAGroup n → TypeAGroup (n + 1)) ∘ simple n =
      initial (simple (n + 1)) := by
    funext i
    exact embed_simple n i
  calc
    (embed n).range = (generated (simple n)).map (embed n) := by
      rw [hgen, Subgroup.map_top]
    _ = generated (initial (simple (n + 1))) := by
      rw [MonoidHom.map_closure, ← Set.range_comp, hsimple]

/-- The concrete lower-rank factor and descending-chain normal form map. -/
def normalMap (n : ℕ) (p : TypeAGroup n × Fin (n + 2)) : TypeAGroup (n + 1) :=
  embed n p.1 * chain (simple (n + 1)) p.2

/-- Every type A element has the constructed lower-rank normal form. -/
theorem normalMap_surjective (n : ℕ) : Function.Surjective (normalMap n) := by
  intro w
  refine (CoxeterMatrix.A (n + 1)).toCoxeterSystem.simple_induction_right
    (p := fun w => ∃ p, normalMap n p = w) w ?_ ?_
  · refine ⟨(1, Fin.last (n + 1)), ?_⟩
    simp only [normalMap, map_one, chain_last, one_mul]
  · intro w i hw
    obtain ⟨⟨a, k⟩, rfl⟩ := hw
    obtain ⟨b, k', hb, heq⟩ := normalStep n (simple (n + 1)) (typeARelations (n + 1)) k i
    have hb' : b ∈ (embed n).range := by rw [embed_range]; exact hb
    obtain ⟨b', hb'⟩ := MonoidHom.mem_range.mp hb'
    refine ⟨(a * b', k'), ?_⟩
    change embed n (a * b') * chain (simple (n + 1)) k' =
      (embed n a * chain (simple (n + 1)) k) * simple (n + 1) i
    rw [map_mul, hb', mul_assoc, ← heq, ← mul_assoc]

/-- Rank zero has no generators and every element is the identity. -/
theorem typeA_zero_eq_one (w : TypeAGroup 0) : w = 1 :=
  (CoxeterMatrix.A 0).toCoxeterSystem.simple_induction_right
    (p := fun w => w = 1) w rfl (fun _ i _ => Fin.elim0 i)

/-- Finiteness of the type A group follows from the actual normal form. -/
theorem finiteTypeA : ∀ n : ℕ, Finite (TypeAGroup n)
  | 0 => Finite.of_surjective (fun _ : Fin 1 => (1 : TypeAGroup 0))
      (fun w => ⟨0, (typeA_zero_eq_one w).symm⟩)
  | n + 1 => by
      have : Finite (TypeAGroup n) := finiteTypeA n
      exact Finite.of_surjective (normalMap n) (normalMap_surjective n)

/-- The normal form bounds rank `n` by the original factorial `(n+1)!`. -/
theorem card_bound (n : ℕ) : Nat.card (TypeAGroup n) ≤ (n + 1)! := by
  induction n with
  | zero =>
      have : Subsingleton (TypeAGroup 0) :=
        ⟨fun a b => (typeA_zero_eq_one a).trans (typeA_zero_eq_one b).symm⟩
      rw [Nat.card_of_subsingleton (1 : TypeAGroup 0)]
      simp only [Nat.reduceAdd, Nat.factorial_one, le_refl]
  | succ n ih =>
      have : Finite (TypeAGroup n) := finiteTypeA n
      have h := Nat.card_le_card_of_surjective (normalMap n) (normalMap_surjective n)
      rw [Nat.card_prod, Nat.card_fin] at h
      calc
        Nat.card (TypeAGroup (n + 1)) ≤ Nat.card (TypeAGroup n) * (n + 2) := h
        _ ≤ (n + 1)! * (n + 2) := Nat.mul_le_mul_right (n + 2) ih
        _ = (n + 1 + 1)! := by
          rw [Nat.factorial_succ (n + 1)]
          exact Nat.mul_comm _ _

/-- The original adjacent transpositions generate the actual finite permutation group. -/
theorem toPerm_surjective (n : ℕ) : Function.Surjective (toPerm n) := by
  have hgen : generated (adjacent n) = ⊤ :=
    Subgroup.closure_eq_top_of_mclosure_eq_top (by
      change Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) = ⊤
      exact Equiv.Perm.mclosure_swap_castSucc_succ n)
  have hle : generated (adjacent n) ≤ (toPerm n).range := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨simple n i, toPerm_simple n i⟩
  apply MonoidHom.range_eq_top.mp
  exact le_antisymm le_top (hgen ▸ hle)

/-- The actual type A permutation map is bijective by its normal form cardinal bound. -/
theorem toPerm_bijective (n : ℕ) : Function.Bijective (toPerm n) := by
  have : Finite (TypeAGroup n) := finiteTypeA n
  apply (toPerm_surjective n).bijective_of_nat_card_le
  simpa only [Nat.card_perm, Nat.card_fin] using card_bound n

/-- The constructed type A group equivalence with the actual finite permutation group. -/
noncomputable def typeAEquiv (n : ℕ) : TypeAGroup n ≃* Equiv.Perm (Fin (n + 1)) :=
  MulEquiv.ofBijective (toPerm n) (toPerm_bijective n)

/-- The constructed equivalence retains each actual adjacent transposition. -/
@[simp] theorem typeAEquiv_simple (n : ℕ) (i : Fin n) :
    typeAEquiv n (simple n i) = adjacent n i := toPerm_simple n i

/-- The proved inverse maps an actual adjacent transposition back to its original generator. -/
@[simp] theorem typeAEquiv_symm_adjacent (n : ℕ) (i : Fin n) :
    (typeAEquiv n).symm (adjacent n i) = simple n i := by
  apply (typeAEquiv n).injective
  rw [MulEquiv.apply_symm_apply, typeAEquiv_simple]

end Equiv.Perm.AdjacentPresentation
end
end source_RankFinite

/- Source proof segment: Lift -/
section source_Lift
/-!
# The universal adjacent-transposition presentation of finite permutations

Actual finite permutations act through any family of group elements
satisfying the original involution, braid, and distant commutation
relations. The type A permutation equivalence used by the construction
is proved from a normal form and factorial bound.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Equiv.Perm.AdjacentPresentation

variable {G : Type u} [Group G]

/-- Lift the adjacent-generator data to the actual finite permutation group. -/
noncomputable def lift {n : ℕ} (s : Fin n → G) (hs : Relations s) :
    Equiv.Perm (Fin (n + 1)) →* G :=
  ((CoxeterMatrix.A n).toCoxeterSystem.lift ⟨s, hs.toLiftable⟩).comp
    (typeAEquiv n).symm.toMonoidHom

/-- The constructed permutation lift agrees with every supplied adjacent generator. -/
@[simp] theorem lift_adjacent {n : ℕ} (s : Fin n → G) (hs : Relations s) (i : Fin n) :
    lift s hs (adjacent n i) = s i := by
  change (CoxeterMatrix.A n).toCoxeterSystem.lift ⟨s, hs.toLiftable⟩
    ((typeAEquiv n).symm (adjacent n i)) = s i
  rw [typeAEquiv_symm_adjacent]
  exact (CoxeterMatrix.A n).toCoxeterSystem.lift_apply_simple hs.toLiftable i

/-- A homomorphism from actual finite permutations is determined by the adjacent generators. -/
theorem lift_unique {n : ℕ} (s : Fin n → G) (hs : Relations s)
    (φ : Equiv.Perm (Fin (n + 1)) →* G) (hφ : ∀ i, φ (adjacent n i) = s i) :
    φ = lift s hs := by
  apply MonoidHom.eq_of_eqOn_denseM (show Submonoid.closure (Set.range (adjacent n)) = ⊤ from by
    change Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) = ⊤
    exact Equiv.Perm.mclosure_swap_castSucc_succ n)
  rintro _ ⟨i, rfl⟩
  exact (hφ i).trans (lift_adjacent s hs i).symm

/-- Adjacent-generator relations are retained by any homomorphism of ambient groups. -/
theorem Relations.map {H : Type v} [Group H] {n : ℕ} {s : Fin n → G}
    (hs : Relations s) (f : G →* H) : Relations (fun i => f (s i)) where
  square i := by
    rw [← map_mul, hs.square, map_one]
  braid i j h := by
    simpa only [map_mul] using congrArg f (hs.braid i j h)
  distant i j h := by
    simpa only [map_mul] using congrArg f (hs.distant i j h)

/-- The actual permutation lift is natural in the ambient group homomorphism. -/
theorem lift_map {H : Type v} [Group H] {n : ℕ} (s : Fin n → G) (hs : Relations s)
    (f : G →* H) : lift (fun i => f (s i)) (hs.map f) = f.comp (lift s hs) := by
  apply (lift_unique (fun i => f (s i)) (hs.map f) (f.comp (lift s hs)) ?_).symm
  intro i
  change f (lift s hs (adjacent n i)) = f (s i)
  rw [lift_adjacent]

/-- Full equivalence between adjacent-generator data and actual permutation homomorphisms. -/
noncomputable def liftEquiv (n : ℕ) :
    {s : Fin n → G // Relations s} ≃ (Equiv.Perm (Fin (n + 1)) →* G) where
  toFun s := lift s.val s.property
  invFun φ := ⟨fun i => φ (adjacent n i), (adjacentRelations n).map φ⟩
  left_inv s := by
    apply Subtype.ext
    funext i
    exact lift_adjacent s.val s.property i
  right_inv φ :=
    (lift_unique (fun i => φ (adjacent n i)) ((adjacentRelations n).map φ) φ
      (fun _ => rfl)).symm

end Equiv.Perm.AdjacentPresentation
end
end source_Lift

/- Source proof segment: ActualTensorGeneratorBraid -/
section source_ActualTensorGeneratorBraid
/-!
# The original tensor boundary braid in the actual reindexing group

The retained permutation and all original tensor comparison maps
give the full boundary braid relation of the actual generator group.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory
open TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The last two actual tensor generators satisfy the original three-map braid relation. -/
theorem tensorGenerator_boundary_braid (n : ℕ) :
    tensorGenerator (C := C) (Fin.last n).castSucc * tensorGenerator (Fin.last (n + 1)) *
        tensorGenerator (Fin.last n).castSucc =
      tensorGenerator (Fin.last (n + 1)) * tensorGenerator (Fin.last n).castSucc *
        tensorGenerator (Fin.last (n + 1)) := by
  let i := (Fin.last n).castSucc
  let j := Fin.last (n + 1)
  let s := Equiv.swap i.castSucc i.succ
  let t := Equiv.swap j.castSucc j.succ
  apply TensorReindexing.ext
  · change s * t * s = t * s * t
    exact (Equiv.Perm.AdjacentPresentation.adjacentRelations (n + 2)).braid i j rfl
  · intro X
    simp only [mul_hom_app]
    have heS (Y : Fin (n + 3) → C) : familyEquiv s Y = Y ∘ s := by
      simp only [familyEquiv]
      rfl
    have heT (Y : Fin (n + 3) → C) : familyEquiv t Y = Y ∘ t := by
      simp only [familyEquiv]
      rfl
    have hL₁ := tensorGenerator_hom_app i X
    have hL₂ := tensorGenerator_hom_app j (familyEquiv s X)
    have hL₃ := tensorGenerator_hom_app i (familyEquiv t (familyEquiv s X))
    have hR₁ := tensorGenerator_hom_app j X
    have hR₂ := tensorGenerator_hom_app i (familyEquiv t X)
    have hR₃ := tensorGenerator_hom_app j (familyEquiv s (familyEquiv t X))
    rw [heS] at hL₂ hL₃ hR₃
    rw [heT] at hL₃ hR₂ hR₃
    have htensorS (Y : Fin (n + 3) → C) :
        (pull C (n + 3) (tensorGenerator (C := C) i).perm).obj Y = Y ∘ s := by
      change familyEquiv s Y = Y ∘ s
      exact heS Y
    have htensorT (Y : Fin (n + 3) → C) :
        (pull C (n + 3) (tensorGenerator (C := C) j).perm).obj Y = Y ∘ t := by
      change familyEquiv t Y = Y ∘ t
      exact heT Y
    have hL := heq_comp rfl (congrArg obj (heS X))
      (congrArg obj (htensorS ((X ∘ s) ∘ t))) hL₁
      (heq_comp (congrArg obj (heS X)) (congrArg obj (htensorT (X ∘ s)))
        (congrArg obj (htensorS ((X ∘ s) ∘ t))) hL₂ hL₃)
    have hR := heq_comp rfl (congrArg obj (heT X))
      (congrArg obj (htensorT ((X ∘ t) ∘ s))) hR₁
      (heq_comp (congrArg obj (heT X)) (congrArg obj (htensorS (X ∘ t)))
        (congrArg obj (htensorT ((X ∘ t) ∘ s))) hR₂ hR₃)
    have hb := adjacentIso_boundary_braid X
    exact hL.trans (hb.trans hR.symm)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ActualTensorGeneratorBraid

/- Source proof segment: OrderedBoundaryFar -/
section source_OrderedBoundaryFar
/-!
# Distant original finite tensor transpositions

The final adjacent transposition commutes with every transposition
inside the preceding tensor prefix. This follows from naturality of
the original binary braiding in that arbitrary prefix map.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The original doubly lower transposition is the prefix transposition
tensored with the identities of both retained final factors. -/
theorem doubleLowerMap_heq {n : ℕ} (X : Fin (n + 3) → C) (j : Fin n) :
    HEq (adjacentIso X j.castSucc.castSucc).hom
      (((adjacentIso (Fin.init (Fin.init X)) j).hom ⊗ₘ
        𝟙 (X (Fin.last (n + 1)).castSucc)) ⊗ₘ 𝟙 (X (Fin.last (n + 2)))) := by
  have h₁ := lowerMap_heq X j.castSucc
  have h₂ := lowerMap_heq (Fin.init X) j
  have hs : obj (Fin.init X) =
      obj (Fin.init (Fin.init X)) ⊗ X (Fin.last (n + 1)).castSucc := rfl
  have ht := obj_swapLower (Fin.init X) j
  exact h₁.trans (tensorMapBoundary_heq hs ht rfl rfl h₂ HEq.rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The final adjacent tensor transposition commutes with every
original prefix transposition separated from it by another slot. -/
theorem adjacentIso_boundary_far {n : ℕ} (X : Fin (n + 3) → C) (j : Fin n) :
    HEq
      ((adjacentIso X j.castSucc.castSucc).hom ≫
        (adjacentIso
          (X ∘ Equiv.swap j.castSucc.castSucc.castSucc j.castSucc.castSucc.succ)
          (Fin.last (n + 1))).hom)
      ((adjacentIso X (Fin.last (n + 1))).hom ≫
        (adjacentIso
          (X ∘ Equiv.swap (Fin.last (n + 1)).castSucc (Fin.last (n + 1)).succ)
          j.castSucc.castSucc).hom) := by
  let U := Fin.init (Fin.init X)
  let P := obj U
  let Q := obj (U ∘ Equiv.swap j.castSucc j.succ)
  let A := X (Fin.last (n + 1)).castSucc
  let B := X (Fin.last (n + 2))
  let s := Equiv.swap j.castSucc.castSucc.castSucc j.castSucc.castSucc.succ
  let t := Equiv.swap (Fin.last (n + 1)).castSucc (Fin.last (n + 1)).succ
  let p := (adjacentIso U j).hom
  have hxs : Fin.init (Fin.init (X ∘ s)) = U ∘ Equiv.swap j.castSucc j.succ := by
    dsimp only [s, U]
    rw [init_swapLower, init_swapLower]
  have ha : (X ∘ s) (Fin.last (n + 1)).castSucc = A := by
    have h := last_swapLower (Fin.init X) j
    have hi := init_swapLower X j.castSucc
    change Fin.init (X ∘ s) (Fin.last (n + 1)) = _
    dsimp only [s]
    rw [hi]
    exact h
  have hb : (X ∘ s) (Fin.last (n + 2)) = B := by
    exact last_swapLower X j.castSucc
  have hxt : Fin.init (Fin.init (X ∘ t)) = U := by
    exact prefix_swapLast X
  have hat : (X ∘ t) (Fin.last (n + 1)).castSucc = B := penultimate_swapLast X
  have hbt : (X ∘ t) (Fin.last (n + 2)) = A := last_swapLast X
  have h₁ : HEq (adjacentIso X j.castSucc.castSucc).hom
      ((p ⊗ₘ 𝟙 A) ⊗ₘ 𝟙 B) := doubleLowerMap_heq X j
  have h₂ : HEq (adjacentIso (X ∘ s) (Fin.last (n + 1))).hom
      (swapLastIso Q A B).hom := by
    have h := lastMap_heq (X ∘ s)
    change HEq (adjacentIso (X ∘ s) (Fin.last (n + 1))).hom
      (swapLastIso (obj (Fin.init (Fin.init (X ∘ s))))
        ((X ∘ s) (Fin.last (n + 1)).castSucc) ((X ∘ s) (Fin.last (n + 2)))).hom at h
    rw [hxs, ha, hb] at h
    exact h
  have h₃ : HEq (adjacentIso X (Fin.last (n + 1))).hom
      (swapLastIso P A B).hom := lastMap_heq X
  have h₄ : HEq (adjacentIso (X ∘ t) j.castSucc.castSucc).hom
      ((p ⊗ₘ 𝟙 B) ⊗ₘ 𝟙 A) := by
    have h := doubleLowerMap_heq (X ∘ t) j
    rw [hxt, hat, hbt] at h
    exact h
  have hX : obj X = (P ⊗ A) ⊗ B := rfl
  have hXs : obj (X ∘ s) = (Q ⊗ A) ⊗ B := by
    change (obj (Fin.init (Fin.init (X ∘ s))) ⊗
      (X ∘ s) (Fin.last (n + 1)).castSucc) ⊗ (X ∘ s) (Fin.last (n + 2)) = _
    rw [hxs, ha, hb]
  have hXt : obj (X ∘ t) = (P ⊗ B) ⊗ A := obj_swapLast X
  have hXst : obj ((X ∘ s) ∘ t) = (Q ⊗ B) ⊗ A := by
    have h := obj_swapLast (X ∘ s)
    change obj ((X ∘ s) ∘ t) =
      (obj (Fin.init (Fin.init (X ∘ s))) ⊗ (X ∘ s) (Fin.last (n + 2))) ⊗
        (X ∘ s) (Fin.last (n + 1)).castSucc at h
    rw [hxs, hb, ha] at h
    exact h
  have hXts : obj ((X ∘ t) ∘ s) = (Q ⊗ B) ⊗ A := by
    have hi : Fin.init (Fin.init ((X ∘ t) ∘ s)) =
        U ∘ Equiv.swap j.castSucc j.succ := by
      dsimp only [s]
      rw [init_swapLower, init_swapLower, hxt]
    have hiA : ((X ∘ t) ∘ s) (Fin.last (n + 1)).castSucc = B := by
      change Fin.init ((X ∘ t) ∘ s) (Fin.last (n + 1)) = _
      dsimp only [s]
      rw [init_swapLower]
      exact (last_swapLower (Fin.init (X ∘ t)) j).trans hat
    have hiB : ((X ∘ t) ∘ s) (Fin.last (n + 2)) = A :=
      (last_swapLower (X ∘ t) j.castSucc).trans hbt
    change (obj (Fin.init (Fin.init ((X ∘ t) ∘ s))) ⊗
      ((X ∘ t) ∘ s) (Fin.last (n + 1)).castSucc) ⊗
      ((X ∘ t) ∘ s) (Fin.last (n + 2)) = _
    rw [hi, hiA, hiB]
  have hL := heq_comp hX hXs hXst h₁ h₂
  have hR := heq_comp hX hXt hXts h₃ h₄
  have hc : ((p ⊗ₘ 𝟙 A) ⊗ₘ 𝟙 B) ≫ (swapLastIso Q A B).hom =
      (swapLastIso P A B).hom ≫ ((p ⊗ₘ 𝟙 B) ⊗ₘ 𝟙 A) := by
    simpa only [Category.id_comp, Category.comp_id] using
      swapLastIso_naturality p (𝟙 A) (𝟙 B)
  exact hL.trans ((heq_of_eq hc).trans hR.symm)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedBoundaryFar

/- Source proof segment: ActualTensorGeneratorFar -/
section source_ActualTensorGeneratorFar
/-!
# The original tensor distant boundary in the actual reindexing group

The full tensor comparison maps and original finite transpositions
supply the distant commutation boundary of the generator group.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory
open TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The original doubly lower tensor generator commutes with the actual final generator. -/
theorem tensorGenerator_boundary_far {n : ℕ} (k : Fin n) :
    tensorGenerator (C := C) k.castSucc.castSucc * tensorGenerator (Fin.last (n + 1)) =
      tensorGenerator (Fin.last (n + 1)) * tensorGenerator k.castSucc.castSucc := by
  let i := k.castSucc.castSucc
  let j := Fin.last (n + 1)
  let s := Equiv.swap i.castSucc i.succ
  let t := Equiv.swap j.castSucc j.succ
  apply TensorReindexing.ext
  · change s * t = t * s
    exact (Equiv.Perm.AdjacentPresentation.adjacentRelations (n + 2)).distant i j
      (by simp only [i, j, Fin.val_castSucc, Fin.val_last]; omega)
  · intro X
    simp only [mul_hom_app]
    have heS (Y : Fin (n + 3) → C) : familyEquiv s Y = Y ∘ s := by
      simp only [familyEquiv]
      rfl
    have heT (Y : Fin (n + 3) → C) : familyEquiv t Y = Y ∘ t := by
      simp only [familyEquiv]
      rfl
    have hL₁ := tensorGenerator_hom_app j X
    have hL₂ := tensorGenerator_hom_app i (familyEquiv t X)
    have hR₁ := tensorGenerator_hom_app i X
    have hR₂ := tensorGenerator_hom_app j (familyEquiv s X)
    rw [heT] at hL₂
    rw [heS] at hR₂
    have htensorS (Y : Fin (n + 3) → C) :
        (pull C (n + 3) (tensorGenerator (C := C) i).perm).obj Y = Y ∘ s := by
      change familyEquiv s Y = Y ∘ s
      exact heS Y
    have htensorT (Y : Fin (n + 3) → C) :
        (pull C (n + 3) (tensorGenerator (C := C) j).perm).obj Y = Y ∘ t := by
      change familyEquiv t Y = Y ∘ t
      exact heT Y
    have hL := heq_comp rfl (congrArg obj (heT X))
      (congrArg obj (htensorS (X ∘ t))) hL₁ hL₂
    have hR := heq_comp rfl (congrArg obj (heS X))
      (congrArg obj (htensorT (X ∘ s))) hR₁ hR₂
    have hb := adjacentIso_boundary_far X k
    exact hL.trans (hb.symm.trans hR.symm)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ActualTensorGeneratorFar

/- Source proof segment: PrefixHom -/
section source_PrefixHom
/-!
# The actual fixed-final-slot tensor reindexing homomorphism

Extending a natural tensor comparison tensors its original component
maps with the identity of the retained final object. The actual index
transports are retained by `extend_hom_app`; they determine the group
homomorphism on every finite arity, including zero.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor.TensorReindexing

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {n : ℕ}

/-- Extension has the actual tensor comparison after the retained target equality transport. -/
theorem extend_hom_app_heq (r : TensorReindexing C n) (X : Fin (n + 1) → C) :
    HEq ((extend r).comparison.hom.app X)
      (r.comparison.hom.app (Fin.init (n := n) X) ⊗ₘ 𝟙 (X (Fin.last n))) :=
  (heq_of_eq (extend_hom_app r X)).trans (comp_eqToHom_heq _ _)

/-- Adjoining the fixed final tensor slot preserves the original identity comparison. -/
theorem extend_one : extend (1 : TensorReindexing C n) = 1 := by
  apply ext (show (extend (1 : TensorReindexing C n)).perm =
      (1 : TensorReindexing C (n + 1)).perm from by
    change extendPerm n (1 : Equiv.Perm (Fin n)) = 1
    exact map_one _)
  intro X
  have h := extend_hom_app_heq (1 : TensorReindexing C n) X
  rw [one_hom_app] at h
  have ht : (𝟙 (obj (Fin.init (n := n) X)) ⊗ₘ 𝟙 (X (Fin.last n))) = 𝟙 (obj X) :=
    id_tensorHom_id _ _
  exact h.trans ((heq_of_eq ht).trans (heq_of_eq (one_hom_app X)).symm)

/-- Adjoining the fixed final tensor slot preserves actual consecutive natural comparisons. -/
theorem extend_mul (r s : TensorReindexing C n) : extend (r * s) = extend r * extend s := by
  apply ext (show (extend (r * s)).perm = (extend r * extend s).perm from by
    change extendPerm n (r.perm * s.perm) = extendPerm n r.perm * extendPerm n s.perm
    exact map_mul _ _ _)
  intro X
  let X0 := Fin.init (n := n) X
  let V := X (Fin.last n)
  let Y := familyEquiv (extendPerm n s.perm) X
  let Y0 := familyEquiv s.perm X0
  let Z0 := familyEquiv r.perm Y0
  have hY0 : Fin.init (n := n) Y = Y0 := familyEquiv_extend_initial s.perm X
  have hYV : Y (Fin.last n) = V := familyEquiv_extend_last s.perm X
  have hB : obj Y = obj Y0 ⊗ V := prefixTarget_obj_eq s.perm X
  have hD : obj (familyEquiv (extendPerm n r.perm) Y) = obj Z0 ⊗ V := by
    rw [prefixTarget_obj_eq, hY0, hYV]
  have hs := extend_hom_app_heq s X
  have hr : HEq ((extend r).comparison.hom.app Y)
      (r.comparison.hom.app Y0 ⊗ₘ 𝟙 V) := by
    have aux (I J : Fin n → C) (A B : C) (hI : I = J) (hA : A = B) :
        HEq (r.comparison.hom.app I ⊗ₘ 𝟙 A) (r.comparison.hom.app J ⊗ₘ 𝟙 B) := by
      cases hI
      cases hA
      rfl
    exact (extend_hom_app_heq r Y).trans (aux _ _ _ _ hY0 hYV)
  have hcomp : HEq
      ((extend s).comparison.hom.app X ≫ (extend r).comparison.hom.app Y)
      ((s.comparison.hom.app X0 ⊗ₘ 𝟙 V) ≫ (r.comparison.hom.app Y0 ⊗ₘ 𝟙 V)) :=
    heq_comp (show obj X = obj X0 ⊗ V from rfl) hB hD hs hr
  have ht : (r * s).comparison.hom.app X0 ⊗ₘ 𝟙 V =
      (s.comparison.hom.app X0 ≫ r.comparison.hom.app Y0) ⊗ₘ 𝟙 V :=
    congrArg (· ⊗ₘ 𝟙 V) (mul_hom_app r s X0)
  have htensor : (s.comparison.hom.app X0 ≫ r.comparison.hom.app Y0) ⊗ₘ 𝟙 V =
      (s.comparison.hom.app X0 ⊗ₘ 𝟙 V) ≫ (r.comparison.hom.app Y0 ⊗ₘ 𝟙 V) := by
    simpa only [Category.id_comp] using
      (tensorHom_comp_tensorHom (s.comparison.hom.app X0) (𝟙 V)
        (r.comparison.hom.app Y0) (𝟙 V)).symm
  have hrhs : (extend r * extend s).comparison.hom.app X =
      (extend s).comparison.hom.app X ≫ (extend r).comparison.hom.app Y :=
    mul_hom_app (extend r) (extend s) X
  exact (extend_hom_app_heq (r * s) X).trans
    ((heq_of_eq ht).trans ((heq_of_eq htensor).trans (hcomp.symm.trans (heq_of_eq hrhs).symm)))

/-- The constructed fixed-final-slot extension is the original tensor
reindexing group homomorphism. -/
noncomputable def extendHom : TensorReindexing C n →* TensorReindexing C (n + 1) where
  toFun := extend
  map_one' := extend_one
  map_mul' := extend_mul

/-- The homomorphism retains the original extended input permutation. -/
@[simp] theorem extendHom_perm (r : TensorReindexing C n) :
    (extendHom r).perm = extendPerm n r.perm := rfl

/-- The homomorphism retains the original tensor identity on the final object. -/
theorem extendHom_hom_app (r : TensorReindexing C n) (X : Fin (n + 1) → C) :
    (extendHom r).comparison.hom.app X =
      (r.comparison.hom.app (Fin.init (n := n) X) ⊗ₘ 𝟙 (X (Fin.last n))) ≫
        eqToHom (Functor.congr_obj (prefixTarget_eq_pull r.perm) X) :=
  extend_hom_app r X

end CategoryTheory.MonoidalCategory.OrderedTensor.TensorReindexing
end
end source_PrefixHom

/- Source proof segment: ActualTensorRelations -/
section source_ActualTensorRelations
/-!
# The actual adjacent presentation of heterogeneous tensor permutations

All relations are proved for the original tensor generators. Initial
relations lift through the constructed fixed-last tensor homomorphism;
the original binary square, braid and distant boundary maps prove
every new top-rank relation.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory
open TensorReindexing
open Equiv.Perm.AdjacentPresentation

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- Every original adjacent finite tensor generator satisfies the full permutation presentation. -/
theorem tensorGenerator_relations : ∀ n : ℕ,
    Relations (fun i : Fin n => tensorGenerator (C := C) i)
  | 0 =>
      { square := fun i => i.elim0
        braid := fun i => i.elim0
        distant := fun i => i.elim0 }
  | n + 1 => by
      have ih := tensorGenerator_relations n
      have hi := ih.map (extendHom (C := C) (n := n + 1))
      refine ⟨?_, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · exact tensorGenerator_last_square n
        · rw [tensorGenerator_castSucc]
          exact hi.square j
      · intro i j
        refine Fin.lastCases ?_ (fun j' => ?_) j
        · intro hij
          cases n with
          | zero =>
              have hi0 : i = 0 := Fin.eq_zero i
              subst i
              simp only [Fin.val_zero] at hij
              omega
          | succ n =>
              have hieq : i = (Fin.last n).castSucc := by
                apply Fin.ext
                simp only [Fin.val_last, Fin.val_castSucc] at hij ⊢
                omega
              subst i
              exact tensorGenerator_boundary_braid n
        · intro hij
          have hi_ne : i ≠ Fin.last n := by
            intro hi
            subst i
            simp only [Fin.val_last] at hij
            have := j'.isLt
            omega
          obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hi_ne
          rw [tensorGenerator_castSucc, tensorGenerator_castSucc]
          exact hi.braid i' j' hij
      · intro i j
        refine Fin.lastCases ?_ (fun j' => ?_) j
        · intro hij
          cases n with
          | zero =>
              change i.val + 1 < 0 at hij
              omega
          | succ n =>
              have hin : i.val < n := by
                change i.val + 1 < n + 1 at hij
                omega
              let k : Fin n := ⟨i.val, hin⟩
              have hieq : i = k.castSucc.castSucc := Fin.ext rfl
              rw [hieq]
              exact tensorGenerator_boundary_far k
        · intro hij
          have hi_ne : i ≠ Fin.last n := by
            intro hi
            subst i
            simp only [Fin.val_last] at hij
            have := j'.isLt
            omega
          obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hi_ne
          rw [tensorGenerator_castSucc, tensorGenerator_castSucc]
          exact hi.distant i' j' hij

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ActualTensorRelations

/- Source proof segment: ActualTensorPermutations -/
section source_ActualTensorPermutations
/-!
# The actual permutation action on heterogeneous finite tensors

The permutation homomorphism is constructed from the original binary
adjacent tensor maps and their proved relations. No permutation action
or tensor coherence outcome is supplied as a premise.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory
open TensorReindexing
open Equiv.Perm.AdjacentPresentation

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- Construct the actual finite permutation action from the original binary tensor generators. -/
noncomputable def permutationHom (n : ℕ) :
    Equiv.Perm (Fin n) →* TensorReindexing C n :=
  match n with
  | 0 =>
      { toFun := fun _ => 1
        map_one' := rfl
        map_mul' := fun _ _ => (one_mul _).symm }
  | k + 1 => lift (fun i : Fin k => tensorGenerator (C := C) i)
      (tensorGenerator_relations k)

/-- The actual permutation homomorphism retains every original adjacent generator. -/
theorem permutationHom_adjacent {n : ℕ} (i : Fin n) :
    permutationHom (C := C) (n + 1) (Equiv.swap i.castSucc i.succ) = tensorGenerator i :=
  lift_adjacent (fun i : Fin n => tensorGenerator (C := C) i) (tensorGenerator_relations n) i

/-- The original finite input permutation is retained by the constructed tensor action. -/
theorem permutationHom_perm (n : ℕ) (p : Equiv.Perm (Fin n)) :
    (permutationHom (C := C) n p).perm = p := by
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ n =>
      have h : (TensorReindexing.permutationHom (C := C) (n := n + 1)).comp
          (permutationHom (C := C) (n + 1)) = MonoidHom.id _ := by
        apply MonoidHom.eq_of_eqOn_denseM
          (show Submonoid.closure (Set.range (adjacent n)) = ⊤ from
            Equiv.Perm.mclosure_swap_castSucc_succ n)
        rintro _ ⟨i, rfl⟩
        change (permutationHom (C := C) (n + 1) (Equiv.swap i.castSucc i.succ)).perm =
          Equiv.swap i.castSucc i.succ
        rw [permutationHom_adjacent, tensorGenerator_perm]
      exact congrArg (fun f => f p) h

/-- The actual permutation comparison as a natural isomorphism,
including the retained permutation-field equality transport. -/
noncomputable def permutationNatIso {n : ℕ} (p : Equiv.Perm (Fin n)) :
    functor C n ≅ pull C n p ⋙ functor C n :=
  (permutationHom (C := C) n p).comparison ≪≫
    eqToIso (congrArg (fun e : Equiv.Perm (Fin n) => pull C n e ⋙ functor C n)
      (permutationHom_perm n p))

/-- The actual inverse-reindexing tensor comparison of an arbitrary finite permutation. -/
noncomputable def permutationIso {n : ℕ} (p : Equiv.Perm (Fin n)) (X : Fin n → C) :
    obj X ≅ obj (X ∘ p.symm) :=
  (permutationNatIso p).app X

/-- Every tensor input map commutes with the actual arbitrary finite permutation. -/
theorem permutationIso_naturality {n : ℕ} (p : Equiv.Perm (Fin n))
    {X Y : Fin n → C} (f : ∀ i, X i ⟶ Y i) :
    map f ≫ (permutationIso p Y).hom =
      (permutationIso p X).hom ≫ map (fun i => f (p.symm i)) := by
  exact (permutationNatIso p).hom.naturality f

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ActualTensorPermutations

/- Source proof segment: FiniteTensorMap -/
section source_FiniteTensorMap
/-!
# Actual maps of the binary finite tensor carrier

Finite-family morphisms retain their original input bijection and
component morphisms. The tensor map is constructed from the actual
finite permutation comparison and componentwise tensor map.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

attribute [local instance] FintypeCat.fintype

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- Tensor an actual bijection of ordered finite inputs together with its original component
maps. -/
noncomputable def mapEquiv : {m n : ℕ} → {X : Fin m → C} → {Y : Fin n → C} →
    (e : Fin m ≃ Fin n) → (∀ i, X i ⟶ Y (e i)) → (obj X ⟶ obj Y) := by
  intro m n X Y e f
  have hmn : m = n := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst n
  exact (permutationIso e X).hom ≫
    map (fun j => f (e.symm j) ≫ eqToHom (congrArg Y (e.apply_symm_apply j)))

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The actual original finite-family morphism normalized by its two original enumerations. -/
noncomputable def enumeratedEquiv {X Y : FiniteFamily C} (f : X ⟶ Y) :
    Fin (arity X) ≃ Fin (arity Y) :=
  (enumeration X).trans (f.equiv.trans (enumeration Y).symm)

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The original component map of an enumerated finite-family morphism. -/
noncomputable def enumeratedMap {X Y : FiniteFamily C} (f : X ⟶ Y)
    (i : Fin (arity X)) :
    orderedFamily X i ⟶ orderedFamily Y (enumeratedEquiv f i) :=
  f.hom (enumeration X i) ≫
    eqToHom (congrArg Y.obj ((enumeration Y).apply_symm_apply (f.equiv (enumeration X i))).symm)

/-- The original finite tensor map on a finite-family morphism. -/
noncomputable def finiteMap {X Y : FiniteFamily C} (f : X ⟶ Y) :
    finiteObj X ⟶ finiteObj Y :=
  mapEquiv (enumeratedEquiv f) (enumeratedMap f)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FiniteTensorMap

/- Source proof segment: FiniteTensorEnumeration -/
section source_FiniteTensorEnumeration
/-!
# Exact original enumeration maps of finite tensor morphisms

The chosen original input enumerations normalize actual finite-family
bijections. Their identities and compositions retain every original
input index and every component map.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- Identity of original finite inputs normalizes to the identity finite equivalence. -/
theorem enumeratedEquiv_id (X : FiniteFamily C) :
    enumeratedEquiv (𝟙 X) = Equiv.refl (Fin (arity X)) := by
  apply Equiv.ext
  intro i
  exact (enumeration X).symm_apply_apply i

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- Composition of actual original finite input maps retains their consecutive normalized
bijections. -/
theorem enumeratedEquiv_comp {X Y Z : FiniteFamily C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    enumeratedEquiv (f ≫ g) = (enumeratedEquiv f).trans (enumeratedEquiv g) := by
  apply Equiv.ext
  intro i
  change (enumeration Z).symm (g.equiv (f.equiv (enumeration X i))) =
    (enumeration Z).symm
      (g.equiv (enumeration Y ((enumeration Y).symm (f.equiv (enumeration X i)))))
  rw [Equiv.apply_symm_apply]

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The original object underlying a normalized target position is retained. -/
theorem orderedFamily_enumeratedEquiv {X Y : FiniteFamily C} (f : X ⟶ Y)
    (i : Fin (arity X)) :
    orderedFamily Y (enumeratedEquiv f i) = Y.obj (f.equiv (enumeration X i)) := by
  change Y.obj (enumeration Y ((enumeration Y).symm (f.equiv (enumeration X i)))) = _
  rw [Equiv.apply_symm_apply]

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The original normalized component tensor map differs only by its exact object transport. -/
theorem enumeratedMap_heq {X Y : FiniteFamily C} (f : X ⟶ Y) (i : Fin (arity X)) :
    HEq (enumeratedMap f i) (f.hom (enumeration X i)) := by
  unfold enumeratedMap
  exact comp_eqToHom_heq _ _

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FiniteTensorEnumeration

/- Source proof segment: GenericRebase -/
section source_GenericRebase
/-!
# Transport of natural tensor comparisons along retained permutations

The record and its full natural comparison are transported along the
actual equality of input permutations. The generic laws are proved
before applying the factory to constructed permutation-action values.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor.TensorReindexing

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {n : ℕ}

/-- Retarget the actual natural comparison along its retained permutation equality. -/
def rebase (r : TensorReindexing C n) (p : Equiv.Perm (Fin n)) (h : r.perm = p) :
    functor C n ≅ pull C n p ⋙ functor C n :=
  r.comparison ≪≫ eqToIso (congrArg
    (fun e : Equiv.Perm (Fin n) => pull C n e ⋙ functor C n) h)

/-- Identity transport keeps the original natural comparison. -/
theorem rebase_refl (r : TensorReindexing C n) : rebase r r.perm rfl = r.comparison := by
  simp only [rebase, eqToIso_refl, Iso.trans_refl]

/-- The exact component map retains the original target equality transport. -/
theorem rebase_hom_app (r : TensorReindexing C n) (p : Equiv.Perm (Fin n))
    (h : r.perm = p) (X : Fin n → C) :
    (rebase r p h).hom.app X = r.comparison.hom.app X ≫
      eqToHom (Functor.congr_obj (congrArg
        (fun e : Equiv.Perm (Fin n) => pull C n e ⋙ functor C n) h) X) := by
  simp only [rebase, Iso.trans_hom, eqToIso.hom, NatTrans.comp_app, eqToHom_app]

/-- Changing a whole record by equality retains the same transported natural comparison. -/
theorem rebase_congr {r s : TensorReindexing C n} (hrs : r = s)
    (p : Equiv.Perm (Fin n)) (hr : r.perm = p) (hs : s.perm = p) :
    rebase r p hr = rebase s p hs := by
  cases hrs
  rfl

/-- The whole record factory with the specified actual retained permutation. -/
def rebaseRecord (r : TensorReindexing C n) (p : Equiv.Perm (Fin n)) (h : r.perm = p) :
    TensorReindexing C n where
  perm := p
  comparison := rebase r p h

/-- The whole transported record is the original record. -/
theorem rebaseRecord_eq (r : TensorReindexing C n) (p : Equiv.Perm (Fin n))
    (h : r.perm = p) : rebaseRecord r p h = r := by
  cases h
  simp only [rebaseRecord, rebase_refl]

/-- The record factory retains its specified original input permutation. -/
@[simp] theorem rebaseRecord_perm (r : TensorReindexing C n) (p : Equiv.Perm (Fin n))
    (h : r.perm = p) : (rebaseRecord r p h).perm = p := rfl

/-- Transport of the identity record is its original identity natural comparison. -/
theorem rebase_one : rebase (1 : TensorReindexing C n) (1 : Equiv.Perm (Fin n)) rfl =
    Iso.refl (functor C n) := rebase_refl (1 : TensorReindexing C n)

/-- The actual product record retains the product of the specified input permutations. -/
theorem product_perm_eq (r s : TensorReindexing C n) (p q : Equiv.Perm (Fin n))
    (hr : r.perm = p) (hs : s.perm = q) : (r * s).perm = p * q := by
  change r.perm * s.perm = p * q
  exact congrArg₂ (· * ·) hr hs

/-- Transport preserves the actual consecutive natural comparison multiplication. -/
theorem rebase_mul (r s : TensorReindexing C n) (p q : Equiv.Perm (Fin n))
    (hr : r.perm = p) (hs : s.perm = q) :
    rebase (r * s) (p * q) (product_perm_eq r s p q hr hs) =
      rebase s q hs ≪≫ Functor.isoWhiskerLeft (pull C n q) (rebase r p hr) := by
  cases hr
  cases hs
  rw [rebase_refl s, rebase_refl r]
  exact rebase_refl (r * s)

/-- The whole record factory preserves the actual multiplication of the original records. -/
theorem rebaseRecord_mul (r s : TensorReindexing C n) (p q : Equiv.Perm (Fin n))
    (hr : r.perm = p) (hs : s.perm = q) :
    rebaseRecord (r * s) (p * q) (product_perm_eq r s p q hr hs) =
      rebaseRecord r p hr * rebaseRecord s q hs := by
  rw [rebaseRecord_eq, rebaseRecord_eq, rebaseRecord_eq]

end CategoryTheory.MonoidalCategory.OrderedTensor.TensorReindexing
end
end source_GenericRebase

/- Source proof segment: ActualRebaseLaws -/
section source_ActualRebaseLaws
/-!
# Identity and multiplication of the constructed tensor permutation comparisons

The generic whole-record transport factory is applied to the actual
permutation homomorphism. Its group homomorphism laws produce the full
natural comparison laws with every original equality transport retained.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The actual tensor permutation natural comparison is identity at the identity permutation. -/
theorem permutationNatIso_one (n : ℕ) :
    permutationNatIso (C := C) (1 : Equiv.Perm (Fin n)) = Iso.refl (functor C n) := by
  change rebase (permutationHom (C := C) n 1) 1 (permutationHom_perm n 1) = _
  exact (rebase_congr (map_one (permutationHom (C := C) n)) 1 _ _).trans
    (rebase_one (C := C) (n := n))

/-- Every original tensor object has the original identity map at the identity permutation. -/
@[simp] theorem permutationIso_one {n : ℕ} (X : Fin n → C) :
    (permutationIso (C := C) (1 : Equiv.Perm (Fin n)) X).hom = 𝟙 (obj X) := by
  change (permutationNatIso (C := C) (1 : Equiv.Perm (Fin n))).hom.app X = _
  rw [permutationNatIso_one]
  rfl

/-- Actual consecutive permutation comparisons multiply as full natural isomorphisms. -/
theorem permutationNatIso_mul {n : ℕ} (p q : Equiv.Perm (Fin n)) :
    permutationNatIso (C := C) (p * q) =
      permutationNatIso q ≪≫ Functor.isoWhiskerLeft (pull C n q) (permutationNatIso p) := by
  let r := permutationHom (C := C) n p
  let s := permutationHom (C := C) n q
  have hr : r.perm = p := permutationHom_perm n p
  have hs : s.perm = q := permutationHom_perm n q
  have h0 : permutationNatIso (C := C) (p * q) =
      rebase (r * s) (p * q) (product_perm_eq r s p q hr hs) :=
    rebase_congr (map_mul (permutationHom (C := C) n) p q) (p * q)
      (permutationHom_perm n (p * q)) (product_perm_eq r s p q hr hs)
  exact h0.trans (rebase_mul r s p q hr hs)

/-- The actual finite tensor comparison maps keep the original group-product composition rule. -/
theorem permutationIso_mul_hom {n : ℕ} (p q : Equiv.Perm (Fin n)) (X : Fin n → C) :
    (permutationIso (C := C) (p * q) X).hom =
      (permutationIso q X).hom ≫ (permutationIso p (X ∘ q.symm)).hom := by
  change (permutationNatIso (C := C) (p * q)).hom.app X = _
  rw [permutationNatIso_mul]
  rfl

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ActualRebaseLaws

/- Source proof segment: FiniteTensorMapLaws -/
section source_FiniteTensorMapLaws
/-!
# Functoriality of original finite tensor bijection maps

The proofs use the actual constructed finite permutation comparisons
and all original component morphisms, retaining their target transports.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- At one fixed rank the actual bijection tensor map has its original permutation/map formula. -/
theorem mapEquiv_same {n : ℕ} {X Y : Fin n → C} (e : Equiv.Perm (Fin n))
    (f : ∀ i, X i ⟶ Y (e i)) :
    mapEquiv e f = (permutationIso e X).hom ≫
      map (fun j => f (e.symm j) ≫ eqToHom (congrArg Y (e.apply_symm_apply j))) := by
  unfold mapEquiv
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The identity finite input bijection gives the original componentwise tensor map. -/
theorem mapEquiv_refl {n : ℕ} {X Y : Fin n → C} (f : ∀ i, X i ⟶ Y i) :
    mapEquiv (Equiv.refl (Fin n)) f = map f := by
  rw [mapEquiv_same]
  change (permutationIso (C := C) (1 : Equiv.Perm (Fin n)) X).hom ≫
      map (fun i => f i ≫ 𝟙 (Y i)) = map f
  rw [permutationIso_one]
  simp only [Category.comp_id, Category.id_comp]

/-- Identity of all original finite inputs gives the actual original tensor identity. -/
theorem mapEquiv_id {n : ℕ} (X : Fin n → C) :
    mapEquiv (Equiv.refl (Fin n)) (fun i => 𝟙 (X i)) = 𝟙 (obj X) := by
  rw [mapEquiv_refl, map_id]

/-- Compose a componentwise tensor map with an actual finite input bijection map. -/
theorem map_mapEquiv {n : ℕ} {X Y Z : Fin n → C}
    (f : ∀ i, X i ⟶ Y i) (e : Equiv.Perm (Fin n)) (g : ∀ i, Y i ⟶ Z (e i)) :
    map f ≫ mapEquiv e g = mapEquiv e (fun i => f i ≫ g i) := by
  rw [mapEquiv_same, mapEquiv_same]
  rw [← Category.assoc, permutationIso_naturality, Category.assoc, ← map_comp]
  congr 1
  have hc : (fun i : Fin n => f (e.symm i) ≫ g (e.symm i) ≫
      eqToHom (congrArg Z (e.apply_symm_apply i))) =
      (fun i : Fin n => (f (e.symm i) ≫ g (e.symm i)) ≫
        eqToHom (congrArg Z (e.apply_symm_apply i))) := by
    funext i
    exact (Category.assoc (f (e.symm i)) (g (e.symm i))
      (eqToHom (congrArg Z (e.apply_symm_apply i)))).symm
  exact congrArg (fun h : ∀ i : Fin n, X (e.symm i) ⟶ Z i => map h) hc

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FiniteTensorMapLaws

/- Source proof segment: FiniteTensorMapComposition -/
section source_FiniteTensorMapComposition
/-!
# Composition of original finite tensor bijection maps

The original finite input bijections and all component maps are
composed using the proved actual tensor permutation multiplication
and naturality laws.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- Consecutive original finite input bijections tensor to their composite original map. -/
theorem mapEquiv_comp_same {n : ℕ} {X Y Z : Fin n → C}
    (e d : Equiv.Perm (Fin n)) (f : ∀ i, X i ⟶ Y (e i))
    (g : ∀ i, Y i ⟶ Z (d i)) :
    mapEquiv e f ≫ mapEquiv d g = mapEquiv (e.trans d) (fun i => f i ≫ g (e i)) := by
  rw [mapEquiv_same, mapEquiv_same, mapEquiv_same]
  let f' := fun j => f (e.symm j) ≫ eqToHom (congrArg Y (e.apply_symm_apply j))
  let g' := fun j => g (d.symm j) ≫ eqToHom (congrArg Z (d.apply_symm_apply j))
  have hn := permutationIso_naturality d f'
  change ((permutationIso e X).hom ≫ map f') ≫
      ((permutationIso d Y).hom ≫ map g') = _
  simp only [Category.assoc]
  rw [← Category.assoc (map f') (permutationIso d Y).hom, hn]
  have he : (permutationIso (e.trans d) X).hom =
      (permutationIso e X).hom ≫ (permutationIso d (X ∘ e.symm)).hom :=
    permutationIso_mul_hom d e X
  rw [he]
  simp only [Category.assoc]
  rw [← map_comp]
  congr 1
  congr 1
  apply congrArg (fun h => map h)
  funext j
  dsimp only [f', g']
  have transport_naturality {a b : Fin n} (h : a = b) :
      eqToHom (congrArg Y h) ≫ g b = g a ≫ eqToHom (congrArg (fun i => Z (d i)) h) := by
    cases h
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [Category.assoc, ← Category.assoc
    (eqToHom (congrArg Y (e.apply_symm_apply (d.symm j)))) (g (d.symm j)),
    transport_naturality]
  · simp only [Category.assoc, eqToHom_trans]
    rfl
  · exact e.apply_symm_apply _

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FiniteTensorMapComposition

/- Source proof segment: FiniteTensorMapTransport -/
section source_FiniteTensorMapTransport
/-!
# Transport of actual finite tensor maps across input bijections

Arbitrary finite input counts are retained until their actual bijection
identifies them. The fixed-rank tensor map laws then apply to the
original component maps.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- An actual bijection identifies the original finite input counts. -/
theorem equiv_arity_eq {m n : ℕ} (e : Fin m ≃ Fin n) : m = n :=
  by simpa only [Fintype.card_fin] using Fintype.card_congr e

/-- Whole input bijections and their original component maps determine the same tensor map. -/
theorem mapEquiv_congr {m n : ℕ} {X : Fin m → C} {Y : Fin n → C}
    {e d : Fin m ≃ Fin n} (he : e = d)
    (f : ∀ i, X i ⟶ Y (e i)) (g : ∀ i, X i ⟶ Y (d i))
    (hfg : ∀ i, HEq (f i) (g i)) : mapEquiv e f = mapEquiv d g := by
  cases he
  have h : f = g := by
    funext i
    exact eq_of_heq (hfg i)
  cases h
  rfl

/-- The original finite tensor map preserves arbitrary consecutive finite input bijections. -/
theorem mapEquiv_comp {l m n : ℕ} {X : Fin l → C} {Y : Fin m → C} {Z : Fin n → C}
    (e : Fin l ≃ Fin m) (d : Fin m ≃ Fin n)
    (f : ∀ i, X i ⟶ Y (e i)) (g : ∀ i, Y i ⟶ Z (d i)) :
    mapEquiv e f ≫ mapEquiv d g = mapEquiv (e.trans d) (fun i => f i ≫ g (e i)) := by
  have hlm := equiv_arity_eq e
  have hmn := equiv_arity_eq d
  subst m
  subst n
  exact mapEquiv_comp_same e d f g

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FiniteTensorMapTransport

/- Source proof segment: FiniteTensorMapIso -/
section source_FiniteTensorMapIso
/-!
# Actual finite tensor maps induced by input and component isomorphisms

The isomorphism is built from the proved actual finite permutation
comparison and the original component isomorphisms. Its forward map
is the original `mapEquiv` construction.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The actual tensor isomorphism of a finite input bijection and original component
isomorphisms. -/
noncomputable def isoEquiv : {m n : ℕ} → {X : Fin m → C} → {Y : Fin n → C} →
    (e : Fin m ≃ Fin n) → (∀ i, X i ≅ Y (e i)) → (obj X ≅ obj Y) := by
  intro m n X Y e f
  have hmn : m = n := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst n
  exact permutationIso e X ≪≫
    iso (fun j => f (e.symm j) ≪≫ eqToIso (congrArg Y (e.apply_symm_apply j)))

/-- Forward isomorphism evaluation is the original finite-bijection tensor map. -/
theorem isoEquiv_hom {m n : ℕ} {X : Fin m → C} {Y : Fin n → C}
    (e : Fin m ≃ Fin n) (f : ∀ i, X i ≅ Y (e i)) :
    (isoEquiv e f).hom = mapEquiv e (fun i => (f i).hom) := by
  unfold isoEquiv mapEquiv
  have hmn : m = n := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst n
  rfl

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FiniteTensorMapIso

/- Source proof segment: IsoEquivLaws -/
section source_IsoEquivLaws
/-!
# Laws of the original finite input isomorphism maps

The original finite bijection and every component isomorphism are
retained. All arity and object equality transports are derived from
the actual map construction before selecting a block permutation.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- Whole finite input and component isomorphisms determine the original tensor isomorphism. -/
theorem isoEquiv_congr {m n : ℕ} {X : Fin m → C} {Y : Fin n → C}
    {e d : Fin m ≃ Fin n} (he : e = d)
    (f : ∀ i, X i ≅ Y (e i)) (g : ∀ i, X i ≅ Y (d i))
    (hfg : ∀ i, HEq (f i) (g i)) : isoEquiv e f = isoEquiv d g := by
  cases he
  have h : f = g := funext (fun i => eq_of_heq (hfg i))
  cases h
  rfl

/-- Original consecutive finite input isomorphisms give their original composite. -/
theorem isoEquiv_trans {l m n : ℕ} {X : Fin l → C} {Y : Fin m → C} {Z : Fin n → C}
    (e : Fin l ≃ Fin m) (d : Fin m ≃ Fin n)
    (f : ∀ i, X i ≅ Y (e i)) (g : ∀ i, Y i ≅ Z (d i)) :
    isoEquiv e f ≪≫ isoEquiv d g = isoEquiv (e.trans d) (fun i => f i ≪≫ g (e i)) := by
  apply Iso.ext
  simp only [Iso.trans_hom, isoEquiv_hom]
  exact mapEquiv_comp e d (fun i => (f i).hom) (fun i => (g i).hom)

set_option backward.isDefEq.respectTransparency false in
/-- The original identity input bijection retains the original component tensor isomorphism. -/
theorem isoEquiv_refl {n : ℕ} {X Y : Fin n → C} (f : ∀ i, X i ≅ Y i) :
    isoEquiv (Equiv.refl (Fin n)) f = iso f := by
  apply Iso.ext
  rw [isoEquiv_hom, mapEquiv_refl]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Identity of every original finite input gives the tensor identity isomorphism. -/
theorem isoEquiv_refl_id {n : ℕ} (X : Fin n → C) :
    isoEquiv (Equiv.refl (Fin n)) (fun i => Iso.refl (X i)) = Iso.refl (obj X) := by
  apply Iso.ext
  rw [isoEquiv_hom]
  exact mapEquiv_id X

omit [SymmetricCategory C] in
/-- The original tensor map of a whole family equality is its actual object transport. -/
theorem map_family_eqToHom {n : ℕ} {X Y : Fin n → C} (h : X = Y) :
    map (fun i => eqToHom (congrFun h i)) = eqToHom (congrArg obj h) := by
  cases h
  exact map_id X

set_option backward.isDefEq.respectTransparency false in
/-- A generic equal-count input transport is the original ordered tensor transport. -/
theorem isoEquiv_finCongr {m n : ℕ} (h : m = n) (X : Fin m → C) (Y : Fin n → C)
    (hXY : ∀ i, X i = Y (Fin.cast h i)) :
    isoEquiv (finCongr h) (fun i => eqToIso (hXY i)) = congrIso h X Y hXY := by
  cases h
  have hX : X = Y := funext hXY
  cases hX
  apply Iso.ext
  rw [isoEquiv_hom]
  change mapEquiv (Equiv.refl (Fin m)) (fun i => 𝟙 (X i)) = 𝟙 (obj X)
  rw [mapEquiv_refl]
  exact map_id X

/-- Equal target objects expose the actual permutation comparison and its family transport. -/
theorem isoEquiv_eqToIso_hom {n : ℕ} (e : Equiv.Perm (Fin n))
    (X Y : Fin n → C) (hXY : ∀ i, X i = Y (e i))
    (hFamily : X ∘ e.symm = Y) :
    (isoEquiv e (fun i => eqToIso (hXY i))).hom =
      (permutationIso e X).hom ≫ eqToHom (congrArg obj hFamily) := by
  rw [isoEquiv_hom, mapEquiv_same]
  simp only [eqToIso.hom]
  have hMaps :
      (fun i => eqToHom (hXY (e.symm i)) ≫
        eqToHom (congrArg Y (e.apply_symm_apply i))) =
      (fun i => eqToHom (congrFun hFamily i)) := by
    funext i
    rw [eqToHom_trans]
  rw [hMaps, map_family_eqToHom hFamily]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_IsoEquivLaws

/- Source proof segment: BijectionIso -/
section source_BijectionIso
/-!
# The original tensor reindexing for arbitrary finite input bijections

The original isomorphism map retains the input bijection, even across
equal finite counts with different arithmetic expressions. Generic
composition and object transport precede the block specialization.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- Tensor the original finite input bijection, with its actual inverse-reindexed objects. -/
noncomputable def bijectionIso {m n : ℕ} (e : Fin m ≃ Fin n) (X : Fin m → C) :
    obj X ≅ obj (X ∘ e.symm) :=
  isoEquiv e (fun i => eqToIso (congrArg X (e.symm_apply_apply i).symm))

set_option backward.isDefEq.respectTransparency false in
/-- At a fixed arity the original bijection isomorphism is the actual permutation comparison. -/
theorem bijectionIso_same {n : ℕ} (e : Equiv.Perm (Fin n)) (X : Fin n → C) :
    bijectionIso e X = permutationIso e X := by
  apply Iso.ext
  have h := isoEquiv_eqToIso_hom e X (X ∘ e.symm)
    (fun i => congrArg X (e.symm_apply_apply i).symm) rfl
  simpa only [bijectionIso, eqToHom_refl, Category.comp_id] using h

set_option backward.isDefEq.respectTransparency false in
/-- The original consecutive finite reindexings retain their composite actual bijection. -/
theorem bijectionIso_trans {l m n : ℕ} (e : Fin l ≃ Fin m) (d : Fin m ≃ Fin n)
    (X : Fin l → C) :
    bijectionIso e X ≪≫ bijectionIso d (X ∘ e.symm) = bijectionIso (e.trans d) X := by
  unfold bijectionIso
  rw [isoEquiv_trans]
  apply isoEquiv_congr rfl
  intro i
  apply heq_of_eq
  apply Iso.ext
  simp only [Iso.trans_hom, eqToIso.hom, eqToHom_trans]

set_option backward.isDefEq.respectTransparency false in
/-- The original identity bijection has the actual identity tensor comparison. -/
theorem bijectionIso_refl {n : ℕ} (X : Fin n → C) :
    bijectionIso (Equiv.refl (Fin n)) X = Iso.refl (obj X) := by
  apply Iso.ext
  change (bijectionIso (1 : Equiv.Perm (Fin n)) X).hom = 𝟙 (obj X)
  rw [bijectionIso_same]
  exact permutationIso_one X

/-- Equality of the retained finite count gives precisely the original ordered tensor transport. -/
theorem bijectionIso_finCongr {m n : ℕ} (h : m = n) (X : Fin m → C) :
    bijectionIso (finCongr h) X =
      congrIso h X (X ∘ (finCongr h).symm)
        (fun i => congrArg X ((finCongr h).symm_apply_apply i).symm) :=
  isoEquiv_finCongr h X (X ∘ (finCongr h).symm)
    (fun i => congrArg X ((finCongr h).symm_apply_apply i).symm)

omit [Category C] [MonoidalCategory C] [SymmetricCategory C] in
/-- The original component equalities identify the actual inverse-reindexed family. -/
theorem reindexedFamily_eq {m n : ℕ} (e : Fin m ≃ Fin n)
    (X : Fin m → C) (Y : Fin n → C) (hXY : ∀ i, X i = Y (e i)) : X ∘ e.symm = Y :=
  funext (fun j => (hXY (e.symm j)).trans (congrArg Y (e.apply_symm_apply j)))

set_option backward.isDefEq.respectTransparency false in
/-- Original equal-object input isomorphisms are the actual reindexing and family transport. -/
theorem isoEquiv_eqToIso {m n : ℕ} (e : Fin m ≃ Fin n)
    (X : Fin m → C) (Y : Fin n → C) (hXY : ∀ i, X i = Y (e i)) :
    isoEquiv e (fun i => eqToIso (hXY i)) =
      bijectionIso e X ≪≫ eqToIso (congrArg obj (reindexedFamily_eq e X Y hXY)) := by
  have hmn := equiv_arity_eq e
  cases hmn
  apply Iso.ext
  rw [Iso.trans_hom, bijectionIso_same, eqToIso.hom]
  exact isoEquiv_eqToIso_hom e X Y hXY (reindexedFamily_eq e X Y hXY)

set_option backward.isDefEq.respectTransparency false in
/-- An actual equal-count bijection transports its original components
along its retained equality. -/
theorem isoEquiv_eqToIso_cast {m n : ℕ} (e : Fin m ≃ Fin n) (h : m = n)
    (he : e = finCongr h) (X : Fin m → C) (Y : Fin n → C)
    (hXY : ∀ i, X i = Y (e i)) :
    isoEquiv e (fun i => eqToIso (hXY i)) =
      congrIso h X Y (fun i => (hXY i).trans
        (congrArg Y (congrArg (fun d : Fin m ≃ Fin n => d i) he))) := by
  cases he
  exact isoEquiv_finCongr h X Y hXY

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_BijectionIso

/- Source proof segment: OrderedHeadTail -/
section source_OrderedHeadTail
/-!
# Original heterogeneous ordered tensor head-tail comparison

The comparison separates the first original input from the remaining
ordered tensor using the original unitors and associators, with the
empty tail retained.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The original heterogeneous ordered tensor separates into its first input and remaining
tensor. -/
def headTailIso : {n : ℕ} → (X : Fin (n + 1) → C) →
    obj X ≅ X 0 ⊗ obj (Fin.tail X)
  | 0, X => (λ_ (X 0)) ≪≫ (ρ_ (X 0)).symm
  | n + 1, X =>
      tensorIso (headTailIso (Fin.init X)) (Iso.refl (X (Fin.last (n + 1)))) ≪≫
        (α_ (X 0) (obj (Fin.tail (Fin.init X))) (X (Fin.last (n + 1)))) ≪≫
        eqToIso (show X 0 ⊗
            (obj (Fin.tail (Fin.init X)) ⊗ X (Fin.last (n + 1))) =
              X 0 ⊗ obj (Fin.tail X) from rfl)

/-- The original head-tail comparison retains both original unitors for an empty tail. -/
theorem headTailIso_zero_hom (X : Fin 1 → C) :
    (headTailIso X).hom = (λ_ (X 0)).hom ≫ (ρ_ (X 0)).inv := rfl

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedHeadTail

/- Source proof segment: OrderedHeadTailNaturality -/
section source_OrderedHeadTailNaturality
/-!
# Naturality of the original heterogeneous tensor head-tail map

Every original input morphism commutes with the unitor/associator
comparison separating the first factor and the retained tensor tail.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The original heterogeneous head-tail map is natural in all original input maps. -/
theorem headTailIso_naturality : ∀ {n : ℕ} {X Y : Fin (n + 1) → C}
    (f : ∀ i, X i ⟶ Y i),
    map f ≫ (headTailIso Y).hom =
      (headTailIso X).hom ≫ (f 0 ⊗ₘ map (Fin.tail f))
  | 0, X, Y, f => by
      change (𝟙 (𝟙_ C) ⊗ₘ f 0) ≫ ((λ_ (Y 0)).hom ≫ (ρ_ (Y 0)).inv) =
        ((λ_ (X 0)).hom ≫ (ρ_ (X 0)).inv) ≫ (f 0 ⊗ₘ 𝟙 (𝟙_ C))
      rw [id_tensorHom, tensorHom_id, ← Category.assoc,
        leftUnitor_naturality, Category.assoc, rightUnitor_inv_naturality]
      exact (Category.assoc _ _ _).symm
  | n + 1, X, Y, f => by
      let f₀ : ∀ i : Fin (n + 1), (Fin.init X) i ⟶ (Fin.init Y) i :=
        fun i => f i.castSucc
      have ih := headTailIso_naturality (n := n) (X := Fin.init X) (Y := Fin.init Y) f₀
      simp only [headTailIso, Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
        eqToIso.hom, eqToHom_refl, Category.comp_id]
      change (map f₀ ⊗ₘ f (Fin.last (n + 1))) ≫
          ((headTailIso (Fin.init Y)).hom ⊗ₘ 𝟙 (Y (Fin.last (n + 1)))) ≫
          (α_ (Y 0) (obj (Fin.tail (Fin.init Y))) (Y (Fin.last (n + 1)))).hom = _
      rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, ih]
      have hs : ((headTailIso (Fin.init X)).hom ≫
          (f₀ 0 ⊗ₘ map (Fin.tail f₀))) ⊗ₘ f (Fin.last (n + 1)) =
          ((headTailIso (Fin.init X)).hom ⊗ₘ 𝟙 (X (Fin.last (n + 1)))) ≫
            ((f₀ 0 ⊗ₘ map (Fin.tail f₀)) ⊗ₘ f (Fin.last (n + 1))) := by
        simpa only [Category.id_comp] using (tensorHom_comp_tensorHom (headTailIso (Fin.init X)).hom
          (𝟙 (X (Fin.last (n + 1)))) (f₀ 0 ⊗ₘ map (Fin.tail f₀))
          (f (Fin.last (n + 1)))).symm
      rw [hs]
      have ha := associator_naturality (f₀ 0) (map (Fin.tail f₀))
        (f (Fin.last (n + 1)))
      change ((f₀ 0 ⊗ₘ map (Fin.tail f₀)) ⊗ₘ f (Fin.last (n + 1))) ≫
          (α_ (Y 0) (obj (Fin.tail (Fin.init Y))) (Y (Fin.last (n + 1)))).hom =
        (α_ (X 0) (obj (Fin.tail (Fin.init X))) (X (Fin.last (n + 1)))).hom ≫
          (f₀ 0 ⊗ₘ (map (Fin.tail f₀) ⊗ₘ f (Fin.last (n + 1)))) at ha
      have hfull := congrArg
        (((headTailIso (Fin.init X)).hom ⊗ₘ 𝟙 (X (Fin.last (n + 1)))) ≫ ·) ha
      have hend :
          ((headTailIso (Fin.init X)).hom ⊗ₘ 𝟙 (X (Fin.last (n + 1)))) ≫
            (α_ (X 0) (obj (Fin.tail (Fin.init X))) (X (Fin.last (n + 1)))).hom ≫
              (f₀ 0 ⊗ₘ (map (Fin.tail f₀) ⊗ₘ f (Fin.last (n + 1)))) =
          (((headTailIso (Fin.init X)).hom ⊗ₘ 𝟙 (X (Fin.last (n + 1)))) ≫
            (α_ (X 0) (obj (Fin.tail (Fin.init X))) (X (Fin.last (n + 1)))).hom) ≫
              (f 0 ⊗ₘ map (X := Fin.tail X) (Y := Fin.tail Y)
                (fun i : Fin (n + 1) => f i.succ)) := by
        exact (Category.assoc _ _ _).symm
      exact (Category.assoc _ _ _).trans (hfull.trans hend)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedHeadTailNaturality

/- Source proof segment: OrderedHeadTailNatIso -/
section source_OrderedHeadTailNatIso
/-!
# Original natural head-tail tensor comparison

The full natural isomorphism is assembled from the original
heterogeneous unitor/associator component maps and their naturality.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The actual tensor functor separating the first original input and its original tensor tail. -/
def headTailFunctor (n : ℕ) : (Fin (n + 1) → C) ⥤ C :=
  ((Pi.eval (fun _ : Fin (n + 1) => C) 0).prod'
    (Pi.comap (fun _ : Fin (n + 1) => C) Fin.succ ⋙ functor C n)) ⋙ tensor C

/-- The original heterogeneous tensor head-tail maps form a full natural isomorphism. -/
def headTailNatIso (n : ℕ) : functor C (n + 1) ≅ headTailFunctor (C := C) n :=
  NatIso.ofComponents headTailIso (by
    intro X Y f
    exact headTailIso_naturality f)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedHeadTailNatIso

/- Source proof segment: ActualTensorFirstExtension -/
section source_ActualTensorFirstExtension
/-!
# Original tensor reindexing with one retained first input

The input permutation fixes the original first slot. Its tensor
comparison is constructed from the original natural head-tail maps,
the original tail comparison, and the retained first-object identity.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory
open TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The original finite input permutation extended by one fixed first input. -/
noncomputable def extendFirstPerm (n : ℕ) :
    Equiv.Perm (Fin n) →* Equiv.Perm (Fin (n + 1)) :=
  { toFun p := (finSuccEquiv n).trans ((Equiv.optionCongr p).trans (finSuccEquiv n).symm)
    map_one' := by
      apply Equiv.ext
      intro i
      change (finSuccEquiv n).symm
        (Equiv.optionCongr (Equiv.refl (Fin n)) ((finSuccEquiv n) i)) = i
      rw [Equiv.optionCongr_refl]
      exact (finSuccEquiv n).symm_apply_apply i
    map_mul' p q := by
      apply Equiv.ext
      intro i
      simp only [Equiv.trans_apply, Equiv.Perm.mul_apply]
      rw [Equiv.apply_symm_apply]
      have h : p * q = q.trans p := rfl
      rw [h, Equiv.optionCongr_trans]
      rfl }

/-- The original first input is fixed by the extension. -/
theorem extendFirstPerm_zero {n : ℕ} (p : Equiv.Perm (Fin n)) :
    extendFirstPerm n p 0 = 0 := by
  change (finSuccEquiv n).symm (Equiv.optionCongr p ((finSuccEquiv n) 0)) = 0
  rw [finSuccEquiv_zero]
  rfl

/-- The original tail input permutation is retained at every tail position. -/
theorem extendFirstPerm_succ {n : ℕ} (p : Equiv.Perm (Fin n)) (i : Fin n) :
    extendFirstPerm n p i.succ = (p i).succ := by
  change (finSuccEquiv n).symm (Equiv.optionCongr p ((finSuccEquiv n) i.succ)) = _
  rw [finSuccEquiv_succ]
  rfl

/-- The original inverse input extension also fixes the first position. -/
theorem extendFirstPerm_inverse_zero {n : ℕ} (p : Equiv.Perm (Fin n)) :
    (extendFirstPerm n p).symm 0 = 0 := by
  exact (extendFirstPerm n p).injective (by rw [Equiv.apply_symm_apply, extendFirstPerm_zero])

/-- The original inverse tail permutation is retained at every tail position. -/
theorem extendFirstPerm_inverse_succ {n : ℕ} (p : Equiv.Perm (Fin n)) (i : Fin n) :
    (extendFirstPerm n p).symm i.succ = (p.symm i).succ := by
  apply (extendFirstPerm n p).injective
  rw [Equiv.apply_symm_apply, extendFirstPerm_succ, Equiv.apply_symm_apply]

omit [Category.{v} C] [MonoidalCategory C] in
/-- The original inverse-reindexed family retains the original first object. -/
theorem familyEquiv_first_zero {n : ℕ} (p : Equiv.Perm (Fin n)) (X : Fin (n + 1) → C) :
    familyEquiv (extendFirstPerm n p) X 0 = X 0 := by
  rw [familyEquiv_apply, extendFirstPerm_inverse_zero]

omit [Category.{v} C] [MonoidalCategory C] in
/-- The original inverse-reindexed family retains its actual reindexed tail. -/
theorem familyEquiv_first_tail {n : ℕ} (p : Equiv.Perm (Fin n)) (X : Fin (n + 1) → C) :
    Fin.tail (familyEquiv (extendFirstPerm n p) X) = familyEquiv p (Fin.tail X) := by
  funext i
  change X ((extendFirstPerm n p).symm i.succ) = X (p.symm i).succ
  rw [extendFirstPerm_inverse_succ]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ActualTensorFirstExtension

/- Source proof segment: ActualTensorFirstComparison -/
section source_ActualTensorFirstComparison
/-!
# Original natural tensor comparisons retaining a fixed first factor

The comparison is constructed from the original natural head-tail
maps and the actual tail comparison. The original first object and
all original component maps are retained.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory
open TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {n : ℕ}

/-- The original tensor of the retained first object and reindexed original tail. -/
def firstTarget (p : Equiv.Perm (Fin n)) : (Fin (n + 1) → C) ⥤ C :=
  ((Pi.eval (fun _ : Fin (n + 1) => C) 0).prod'
    (Pi.comap (fun _ : Fin (n + 1) => C) Fin.succ ⋙ pull C n p ⋙ functor C n)) ⋙ tensor C

/-- The reindexed original head-tail tensor has exactly the retained first/actual tail factors. -/
theorem firstTarget_eq (p : Equiv.Perm (Fin n)) :
    pull C (n + 1) (extendFirstPerm n p) ⋙ headTailFunctor (C := C) n =
      firstTarget (C := C) p := by
  apply Functor.hext
  · intro X
    change (familyEquiv (extendFirstPerm n p) X) 0 ⊗
      obj (Fin.tail (familyEquiv (extendFirstPerm n p) X)) =
      X 0 ⊗ obj (familyEquiv p (Fin.tail X))
    rw [familyEquiv_first_zero, familyEquiv_first_tail]
  · intro X Y f
    change HEq
      (f ((extendFirstPerm n p).symm 0) ⊗ₘ
        map (fun i : Fin n => f ((extendFirstPerm n p).symm i.succ)))
      (f 0 ⊗ₘ map (fun i : Fin n => f (p.symm i).succ))
    have hi : (fun i : Fin n => (extendFirstPerm n p).symm i.succ) =
        (fun i : Fin n => (p.symm i).succ) := funext (extendFirstPerm_inverse_succ p)
    rw [extendFirstPerm_inverse_zero]
    cases hi
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The original tail tensor comparison with the identity of the retained first object. -/
def firstComparisonAux (r : TensorReindexing C n) :
    headTailFunctor (C := C) n ≅ firstTarget r.perm :=
  NatIso.ofComponents (fun X => tensorIso (Iso.refl (X 0))
    (r.comparison.app (Fin.tail X))) (by
      intro X Y f
      have h := r.comparison.hom.naturality
        (show Fin.tail X ⟶ Fin.tail Y from fun i => f i.succ)
      change (f 0 ⊗ₘ map (Fin.tail f)) ≫
          (𝟙 (Y 0) ⊗ₘ r.comparison.hom.app (Fin.tail Y)) =
        (𝟙 (X 0) ⊗ₘ r.comparison.hom.app (Fin.tail X)) ≫
          (f 0 ⊗ₘ map (fun i => f (r.perm.symm i).succ))
      rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
        Category.comp_id, Category.id_comp]
      exact congrArg (f 0 ⊗ₘ ·) h)

/-- The actual natural fixed-first tensor comparison including the original head-tail maps. -/
noncomputable def firstComparison (r : TensorReindexing C n) :
    functor C (n + 1) ≅ pull C (n + 1) (extendFirstPerm n r.perm) ⋙ functor C (n + 1) :=
  headTailNatIso n ≪≫ firstComparisonAux r ≪≫
    (eqToIso (firstTarget_eq r.perm)).symm ≪≫
    (Functor.isoWhiskerLeft (pull C (n + 1) (extendFirstPerm n r.perm))
      (headTailNatIso n)).symm

/-- Extend an original tensor reindexing through one retained first input. -/
noncomputable def extendFirstTensor (r : TensorReindexing C n) : TensorReindexing C (n + 1) where
  perm := extendFirstPerm n r.perm
  comparison := firstComparison r

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ActualTensorFirstComparison

/- Source proof segment: FirstPayloadCore -/
section source_FirstPayloadCore
/-!
# The original fixed-first payload and head-tail conjugation

The retained-first tensor payload is compared to the actual reindexed
head-tail functor with its original equality transport. Conjugation uses
the original heterogeneous head-tail isomorphisms.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {n : ℕ}

/-- The original natural retained-first payload with the actual reindexed target frame. -/
noncomputable def firstPayload (r : TensorReindexing C n) :
    headTailFunctor (C := C) n ≅
      pull C (n + 1) (extendFirstPerm n r.perm) ⋙ headTailFunctor (C := C) n :=
  firstComparisonAux r ≪≫ (eqToIso (firstTarget_eq r.perm)).symm

/-- The payload evaluation retains the original first identity, tail map and target transport. -/
theorem firstPayload_hom_app (r : TensorReindexing C n) (X : Fin (n + 1) → C) :
    (firstPayload r).hom.app X =
      (𝟙 (X 0) ⊗ₘ r.comparison.hom.app (Fin.tail X)) ≫
        eqToHom (Functor.congr_obj (firstTarget_eq r.perm).symm X) := by
  simp only [firstPayload, Iso.trans_hom, Iso.symm_hom, eqToIso.inv,
    NatTrans.comp_app, eqToHom_app]
  rfl

/-- The actual payload is the original retained-first tensor map after its target equality. -/
theorem firstPayload_hom_heq (r : TensorReindexing C n) (X : Fin (n + 1) → C) :
    HEq ((firstPayload r).hom.app X) (𝟙 (X 0) ⊗ₘ r.comparison.hom.app (Fin.tail X)) :=
  (heq_of_eq (firstPayload_hom_app r X)).trans (comp_eqToHom_heq _ _)

/-- Conjugate an original head-tail map by both original heterogeneous tensor comparisons. -/
def headTailConjugate (X Y : Fin (n + 1) → C)
    (f : (headTailFunctor (C := C) n).obj X ⟶ (headTailFunctor (C := C) n).obj Y) :
    (functor C (n + 1)).obj X ⟶ (functor C (n + 1)).obj Y :=
  (headTailNatIso (C := C) n).hom.app X ≫ f ≫ (headTailNatIso (C := C) n).inv.app Y

/-- Original head-tail conjugation preserves the original identity map. -/
theorem headTailConjugate_id (X : Fin (n + 1) → C) :
    headTailConjugate X X (𝟙 ((headTailFunctor (C := C) n).obj X)) = 𝟙 (obj X) := by
  change ((headTailNatIso (C := C) n).app X).hom ≫ 𝟙 _ ≫
    ((headTailNatIso (C := C) n).app X).inv = _
  rw [Category.id_comp, Iso.hom_inv_id]
  rfl

/-- Original head-tail conjugation preserves actual consecutive maps. -/
theorem headTailConjugate_comp (X Y Z : Fin (n + 1) → C)
    (f : (headTailFunctor (C := C) n).obj X ⟶ (headTailFunctor (C := C) n).obj Y)
    (g : (headTailFunctor (C := C) n).obj Y ⟶ (headTailFunctor (C := C) n).obj Z) :
    headTailConjugate X Y f ≫ headTailConjugate Y Z g = headTailConjugate X Z (f ≫ g) :=
  (Iso.homCongr_comp ((headTailNatIso (C := C) n).app X).symm
    ((headTailNatIso (C := C) n).app Y).symm ((headTailNatIso (C := C) n).app Z).symm f g).symm

/-- The generic conjugation factory transports a target family and its original map together. -/
theorem headTailConjugate_heq (X Y Y' : Fin (n + 1) → C) (hY : Y = Y')
    (f : (headTailFunctor (C := C) n).obj X ⟶ (headTailFunctor (C := C) n).obj Y)
    (g : (headTailFunctor (C := C) n).obj X ⟶ (headTailFunctor (C := C) n).obj Y')
    (hf : HEq f g) : HEq (headTailConjugate X Y f) (headTailConjugate X Y' g) := by
  cases hY
  have hfg : f = g := eq_of_heq hf
  subst g
  rfl

/-- The actual fixed-first tensor map is the original head-tail conjugation of its payload. -/
theorem firstComparison_eq (r : TensorReindexing C n) :
    firstComparison r = headTailNatIso n ≪≫ firstPayload r ≪≫
      (Functor.isoWhiskerLeft (pull C (n + 1) (extendFirstPerm n r.perm))
        (headTailNatIso n)).symm := by
  simp only [firstComparison, firstPayload, Iso.trans_assoc]

/-- The actual fixed-first tensor map is the original head-tail conjugation of its payload. -/
theorem extendFirstTensor_hom_conjugate (r : TensorReindexing C n) (X : Fin (n + 1) → C) :
    (extendFirstTensor r).comparison.hom.app X =
      headTailConjugate X (familyEquiv (extendFirstPerm n r.perm) X)
        ((firstPayload r).hom.app X) := by
  change (firstComparison r).hom.app X = _
  rw [firstComparison_eq]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_inv]
  rfl

/-- The exact original fixed-first map retains both original head-tail maps and target transport. -/
theorem extendFirstTensor_hom_app (r : TensorReindexing C n) (X : Fin (n + 1) → C) :
    (extendFirstTensor r).comparison.hom.app X =
      (headTailIso X).hom ≫ (𝟙 (X 0) ⊗ₘ r.comparison.hom.app (Fin.tail X)) ≫
        eqToHom (Functor.congr_obj (firstTarget_eq r.perm).symm X) ≫
        (headTailIso (familyEquiv (extendFirstPerm n r.perm) X)).inv := by
  simp only [extendFirstTensor, firstComparison, Iso.trans_hom, NatTrans.comp_app]
  rfl

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FirstPayloadCore

/- Source proof segment: VerifiedTensorFirstHom -/
section source_VerifiedTensorFirstHom
/-!
# The actual fixed-first natural tensor reindexing homomorphism

The first object is retained and the original tail comparison is
conjugated by the original head-tail maps. Its full group laws use
the actual permutation/frame maps and actual tensor composition.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {n : ℕ}

/-- The retained-first payload of the identity is the original head-tail identity map. -/
theorem firstPayload_one_heq (X : Fin (n + 1) → C) :
    HEq ((firstPayload (1 : TensorReindexing C n)).hom.app X)
      (𝟙 ((headTailFunctor (C := C) n).obj X)) := by
  have ht : (𝟙 (X 0) ⊗ₘ (1 : TensorReindexing C n).comparison.hom.app (Fin.tail X)) =
      𝟙 ((headTailFunctor (C := C) n).obj X) := by
    rw [TensorReindexing.one_hom_app]
    exact id_tensorHom_id _ _
  exact (firstPayload_hom_heq (1 : TensorReindexing C n) X).trans (heq_of_eq ht)

/-- The retained-first payload preserves the original consecutive tail maps with actual frames. -/
theorem firstPayload_mul_heq (r s : TensorReindexing C n) (X : Fin (n + 1) → C) :
    HEq ((firstPayload (r * s)).hom.app X)
      ((firstPayload s).hom.app X ≫
        (firstPayload r).hom.app (familyEquiv (extendFirstPerm n s.perm) X)) := by
  let T := Fin.tail X
  let V := X 0
  let Y := familyEquiv (extendFirstPerm n s.perm) X
  let U := familyEquiv s.perm T
  let Z := familyEquiv (extendFirstPerm n r.perm) Y
  let W := familyEquiv r.perm U
  have hY0 : Y 0 = V := familyEquiv_first_zero s.perm X
  have hYT : Fin.tail Y = U := familyEquiv_first_tail s.perm X
  have hY : (headTailFunctor (C := C) n).obj Y = V ⊗ obj U := by
    change Y 0 ⊗ obj (Fin.tail Y) = V ⊗ obj U
    rw [hY0, hYT]
  have hZ : (headTailFunctor (C := C) n).obj Z = V ⊗ obj W := by
    change Z 0 ⊗ obj (Fin.tail Z) = V ⊗ obj W
    dsimp only [Z]
    rw [familyEquiv_first_zero, familyEquiv_first_tail, hY0, hYT]
  have hs := firstPayload_hom_heq s X
  have hr : HEq ((firstPayload r).hom.app Y) (𝟙 V ⊗ₘ r.comparison.hom.app U) := by
    have aux (A B : C) (I J : Fin n → C) (hA : A = B) (hI : I = J) :
        HEq (𝟙 A ⊗ₘ r.comparison.hom.app I) (𝟙 B ⊗ₘ r.comparison.hom.app J) := by
      cases hA
      cases hI
      rfl
    exact (firstPayload_hom_heq r Y).trans (aux _ _ _ _ hY0 hYT)
  have hc : HEq ((firstPayload s).hom.app X ≫ (firstPayload r).hom.app Y)
      ((𝟙 V ⊗ₘ s.comparison.hom.app T) ≫ (𝟙 V ⊗ₘ r.comparison.hom.app U)) :=
    heq_comp (show (headTailFunctor (C := C) n).obj X = V ⊗ obj T from rfl) hY hZ hs hr
  have hm : 𝟙 V ⊗ₘ (r * s).comparison.hom.app T =
      𝟙 V ⊗ₘ (s.comparison.hom.app T ≫ r.comparison.hom.app U) :=
    congrArg (𝟙 V ⊗ₘ ·) (TensorReindexing.mul_hom_app r s T)
  have ht : 𝟙 V ⊗ₘ (s.comparison.hom.app T ≫ r.comparison.hom.app U) =
      (𝟙 V ⊗ₘ s.comparison.hom.app T) ≫ (𝟙 V ⊗ₘ r.comparison.hom.app U) := by
    simpa only [Category.id_comp] using
      (tensorHom_comp_tensorHom (𝟙 V) (s.comparison.hom.app T)
        (𝟙 V) (r.comparison.hom.app U)).symm
  exact (firstPayload_hom_heq (r * s) X).trans
    ((heq_of_eq hm).trans ((heq_of_eq ht).trans hc.symm))

/-- The original fixed-first tensor record preserves its original identity comparison. -/
theorem extendFirstTensor_one : extendFirstTensor (1 : TensorReindexing C n) = 1 := by
  apply TensorReindexing.ext (show (extendFirstTensor (1 : TensorReindexing C n)).perm =
      (1 : TensorReindexing C (n + 1)).perm from by
    change extendFirstPerm n (1 : Equiv.Perm (Fin n)) = 1
    exact map_one _)
  intro X
  let Y := familyEquiv (extendFirstPerm n (1 : Equiv.Perm (Fin n))) X
  have hY : Y = X := by
    dsimp only [Y]
    rw [map_one]
    rfl
  have hc := headTailConjugate_heq X Y X hY
    ((firstPayload (1 : TensorReindexing C n)).hom.app X)
    (𝟙 ((headTailFunctor (C := C) n).obj X)) (firstPayload_one_heq X)
  exact (heq_of_eq (extendFirstTensor_hom_conjugate (1 : TensorReindexing C n) X)).trans
    (hc.trans ((heq_of_eq (headTailConjugate_id X)).trans
      (heq_of_eq (TensorReindexing.one_hom_app X)).symm))

/-- The original fixed-first tensor record preserves actual
consecutive comparison multiplication. -/
theorem extendFirstTensor_mul (r s : TensorReindexing C n) :
    extendFirstTensor (r * s) = extendFirstTensor r * extendFirstTensor s := by
  apply TensorReindexing.ext (show (extendFirstTensor (r * s)).perm =
      (extendFirstTensor r * extendFirstTensor s).perm from by
    change extendFirstPerm n (r.perm * s.perm) =
      extendFirstPerm n r.perm * extendFirstPerm n s.perm
    exact map_mul _ _ _)
  intro X
  let Y := familyEquiv (extendFirstPerm n s.perm) X
  let Z := familyEquiv (extendFirstPerm n r.perm) Y
  let Z' := familyEquiv (extendFirstPerm n (r * s).perm) X
  have hZ : Z' = Z := by
    change familyEquiv (extendFirstPerm n (r.perm * s.perm)) X =
      familyEquiv (extendFirstPerm n r.perm) (familyEquiv (extendFirstPerm n s.perm) X)
    rw [map_mul]
    rfl
  have hc := headTailConjugate_heq X Z' Z hZ ((firstPayload (r * s)).hom.app X)
    ((firstPayload s).hom.app X ≫ (firstPayload r).hom.app Y) (firstPayload_mul_heq r s X)
  have hrhs : (extendFirstTensor r * extendFirstTensor s).comparison.hom.app X =
      headTailConjugate X Z ((firstPayload s).hom.app X ≫ (firstPayload r).hom.app Y) := by
    rw [TensorReindexing.mul_hom_app, extendFirstTensor_hom_conjugate,
      extendFirstTensor_hom_conjugate]
    change headTailConjugate X Y ((firstPayload s).hom.app X) ≫
      headTailConjugate Y Z ((firstPayload r).hom.app Y) = _
    exact headTailConjugate_comp X Y Z _ _
  exact (heq_of_eq (extendFirstTensor_hom_conjugate (r * s) X)).trans
    (hc.trans (heq_of_eq hrhs).symm)

/-- The actual fixed-first tensor reindexing group homomorphism, including empty tails. -/
noncomputable def extendFirstHom : TensorReindexing C n →* TensorReindexing C (n + 1) where
  toFun := extendFirstTensor
  map_one' := extendFirstTensor_one
  map_mul' := extendFirstTensor_mul

/-- The homomorphism retains the original fixed-first finite input permutation. -/
@[simp] theorem extendFirstHom_perm (r : TensorReindexing C n) :
    (extendFirstHom r).perm = extendFirstPerm n r.perm := rfl

/-- The actual group homomorphism retains its original head-tail/tail tensor maps and transport. -/
theorem extendFirstHom_hom_app (r : TensorReindexing C n) (X : Fin (n + 1) → C) :
    (extendFirstHom r).comparison.hom.app X =
      (headTailIso X).hom ≫ (𝟙 (X 0) ⊗ₘ r.comparison.hom.app (Fin.tail X)) ≫
        eqToHom (Functor.congr_obj (firstTarget_eq r.perm).symm X) ≫
        (headTailIso (familyEquiv (extendFirstPerm n r.perm) X)).inv :=
  extendFirstTensor_hom_app r X

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_VerifiedTensorFirstHom

/- Source proof segment: FirstPermutationShape -/
section source_FirstPermutationShape
/-!
# Original transpositions through the fixed-first finite permutation extension

The statement follows from the original zero/successor slot maps and
injectivity of the original finite successor embedding.
-/

@[expose] public section

set_option autoImplicit false

namespace CategoryTheory.MonoidalCategory.OrderedTensor

/-- The actual fixed-first input extension sends an original transposition to its shifted one. -/
theorem extendFirstPerm_swap {n : ℕ} (i j : Fin n) :
    extendFirstPerm n (Equiv.swap i j) = Equiv.swap i.succ j.succ := by
  apply Equiv.ext
  intro x
  refine Fin.cases ?_ (fun k => ?_) x
  · rw [extendFirstPerm_zero]
    exact (Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm
      (Fin.succ_ne_zero j).symm).symm
  · rw [extendFirstPerm_succ]
    exact Function.Injective.map_swap (Fin.succ_injective n) i j k

/-- An actual adjacent input transposition is retained at the shifted adjacent tail positions. -/
theorem extendFirstPerm_adjacent {n : ℕ} (i : Fin n) :
    extendFirstPerm (n + 1) (Equiv.swap i.castSucc i.succ) =
      Equiv.swap i.succ.castSucc i.succ.succ :=
  extendFirstPerm_swap i.castSucc i.succ

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FirstPermutationShape

/- Source proof segment: BinaryFirstPull -/
section source_BinaryFirstPull
/-!
# Original binary interchange after extracting the first factor

The original prefix-adjusted braiding commutes with the original
associator comparison extracting a retained first factor. All objects
and the prefix map are independent and heterogeneous.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The original binary association extracting a first factor before two final objects. -/
def firstPullIso (A Q B D : C) : ((A ⊗ Q) ⊗ B) ⊗ D ≅ A ⊗ ((Q ⊗ B) ⊗ D) :=
  tensorIso (α_ A Q B) (Iso.refl D) ≪≫ α_ A (Q ⊗ B) D

/-- Extracting the first factor commutes with the original braiding of the two final objects. -/
theorem firstPullIso_swap (A Q B D : C) :
    firstPullIso A Q B D ≪≫ whiskerLeftIso A (swapLastIso Q B D) =
      swapLastIso (A ⊗ Q) B D ≪≫ firstPullIso A Q D B := by
  apply Iso.ext
  simp only [firstPullIso, swapLastIso, Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
    whiskerLeftIso_hom, Iso.symm_hom]
  monoidal

/-- The original first-factor extraction after an arbitrary original prefix map. -/
def firstPullHom {P A Q : C} (f : P ⟶ A ⊗ Q) (B D : C) :
    (P ⊗ B) ⊗ D ⟶ A ⊗ ((Q ⊗ B) ⊗ D) :=
  ((f ⊗ₘ 𝟙 B) ⊗ₘ 𝟙 D) ≫ (firstPullIso A Q B D).hom

/-- Original prefix naturality and binary associators give the first-factor interchange law. -/
theorem firstPullHom_swap {P A Q : C} (f : P ⟶ A ⊗ Q) (B D : C) :
    firstPullHom f B D ≫ (𝟙 A ⊗ₘ (swapLastIso Q B D).hom) =
      (swapLastIso P B D).hom ≫ firstPullHom f D B := by
  have hc := congrArg Iso.hom (firstPullIso_swap A Q B D)
  simp only [Iso.trans_hom, whiskerLeftIso_hom] at hc
  have hn : ((f ⊗ₘ 𝟙 B) ⊗ₘ 𝟙 D) ≫ (swapLastIso (A ⊗ Q) B D).hom =
      (swapLastIso P B D).hom ≫ ((f ⊗ₘ 𝟙 D) ⊗ₘ 𝟙 B) := by
    simpa only [Category.comp_id, Category.id_comp] using
      swapLastIso_naturality f (𝟙 B) (𝟙 D)
  unfold firstPullHom
  rw [Category.assoc, id_tensorHom, hc, ← Category.assoc, hn, Category.assoc]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_BinaryFirstPull

/- Source proof segment: ShiftedShapes -/
section source_ShiftedShapes
/-!
# Original input shapes of shifted adjacent transpositions

The first input is fixed and the original adjacent tail permutation is
retained at every successor position. The target tensor equality is
the corresponding original first/tail object transport.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

/-- The original adjacent input transposition shifted past one retained first input. -/
def shiftedSwap {n : ℕ} (i : Fin n) : Equiv.Perm (Fin (n + 2)) :=
  Equiv.swap i.succ.castSucc i.succ.succ

/-- The shifted original adjacent transposition fixes the original first input. -/
@[simp] theorem shiftedSwap_zero {n : ℕ} (i : Fin n) : shiftedSwap i 0 = 0 := by
  unfold shiftedSwap
  apply Equiv.swap_apply_of_ne_of_ne
  · simpa only [← Fin.succ_castSucc] using (Fin.succ_ne_zero i.castSucc).symm
  · exact (Fin.succ_ne_zero i.succ).symm

/-- The shifted original adjacent map retains the original tail permutation at every tail slot. -/
@[simp] theorem shiftedSwap_succ {n : ℕ} (i : Fin n) (j : Fin (n + 1)) :
    shiftedSwap i j.succ = (Equiv.swap i.castSucc i.succ j).succ := by
  unfold shiftedSwap
  simpa only [Fin.succ_castSucc] using
    (Fin.succ_injective (n + 1)).swap_apply i.castSucc i.succ j

variable {C : Type u}

/-- The reindexed family retains the original first object. -/
theorem shiftedFamily_zero {n : ℕ} (i : Fin n) (X : Fin (n + 2) → C) :
    (X ∘ shiftedSwap i) 0 = X 0 := by rw [Function.comp_apply, shiftedSwap_zero]

/-- The reindexed original tail is exactly the original adjacent tail family. -/
theorem shiftedFamily_tail {n : ℕ} (i : Fin n) (X : Fin (n + 2) → C) :
    Fin.tail (X ∘ shiftedSwap i) = Fin.tail X ∘ Equiv.swap i.castSucc i.succ := by
  funext j
  change X (shiftedSwap i j.succ) = X (Equiv.swap i.castSucc i.succ j).succ
  rw [shiftedSwap_succ]

/-- The original input family before two final objects. -/
def initTwo {n : ℕ} (X : Fin (n + 2) → C) : Fin n → C :=
  fun i => X i.castSucc.castSucc

/-- Taking the original tail commutes with retaining the original two-fold initial family. -/
theorem initTwo_tail {n : ℕ} (X : Fin (n + 3) → C) :
    initTwo (Fin.tail X) = Fin.tail (initTwo X) := by
  funext i
  rfl

/-- The shifted final transposition retains the complete original initial family. -/
theorem initTwo_shifted_last {n : ℕ} (X : Fin (n + 3) → C) :
    initTwo (X ∘ shiftedSwap (Fin.last n)) = initTwo X := by
  funext j
  change X (Equiv.swap (Fin.last (n + 1)).castSucc (Fin.last (n + 1)).succ
    j.castSucc.castSucc) = X j.castSucc.castSucc
  rw [Equiv.swap_apply_of_ne_of_ne]
  · exact fun h => Fin.castSucc_ne_last j ((Fin.castSucc_injective (n + 2)) h)
  · exact Fin.castSucc_ne_last j.castSucc

/-- The shifted final transposition sends the original penultimate input to the original last
one. -/
theorem shifted_last_penultimate {n : ℕ} (X : Fin (n + 3) → C) :
    (X ∘ shiftedSwap (Fin.last n)) (Fin.last (n + 1)).castSucc = X (Fin.last (n + 2)) := by
  change X (Equiv.swap (Fin.last (n + 1)).castSucc (Fin.last (n + 1)).succ
    (Fin.last (n + 1)).castSucc) = _
  rw [Equiv.swap_apply_left]
  rfl

/-- The shifted final transposition sends the original last input to the original penultimate
one. -/
theorem shifted_last_last {n : ℕ} (X : Fin (n + 3) → C) :
    (X ∘ shiftedSwap (Fin.last n)) (Fin.last (n + 2)) = X (Fin.last (n + 1)).castSucc := by
  change X (Equiv.swap (Fin.last (n + 1)).castSucc (Fin.last (n + 1)).succ
    (Fin.last (n + 1)).succ) = _
  rw [Equiv.swap_apply_right]

variable [Category.{v} C] [MonoidalCategory C]

/-- The exact original target equality after retaining the first object and reindexing the tail. -/
theorem shiftedHeadTail_target {n : ℕ} (i : Fin n) (X : Fin (n + 2) → C) :
    (X ∘ shiftedSwap i) 0 ⊗ obj (Fin.tail (X ∘ shiftedSwap i)) =
      X 0 ⊗ obj (Fin.tail X ∘ Equiv.swap i.castSucc i.succ) := by
  rw [shiftedFamily_zero, shiftedFamily_tail]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ShiftedShapes

/- Source proof segment: HeadTailBlockNormal -/
section source_HeadTailBlockNormal
/-!
# Original two-step head-tail extraction

Two recursive head-tail steps are exactly the original binary first
factor extraction before the two final objects. Input-family equality
transports this entire map, including its source and target tensors.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The original binary head-tail extraction from a prefix and two retained final objects. -/
def headTailTwoHom {n : ℕ} (U : Fin (n + 1) → C) (B D : C) :
    (obj U ⊗ B) ⊗ D ⟶ U 0 ⊗ ((obj (Fin.tail U) ⊗ B) ⊗ D) :=
  firstPullHom (headTailIso U).hom B D

set_option backward.isDefEq.respectTransparency false in
/-- Two original recursive head-tail maps have exactly the original binary extraction form. -/
theorem headTailIso_two_hom {n : ℕ} (X : Fin (n + 3) → C) :
    (headTailIso X).hom =
      headTailTwoHom (initTwo X) (X (Fin.last (n + 1)).castSucc) (X (Fin.last (n + 2))) := by
  simp only [headTailIso, Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
    eqToIso.hom, eqToHom_refl, Category.comp_id, headTailTwoHom, firstPullHom,
    firstPullIso, initTwo, tensorHom_id, comp_whiskerRight, Category.assoc]
  rfl

/-- One original recursive head-tail step, before its actual final object. -/
def headTailOneHom {n : ℕ} (U : Fin (n + 1) → C) (D : C) :
    obj U ⊗ D ⟶ U 0 ⊗ (obj (Fin.tail U) ⊗ D) :=
  ((headTailIso U).hom ⊗ₘ 𝟙 D) ≫ (α_ (U 0) (obj (Fin.tail U)) D).hom

set_option backward.isDefEq.respectTransparency false in
/-- The original head-tail successor is exactly its one-step binary comparison. -/
theorem headTailIso_one_hom {n : ℕ} (X : Fin (n + 2) → C) :
    (headTailIso X).hom = headTailOneHom (Fin.init X) (X (Fin.last (n + 1))) := by
  simp only [headTailIso, Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
    eqToIso.hom, eqToHom_refl, Category.comp_id, headTailOneHom]
  rfl

/-- Equality of the original prefix and final object transports the entire one-step comparison. -/
theorem headTailOneHom_heq {n : ℕ} (U U' : Fin (n + 1) → C) (D D' : C)
    (hU : U = U') (hD : D = D') : HEq (headTailOneHom U D) (headTailOneHom U' D') := by
  cases hU
  cases hD
  rfl

/-- The original two-step extraction transports the entire original prefix and final objects. -/
theorem headTailTwoHom_heq {n : ℕ} (U U' : Fin (n + 1) → C) (B B' D D' : C)
    (hU : U = U') (hB : B = B') (hD : D = D') :
    HEq (headTailTwoHom U B D) (headTailTwoHom U' B' D') := by
  cases hU
  cases hB
  cases hD
  rfl

/-- The original head-tail map transports with equality of its entire original input family. -/
theorem headTailIso_family_heq {n : ℕ} (X Y : Fin (n + 1) → C) (hXY : X = Y) :
    HEq (headTailIso X).hom (headTailIso Y).hom := by
  cases hXY
  rfl

/-- The shifted final target has the original extracted prefix and the actual exchanged objects. -/
theorem shiftedLast_headTail_target {n : ℕ} (X : Fin (n + 3) → C) :
    (X ∘ shiftedSwap (Fin.last n)) 0 ⊗
      obj (Fin.tail (X ∘ shiftedSwap (Fin.last n))) =
    X 0 ⊗ ((obj (Fin.tail (initTwo X)) ⊗ X (Fin.last (n + 2))) ⊗
      X (Fin.last (n + 1)).castSucc) := by
  rw [shiftedFamily_zero, shiftedFamily_tail, obj_swapLast]
  rfl

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_HeadTailBlockNormal

/- Source proof segment: FirstAssociateFrame -/
section source_FirstAssociateFrame
/-!
# Original first-factor associator transport

These equalities use original object equalities and binary associator
naturality. They transport the actual head-tail induction diagram with
its retained final object.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

omit [MonoidalCategory C] in
/-- Original source/target equality transports turn a heterogeneous map equality into exact
equality. -/
theorem shiftedTransportedHom {A B A' B' : C} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B') (hfg : HEq f g) :
    eqToHom hA.symm ≫ f ≫ eqToHom hB = g := by
  cases hA
  cases hB
  have h : f = g := eq_of_heq hfg
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, h]

/-- Original equality transport in a retained-first tensor factor cancels its exact endpoint map. -/
theorem fixedLeft_tensor_postEq_cancel {P A S T U : C} (k : P ⟶ A ⊗ S)
    (f : S ⟶ T) (h : T = U) :
    (k ≫ (𝟙 A ⊗ₘ (f ≫ eqToHom h))) ≫
        eqToHom (congrArg (fun V : C => A ⊗ V) h).symm = k ≫ (𝟙 A ⊗ₘ f) := by
  cases h
  simp only [eqToHom_refl, Category.comp_id]

/-- Original first/tail object transport commutes with the original retained-final associator. -/
theorem firstAssociate_frame {S A A' B B' D : C} (f : S ⟶ A ⊗ B)
    (hA : A = A') (hB : B = B') :
    (f ⊗ₘ 𝟙 D) ≫ (α_ A B D).hom ≫
        eqToHom (congrArg₂ (· ⊗ ·) hA (congrArg (· ⊗ D) hB)) =
      ((f ≫ eqToHom (congrArg₂ (· ⊗ ·) hA hB)) ⊗ₘ 𝟙 D) ≫ (α_ A' B' D).hom := by
  cases hA
  cases hB
  simp only [eqToHom_refl, Category.comp_id]

/-- Original associator naturality lifts a first/tail interchange through a retained final
object. -/
theorem firstAssociate_interchange {S T A B B' D : C}
    (f : S ⟶ A ⊗ B) (g : B ⟶ B') (h : S ⟶ T) (k : T ⟶ A ⊗ B')
    (hi : f ≫ (𝟙 A ⊗ₘ g) = h ≫ k) :
    (f ⊗ₘ 𝟙 D) ≫ (α_ A B D).hom ≫ (𝟙 A ⊗ₘ (g ⊗ₘ 𝟙 D)) =
      (h ⊗ₘ 𝟙 D) ≫ (k ⊗ₘ 𝟙 D) ≫ (α_ A B' D).hom := by
  have ha : (α_ A B D).hom ≫ (𝟙 A ⊗ₘ (g ⊗ₘ 𝟙 D)) =
      ((𝟙 A ⊗ₘ g) ⊗ₘ 𝟙 D) ≫ (α_ A B' D).hom :=
    (associator_naturality (𝟙 A) g (𝟙 D)).symm
  rw [ha, ← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, hi]
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FirstAssociateFrame

/- Source proof segment: ShiftedLastCompatibility -/
section source_ShiftedLastCompatibility
/-!
# Original final adjacent interchange after first-factor extraction

The equality retains both original adjacent tensor maps, the original
head-tail maps and the actual first/tail target equality transport.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable [BraidedCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The original last adjacent tensor map intertwines the original extraction of the first
factor. -/
theorem headTailIso_shifted_last {n : ℕ} (X : Fin (n + 3) → C) :
    (headTailIso X).hom ≫ (𝟙 (X 0) ⊗ₘ (adjacentIso (Fin.tail X) (Fin.last n)).hom) =
      (adjacentIso X (Fin.last n).succ).hom ≫
        (headTailIso (X ∘ shiftedSwap (Fin.last n))).hom ≫
          eqToHom (shiftedHeadTail_target (Fin.last n) X) := by
  let U := initTwo X
  let A := X 0
  let Q := obj (Fin.tail U)
  let B := X (Fin.last (n + 1)).castSucc
  let D := X (Fin.last (n + 2))
  let Y := X ∘ shiftedSwap (Fin.last n)
  have hS : obj Y = (obj U ⊗ D) ⊗ B := obj_swapLast X
  have hT : Y 0 ⊗ obj (Fin.tail Y) = A ⊗ ((Q ⊗ D) ⊗ B) :=
    shiftedLast_headTail_target X
  have hy : HEq (headTailIso Y).hom (headTailTwoHom U D B) :=
    (heq_of_eq (headTailIso_two_hom Y)).trans
      (headTailTwoHom_heq (initTwo Y) U (Y (Fin.last (n + 1)).castSucc) D
        (Y (Fin.last (n + 2))) B (initTwo_shifted_last X)
        (shifted_last_penultimate X) (shifted_last_last X))
  have hY : eqToHom hS.symm ≫ (headTailIso Y).hom ≫ eqToHom hT =
      headTailTwoHom U D B := shiftedTransportedHom hS hT _ _ hy
  have htail : obj (Fin.tail X ∘ Equiv.swap (Fin.last n).castSucc (Fin.last n).succ) =
      (Q ⊗ D) ⊗ B := obj_swapLast (Fin.tail X)
  have haTail : (adjacentIso (Fin.tail X) (Fin.last n)).hom =
      (swapLastIso Q B D).hom ≫ eqToHom htail.symm :=
    adjacentIso_last_hom (Fin.tail X)
  have haFull : (adjacentIso X (Fin.last n).succ).hom =
      (swapLastIso (obj U) B D).hom ≫ eqToHom hS.symm :=
    adjacentIso_last_hom X
  let hpost := congrArg (fun V : C => A ⊗ V) htail
  have hcore : (headTailIso X).hom ≫ (𝟙 A ⊗ₘ (swapLastIso Q B D).hom) =
      (swapLastIso (obj U) B D).hom ≫ headTailTwoHom U D B := by
    rw [headTailIso_two_hom]
    exact firstPullHom_swap (headTailIso U).hom B D
  have hleft : ((headTailIso X).hom ≫
        (𝟙 A ⊗ₘ (adjacentIso (Fin.tail X) (Fin.last n)).hom)) ≫ eqToHom hpost =
      (headTailIso X).hom ≫ (𝟙 A ⊗ₘ (swapLastIso Q B D).hom) := by
    rw [haTail]
    exact fixedLeft_tensor_postEq_cancel (headTailIso X).hom
      (swapLastIso Q B D).hom htail.symm
  have hright : ((adjacentIso X (Fin.last n).succ).hom ≫ (headTailIso Y).hom ≫
        eqToHom (shiftedHeadTail_target (Fin.last n) X)) ≫ eqToHom hpost =
      (swapLastIso (obj U) B D).hom ≫ headTailTwoHom U D B := by
    rw [haFull]
    have ht : eqToHom (shiftedHeadTail_target (Fin.last n) X) ≫ eqToHom hpost =
        eqToHom hT := by rw [eqToHom_trans]
    simp only [Category.assoc]
    rw [ht, hY]
  apply (cancel_mono (eqToHom hpost)).mp
  exact hleft.trans (hcore.trans hright.symm)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ShiftedLastCompatibility

/- Source proof segment: ShiftedLowerShapes -/
section source_ShiftedLowerShapes
/-!
# Original lower shifted-adjacent input shapes

A shifted transposition below the final slot retains that original
slot and restricts to the same shifted transposition on the original
initial family.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

/-- The original lower shifted transposition restricts through the original initial embedding. -/
theorem shiftedSwap_castSucc {n : ℕ} (i : Fin n) (j : Fin (n + 2)) :
    shiftedSwap i.castSucc j.castSucc = (shiftedSwap i j).castSucc := by
  unfold shiftedSwap
  simpa only [Fin.succ_castSucc] using
    (Fin.castSucc_injective (n + 2)).swap_apply i.succ.castSucc i.succ.succ j

/-- The original lower shifted transposition retains the original final slot. -/
theorem shiftedSwap_castSucc_last {n : ℕ} (i : Fin n) :
    shiftedSwap i.castSucc (Fin.last (n + 2)) = Fin.last (n + 2) := by
  unfold shiftedSwap
  apply Equiv.swap_apply_of_ne_of_ne
  · exact (Fin.castSucc_ne_last i.castSucc.succ).symm
  · simpa only [Fin.succ_castSucc] using (Fin.castSucc_ne_last i.succ.succ).symm

variable {C : Type u}

/-- Original initial families restrict the shifted lower transposition without changing inputs. -/
theorem shiftedFamily_init {n : ℕ} (i : Fin n) (X : Fin (n + 3) → C) :
    Fin.init (n := n + 2) (X ∘ shiftedSwap i.castSucc) =
      Fin.init (n := n + 2) X ∘ shiftedSwap i := by
  funext j
  change X (shiftedSwap i.castSucc j.castSucc) = X (shiftedSwap i j).castSucc
  rw [shiftedSwap_castSucc]

/-- Original lower shifted reindexing retains the original final object. -/
theorem shiftedFamily_castSucc_last {n : ℕ} (i : Fin n) (X : Fin (n + 3) → C) :
    (X ∘ shiftedSwap i.castSucc) (Fin.last (n + 2)) = X (Fin.last (n + 2)) := by
  rw [Function.comp_apply, shiftedSwap_castSucc_last]

variable [Category.{v} C] [MonoidalCategory C]

/-- The original lower shifted tensor has exactly its original initial tensor and retained
final object. -/
theorem shiftedLower_source_eq {n : ℕ} (i : Fin n) (X : Fin (n + 3) → C) :
    obj (X ∘ shiftedSwap i.castSucc) =
      obj (Fin.init X ∘ shiftedSwap i) ⊗ X (Fin.last (n + 2)) := by
  rw [obj_succ]
  change obj (Fin.init (n := n + 2) (X ∘ shiftedSwap i.castSucc)) ⊗
    (X ∘ shiftedSwap i.castSucc) (Fin.last (n + 2)) = _
  rw [shiftedFamily_init, shiftedFamily_castSucc_last]

/-- The lower shifted head-tail target retains the original tail prefix and original final
object. -/
theorem shiftedLower_headTail_target {n : ℕ} (i : Fin n) (X : Fin (n + 3) → C) :
    (X ∘ shiftedSwap i.castSucc) 0 ⊗ obj (Fin.tail (X ∘ shiftedSwap i.castSucc)) =
      X 0 ⊗ (obj (Fin.tail (Fin.init X) ∘ Equiv.swap i.castSucc i.succ) ⊗
        X (Fin.last (n + 2))) := by
  rw [shiftedFamily_zero, shiftedFamily_tail, obj_swapLower]
  rfl

/-- The original lower target is the original head-tail successor of its original initial family. -/
theorem shiftedLower_one_target {n : ℕ} (i : Fin n) (X : Fin (n + 3) → C) :
    (X ∘ shiftedSwap i.castSucc) 0 ⊗ obj (Fin.tail (X ∘ shiftedSwap i.castSucc)) =
      (Fin.init X ∘ shiftedSwap i) 0 ⊗
        (obj (Fin.tail (Fin.init X ∘ shiftedSwap i)) ⊗ X (Fin.last (n + 2))) := by
  change (Fin.init (n := n + 2) (X ∘ shiftedSwap i.castSucc)) 0 ⊗
      (obj (Fin.tail (Fin.init (n := n + 2) (X ∘ shiftedSwap i.castSucc))) ⊗
        (X ∘ shiftedSwap i.castSucc) (Fin.last (n + 2))) = _
  rw [shiftedFamily_init, shiftedFamily_castSucc_last]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ShiftedLowerShapes

/- Source proof segment: ShiftedLowerCompatibility -/
section source_ShiftedLowerCompatibility
/-!
# Original lower adjacent head-tail induction step

Original associator naturality lifts the original adjacent-prefix
interchange past the retained final object. All actual target family
equality maps are retained in the induction step.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The original lower adjacent head-tail interchange lifts through the original final object. -/
theorem headTailIso_shifted_lower_step {n : ℕ} (i : Fin n) (X : Fin (n + 3) → C)
    (hi : (headTailIso (Fin.init X)).hom ≫
        (𝟙 (X 0) ⊗ₘ (adjacentIso (Fin.tail (Fin.init X)) i).hom) =
      (adjacentIso (Fin.init X) i.succ).hom ≫
        (headTailIso (Fin.init X ∘ shiftedSwap i)).hom ≫
          eqToHom (shiftedHeadTail_target i (Fin.init X))) :
    (headTailIso X).hom ≫ (𝟙 (X 0) ⊗ₘ (adjacentIso (Fin.tail X) i.castSucc).hom) =
      (adjacentIso X i.castSucc.succ).hom ≫
        (headTailIso (X ∘ shiftedSwap i.castSucc)).hom ≫
          eqToHom (shiftedHeadTail_target i.castSucc X) := by
  let U := Fin.init (n := n + 2) X
  let V := U ∘ shiftedSwap i
  let Y := X ∘ shiftedSwap i.castSucc
  let A := X 0
  let B := obj (Fin.tail U)
  let B' := obj (Fin.tail U ∘ Equiv.swap i.castSucc i.succ)
  let D := X (Fin.last (n + 2))
  have hS : obj Y = obj V ⊗ D := shiftedLower_source_eq i X
  have hOld : Y 0 ⊗ obj (Fin.tail Y) = V 0 ⊗ (obj (Fin.tail V) ⊗ D) :=
    shiftedLower_one_target i X
  have hA : V 0 = A := shiftedFamily_zero i U
  have hB : obj (Fin.tail V) = B' := congrArg obj (shiftedFamily_tail i U)
  have hF : V 0 ⊗ obj (Fin.tail V) = A ⊗ B' := shiftedHeadTail_target i U
  let hAssoc := congrArg₂ (· ⊗ ·) hA (congrArg (· ⊗ D) hB)
  have hy : HEq (headTailIso Y).hom (headTailOneHom V D) :=
    (heq_of_eq (headTailIso_one_hom Y)).trans
      (headTailOneHom_heq (Fin.init Y) V (Y (Fin.last (n + 2))) D
        (shiftedFamily_init i X) (shiftedFamily_castSucc_last i X))
  have hY : eqToHom hS.symm ≫ (headTailIso Y).hom ≫ eqToHom hOld =
      headTailOneHom V D := shiftedTransportedHom hS hOld _ _ hy
  have hYA : eqToHom hS.symm ≫ (headTailIso Y).hom ≫ eqToHom (hOld.trans hAssoc) =
      (((headTailIso V).hom ≫ eqToHom hF) ⊗ₘ 𝟙 D) ≫ (α_ A B' D).hom := by
    have h0 := congrArg (· ≫ eqToHom hAssoc) hY
    have h1 : eqToHom hS.symm ≫ (headTailIso Y).hom ≫ eqToHom (hOld.trans hAssoc) =
        headTailOneHom V D ≫ eqToHom hAssoc := by
      simpa only [Category.assoc, eqToHom_trans] using h0
    have hf : headTailOneHom V D ≫ eqToHom hAssoc =
        (((headTailIso V).hom ≫ eqToHom hF) ⊗ₘ 𝟙 D) ≫ (α_ A B' D).hom := by
      simpa only [headTailOneHom, Category.assoc] using
        firstAssociate_frame (D := D) (headTailIso V).hom hA hB
    exact h1.trans hf
  have htail : obj (Fin.tail X ∘ Equiv.swap i.castSucc.castSucc i.castSucc.succ) =
      B' ⊗ D := obj_swapLower (Fin.tail X) i
  have haTail : (adjacentIso (Fin.tail X) i.castSucc).hom =
      ((adjacentIso (Fin.tail U) i).hom ⊗ₘ 𝟙 D) ≫ eqToHom htail.symm :=
    adjacentIso_castSucc_hom (Fin.tail X) i
  have haFull : (adjacentIso X i.castSucc.succ).hom =
      ((adjacentIso U i.succ).hom ⊗ₘ 𝟙 D) ≫ eqToHom hS.symm :=
    adjacentIso_castSucc_hom X i.succ
  let hpost := congrArg (fun Q : C => A ⊗ Q) htail
  have hcore : ((headTailIso U).hom ⊗ₘ 𝟙 D) ≫ (α_ A B D).hom ≫
        (𝟙 A ⊗ₘ ((adjacentIso (Fin.tail U) i).hom ⊗ₘ 𝟙 D)) =
      ((adjacentIso U i.succ).hom ⊗ₘ 𝟙 D) ≫
        (((headTailIso V).hom ≫ eqToHom hF) ⊗ₘ 𝟙 D) ≫ (α_ A B' D).hom :=
    firstAssociate_interchange (D := D) (headTailIso U).hom
      (adjacentIso (Fin.tail U) i).hom (adjacentIso U i.succ).hom
      ((headTailIso V).hom ≫ eqToHom hF) hi
  have hleft : ((headTailIso X).hom ≫
        (𝟙 A ⊗ₘ (adjacentIso (Fin.tail X) i.castSucc).hom)) ≫ eqToHom hpost =
      ((headTailIso U).hom ⊗ₘ 𝟙 D) ≫ (α_ A B D).hom ≫
        (𝟙 A ⊗ₘ ((adjacentIso (Fin.tail U) i).hom ⊗ₘ 𝟙 D)) := by
    rw [haTail]
    have hc := fixedLeft_tensor_postEq_cancel (headTailIso X).hom
      ((adjacentIso (Fin.tail U) i).hom ⊗ₘ 𝟙 D) htail.symm
    have hn : (headTailIso X).hom ≫
        (𝟙 A ⊗ₘ ((adjacentIso (Fin.tail U) i).hom ⊗ₘ 𝟙 D)) =
      ((headTailIso U).hom ⊗ₘ 𝟙 D) ≫ (α_ A B D).hom ≫
        (𝟙 A ⊗ₘ ((adjacentIso (Fin.tail U) i).hom ⊗ₘ 𝟙 D)) := by
      exact (congrArg (· ≫ (𝟙 A ⊗ₘ ((adjacentIso (Fin.tail U) i).hom ⊗ₘ 𝟙 D)))
        (headTailIso_one_hom X)).trans
          (Category.assoc ((headTailIso U).hom ⊗ₘ 𝟙 D) (α_ A B D).hom
            (𝟙 A ⊗ₘ ((adjacentIso (Fin.tail U) i).hom ⊗ₘ 𝟙 D)))
    exact hc.trans hn
  have hright : ((adjacentIso X i.castSucc.succ).hom ≫ (headTailIso Y).hom ≫
        eqToHom (shiftedHeadTail_target i.castSucc X)) ≫ eqToHom hpost =
      ((adjacentIso U i.succ).hom ⊗ₘ 𝟙 D) ≫
        (((headTailIso V).hom ≫ eqToHom hF) ⊗ₘ 𝟙 D) ≫ (α_ A B' D).hom := by
    rw [haFull]
    have ht : eqToHom (shiftedHeadTail_target i.castSucc X) ≫ eqToHom hpost =
        eqToHom (hOld.trans hAssoc) := by rw [eqToHom_trans]
    simp only [Category.assoc]
    rw [ht, hYA]
  apply (cancel_mono (eqToHom hpost)).mp
  exact hleft.trans (hcore.trans hright.symm)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ShiftedLowerCompatibility

/- Source proof segment: ShiftedAdjacentCompatibility -/
section source_ShiftedAdjacentCompatibility
/-!
# Original head-tail compatibility with every shifted adjacent tensor map

The proof retains the original binary braiding maps and the original
first/tail target equality transport. Empty generator families and
all heterogeneous finite arities are included.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Every original adjacent tail tensor map intertwines the original first-factor extraction. -/
theorem headTailIso_shifted_adjacent : ∀ {n : ℕ} (i : Fin n) (X : Fin (n + 2) → C),
    (headTailIso X).hom ≫ (𝟙 (X 0) ⊗ₘ (adjacentIso (Fin.tail X) i).hom) =
      (adjacentIso X i.succ).hom ≫ (headTailIso (X ∘ shiftedSwap i)).hom ≫
        eqToHom (shiftedHeadTail_target i X) := by
  intro n
  induction n with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      intro i X
      cases i using Fin.lastCases with
      | last => exact headTailIso_shifted_last X
      | cast j => exact headTailIso_shifted_lower_step j X (ih j (Fin.init X))

/-- The exact transported law retains the original two-map word in heterogeneous form. -/
theorem headTailIso_shifted_adjacent_heq {n : ℕ} (i : Fin n) (X : Fin (n + 2) → C) :
    HEq ((headTailIso X).hom ≫ (𝟙 (X 0) ⊗ₘ (adjacentIso (Fin.tail X) i).hom))
      ((adjacentIso X i.succ).hom ≫ (headTailIso (X ∘ shiftedSwap i)).hom) := by
  have h := headTailIso_shifted_adjacent i X
  have ht : HEq ((adjacentIso X i.succ).hom ≫
        (headTailIso (X ∘ shiftedSwap i)).hom ≫ eqToHom (shiftedHeadTail_target i X))
      ((adjacentIso X i.succ).hom ≫ (headTailIso (X ∘ shiftedSwap i)).hom) :=
    (heq_of_eq (Category.assoc _ _ _).symm).trans (comp_eqToHom_heq _ _)
  exact (heq_of_eq h).trans ht

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ShiftedAdjacentCompatibility

/- Source proof segment: TensorMapTransport -/
section source_TensorMapTransport
/-!
# Transport of original heterogeneous finite tensor maps

Equality of the original arity, input objects and component maps
transports the actual finite tensor map. No map or coherence outcome is
assumed beyond those input equalities.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Equal original arities, objects and components give heterogeneously equal tensor maps. -/
theorem map_heq {m n : ℕ} (h : m = n) {X X' : Fin m → C} {Y Y' : Fin n → C}
    (hX : ∀ i, X i = Y (Fin.cast h i)) (hX' : ∀ i, X' i = Y' (Fin.cast h i))
    (f : X ⟶ X') (g : Y ⟶ Y') (hf : ∀ i, HEq (f i) (g (Fin.cast h i))) :
    HEq (map f) (map g) := by
  subst n
  have hXY : X = Y := funext hX
  have hXY' : X' = Y' := funext hX'
  subst Y
  subst Y'
  have hfg : f = g := funext (fun i => eq_of_heq (hf i))
  subst g
  rfl

/-- Actual binary tensor maps transport along equal original source and target objects. -/
theorem tensorHom_heq {X X' Y Y' A A' B B' : C}
    (hX : X = X') (hY : Y = Y') (hA : A = A') (hB : B = B')
    (f : X ⟶ Y) (g : A ⟶ B) (f' : X' ⟶ Y') (g' : A' ⟶ B')
    (hf : HEq f f') (hg : HEq g g') : HEq (f ⊗ₘ g) (f' ⊗ₘ g') := by
  subst X'
  subst Y'
  subst A'
  subst B'
  have hf' : f = f' := eq_of_heq hf
  have hg' : g = g' := eq_of_heq hg
  subst f'
  subst g'
  rfl

/-- The successor tensor map transports its original initial family and last component. -/
theorem map_succ_heq {n : ℕ} {X X' : Fin (n + 1) → C} {Y Y' : Fin n → C} {A A' : C}
    (hX : Fin.init (n := n) X = Y) (hX' : Fin.init (n := n) X' = Y')
    (hA : X (Fin.last n) = A) (hA' : X' (Fin.last n) = A')
    (f : X ⟶ X') (g : Y ⟶ Y') (a : A ⟶ A')
    (hf : ∀ i, HEq (f i.castSucc) (g i)) (ha : HEq (f (Fin.last n)) a) :
    HEq (map f) (map g ⊗ₘ a) := by
  have hi : HEq (map (fun i : Fin n => f i.castSucc)) (map g) :=
    map_heq rfl (congrFun hX) (congrFun hX') _ g hf
  exact tensorHom_heq (congrArg obj hX) (congrArg obj hX') hA hA' _ _ _ _ hi ha

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_TensorMapTransport

/- Source proof segment: FirstGeneratorCompatibility -/
section source_FirstGeneratorCompatibility
/-!
# Original adjacent tensor maps through the fixed-first extension

The comparison is derived from the original binary head-tail/adjacent
interchange, with its actual target equality transport, and the actual
fixed-first tensor comparison. No compatibility outcome is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Original head-tail conjugation recovers the original tensor map. -/
theorem headTailConjugate_recover {n : ℕ} (X Y : Fin (n + 1) → C)
    (f : (functor C (n + 1)).obj X ⟶ (functor C (n + 1)).obj Y) :
    headTailConjugate X Y ((headTailNatIso n).inv.app X ≫ f ≫
      (headTailNatIso n).hom.app Y) = f :=
  (Iso.homCongr ((headTailNatIso n).app X).symm
    ((headTailNatIso n).app Y).symm).right_inv f

variable [BraidedCategory C]

/-- The original adjacent generator is exactly the actual fixed-first extension of the tail one. -/
theorem tensorGenerator_first_extension {n : ℕ} (i : Fin n) :
    extendFirstHom (tensorGenerator (C := C) i) = tensorGenerator i.succ := by
  apply TensorReindexing.ext (show (extendFirstHom (tensorGenerator (C := C) i)).perm =
      (tensorGenerator (C := C) i.succ).perm from by
    change extendFirstPerm (n + 1) (Equiv.swap i.castSucc i.succ) =
      Equiv.swap i.succ.castSucc i.succ.succ
    exact extendFirstPerm_adjacent i)
  intro X
  let r := tensorGenerator (C := C) i
  let Y := X ∘ shiftedSwap i
  let Y' := familyEquiv (extendFirstPerm (n + 1) r.perm) X
  have hY : Y' = Y := by
    change familyEquiv (extendFirstPerm (n + 1) (Equiv.swap i.castSucc i.succ)) X =
      X ∘ shiftedSwap i
    rw [extendFirstPerm_adjacent]
    change X ∘ (shiftedSwap i).symm = X ∘ shiftedSwap i
    rw [show (shiftedSwap i).symm = shiftedSwap i from Equiv.swap_inv _ _]
  have hTail : ((pull C (n + 1) r.perm ⋙ functor C (n + 1)).obj (Fin.tail X)) =
      obj (Fin.tail X ∘ Equiv.swap i.castSucc i.succ) := by
    change obj (Fin.tail X ∘ (Equiv.swap i.castSucc i.succ).symm) = _
    rw [show (Equiv.swap i.castSucc i.succ).symm = Equiv.swap i.castSucc i.succ from
      Equiv.swap_inv _ _]
  have ht : HEq (𝟙 (X 0) ⊗ₘ r.comparison.hom.app (Fin.tail X))
      (𝟙 (X 0) ⊗ₘ (adjacentIso (Fin.tail X) i).hom) :=
    tensorHom_heq rfl rfl rfl hTail _ _ _ _ HEq.rfl (tensorGenerator_hom_app i (Fin.tail X))
  let d : (functor C (n + 2)).obj X ⟶ (functor C (n + 2)).obj Y :=
    (adjacentIso X i.succ).hom
  let f : (headTailFunctor (C := C) (n + 1)).obj X ⟶
      (headTailFunctor (C := C) (n + 1)).obj Y :=
    (headTailNatIso (n + 1)).inv.app X ≫ d ≫ (headTailNatIso (n + 1)).hom.app Y
  have hc : (𝟙 (X 0) ⊗ₘ (adjacentIso (Fin.tail X) i).hom) =
      (headTailIso X).inv ≫ ((adjacentIso X i.succ).hom ≫
        (headTailIso Y).hom ≫ eqToHom (shiftedHeadTail_target i X)) :=
    (Iso.eq_inv_comp (headTailIso X)).mpr (headTailIso_shifted_adjacent i X)
  have ha : (headTailIso X).inv ≫ ((adjacentIso X i.succ).hom ≫
      (headTailIso Y).hom ≫ eqToHom (shiftedHeadTail_target i X)) =
      f ≫ eqToHom (shiftedHeadTail_target i X) := by
    change (headTailIso X).inv ≫ ((adjacentIso X i.succ).hom ≫
      (headTailIso Y).hom ≫ eqToHom (shiftedHeadTail_target i X)) =
      ((headTailIso X).inv ≫ (adjacentIso X i.succ).hom ≫ (headTailIso Y).hom) ≫
        eqToHom (shiftedHeadTail_target i X)
    exact (congrArg ((headTailIso X).inv ≫ ·)
      (Category.assoc (adjacentIso X i.succ).hom (headTailIso Y).hom
        (eqToHom (shiftedHeadTail_target i X))).symm).trans
      (Category.assoc (headTailIso X).inv
        ((adjacentIso X i.succ).hom ≫ (headTailIso Y).hom)
        (eqToHom (shiftedHeadTail_target i X))).symm
  have hp : HEq ((firstPayload r).hom.app X) f :=
    (firstPayload_hom_heq r X).trans (ht.trans ((heq_of_eq hc).trans
      ((heq_of_eq ha).trans (comp_eqToHom_heq f _))))
  have hconj := headTailConjugate_heq X Y' Y hY ((firstPayload r).hom.app X) f hp
  change HEq ((extendFirstTensor r).comparison.hom.app X)
    ((tensorGenerator (C := C) i.succ).comparison.hom.app X)
  exact (heq_of_eq (extendFirstTensor_hom_conjugate r X)).trans
    (hconj.trans ((heq_of_eq (headTailConjugate_recover X Y d)).trans
      (tensorGenerator_hom_app i.succ X).symm))

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FirstGeneratorCompatibility

/- Source proof segment: FirstPresentationLift -/
section source_FirstPresentationLift
/-!
# Presentation step for the original fixed-first tensor permutation comparison

The arbitrary permutation join follows from the actual adjacent input
maps and their proved shifted binary tensor comparison, using the
original finite permutation presentation.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory TensorReindexing
open Equiv.Perm.AdjacentPresentation

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

private theorem firstPermutation_join
    (hgen : ∀ {n : ℕ} (i : Fin n),
      extendFirstHom (tensorGenerator (C := C) i) = tensorGenerator i.succ) (n : ℕ) :
    (permutationHom (C := C) (n + 1)).comp (extendFirstPerm n) =
      (extendFirstHom (C := C) (n := n)).comp (permutationHom (C := C) n) := by
  cases n with
  | zero =>
      apply MonoidHom.ext
      intro p
      have hp : p = (1 : Equiv.Perm (Fin 0)) := by
        apply Equiv.ext
        intro i
        exact Fin.elim0 i
      rw [hp, map_one, map_one]
  | succ n =>
      apply MonoidHom.eq_of_eqOn_denseM
        (show Submonoid.closure (Set.range (adjacent n)) = ⊤ from
          Equiv.Perm.mclosure_swap_castSucc_succ n)
      rintro _ ⟨i, rfl⟩
      change permutationHom (C := C) (n + 2)
          (extendFirstPerm (n + 1) (Equiv.swap i.castSucc i.succ)) =
        extendFirstHom (permutationHom (C := C) (n + 1) (Equiv.swap i.castSucc i.succ))
      rw [extendFirstPerm_adjacent, permutationHom_adjacent, permutationHom_adjacent]
      exact (hgen i).symm

/-- The actual arbitrary tensor permutation homomorphism matches
the original fixed-first extension. -/
theorem permutationHom_first_extension (n : ℕ) :
    (permutationHom (C := C) (n + 1)).comp (extendFirstPerm n) =
      (extendFirstHom (C := C) (n := n)).comp (permutationHom (C := C) n) :=
  firstPermutation_join (fun i => tensorGenerator_first_extension i) n

/-- Every original finite input permutation has the actual fixed-first tensor comparison. -/
theorem permutationHom_first_extension_apply {n : ℕ} (p : Equiv.Perm (Fin n)) :
    permutationHom (C := C) (n + 1) (extendFirstPerm n p) =
      extendFirstHom (permutationHom (C := C) n p) :=
  congrArg (fun f => f p) (permutationHom_first_extension (C := C) n)

/-- Retain the actual source permutation in the original constructed tensor-action record. -/
noncomputable def firstPermutationRecord {n : ℕ} (p : Equiv.Perm (Fin n)) :
    TensorReindexing C n :=
  rebaseRecord (permutationHom (C := C) n p) p (permutationHom_perm n p)

/-- The actual arbitrary permutation natural comparison has its
original fixed-first construction. -/
theorem permutationNatIso_first_extension {n : ℕ} (p : Equiv.Perm (Fin n)) :
    permutationNatIso (C := C) (extendFirstPerm n p) =
      firstComparison (firstPermutationRecord p) := by
  let r := firstPermutationRecord (C := C) p
  have hr : r = permutationHom (C := C) n p :=
    rebaseRecord_eq (permutationHom (C := C) n p) p (permutationHom_perm n p)
  have he : extendFirstTensor r = permutationHom (C := C) (n + 1) (extendFirstPerm n p) :=
    (congrArg (extendFirstHom (C := C) (n := n)) hr).trans
      (permutationHom_first_extension_apply (C := C) p).symm
  change rebase (permutationHom (C := C) (n + 1) (extendFirstPerm n p))
    (extendFirstPerm n p) (permutationHom_perm (n + 1) (extendFirstPerm n p)) = _
  exact (rebase_congr he.symm (extendFirstPerm n p)
    (permutationHom_perm (n + 1) (extendFirstPerm n p)) rfl).trans
      (rebase_refl (extendFirstTensor r))

/-- The actual arbitrary permutation retains the original first
identity, tail maps and transports. -/
theorem permutationIso_first_extension_hom {n : ℕ} (p : Equiv.Perm (Fin n))
    (X : Fin (n + 1) → C) :
    (permutationIso (C := C) (extendFirstPerm n p) X).hom =
      (headTailIso X).hom ≫ (𝟙 (X 0) ⊗ₘ (permutationIso p (Fin.tail X)).hom) ≫
        eqToHom (Functor.congr_obj (firstTarget_eq p).symm X) ≫
          (headTailIso (familyEquiv (extendFirstPerm n p) X)).inv := by
  change (permutationNatIso (C := C) (extendFirstPerm n p)).hom.app X = _
  rw [permutationNatIso_first_extension]
  exact extendFirstTensor_hom_app (firstPermutationRecord (C := C) p) X

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FirstPresentationLift

/- Source proof segment: ComparisonAlong -/
section source_ComparisonAlong
/-!
# Whole-record transport of original tensor comparisons

An original natural reindexing record can be compared with a named
target family. Equality and composition are proved for whole records
before applying the factory to the actual permutation homomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {n : ℕ}

/-- The original natural tensor comparison with its actual target family equality transport. -/
def comparisonAlong (r : TensorReindexing C n) (X Y : Fin n → C)
    (h : familyEquiv r.perm X = Y) : obj X ≅ obj Y :=
  (show obj X ≅ obj (familyEquiv r.perm X) from r.comparison.app X) ≪≫
    eqToIso (congrArg obj h)

/-- The original comparison retains its exact forward map and target transport. -/
theorem comparisonAlong_hom (r : TensorReindexing C n) (X Y : Fin n → C)
    (h : familyEquiv r.perm X = Y) :
    (comparisonAlong r X Y h).hom =
      r.comparison.hom.app X ≫ eqToHom (congrArg obj h) := rfl

/-- Equal whole records retain the same original named-target comparison. -/
theorem comparisonAlong_congr {r s : TensorReindexing C n} (hrs : r = s)
    (X Y : Fin n → C) (hr : familyEquiv r.perm X = Y)
    (hs : familyEquiv s.perm X = Y) :
    comparisonAlong r X Y hr = comparisonAlong s X Y hs := by
  cases hrs
  rfl

/-- Consecutive original named target families determine the actual product target family. -/
theorem comparisonAlong_mul_family (r s : TensorReindexing C n) (X Y Z : Fin n → C)
    (hs : familyEquiv s.perm X = Y) (hr : familyEquiv r.perm Y = Z) :
    familyEquiv (r * s).perm X = Z := by
  change familyEquiv (r.perm * s.perm) X = Z
  exact (congrArg (fun e => e X) (familyEquiv_mul r.perm s.perm)).trans
    ((congrArg (familyEquiv r.perm) hs).trans hr)

set_option backward.isDefEq.respectTransparency false in
/-- The original named-target comparison preserves actual whole-record composition. -/
theorem comparisonAlong_trans (r s : TensorReindexing C n) (X Y Z : Fin n → C)
    (hs : familyEquiv s.perm X = Y) (hr : familyEquiv r.perm Y = Z) :
    comparisonAlong s X Y hs ≪≫ comparisonAlong r Y Z hr =
      comparisonAlong (r * s) X Z (comparisonAlong_mul_family r s X Y Z hs hr) := by
  cases hs
  cases hr
  apply Iso.ext
  simp only [comparisonAlong, Iso.trans_hom, eqToIso.hom, eqToHom_refl,
    Category.comp_id]
  exact (mul_hom_app r s X).symm

variable [SymmetricCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The actual rebased record retains its original permutation natural comparison. -/
theorem firstPermutationRecord_hom_app (p : Equiv.Perm (Fin n)) (X : Fin n → C) :
    (firstPermutationRecord (C := C) p).comparison.hom.app X =
      (permutationIso p X).hom := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual constructed permutation record retains its original finite-bijection map. -/
theorem comparisonAlong_actual (p : Equiv.Perm (Fin n)) (X Y : Fin n → C)
    (hXY : ∀ i, X i = Y (p i)) (hFamily : X ∘ p.symm = Y) :
    comparisonAlong (firstPermutationRecord p) X Y hFamily =
      isoEquiv p (fun i => eqToIso (hXY i)) := by
  apply Iso.ext
  change (permutationIso p X).hom ≫ eqToHom (congrArg obj hFamily) = _
  exact (isoEquiv_eqToIso_hom p X Y hXY hFamily).symm

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ComparisonAlong

/- Source proof segment: ActualTensorRightBlockExtension -/
section source_ActualTensorRightBlockExtension
/-!
# Original tensor permutations inside a block after a retained prefix

Each original prefix factor is retained by the constructed fixed-first
tensor extension. Arbitrary finite input permutations act through the
proved original generator compatibility, not an assumed block action.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory
open TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The actual input permutation extended through a prescribed original first-factor history. -/
noncomputable def extendPermPrefix {n : ℕ} (p : Equiv.Perm (Fin n)) :
    (m : ℕ) → Equiv.Perm (Fin (n + m))
  | 0 => p
  | m + 1 => extendFirstPerm (n + m) (extendPermPrefix p m)

/-- The actual tensor comparison extended through a prescribed original first-factor history. -/
noncomputable def extendTensorPrefix {n : ℕ} (r : TensorReindexing C n) :
    (m : ℕ) → TensorReindexing C (n + m)
  | 0 => r
  | m + 1 => extendFirstHom (extendTensorPrefix r m)

/-- Arbitrary original finite tensor permutations retain every original prefix factor. -/
theorem permutationHom_extendPrefix {n : ℕ} (p : Equiv.Perm (Fin n)) :
    ∀ m : ℕ, permutationHom (C := C) (n + m) (extendPermPrefix p m) =
      extendTensorPrefix (permutationHom n p) m
  | 0 => rfl
  | m + 1 =>
      (permutationHom_first_extension_apply (extendPermPrefix p m)).trans
        (congrArg extendFirstHom (permutationHom_extendPrefix p m))

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ActualTensorRightBlockExtension

/- Source proof segment: OrderedAppend -/
section source_OrderedAppend
/-!
# Splitting heterogeneous ordered tensor blocks

The block comparison is built from the original right unitor and
associators. Its inputs may all be different objects.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

omit [Category.{v} C] [MonoidalCategory C] in
/-- Appending an empty family leaves the original ordered family. -/
theorem append_nil {m : ℕ} (X : Fin m → C) (Y : Fin 0 → C) :
    Fin.append X Y = X := by
  funext i
  change Fin.append X Y (Fin.castAdd 0 i) = X i
  exact Fin.append_left X Y i

omit [Category.{v} C] [MonoidalCategory C] in
/-- Removing the last slot of an appended positive block removes its last slot. -/
theorem init_append {m n : ℕ} (X : Fin m → C) (Y : Fin (n + 1) → C) :
    Fin.init (n := m + n) (Fin.append (m := m) (n := n + 1) X Y) =
      Fin.append (m := m) (n := n) X (Fin.init (n := n) Y) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · dsimp only [Fin.init]
    have h : Fin.castSucc (Fin.castAdd n i) = Fin.castAdd (n + 1) i := rfl
    rw [h, Fin.append_left, Fin.append_left]
  · dsimp only [Fin.init]
    have h : Fin.castSucc (Fin.natAdd m i) = Fin.natAdd m i.castSucc := rfl
    rw [h, Fin.append_right, Fin.append_right]
    rfl

omit [Category.{v} C] [MonoidalCategory C] in
/-- The last object of an appended positive block is the last object of that block. -/
theorem last_append {m n : ℕ} (X : Fin m → C) (Y : Fin (n + 1) → C) :
    Fin.append (m := m) (n := n + 1) X Y (Fin.last (m + n)) = Y (Fin.last n) := by
  have h : Fin.last (m + n) = Fin.natAdd m (Fin.last n) := rfl
  rw [h, Fin.append_right]

/-- Successor reduction of the tensor of appended blocks. -/
theorem append_step {m n : ℕ} (X : Fin m → C) (Y : Fin (n + 1) → C) :
    obj (Fin.append (m := m) (n := n + 1) X Y) =
      obj (Fin.append (m := m) (n := n) X (Fin.init Y)) ⊗ Y (Fin.last n) := by
  rw [obj_succ]
  change obj (Fin.init (n := m + n) (Fin.append (m := m) (n := n + 1) X Y)) ⊗
    Fin.append (m := m) (n := n + 1) X Y (Fin.last (m + n)) = _
  rw [init_append, last_append]

/-- Split the tensor of two consecutive blocks into the tensor of the
two block tensors. The maps use the original binary monoidal coherence. -/
def appendIso {m : ℕ} (X : Fin m → C) :
    {n : ℕ} → (Y : Fin n → C) → obj (Fin.append X Y) ≅ obj X ⊗ obj Y
  | 0, Y => eqToIso (congrArg obj (append_nil X Y)) ≪≫ (ρ_ (obj X)).symm
  | n + 1, Y => eqToIso (append_step X Y) ≪≫
      tensorIso (appendIso X (Fin.init Y)) (Iso.refl (Y (Fin.last n))) ≪≫
      α_ (obj X) (obj (Fin.init Y)) (Y (Fin.last n))

/-- The block split in empty second degree is the original right unitor inverse. -/
theorem appendIso_zero_hom {m : ℕ} (X : Fin m → C) (Y : Fin 0 → C) :
    (appendIso X Y).hom =
      eqToHom (congrArg obj (append_nil X Y)) ≫ (ρ_ (obj X)).inv := rfl

/-- Successor computation of the original block split. -/
theorem appendIso_succ_hom {m n : ℕ} (X : Fin m → C) (Y : Fin (n + 1) → C) :
    (appendIso X Y).hom = eqToHom (append_step X Y) ≫
      ((appendIso X (Fin.init Y)).hom ⊗ₘ 𝟙 (Y (Fin.last n))) ≫
      (α_ (obj X) (obj (Fin.init Y)) (Y (Fin.last n))).hom := rfl

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedAppend

/- Source proof segment: ActualTensorRightBlockShapes -/
section source_ActualTensorRightBlockShapes
/-!
# Original finite input shapes under a retained tensor prefix

The constructed fixed-first permutation history retains every original
prefix index and applies the original permutation to the final block.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory
open TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- Repeated fixed-first extension retains the original final block's shifted indices. -/
theorem extendPermPrefix_addNat {n : ℕ} (p : Equiv.Perm (Fin n)) :
    ∀ (m : ℕ) (i : Fin n), extendPermPrefix p m (Fin.addNat i m) = Fin.addNat (p i) m
  | 0, i => by
      have h : Fin.addNat i 0 = i := Fin.ext (Nat.add_zero _)
      rw [h]
      rfl
  | m + 1, i => by
      have h : Fin.addNat i (m + 1) = (Fin.addNat i m).succ := rfl
      rw [h, extendPermPrefix, extendFirstPerm_succ, extendPermPrefix_addNat]
      rfl

/-- Repeated fixed-first extension fixes every original prefix position. -/
theorem extendPermPrefix_prefix {n : ℕ} (p : Equiv.Perm (Fin n)) :
    ∀ (m : ℕ) (i : Fin m),
      extendPermPrefix p m (Fin.cast (Nat.add_comm m n) (Fin.castAdd n i)) =
        Fin.cast (Nat.add_comm m n) (Fin.castAdd n i)
  | 0, i => i.elim0
  | m + 1, i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · have h : Fin.cast (Nat.add_comm (m + 1) n) (Fin.castAdd n (0 : Fin (m + 1))) =
            (0 : Fin (n + (m + 1))) := Fin.ext rfl
        rw [h, extendPermPrefix, extendFirstPerm_zero]
      · have h : Fin.cast (Nat.add_comm (m + 1) n) (Fin.castAdd n j.succ) =
            (Fin.cast (Nat.add_comm m n) (Fin.castAdd n j)).succ := Fin.ext rfl
        rw [h, extendPermPrefix, extendFirstPerm_succ, extendPermPrefix_prefix]

omit [SymmetricCategory C] in
/-- The original fixed-first history retains its original input permutation field. -/
theorem extendTensorPrefix_perm {n : ℕ} (r : TensorReindexing C n) :
    ∀ m : ℕ, (extendTensorPrefix r m).perm = extendPermPrefix r.perm m
  | 0 => rfl
  | m + 1 => congrArg (extendFirstPerm (n + m)) (extendTensorPrefix_perm r m)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ActualTensorRightBlockShapes

/- Source proof segment: ActualTensorRightBlockPermutation -/
section source_ActualTensorRightBlockPermutation
/-!
# Original right-block permutation on literal concatenated input counts

The actual add-commutation arity equivalence is retained when the
fixed-first permutation history is expressed on the original
`Fin (m+n)` concatenated family.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

/-- The original right-block permutation expressed on the literal concatenated input type. -/
noncomputable def rightBlockPerm (m n : ℕ) (p : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (m + n)) :=
  (finCongr (Nat.add_comm m n)).trans
    ((extendPermPrefix p m).trans (finCongr (Nat.add_comm n m)))

/-- The original right-block permutation fixes every literal first-block input. -/
theorem rightBlockPerm_castAdd {m n : ℕ} (p : Equiv.Perm (Fin n)) (i : Fin m) :
    rightBlockPerm m n p (Fin.castAdd n i) = Fin.castAdd n i := by
  have h := extendPermPrefix_prefix p m i
  change Fin.cast (Nat.add_comm n m)
    (extendPermPrefix p m (Fin.cast (Nat.add_comm m n) (Fin.castAdd n i))) = _
  rw [h]
  exact Fin.ext rfl

/-- The original right-block permutation acts on every literal final-block input by its
original map. -/
theorem rightBlockPerm_natAdd {m n : ℕ} (p : Equiv.Perm (Fin n)) (i : Fin n) :
    rightBlockPerm m n p (Fin.natAdd m i) = Fin.natAdd m (p i) := by
  have hi : Fin.cast (Nat.add_comm m n) (Fin.natAdd m i) = Fin.addNat i m := by
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_addNat]
    exact Nat.add_comm m i.val
  change Fin.cast (Nat.add_comm n m)
    (extendPermPrefix p m (Fin.cast (Nat.add_comm m n) (Fin.natAdd m i))) = _
  rw [hi, extendPermPrefix_addNat]
  apply Fin.ext
  simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_addNat]
  exact Nat.add_comm (p i).val m

/-- Literal right-block permutation is the actual block-sum bijection. -/
theorem rightBlockPerm_eq_sum {m n : ℕ} (p : Equiv.Perm (Fin n)) :
    rightBlockPerm m n p = finSumFinEquiv.symm.trans
      ((Equiv.sumCongr (Equiv.refl (Fin m)) p).trans finSumFinEquiv) := by
  apply Equiv.ext
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [rightBlockPerm_castAdd]
    simp only [Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply]
    rfl
  · rw [rightBlockPerm_natAdd]
    simp only [Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply]
    rfl

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ActualTensorRightBlockPermutation

/- Source proof segment: AppendFunctor -/
section source_AppendFunctor
/-!
# Actual ordered family append as a functor of both blocks

The functor appends the original finite object families and their
independent original component morphisms. Both finite blocks may be empty.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C]

/-- Combine two original constant-category families over their disjoint finite input sum. -/
def blockSumFunctor (C : Type u) [Category.{v} C] (m n : ℕ) :
    (Fin m → C) × (Fin n → C) ⥤ (Fin m ⊕ Fin n → C) :=
  Functor.pi' (fun i : Fin m ⊕ Fin n => match i with
    | Sum.inl j => CategoryTheory.Prod.fst _ _ ⋙ Pi.eval (fun _ : Fin m => C) j
    | Sum.inr j => CategoryTheory.Prod.snd _ _ ⋙ Pi.eval (fun _ : Fin n => C) j)

/-- Reindex the actual disjoint block families through the original ordered finite-sum bijection. -/
def appendFamilyBase (C : Type u) [Category.{v} C] (m n : ℕ) :
    (Fin m → C) × (Fin n → C) ⥤ (Fin (m + n) → C) :=
  blockSumFunctor C m n ⋙
    Pi.comap (fun _ : Fin m ⊕ Fin n => C) finSumFinEquiv.symm

/-- The functor retains the original ordered appended object family. -/
theorem appendFamilyBase_obj {m n : ℕ} (X : Fin m → C) (Y : Fin n → C) :
    (appendFamilyBase C m n).obj (X, Y) = Fin.append X Y := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · change (blockSumFunctor C m n).obj (X, Y)
      (finSumFinEquiv.symm (Fin.castAdd n i)) =
      Fin.append X Y (Fin.castAdd n i)
    rw [finSumFinEquiv_symm_apply_castAdd, Fin.append_left]
    rfl
  · change (blockSumFunctor C m n).obj (X, Y)
      (finSumFinEquiv.symm (Fin.natAdd m i)) =
      Fin.append X Y (Fin.natAdd m i)
    rw [finSumFinEquiv_symm_apply_natAdd, Fin.append_right]
    rfl

/-- Every original component of the first block is retained by the append map. -/
theorem appendFamilyBase_map_left {m n : ℕ} {X X' : Fin m → C} {Y Y' : Fin n → C}
    (f : X ⟶ X') (g : Y ⟶ Y') (i : Fin m) :
    HEq ((appendFamilyBase C m n).map (show (X, Y) ⟶ (X', Y') from (f, g))
      (Fin.castAdd n i)) (f i) := by
  change HEq
    ((blockSumFunctor C m n).map (show (X, Y) ⟶ (X', Y') from (f, g))
      (finSumFinEquiv.symm (Fin.castAdd n i))) (f i)
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

/-- Every original component of the second block is retained by the append map. -/
theorem appendFamilyBase_map_right {m n : ℕ} {X X' : Fin m → C} {Y Y' : Fin n → C}
    (f : X ⟶ X') (g : Y ⟶ Y') (i : Fin n) :
    HEq ((appendFamilyBase C m n).map (show (X, Y) ⟶ (X', Y') from (f, g))
      (Fin.natAdd m i)) (g i) := by
  change HEq
    ((blockSumFunctor C m n).map (show (X, Y) ⟶ (X', Y') from (f, g))
      (finSumFinEquiv.symm (Fin.natAdd m i))) (g i)
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

/-- The complete actual append functor with the original `Fin.append` object formula. -/
def appendFamilyFunctor (C : Type u) [Category.{v} C] (m n : ℕ) :
    (Fin m → C) × (Fin n → C) ⥤ (Fin (m + n) → C) :=
  (appendFamilyBase C m n).copyObj (fun P => Fin.append P.1 P.2)
    (fun P => eqToIso (appendFamilyBase_obj P.1 P.2))

/-- The append functor is definitionally the original appended object family. -/
@[simp] theorem appendFamilyFunctor_obj {m n : ℕ} (X : Fin m → C) (Y : Fin n → C) :
    (appendFamilyFunctor C m n).obj (X, Y) = Fin.append X Y := rfl

/-- The actual independent block maps retain their original family equality transports. -/
theorem appendFamilyFunctor_map {m n : ℕ} {X X' : Fin m → C} {Y Y' : Fin n → C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (appendFamilyFunctor C m n).map (show (X, Y) ⟶ (X', Y') from (f, g)) =
      eqToHom (appendFamilyBase_obj X Y).symm ≫
        (appendFamilyBase C m n).map (show (X, Y) ⟶ (X', Y') from (f, g)) ≫
        eqToHom (appendFamilyBase_obj X' Y') := rfl

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_AppendFunctor

/- Source proof segment: AppendMapReadback -/
section source_AppendMapReadback
/-!
# Original appended component maps and successor transport

The copied append functor retains the original independent input maps.
Its tensor map commutes with the exact original empty/successor object
transports used to define `appendIso`.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C]

/-- Object-copy transports do not change the original appended component morphism. -/
theorem appendFamilyFunctor_map_pointwise {m n : ℕ} {X X' : Fin m → C} {Y Y' : Fin n → C}
    (f : X ⟶ X') (g : Y ⟶ Y') (i : Fin (m + n)) :
    HEq ((appendFamilyFunctor C m n).map (show (X, Y) ⟶ (X', Y') from (f, g)) i)
      ((appendFamilyBase C m n).map (show (X, Y) ⟶ (X', Y') from (f, g)) i) := by
  change HEq
    ((Pi.eval (fun _ : Fin (m + n) => C) i).map
        (eqToHom (appendFamilyBase_obj X Y).symm) ≫
      (Pi.eval (fun _ : Fin (m + n) => C) i).map
        ((appendFamilyBase C m n).map (show (X, Y) ⟶ (X', Y') from (f, g))) ≫
        (Pi.eval (fun _ : Fin (m + n) => C) i).map (eqToHom (appendFamilyBase_obj X' Y')))
    ((Pi.eval (fun _ : Fin (m + n) => C) i).map
      ((appendFamilyBase C m n).map (show (X, Y) ⟶ (X', Y') from (f, g))))
  rw [eqToHom_map, eqToHom_map]
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

/-- The actual appended map retains every original first-block component. -/
theorem appendFamilyFunctor_map_left {m n : ℕ} {X X' : Fin m → C} {Y Y' : Fin n → C}
    (f : X ⟶ X') (g : Y ⟶ Y') (i : Fin m) :
    HEq ((appendFamilyFunctor C m n).map (show (X, Y) ⟶ (X', Y') from (f, g))
      (Fin.castAdd n i)) (f i) :=
  (appendFamilyFunctor_map_pointwise f g _).trans (appendFamilyBase_map_left f g i)

/-- The actual appended map retains every original second-block component. -/
theorem appendFamilyFunctor_map_right {m n : ℕ} {X X' : Fin m → C} {Y Y' : Fin n → C}
    (f : X ⟶ X') (g : Y ⟶ Y') (i : Fin n) :
    HEq ((appendFamilyFunctor C m n).map (show (X, Y) ⟶ (X', Y') from (f, g))
      (Fin.natAdd m i)) (g i) :=
  (appendFamilyFunctor_map_pointwise f g _).trans (appendFamilyBase_map_right f g i)

variable [MonoidalCategory C]

/-- The actual appended empty-block tensor map is the original first-block tensor map. -/
theorem appendMap_zero_heq {m : ℕ} {X X' : Fin m → C} {Y Y' : Fin 0 → C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    HEq (map ((appendFamilyFunctor C m 0).map
      (show (X, Y) ⟶ (X', Y') from (f, g)))) (map f) :=
  map_heq rfl (congrFun (append_nil X Y)) (congrFun (append_nil X' Y')) _ f
    (fun i => appendFamilyFunctor_map_left f g i)

/-- The actual appended successor tensor map retains its initial append and final component. -/
theorem appendMap_succ_heq {m n : ℕ} {X X' : Fin m → C} {Y Y' : Fin (n + 1) → C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    HEq (map ((appendFamilyFunctor C m (n + 1)).map
        (show (X, Y) ⟶ (X', Y') from (f, g))))
      (map ((appendFamilyFunctor C m n).map
          (show (X, Fin.init (n := n) Y) ⟶ (X', Fin.init (n := n) Y') from
            (f, fun i => g i.castSucc))) ⊗ₘ g (Fin.last n)) := by
  let g0 : Fin.init (n := n) Y ⟶ Fin.init (n := n) Y' := fun i => g i.castSucc
  let a := (appendFamilyFunctor C m (n + 1)).map
    (show (X, Y) ⟶ (X', Y') from (f, g))
  let b := (appendFamilyFunctor C m n).map
    (show (X, Fin.init (n := n) Y) ⟶ (X', Fin.init (n := n) Y') from (f, g0))
  have hi : ∀ i : Fin (m + n), HEq (a i.castSucc) (b i) := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · have he : (Fin.castAdd n i).castSucc = Fin.castAdd (n + 1) i := rfl
      rw [he]
      exact (appendFamilyFunctor_map_left f g i).trans
        (appendFamilyFunctor_map_left f g0 i).symm
    · have he : (Fin.natAdd m i).castSucc = Fin.natAdd m i.castSucc := rfl
      rw [he]
      exact (appendFamilyFunctor_map_right f g i.castSucc).trans
        (appendFamilyFunctor_map_right f g0 i).symm
  have hl : HEq (a (Fin.last (m + n))) (g (Fin.last n)) := by
    have he : Fin.last (m + n) = Fin.natAdd m (Fin.last n) := rfl
    rw [he]
    exact appendFamilyFunctor_map_right f g (Fin.last n)
  exact map_succ_heq (init_append X Y) (init_append X' Y') (last_append X Y)
    (last_append X' Y') a b (g (Fin.last n)) hi hl

omit [MonoidalCategory C] in
/-- Heterogeneously equal original maps commute with their exact
source/target equality transports. -/
theorem equality_square {A B A' B' : C} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B') (hfg : HEq f g) :
    f ≫ eqToHom hB = eqToHom hA ≫ g := by
  have h := (conj_eqToHom_iff_heq f g hA hB).mpr hfg
  rw [h]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_AppendMapReadback

/- Source proof segment: AppendNaturality -/
section source_AppendNaturality
/-!
# Naturality of the original heterogeneous ordered block split

Both block families and all component maps vary independently. The
comparison uses the original right unitor, associator and equality
transports, including the empty second block.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

private theorem splitStep_naturality {L L' A A' B B' D D' : C}
    (u : L ⟶ L') (f : A ⟶ A') (g : B ⟶ B') (h : D ⟶ D')
    (a : L ⟶ A ⊗ B) (a' : L' ⟶ A' ⊗ B')
    (hnat : u ≫ a' = a ≫ (f ⊗ₘ g)) :
    (u ⊗ₘ h) ≫ (a' ⊗ₘ 𝟙 D') ≫ (α_ A' B' D').hom =
      (a ⊗ₘ 𝟙 D) ≫ (α_ A B D).hom ≫ (f ⊗ₘ (g ⊗ₘ h)) := by
  calc
    (u ⊗ₘ h) ≫ (a' ⊗ₘ 𝟙 D') ≫ (α_ A' B' D').hom =
        ((u ≫ a') ⊗ₘ h) ≫ (α_ A' B' D').hom := by
      rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]
    _ = ((a ≫ (f ⊗ₘ g)) ⊗ₘ h) ≫ (α_ A' B' D').hom := by rw [hnat]
    _ = (a ⊗ₘ 𝟙 D) ≫ ((f ⊗ₘ g) ⊗ₘ h) ≫ (α_ A' B' D').hom := by
      rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
    _ = (a ⊗ₘ 𝟙 D) ≫ (α_ A B D).hom ≫ (f ⊗ₘ (g ⊗ₘ h)) := by
      rw [associator_naturality]

/-- The original block split is natural in both independent families and all component maps. -/
theorem appendIso_naturality : ∀ {m n : ℕ} {X X' : Fin m → C} {Y Y' : Fin n → C}
    (f : X ⟶ X') (g : Y ⟶ Y'),
    map ((appendFamilyFunctor C m n).map
        (show (X, Y) ⟶ (X', Y') from (f, g))) ≫ (appendIso X' Y').hom =
      (appendIso X Y).hom ≫ (map f ⊗ₘ map g) := by
  intro m n
  induction n with
  | zero =>
      intro X X' Y Y' f g
      let u : obj (Fin.append X Y) ⟶ obj (Fin.append X' Y') :=
        map ((appendFamilyFunctor C m 0).map
        (show (X, Y) ⟶ (X', Y') from (f, g)))
      have hs := equality_square (congrArg obj (append_nil X Y))
        (congrArg obj (append_nil X' Y')) u (map f) (appendMap_zero_heq f g)
      have hr : map f ≫ (ρ_ (obj X')).inv =
          (ρ_ (obj X)).inv ≫ (map f ⊗ₘ 𝟙 (𝟙_ C)) := by
        simpa only [tensorHom_id] using rightUnitor_inv_naturality (map f)
      rw [appendIso_zero_hom, appendIso_zero_hom]
      change u ≫ (eqToHom (congrArg obj (append_nil X' Y')) ≫ (ρ_ (obj X')).inv) =
        (eqToHom (congrArg obj (append_nil X Y)) ≫ (ρ_ (obj X)).inv) ≫
          (map f ⊗ₘ 𝟙 (𝟙_ C))
      rw [← Category.assoc, hs, Category.assoc, hr, Category.assoc]
  | succ n ih =>
      intro X X' Y Y' f g
      let g0 : Fin.init (n := n) Y ⟶ Fin.init (n := n) Y' := fun i => g i.castSucc
      let u : obj (Fin.append X Y) ⟶ obj (Fin.append X' Y') :=
        map ((appendFamilyFunctor C m (n + 1)).map
        (show (X, Y) ⟶ (X', Y') from (f, g)))
      let u0 : obj (Fin.append X (Fin.init (n := n) Y)) ⟶
          obj (Fin.append X' (Fin.init (n := n) Y')) :=
        map ((appendFamilyFunctor C m n).map
        (show (X, Fin.init (n := n) Y) ⟶ (X', Fin.init (n := n) Y') from (f, g0)))
      have hs := equality_square (append_step X Y) (append_step X' Y') u
        (u0 ⊗ₘ g (Fin.last n)) (appendMap_succ_heq f g)
      have ht := splitStep_naturality u0 (map f) (map g0) (g (Fin.last n))
        (appendIso X (Fin.init Y)).hom (appendIso X' (Fin.init Y')).hom (ih f g0)
      rw [appendIso_succ_hom, appendIso_succ_hom]
      change u ≫ (eqToHom (append_step X' Y') ≫
          ((appendIso X' (Fin.init Y')).hom ⊗ₘ 𝟙 (Y' (Fin.last n))) ≫
            (α_ (obj X') (obj (Fin.init Y')) (Y' (Fin.last n))).hom) =
        (eqToHom (append_step X Y) ≫ ((appendIso X (Fin.init Y)).hom ⊗ₘ
          𝟙 (Y (Fin.last n))) ≫ (α_ (obj X) (obj (Fin.init Y)) (Y (Fin.last n))).hom) ≫
            (map f ⊗ₘ (map g0 ⊗ₘ g (Fin.last n)))
      rw [← Category.assoc u, hs]
      simpa only [Category.assoc] using congrArg (eqToHom (append_step X Y) ≫ ·) ht

/-- The actual tensor functor of the original ordered appended families. -/
def appendTensorFunctor (C : Type u) [Category.{v} C] [MonoidalCategory C] (m n : ℕ) :
    (Fin m → C) × (Fin n → C) ⥤ C := appendFamilyFunctor C m n ⋙ functor C (m + n)

/-- The original binary tensor of the two independent finite tensor functors. -/
def blockTensorFunctor (C : Type u) [Category.{v} C] [MonoidalCategory C] (m n : ℕ) :
    (Fin m → C) × (Fin n → C) ⥤ C := (functor C m).prod (functor C n) ⋙ tensor C

/-- The complete natural ordered block split with the original component isomorphisms. -/
def appendNatIso (C : Type u) [Category.{v} C] [MonoidalCategory C] (m n : ℕ) :
    appendTensorFunctor C m n ≅ blockTensorFunctor C m n :=
  NatIso.ofComponents (fun P => appendIso P.1 P.2) (by
    intro P Q f
    exact appendIso_naturality f.1 f.2)

/-- The natural block split evaluates to the original ordered tensor split map. -/
theorem appendNatIso_hom_app {m n : ℕ} (X : Fin m → C) (Y : Fin n → C) :
    (appendNatIso C m n).hom.app (X, Y) = (appendIso X Y).hom := rfl

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_AppendNaturality

/- Source proof segment: AppendEquality -/
section source_AppendEquality
/-!
# Original arity transports for heterogeneous ordered block splits

The transport of three-block append uses the original `Fin.append_assoc`
and the original arity equality. Successor transport is tensoring that
same equality map with the identity of the actual final object.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Equal original block arities and objects transport the original block-split hom. -/
theorem appendIso_hom_heq {m m' n n' : ℕ} (hm : m = m') (hn : n = n')
    (X : Fin m → C) (X' : Fin m' → C) (Y : Fin n → C) (Y' : Fin n' → C)
    (hX : ∀ i, X i = X' (Fin.cast hm i)) (hY : ∀ i, Y i = Y' (Fin.cast hn i)) :
    HEq (appendIso X Y).hom (appendIso X' Y').hom := by
  subst m'
  subst n'
  have hx : X = X' := funext hX
  have hy : Y = Y' := funext hY
  subst X'
  subst Y'
  rfl

/-- The original three-block finite append associator equality on tensor objects. -/
theorem appendAssociator_obj_eq {m n p : ℕ}
    (X : Fin m → C) (Y : Fin n → C) (Z : Fin p → C) :
    obj (Fin.append (Fin.append X Y) Z) = obj (Fin.append X (Fin.append Y Z)) :=
  obj_congr (Nat.add_assoc m n p) _ _ (congrFun (Fin.append_assoc X Y Z))

/-- The exact tensor-object transport induced by the original finite append associator. -/
def appendAssociator {m n p : ℕ} (X : Fin m → C) (Y : Fin n → C) (Z : Fin p → C) :
    obj (Fin.append (Fin.append X Y) Z) ≅ obj (Fin.append X (Fin.append Y Z)) :=
  eqToIso (appendAssociator_obj_eq X Y Z)

/-- The right-associated positive triple append has its original initial triple and final object. -/
theorem rightTriple_step {m n p : ℕ}
    (X : Fin m → C) (Y : Fin n → C) (Z : Fin (p + 1) → C) :
    obj (Fin.append X (Fin.append Y Z)) =
      obj (Fin.append X (Fin.append Y (Fin.init (n := p) Z))) ⊗ Z (Fin.last p) := by
  rw [append_step (m := m) (n := n + p) X (Fin.append (m := n) (n := p + 1) Y Z),
    init_append (m := n) (n := p) Y Z, last_append (m := n) (n := p) Y Z]

/-- Successor three-block transport tensors the original arity transport with the final identity. -/
theorem appendAssociator_succ_transport {m n p : ℕ}
    (X : Fin m → C) (Y : Fin n → C) (Z : Fin (p + 1) → C) :
    eqToHom (append_step (Fin.append X Y) Z).symm ≫ (appendAssociator X Y Z).hom ≫
        eqToHom (rightTriple_step X Y Z) =
      (appendAssociator X Y (Fin.init (n := p) Z)).hom ⊗ₘ 𝟙 (Z (Fin.last p)) := by
  simp only [appendAssociator, eqToIso.hom, tensorHom_id, eqToHom_whiskerRight,
    eqToHom_trans]

/-- Transport of the original second block is its exact source and tensor-target equality square. -/
theorem appendIso_transport_second {m n : ℕ} (X : Fin m → C) (Y Y' : Fin n → C)
    (hY : Y = Y') :
    (appendIso X Y).hom ≫ (𝟙 (obj X) ⊗ₘ eqToHom (congrArg obj hY)) =
      eqToHom (congrArg (fun Z : Fin n → C => obj (Fin.append X Z)) hY) ≫
        (appendIso X Y').hom := by
  cases hY
  simp only [eqToHom_refl, id_tensorHom_id, Category.comp_id, Category.id_comp]

/-- Equality of the right-associated empty final append retains the original two-block object. -/
theorem rightTriple_zero {m n : ℕ} (X : Fin m → C) (Y : Fin n → C) (Z : Fin 0 → C) :
    obj (Fin.append X (Fin.append Y Z)) = obj (Fin.append X Y) :=
  congrArg (fun V : Fin n → C => obj (Fin.append X V)) (append_nil Y Z)

/-- The original zero-degree three-block arity transport is identity
after its exact endpoint maps. -/
theorem appendAssociator_zero_transport {m n : ℕ}
    (X : Fin m → C) (Y : Fin n → C) (Z : Fin 0 → C) :
    eqToHom (congrArg obj (append_nil (Fin.append X Y) Z)).symm ≫
        (appendAssociator X Y Z).hom ≫ eqToHom (rightTriple_zero X Y Z) =
      𝟙 (obj (Fin.append X Y)) := by
  simp only [appendAssociator, eqToIso.hom, eqToHom_trans]
  rfl

/-- The generic original one-step block split, with its specified actual source equality. -/
def successorSplitIso {m n : ℕ} (X : Fin m → C) (Y : Fin n → C) (V S : C)
    (hS : S = obj (Fin.append X Y) ⊗ V) : S ≅ obj X ⊗ (obj Y ⊗ V) :=
  eqToIso hS ≪≫ tensorIso (appendIso X Y) (Iso.refl V) ≪≫ α_ (obj X) (obj Y) V

/-- The whole one-step split transports both its original initial block and final object. -/
theorem successorSplitIso_hom_heq {m n : ℕ} (X : Fin m → C) (Y Y' : Fin n → C)
    (V V' S : C) (hY : Y = Y') (hV : V = V')
    (hS : S = obj (Fin.append X Y) ⊗ V) (hS' : S = obj (Fin.append X Y') ⊗ V') :
    HEq (successorSplitIso X Y V S hS).hom (successorSplitIso X Y' V' S hS').hom := by
  cases hY
  cases hV
  rfl

/-- The original positive block split is exactly the specified generic one-step construction. -/
theorem appendIso_succ_eq {m n : ℕ} (X : Fin m → C) (Y : Fin (n + 1) → C) :
    (appendIso X Y).hom =
      (successorSplitIso X (Fin.init (n := n) Y) (Y (Fin.last n))
        (obj (Fin.append X Y)) (append_step X Y)).hom := rfl

/-- The original nested positive outer split retains the actual second-block successor transport. -/
theorem appendOuter_succ_transport {m n p : ℕ}
    (X : Fin m → C) (Y : Fin n → C) (Z : Fin (p + 1) → C) :
    (appendIso X (Fin.append Y Z)).hom ≫ (𝟙 (obj X) ⊗ₘ eqToHom (append_step Y Z)) =
      (successorSplitIso X (Fin.append Y (Fin.init (n := p) Z)) (Z (Fin.last p))
        (obj (Fin.append X (Fin.append Y Z))) (rightTriple_step X Y Z)).hom := by
  have hh : HEq (appendIso X (Fin.append Y Z)).hom
      (successorSplitIso X (Fin.append Y (Fin.init (n := p) Z)) (Z (Fin.last p))
        (obj (Fin.append X (Fin.append Y Z))) (rightTriple_step X Y Z)).hom := by
    rw [appendIso_succ_eq]
    exact successorSplitIso_hom_heq X _ _ _ _ _ (init_append Y Z) (last_append Y Z) _ _
  have hs := (conj_eqToHom_iff_heq (appendIso X (Fin.append Y Z)).hom
    (successorSplitIso X (Fin.append Y (Fin.init (n := p) Z)) (Z (Fin.last p))
      (obj (Fin.append X (Fin.append Y Z))) (rightTriple_step X Y Z)).hom rfl
    (congrArg (fun V : C => obj X ⊗ V) (append_step Y Z))).mpr hh
  rw [hs]
  rw [id_tensorHom, whiskerLeft_eqToHom]
  simp only [eqToHom_refl, Category.id_comp, Category.assoc, eqToHom_trans, Category.comp_id]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_AppendEquality

/- Source proof segment: BinaryAppendCoherence -/
section source_BinaryAppendCoherence
/-!
# Binary associator coherence for the ordered append induction

This is the original four-object pentagon and associator naturality
applied to the arbitrary heterogeneous block maps of an induction step.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The original binary pentagon carries one associative split to its successor split. -/
theorem splitStep_associativity {L R P Q A B D W : C}
    (e : L ⟶ R) (a : R ⟶ A ⊗ Q) (b : Q ⟶ B ⊗ D)
    (c : L ⟶ P ⊗ D) (d : P ⟶ A ⊗ B)
    (h : e ≫ a ≫ (𝟙 A ⊗ₘ b) = c ≫ (d ⊗ₘ 𝟙 D) ≫ (α_ A B D).hom) :
    (e ⊗ₘ 𝟙 W) ≫ (a ⊗ₘ 𝟙 W) ≫ (α_ A Q W).hom ≫
        (𝟙 A ⊗ₘ (b ⊗ₘ 𝟙 W)) ≫ (𝟙 A ⊗ₘ (α_ B D W).hom) =
      (c ⊗ₘ 𝟙 W) ≫ (α_ P D W).hom ≫
        (d ⊗ₘ 𝟙 (D ⊗ W)) ≫ (α_ A B (D ⊗ W)).hom := by
  have hb : (α_ A Q W).hom ≫ (𝟙 A ⊗ₘ (b ⊗ₘ 𝟙 W)) =
      ((𝟙 A ⊗ₘ b) ⊗ₘ 𝟙 W) ≫ (α_ A (B ⊗ D) W).hom :=
    (associator_naturality (𝟙 A) b (𝟙 W)).symm
  have hp : ((α_ A B D).hom ⊗ₘ 𝟙 W) ≫ (α_ A (B ⊗ D) W).hom ≫
      (𝟙 A ⊗ₘ (α_ B D W).hom) =
    (α_ (A ⊗ B) D W).hom ≫ (α_ A B (D ⊗ W)).hom := by
    simpa only [tensorHom_id, id_tensorHom] using pentagon A B D W
  have hd : ((d ⊗ₘ 𝟙 D) ⊗ₘ 𝟙 W) ≫ (α_ (A ⊗ B) D W).hom =
      (α_ P D W).hom ≫ (d ⊗ₘ 𝟙 (D ⊗ W)) := by
    simpa only [id_tensorHom_id] using associator_naturality d (𝟙 D) (𝟙 W)
  calc
    (e ⊗ₘ 𝟙 W) ≫ (a ⊗ₘ 𝟙 W) ≫ (α_ A Q W).hom ≫
        (𝟙 A ⊗ₘ (b ⊗ₘ 𝟙 W)) ≫ (𝟙 A ⊗ₘ (α_ B D W).hom) =
      ((e ≫ a ≫ (𝟙 A ⊗ₘ b)) ⊗ₘ 𝟙 W) ≫
        (α_ A (B ⊗ D) W).hom ≫ (𝟙 A ⊗ₘ (α_ B D W).hom) := by
      slice_lhs 3 4 => rw [hb]
      simp only [tensorHom_id, comp_whiskerRight, Category.assoc]
    _ = ((c ≫ (d ⊗ₘ 𝟙 D) ≫ (α_ A B D).hom) ⊗ₘ 𝟙 W) ≫
        (α_ A (B ⊗ D) W).hom ≫ (𝟙 A ⊗ₘ (α_ B D W).hom) := by rw [h]
    _ = (c ⊗ₘ 𝟙 W) ≫ ((d ⊗ₘ 𝟙 D) ⊗ₘ 𝟙 W) ≫
        ((α_ A B D).hom ⊗ₘ 𝟙 W) ≫ (α_ A (B ⊗ D) W).hom ≫
          (𝟙 A ⊗ₘ (α_ B D W).hom) := by
      simp only [tensorHom_id, comp_whiskerRight, Category.assoc]
    _ = (c ⊗ₘ 𝟙 W) ≫ ((d ⊗ₘ 𝟙 D) ⊗ₘ 𝟙 W) ≫
        (α_ (A ⊗ B) D W).hom ≫ (α_ A B (D ⊗ W)).hom := by
      slice_lhs 3 5 => rw [hp]
    _ = (c ⊗ₘ 𝟙 W) ≫ (α_ P D W).hom ≫
        (d ⊗ₘ 𝟙 (D ⊗ W)) ≫ (α_ A B (D ⊗ W)).hom := by
      slice_lhs 2 3 => rw [hd]
      simp only [Category.assoc]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_BinaryAppendCoherence

/- Source proof segment: AppendAssociativity -/
section source_AppendAssociativity
/-!
# Associativity of the original heterogeneous ordered block splits

Both three-block routes retain the original finite append arity map.
The proof uses the original zero-degree unitors and the original binary
four-object pentagon at every positive final degree.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Split the last two blocks after applying the actual original three-block arity transport. -/
def appendAssocLeft {m n p : ℕ} (X : Fin m → C) (Y : Fin n → C) (Z : Fin p → C) :
    obj (Fin.append (Fin.append X Y) Z) ⟶ obj X ⊗ (obj Y ⊗ obj Z) :=
  (appendAssociator X Y Z).hom ≫ (appendIso X (Fin.append Y Z)).hom ≫
    (𝟙 (obj X) ⊗ₘ (appendIso Y Z).hom)

/-- Split the first two blocks and apply the original binary associator. -/
def appendAssocRight {m n p : ℕ} (X : Fin m → C) (Y : Fin n → C) (Z : Fin p → C) :
    obj (Fin.append (Fin.append X Y) Z) ⟶ obj X ⊗ (obj Y ⊗ obj Z) :=
  (appendIso (Fin.append X Y) Z).hom ≫ ((appendIso X Y).hom ⊗ₘ 𝟙 (obj Z)) ≫
    (α_ (obj X) (obj Y) (obj Z)).hom

private theorem rightUnit_split_coherence {S A B : C} (d : S ⟶ A ⊗ B) :
    d ≫ (𝟙 A ⊗ₘ (ρ_ B).inv) =
      (ρ_ S).inv ≫ (d ⊗ₘ 𝟙 (𝟙_ C)) ≫ (α_ A B (𝟙_ C)).hom := by
  have h : (ρ_ S).inv ≫ (d ⊗ₘ 𝟙 (𝟙_ C)) = d ≫ (ρ_ (A ⊗ B)).inv := by
    simpa only [tensorHom_id] using (rightUnitor_inv_naturality d).symm
  rw [← Category.assoc, h, rightUnitor_tensor_inv]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, id_tensorHom]

private theorem appendAssocLeft_zero {m n : ℕ}
    (X : Fin m → C) (Y : Fin n → C) (Z : Fin 0 → C) :
    eqToHom (congrArg obj (append_nil (Fin.append X Y) Z)).symm ≫
        appendAssocLeft X Y Z = (appendIso X Y).hom ≫ (𝟙 (obj X) ⊗ₘ (ρ_ (obj Y)).inv) := by
  unfold appendAssocLeft
  change eqToHom (congrArg obj (append_nil (Fin.append X Y) Z)).symm ≫
      (appendAssociator X Y Z).hom ≫ (appendIso X (Fin.append Y Z)).hom ≫
        (𝟙 (obj X) ⊗ₘ (eqToHom (congrArg obj (append_nil Y Z)) ≫ (ρ_ (obj Y)).inv)) = _
  simp only [id_tensorHom, whiskerLeft_comp]
  have ho := appendIso_transport_second X (Fin.append Y Z) Y (append_nil Y Z)
  simp only [id_tensorHom] at ho
  slice_lhs 3 4 => rw [ho]
  slice_lhs 1 3 => rw [appendAssociator_zero_transport X Y Z]
  simp only [Category.id_comp]

private theorem appendAssocRight_zero {m n : ℕ}
    (X : Fin m → C) (Y : Fin n → C) (Z : Fin 0 → C) :
    eqToHom (congrArg obj (append_nil (Fin.append X Y) Z)).symm ≫
        appendAssocRight X Y Z =
      (ρ_ (obj (Fin.append X Y))).inv ≫ ((appendIso X Y).hom ⊗ₘ 𝟙 (𝟙_ C)) ≫
        (α_ (obj X) (obj Y) (𝟙_ C)).hom := by
  unfold appendAssocRight
  change eqToHom (congrArg obj (append_nil (Fin.append X Y) Z)).symm ≫
      ((eqToHom (congrArg obj (append_nil (Fin.append X Y) Z)) ≫
        (ρ_ (obj (Fin.append X Y))).inv) ≫ ((appendIso X Y).hom ⊗ₘ 𝟙 (𝟙_ C)) ≫
          (α_ (obj X) (obj Y) (𝟙_ C)).hom) = _
  simpa only [eqToIso.inv, eqToIso.hom, Category.assoc] using
    Iso.inv_hom_id_assoc (eqToIso (congrArg obj (append_nil (Fin.append X Y) Z)))
      ((ρ_ (obj (Fin.append X Y))).inv ≫ ((appendIso X Y).hom ⊗ₘ 𝟙 (𝟙_ C)) ≫
        (α_ (obj X) (obj Y) (𝟙_ C)).hom)

private theorem appendAssocLeft_succ {m n p : ℕ}
    (X : Fin m → C) (Y : Fin n → C) (Z : Fin (p + 1) → C) :
    eqToHom (append_step (Fin.append X Y) Z).symm ≫ appendAssocLeft X Y Z =
      ((appendAssociator X Y (Fin.init (n := p) Z)).hom ⊗ₘ 𝟙 (Z (Fin.last p))) ≫
        ((appendIso X (Fin.append Y (Fin.init (n := p) Z))).hom ⊗ₘ 𝟙 (Z (Fin.last p))) ≫
          (α_ (obj X) (obj (Fin.append Y (Fin.init (n := p) Z))) (Z (Fin.last p))).hom ≫
            (𝟙 (obj X) ⊗ₘ ((appendIso Y (Fin.init (n := p) Z)).hom ⊗ₘ
              𝟙 (Z (Fin.last p)))) ≫
              (𝟙 (obj X) ⊗ₘ (α_ (obj Y) (obj (Fin.init (n := p) Z)) (Z (Fin.last p))).hom) := by
  unfold appendAssocLeft
  change eqToHom (append_step (Fin.append X Y) Z).symm ≫
      (appendAssociator X Y Z).hom ≫ (appendIso X (Fin.append Y Z)).hom ≫
        (𝟙 (obj X) ⊗ₘ (eqToHom (append_step Y Z) ≫
          ((appendIso Y (Fin.init (n := p) Z)).hom ⊗ₘ 𝟙 (Z (Fin.last p))) ≫
            (α_ (obj Y) (obj (Fin.init (n := p) Z)) (Z (Fin.last p))).hom)) = _
  simp only [id_tensorHom, whiskerLeft_comp]
  have ho := appendOuter_succ_transport X Y Z
  simp only [id_tensorHom] at ho
  slice_lhs 3 4 => rw [ho]
  simp only [successorSplitIso, Iso.trans_hom, eqToIso.hom, tensorIso_hom, Iso.refl_hom,
    Category.assoc]
  slice_lhs 1 3 => rw [appendAssociator_succ_transport X Y Z]
  simp only [Category.assoc]

private theorem appendAssocRight_succ {m n p : ℕ}
    (X : Fin m → C) (Y : Fin n → C) (Z : Fin (p + 1) → C) :
    eqToHom (append_step (Fin.append X Y) Z).symm ≫ appendAssocRight X Y Z =
      ((appendIso (Fin.append X Y) (Fin.init (n := p) Z)).hom ⊗ₘ 𝟙 (Z (Fin.last p))) ≫
        (α_ (obj (Fin.append X Y)) (obj (Fin.init (n := p) Z)) (Z (Fin.last p))).hom ≫
          ((appendIso X Y).hom ⊗ₘ 𝟙 (obj (Fin.init (n := p) Z) ⊗ Z (Fin.last p))) ≫
            (α_ (obj X) (obj Y) (obj (Fin.init (n := p) Z) ⊗ Z (Fin.last p))).hom := by
  unfold appendAssocRight
  change eqToHom (append_step (Fin.append X Y) Z).symm ≫
      ((eqToHom (append_step (Fin.append X Y) Z) ≫
        ((appendIso (Fin.append X Y) (Fin.init (n := p) Z)).hom ⊗ₘ 𝟙 (Z (Fin.last p))) ≫
          (α_ (obj (Fin.append X Y)) (obj (Fin.init (n := p) Z)) (Z (Fin.last p))).hom) ≫
            ((appendIso X Y).hom ⊗ₘ 𝟙 (obj (Fin.init (n := p) Z) ⊗ Z (Fin.last p))) ≫
              (α_ (obj X) (obj Y) (obj (Fin.init (n := p) Z) ⊗ Z (Fin.last p))).hom) = _
  simpa only [eqToIso.inv, eqToIso.hom, Category.assoc] using
    Iso.inv_hom_id_assoc (eqToIso (append_step (Fin.append X Y) Z))
      (((appendIso (Fin.append X Y) (Fin.init (n := p) Z)).hom ⊗ₘ 𝟙 (Z (Fin.last p))) ≫
        (α_ (obj (Fin.append X Y)) (obj (Fin.init (n := p) Z)) (Z (Fin.last p))).hom ≫
          ((appendIso X Y).hom ⊗ₘ 𝟙 (obj (Fin.init (n := p) Z) ⊗ Z (Fin.last p))) ≫
            (α_ (obj X) (obj Y) (obj (Fin.init (n := p) Z) ⊗ Z (Fin.last p))).hom)

/-- Both original heterogeneous three-block split routes agree at every finite arity. -/
theorem appendSplit_associativity : ∀ {m n p : ℕ}
    (X : Fin m → C) (Y : Fin n → C) (Z : Fin p → C),
      appendAssocLeft X Y Z = appendAssocRight X Y Z := by
  intro m n p
  induction p with
  | zero =>
      intro X Y Z
      apply (cancel_epi (eqToHom (congrArg obj (append_nil (Fin.append X Y) Z)).symm)).mp
      exact (appendAssocLeft_zero X Y Z).trans
        ((rightUnit_split_coherence (appendIso X Y).hom).trans (appendAssocRight_zero X Y Z).symm)
  | succ p ih =>
      intro X Y Z
      apply (cancel_epi (eqToHom (append_step (Fin.append X Y) Z).symm)).mp
      have hb := splitStep_associativity (W := Z (Fin.last p))
        (appendAssociator X Y (Fin.init (n := p) Z)).hom
        (appendIso X (Fin.append Y (Fin.init (n := p) Z))).hom
        (appendIso Y (Fin.init (n := p) Z)).hom
        (appendIso (Fin.append X Y) (Fin.init (n := p) Z)).hom
        (appendIso X Y).hom (ih X Y (Fin.init (n := p) Z))
      exact (appendAssocLeft_succ X Y Z).trans (hb.trans (appendAssocRight_succ X Y Z).symm)

/-- The original finite append arity map and original binary associator give the full split law. -/
theorem appendIso_assoc {m n p : ℕ} (X : Fin m → C) (Y : Fin n → C) (Z : Fin p → C) :
    (appendAssociator X Y Z).hom ≫ (appendIso X (Fin.append Y Z)).hom ≫
        (𝟙 (obj X) ⊗ₘ (appendIso Y Z).hom) =
      (appendIso (Fin.append X Y) Z).hom ≫ ((appendIso X Y).hom ⊗ₘ 𝟙 (obj Z)) ≫
        (α_ (obj X) (obj Y) (obj Z)).hom :=
  appendSplit_associativity X Y Z

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_AppendAssociativity

/- Source proof segment: AppendUnit -/
section source_AppendUnit
/-!
# Original empty-block unit coherence of ordered tensor append

Both unit maps are the original binary unitors, with the actual
finite-family equality and arity transports retained.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The original empty first block append induces its actual arity/object equality. -/
theorem appendLeftUnit_obj_eq {n : ℕ} (X : Fin 0 → C) (Y : Fin n → C) :
    obj (Fin.append X Y) = obj Y :=
  obj_congr (Nat.zero_add n) _ _ (congrFun (Fin.append_left_nil X Y rfl))

private theorem leftUnit_split_step {A B W : C} (a : A ⟶ 𝟙_ C ⊗ B) :
    (a ⊗ₘ 𝟙 W) ≫ (α_ (𝟙_ C) B W).hom ≫ (λ_ (B ⊗ W)).hom =
      (a ≫ (λ_ B).hom) ⊗ₘ 𝟙 W := by
  rw [leftUnitor_tensor_hom]
  simp only [Iso.hom_inv_id_assoc]
  rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]

/-- The actual empty first block split is the original left unitor inverse with arity transport. -/
theorem appendIso_empty_left : ∀ {n : ℕ} (X : Fin 0 → C) (Y : Fin n → C),
    (appendIso X Y).hom ≫ (λ_ (obj Y)).hom = eqToHom (appendLeftUnit_obj_eq X Y) := by
  intro n
  induction n with
  | zero =>
      intro X Y
      rw [appendIso_zero_hom]
      change (𝟙 (𝟙_ C) ≫ (ρ_ (𝟙_ C)).inv) ≫ (λ_ (𝟙_ C)).hom = 𝟙 (𝟙_ C)
      rw [Category.id_comp, unitors_equal, Iso.inv_hom_id]
  | succ n ih =>
      intro X Y
      let a : obj (Fin.append X (Fin.init (n := n) Y)) ⟶ 𝟙_ C ⊗ obj (Fin.init (n := n) Y) :=
        (appendIso X (Fin.init (n := n) Y)).hom
      have hi : a ≫ (λ_ (obj (Fin.init (n := n) Y))).hom =
          eqToHom (appendLeftUnit_obj_eq X (Fin.init (n := n) Y)) := ih X (Fin.init Y)
      change (eqToHom (append_step X Y) ≫ (a ⊗ₘ
          𝟙 (Y (Fin.last n))) ≫ (α_ (𝟙_ C) (obj (Fin.init Y)) (Y (Fin.last n))).hom) ≫
          (λ_ (obj (Fin.init Y) ⊗ Y (Fin.last n))).hom = _
      simp only [Category.assoc]
      rw [leftUnit_split_step, hi]
      simp only [tensorHom_id, eqToHom_whiskerRight, eqToHom_trans]
      rfl

/-- The actual empty second block split is the original right unitor
inverse with object transport. -/
theorem appendIso_empty_right {m : ℕ} (X : Fin m → C) (Y : Fin 0 → C) :
    (appendIso X Y).hom ≫ (ρ_ (obj X)).hom = eqToHom (congrArg obj (append_nil X Y)) := by
  change (eqToHom (congrArg obj (append_nil X Y)) ≫ (ρ_ (obj X)).inv) ≫
    (ρ_ (obj X)).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_AppendUnit

/- Source proof segment: OrderedAppendCoherence -/
section source_OrderedAppendCoherence
/-!
# Full original heterogeneous ordered append coherence

The original ordered block split is natural in both independent
families, associative through the original arity map and binary
associator, and coherent with both original empty-block unitors.
-/
end source_OrderedAppendCoherence

/- Source proof segment: RightPrefixAppendComparison -/
section source_RightPrefixAppendComparison
/-!
# Original right-block tensor comparison through a retained prefix

The literal concatenated input type is transported by its actual
add-commutation bijection before the fixed-first tensor history is
applied. The original append and head-tail maps remain explicit.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory
open TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The original literal appended family transported to the actual fixed-first input count. -/
def prefixHistoryFamily {m n : ℕ} (X : Fin m → C) (Y : Fin n → C) : Fin (n + m) → C :=
  Fin.append X Y ∘ Fin.cast (Nat.add_comm n m)

/-- The actual finite tensor map from the original literal append carrier to its
retained-prefix history. -/
noncomputable def prefixHistorySourceIso {m n : ℕ} (X : Fin m → C) (Y : Fin n → C) :
    obj (Fin.append X Y) ≅ obj (prefixHistoryFamily X Y) :=
  congrIso (Nat.add_comm m n) (Fin.append X Y) (prefixHistoryFamily X Y) (fun i => by
    rfl)

omit [SymmetricCategory C] in
/-- The original retained-prefix history reindexes precisely the right block of its original
family. -/
theorem prefixHistory_reindex {m n : ℕ} (r : TensorReindexing C n)
    (X : Fin m → C) (Y : Fin n → C) :
    familyEquiv (extendTensorPrefix r m).perm (prefixHistoryFamily X Y) =
      prefixHistoryFamily X (familyEquiv r.perm Y) := by
  have hLiteral : Fin.append X Y ∘ (rightBlockPerm m n r.perm).symm =
      Fin.append X (familyEquiv r.perm Y) := by
    have hleft (j : Fin m) : (rightBlockPerm m n r.perm).symm (Fin.castAdd n j) =
        Fin.castAdd n j := by
      apply (rightBlockPerm m n r.perm).injective
      rw [Equiv.apply_symm_apply, rightBlockPerm_castAdd]
    have hright (j : Fin n) : (rightBlockPerm m n r.perm).symm (Fin.natAdd m j) =
        Fin.natAdd m (r.perm.symm j) := by
      apply (rightBlockPerm m n r.perm).injective
      rw [Equiv.apply_symm_apply, rightBlockPerm_natAdd, Equiv.apply_symm_apply]
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · change Fin.append X Y ((rightBlockPerm m n r.perm).symm (Fin.castAdd n j)) = _
      rw [hleft, Fin.append_left, Fin.append_left]
    · change Fin.append X Y ((rightBlockPerm m n r.perm).symm (Fin.natAdd m j)) = _
      rw [hright, Fin.append_right, Fin.append_right]
      rfl
  funext i
  rw [familyEquiv_apply, extendTensorPrefix_perm]
  have h := congrFun hLiteral (Fin.cast (Nat.add_comm n m) i)
  exact h

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_RightPrefixAppendComparison

/- Source proof segment: PrefixHistoryAppendIso -/
section source_PrefixHistoryAppendIso
/-!
# Original append comparison on its actual retained-prefix count
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Original append split after its actual add-commutation source-count transport. -/
noncomputable def prefixHistoryAppendIso {m n : ℕ} (X : Fin m → C) (Y : Fin n → C) :
    obj (prefixHistoryFamily X Y) ≅ obj X ⊗ obj Y :=
  (prefixHistorySourceIso X Y).symm ≪≫ appendIso X Y

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_PrefixHistoryAppendIso

/- Source proof segment: HeadTailAppendCoherence -/
section source_HeadTailAppendCoherence
/-!
# Original head-tail and append tensor coherence

Separating the first input and splitting the final original block
give the same original binary associator route as splitting the whole
first block and separating its original head.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

omit [Category.{v} C] [MonoidalCategory C] in
/-- The literal transported append history keeps its original first object. -/
theorem prefixHistory_head {m n : ℕ} (X : Fin (m + 1) → C) (Y : Fin n → C) :
    prefixHistoryFamily X Y 0 = X 0 := by
  unfold prefixHistoryFamily
  have h : Fin.cast (Nat.add_comm n (m + 1)) (0 : Fin (n + (m + 1))) =
      Fin.castAdd n (0 : Fin (m + 1)) := Fin.ext rfl
  rw [Function.comp_apply, h, Fin.append_left]

omit [Category.{v} C] [MonoidalCategory C] in
/-- The literal transported append history keeps the original tail block sequence. -/
theorem prefixHistory_tail {m n : ℕ} (X : Fin (m + 1) → C) (Y : Fin n → C) :
    Fin.tail (n := n + m) (prefixHistoryFamily (m := m + 1) (n := n) X Y) =
      prefixHistoryFamily (m := m) (n := n) (Fin.tail X) Y := by
  funext i
  unfold prefixHistoryFamily
  change Fin.append X Y (Fin.cast (Nat.add_comm n (m + 1)) i.succ) =
    Fin.append (Fin.tail X) Y (Fin.cast (Nat.add_comm n m) i)
  let j := Fin.cast (Nat.add_comm n m) i
  have hcount : m + n + 1 = m + 1 + n := by omega
  have hi : Fin.cast (Nat.add_comm n (m + 1)) i.succ =
      Fin.cast hcount j.succ := Fin.ext rfl
  rw [hi]
  change Fin.append X Y (Fin.cast hcount j.succ) = Fin.append (Fin.tail X) Y j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · have hk : Fin.cast hcount (Fin.castAdd n k).succ =
        Fin.castAdd n k.succ := Fin.ext rfl
    rw [hk, Fin.append_left, Fin.append_left]
    rfl
  · have hk : Fin.cast hcount (Fin.natAdd m k).succ =
        Fin.natAdd (m + 1) k := by
      apply Fin.ext
      simp only [Fin.val_cast, Fin.val_succ, Fin.val_natAdd]
      omega
    rw [hk, Fin.append_right, Fin.append_right]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_HeadTailAppendCoherence

/- Source proof segment: HeadTailAppendMapCoherence -/
section source_HeadTailAppendMapCoherence
/-!
# Original tensor coherence of head-tail and append maps

The two original binary tensor routes separate the first object and
split the right block, with their actual finite input-count transports.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The original head-tail map is the original singleton-block append split followed by its
unitor. -/
theorem headTail_eq_singleton_append : ∀ {m : ℕ} (X : Fin (m + 1) → C),
    HEq (headTailIso X).hom
      ((appendIso (fun _ : Fin 1 => X 0) (Fin.tail X)).hom ≫
        ((singletonIso (fun _ : Fin 1 => X 0)).hom ⊗ₘ 𝟙 (obj (Fin.tail X)))) := by
  intro m
  induction m with
  | zero =>
      intro X
      rw [headTailIso_zero_hom, appendIso_zero_hom]
      have h : (λ_ (X 0)).hom ≫ (ρ_ (X 0)).inv =
          (ρ_ (𝟙_ C ⊗ X 0)).inv ≫ ((λ_ (X 0)).hom ⊗ₘ 𝟙 (𝟙_ C)) := by
        simpa only [tensorHom_id] using rightUnitor_inv_naturality (λ_ (X 0)).hom
      have hs : HEq
          ((eqToHom (congrArg obj (append_nil (fun _ : Fin 1 => X 0) (Fin.tail X))) ≫
            (ρ_ (𝟙_ C ⊗ X 0)).inv) ≫ ((λ_ (X 0)).hom ⊗ₘ 𝟙 (𝟙_ C)))
          ((ρ_ (𝟙_ C ⊗ X 0)).inv ≫ ((λ_ (X 0)).hom ⊗ₘ 𝟙 (𝟙_ C))) := by
        simp only [Category.assoc]
        exact eqToHom_comp_heq _ _
      exact (heq_of_eq h).trans hs.symm
  | succ m ih =>
      intro X
      have h := ih (Fin.init X)
      dsimp only [headTailIso]
      simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
        eqToIso.hom, eqToHom_refl, Category.comp_id]
      rw [appendIso_succ_hom]
      have hsrc : obj (Fin.init X) =
          obj (Fin.append (fun _ : Fin 1 => X 0) (Fin.tail (Fin.init X))) := by
        have hx := Fin.cons_self_tail (Fin.init X)
        have ha := Fin.append_left_eq_cons (fun _ : Fin 1 => X 0) (Fin.tail (Fin.init X))
        have hc : m + 1 = 1 + m := Nat.add_comm m 1
        exact obj_congr hc (Fin.init X)
          (Fin.append (fun _ : Fin 1 => X 0) (Fin.tail (Fin.init X))) (fun i => by
            have hi := congrFun ha (Fin.cast hc i)
            change Fin.append (fun _ : Fin 1 => X 0) (Fin.tail (Fin.init X)) (Fin.cast hc i) =
              Fin.cons ((Fin.init X) 0) (Fin.tail (Fin.init X))
                (Fin.cast (Nat.add_comm 1 m) (Fin.cast hc i)) at hi
            rw [hx] at hi
            have hcast : Fin.cast (Nat.add_comm 1 m) (Fin.cast hc i) = i := Fin.ext rfl
            rw [hcast] at hi
            exact hi.symm)
      have hs := tensorMapBoundary_heq
        (D := X (Fin.last (m + 1))) (E := X (Fin.last (m + 1)))
        (D' := X (Fin.last (m + 1))) (E' := X (Fin.last (m + 1)))
        hsrc rfl rfl rfl h (HEq.rfl (a := 𝟙 (X (Fin.last (m + 1)))))
      have hn := associator_naturality (singletonIso (fun _ : Fin 1 => X 0)).hom
        (𝟙 (obj (Fin.tail (Fin.init X)))) (𝟙 (X (Fin.last (m + 1))))
      simp only [id_tensorHom_id] at hn
      have hfactor :
          (((appendIso (fun _ : Fin 1 => X 0) (Fin.tail (Fin.init X))).hom ≫
            ((singletonIso (fun _ : Fin 1 => X 0)).hom ⊗ₘ
              𝟙 (obj (Fin.tail (Fin.init X))))) ⊗ₘ 𝟙 (X (Fin.last (m + 1)))) ≫
            (α_ (X 0) (obj (Fin.tail (Fin.init X))) (X (Fin.last (m + 1)))).hom =
          ((appendIso (fun _ : Fin 1 => X 0) (Fin.tail (Fin.init X))).hom ⊗ₘ
            𝟙 (X (Fin.last (m + 1)))) ≫
            (α_ (obj (fun _ : Fin 1 => X 0)) (obj (Fin.tail (Fin.init X)))
              (X (Fin.last (m + 1)))).hom ≫
            ((singletonIso (fun _ : Fin 1 => X 0)).hom ⊗ₘ
              𝟙 (obj (Fin.tail (Fin.init X)) ⊗ X (Fin.last (m + 1)))) := by
        have hc := tensorHom_comp_tensorHom
          (appendIso (fun _ : Fin 1 => X 0) (Fin.tail (Fin.init X))).hom
          (𝟙 (X (Fin.last (m + 1))))
          ((singletonIso (fun _ : Fin 1 => X 0)).hom ⊗ₘ
            𝟙 (obj (Fin.tail (Fin.init X)))) (𝟙 (X (Fin.last (m + 1))))
        simp only [Category.id_comp] at hc
        rw [← hc, Category.assoc, hn]
      have hwhole := heq_comp
        (congrArg (fun T : C => T ⊗ X (Fin.last (m + 1))) hsrc) rfl rfl hs
        (HEq.rfl (a := (α_ (X 0) (obj (Fin.tail (Fin.init X)))
          (X (Fin.last (m + 1)))).hom))
      have hright := eqToHom_comp_heq
        (((appendIso (fun _ : Fin 1 => X 0) (Fin.init (Fin.tail X))).hom ⊗ₘ
          𝟙 ((Fin.tail X) (Fin.last m))) ≫
          (α_ (obj (fun _ : Fin 1 => X 0)) (obj (Fin.init (Fin.tail X)))
            ((Fin.tail X) (Fin.last m))).hom ≫
          ((singletonIso (fun _ : Fin 1 => X 0)).hom ⊗ₘ 𝟙 (obj (Fin.tail X))))
        (append_step (fun _ : Fin 1 => X 0) (Fin.tail X))
      simpa only [Category.assoc] using
        hwhole.trans ((heq_of_eq hfactor).trans hright.symm)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_HeadTailAppendMapCoherence

/- Source proof segment: HeadTailAppendTransport -/
section source_HeadTailAppendTransport
/-!
# Original head-tail and append equality transports

The original index and object equalities transport the actual ordered
tensor comparisons. Every map remains the supplied binary tensor map.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

omit [Category.{v} C] [MonoidalCategory C] in
/-- The original singleton and tail append retains each original input. -/
theorem singletonAppend_family {m : ℕ} (X : Fin (m + 1) → C) (i : Fin (m + 1)) :
    X i = Fin.append (fun _ : Fin 1 => X 0) (Fin.tail X)
      (Fin.cast (Nat.add_comm m 1) i) := by
  have h := congrFun (Fin.append_left_eq_cons (fun _ : Fin 1 => X 0) (Fin.tail X))
    (Fin.cast (Nat.add_comm m 1) i)
  change Fin.append (fun _ : Fin 1 => X 0) (Fin.tail X) (Fin.cast (Nat.add_comm m 1) i) =
    Fin.cons (X 0) (Fin.tail X)
      (Fin.cast (Nat.add_comm 1 m) (Fin.cast (Nat.add_comm m 1) i)) at h
  rw [Fin.cons_self_tail] at h
  have hc : Fin.cast (Nat.add_comm 1 m) (Fin.cast (Nat.add_comm m 1) i) = i := Fin.ext rfl
  rw [hc] at h
  exact h.symm

/-- The original head-tail carrier is the singleton and tail append carrier. -/
theorem singletonAppend_obj_eq {m : ℕ} (X : Fin (m + 1) → C) :
    obj X = obj (Fin.append (fun _ : Fin 1 => X 0) (Fin.tail X)) :=
  obj_congr (Nat.add_comm m 1) X _ (singletonAppend_family X)

/-- Equal original arities and objects transport the original head-tail map. -/
theorem headTailIso_hom_heq {m n : ℕ} (h : m = n)
    (X : Fin (m + 1) → C) (Y : Fin (n + 1) → C)
    (hXY : ∀ i, X i = Y (Fin.cast (congrArg (· + 1) h) i)) :
    HEq (headTailIso X).hom (headTailIso Y).hom := by
  subst n
  have hx : X = Y := funext hXY
  subst Y
  rfl

/-- Equal original block profiles have equal original append tensor carriers. -/
theorem append_obj_congr {m m' n n' : ℕ} (hm : m = m') (hn : n = n')
    (X : Fin m → C) (X' : Fin m' → C) (Y : Fin n → C) (Y' : Fin n' → C)
    (hX : ∀ i, X i = X' (Fin.cast hm i)) (hY : ∀ i, Y i = Y' (Fin.cast hn i)) :
    obj (Fin.append X Y) = obj (Fin.append X' Y') := by
  subst m'
  subst n'
  have hx : X = X' := funext hX
  have hy : Y = Y' := funext hY
  subst X'
  subst Y'
  rfl

/-- The original retained-prefix history is the original literal append carrier. -/
theorem prefixHistory_obj_eq {m n : ℕ} (X : Fin m → C) (Y : Fin n → C) :
    obj (prefixHistoryFamily X Y) = obj (Fin.append X Y) :=
  obj_congr (Nat.add_comm n m) _ _ (fun _ => rfl)

/-- The history append hom retains the actual original block split after its source equality. -/
theorem prefixHistoryAppend_hom_heq {m n : ℕ} (X : Fin m → C) (Y : Fin n → C) :
    HEq (prefixHistoryAppendIso X Y).hom (appendIso X Y).hom := by
  change HEq (eqToHom (prefixHistory_obj_eq X Y) ≫ (appendIso X Y).hom) (appendIso X Y).hom
  exact eqToHom_comp_heq _ _

omit [Category.{v} C] [MonoidalCategory C] in
/-- The original retained-prefix history is the cons of its original head and literal tail
append. -/
theorem prefixHistory_cons_family {m n : ℕ} (X : Fin (m + 1) → C) (Y : Fin n → C)
    (i : Fin (n + m + 1)) :
    prefixHistoryFamily (m := m + 1) (n := n) X Y i =
      Fin.cons (α := fun _ : Fin (m + n + 1) => C) (X 0) (Fin.append (Fin.tail X) Y)
        (Fin.cast (congrArg (· + 1) (Nat.add_comm n m)) i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [prefixHistory_head]
    rfl
  · have ht := congrFun (prefixHistory_tail X Y) j
    change prefixHistoryFamily X Y j.succ =
      Fin.append (Fin.tail X) Y (Fin.cast (Nat.add_comm n m) j) at ht
    have hc : Fin.cast (congrArg (· + 1) (Nat.add_comm n m)) j.succ =
        (Fin.cast (Nat.add_comm n m) j).succ := Fin.ext rfl
    rw [hc, Fin.cons_succ]
    exact ht

/-- The history head-tail map is the original singleton and literal tail-append split. -/
theorem prefixHistory_headTail_hom_heq {m n : ℕ} (X : Fin (m + 1) → C) (Y : Fin n → C) :
    HEq (headTailIso (n := n + m) (prefixHistoryFamily (m := m + 1) (n := n) X Y)).hom
      ((appendIso (fun _ : Fin 1 => X 0) (Fin.append (Fin.tail X) Y)).hom ≫
        ((singletonIso (fun _ : Fin 1 => X 0)).hom ⊗ₘ
          𝟙 (obj (Fin.append (Fin.tail X) Y)))) := by
  have h := headTailIso_hom_heq (Nat.add_comm n m)
    (prefixHistoryFamily (m := m + 1) (n := n) X Y)
    (Fin.cons (α := fun _ : Fin (m + n + 1) => C) (X 0) (Fin.append (Fin.tail X) Y))
    (prefixHistory_cons_family X Y)
  have hs := headTail_eq_singleton_append
    (Fin.cons (α := fun _ : Fin (m + n + 1) => C) (X 0) (Fin.append (Fin.tail X) Y))
  exact h.trans hs

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_HeadTailAppendTransport

/- Source proof segment: HeadTailAppendAssociativity -/
section source_HeadTailAppendAssociativity
/-!
# Original head-tail append associativity
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The original head unitor interchanges with an arbitrary original tail map. -/
theorem headUnit_tensor_interchange {S A B : C} (d : A ⟶ B) :
    ((λ_ S).hom ⊗ₘ 𝟙 A) ≫ (𝟙 S ⊗ₘ d) =
      (𝟙 (𝟙_ C ⊗ S) ⊗ₘ d) ≫ ((λ_ S).hom ⊗ₘ 𝟙 B) := by
  have hl := tensorHom_comp_tensorHom (λ_ S).hom (𝟙 A) (𝟙 S) d
  have hr := tensorHom_comp_tensorHom (𝟙 (𝟙_ C ⊗ S)) d (λ_ S).hom (𝟙 B)
  simp only [Category.comp_id, Category.id_comp] at hl hr
  exact hl.trans hr.symm

/-- The original singleton-head split joins the original associator naturally. -/
theorem headUnit_assoc_split {P S A B : C} (d : P ⟶ (𝟙_ C ⊗ S) ⊗ A) :
    ((d ≫ ((λ_ S).hom ⊗ₘ 𝟙 A)) ⊗ₘ 𝟙 B) ≫ (α_ S A B).hom =
      (d ⊗ₘ 𝟙 B) ≫ (α_ (𝟙_ C ⊗ S) A B).hom ≫ ((λ_ S).hom ⊗ₘ 𝟙 (A ⊗ B)) := by
  have hc := tensorHom_comp_tensorHom d (𝟙 B) ((λ_ S).hom ⊗ₘ 𝟙 A) (𝟙 B)
  simp only [Category.id_comp] at hc
  have hn := associator_naturality (λ_ S).hom (𝟙 A) (𝟙 B)
  simp only [id_tensorHom_id] at hn
  rw [← hc, Category.assoc, hn]

set_option backward.isDefEq.respectTransparency false in
/-- Original head-tail and block append splits obey the original binary associator coherence. -/
theorem headTail_append_coherence {m n : ℕ} (X : Fin (m + 1) → C) (Y : Fin n → C) :
    (headTailIso (prefixHistoryFamily (m := m + 1) (n := n) X Y)).hom ≫
        eqToHom (show prefixHistoryFamily X Y 0 ⊗ obj (Fin.tail
            (n := n + m) (prefixHistoryFamily (m := m + 1) (n := n) X Y)) =
            X 0 ⊗ obj (prefixHistoryFamily (Fin.tail X) Y) from by
          rw [prefixHistory_head, prefixHistory_tail]) ≫
        (𝟙 (X 0) ⊗ₘ (prefixHistoryAppendIso (Fin.tail X) Y).hom) =
      (prefixHistoryAppendIso X Y).hom ≫ ((headTailIso X).hom ⊗ₘ 𝟙 (obj Y)) ≫
        (α_ (X 0) (obj (Fin.tail X)) (obj Y)).hom := by
  let S : Fin 1 → C := fun _ => X 0
  let T := Fin.tail X
  let F := prefixHistoryFamily (m := m + 1) (n := n) X Y
  let Z : Fin (m + n + 1) → C := Fin.cons (α := fun _ : Fin (m + n + 1) => C)
    (X 0) (Fin.append T Y)
  have hSourceL : obj F = obj (Fin.append S (Fin.append T Y)) :=
    (obj_congr (congrArg (· + 1) (Nat.add_comm n m)) F Z
      (prefixHistory_cons_family X Y)).trans (singletonAppend_obj_eq Z)
  have hMiddleL : F 0 ⊗ obj (Fin.tail (n := n + m) F) = X 0 ⊗ obj (Fin.append T Y) := by
    dsimp only [F, T]
    rw [prefixHistory_head, prefixHistory_tail, prefixHistory_obj_eq]
  have hTensorL := tensorMapBoundary_heq rfl rfl
    (prefixHistory_obj_eq T Y) rfl
    (HEq.rfl (a := 𝟙 (X 0))) (prefixHistoryAppend_hom_heq T Y)
  have hGL := (eqToHom_comp_heq
    (𝟙 (X 0) ⊗ₘ (prefixHistoryAppendIso T Y).hom)
    (show F 0 ⊗ obj (Fin.tail (n := n + m) F) =
        X 0 ⊗ obj (prefixHistoryFamily T Y) from by
      dsimp only [F, T]
      rw [prefixHistory_head, prefixHistory_tail])).trans hTensorL
  have hJoinL := heq_comp hSourceL hMiddleL rfl
    (prefixHistory_headTail_hom_heq X Y) hGL
  have hCoreL :
      ((appendIso S (Fin.append T Y)).hom ≫
        ((λ_ (X 0)).hom ⊗ₘ 𝟙 (obj (Fin.append T Y)))) ≫
          (𝟙 (X 0) ⊗ₘ (appendIso T Y).hom) =
      (appendIso S (Fin.append T Y)).hom ≫
        (𝟙 (obj S) ⊗ₘ (appendIso T Y).hom) ≫
        ((λ_ (X 0)).hom ⊗ₘ 𝟙 (obj T ⊗ obj Y)) := by
    rw [Category.assoc, headUnit_tensor_interchange]
    rfl
  have hAssocL := eqToHom_comp_heq
    ((appendIso S (Fin.append T Y)).hom ≫
      (𝟙 (obj S) ⊗ₘ (appendIso T Y).hom) ≫
      ((λ_ (X 0)).hom ⊗ₘ 𝟙 (obj T ⊗ obj Y))) (appendAssociator_obj_eq S T Y)
  have hLeft : HEq
      ((headTailIso F).hom ≫ eqToHom
        (show F 0 ⊗ obj (Fin.tail (n := n + m) F) =
            X 0 ⊗ obj (prefixHistoryFamily T Y) from by
          dsimp only [F, T]
          rw [prefixHistory_head, prefixHistory_tail]) ≫
        (𝟙 (X 0) ⊗ₘ (prefixHistoryAppendIso T Y).hom))
      (appendAssocLeft S T Y ≫ ((λ_ (X 0)).hom ⊗ₘ 𝟙 (obj T ⊗ obj Y))) := by
    simpa only [appendAssocLeft, appendAssociator, eqToIso.hom, Category.assoc] using
      hJoinL.trans ((heq_of_eq hCoreL).trans hAssocL.symm)
  have hSourceX := singletonAppend_obj_eq X
  have hMiddleR : obj X ⊗ obj Y = obj (Fin.append S T) ⊗ obj Y :=
    congrArg (fun A : C => A ⊗ obj Y) hSourceX
  have hTensorR := tensorMapBoundary_heq hSourceX rfl rfl rfl
    (headTail_eq_singleton_append X) (HEq.rfl (a := 𝟙 (obj Y)))
  have hJoinGR := heq_comp hMiddleR rfl rfl hTensorR
    (HEq.rfl (a := (α_ (X 0) (obj T) (obj Y)).hom))
  have hCoreR := headUnit_assoc_split (B := obj Y) (appendIso S T).hom
  have hAppR := (prefixHistoryAppend_hom_heq X Y).trans
    (appendIso_hom_heq (Nat.add_comm m 1) rfl X (Fin.append S T) Y Y
      (singletonAppend_family X) (fun _ => rfl))
  have hSourceR : obj F = obj (Fin.append (Fin.append S T) Y) :=
    (prefixHistory_obj_eq X Y).trans
      (append_obj_congr (Nat.add_comm m 1) rfl X (Fin.append S T) Y Y
        (singletonAppend_family X) (fun _ => rfl))
  have hJoinR := heq_comp hSourceR hMiddleR rfl hAppR
    (hJoinGR.trans (heq_of_eq hCoreR))
  have hRight : HEq
      ((prefixHistoryAppendIso X Y).hom ≫ ((headTailIso X).hom ⊗ₘ 𝟙 (obj Y)) ≫
        (α_ (X 0) (obj T) (obj Y)).hom)
      (appendAssocRight S T Y ≫ ((λ_ (X 0)).hom ⊗ₘ 𝟙 (obj T ⊗ obj Y))) := by
    dsimp only [S] at hJoinR ⊢
    simpa only [appendAssocRight, Category.assoc, obj_succ, obj_zero] using hJoinR
  have hAssoc := congrArg (· ≫ ((λ_ (X 0)).hom ⊗ₘ 𝟙 (obj T ⊗ obj Y)))
    (appendSplit_associativity S T Y)
  exact eq_of_heq (hLeft.trans ((heq_of_eq hAssoc).trans hRight.symm))

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_HeadTailAppendAssociativity

/- Source proof segment: RightPrefixHeadTail -/
section source_RightPrefixHeadTail
/-!
# Actual head-tail map of a retained-prefix tensor action

The constructed fixed-first action transports the original head-tail
map, with the original tail action and all finite input equalities.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The original head-tail comparison on the literal retained-prefix history. -/
noncomputable def headHistoryIso {m n : ℕ} (X : Fin (m + 1) → C) (Y : Fin n → C) :
    obj (prefixHistoryFamily X Y) ≅ X 0 ⊗ obj (prefixHistoryFamily (Fin.tail X) Y) :=
  headTailIso (n := n + m) (prefixHistoryFamily (m := m + 1) (n := n) X Y) ≪≫
    eqToIso (show prefixHistoryFamily (m := m + 1) (n := n) X Y 0 ⊗
        obj (Fin.tail (n := n + m) (prefixHistoryFamily (m := m + 1) (n := n) X Y)) =
        X 0 ⊗ obj (prefixHistoryFamily (Fin.tail X) Y) from by
      rw [prefixHistory_head, prefixHistory_tail])

/-- Equality of original families transports the actual head-tail comparison. -/
@[reassoc] theorem headTailIso_transport {n : ℕ} (X Y : Fin (n + 1) → C) (h : X = Y) :
    eqToHom (congrArg obj h) ≫ (headTailIso Y).hom =
      (headTailIso X).hom ≫
        eqToHom (congrArg (fun Z : Fin (n + 1) → C => Z 0 ⊗ obj (Fin.tail Z)) h) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The original retained-prefix head-tail comparison joins the original append split. -/
theorem headHistory_append_coherence {m n : ℕ} (X : Fin (m + 1) → C) (Y : Fin n → C) :
    (headHistoryIso X Y).hom ≫ (𝟙 (X 0) ⊗ₘ (prefixHistoryAppendIso (Fin.tail X) Y).hom) =
      (prefixHistoryAppendIso X Y).hom ≫ ((headTailIso X).hom ⊗ₘ 𝟙 (obj Y)) ≫
        (α_ (X 0) (obj (Fin.tail X)) (obj Y)).hom := by
  simpa only [headHistoryIso, Iso.trans_hom, eqToIso.hom, Category.assoc] using
    headTail_append_coherence X Y

variable [SymmetricCategory C]

omit [SymmetricCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- The actual retained-prefix action commutes with the original head-tail map and actual
tail action. -/
theorem extendTensorPrefix_headHistory {n m : ℕ} (r : TensorReindexing C n)
    (X : Fin (m + 1) → C) (Y : Fin n → C) :
    (extendTensorPrefix r (m + 1)).comparison.hom.app (prefixHistoryFamily X Y) ≫
        eqToHom (congrArg obj (prefixHistory_reindex r X Y)) ≫
        (headHistoryIso X (familyEquiv r.perm Y)).hom =
      (headHistoryIso X Y).hom ≫
        (𝟙 (X 0) ⊗ₘ ((extendTensorPrefix r m).comparison.hom.app
          (prefixHistoryFamily (Fin.tail X) Y) ≫
            eqToHom (congrArg obj (prefixHistory_reindex r (Fin.tail X) Y)))) := by
  let R := extendTensorPrefix r m
  let F := prefixHistoryFamily (m := m + 1) (n := n) X Y
  let T := prefixHistoryFamily (Fin.tail X) Y
  let G := prefixHistoryFamily (m := m + 1) (n := n) X (familyEquiv r.perm Y)
  have hG : familyEquiv (extendFirstPerm (n + m) R.perm) F = G :=
    prefixHistory_reindex r X Y
  have hLeft : HEq
      ((extendTensorPrefix r (m + 1)).comparison.hom.app F ≫
        eqToHom (congrArg obj hG) ≫ (headHistoryIso X (familyEquiv r.perm Y)).hom)
      ((headTailIso F).hom ≫ (𝟙 (F 0) ⊗ₘ R.comparison.hom.app (Fin.tail F))) := by
    change HEq ((extendFirstHom R).comparison.hom.app F ≫
      eqToHom (congrArg obj hG) ≫ (headHistoryIso X (familyEquiv r.perm Y)).hom) _
    rw [extendFirstHom_hom_app]
    dsimp only [headHistoryIso]
    simp only [Iso.trans_hom, eqToIso.hom, Category.assoc]
    dsimp only [functor]
    rw [headTailIso_transport_assoc _ _ hG]
    simp only [Iso.inv_hom_id_assoc, eqToHom_trans]
    simp only [← Category.assoc]
    exact comp_eqToHom_heq _ _
  have hF0 : F 0 = X 0 := prefixHistory_head X Y
  have hFT : Fin.tail (n := n + m) F = T := prefixHistory_tail X Y
  have payloadTransport (A B : C) (P Q : Fin (n + m) → C)
      (hA : A = B) (hP : P = Q) :
      HEq (𝟙 A ⊗ₘ R.comparison.hom.app P) (𝟙 B ⊗ₘ R.comparison.hom.app Q) := by
    cases hA
    cases hP
    rfl
  have hPayload := payloadTransport (F 0) (X 0) (Fin.tail F) T hF0 hFT
  have hSource : F 0 ⊗ obj (Fin.tail F) = X 0 ⊗ obj T := by rw [hF0, hFT]
  have hTarget : F 0 ⊗ obj (familyEquiv R.perm (Fin.tail F)) =
      X 0 ⊗ obj (familyEquiv R.perm T) := by rw [hF0, hFT]
  have hRightBase := heq_comp rfl rfl hTarget
    (HEq.rfl (a := (headTailIso F).hom))
    (hPayload.trans (eqToHom_comp_heq (𝟙 (X 0) ⊗ₘ R.comparison.hom.app T) hSource).symm)
  have hRight : HEq
      ((headHistoryIso X Y).hom ≫
        (𝟙 (X 0) ⊗ₘ (R.comparison.hom.app T ≫
          eqToHom (congrArg obj (prefixHistory_reindex r (Fin.tail X) Y)))))
      ((headHistoryIso X Y).hom ≫ (𝟙 (X 0) ⊗ₘ R.comparison.hom.app T)) := by
    have ht := tensorHom_comp_tensorHom (𝟙 (X 0)) (R.comparison.hom.app T)
      (𝟙 (X 0)) (eqToHom (congrArg obj (prefixHistory_reindex r (Fin.tail X) Y)))
    simp only [Category.id_comp] at ht
    rw [← ht]
    have he : (𝟙 (X 0) ⊗ₘ eqToHom
        (congrArg obj (prefixHistory_reindex r (Fin.tail X) Y))) =
        eqToHom (congrArg (fun A : C => X 0 ⊗ A)
          (congrArg obj (prefixHistory_reindex r (Fin.tail X) Y))) := by
      rw [id_tensorHom, whiskerLeft_eqToHom]
    rw [he, ← Category.assoc]
    exact comp_eqToHom_heq _ _
  have hJoin : HEq
      ((headTailIso F).hom ≫ (𝟙 (F 0) ⊗ₘ R.comparison.hom.app (Fin.tail F)))
      ((headHistoryIso X Y).hom ≫ (𝟙 (X 0) ⊗ₘ R.comparison.hom.app T)) := by
    simpa only [headHistoryIso, Iso.trans_hom, eqToIso.hom, Category.assoc] using hRightBase
  exact eq_of_heq (hLeft.trans (hJoin.trans hRight.symm))

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_RightPrefixHeadTail

/- Source proof segment: RightPrefixAppendMaps -/
section source_RightPrefixAppendMaps
/-!
# Original tensor map of a right block under a retained prefix

The actual fixed-first comparison history is joined to the original
append split with its literal finite input-count transport retained.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory
open TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [SymmetricCategory C] in
/-- The original empty-prefix append split is the original left unitor inverse after its
input equality. -/
theorem prefixHistoryAppend_empty_left_heq {n : ℕ} (X : Fin 0 → C) (Y : Fin n → C) :
    HEq (prefixHistoryAppendIso X Y).hom (λ_ (obj Y)).inv := by
  let d : obj (Fin.append X Y) ⟶ 𝟙_ C ⊗ obj Y := (appendIso X Y).hom
  have hunit : d ≫ (λ_ (obj Y)).hom = eqToHom (appendLeftUnit_obj_eq X Y) :=
    appendIso_empty_left X Y
  have ha : d =
      eqToHom (appendLeftUnit_obj_eq X Y) ≫ (λ_ (obj Y)).inv := by
    calc
      d = (d ≫ (λ_ (obj Y)).hom) ≫
          (λ_ (obj Y)).inv := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = _ := by rw [hunit]
  exact (prefixHistoryAppend_hom_heq X Y).trans
    ((heq_of_eq ha).trans (eqToHom_comp_heq _ _))

omit [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] in
/-- The empty retained prefix leaves each original tail input unchanged. -/
theorem prefixHistory_empty_family {n : ℕ} (X : Fin 0 → C) (Y : Fin n → C) :
    prefixHistoryFamily X Y = Y := by
  have hx : X = Fin.elim0 := funext (fun i => i.elim0)
  subst X
  funext i
  simp only [prefixHistoryFamily, Fin.elim0_append, Function.comp_apply, Fin.cast_cast]
  congr 1

omit [SymmetricCategory C] in
/-- A map after the prefix split joins the original binary associator square. -/
theorem prefixSquare_associator {Q V T A B : C} (h : Q ⟶ V ⊗ T) (a : A ⟶ B) :
    (𝟙 Q ⊗ₘ a) ≫ (h ⊗ₘ 𝟙 B) ≫ (α_ V T B).hom =
      (h ⊗ₘ 𝟙 A) ≫ (α_ V T A).hom ≫ (𝟙 V ⊗ₘ (𝟙 T ⊗ₘ a)) := by
  have hl := tensorHom_comp_tensorHom (𝟙 Q) a h (𝟙 B)
  have hr := tensorHom_comp_tensorHom h (𝟙 A) (𝟙 (V ⊗ T)) a
  simp only [Category.id_comp, Category.comp_id] at hl hr
  have hn := associator_naturality (𝟙 V) (𝟙 T) a
  simp only [id_tensorHom_id] at hn
  rw [← Category.assoc, hl, ← hr, Category.assoc, hn]

omit [SymmetricCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- The original right-block comparison intertwines the full retained prefix and original
append split. -/
theorem extendTensorPrefix_append {n : ℕ} (r : TensorReindexing C n) (Y : Fin n → C) :
    ∀ {m : ℕ} (X : Fin m → C),
    (extendTensorPrefix r m).comparison.hom.app (prefixHistoryFamily X Y) ≫
        eqToHom (congrArg obj (prefixHistory_reindex r X Y)) ≫
        (prefixHistoryAppendIso X (familyEquiv r.perm Y)).hom =
      (prefixHistoryAppendIso X Y).hom ≫ (𝟙 (obj X) ⊗ₘ r.comparison.hom.app Y) := by
  intro m
  induction m with
  | zero =>
      intro X
      have hf := prefixHistory_empty_family X Y
      have hSource := congrArg obj hf
      have hTarget := congrArg (fun F : Fin n → C => obj (familyEquiv r.perm F)) hf
      have comparisonTransport (P Q : Fin n → C) (h : P = Q) :
          HEq (r.comparison.hom.app P) (r.comparison.hom.app Q) := by
        cases h
        rfl
      have he := comparisonTransport _ _ hf
      have hg := (eqToHom_comp_heq
        (prefixHistoryAppendIso X (familyEquiv r.perm Y)).hom
        (congrArg obj (prefixHistory_reindex r X Y))).trans
        (prefixHistoryAppend_empty_left_heq X (familyEquiv r.perm Y))
      have hLeft := heq_comp hSource hTarget rfl he hg
      have hRight := heq_comp hSource rfl rfl (prefixHistoryAppend_empty_left_heq X Y)
        (HEq.rfl (a := 𝟙 (𝟙_ C) ⊗ₘ r.comparison.hom.app Y))
      have hnat := leftUnitor_inv_naturality (r.comparison.hom.app Y)
      simp only [← id_tensorHom] at hnat
      exact eq_of_heq (hLeft.trans ((heq_of_eq hnat).trans hRight.symm))
  | succ m ih =>
      intro X
      let Z := familyEquiv r.perm Y
      let T := Fin.tail X
      let F := prefixHistoryFamily (m := m + 1) (n := n) X Y
      let G := prefixHistoryFamily (m := m + 1) (n := n) X Z
      let E : obj F ⟶ obj G :=
        (extendTensorPrefix r (m + 1)).comparison.hom.app F ≫
          eqToHom (congrArg obj (prefixHistory_reindex r X Y))
      let D : obj (prefixHistoryFamily T Y) ⟶ obj (prefixHistoryFamily T Z) :=
        (extendTensorPrefix r m).comparison.hom.app (prefixHistoryFamily T Y) ≫
          eqToHom (congrArg obj (prefixHistory_reindex r T Y))
      let a : obj Y ⟶ obj Z := r.comparison.hom.app Y
      have hrec : D ≫ (prefixHistoryAppendIso T Z).hom =
          (prefixHistoryAppendIso T Y).hom ≫ (𝟙 (obj T) ⊗ₘ a) := by
        simpa only [D, a, Z, Category.assoc] using ih T
      have hhead : E ≫ (headHistoryIso X Z).hom =
          (headHistoryIso X Y).hom ≫ (𝟙 (X 0) ⊗ₘ D) := by
        simpa only [E, D, F, G, Z, T, Category.assoc] using
          extendTensorPrefix_headHistory r X Y
      let K : obj X ⊗ obj Z ≅ X 0 ⊗ (obj T ⊗ obj Z) :=
        tensorIso (headTailIso X) (Iso.refl (obj Z)) ≪≫ α_ (X 0) (obj T) (obj Z)
      apply (cancel_mono K.hom).mp
      simp only [← Category.assoc]
      change (E ≫ (prefixHistoryAppendIso X Z).hom) ≫ K.hom =
        ((prefixHistoryAppendIso X Y).hom ≫ (𝟙 (obj X) ⊗ₘ a)) ≫ K.hom
      have hTensor := tensorHom_comp_tensorHom (𝟙 (X 0)) D (𝟙 (X 0))
        (prefixHistoryAppendIso T Z).hom
      simp only [Category.id_comp] at hTensor
      have hTensorRec := tensorHom_comp_tensorHom (𝟙 (X 0))
        (prefixHistoryAppendIso T Y).hom (𝟙 (X 0)) (𝟙 (obj T) ⊗ₘ a)
      simp only [Category.id_comp] at hTensorRec
      calc
        (E ≫ (prefixHistoryAppendIso X Z).hom) ≫ K.hom =
            E ≫ (headHistoryIso X Z).hom ≫ (𝟙 (X 0) ⊗ₘ (prefixHistoryAppendIso T Z).hom) := by
          dsimp only [K]
          simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, Category.assoc]
          rw [← headHistory_append_coherence X Z]
        _ = (headHistoryIso X Y).hom ≫ (𝟙 (X 0) ⊗ₘ D) ≫
            (𝟙 (X 0) ⊗ₘ (prefixHistoryAppendIso T Z).hom) := by
          rw [← Category.assoc, hhead, Category.assoc]
        _ = (headHistoryIso X Y).hom ≫ (𝟙 (X 0) ⊗ₘ (D ≫ (prefixHistoryAppendIso T Z).hom)) := by
          rw [hTensor]
        _ = (headHistoryIso X Y).hom ≫
            (𝟙 (X 0) ⊗ₘ ((prefixHistoryAppendIso T Y).hom ≫ (𝟙 (obj T) ⊗ₘ a))) := by rw [hrec]
        _ = (headHistoryIso X Y).hom ≫ (𝟙 (X 0) ⊗ₘ (prefixHistoryAppendIso T Y).hom) ≫
            (𝟙 (X 0) ⊗ₘ (𝟙 (obj T) ⊗ₘ a)) := by rw [← hTensorRec]
        _ = (prefixHistoryAppendIso X Y).hom ≫ ((headTailIso X).hom ⊗ₘ 𝟙 (obj Y)) ≫
            (α_ (X 0) (obj T) (obj Y)).hom ≫ (𝟙 (X 0) ⊗ₘ (𝟙 (obj T) ⊗ₘ a)) := by
          rw [← Category.assoc, headHistory_append_coherence X Y, Category.assoc]
          simp only [Category.assoc]
          rfl
        _ = ((prefixHistoryAppendIso X Y).hom ≫ (𝟙 (obj X) ⊗ₘ a)) ≫ K.hom := by
          dsimp only [K]
          simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, Category.assoc]
          rw [prefixSquare_associator]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_RightPrefixAppendMaps

/- Source proof segment: PrefixHistoryAction -/
section source_PrefixHistoryAction
/-!
# The actual constructed action on original retained-prefix histories

The complete original fixed-first extension record is joined to the
constructed permutation homomorphism before the natural comparison
is projected. Original input count transports remain explicit.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The original retained-prefix record is the actual constructed input permutation record. -/
theorem actualPrefixRecord_eq {n : ℕ} (p : Equiv.Perm (Fin n)) (m : ℕ) :
    extendTensorPrefix (firstPermutationRecord (C := C) p) m =
      firstPermutationRecord (extendPermPrefix p m) := by
  have hBase : firstPermutationRecord (C := C) p = permutationHom n p :=
    rebaseRecord_eq _ _ (permutationHom_perm n p)
  have hTotal : firstPermutationRecord (C := C) (extendPermPrefix p m) =
      permutationHom (n + m) (extendPermPrefix p m) :=
    rebaseRecord_eq _ _ (permutationHom_perm (n + m) (extendPermPrefix p m))
  exact (congrArg (fun r => extendTensorPrefix r m) hBase).trans
    ((permutationHom_extendPrefix p m).symm.trans hTotal.symm)

set_option backward.isDefEq.respectTransparency false in
/-- The actual constructed prefix permutation retains the original reindexed history family. -/
theorem actualPrefix_family {m n : ℕ} (p : Equiv.Perm (Fin n))
    (X : Fin m → C) (Y : Fin n → C) :
    familyEquiv (firstPermutationRecord (C := C) (extendPermPrefix p m)).perm
      (prefixHistoryFamily X Y) = prefixHistoryFamily X (familyEquiv p Y) := by
  have hs := prefixHistory_reindex (firstPermutationRecord (C := C) p) X Y
  have he := congrArg (fun q : TensorReindexing C (n + m) =>
    familyEquiv q.perm (prefixHistoryFamily X Y)) (actualPrefixRecord_eq (C := C) p m)
  exact he.symm.trans hs

set_option backward.isDefEq.respectTransparency false in
/-- The original actual prefix-history action retains its original append comparison square. -/
theorem actualPrefix_append {m n : ℕ} (p : Equiv.Perm (Fin n))
    (X : Fin m → C) (Y : Fin n → C) :
    (comparisonAlong (firstPermutationRecord (extendPermPrefix p m))
        (prefixHistoryFamily X Y) (prefixHistoryFamily X (familyEquiv p Y))
          (actualPrefix_family p X Y)).hom ≫
            (prefixHistoryAppendIso X (familyEquiv p Y)).hom =
      (prefixHistoryAppendIso X Y).hom ≫ (𝟙 (obj X) ⊗ₘ (permutationIso p Y).hom) := by
  let r := firstPermutationRecord (C := C) p
  let s := extendTensorPrefix r m
  let S := prefixHistoryFamily X Y
  let T := prefixHistoryFamily X (familyEquiv p Y)
  have hs : familyEquiv s.perm S = T := prefixHistory_reindex r X Y
  have ht : familyEquiv (firstPermutationRecord (C := C) (extendPermPrefix p m)).perm S = T := by
    exact (congrArg (fun q : TensorReindexing C (n + m) => familyEquiv q.perm S)
      (actualPrefixRecord_eq (C := C) p m)).symm.trans hs
  have hAlong := comparisonAlong_congr (actualPrefixRecord_eq (C := C) p m) S T hs ht
  have hOriginal := extendTensorPrefix_append r Y X
  have hSquare :
      (comparisonAlong (firstPermutationRecord (extendPermPrefix p m)) S T ht).hom ≫
          (prefixHistoryAppendIso X (familyEquiv p Y)).hom =
        (prefixHistoryAppendIso X Y).hom ≫ (𝟙 (obj X) ⊗ₘ r.comparison.hom.app Y) := by
    rw [← hAlong, comparisonAlong_hom]
    dsimp only [r, s, S, T] at hOriginal ⊢
    simp only [Category.assoc] at hOriginal ⊢
    exact hOriginal
  dsimp only [r, S, T] at hSquare
  rw [firstPermutationRecord_hom_app] at hSquare
  exact hSquare

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_PrefixHistoryAction

/- Source proof segment: InputEqualityIsoLaws -/
section source_InputEqualityIsoLaws
/-!
# Original finite component equality-isomorphism laws

Generic equality transports are checked before selecting the actual
block input bijections. These laws retain every original component
equality and the full input bijection.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C]

/-- Original equality isomorphisms with a common original source agree heterogeneously. -/
theorem eqToIso_heq_dom {X Y Z : C} (h : X = Y) (k : X = Z) :
    HEq (eqToIso h) (eqToIso k) := by
  cases h
  cases k
  rfl

/-- Original consecutive component equality isomorphisms retain the same original source. -/
theorem eqToIso_chain_heq {X Y Z W : C} (h : X = Y) (k : Y = Z) (l : X = W) :
    HEq (eqToIso h ≪≫ eqToIso k) (eqToIso l) := by
  cases h
  cases k
  cases l
  simpa only [eqToIso_refl, Iso.refl_trans] using (HEq.refl (Iso.refl X))

variable [MonoidalCategory C] [SymmetricCategory C]

/-- Equal whole input bijections retain the same original component equality tensor map. -/
theorem isoEquiv_eq_congr {m n : ℕ} {X : Fin m → C} {Y : Fin n → C}
    {e d : Fin m ≃ Fin n} (he : e = d)
    (h : ∀ i, X i = Y (e i)) (k : ∀ i, X i = Y (d i)) :
    isoEquiv e (fun i => eqToIso (h i)) = isoEquiv d (fun i => eqToIso (k i)) :=
  isoEquiv_congr he _ _ (fun i => eqToIso_heq_dom (h i) (k i))

/-- Original consecutive equal-object finite input isomorphisms tensor to their composite. -/
theorem isoEquiv_eq_trans {l m n : ℕ} {X : Fin l → C} {Y : Fin m → C} {Z : Fin n → C}
    (e : Fin l ≃ Fin m) (d : Fin m ≃ Fin n)
    (h : ∀ i, X i = Y (e i)) (k : ∀ i, Y i = Z (d i)) :
    isoEquiv e (fun i => eqToIso (h i)) ≪≫ isoEquiv d (fun i => eqToIso (k i)) =
      isoEquiv (e.trans d) (fun i => eqToIso ((h i).trans (k (e i)))) := by
  rw [isoEquiv_trans]
  exact isoEquiv_congr rfl _ _
    (fun i => eqToIso_chain_heq (h i) (k (e i)) ((h i).trans (k (e i))))

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_InputEqualityIsoLaws

/- Source proof segment: BlockInputs -/
section source_BlockInputs
/-!
# Original finite input bijections for two heterogeneous blocks

Every input slot, both block lengths and the original arithmetic
transports are retained, including either empty block.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

/-- The original sum of two independently specified finite input bijections. -/
def sumInputsEquiv {m m' n n' : ℕ} (e : Fin m ≃ Fin m') (d : Fin n ≃ Fin n') :
    Fin (m + n) ≃ Fin (m' + n') :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr e d).trans finSumFinEquiv)

/-- The original sum bijection acts on the original first-block injection. -/
@[simp] theorem sumInputsEquiv_left {m m' n n' : ℕ}
    (e : Fin m ≃ Fin m') (d : Fin n ≃ Fin n') (i : Fin m) :
    sumInputsEquiv e d (Fin.castAdd n i) = Fin.castAdd n' (e i) := by
  simp [sumInputsEquiv, Equiv.trans_apply]

/-- The original sum bijection acts on the original second-block injection. -/
@[simp] theorem sumInputsEquiv_right {m m' n n' : ℕ}
    (e : Fin m ≃ Fin m') (d : Fin n ≃ Fin n') (i : Fin n) :
    sumInputsEquiv e d (Fin.natAdd m i) = Fin.natAdd m' (d i) := by
  simp [sumInputsEquiv, Equiv.trans_apply]

/-- The two independent identity input bijections give the original total identity. -/
theorem sumInputsEquiv_refl (m n : ℕ) :
    sumInputsEquiv (Equiv.refl (Fin m)) (Equiv.refl (Fin n)) = Equiv.refl (Fin (m + n)) := by
  apply Equiv.ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

/-- Consecutive original block input bijections retain their independently composed slots. -/
theorem sumInputsEquiv_trans {m m' m'' n n' n'' : ℕ}
    (e : Fin m ≃ Fin m') (e' : Fin m' ≃ Fin m'')
    (d : Fin n ≃ Fin n') (d' : Fin n' ≃ Fin n'') :
    (sumInputsEquiv e d).trans (sumInputsEquiv e' d') =
      sumInputsEquiv (e.trans e') (d.trans d') := by
  apply Equiv.ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [Equiv.trans_apply]

/-- The literal block flip retains every original object at its actual target slot. -/
theorem blockFlip_objects {m n : ℕ} {α : Sort u} (X : Fin m → α) (Y : Fin n → α)
    (i : Fin (m + n)) :
    Fin.append X Y i = Fin.append Y X ((finAddFlip : Fin (m + n) ≃ Fin (n + m)) i) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left, finAddFlip_apply_castAdd, Fin.append_right]
  · rw [Fin.append_right, finAddFlip_apply_natAdd, Fin.append_left]

/-- With an empty second block the original flip is its actual count transport. -/
theorem blockFlip_zero_right_equiv (m : ℕ) :
    (finAddFlip : Fin (m + 0) ≃ Fin (0 + m)) =
      finCongr (Nat.zero_add m).symm := by
  apply Equiv.ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => Fin.elim0 j) i
  rw [finAddFlip_apply_castAdd]
  apply Fin.ext
  simp

/-- With an empty first block the original flip is its actual count transport. -/
theorem blockFlip_zero_left_equiv (n : ℕ) :
    (finAddFlip : Fin (0 + n) ≃ Fin (n + 0)) = finCongr (Nat.zero_add n) := by
  apply Equiv.ext
  intro i
  refine Fin.addCases (fun j => Fin.elim0 j) (fun j => ?_) i
  rw [finAddFlip_apply_natAdd]
  apply Fin.ext
  simp

/-- The original two literal block flips compose to the original finite input identity. -/
theorem blockFlip_double (m n : ℕ) :
    (finAddFlip : Fin (m + n) ≃ Fin (n + m)).trans
      (finAddFlip : Fin (n + m) ≃ Fin (m + n)) = Equiv.refl (Fin (m + n)) := by
  apply Equiv.ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [Equiv.trans_apply, finAddFlip_apply_castAdd, finAddFlip_apply_natAdd]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_BlockInputs

/- Source proof segment: ActualTensorPrefixCompatibility -/
section source_ActualTensorPrefixCompatibility
/-!
# Original finite tensor permutations retain a fixed final slot

The compatibility is proved on the actual adjacent generators and
extended to every actual finite permutation by homomorphism uniqueness.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory
open TensorReindexing
open Equiv.Perm.AdjacentPresentation

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- Arbitrary actual tensor permutations commute with the constructed fixed-last extension. -/
theorem permutationHom_extend (n : ℕ) :
    (permutationHom (C := C) (n + 1)).comp (extendPerm n) =
      (extendHom (C := C) (n := n)).comp (permutationHom n) := by
  cases n with
  | zero =>
      apply MonoidHom.ext
      intro p
      have hp : p = 1 := Subsingleton.elim _ _
      subst p
      simp only [map_one]
  | succ n =>
      apply MonoidHom.eq_of_eqOn_denseM
        (show Submonoid.closure (Set.range (adjacent n)) = ⊤ from
          Equiv.Perm.mclosure_swap_castSucc_succ n)
      rintro _ ⟨i, rfl⟩
      change permutationHom (C := C) (n + 2)
          (extendPerm (n + 1) (Equiv.swap i.castSucc i.succ)) =
        extendHom (permutationHom (n + 1) (Equiv.swap i.castSucc i.succ))
      have he : extendPerm (n + 1) (Equiv.swap i.castSucc i.succ) =
          Equiv.swap i.castSucc.castSucc i.castSucc.succ := by
        apply Equiv.ext
        intro j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · rw [extendPerm_last, Equiv.swap_apply_of_ne_of_ne]
          · exact (Fin.castSucc_ne_last i.castSucc).symm
          · simpa only [Fin.succ_castSucc] using (Fin.castSucc_ne_last i.succ).symm
        · rw [extendPerm_castSucc, Fin.succ_castSucc,
            (Fin.castSucc_injective (n + 1)).swap_apply]
      rw [he, permutationHom_adjacent, permutationHom_adjacent, tensorGenerator_castSucc]
      rfl

/-- The actual fixed-last extension retains arbitrary original tensor comparison maps. -/
theorem permutationHom_extend_hom {n : ℕ} (p : Equiv.Perm (Fin n))
    (X : Fin (n + 1) → C) :
    HEq
      ((permutationHom (C := C) (n + 1) (extendPerm n p)).comparison.hom.app X)
      ((permutationHom n p).comparison.hom.app (Fin.init X) ⊗ₘ 𝟙 (X (Fin.last n))) := by
  have h := congrArg (fun f => f p) (permutationHom_extend (C := C) n)
  change permutationHom (C := C) (n + 1) (extendPerm n p) =
    extend (permutationHom n p) at h
  rw [h]
  exact extend_hom_app_heq _ _

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ActualTensorPrefixCompatibility

/- Source proof segment: ActualTensorBlockExtension -/
section source_ActualTensorBlockExtension
/-!
# Retaining an ordered suffix under original tensor permutations

The input permutation and its actual natural tensor comparison are
extended through every retained suffix factor using the constructed
fixed-last homomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory
open TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- Extend an original input permutation through a prescribed ordered suffix length. -/
noncomputable def extendPermSuffix {n : ℕ} (p : Equiv.Perm (Fin n)) :
    (m : ℕ) → Equiv.Perm (Fin (n + m))
  | 0 => p
  | m + 1 => extendPerm (n + m) (extendPermSuffix p m)

/-- Extend an original natural tensor comparison through all retained suffix factors. -/
noncomputable def extendTensorSuffix {n : ℕ} (r : TensorReindexing C n) :
    (m : ℕ) → TensorReindexing C (n + m)
  | 0 => r
  | m + 1 => extendHom (extendTensorSuffix r m)

/-- Arbitrary original finite tensor permutations retain every prescribed suffix factor. -/
theorem permutationHom_extendSuffix {n : ℕ} (p : Equiv.Perm (Fin n)) :
    ∀ m : ℕ, permutationHom (C := C) (n + m) (extendPermSuffix p m) =
      extendTensorSuffix (permutationHom n p) m
  | 0 => rfl
  | m + 1 => by
      have h := congrArg (fun f => f (extendPermSuffix p m))
        (permutationHom_extend (C := C) (n + m))
      change permutationHom (C := C) (n + m + 1)
          (extendPerm (n + m) (extendPermSuffix p m)) =
        extendHom (permutationHom (n + m) (extendPermSuffix p m)) at h
      exact h.trans (congrArg extendHom (permutationHom_extendSuffix p m))

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ActualTensorBlockExtension

/- Source proof segment: ActualTensorBlockSplitCompatibility -/
section source_ActualTensorBlockSplitCompatibility
/-!
# Original tensor comparisons on an initial block and a retained suffix

The block split intertwines the original initial comparison extended
through the actual suffix tensor factors.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory
open TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The actual suffix extension acts only on the original initial input block. -/
theorem extendPermSuffix_castAdd {n : ℕ} (p : Equiv.Perm (Fin n)) :
    ∀ (m : ℕ) (i : Fin n), extendPermSuffix p m (Fin.castAdd m i) =
      Fin.castAdd m (p i)
  | 0, i => rfl
  | m + 1, i => by
      have h : Fin.castAdd (m + 1) i = (Fin.castAdd m i).castSucc := rfl
      rw [h, extendPermSuffix, extendPerm_castSucc, extendPermSuffix_castAdd]
      rfl

/-- The actual suffix extension retains each original final-block input index. -/
theorem extendPermSuffix_natAdd {n : ℕ} (p : Equiv.Perm (Fin n)) :
    ∀ (m : ℕ) (i : Fin m), extendPermSuffix p m (Fin.natAdd n i) = Fin.natAdd n i
  | 0, i => i.elim0
  | m + 1, i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have h : Fin.natAdd n (Fin.last m) = Fin.last (n + m) := rfl
        rw [h, extendPermSuffix, extendPerm_last]
      · have h : Fin.natAdd n j.castSucc = (Fin.natAdd n j).castSucc := rfl
        rw [h, extendPermSuffix, extendPerm_castSucc, extendPermSuffix_natAdd]

/-- The inverse actual extended permutation acts only on the original initial block. -/
theorem extendPermSuffix_inverse {n : ℕ} (p : Equiv.Perm (Fin n)) :
    ∀ m : ℕ, (extendPermSuffix p m).symm = extendPermSuffix p.symm m
  | 0 => rfl
  | m + 1 => by
      change (extendPerm (n + m) (extendPermSuffix p m))⁻¹ =
        extendPerm (n + m) (extendPermSuffix p.symm m)
      rw [← map_inv]
      exact congrArg (extendPerm (n + m)) (extendPermSuffix_inverse p m)

omit [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] in
/-- Reindexing the original concatenated family retains the actual unchanged suffix. -/
theorem append_reindex_extendSuffix {n m : ℕ} (p : Equiv.Perm (Fin n))
    (X : Fin n → C) (Y : Fin m → C) :
    Fin.append X Y ∘ (extendPermSuffix p m).symm = Fin.append (X ∘ p.symm) Y := by
  funext i
  rw [extendPermSuffix_inverse]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [Function.comp_apply, extendPermSuffix_castAdd, Fin.append_left]
  · simp only [Function.comp_apply, extendPermSuffix_natAdd, Fin.append_right]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ActualTensorBlockSplitCompatibility

/- Source proof segment: SumPermutation -/
section source_SumPermutation
/-!
# Original independent block permutations and their finite factors

The literal sum bijection is identified with the actual retained
suffix and the actual right-block permutation. The latter keeps
its original add-commutation count transports.
-/

@[expose] public section

set_option autoImplicit false

namespace CategoryTheory.MonoidalCategory.OrderedTensor

/-- Inversion of original independent finite input bijections retains both inverse inputs. -/
theorem sumInputsEquiv_symm {m m' n n' : ℕ}
    (e : Fin m ≃ Fin m') (d : Fin n ≃ Fin n') :
    (sumInputsEquiv e d).symm = sumInputsEquiv e.symm d.symm := by
  apply Equiv.ext
  intro i
  apply (sumInputsEquiv e d).injective
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [Equiv.apply_symm_apply, sumInputsEquiv_left, sumInputsEquiv_right]

/-- The literal initial-block permutation is the original suffix-extension permutation. -/
theorem sumInputsEquiv_suffix {m : ℕ} (e : Equiv.Perm (Fin m)) (n : ℕ) :
    sumInputsEquiv e (Equiv.refl (Fin n)) = extendPermSuffix e n := by
  apply Equiv.ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [sumInputsEquiv_left, extendPermSuffix_castAdd]
  · rw [sumInputsEquiv_right, extendPermSuffix_natAdd]
    rfl

/-- The literal independent block permutation has its two actual consecutive finite factors. -/
theorem sumInputsEquiv_factor {m n : ℕ}
    (e : Equiv.Perm (Fin m)) (d : Equiv.Perm (Fin n)) :
    sumInputsEquiv e d =
      (extendPermSuffix e n).trans (rightBlockPerm m n d) := by
  apply Equiv.ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Equiv.trans_apply, sumInputsEquiv_left,
      extendPermSuffix_castAdd, rightBlockPerm_castAdd]
  · simp only [Equiv.trans_apply, sumInputsEquiv_right,
      extendPermSuffix_natAdd, rightBlockPerm_natAdd]

/-- The actual permutation group convention applies the original initial factor first. -/
theorem sumInputsEquiv_factor_mul {m n : ℕ}
    (e : Equiv.Perm (Fin m)) (d : Equiv.Perm (Fin n)) :
    sumInputsEquiv e d = rightBlockPerm m n d * extendPermSuffix e n := by
  change sumInputsEquiv e d =
    (extendPermSuffix e n).trans (rightBlockPerm m n d)
  exact sumInputsEquiv_factor e d

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_SumPermutation

/- Source proof segment: SumInputIso -/
section source_SumInputIso
/-!
# Original finite isomorphisms of two heterogeneous input blocks

The complete input bijections and every original object equality
determine the two-block map. Composition is proved before selecting
the original two-block flips.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory TensorReindexing

/-- Every original block object equality occupies its original sum-bijection target slot. -/
theorem sumInputs_objects {m m' n n' : ℕ} {α : Type u}
    (e : Fin m ≃ Fin m') (d : Fin n ≃ Fin n')
    (X : Fin m → α) (Y : Fin n → α) (X' : Fin m' → α) (Y' : Fin n' → α)
    (hX : ∀ i, X i = X' (e i)) (hY : ∀ i, Y i = Y' (d i)) (i : Fin (m + n)) :
    Fin.append X Y i = Fin.append X' Y' (sumInputsEquiv e d i) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [sumInputsEquiv_left, Fin.append_left, Fin.append_left]
    exact hX j
  · rw [sumInputsEquiv_right, Fin.append_right, Fin.append_right]
    exact hY j

/-- The original inverse sum bijection gives the two original inverse-reindexed families. -/
theorem sumInputs_family {m m' n n' : ℕ} {α : Type u}
    (e : Fin m ≃ Fin m') (d : Fin n ≃ Fin n') (X : Fin m → α) (Y : Fin n → α) :
    Fin.append X Y ∘ (sumInputsEquiv e d).symm =
      Fin.append (X ∘ e.symm) (Y ∘ d.symm) :=
  reindexedFamily_eq _ _ _ (sumInputs_objects e d X Y (X ∘ e.symm) (Y ∘ d.symm)
    (fun i => congrArg X (e.symm_apply_apply i).symm)
    (fun i => congrArg Y (d.symm_apply_apply i).symm))

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The actual original sum input map, with its original named target blocks. -/
noncomputable def sumNamedIso {m m' n n' : ℕ}
    (e : Fin m ≃ Fin m') (d : Fin n ≃ Fin n')
    (X : Fin m → C) (Y : Fin n → C) (X' : Fin m' → C) (Y' : Fin n' → C)
    (hX : ∀ i, X i = X' (e i)) (hY : ∀ i, Y i = Y' (d i)) :
    obj (Fin.append X Y) ≅ obj (Fin.append X' Y') :=
  isoEquiv (sumInputsEquiv e d) (fun i => eqToIso (sumInputs_objects e d X Y X' Y' hX hY i))

/-- The sum input isomorphism retains exactly the original whole finite-bijection map. -/
theorem sumNamedIso_hom {m m' n n' : ℕ}
    (e : Fin m ≃ Fin m') (d : Fin n ≃ Fin n')
    (X : Fin m → C) (Y : Fin n → C) (X' : Fin m' → C) (Y' : Fin n' → C)
    (hX : ∀ i, X i = X' (e i)) (hY : ∀ i, Y i = Y' (d i)) :
    (sumNamedIso e d X Y X' Y' hX hY).hom =
      mapEquiv (sumInputsEquiv e d)
        (fun i => eqToHom (sumInputs_objects e d X Y X' Y' hX hY i)) :=
  isoEquiv_hom _ _

set_option backward.isDefEq.respectTransparency false in
/-- The original two named-block input isomorphisms preserve their actual consecutive inputs. -/
theorem sumNamedIso_trans {m m' m'' n n' n'' : ℕ}
    (e : Fin m ≃ Fin m') (e' : Fin m' ≃ Fin m'')
    (d : Fin n ≃ Fin n') (d' : Fin n' ≃ Fin n'')
    (X : Fin m → C) (Y : Fin n → C) (X' : Fin m' → C) (Y' : Fin n' → C)
    (X'' : Fin m'' → C) (Y'' : Fin n'' → C)
    (hX : ∀ i, X i = X' (e i)) (hY : ∀ i, Y i = Y' (d i))
    (kX : ∀ i, X' i = X'' (e' i)) (kY : ∀ i, Y' i = Y'' (d' i)) :
    sumNamedIso e d X Y X' Y' hX hY ≪≫ sumNamedIso e' d' X' Y' X'' Y'' kX kY =
      sumNamedIso (e.trans e') (d.trans d') X Y X'' Y''
        (fun i => (hX i).trans (kX (e i))) (fun i => (hY i).trans (kY (d i))) := by
  unfold sumNamedIso
  rw [isoEquiv_trans]
  exact isoEquiv_congr (sumInputsEquiv_trans e e' d d') _ _
    (fun i => eqToIso_chain_heq
      (sumInputs_objects e d X Y X' Y' hX hY i)
      (sumInputs_objects e' d' X' Y' X'' Y'' kX kY (sumInputsEquiv e d i))
      (sumInputs_objects (e.trans e') (d.trans d') X Y X'' Y''
        (fun j => (hX j).trans (kX (e j))) (fun j => (hY j).trans (kY (d j))) i))

/-- Identity on every original two-block input gives the actual tensor identity. -/
theorem sumNamedIso_refl {m n : ℕ} (X : Fin m → C) (Y : Fin n → C) :
    sumNamedIso (Equiv.refl (Fin m)) (Equiv.refl (Fin n)) X Y X Y
      (fun _ => rfl) (fun _ => rfl) = Iso.refl (obj (Fin.append X Y)) := by
  unfold sumNamedIso
  exact (isoEquiv_eq_congr (sumInputsEquiv_refl m n) _ (fun _ => rfl)).trans
    (isoEquiv_refl_id (Fin.append X Y))

/-- The original independent input bijections with their actual inverse-reindexed blocks. -/
noncomputable def sumInputIso {m m' n n' : ℕ}
    (e : Fin m ≃ Fin m') (d : Fin n ≃ Fin n') (X : Fin m → C) (Y : Fin n → C) :
    obj (Fin.append X Y) ≅ obj (Fin.append (X ∘ e.symm) (Y ∘ d.symm)) :=
  sumNamedIso e d X Y (X ∘ e.symm) (Y ∘ d.symm)
    (fun i => congrArg X (e.symm_apply_apply i).symm)
    (fun i => congrArg Y (d.symm_apply_apply i).symm)

/-- The inverse-block comparison is the actual original sum reindexing and target transport. -/
theorem sumInputIso_reindex {m m' n n' : ℕ}
    (e : Fin m ≃ Fin m') (d : Fin n ≃ Fin n') (X : Fin m → C) (Y : Fin n → C) :
    sumInputIso e d X Y = bijectionIso (sumInputsEquiv e d) (Fin.append X Y) ≪≫
      eqToIso (congrArg obj (sumInputs_family e d X Y)) :=
  isoEquiv_eqToIso _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- At fixed original counts the sum comparison is the actual constructed permutation record. -/
theorem sumInputIso_actual {m n : ℕ}
    (e : Equiv.Perm (Fin m)) (d : Equiv.Perm (Fin n)) (X : Fin m → C) (Y : Fin n → C) :
    sumInputIso e d X Y = comparisonAlong (firstPermutationRecord (sumInputsEquiv e d))
      (Fin.append X Y) (Fin.append (X ∘ e.symm) (Y ∘ d.symm))
        (by exact sumInputs_family e d X Y) :=
  (comparisonAlong_actual _ _ _ _ _).symm

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_SumInputIso

/- Source proof segment: BlockSquareComposition -/
section source_BlockSquareComposition
/-!
# Composing original tensor block squares

The generic identities combine the actual block comparison maps and
the original binary associator naturality square. They carry no
unproved tensor reindexing or flattening premise.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A true block-square equality remains true after tensoring with an unchanged last factor. -/
theorem tensorSquare_right {A B P Q V : C}
    (f : A ⟶ B) (a : A ⟶ P) (b : B ⟶ Q) (g : P ⟶ Q)
    (h : f ≫ b = a ≫ g) :
    (f ⊗ₘ 𝟙 V) ≫ (b ⊗ₘ 𝟙 V) = (a ⊗ₘ 𝟙 V) ≫ (g ⊗ₘ 𝟙 V) := by
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
    Category.id_comp, h]

/-- Composing an actual prefix block square with the original associator
naturality produces the actual successor block square. -/
theorem blockSquare_successor {A B P Q R V : C}
    (f : A ⟶ B) (a : A ⟶ P ⊗ R) (b : B ⟶ Q ⊗ R) (g : P ⟶ Q)
    (h : f ≫ b = a ≫ (g ⊗ₘ 𝟙 R)) :
    (f ⊗ₘ 𝟙 V) ≫ (b ⊗ₘ 𝟙 V) ≫ (α_ Q R V).hom =
      (a ⊗ₘ 𝟙 V) ≫ (α_ P R V).hom ≫ (g ⊗ₘ 𝟙 (R ⊗ V)) := by
  have h₁ := tensorSquare_right (V := V) f a b (g ⊗ₘ 𝟙 R) h
  have h₂ := associator_naturality g (𝟙 R) (𝟙 V)
  simp only [id_tensorHom_id] at h₂
  rw [← Category.assoc, h₁, Category.assoc, h₂]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_BlockSquareComposition

/- Source proof segment: ActualTensorBlockSplitMaps -/
section source_ActualTensorBlockSplitMaps
/-!
# Actual initial-block tensor maps under a retained suffix

The original append split identifies the suffix-extended tensor map
with the original initial tensor comparison tensored with the identity
of the whole retained suffix tensor.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory
open TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [SymmetricCategory C] in
/-- The original suffix-extended record retains exactly its original extended permutation. -/
theorem extendTensorSuffix_perm {n : ℕ} (r : TensorReindexing C n) :
    ∀ m : ℕ, (extendTensorSuffix r m).perm = extendPermSuffix r.perm m
  | 0 => rfl
  | m + 1 => congrArg (extendPerm (n + m)) (extendTensorSuffix_perm r m)

omit [SymmetricCategory C] in
/-- Its original reindexed input family is the reindexed initial block and retained suffix. -/
theorem extendTensorSuffix_family {n m : ℕ} (r : TensorReindexing C n)
    (X : Fin n → C) (Y : Fin m → C) :
    familyEquiv (extendTensorSuffix r m).perm (Fin.append X Y) =
      Fin.append (familyEquiv r.perm X) Y := by
  change Fin.append X Y ∘ (extendTensorSuffix r m).perm.symm = _
  rw [extendTensorSuffix_perm]
  exact append_reindex_extendSuffix r.perm X Y

omit [SymmetricCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- Retaining a whole original suffix intertwines the actual comparison with the original
block split. -/
theorem extendTensorSuffix_append {n : ℕ} (r : TensorReindexing C n) (X : Fin n → C) :
    ∀ {m : ℕ} (Y : Fin m → C),
      HEq
        ((extendTensorSuffix r m).comparison.hom.app (Fin.append X Y) ≫
          eqToHom (congrArg obj (extendTensorSuffix_family r X Y)) ≫
          (appendIso (familyEquiv r.perm X) Y).hom)
        ((appendIso X Y).hom ≫ (r.comparison.hom.app X ⊗ₘ 𝟙 (obj Y))) := by
  intro m
  induction m with
  | zero =>
      intro Y
      have hX : Fin.append X Y = X := append_nil X Y
      have hY : Fin.append (familyEquiv r.perm X) Y = familyEquiv r.perm X :=
        append_nil _ Y
      simp only [extendTensorSuffix, appendIso_zero_hom]
      have hn := rightUnitor_inv_naturality (r.comparison.hom.app X)
      have hmap := r.comparison.hom.naturality (eqToHom hX)
      simp only [eqToHom_map] at hmap
      have hcomp :
          r.comparison.hom.app (Fin.append X Y) ≫
            eqToHom (congrArg obj (extendTensorSuffix_family r X Y)) ≫
            eqToHom (congrArg obj hY) =
          eqToHom (congrArg obj hX) ≫ r.comparison.hom.app X := by
        simpa only [Category.assoc, eqToHom_trans] using hmap.symm
      have hcompUnit := congrArg (· ≫ (ρ_ (obj (familyEquiv r.perm X))).inv) hcomp
      have hn' : r.comparison.hom.app X ≫ (ρ_ (obj (familyEquiv r.perm X))).inv =
          (ρ_ (obj X)).inv ≫ (r.comparison.hom.app X ⊗ₘ 𝟙 (𝟙_ C)) := by
        rw [tensorHom_id]
        exact hn
      have hunit := congrArg (eqToHom (congrArg obj hX) ≫ ·)
        (show r.comparison.hom.app X ≫ (ρ_ (obj (familyEquiv r.perm X))).inv =
          (ρ_ (obj X)).inv ≫ (r.comparison.hom.app X ⊗ₘ 𝟙 (obj Y)) from by
          exact hn')
      simp only [Category.assoc] at hcompUnit hunit
      exact heq_of_eq (by simpa only [Category.assoc] using hcompUnit.trans hunit)
  | succ m ih =>
      intro Y
      have hinit := init_append (m := n) (n := m) X Y
      have hlast := last_append (m := n) (n := m) X Y
      have hrec := ih (Fin.init Y)
      have hExt := extend_hom_app_heq (extendTensorSuffix r m)
        (Fin.append (m := n) (n := m + 1) X Y)
      rw [hinit, hlast] at hExt
      rw [appendIso_succ_hom, appendIso_succ_hom]
      have hrecEq :
          (extendTensorSuffix r m).comparison.hom.app (Fin.append X (Fin.init Y)) ≫
            eqToHom (congrArg obj (extendTensorSuffix_family r X (Fin.init Y))) ≫
            (appendIso (familyEquiv r.perm X) (Fin.init Y)).hom =
          (appendIso X (Fin.init Y)).hom ≫
            (r.comparison.hom.app X ⊗ₘ 𝟙 (obj (Fin.init Y))) :=
        eq_of_heq hrec
      have hs := blockSquare_successor (V := Y (Fin.last m))
        ((extendTensorSuffix r m).comparison.hom.app (Fin.append X (Fin.init Y)))
        (appendIso X (Fin.init Y)).hom
        (eqToHom (congrArg obj (extendTensorSuffix_family r X (Fin.init Y))) ≫
          (appendIso (familyEquiv r.perm X) (Fin.init Y)).hom)
        (r.comparison.hom.app X) hrecEq
      have hSource : obj (Fin.append (m := n) (n := m + 1) X Y) =
          obj (Fin.append X (Fin.init Y)) ⊗ Y (Fin.last m) := append_step X Y
      have hTarget :
          obj (familyEquiv (extendTensorSuffix r (m + 1)).perm
            (Fin.append (m := n) (n := m + 1) X Y)) =
          obj (familyEquiv (extendTensorSuffix r m).perm
            (Fin.append X (Fin.init Y))) ⊗ Y (Fin.last m) := by
        change obj (familyEquiv
          (extendPerm (n + m) (extendTensorSuffix r m).perm)
          (Fin.append (m := n) (n := m + 1) X Y)) = _
        rw [prefixTarget_obj_eq, hinit, hlast]
      have hAppendTarget : HEq
          (eqToHom (congrArg obj (extendTensorSuffix_family r X Y)) ≫
            eqToHom (append_step (familyEquiv r.perm X) Y) ≫
            ((appendIso (familyEquiv r.perm X) (Fin.init Y)).hom ⊗ₘ
              𝟙 (Y (Fin.last m))) ≫
            (α_ (obj (familyEquiv r.perm X)) (obj (Fin.init Y)) (Y (Fin.last m))).hom)
          (((eqToHom (congrArg obj (extendTensorSuffix_family r X (Fin.init Y))) ≫
            (appendIso (familyEquiv r.perm X) (Fin.init Y)).hom) ⊗ₘ
              𝟙 (Y (Fin.last m))) ≫
            (α_ (obj (familyEquiv r.perm X)) (obj (Fin.init Y)) (Y (Fin.last m))).hom) := by
        have hTensor := tensorHom_comp_tensorHom
          (eqToHom (congrArg obj (extendTensorSuffix_family r X (Fin.init Y))))
          (𝟙 (Y (Fin.last m)))
          (appendIso (familyEquiv r.perm X) (Fin.init Y)).hom (𝟙 (Y (Fin.last m)))
        simp only [Category.id_comp] at hTensor
        rw [← hTensor]
        simp only [Category.assoc]
        have hEq :
            eqToHom (congrArg obj (extendTensorSuffix_family r X Y)) ≫
                eqToHom (append_step (familyEquiv r.perm X) Y) =
              eqToHom hTarget ≫
                (eqToHom (congrArg obj (extendTensorSuffix_family r X (Fin.init Y))) ⊗ₘ
                  𝟙 (Y (Fin.last m))) := by
          rw [tensorHom_id]
          have ht := eqToHom_map (tensorRight (Y (Fin.last m)))
            (congrArg obj (extendTensorSuffix_family r X (Fin.init Y)))
          change eqToHom _ ≫ eqToHom _ = eqToHom _ ≫
            (tensorRight (Y (Fin.last m))).map (eqToHom _)
          rw [ht]
          rw [eqToHom_trans, eqToHom_trans]
        have hFull := congrArg
          (· ≫ ((appendIso (familyEquiv r.perm X) (Fin.init Y)).hom ⊗ₘ
            𝟙 (Y (Fin.last m))) ≫
            (α_ (obj (familyEquiv r.perm X)) (obj (Fin.init Y)) (Y (Fin.last m))).hom) hEq
        simp only [Category.assoc] at hFull
        exact (heq_of_eq hFull).trans (eqToHom_comp_heq _ _)
      have hLeft := heq_comp hSource hTarget rfl hExt hAppendTarget
      have hRight : HEq
          ((eqToHom (append_step X Y) ≫
            ((appendIso X (Fin.init Y)).hom ⊗ₘ 𝟙 (Y (Fin.last m))) ≫
            (α_ (obj X) (obj (Fin.init Y)) (Y (Fin.last m))).hom) ≫
            (r.comparison.hom.app X ⊗ₘ 𝟙 (obj Y)))
          (((appendIso X (Fin.init Y)).hom ⊗ₘ 𝟙 (Y (Fin.last m))) ≫
            (α_ (obj X) (obj (Fin.init Y)) (Y (Fin.last m))).hom ≫
            (r.comparison.hom.app X ⊗ₘ 𝟙 (obj (Fin.init Y) ⊗ Y (Fin.last m)))) := by
        simp only [Category.assoc]
        exact eqToHom_comp_heq
          (((appendIso X (Fin.init Y)).hom ⊗ₘ 𝟙 (Y (Fin.last m))) ≫
            (α_ (obj X) (obj (Fin.init Y)) (Y (Fin.last m))).hom ≫
            (r.comparison.hom.app X ⊗ₘ 𝟙 (obj Y)))
          (append_step X Y)
      exact hLeft.trans ((heq_of_eq hs).trans hRight.symm)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ActualTensorBlockSplitMaps

/- Source proof segment: ActualSumSuffix -/
section source_ActualSumSuffix
/-!
# The original actual tensor action under a retained suffix block

The whole extended record is joined to the constructed permutation
homomorphism before projecting its comparison. The resulting square
uses the original heterogeneous append split and its exact target
family transport, including empty blocks.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The original suffix extension is exactly the actual constructed permutation record. -/
theorem actualSuffixRecord_eq {m : ℕ} (e : Equiv.Perm (Fin m)) (n : ℕ) :
    extendTensorSuffix (firstPermutationRecord (C := C) e) n =
      firstPermutationRecord (extendPermSuffix e n) := by
  have hBase : firstPermutationRecord (C := C) e = permutationHom m e :=
    rebaseRecord_eq _ _ (permutationHom_perm m e)
  have hTotal : firstPermutationRecord (C := C) (extendPermSuffix e n) =
      permutationHom (m + n) (extendPermSuffix e n) :=
    rebaseRecord_eq _ _ (permutationHom_perm (m + n) (extendPermSuffix e n))
  exact (congrArg (fun r => extendTensorSuffix r n) hBase).trans
    ((permutationHom_extendSuffix e n).symm.trans hTotal.symm)

set_option backward.isDefEq.respectTransparency false in
/-- The actual suffix-extended input permutation intertwines the original append split. -/
theorem actualSuffix_append {m n : ℕ} (e : Equiv.Perm (Fin m))
    (X : Fin m → C) (Y : Fin n → C) :
    (permutationIso (extendPermSuffix e n) (Fin.append X Y)).hom ≫
        eqToHom (congrArg obj (append_reindex_extendSuffix e X Y)) ≫
          (appendIso (familyEquiv e X) Y).hom =
      (appendIso X Y).hom ≫ ((permutationIso e X).hom ⊗ₘ 𝟙 (obj Y)) := by
  let r := firstPermutationRecord (C := C) e
  let s := extendTensorSuffix r n
  let S := Fin.append X Y
  let T := Fin.append (familyEquiv e X) Y
  have hs : familyEquiv s.perm S = T := extendTensorSuffix_family r X Y
  have ht : familyEquiv (firstPermutationRecord (C := C) (extendPermSuffix e n)).perm S = T :=
    append_reindex_extendSuffix e X Y
  have hAlong := comparisonAlong_congr (actualSuffixRecord_eq (C := C) e n) S T hs ht
  have hOriginal := extendTensorSuffix_append r X Y
  have hSquare :
      (comparisonAlong (firstPermutationRecord (extendPermSuffix e n)) S T ht).hom ≫
          (appendIso (familyEquiv e X) Y).hom =
        (appendIso X Y).hom ≫ (r.comparison.hom.app X ⊗ₘ 𝟙 (obj Y)) := by
    rw [← hAlong, comparisonAlong_hom]
    dsimp only [r, s, S, T] at hOriginal ⊢
    simp only [Category.assoc] at hOriginal ⊢
    exact eq_of_heq hOriginal
  dsimp only [r, S, T] at hSquare
  simpa only [comparisonAlong_hom, firstPermutationRecord_hom_app, Category.assoc] using hSquare

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ActualSumSuffix

/- Source proof segment: SumRecordFactory -/
section source_SumRecordFactory
/-!
# Whole actual records for two original independent block permutations

Actual finite permutation homomorphism multiplication is joined at
the whole-record level. The original named intermediate and final
families are retained before comparison maps are projected.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [Category C] [MonoidalCategory C] [SymmetricCategory C] in
/-- The actual right-block input bijection retains its original inverse-reindexed final block. -/
theorem rightBlock_family {m n : ℕ} (p : Equiv.Perm (Fin n))
    (X : Fin m → C) (Y : Fin n → C) :
    familyEquiv (rightBlockPerm m n p) (Fin.append X Y) =
      Fin.append X (familyEquiv p Y) := by
  have h := sumInputs_family (Equiv.refl (Fin m)) p X Y
  dsimp only [sumInputsEquiv] at h
  rw [← rightBlockPerm_eq_sum] at h
  exact h

/-- The two actual retained block records give their original complete sum-permutation record. -/
theorem actualSumRecord_eq {m n : ℕ}
    (e : Equiv.Perm (Fin m)) (d : Equiv.Perm (Fin n)) :
    firstPermutationRecord (C := C) (rightBlockPerm m n d) *
        firstPermutationRecord (extendPermSuffix e n) =
      firstPermutationRecord (sumInputsEquiv e d) := by
  have hr (p : Equiv.Perm (Fin (m + n))) :
      firstPermutationRecord (C := C) p = permutationHom (m + n) p :=
    rebaseRecord_eq _ _ (permutationHom_perm (m + n) p)
  rw [hr, hr, hr, ← map_mul, ← sumInputsEquiv_factor_mul]

set_option backward.isDefEq.respectTransparency false in
/-- The actual sum comparison is the original two named-block comparison composites. -/
theorem sumInputIso_two_comparisons {m n : ℕ}
    (e : Equiv.Perm (Fin m)) (d : Equiv.Perm (Fin n)) (X : Fin m → C) (Y : Fin n → C) :
    sumInputIso e d X Y =
      comparisonAlong (firstPermutationRecord (extendPermSuffix e n))
        (Fin.append X Y) (Fin.append (familyEquiv e X) Y)
          (by exact append_reindex_extendSuffix e X Y) ≪≫
        comparisonAlong (firstPermutationRecord (rightBlockPerm m n d))
          (Fin.append (familyEquiv e X) Y)
          (Fin.append (familyEquiv e X) (familyEquiv d Y))
            (by exact rightBlock_family d (familyEquiv e X) Y) := by
  let L := firstPermutationRecord (C := C) (extendPermSuffix e n)
  let R := firstPermutationRecord (C := C) (rightBlockPerm m n d)
  let S := Fin.append X Y
  let T := Fin.append (familyEquiv e X) Y
  let V := Fin.append (familyEquiv e X) (familyEquiv d Y)
  have hL : familyEquiv L.perm S = T := append_reindex_extendSuffix e X Y
  have hR : familyEquiv R.perm T = V := rightBlock_family d (familyEquiv e X) Y
  have hComp := comparisonAlong_trans R L S T V hL hR
  have hActual := comparisonAlong_congr (actualSumRecord_eq (C := C) e d) S V
    (comparisonAlong_mul_family R L S T V hL hR)
    (by exact sumInputs_family e d X Y)
  exact (sumInputIso_actual e d X Y).trans (hActual.symm.trans hComp.symm)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_SumRecordFactory

/- Source proof segment: InputIsoThreeFactor -/
section source_InputIsoThreeFactor
/-!
# Original three-step finite input conjugation

The complete input count bijections and original component equalities
are joined before selecting the literal right-block permutation.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- Original consecutive input conjugation factors give the original whole tensor isomorphism. -/
theorem isoEquiv_eq_factor_three {n₀ n₁ n₂ n₃ : ℕ}
    (X₀ : Fin n₀ → C) (X₁ : Fin n₁ → C) (X₂ : Fin n₂ → C) (X₃ : Fin n₃ → C)
    (e₀ : Fin n₀ ≃ Fin n₁) (e₁ : Fin n₁ ≃ Fin n₂) (e₂ : Fin n₂ ≃ Fin n₃)
    (e : Fin n₀ ≃ Fin n₃) (he : e = (e₀.trans e₁).trans e₂)
    (h₀ : ∀ i, X₀ i = X₁ (e₀ i)) (h₁ : ∀ i, X₁ i = X₂ (e₁ i))
    (h₂ : ∀ i, X₂ i = X₃ (e₂ i)) (h : ∀ i, X₀ i = X₃ (e i)) :
    isoEquiv e (fun i => eqToIso (h i)) =
      isoEquiv e₀ (fun i => eqToIso (h₀ i)) ≪≫
        isoEquiv e₁ (fun i => eqToIso (h₁ i)) ≪≫ isoEquiv e₂ (fun i => eqToIso (h₂ i)) := by
  symm
  rw [← Iso.trans_assoc, isoEquiv_eq_trans, isoEquiv_eq_trans]
  exact isoEquiv_eq_congr he.symm _ h

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_InputIsoThreeFactor

/- Source proof segment: InputEqualityIsoInverse -/
section source_InputEqualityIsoInverse
/-!
# Inverting original finite equal-object input isomorphisms

The inverse retains the actual inverse input bijection and the
original target equality transports. Its tensor isomorphism law
follows from actual input composition and identity.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

/-- Original equal-object components determine their actual inverse input components. -/
theorem inverseInputEquality {m n : ℕ} {α : Type u} (e : Fin m ≃ Fin n)
    (X : Fin m → α) (Y : Fin n → α) (h : ∀ i, X i = Y (e i)) (j : Fin n) :
    Y j = X (e.symm j) :=
  (congrArg Y (e.apply_symm_apply j).symm).trans (h (e.symm j)).symm

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- Inversion of original equal-object input isomorphisms retains the actual inverse inputs. -/
theorem isoEquiv_eq_inverse {m n : ℕ} (e : Fin m ≃ Fin n)
    (X : Fin m → C) (Y : Fin n → C) (h : ∀ i, X i = Y (e i)) :
    (isoEquiv e (fun i => eqToIso (h i))).symm =
      isoEquiv e.symm (fun j => eqToIso (inverseInputEquality e X Y h j)) := by
  let F := isoEquiv e (fun i => eqToIso (h i))
  let G := isoEquiv e.symm (fun j => eqToIso (inverseInputEquality e X Y h j))
  have he : e.trans e.symm = Equiv.refl (Fin m) := by
    apply Equiv.ext
    intro i
    exact e.symm_apply_apply i
  have hFG : F ≪≫ G = Iso.refl (obj X) :=
    (isoEquiv_eq_trans e e.symm h (inverseInputEquality e X Y h)).trans
      ((isoEquiv_eq_congr he _ (fun _ => rfl)).trans (isoEquiv_refl_id X))
  simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.trans_refl] using
    (congrArg (fun K : obj X ≅ obj X => F.symm ≪≫ K) hFG).symm

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_InputEqualityIsoInverse

/- Source proof segment: LiteralRightBlockAction -/
section source_LiteralRightBlockAction
/-!
# Literal original right-block tensor action

The original add-commutation count isomorphism conjugates the actual
fixed-first input history. The complete finite input conjugation is
proved before its original append comparison is projected.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [Category C] [MonoidalCategory C] [SymmetricCategory C] in
/-- Original literal append inputs retain their actual prefix-history target inputs. -/
theorem prefixHistory_source_objects {m n : ℕ} (X : Fin m → C) (Y : Fin n → C)
    (i : Fin (m + n)) :
    Fin.append X Y i = prefixHistoryFamily X Y (Fin.cast (Nat.add_comm m n) i) := rfl

/-- The original prefix source isomorphism is its actual finite count/component isomorphism. -/
theorem prefixHistorySource_input {m n : ℕ} (X : Fin m → C) (Y : Fin n → C) :
    isoEquiv (finCongr (Nat.add_comm m n))
        (fun i => eqToIso (prefixHistory_source_objects X Y i)) =
      prefixHistorySourceIso X Y :=
  isoEquiv_finCongr _ _ _ _

/-- The inverse original source isomorphism retains its actual inverse input components. -/
theorem prefixHistorySource_input_symm {m n : ℕ} (X : Fin m → C) (Y : Fin n → C) :
    isoEquiv (finCongr (Nat.add_comm m n)).symm
        (fun i => eqToIso (inverseInputEquality (finCongr (Nat.add_comm m n))
          (Fin.append X Y) (prefixHistoryFamily X Y) (prefixHistory_source_objects X Y) i)) =
      (prefixHistorySourceIso X Y).symm :=
  (isoEquiv_eq_inverse _ _ _ _).symm.trans (congrArg Iso.symm (prefixHistorySource_input X Y))

set_option backward.isDefEq.respectTransparency false in
/-- The actual literal right-block record is the original count-conjugated prefix-history map. -/
theorem literalRightBlock_comparison {m n : ℕ} (p : Equiv.Perm (Fin n))
    (X : Fin m → C) (Y : Fin n → C) :
    comparisonAlong (firstPermutationRecord (rightBlockPerm m n p))
        (Fin.append X Y) (Fin.append X (familyEquiv p Y))
          (by exact rightBlock_family p X Y) =
      prefixHistorySourceIso X Y ≪≫
        comparisonAlong (firstPermutationRecord (extendPermPrefix p m))
          (prefixHistoryFamily X Y) (prefixHistoryFamily X (familyEquiv p Y))
            (actualPrefix_family p X Y) ≪≫
        (prefixHistorySourceIso X (familyEquiv p Y)).symm := by
  let S := Fin.append X Y
  let T := prefixHistoryFamily X Y
  let V := prefixHistoryFamily X (familyEquiv p Y)
  let W := Fin.append X (familyEquiv p Y)
  let P := extendPermPrefix p m
  let hT : T ∘ P.symm = V := by
    have h := prefixHistory_reindex (firstPermutationRecord (C := C) p) X Y
    rw [extendTensorPrefix_perm] at h
    exact h
  let hTV : ∀ i, T i = V (P i) := fun i => by
    have h := congrFun hT (P i)
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using h
  let hSW : ∀ i, S i = W (rightBlockPerm m n p i) := fun i => by
    have h := congrFun (rightBlock_family p X Y) (rightBlockPerm m n p i)
    simpa only [familyEquiv_apply, Equiv.symm_apply_apply] using h
  have he : rightBlockPerm m n p =
      ((finCongr (Nat.add_comm m n)).trans P).trans (finCongr (Nat.add_comm m n)).symm := by
    change (finCongr (Nat.add_comm m n)).trans
        (P.trans (finCongr (Nat.add_comm n m))) = _
    rfl
  have h := isoEquiv_eq_factor_three S T V W
    (finCongr (Nat.add_comm m n)) P (finCongr (Nat.add_comm m n)).symm
    (rightBlockPerm m n p) he (prefixHistory_source_objects X Y) hTV
    (inverseInputEquality (finCongr (Nat.add_comm m n)) W V
      (prefixHistory_source_objects X (familyEquiv p Y))) hSW
  rw [prefixHistorySource_input, prefixHistorySource_input_symm] at h
  have hStart := comparisonAlong_actual (rightBlockPerm m n p) S W hSW
    (by exact rightBlock_family p X Y)
  have hMiddle := comparisonAlong_actual P T V hTV hT
  exact hStart.trans (h.trans (congrArg
    (fun K : obj T ≅ obj V => prefixHistorySourceIso X Y ≪≫ K ≪≫
      (prefixHistorySourceIso X (familyEquiv p Y)).symm) hMiddle.symm))

set_option backward.isDefEq.respectTransparency false in
/-- The actual literal right-block action intertwines the original append split. -/
theorem literalRightBlock_append {m n : ℕ} (p : Equiv.Perm (Fin n))
    (X : Fin m → C) (Y : Fin n → C) :
    (comparisonAlong (firstPermutationRecord (rightBlockPerm m n p))
      (Fin.append X Y) (Fin.append X (familyEquiv p Y))
        (by exact rightBlock_family p X Y)).hom ≫
          (appendIso X (familyEquiv p Y)).hom =
      (appendIso X Y).hom ≫ (𝟙 (obj X) ⊗ₘ (permutationIso p Y).hom) := by
  rw [literalRightBlock_comparison]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  change (prefixHistorySourceIso X Y).hom ≫
    ((comparisonAlong (firstPermutationRecord (extendPermPrefix p m))
      (prefixHistoryFamily X Y) (prefixHistoryFamily X (familyEquiv p Y))
        (actualPrefix_family p X Y)).hom ≫
      (prefixHistoryAppendIso X (familyEquiv p Y)).hom) = _
  rw [actualPrefix_append]
  simp only [prefixHistoryAppendIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_LiteralRightBlockAction

/- Source proof segment: AppendInputTransport -/
section source_AppendInputTransport
/-!
# Transport of original independent append blocks

Both original block family equalities induce their actual whole
append-family transport and the original component tensor transports.
No naturality or coherence outcome is supplied as an assumption.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Whole equalities of two original finite blocks transport the original append split. -/
theorem appendIso_transport_blocks {m n : ℕ} {X X' : Fin m → C} {Y Y' : Fin n → C}
    (hX : X = X') (hY : Y = Y') :
    eqToHom (congrArg obj (congrArg₂ Fin.append hX hY)) ≫ (appendIso X' Y').hom =
      (appendIso X Y).hom ≫ (eqToHom (congrArg obj hX) ⊗ₘ eqToHom (congrArg obj hY)) := by
  cases hX
  cases hY
  simp only [eqToHom_refl, Category.id_comp, id_tensorHom_id, Category.comp_id]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_AppendInputTransport

/- Source proof segment: NamedSumTransport -/
section source_NamedSumTransport
/-!
# Original named target blocks of finite input isomorphisms

The named target block maps are obtained from the actual independent
inverse reindexings and their original target equality transports.
The square is proved for complete input data before specialization.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The original named two-block map retains its actual inverse-family target transports. -/
theorem sumNamedIso_transport {m m' n n' : ℕ}
    (e : Fin m ≃ Fin m') (d : Fin n ≃ Fin n')
    (X : Fin m → C) (Y : Fin n → C) (X' : Fin m' → C) (Y' : Fin n' → C)
    (hX : ∀ i, X i = X' (e i)) (hY : ∀ i, Y i = Y' (d i)) :
    sumNamedIso e d X Y X' Y' hX hY = sumInputIso e d X Y ≪≫
      eqToIso (congrArg obj (congrArg₂ Fin.append
        (reindexedFamily_eq e X X' hX) (reindexedFamily_eq d Y Y' hY))) := by
  unfold sumNamedIso
  rw [isoEquiv_eqToIso, sumInputIso_reindex]
  apply Iso.ext
  simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_NamedSumTransport

/- Source proof segment: NamedSumSquareFactory -/
section source_NamedSumSquareFactory
/-!
# Generic original named-block comparison square

The factory transports a proved original inverse-block square to its
original named target blocks. Its premises are used only as a proof
join; the actual two-block construction supplies the square later.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- Original target equalities transport the complete original inverse-block comparison square. -/
theorem sumNamedIso_square_of_inverse {m m' n n' : ℕ}
    (e : Fin m ≃ Fin m') (d : Fin n ≃ Fin n')
    (X : Fin m → C) (Y : Fin n → C) (X' : Fin m' → C) (Y' : Fin n' → C)
    (hX : ∀ i, X i = X' (e i)) (hY : ∀ i, Y i = Y' (d i))
    (hSquare : (sumInputIso e d X Y).hom ≫
        (appendIso (X ∘ e.symm) (Y ∘ d.symm)).hom =
      (appendIso X Y).hom ≫ ((bijectionIso e X).hom ⊗ₘ (bijectionIso d Y).hom)) :
    (sumNamedIso e d X Y X' Y' hX hY).hom ≫ (appendIso X' Y').hom =
      (appendIso X Y).hom ≫
        ((isoEquiv e (fun i => eqToIso (hX i))).hom ⊗ₘ
          (isoEquiv d (fun i => eqToIso (hY i))).hom) := by
  let hx := reindexedFamily_eq e X X' hX
  let hy := reindexedFamily_eq d Y Y' hY
  rw [sumNamedIso_transport, Iso.trans_hom, eqToIso.hom]
  simp only [Category.assoc]
  rw [appendIso_transport_blocks hx hy]
  rw [← Category.assoc, hSquare]
  rw [Category.assoc, tensorHom_comp_tensorHom]
  rw [isoEquiv_eqToIso, isoEquiv_eqToIso]
  simp only [Iso.trans_hom, eqToIso.hom]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_NamedSumSquareFactory

/- Source proof segment: SumSquareFactory -/
section source_SumSquareFactory
/-!
# Generic join of original two retained-block comparison squares

The actual complete sum record was constructed and proved before this
comparison join. The original left and right block squares are joined
through the original binary tensor composition law.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- Two proved original retained-block squares give the actual original inverse-block square. -/
theorem sumInputIso_square_of_right {m n : ℕ}
    (e : Equiv.Perm (Fin m)) (d : Equiv.Perm (Fin n)) (X : Fin m → C) (Y : Fin n → C)
    (hRight :
      (comparisonAlong (firstPermutationRecord (rightBlockPerm m n d))
        (Fin.append (familyEquiv e X) Y)
        (Fin.append (familyEquiv e X) (familyEquiv d Y))
          (by exact rightBlock_family d (familyEquiv e X) Y)).hom ≫
            (appendIso (familyEquiv e X) (familyEquiv d Y)).hom =
      (appendIso (familyEquiv e X) Y).hom ≫
        (𝟙 (obj (familyEquiv e X)) ⊗ₘ (permutationIso d Y).hom)) :
    (sumInputIso e d X Y).hom ≫ (appendIso (X ∘ e.symm) (Y ∘ d.symm)).hom =
      (appendIso X Y).hom ≫ ((bijectionIso e X).hom ⊗ₘ (bijectionIso d Y).hom) := by
  rw [sumInputIso_two_comparisons, Iso.trans_hom]
  simp only [Category.assoc]
  change (comparisonAlong (firstPermutationRecord (extendPermSuffix e n))
    (Fin.append X Y) (Fin.append (familyEquiv e X) Y)
      (by exact append_reindex_extendSuffix e X Y)).hom ≫
    ((comparisonAlong (firstPermutationRecord (rightBlockPerm m n d))
      (Fin.append (familyEquiv e X) Y)
      (Fin.append (familyEquiv e X) (familyEquiv d Y))
        (by exact rightBlock_family d (familyEquiv e X) Y)).hom ≫
      (appendIso (familyEquiv e X) (familyEquiv d Y)).hom) = _
  rw [hRight]
  rw [← Category.assoc]
  have hLeft := actualSuffix_append e X Y
  have hLeft' :
      (comparisonAlong (firstPermutationRecord (extendPermSuffix e n))
        (Fin.append X Y) (Fin.append (familyEquiv e X) Y)
          (by exact append_reindex_extendSuffix e X Y)).hom ≫
            (appendIso (familyEquiv e X) Y).hom =
      (appendIso X Y).hom ≫ ((permutationIso e X).hom ⊗ₘ 𝟙 (obj Y)) := by
    simpa only [comparisonAlong_hom, firstPermutationRecord_hom_app, Category.assoc] using hLeft
  rw [hLeft', Category.assoc, tensorHom_comp_tensorHom]
  simp only [Category.id_comp, bijectionIso_same]
  have hf : (permutationIso e X).hom ≫ 𝟙 (obj (familyEquiv e X)) =
      (permutationIso e X).hom := Category.comp_id _
  rw [hf]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_SumSquareFactory

/- Source proof segment: ActualSumInputCoherence -/
section source_ActualSumInputCoherence
/-!
# Original independent two-block finite input coherence

Both actual retained-block actions are constructed and proved. Their
complete sum input map intertwines the original append split, for
arbitrary finite counts and heterogeneous block objects.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The actual independent finite input comparison intertwines the original append split. -/
theorem sumInputIso_append_hom {m m' n n' : ℕ}
    (e : Fin m ≃ Fin m') (d : Fin n ≃ Fin n') (X : Fin m → C) (Y : Fin n → C) :
    (sumInputIso e d X Y).hom ≫ (appendIso (X ∘ e.symm) (Y ∘ d.symm)).hom =
      (appendIso X Y).hom ≫ ((bijectionIso e X).hom ⊗ₘ (bijectionIso d Y).hom) := by
  have hm := equiv_arity_eq e
  have hn := equiv_arity_eq d
  cases hm
  cases hn
  exact sumInputIso_square_of_right e d X Y (literalRightBlock_append d (X ∘ e.symm) Y)

/-- The original independent input bijections give their complete original tensor isomorphism. -/
theorem sumInputIso_append {m m' n n' : ℕ}
    (e : Fin m ≃ Fin m') (d : Fin n ≃ Fin n') (X : Fin m → C) (Y : Fin n → C) :
    sumInputIso e d X Y ≪≫ appendIso (X ∘ e.symm) (Y ∘ d.symm) =
      appendIso X Y ≪≫ tensorIso (bijectionIso e X) (bijectionIso d Y) := by
  apply Iso.ext
  exact sumInputIso_append_hom e d X Y

/-- Every original named target block retains its complete original append tensor comparison. -/
theorem sumNamedIso_append_hom {m m' n n' : ℕ}
    (e : Fin m ≃ Fin m') (d : Fin n ≃ Fin n')
    (X : Fin m → C) (Y : Fin n → C) (X' : Fin m' → C) (Y' : Fin n' → C)
    (hX : ∀ i, X i = X' (e i)) (hY : ∀ i, Y i = Y' (d i)) :
    (sumNamedIso e d X Y X' Y' hX hY).hom ≫ (appendIso X' Y').hom =
      (appendIso X Y).hom ≫
        ((isoEquiv e (fun i => eqToIso (hX i))).hom ⊗ₘ
          (isoEquiv d (fun i => eqToIso (hY i))).hom) :=
  sumNamedIso_square_of_inverse e d X Y X' Y' hX hY (sumInputIso_append_hom e d X Y)

/-- The actual complete named two-block map is the original component tensor isomorphism. -/
theorem sumNamedIso_append {m m' n n' : ℕ}
    (e : Fin m ≃ Fin m') (d : Fin n ≃ Fin n')
    (X : Fin m → C) (Y : Fin n → C) (X' : Fin m' → C) (Y' : Fin n' → C)
    (hX : ∀ i, X i = X' (e i)) (hY : ∀ i, Y i = Y' (d i)) :
    sumNamedIso e d X Y X' Y' hX hY ≪≫ appendIso X' Y' =
      appendIso X Y ≪≫ tensorIso (isoEquiv e (fun i => eqToIso (hX i)))
        (isoEquiv d (fun i => eqToIso (hY i))) := by
  apply Iso.ext
  exact sumNamedIso_append_hom e d X Y X' Y' hX hY

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ActualSumInputCoherence

/- Source proof segment: SumTensorMaps -/
section source_SumTensorMaps
/-!
# Original tensor maps of two independent heterogeneous finite blocks

Every original block input bijection and every component morphism is
retained. Their tensor map commutes with the original append split,
using the actual constructed independent-block permutation comparison.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C]

/-- The original component map on the sum of two original input blocks. -/
def sumInputsComponent {m m' n n' : ℕ} {X : Fin m → C} {X' : Fin m' → C}
    {Y : Fin n → C} {Y' : Fin n' → C} {e : Fin m ≃ Fin m'} {d : Fin n ≃ Fin n'}
    (f : ∀ i, X i ⟶ X' (e i)) (g : ∀ j, Y j ⟶ Y' (d j)) :
    (i : Fin (m + n)) → Fin.append X Y i ⟶ Fin.append X' Y' (sumInputsEquiv e d i) :=
  Fin.addCases
    (fun i => eqToHom (Fin.append_left X Y i) ≫ f i ≫
      eqToHom ((congrArg (Fin.append X' Y') (sumInputsEquiv_left e d i)).trans
        (Fin.append_left X' Y' (e i))).symm)
    (fun j => eqToHom (Fin.append_right X Y j) ≫ g j ≫
      eqToHom ((congrArg (Fin.append X' Y') (sumInputsEquiv_right e d j)).trans
        (Fin.append_right X' Y' (d j))).symm)

/-- The sum input map retains every original first-block component. -/
theorem sumInputsComponent_left_heq {m m' n n' : ℕ} {X : Fin m → C} {X' : Fin m' → C}
    {Y : Fin n → C} {Y' : Fin n' → C} {e : Fin m ≃ Fin m'} {d : Fin n ≃ Fin n'}
    (f : ∀ i, X i ⟶ X' (e i)) (g : ∀ j, Y j ⟶ Y' (d j)) (i : Fin m) :
    HEq (sumInputsComponent f g (Fin.castAdd n i)) (f i) := by
  simp only [sumInputsComponent, Fin.addCases_left]
  exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)

/-- The sum input map retains every original second-block component. -/
theorem sumInputsComponent_right_heq {m m' n n' : ℕ} {X : Fin m → C} {X' : Fin m' → C}
    {Y : Fin n → C} {Y' : Fin n' → C} {e : Fin m ≃ Fin m'} {d : Fin n ≃ Fin n'}
    (f : ∀ i, X i ⟶ X' (e i)) (g : ∀ j, Y j ⟶ Y' (d j)) (j : Fin n) :
    HEq (sumInputsComponent f g (Fin.natAdd m j)) (g j) := by
  simp only [sumInputsComponent, Fin.addCases_right]
  exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)

private theorem componentAt_heq {N : ℕ} {A B : Fin N → C}
    (f : ∀ i, A i ⟶ B i) {i j : Fin N} (h : i = j) : HEq (f i) (f j) := by
  cases h
  rfl

variable [MonoidalCategory C] [SymmetricCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- At equal original counts, independent block bijections and all original component maps
give the original append
  square. -/
theorem mapEquiv_sum_same {m n : ℕ} {X X' : Fin m → C} {Y Y' : Fin n → C}
    (e : Equiv.Perm (Fin m)) (d : Equiv.Perm (Fin n))
    (f : ∀ i, X i ⟶ X' (e i)) (g : ∀ j, Y j ⟶ Y' (d j)) :
    mapEquiv (sumInputsEquiv e d) (sumInputsComponent f g) ≫ (appendIso X' Y').hom =
      (appendIso X Y).hom ≫ (mapEquiv e f ⊗ₘ mapEquiv d g) := by
  let p := sumInputsEquiv e d
  let U := X ∘ e.symm
  let V := Y ∘ d.symm
  let F : U ⟶ X' := fun i => f (e.symm i) ≫ eqToHom (congrArg X' (e.apply_symm_apply i))
  let G : V ⟶ Y' := fun j => g (d.symm j) ≫ eqToHom (congrArg Y' (d.apply_symm_apply j))
  let H : Fin.append U V ⟶ Fin.append X' Y' :=
    (appendFamilyFunctor C m n).map (show (U, V) ⟶ (X', Y') from (F, G))
  let R : Fin.append X Y ∘ p.symm ⟶ Fin.append X' Y' := fun i =>
    sumInputsComponent f g (p.symm i) ≫ eqToHom (congrArg (Fin.append X' Y') (p.apply_symm_apply i))
  have hFamilies : Fin.append X Y ∘ p.symm = Fin.append U V := sumInputs_family e d X Y
  have hComponents : ∀ i, HEq (R i) (H i) := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have hpos : p.symm (Fin.castAdd n j) = Fin.castAdd n (e.symm j) := by
        dsimp only [p]
        rw [sumInputsEquiv_symm, sumInputsEquiv_left]
      have hR : HEq (R (Fin.castAdd n j)) (f (e.symm j)) :=
        (comp_eqToHom_heq _ _).trans
          ((componentAt_heq (sumInputsComponent f g) hpos).trans
            (sumInputsComponent_left_heq f g (e.symm j)))
      have hH : HEq (H (Fin.castAdd n j)) (f (e.symm j)) :=
        (appendFamilyFunctor_map_left F G j).trans (comp_eqToHom_heq _ _)
      exact hR.trans hH.symm
    · have hpos : p.symm (Fin.natAdd m j) = Fin.natAdd m (d.symm j) := by
        dsimp only [p]
        rw [sumInputsEquiv_symm, sumInputsEquiv_right]
      have hR : HEq (R (Fin.natAdd m j)) (g (d.symm j)) :=
        (comp_eqToHom_heq _ _).trans
          ((componentAt_heq (sumInputsComponent f g) hpos).trans
            (sumInputsComponent_right_heq f g (d.symm j)))
      have hH : HEq (H (Fin.natAdd m j)) (g (d.symm j)) :=
        (appendFamilyFunctor_map_right F G j).trans (comp_eqToHom_heq _ _)
      exact hR.trans hH.symm
  have hMap : map R = eqToHom (congrArg obj hFamilies) ≫ map H := by
    have hm := map_heq rfl (congrFun hFamilies) (fun _ => rfl) R H hComponents
    have ht := (conj_eqToHom_iff_heq (map R) (map H) (congrArg obj hFamilies) rfl).mpr hm
    simpa only [eqToHom_refl, Category.comp_id] using ht
  have hFactors : mapEquiv p (sumInputsComponent f g) = (sumInputIso e d X Y).hom ≫ map H := by
    rw [mapEquiv_same]
    change (permutationIso p (Fin.append X Y)).hom ≫ map R = _
    rw [hMap]
    rw [sumInputIso_reindex, Iso.trans_hom, bijectionIso_same, eqToIso.hom]
    simp only [Category.assoc]
    rfl
  have hFuse : ((bijectionIso e X).hom ⊗ₘ (bijectionIso d Y).hom) ≫ (map F ⊗ₘ map G) =
      mapEquiv e f ⊗ₘ mapEquiv d g := by
    rw [tensorHom_comp_tensorHom, bijectionIso_same, bijectionIso_same,
      mapEquiv_same, mapEquiv_same]
  have hNat : map H ≫ (appendIso X' Y').hom =
      (appendIso U V).hom ≫ (map F ⊗ₘ map G) := appendIso_naturality F G
  rw [hFactors]
  simp only [Category.assoc]
  rw [hNat]
  rw [← Category.assoc (sumInputIso e d X Y).hom, sumInputIso_append_hom]
  simp only [Category.assoc]
  rw [hFuse]

/-- Arbitrary original finite input counts retain the full independent-block tensor map square. -/
theorem mapEquiv_sum {m m' n n' : ℕ} {X : Fin m → C} {X' : Fin m' → C}
    {Y : Fin n → C} {Y' : Fin n' → C}
    (e : Fin m ≃ Fin m') (d : Fin n ≃ Fin n')
    (f : ∀ i, X i ⟶ X' (e i)) (g : ∀ j, Y j ⟶ Y' (d j)) :
    mapEquiv (sumInputsEquiv e d) (sumInputsComponent f g) ≫ (appendIso X' Y').hom =
      (appendIso X Y).hom ≫ (mapEquiv e f ⊗ₘ mapEquiv d g) := by
  have hm := equiv_arity_eq e
  have hn := equiv_arity_eq d
  cases hm
  cases hn
  exact mapEquiv_sum_same e d f g

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_SumTensorMaps

/- Source proof segment: OrderedBlocks -/
section source_OrderedBlocks
/-!
# Ordered flattening of heterogeneous finite tensor blocks

The flattened tensor and its comparison to the tensor of block tensors
are constructed recursively using the original binary associators and
right unitor. Empty outer and inner blocks are retained.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable (C : Type u)

/-- A finite ordered sequence of finite ordered blocks of objects. -/
inductive Blocks (C : Type u) where
  | nil : Blocks C
  | snoc (initial : Blocks C) {arity : ℕ} (last : Fin arity → C) : Blocks C

namespace Blocks

variable {C}

/-- The number of outer blocks, including blocks with no inputs. -/
def length : Blocks C → ℕ
  | .nil => 0
  | .snoc B _ => B.length + 1

/-- The number of flattened original inputs. -/
def totalArity : Blocks C → ℕ
  | .nil => 0
  | .snoc B (arity := n) _ => B.totalArity + n

/-- Flatten all original inputs in their ordered block sequence. -/
def inputs : (B : Blocks C) → Fin B.totalArity → C
  | .nil => Fin.elim0
  | .snoc B X => Fin.append B.inputs X

/-- Every original flattened input retains its block and its place inside that block. -/
def position : Blocks C → Type
  | .nil => Empty
  | .snoc B (arity := n) _ => B.position ⊕ Fin n

/-- Evaluate an original block-position input in its original object. -/
def atPosition : (B : Blocks C) → B.position → C
  | .nil => Empty.elim
  | .snoc B X => Sum.elim B.atPosition X

/-- The actual bijection from ordered flattened inputs to their original block positions. -/
def positionEquiv : (B : Blocks C) → Fin B.totalArity ≃ B.position
  | .nil => Equiv.equivEmpty (Fin 0)
  | .snoc B _ => finSumFinEquiv.symm.trans
      (Equiv.sumCongr B.positionEquiv (Equiv.refl _))

/-- The flattened ordered family agrees with evaluation at its original block positions. -/
theorem inputs_position : ∀ (B : Blocks C) (i : Fin B.totalArity),
    B.inputs i = B.atPosition (B.positionEquiv i)
  | .nil, i => Fin.elim0 i
  | .snoc B (arity := n) X, i => by
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · change Fin.append B.inputs X (Fin.castAdd n j) =
          Sum.elim B.atPosition X
            (Equiv.sumCongr B.positionEquiv (Equiv.refl (Fin n))
              (finSumFinEquiv.symm (Fin.castAdd n j)))
        rw [Fin.append_left, finSumFinEquiv_symm_apply_castAdd]
        change B.inputs j = B.atPosition (B.positionEquiv j)
        exact inputs_position B j
      · change Fin.append B.inputs X (Fin.natAdd B.totalArity j) =
          Sum.elim B.atPosition X
            (Equiv.sumCongr B.positionEquiv (Equiv.refl (Fin n))
              (finSumFinEquiv.symm (Fin.natAdd B.totalArity j)))
        rw [Fin.append_right, finSumFinEquiv_symm_apply_natAdd]
        rfl

variable [Category.{v} C] [MonoidalCategory C]

/-- The tensor object of each original ordered block. -/
def blockTensors : (B : Blocks C) → Fin B.length → C
  | .nil => Fin.elim0
  | .snoc B X => Fin.snoc B.blockTensors (obj X)

/-- Successor reduction of the original tensor of block tensors. -/
theorem obj_blockTensors_snoc (B : Blocks C) {n : ℕ} (X : Fin n → C) :
    obj (blockTensors (.snoc B X)) = obj B.blockTensors ⊗ obj X := by
  change obj (Fin.snoc B.blockTensors (obj X)) = _
  rw [obj_succ]
  change obj (Fin.init (n := B.length) (@Fin.snoc B.length (fun _ => C)
    B.blockTensors (obj X))) ⊗
    (@Fin.snoc B.length (fun _ => C) B.blockTensors (obj X)) (Fin.last B.length) = _
  rw [Fin.init_snoc, Fin.snoc_last]

/-- Flatten the original block tensor word using the original monoidal maps. -/
def flattenIso : (B : Blocks C) → obj B.inputs ≅ obj B.blockTensors
  | .nil => Iso.refl _
  | .snoc B X => appendIso B.inputs X ≪≫
      tensorIso B.flattenIso (Iso.refl (obj X)) ≪≫
      eqToIso (obj_blockTensors_snoc B X).symm

/-- Empty outer blocks give the original identity of the tensor unit. -/
theorem flattenIso_nil : (flattenIso (.nil : Blocks C)).hom = 𝟙 (𝟙_ C) := rfl

/-- Successor flattening uses exactly the original block split and preceding flattening. -/
theorem flattenIso_snoc_hom (B : Blocks C) {n : ℕ} (X : Fin n → C) :
    (flattenIso (.snoc B X)).hom = (appendIso B.inputs X).hom ≫
      ((flattenIso B).hom ⊗ₘ 𝟙 (obj X)) ≫
      eqToHom (obj_blockTensors_snoc B X).symm := rfl

end Blocks

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedBlocks

/- Source proof segment: OrderedBlocksNaturality -/
section source_OrderedBlocksNaturality
/-!
# Original ordered block tensor flattening is natural

Both the original input morphisms inside every block and the original
block tensors are retained. The flattening squares use the proved
independent-block append naturality and original binary tensor maps.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace Blocks

/-- A componentwise original morphism between ordered block sequences of the same block lengths. -/
inductive Map : Blocks C → Blocks C → Type (max u v)
  | nil : Map .nil .nil
  | snoc {B B' : Blocks C} (f : Map B B') {n : ℕ} {X Y : Fin n → C}
      (g : ∀ i, X i ⟶ Y i) : Map (.snoc B X) (.snoc B' Y)

/-- Original maps on the full flattened tensor inputs. -/
def inputMap : {B B' : Blocks C} → Map B B' →
    (obj B.inputs ⟶ obj B'.inputs)
  | _, _, .nil => 𝟙 _
  | _, _, .snoc (B := B) (B' := B') f (X := X) (Y := Y) g =>
      (appendIso B.inputs X).hom ≫ (inputMap f ⊗ₘ map g) ≫ (appendIso B'.inputs Y).inv

/-- The original map on the ordered tensor of all block tensors. -/
def tensorMap : {B B' : Blocks C} → Map B B' →
    (obj B.blockTensors ⟶ obj B'.blockTensors)
  | _, _, .nil => 𝟙 _
  | _, _, .snoc (B := B) (B' := B') f (X := X) (Y := Y) g =>
      eqToHom (obj_blockTensors_snoc B X) ≫
        (tensorMap f ⊗ₘ map g) ≫ eqToHom (obj_blockTensors_snoc B' Y).symm

set_option backward.isDefEq.respectTransparency false in
/-- Every original ordered block component map commutes with the constructed original flattening. -/
theorem flattenIso_naturality : ∀ {B B' : Blocks C} (f : Map B B'),
    inputMap f ≫ (flattenIso B').hom = (flattenIso B).hom ≫ tensorMap f
  | _, _, .nil => by simp only [inputMap, tensorMap, Category.id_comp, Category.comp_id]
  | _, _, .snoc (B := B) (B' := B') f (X := X) (Y := Y) g => by
      rw [inputMap, tensorMap, flattenIso_snoc_hom, flattenIso_snoc_hom]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc (inputMap f ⊗ₘ map g), tensorHom_comp_tensorHom,
        Category.comp_id, flattenIso_naturality f]
      have ht : (flattenIso B).hom ≫ tensorMap f ⊗ₘ map g =
          ((flattenIso B).hom ⊗ₘ 𝟙 (obj X)) ≫ (tensorMap f ⊗ₘ map g) := by
        simpa only [Category.id_comp] using
          (tensorHom_comp_tensorHom (flattenIso B).hom (𝟙 (obj X))
            (tensorMap f) (map g)).symm
      have he : eqToHom (obj_blockTensors_snoc B X).symm ≫
          eqToHom (obj_blockTensors_snoc B X) = 𝟙 _ := by
        rw [eqToHom_trans]
        rfl
      rw [ht]
      rw [← Category.assoc (eqToHom (obj_blockTensors_snoc B X).symm)
        (eqToHom (obj_blockTensors_snoc B X)), he]
      simp only [Category.id_comp, Category.assoc]

end Blocks

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedBlocksNaturality

/- Source proof segment: OrderedBlocksOriginalMap -/
section source_OrderedBlocksOriginalMap
/-!
# Original component input maps of ordered tensor blocks

The recursively split block input map is identified with the original
componentwise map on the ordered flattened input family, using the
proved original independent-block append naturality.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace Blocks

/-- Equality-recursion transport retains the original term heterogeneously. -/
theorem transport_mpr_heq {α β : Sort u} (h : α = β) (x : β) : HEq (Eq.mpr h x) x := by
  cases h
  rfl

/-- Casting the original input count commutes with an initial-block injection. -/
theorem cast_castAdd {a b n : ℕ} (h : a = b) (j : Fin a) :
    Fin.cast (congrArg (· + n) h) (Fin.castAdd n j) = Fin.castAdd n (Fin.cast h j) := by
  cases h
  rfl

/-- Casting the original input count retains an unchanged final-block input. -/
theorem cast_natAdd {a b n : ℕ} (h : a = b) (j : Fin n) :
    Fin.cast (congrArg (· + n) h) (Fin.natAdd a j) = Fin.natAdd b j := by
  cases h
  rfl

omit [MonoidalCategory C] in
/-- Equal original block lengths give equal original flattened input counts. -/
theorem Map.totalArity_eq : ∀ {B B' : Blocks C} (_f : Map B B'), B.totalArity = B'.totalArity
  | _, _, .nil => rfl
  | _, _, .snoc f (n := n) _ => congrArg (· + n) (Map.totalArity_eq f)

set_option backward.isDefEq.respectTransparency false in
/-- Actual component maps on all original flattened block positions. -/
def Map.components : {B B' : Blocks C} → (f : Map B B') →
    (i : Fin B.totalArity) → B.inputs i ⟶ B'.inputs (Fin.cast f.totalArity_eq i)
  | _, _, .nil, i => i.elim0
  | _, _, .snoc (B := A) (B' := A') f (n := n) (X := X) (Y := Y) g, i => by
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · have hi := cast_castAdd (n := n) f.totalArity_eq j
        rw [hi, inputs, inputs, Fin.append_left, Fin.append_left]
        exact f.components j
      · have hi := cast_natAdd (n := n) f.totalArity_eq j
        rw [hi, inputs, inputs, Fin.append_right, Fin.append_right]
        exact g j

variable [SymmetricCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The original flattened component maps tensor to the constructed ordered input map. -/
theorem Map.inputMap_original : ∀ {B B' : Blocks C} (f : Map B B'),
    inputMap f = mapEquiv (finCongr f.totalArity_eq) f.components := by
  intro B B' f
  induction f with
  | nil =>
      change 𝟙 (𝟙_ C) = mapEquiv (Equiv.refl (Fin 0)) (fun i => i.elim0)
      change 𝟙 (𝟙_ C) = mapEquiv (Equiv.refl (Fin 0))
        (X := Fin.elim0) (Y := Fin.elim0) (fun i => i.elim0)
      rw [mapEquiv_refl]
      rfl
  | @snoc B B' f n X Y g ih =>
      rw [inputMap, ih]
      have aux {a b n : ℕ} (h : a = b) (U : Fin a → C) (V : Fin b → C)
          (F : ∀ i, U i ⟶ V (Fin.cast h i)) (X Y : Fin n → C) (g : ∀ i, X i ⟶ Y i) :
          (appendIso U X).hom ≫ (mapEquiv (finCongr h) F ⊗ₘ map g) ≫
            (appendIso V Y).inv =
          mapEquiv (finCongr (congrArg (· + n) h))
            (fun i => by
              refine Fin.addCases (fun j => ?_) (fun j => ?_) i
              · change Fin.append U X (Fin.castAdd n j) ⟶
                  Fin.append V Y (Fin.cast (congrArg (· + n) h) (Fin.castAdd n j))
                rw [cast_castAdd h, Fin.append_left, Fin.append_left]
                exact F j
              · change Fin.append U X (Fin.natAdd a j) ⟶
                  Fin.append V Y (Fin.cast (congrArg (· + n) h) (Fin.natAdd a j))
                rw [cast_natAdd h, Fin.append_right, Fin.append_right]
                exact g j) := by
        cases h
        change (appendIso U X).hom ≫
          (mapEquiv (Equiv.refl (Fin a)) F ⊗ₘ map g) ≫ (appendIso V Y).inv =
          mapEquiv (Equiv.refl (Fin (a + n))) _
        rw [mapEquiv_refl, mapEquiv_refl]
        have hn := appendIso_naturality F g
        have hmap : (appendFamilyFunctor C a n).map
            (show (U, X) ⟶ (V, Y) from (F, g)) =
            (fun i => by
              refine Fin.addCases (fun j => ?_) (fun j => ?_) i
              · rw [appendFamilyFunctor_obj, appendFamilyFunctor_obj,
                  Fin.append_left, Fin.append_left]
                exact F j
              · rw [appendFamilyFunctor_obj, appendFamilyFunctor_obj,
                  Fin.append_right, Fin.append_right]
                exact g j) := by
          funext i
          refine Fin.addCases (fun j => ?_) (fun j => ?_) i
          · simp only [Fin.addCases_left]
            have h₁ := appendFamilyFunctor_map_left F g j
            have h₂ : HEq
                (by
                  rw [appendFamilyFunctor_obj, appendFamilyFunctor_obj,
                    Fin.append_left, Fin.append_left]
                  exact F j :
                  (appendFamilyFunctor C a n).obj (U, X) (Fin.castAdd n j) ⟶
                    (appendFamilyFunctor C a n).obj (V, Y) (Fin.castAdd n j)) (F j) := by
              exact (transport_mpr_heq _ _).trans
                ((transport_mpr_heq _ _).trans
                  ((transport_mpr_heq _ _).trans (transport_mpr_heq _ _)))
            exact eq_of_heq (h₁.trans h₂.symm)
          · simp only [Fin.addCases_right]
            have h₁ := appendFamilyFunctor_map_right F g j
            have h₂ : HEq
                (by
                  rw [appendFamilyFunctor_obj, appendFamilyFunctor_obj,
                    Fin.append_right, Fin.append_right]
                  exact g j :
                  (appendFamilyFunctor C a n).obj (U, X) (Fin.natAdd a j) ⟶
                    (appendFamilyFunctor C a n).obj (V, Y) (Fin.natAdd a j)) (g j) := by
              exact (transport_mpr_heq _ _).trans
                ((transport_mpr_heq _ _).trans
                  ((transport_mpr_heq _ _).trans (transport_mpr_heq _ _)))
            exact eq_of_heq (h₁.trans h₂.symm)
        rw [hmap] at hn
        apply (cancel_mono (appendIso V Y).hom).1
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        exact hn.symm
      exact aux f.totalArity_eq B.inputs B'.inputs f.components X Y g

end Blocks

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedBlocksOriginalMap

/- Source proof segment: OrderedBlockTensorMap -/
section source_OrderedBlockTensorMap
/-!
# Original maps on the tensor of ordered block tensors

The blockwise comparison map is identified with the original ordered
componentwise tensor map of all original inner block maps.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

namespace Blocks

/-- Original component maps on a snoc family, with their actual slot transports. -/
def snocMap {a : ℕ} {U V : Fin a → C} {A D : C}
    (F : ∀ i, U i ⟶ V i) (k : A ⟶ D) :
    (∀ i : Fin (a + 1), (@Fin.snoc a (fun _ => C) U A) i ⟶
      (@Fin.snoc a (fun _ => C) V D) i) :=
  Fin.lastCases (by rw [Fin.snoc_last, Fin.snoc_last]; exact k)
    (fun j => by rw [Fin.snoc_castSucc, Fin.snoc_castSucc]; exact F j)

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The original last snoc component is retained heterogeneously. -/
theorem snocMap_last_heq {a : ℕ} {U V : Fin a → C} {A D : C}
    (F : ∀ i, U i ⟶ V i) (k : A ⟶ D) : HEq (snocMap F k (Fin.last a)) k := by
  simp only [snocMap, Fin.lastCases_last]
  exact (transport_mpr_heq _ _).trans (transport_mpr_heq _ _)

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- Every original initial snoc component is retained heterogeneously. -/
theorem snocMap_castSucc_heq {a : ℕ} {U V : Fin a → C} {A D : C}
    (F : ∀ i, U i ⟶ V i) (k : A ⟶ D) (j : Fin a) : HEq (snocMap F k j.castSucc) (F j) := by
  simp only [snocMap, Fin.lastCases_castSucc]
  exact (transport_mpr_heq _ _).trans (transport_mpr_heq _ _)

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- Original block maps preserve the original outer block count. -/
theorem Map.length_eq : ∀ {B B' : Blocks C} (_f : Map B B'), B.length = B'.length
  | _, _, .nil => rfl
  | _, _, .snoc f _ => congrArg (· + 1) (Map.length_eq f)

set_option backward.isDefEq.respectTransparency false in
/-- Every original ordered block map induces its original tensor map as an outer component. -/
def Map.tensorComponents : {B B' : Blocks C} → (f : Map B B') →
    (i : Fin B.length) → B.blockTensors i ⟶ B'.blockTensors (Fin.cast f.length_eq i)
  | _, _, .nil, i => i.elim0
  | _, _, .snoc (B := B) (B' := B') f (X := X) (Y := Y) g, i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have hi : Fin.cast (congrArg (· + 1) f.length_eq) (Fin.last B.length) =
            Fin.last B'.length := by
          have aux {a b : ℕ} (h : a = b) : Fin.cast (congrArg (· + 1) h) (Fin.last a) =
              Fin.last b := by cases h; rfl
          exact aux f.length_eq
        rw [hi, blockTensors, blockTensors, Fin.snoc_last, Fin.snoc_last]
        exact map g
      · have hi : Fin.cast (congrArg (· + 1) f.length_eq) j.castSucc =
            (Fin.cast f.length_eq j).castSucc := cast_castAdd (n := 1) f.length_eq j
        rw [hi, blockTensors, blockTensors, Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact f.tensorComponents j

set_option backward.isDefEq.respectTransparency false in
/-- The original outer snoc component tensor map retains its original count transport and
arbitrary last component. -/
theorem snocTensor_mapEquiv {a b : ℕ} (h : a = b) (U : Fin a → C) (V : Fin b → C)
    (F : ∀ i, U i ⟶ V (Fin.cast h i)) (A D : C) (k : A ⟶ D) :
    eqToHom (show obj (Fin.snoc U A) = obj U ⊗ A from by
      rw [obj_succ]; simp only [Fin.snoc_castSucc, Fin.snoc_last]) ≫
      (mapEquiv (finCongr h) F ⊗ₘ k) ≫
      eqToHom (show obj V ⊗ D = obj (Fin.snoc V D) from by
        rw [obj_succ]; simp only [Fin.snoc_castSucc, Fin.snoc_last]) =
    mapEquiv (finCongr (congrArg (· + 1) h))
      (X := Fin.snoc U A) (Y := Fin.snoc V D) (by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · have hc : Fin.cast (congrArg (· + 1) h) (Fin.last a) = Fin.last b := by
            cases h
            rfl
          change (@Fin.snoc a (fun _ => C) U A) (Fin.last a) ⟶
            (@Fin.snoc b (fun _ => C) V D) (Fin.cast (congrArg (· + 1) h) (Fin.last a))
          rw [hc, Fin.snoc_last, Fin.snoc_last]
          exact k
        · change (@Fin.snoc a (fun _ => C) U A) j.castSucc ⟶
            (@Fin.snoc b (fun _ => C) V D) (Fin.cast (congrArg (· + 1) h) j.castSucc)
          have hc : Fin.cast (congrArg (· + 1) h) j.castSucc =
              (Fin.cast h j).castSucc := by
            cases h
            rfl
          rw [hc, Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact F j) := by
  cases h
  change ∀ i : Fin a, U i ⟶ V i at F
  change eqToHom _ ≫ (mapEquiv (Equiv.refl (Fin a)) F ⊗ₘ k) ≫ eqToHom _ =
    mapEquiv (Equiv.refl (Fin (a + 1))) _
  rw [mapEquiv_refl, mapEquiv_refl]
  have hs : map (snocMap F k) =
      eqToHom (show obj (Fin.snoc U A) = obj U ⊗ A from by
        rw [obj_succ]; simp only [Fin.snoc_castSucc, Fin.snoc_last]) ≫
        (map F ⊗ₘ k) ≫
        eqToHom (show obj V ⊗ D = obj (Fin.snoc V D) from by
          rw [obj_succ]; simp only [Fin.snoc_castSucc, Fin.snoc_last]) := by
    have hh := map_succ_heq
      (show Fin.init (Fin.snoc U A) = U from Fin.init_snoc _ _)
      (show Fin.init (Fin.snoc V D) = V from Fin.init_snoc _ _)
      (Fin.snoc_last _ _) (Fin.snoc_last _ _) (snocMap F k) F k
      (snocMap_castSucc_heq F k) (snocMap_last_heq F k)
    exact eq_of_heq (hh.trans ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).symm)
  rw [← hs]
  apply congrArg (fun h => map h)
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.lastCases_last]
    exact eq_of_heq ((snocMap_last_heq F k).trans
      (((transport_mpr_heq _ _).trans ((transport_mpr_heq _ _).trans
        (transport_mpr_heq _ _))).symm))
  · simp only [Fin.lastCases_castSucc]
    exact eq_of_heq ((snocMap_castSucc_heq F k j).trans
      (((transport_mpr_heq _ _).trans ((transport_mpr_heq _ _).trans
        (transport_mpr_heq _ _))).symm))

set_option backward.isDefEq.respectTransparency false in
/-- Tensoring original outer components gives the constructed original block tensor map. -/
theorem Map.tensorMap_original : ∀ {B B' : Blocks C} (f : Map B B'),
    tensorMap f = mapEquiv (finCongr f.length_eq) f.tensorComponents := by
  intro B B' f
  induction f with
  | nil =>
      change 𝟙 (𝟙_ C) = mapEquiv (Equiv.refl (Fin 0))
        (X := Fin.elim0) (Y := Fin.elim0) (fun i => i.elim0)
      rw [mapEquiv_refl]
      rfl
  | @snoc B B' f n X Y g ih =>
      rw [tensorMap, ih]
      exact snocTensor_mapEquiv f.length_eq B.blockTensors B'.blockTensors
        f.tensorComponents (obj X) (obj Y)
        (map g)

end Blocks

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedBlockTensorMap

/- Source proof segment: FiberTensorBlocks -/
section source_FiberTensorBlocks
/-!
# Actual tensor maps on every original ordered block fiber

Each original inner block has its own finite input bijection and all
of its original component morphisms. The actual flattened word map
commutes with the original ordered block flattening.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C]

namespace Blocks

/-- An original map on every ordered block fiber, with its actual finite input bijection. -/
inductive FiberMap : Blocks C → Blocks C → Type (max u v)
  | nil : FiberMap .nil .nil
  | snoc {B B' : Blocks C} (f : FiberMap B B') {m n : ℕ} {X : Fin m → C} {Y : Fin n → C}
      (e : Fin m ≃ Fin n) (g : ∀ i, X i ⟶ Y (e i)) : FiberMap (.snoc B X) (.snoc B' Y)

/-- The original ordered outer block count is retained by the fiber map. -/
theorem FiberMap.length_eq : ∀ {B B' : Blocks C} (_f : FiberMap B B'), B.length = B'.length
  | _, _, .nil => rfl
  | _, _, .snoc f _ _ => congrArg (· + 1) (FiberMap.length_eq f)

/-- The actual bijection of all original flattened fiber inputs. -/
def FiberMap.inputEquiv : {B B' : Blocks C} → (f : FiberMap B B') →
    Fin B.totalArity ≃ Fin B'.totalArity
  | _, _, .nil => Equiv.refl _
  | _, _, .snoc f e _ => sumInputsEquiv f.inputEquiv e

/-- All original flattened component maps are retained at their actual fiber-input targets. -/
def FiberMap.inputComponents : {B B' : Blocks C} → (f : FiberMap B B') →
    (i : Fin B.totalArity) → B.inputs i ⟶ B'.inputs (f.inputEquiv i)
  | _, _, .nil, i => i.elim0
  | _, _, .snoc f _ g, i => sumInputsComponent f.inputComponents g i

variable [MonoidalCategory C] [SymmetricCategory C]

/-- The actual original tensor map of every flattened fiber input. -/
noncomputable def FiberMap.inputMap {B B' : Blocks C} (f : FiberMap B B') :
    obj B.inputs ⟶ obj B'.inputs :=
  mapEquiv f.inputEquiv f.inputComponents

set_option backward.isDefEq.respectTransparency false in
/-- Each original block tensor map occupies its original outer component slot. -/
noncomputable def FiberMap.tensorComponents : {B B' : Blocks C} → (f : FiberMap B B') →
    (i : Fin B.length) → B.blockTensors i ⟶ B'.blockTensors (Fin.cast f.length_eq i)
  | _, _, .nil, i => i.elim0
  | _, _, .snoc (B := B) (B' := B') f (X := X) (Y := Y) e g, i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have hi : Fin.cast (congrArg (· + 1) f.length_eq) (Fin.last B.length) =
            Fin.last B'.length := by
          have aux {a b : ℕ} (h : a = b) : Fin.cast (congrArg (· + 1) h) (Fin.last a) =
              Fin.last b := by cases h; rfl
          exact aux f.length_eq
        rw [hi, blockTensors, blockTensors, Fin.snoc_last, Fin.snoc_last]
        exact mapEquiv e g
      · have hi : Fin.cast (congrArg (· + 1) f.length_eq) j.castSucc =
            (Fin.cast f.length_eq j).castSucc := cast_castAdd (n := 1) f.length_eq j
        rw [hi, blockTensors, blockTensors, Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact f.tensorComponents j

/-- The original outer component tensor map of the actual inner block tensor maps. -/
noncomputable def FiberMap.tensorMap {B B' : Blocks C} (f : FiberMap B B') :
    obj B.blockTensors ⟶ obj B'.blockTensors :=
  mapEquiv (finCongr f.length_eq) f.tensorComponents

set_option backward.isDefEq.respectTransparency false in
/-- The actual flattened input bijection map retains the original two-block split at each
original fiber. -/
theorem FiberMap.inputMap_snoc {B B' : Blocks C} (f : FiberMap B B') {m n : ℕ}
    {X : Fin m → C} {Y : Fin n → C} (e : Fin m ≃ Fin n) (g : ∀ i, X i ⟶ Y (e i)) :
    (FiberMap.snoc f e g).inputMap =
      (appendIso B.inputs X).hom ≫ (f.inputMap ⊗ₘ mapEquiv e g) ≫ (appendIso B'.inputs Y).inv := by
  apply (cancel_mono (appendIso B'.inputs Y).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact mapEquiv_sum f.inputEquiv e f.inputComponents g

set_option backward.isDefEq.respectTransparency false in
/-- The actual outer block tensor map has its original snoc tensor computation. -/
theorem FiberMap.tensorMap_snoc {B B' : Blocks C} (f : FiberMap B B') {m n : ℕ}
    {X : Fin m → C} {Y : Fin n → C} (e : Fin m ≃ Fin n) (g : ∀ i, X i ⟶ Y (e i)) :
    (FiberMap.snoc f e g).tensorMap =
      eqToHom (obj_blockTensors_snoc B X) ≫ (f.tensorMap ⊗ₘ mapEquiv e g) ≫
        eqToHom (obj_blockTensors_snoc B' Y).symm :=
  (snocTensor_mapEquiv f.length_eq B.blockTensors B'.blockTensors f.tensorComponents
    (obj X) (obj Y) (mapEquiv e g)).symm

set_option backward.isDefEq.respectTransparency false in
/-- Every original inner input bijection and every original component map commute with
original block flattening. -/
theorem FiberMap.flatten_naturality : ∀ {B B' : Blocks C} (f : FiberMap B B'),
    f.inputMap ≫ (flattenIso B').hom = (flattenIso B).hom ≫ f.tensorMap
  | _, _, .nil => by
      change mapEquiv (Equiv.refl (Fin 0)) (X := Fin.elim0) (Y := Fin.elim0)
        (fun i => i.elim0) ≫ 𝟙 _ = 𝟙 _ ≫
          mapEquiv (Equiv.refl (Fin 0)) (X := Fin.elim0) (Y := Fin.elim0) (fun i => i.elim0)
      rw [Category.id_comp, Category.comp_id]
  | _, _, .snoc (B := B) (B' := B') f (X := X) (Y := Y) e g => by
      rw [FiberMap.inputMap_snoc, FiberMap.tensorMap_snoc, flattenIso_snoc_hom,
        flattenIso_snoc_hom]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc (f.inputMap ⊗ₘ mapEquiv e g), tensorHom_comp_tensorHom,
        Category.comp_id, FiberMap.flatten_naturality f]
      have ht : ((flattenIso B).hom ≫ f.tensorMap) ⊗ₘ mapEquiv e g =
          ((flattenIso B).hom ⊗ₘ 𝟙 (obj X)) ≫ (f.tensorMap ⊗ₘ mapEquiv e g) := by
        simpa only [Category.id_comp] using
          (tensorHom_comp_tensorHom (flattenIso B).hom (𝟙 (obj X))
            f.tensorMap (mapEquiv e g)).symm
      have he : eqToHom (obj_blockTensors_snoc B X).symm ≫
          eqToHom (obj_blockTensors_snoc B X) = 𝟙 _ := by
        rw [eqToHom_trans]
        rfl
      rw [ht]
      rw [← Category.assoc (eqToHom (obj_blockTensors_snoc B X).symm)
        (eqToHom (obj_blockTensors_snoc B X)), he]
      simp only [Category.id_comp, Category.assoc]

end Blocks

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FiberTensorBlocks

/- Source proof segment: FiniteTensorBlocks -/
section source_FiniteTensorBlocks
/-!
# The original finite family as an ordered sequence of original input blocks

The outer finite inputs and every inner finite input type retain their
chosen original enumeration. The ordered block flattening supplies
the actual tensor comparison for these block words.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u}

/-- Enumerate an ordered outer family of original finite input blocks. -/
noncomputable def blocksOfFamily : {n : ℕ} → (Fin n → FiniteFamily C) → Blocks C
  | 0, _ => .nil
  | n + 1, X => .snoc (blocksOfFamily (Fin.init X)) (orderedFamily (X (Fin.last n)))

/-- Every original outer block, including an empty input block, is retained. -/
theorem blocksOfFamily_length : ∀ {n : ℕ} (X : Fin n → FiniteFamily C),
    (blocksOfFamily X).length = n
  | 0, _ => rfl
  | _n + 1, X => congrArg (· + 1) (blocksOfFamily_length (Fin.init X))

variable [Category.{v} C] [MonoidalCategory C]

/-- The tensor of block tensors of the original family agrees with
the original ordered outer tensor of its produced inner carriers. -/
theorem blocksOfFamily_tensors : ∀ {n : ℕ} (X : Fin n → FiniteFamily C),
    obj (blocksOfFamily X).blockTensors = obj (fun i => finiteObj (X i))
  | 0, _ => rfl
  | n + 1, X => by
      rw [blocksOfFamily, Blocks.obj_blockTensors_snoc, blocksOfFamily_tensors]
      rfl

/-- The actual flattened original input word is isomorphic to the
ordered tensor of all original finite-block tensor carriers. -/
noncomputable def blocksOfFamilyIso {n : ℕ} (X : Fin n → FiniteFamily C) :
    obj (blocksOfFamily X).inputs ≅ obj (fun i => finiteObj (X i)) :=
  (blocksOfFamily X).flattenIso ≪≫ eqToIso (blocksOfFamily_tensors X)

/-- The original finite outer family provides its ordered inner-block word. -/
noncomputable def blocksOfFiniteFamily (X : FiniteFamily (FiniteFamily C)) : Blocks C :=
  blocksOfFamily (X.obj ∘ enumeration X)

/-- The produced original outer tensor carrier of the actual inner
tensor carriers is the endpoint of the constructed block-word flattening. -/
noncomputable def finiteFamilyBlocksIso (X : FiniteFamily (FiniteFamily C)) :
    obj (blocksOfFiniteFamily X).inputs ≅
      finiteObj (⟨X.index, fun i => finiteObj (X.obj i)⟩ : FiniteFamily C) :=
  blocksOfFamilyIso (X.obj ∘ enumeration X)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FiniteTensorBlocks

/- Source proof segment: FiniteBlockPositions -/
section source_FiniteBlockPositions
/-!
# Original input positions of the finite-block tensor word

The recursively flattened block positions are equivalent to the
actual dependent sum of original inner input types. Every input
object is retained under this equivalence.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

variable {C : Type u}

/-- The original inner input positions of an ordered outer finite family. -/
def OriginalPositions {n : ℕ} (X : Fin n → FiniteFamily C) : Type :=
  Σ i : Fin n, (X i).index

/-- Add a last original block to the dependent sum of original input positions. -/
noncomputable def positionsSnocEquiv {n : ℕ} (X : Fin (n + 1) → FiniteFamily C) :
    OriginalPositions (Fin.init X) ⊕ (X (Fin.last n)).index ≃ OriginalPositions X where
  toFun z := match z with
    | .inl z => ⟨z.1.castSucc, z.2⟩
    | .inr z => ⟨Fin.last n, z⟩
  invFun z := Fin.lastCases
    (fun p : (X (Fin.last n)).index => Sum.inr p)
    (fun i => fun p : (X i.castSucc).index =>
      Sum.inl (⟨i, p⟩ : OriginalPositions (Fin.init X))) z.1 z.2
  left_inv z := by
    cases z with
    | inl z => cases z; simp only [Fin.lastCases_castSucc]
    | inr z => simp only [Fin.lastCases_last]
  right_inv z := by
    cases z with
    | mk i z =>
      refine Fin.lastCases ?_ (fun j => ?_) i z
      · intro z
        simp only [Fin.lastCases_last]
        rfl
      · intro z
        simp only [Fin.lastCases_castSucc]
        rfl

/-- The actual equivalence from recursive block positions to original inner input positions. -/
noncomputable def blockPositionsEquiv : {n : ℕ} → (X : Fin n → FiniteFamily C) →
    (blocksOfFamily X).position ≃ OriginalPositions X
  | 0, X =>
      haveI : IsEmpty (OriginalPositions X) := ⟨fun p => p.1.elim0⟩
      (Equiv.equivEmpty (OriginalPositions X)).symm
  | n + 1, X =>
      (Equiv.sumCongr (blockPositionsEquiv (Fin.init X))
        (enumeration (X (Fin.last n)))).trans (positionsSnocEquiv X)

/-- Original input objects are retained by the actual block-position equivalence. -/
theorem blockPositions_objects : ∀ {n : ℕ} (X : Fin n → FiniteFamily C)
    (p : (blocksOfFamily X).position),
    (blocksOfFamily X).atPosition p =
      (X (blockPositionsEquiv X p).1).obj (blockPositionsEquiv X p).2
  | 0, _, p => Empty.elim p
  | n + 1, X, p => by
      cases p with
      | inl p =>
          dsimp only [blocksOfFamily, Blocks.atPosition, blockPositionsEquiv,
            positionsSnocEquiv, Equiv.trans_apply, Equiv.sumCongr_apply]
          change (blocksOfFamily (Fin.init X)).atPosition p =
            ((Fin.init X) (blockPositionsEquiv (Fin.init X) p).1).obj
              (blockPositionsEquiv (Fin.init X) p).2
          exact blockPositions_objects (Fin.init X) p
      | inr p =>
          dsimp only [blocksOfFamily, Blocks.atPosition, blockPositionsEquiv,
            positionsSnocEquiv, Equiv.trans_apply, Equiv.sumCongr_apply]
          rfl

/-- The actual bijection from the full ordered input word to its original inner positions. -/
noncomputable def flattenedPositionsEquiv {n : ℕ} (X : Fin n → FiniteFamily C) :
    Fin (blocksOfFamily X).totalArity ≃ OriginalPositions X :=
  (blocksOfFamily X).positionEquiv.trans (blockPositionsEquiv X)

/-- Every ordered flattened tensor input is its original inner input object. -/
theorem flattenedPositions_objects {n : ℕ} (X : Fin n → FiniteFamily C)
    (i : Fin (blocksOfFamily X).totalArity) :
    (blocksOfFamily X).inputs i =
      (X (flattenedPositionsEquiv X i).1).obj (flattenedPositionsEquiv X i).2 :=
  ((blocksOfFamily X).inputs_position i).trans
    (blockPositions_objects X ((blocksOfFamily X).positionEquiv i))

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FiniteBlockPositions

/- Source proof segment: FiniteTensorFunctor -/
section source_FiniteTensorFunctor
/-!
# The actual binary tensor functor on finite object families

The functor uses the original input enumeration and original
finite-family morphisms. Its identity and composition laws follow
from the constructed finite permutation action and original
component tensor maps.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The original normalized identity component is the original object identity. -/
theorem enumeratedMap_id_heq (X : FiniteFamily C) (i : Fin (arity X)) :
    HEq (enumeratedMap (𝟙 X) i) (𝟙 (orderedFamily X i)) :=
  enumeratedMap_heq (𝟙 X) i

/-- Original finite-family identities give the original tensor identity. -/
theorem finiteMap_id (X : FiniteFamily C) : finiteMap (𝟙 X) = 𝟙 (finiteObj X) := by
  change mapEquiv (enumeratedEquiv (𝟙 X)) (enumeratedMap (𝟙 X)) = _
  have h := mapEquiv_congr (enumeratedEquiv_id X) (enumeratedMap (𝟙 X))
    (fun i => 𝟙 (orderedFamily X i)) (enumeratedMap_id_heq X)
  exact h.trans (mapEquiv_id (orderedFamily X))

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The original normalized composite components retain the actual consecutive component maps. -/
theorem enumeratedMap_comp_heq {X Y Z : FiniteFamily C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (i : Fin (arity X)) :
    HEq (enumeratedMap (f ≫ g) i)
      (enumeratedMap f i ≫ enumeratedMap g (enumeratedEquiv f i)) := by
  have hf := enumeratedMap_heq f i
  have hg := enumeratedMap_heq g (enumeratedEquiv f i)
  have hidx : enumeration Y (enumeratedEquiv f i) = f.equiv (enumeration X i) :=
    (enumeration Y).apply_symm_apply _
  have hg' : HEq (enumeratedMap g (enumeratedEquiv f i))
      (g.hom (f.equiv (enumeration X i))) := by
    rw [hidx] at hg
    exact hg
  have htarget : orderedFamily Z (enumeratedEquiv g (enumeratedEquiv f i)) =
      Z.obj (g.equiv (f.equiv (enumeration X i))) := by
    have h := orderedFamily_enumeratedEquiv g (enumeratedEquiv f i)
    rw [hidx] at h
    exact h
  have hcomp := heq_comp rfl (orderedFamily_enumeratedEquiv f i) htarget hf hg'
  exact (enumeratedMap_heq (f ≫ g) i).trans hcomp.symm

/-- Original finite-family composition gives composition of the original tensor maps. -/
theorem finiteMap_comp {X Y Z : FiniteFamily C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    finiteMap (f ≫ g) = finiteMap f ≫ finiteMap g := by
  change mapEquiv (enumeratedEquiv (f ≫ g)) (enumeratedMap (f ≫ g)) = _
  have h := mapEquiv_congr (enumeratedEquiv_comp f g) (enumeratedMap (f ≫ g))
    (fun i => enumeratedMap f i ≫ enumeratedMap g (enumeratedEquiv f i))
    (enumeratedMap_comp_heq f g)
  exact h.trans (mapEquiv_comp (enumeratedEquiv f) (enumeratedEquiv g)
    (enumeratedMap f) (enumeratedMap g)).symm

/-- The actual finite-family tensor functor produced from the original binary symmetric tensor. -/
noncomputable def finiteTensorFunctor : FiniteFamily C ⥤ C where
  obj := finiteObj
  map := finiteMap
  map_id := finiteMap_id
  map_comp := finiteMap_comp

/-- Exact object readback of the produced original finite tensor functor. -/
theorem finiteTensorFunctor_obj (X : FiniteFamily C) :
    finiteTensorFunctor.obj X = obj (X.obj ∘ enumeration X) := rfl

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FiniteTensorFunctor

/- Source proof segment: OrderedFiniteFiberMaps -/
section source_OrderedFiniteFiberMaps
/-!
# Original finite-family maps in every ordered tensor block

The original finite index bijection and all component morphisms of
each inner family produce the actual flattened word map. Every
original inner position is retained by the map comparison.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C]

/-- The actual ordered block fiber map of every original inner finite-family morphism. -/
noncomputable def blocksOfFamilyFiberMap : {n : ℕ} → {X Y : Fin n → FiniteFamily C} →
    (∀ i, X i ⟶ Y i) → Blocks.FiberMap (blocksOfFamily X) (blocksOfFamily Y)
  | 0, _, _, _ => .nil
  | n + 1, _, _, f => .snoc (blocksOfFamilyFiberMap (fun i : Fin n => f i.castSucc))
      (enumeratedEquiv (f (Fin.last n))) (enumeratedMap (f (Fin.last n)))

/-- The original inner input bijections act in their original fixed outer slots. -/
def innerInputEquiv {n : ℕ} {X Y : Fin n → FiniteFamily C} (f : ∀ i, X i ⟶ Y i) :
    OriginalPositions X ≃ OriginalPositions Y := Equiv.sigmaCongrRight (fun i => (f i).equiv)

omit [Category.{v} C] in
/-- Every input of the original initial blocks retains its original outer and inner position. -/
theorem flattenedPositions_left {n : ℕ} (X : Fin (n + 1) → FiniteFamily C)
    (i : Fin (blocksOfFamily (Fin.init X)).totalArity) :
    flattenedPositionsEquiv X (Fin.castAdd (arity (X (Fin.last n))) i) =
      ⟨(flattenedPositionsEquiv (Fin.init X) i).1.castSucc,
        (flattenedPositionsEquiv (Fin.init X) i).2⟩ := by
  change positionsSnocEquiv X
    ((Equiv.sumCongr (blockPositionsEquiv (Fin.init X)) (enumeration (X (Fin.last n))))
      ((Equiv.sumCongr (blocksOfFamily (Fin.init X)).positionEquiv
        (Equiv.refl (Fin (arity (X (Fin.last n))))))
        (finSumFinEquiv.symm (Fin.castAdd (arity (X (Fin.last n))) i)))) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

omit [Category.{v} C] in
/-- Every original final-block input retains its original final slot and original inner
enumeration. -/
theorem flattenedPositions_right {n : ℕ} (X : Fin (n + 1) → FiniteFamily C)
    (i : Fin (arity (X (Fin.last n)))) :
    flattenedPositionsEquiv X (Fin.natAdd (blocksOfFamily (Fin.init X)).totalArity i) =
      ⟨Fin.last n, enumeration (X (Fin.last n)) i⟩ := by
  change positionsSnocEquiv X
    ((Equiv.sumCongr (blockPositionsEquiv (Fin.init X)) (enumeration (X (Fin.last n))))
      ((Equiv.sumCongr (blocksOfFamily (Fin.init X)).positionEquiv
        (Equiv.refl (Fin (arity (X (Fin.last n))))))
        (finSumFinEquiv.symm (Fin.natAdd (blocksOfFamily (Fin.init X)).totalArity i)))) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

/-- The actual original inner morphism retains the exact original target input enumeration. -/
theorem enumeration_enumeratedEquiv {X Y : FiniteFamily C} (f : X ⟶ Y)
    (i : Fin (arity X)) :
    enumeration Y (enumeratedEquiv f i) = f.equiv (enumeration X i) :=
  (enumeration Y).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
/-- The actual flattened block map retains every original inner input bijection at its
original outer slot. -/
theorem blocksOfFamilyFiberMap_positions : ∀ {n : ℕ} {X Y : Fin n → FiniteFamily C}
    (f : ∀ i, X i ⟶ Y i) (i : Fin (blocksOfFamily X).totalArity),
    flattenedPositionsEquiv Y ((blocksOfFamilyFiberMap f).inputEquiv i) =
      innerInputEquiv f (flattenedPositionsEquiv X i) := by
  intro n
  induction n with
  | zero => intro X Y f i; exact i.elim0
  | succ n ih =>
      intro X Y f i
      let f0 : ∀ i : Fin n, (Fin.init X) i ⟶ (Fin.init Y) i := fun i => f i.castSucc
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · change flattenedPositionsEquiv Y
          (sumInputsEquiv (blocksOfFamilyFiberMap f0).inputEquiv
            (enumeratedEquiv (f (Fin.last n)))
            (Fin.castAdd (arity (X (Fin.last n))) j)) = _
        rw [sumInputsEquiv_left, flattenedPositions_left, flattenedPositions_left]
        exact congrArg
          (fun p : OriginalPositions (Fin.init Y) => (⟨p.1.castSucc, p.2⟩ : OriginalPositions Y))
          (ih f0 j)
      · change flattenedPositionsEquiv Y
          (sumInputsEquiv (blocksOfFamilyFiberMap f0).inputEquiv
            (enumeratedEquiv (f (Fin.last n)))
            (Fin.natAdd (blocksOfFamily (Fin.init X)).totalArity j)) = _
        rw [sumInputsEquiv_right, flattenedPositions_right, flattenedPositions_right]
        exact congrArg (fun p : (Y (Fin.last n)).index =>
          (⟨Fin.last n, p⟩ : OriginalPositions Y)) (enumeration_enumeratedEquiv (f (Fin.last n)) j)

set_option backward.isDefEq.respectTransparency false in
/-- All original flattened component maps are the original inner component morphisms at
their original positions. -/
theorem blocksOfFamilyFiberMap_components : ∀ {n : ℕ} {X Y : Fin n → FiniteFamily C}
    (f : ∀ i, X i ⟶ Y i) (i : Fin (blocksOfFamily X).totalArity),
    HEq ((blocksOfFamilyFiberMap f).inputComponents i)
      ((f (flattenedPositionsEquiv X i).1).hom (flattenedPositionsEquiv X i).2) := by
  intro n
  induction n with
  | zero => intro X Y f i; exact i.elim0
  | succ n ih =>
      intro X Y f i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [flattenedPositions_left]
        exact (sumInputsComponent_left_heq
          (blocksOfFamilyFiberMap (fun i : Fin n => f i.castSucc)).inputComponents
          (enumeratedMap (f (Fin.last n))) j).trans (ih (fun i : Fin n => f i.castSucc) j)
      · rw [flattenedPositions_right]
        exact (sumInputsComponent_right_heq
          (blocksOfFamilyFiberMap (fun i : Fin n => f i.castSucc)).inputComponents
          (enumeratedMap (f (Fin.last n))) j).trans (enumeratedMap_heq (f (Fin.last n)) j)

variable [MonoidalCategory C] [SymmetricCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The actual outer block tensor map is the original ordered tensor of all original inner
finite tensor maps. -/
theorem blocksOfFamilyFiberMap_tensor_heq : ∀ {n : ℕ} {X Y : Fin n → FiniteFamily C}
    (f : ∀ i, X i ⟶ Y i),
    HEq (blocksOfFamilyFiberMap f).tensorMap (map (fun i => finiteMap (f i))) := by
  intro n
  induction n with
  | zero =>
      intro X Y f
      change HEq (mapEquiv (Equiv.refl (Fin 0)) (X := Fin.elim0) (Y := Fin.elim0)
        (fun i => i.elim0)) (𝟙 (𝟙_ C))
      rw [mapEquiv_refl]
      rfl
  | succ n ih =>
      intro X Y f
      let f0 : ∀ i : Fin n, (Fin.init X) i ⟶ (Fin.init Y) i := fun i => f i.castSucc
      let p0 := blocksOfFamilyFiberMap f0
      change HEq (Blocks.FiberMap.snoc
        p0
        (enumeratedEquiv (f (Fin.last n))) (enumeratedMap (f (Fin.last n)))).tensorMap _
      rw [Blocks.FiberMap.tensorMap_snoc]
      let d := p0.tensorMap ⊗ₘ finiteMap (f (Fin.last n))
      have hX := Blocks.obj_blockTensors_snoc (blocksOfFamily (Fin.init X)) (orderedFamily
        (X (Fin.last n)))
      have hY := Blocks.obj_blockTensors_snoc (blocksOfFamily (Fin.init Y)) (orderedFamily
        (Y (Fin.last n)))
      have hStrip : HEq (eqToHom hX ≫ d ≫ eqToHom hY.symm) d :=
        (eqToHom_comp_heq (d ≫ eqToHom hY.symm) hX).trans (comp_eqToHom_heq d hY.symm)
      have hTensor := tensorMapBoundary_heq (blocksOfFamily_tensors (Fin.init X))
        (blocksOfFamily_tensors (Fin.init Y)) rfl rfl
        (ih f0)
        (HEq.rfl (a := finiteMap (f (Fin.last n))))
      exact hStrip.trans hTensor

set_option backward.isDefEq.respectTransparency false in
/-- The original output block tensor map commutes with the original block-carrier equalities. -/
theorem blocksOfFamilyFiberMap_tensor {n : ℕ} {X Y : Fin n → FiniteFamily C}
    (f : ∀ i, X i ⟶ Y i) :
    (blocksOfFamilyFiberMap f).tensorMap ≫ eqToHom (blocksOfFamily_tensors Y) =
      eqToHom (blocksOfFamily_tensors X) ≫ map (fun i => finiteMap (f i)) := by
  have h := (conj_eqToHom_iff_heq (blocksOfFamilyFiberMap f).tensorMap
    (map (fun i => finiteMap (f i))) (blocksOfFamily_tensors X) (blocksOfFamily_tensors Y)).mpr
      (blocksOfFamilyFiberMap_tensor_heq f)
  rw [h]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- Original finite-family morphisms in every inner block commute with the original full
ordered block split. -/
theorem blocksOfFamilyIso_fiber_naturality {n : ℕ} {X Y : Fin n → FiniteFamily C}
    (f : ∀ i, X i ⟶ Y i) :
    (blocksOfFamilyFiberMap f).inputMap ≫ (blocksOfFamilyIso Y).hom =
      (blocksOfFamilyIso X).hom ≫ map (fun i => finiteMap (f i)) := by
  unfold blocksOfFamilyIso
  simp only [Iso.trans_hom, eqToIso.hom, ← Category.assoc]
  rw [Blocks.FiberMap.flatten_naturality]
  simp only [Category.assoc]
  rw [blocksOfFamilyFiberMap_tensor]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedFiniteFiberMaps

/- Source proof segment: FiniteNestedPositions -/
section source_FiniteNestedPositions
/-!
# Original nested input positions of a finite tensor family

The outer enumeration and every original inner index are retained in
the actual bijection from the ordered tensor word to the original
dependent sum of inner positions.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

variable {C : Type u}

/-- The dependent sum of all original inner inputs of a finite outer family. -/
def NestedPositions (X : FiniteFamily (FiniteFamily C)) : Type :=
  Σ i : X.index, (X.obj i).index

/-- The original outer enumeration retains every original inner position. -/
noncomputable def originalOuterPositionsEquiv (X : FiniteFamily (FiniteFamily C)) :
    OriginalPositions (X.obj ∘ enumeration X) ≃ NestedPositions X :=
  Equiv.sigmaCongr (enumeration X) (fun _ => Equiv.refl _)

/-- The actual equivalence from the ordered tensor word to every original nested input. -/
noncomputable def nestedPositionsEquiv (X : FiniteFamily (FiniteFamily C)) :
    Fin (blocksOfFiniteFamily X).totalArity ≃ NestedPositions X :=
  (flattenedPositionsEquiv (X.obj ∘ enumeration X)).trans (originalOuterPositionsEquiv X)

/-- Original input objects are retained by the full original nested-position equivalence. -/
theorem nestedPositions_objects (X : FiniteFamily (FiniteFamily C))
    (i : Fin (blocksOfFiniteFamily X).totalArity) :
    (blocksOfFiniteFamily X).inputs i =
      (X.obj (nestedPositionsEquiv X i).1).obj (nestedPositionsEquiv X i).2 := by
  exact flattenedPositions_objects (X.obj ∘ enumeration X) i

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FiniteNestedPositions

/- Source proof segment: FiniteTensorFlattenCarrier -/
section source_FiniteTensorFlattenCarrier
/-!
# The original finite tensor flattening carrier comparison

The original nested finite family is related to the constructed
ordered block word by its actual input-position bijection. The
flattening maps use the constructed finite tensor reindexing and
original ordered block flattening.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

attribute [local instance] FintypeCat.fintype

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The actual ordered input family of the original flattened nested finite family. -/
abbrev flattenedOriginalFamily (X : FiniteFamily (FiniteFamily C)) :
    FiniteFamily C := (FiniteFamily.flatten (C := C)).obj X

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The actual bijection from the original flattened enumeration to the constructed block word. -/
noncomputable def flattenWordEquiv (X : FiniteFamily (FiniteFamily C)) :
    Fin (arity (flattenedOriginalFamily X)) ≃ Fin (blocksOfFiniteFamily X).totalArity :=
  (enumeration (flattenedOriginalFamily X)).trans (nestedPositionsEquiv X).symm

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- Every original flattened input is its corresponding constructed block-word object. -/
theorem flattenWord_objects (X : FiniteFamily (FiniteFamily C))
    (i : Fin (arity (flattenedOriginalFamily X))) :
    orderedFamily (flattenedOriginalFamily X) i =
      (blocksOfFiniteFamily X).inputs (flattenWordEquiv X i) := by
  have h := nestedPositions_objects X
    ((nestedPositionsEquiv X).symm (enumeration (flattenedOriginalFamily X) i))
  let evaluate : NestedPositions X → C := fun p => (X.obj p.1).obj p.2
  have he := congrArg evaluate ((nestedPositionsEquiv X).apply_symm_apply
    (enumeration (flattenedOriginalFamily X) i))
  exact (h.trans he).symm

/-- The constructed actual map from the original flattened tensor to its ordered block word. -/
noncomputable def flattenToWord (X : FiniteFamily (FiniteFamily C)) :
    finiteObj (flattenedOriginalFamily X) ⟶ obj (blocksOfFiniteFamily X).inputs :=
  mapEquiv (flattenWordEquiv X) (fun i => eqToHom (flattenWord_objects X i))

/-- The original finite tensor flattening map to the original tensor of inner tensor carriers. -/
noncomputable def finiteFlattenHom (X : FiniteFamily (FiniteFamily C)) :
    finiteObj (flattenedOriginalFamily X) ⟶
      finiteObj (⟨X.index, fun i => finiteObj (X.obj i)⟩ : FiniteFamily C) :=
  flattenToWord X ≫ (finiteFamilyBlocksIso X).hom

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FiniteTensorFlattenCarrier

/- Source proof segment: FiniteTensorFlattenIso -/
section source_FiniteTensorFlattenIso
/-!
# The constructed original finite tensor flattening isomorphism

The maps compare the original flattened finite input family with the
original finite outer family of tensorized inner inputs. They are
constructed from the actual finite input bijection and original
ordered block flattening, including every empty block.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The actual isomorphism from the original flattened tensor to its original ordered word. -/
noncomputable def flattenToWordIso (X : FiniteFamily (FiniteFamily C)) :
    finiteObj (flattenedOriginalFamily X) ≅ obj (blocksOfFiniteFamily X).inputs :=
  isoEquiv (flattenWordEquiv X) (fun i => eqToIso (flattenWord_objects X i))

/-- Its forward map is the original constructed flatten-to-word map. -/
theorem flattenToWordIso_hom (X : FiniteFamily (FiniteFamily C)) :
    (flattenToWordIso X).hom = flattenToWord X :=
  isoEquiv_hom _ _

/-- The original finite tensor flattening isomorphism with its original block maps. -/
noncomputable def finiteFlattenIso (X : FiniteFamily (FiniteFamily C)) :
    finiteObj (flattenedOriginalFamily X) ≅
      finiteObj (⟨X.index, fun i => finiteObj (X.obj i)⟩ : FiniteFamily C) :=
  flattenToWordIso X ≪≫ finiteFamilyBlocksIso X

/-- The full original forward flattening map is retained by the constructed isomorphism. -/
theorem finiteFlattenIso_hom (X : FiniteFamily (FiniteFamily C)) :
    (finiteFlattenIso X).hom = finiteFlattenHom X := by
  rw [finiteFlattenIso, Iso.trans_hom, flattenToWordIso_hom]
  rfl

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FiniteTensorFlattenIso

/- Source proof segment: FiniteTensorPositionNaturality -/
section source_FiniteTensorPositionNaturality
/-!
# Original nested finite tensor input maps

The dependent-sum input morphism of an original nested family retains
the original outer bijection, every original inner bijection, and
all original component morphisms. It is the map used by flattening.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The original nested input bijection of a nested finite-family morphism. -/
def nestedInputEquiv {X Y : FiniteFamily (FiniteFamily C)} (f : X ⟶ Y) :
    NestedPositions X ≃ NestedPositions Y :=
  Equiv.sigmaCongr f.equiv (fun i => (f.hom i).equiv)

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The original component map of a nested finite-family morphism at its original input position. -/
def nestedInputMap {X Y : FiniteFamily (FiniteFamily C)} (f : X ⟶ Y) (p : NestedPositions X) :
    (X.obj p.1).obj p.2 ⟶ (Y.obj (nestedInputEquiv f p).1).obj (nestedInputEquiv f p).2 :=
  (f.hom p.1).hom p.2

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- Original nested input bijections compose with their actual outer and inner components. -/
theorem nestedInputEquiv_comp {X Y Z : FiniteFamily (FiniteFamily C)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    nestedInputEquiv (f ≫ g) = (nestedInputEquiv f).trans (nestedInputEquiv g) := by
  apply Equiv.ext
  intro p
  cases p
  rfl

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The original nested input map is exactly the underlying finite-family flatten map. -/
theorem flatten_map_equiv {X Y : FiniteFamily (FiniteFamily C)} (f : X ⟶ Y) :
    ((FiniteFamily.flatten (C := C)).map f).equiv = nestedInputEquiv f := rfl

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- Every original nested input component is retained by the underlying flatten map. -/
theorem flatten_map_component {X Y : FiniteFamily (FiniteFamily C)} (f : X ⟶ Y)
    (p : NestedPositions X) :
    ((FiniteFamily.flatten (C := C)).map f).hom p = nestedInputMap f p := rfl

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FiniteTensorPositionNaturality

/- Source proof segment: FiniteTensorWordMaps -/
section source_FiniteTensorWordMaps
/-!
# Original nested tensor maps on the ordered input word

The original outer bijection, inner bijections and component maps give
the actual ordered-word tensor map. The flatten-to-word comparison is
natural for these original maps before any block coherence is used.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The original nested bijection on the actual two ordered block words. -/
noncomputable def wordInputEquiv {X Y : FiniteFamily (FiniteFamily C)} (f : X ⟶ Y) :
    Fin (blocksOfFiniteFamily X).totalArity ≃ Fin (blocksOfFiniteFamily Y).totalArity :=
  (nestedPositionsEquiv X).trans ((nestedInputEquiv f).trans (nestedPositionsEquiv Y).symm)

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The original nested input of a word map is exactly its original outer and inner input
bijection. -/
theorem wordInput_positions {X Y : FiniteFamily (FiniteFamily C)} (f : X ⟶ Y)
    (i : Fin (blocksOfFiniteFamily X).totalArity) :
    nestedPositionsEquiv Y (wordInputEquiv f i) = nestedInputEquiv f (nestedPositionsEquiv X i) :=
  (nestedPositionsEquiv Y).apply_symm_apply _

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- Every word-map target is the original target object of its original nested input. -/
theorem wordInput_target_objects {X Y : FiniteFamily (FiniteFamily C)} (f : X ⟶ Y)
    (i : Fin (blocksOfFiniteFamily X).totalArity) :
    (blocksOfFiniteFamily Y).inputs (wordInputEquiv f i) =
      (Y.obj (nestedInputEquiv f (nestedPositionsEquiv X i)).1).obj
        (nestedInputEquiv f (nestedPositionsEquiv X i)).2 := by
  exact (nestedPositions_objects Y (wordInputEquiv f i)).trans
    (congrArg (fun p : NestedPositions Y => (Y.obj p.1).obj p.2) (wordInput_positions f i))

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The actual original component map at an ordered nested word input. -/
noncomputable def wordInputComponent {X Y : FiniteFamily (FiniteFamily C)} (f : X ⟶ Y)
    (i : Fin (blocksOfFiniteFamily X).totalArity) :
    (blocksOfFiniteFamily X).inputs i ⟶ (blocksOfFiniteFamily Y).inputs (wordInputEquiv f i) :=
  eqToHom (nestedPositions_objects X i) ≫ nestedInputMap f (nestedPositionsEquiv X i) ≫
    eqToHom (wordInput_target_objects f i).symm

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The actual word component retains precisely the original nested component map after
object transports. -/
theorem wordInputComponent_heq {X Y : FiniteFamily (FiniteFamily C)} (f : X ⟶ Y)
    (i : Fin (blocksOfFiniteFamily X).totalArity) :
    HEq (wordInputComponent f i) (nestedInputMap f (nestedPositionsEquiv X i)) :=
  (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)

/-- The actual original tensor map on the ordered nested input word. -/
noncomputable def wordInputMap {X Y : FiniteFamily (FiniteFamily C)} (f : X ⟶ Y) :
    obj (blocksOfFiniteFamily X).inputs ⟶ obj (blocksOfFiniteFamily Y).inputs :=
  mapEquiv (wordInputEquiv f) (wordInputComponent f)

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- Flatten-to-word keeps every original flattened input position. -/
theorem nestedPositions_flattenWord (X : FiniteFamily (FiniteFamily C))
    (i : Fin (arity (flattenedOriginalFamily X))) :
    nestedPositionsEquiv X (flattenWordEquiv X i) = enumeration (flattenedOriginalFamily X) i :=
  (nestedPositionsEquiv X).apply_symm_apply _

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The complete original flatten and word input bijections form their actual commutative square. -/
theorem flattenWordEquiv_naturality {X Y : FiniteFamily (FiniteFamily C)} (f : X ⟶ Y) :
    (enumeratedEquiv ((FiniteFamily.flatten (C := C)).map f)).trans (flattenWordEquiv Y) =
      (flattenWordEquiv X).trans (wordInputEquiv f) := by
  apply Equiv.ext
  intro i
  change (nestedPositionsEquiv Y).symm
      (enumeration (flattenedOriginalFamily Y)
        ((enumeration (flattenedOriginalFamily Y)).symm
          (nestedInputEquiv f (enumeration (flattenedOriginalFamily X) i)))) =
    (nestedPositionsEquiv Y).symm
      (nestedInputEquiv f (nestedPositionsEquiv X
        ((nestedPositionsEquiv X).symm (enumeration (flattenedOriginalFamily X) i))))
  exact (congrArg (nestedPositionsEquiv Y).symm
    ((enumeration (flattenedOriginalFamily Y)).apply_symm_apply
      (nestedInputEquiv f (enumeration (flattenedOriginalFamily X) i)))).trans
    (congrArg (fun p : NestedPositions X => (nestedPositionsEquiv Y).symm (nestedInputEquiv f p))
      ((nestedPositionsEquiv X).apply_symm_apply
        (enumeration (flattenedOriginalFamily X) i))).symm

set_option backward.isDefEq.respectTransparency false in
/-- The actual original nested tensor map commutes with the original flatten-to-word comparison. -/
theorem flattenToWord_naturality {X Y : FiniteFamily (FiniteFamily C)} (f : X ⟶ Y) :
    finiteMap ((FiniteFamily.flatten (C := C)).map f) ≫ flattenToWord Y =
      flattenToWord X ≫ wordInputMap f := by
  unfold finiteMap flattenToWord wordInputMap
  rw [mapEquiv_comp, mapEquiv_comp]
  apply mapEquiv_congr (flattenWordEquiv_naturality f)
  intro i
  have hLeft : HEq
      (enumeratedMap ((FiniteFamily.flatten (C := C)).map f) i ≫
        eqToHom (flattenWord_objects Y (enumeratedEquiv ((FiniteFamily.flatten (C := C)).map f) i)))
      (nestedInputMap f (enumeration (flattenedOriginalFamily X) i)) :=
    (comp_eqToHom_heq _ _).trans
      (enumeratedMap_heq ((FiniteFamily.flatten (C := C)).map f) i)
  have hRight : HEq
      (eqToHom (flattenWord_objects X i) ≫ wordInputComponent f (flattenWordEquiv X i))
      (nestedInputMap f (enumeration (flattenedOriginalFamily X) i)) := by
    have hPos := nestedPositions_flattenWord X i
    have hp : HEq (nestedInputMap f (nestedPositionsEquiv X (flattenWordEquiv X i)))
        (nestedInputMap f (enumeration (flattenedOriginalFamily X) i)) := by
      rw [hPos]
    exact (eqToHom_comp_heq _ _).trans
      ((wordInputComponent_heq f (flattenWordEquiv X i)).trans hp)
  exact hLeft.trans hRight.symm

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FiniteTensorWordMaps

/- Source proof segment: FiniteTensorWordFunctor -/
section source_FiniteTensorWordFunctor
/-!
# The original ordered nested tensor input functor

The ordered nested word functor uses the actual input bijections and
component maps. Its laws follow from their proved flatten-to-word
square and the original finite tensor functor laws.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- Identity on the original nested inputs tensors to the actual word identity. -/
theorem wordInputMap_id (X : FiniteFamily (FiniteFamily C)) :
    wordInputMap (𝟙 X) = 𝟙 (obj (blocksOfFiniteFamily X).inputs) := by
  apply (cancel_epi (flattenToWordIso X).hom).mp
  rw [flattenToWordIso_hom, ← flattenToWord_naturality]
  rw [Functor.map_id, finiteMap_id, Category.id_comp, Category.comp_id]

/-- Consecutive original nested input maps give their actual consecutive word tensor maps. -/
theorem wordInputMap_comp {X Y Z : FiniteFamily (FiniteFamily C)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    wordInputMap (f ≫ g) = wordInputMap f ≫ wordInputMap g := by
  apply (cancel_epi (flattenToWordIso X).hom).mp
  rw [flattenToWordIso_hom, ← flattenToWord_naturality]
  rw [Functor.map_comp, finiteMap_comp, Category.assoc, flattenToWord_naturality,
    ← Category.assoc, flattenToWord_naturality, Category.assoc]

/-- The actual tensor functor on the original ordered nested input word. -/
noncomputable def nestedWordFunctor : FiniteFamily (FiniteFamily C) ⥤ C where
  obj X := obj (blocksOfFiniteFamily X).inputs
  map := wordInputMap
  map_id X := wordInputMap_id X
  map_comp f g := wordInputMap_comp f g

/-- The original flatten-to-word comparisons form their full original natural isomorphism. -/
noncomputable def flattenToWordNatIso :
    FiniteFamily.flatten (C := C) ⋙ finiteTensorFunctor ≅ nestedWordFunctor :=
  NatIso.ofComponents flattenToWordIso (by
    intro X Y f
    change finiteMap ((FiniteFamily.flatten (C := C)).map f) ≫ (flattenToWordIso Y).hom =
      (flattenToWordIso X).hom ≫ wordInputMap f
    rw [flattenToWordIso_hom, flattenToWordIso_hom]
    exact flattenToWord_naturality f)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FiniteTensorWordFunctor

/- Source proof segment: OrderedTensorWordMaps -/
section source_OrderedTensorWordMaps
/-!
# Original maps between literal ordered finite block words

The original outer finite input bijection and every inner finite-family
morphism determine the actual flattened ordered-word tensor map. No
enumeration of the outer ordered family is substituted for its literal
ordered input slots.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] in
/-- The original finite family with its literal ordered outer input slots. -/
abbrev literalOuterFamily {n : ℕ} (X : Fin n → FiniteFamily C) : FiniteFamily (FiniteFamily C) :=
  ⟨FintypeCat.of (Fin n), X⟩

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The original flattened family of the literal ordered outer inputs. -/
abbrev literalFlattenedFamily {n : ℕ} (X : Fin n → FiniteFamily C) : FiniteFamily C :=
  (FiniteFamily.flatten (C := C)).obj (literalOuterFamily X)

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The actual original flattened enumeration maps to the literal ordered block word. -/
noncomputable def orderedToWordEquiv {n : ℕ} (X : Fin n → FiniteFamily C) :
    Fin (arity (literalFlattenedFamily X)) ≃ Fin (blocksOfFamily X).totalArity :=
  (enumeration (literalFlattenedFamily X)).trans (flattenedPositionsEquiv X).symm

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- Every flattened original input remains its actual literal ordered block-word object. -/
theorem orderedToWord_objects {n : ℕ} (X : Fin n → FiniteFamily C)
    (i : Fin (arity (literalFlattenedFamily X))) :
    orderedFamily (literalFlattenedFamily X) i = (blocksOfFamily X).inputs
      (orderedToWordEquiv X i) := by
  have h := flattenedPositions_objects X
    ((flattenedPositionsEquiv X).symm (enumeration (literalFlattenedFamily X) i))
  have he := congrArg (fun p : OriginalPositions X => (X p.1).obj p.2)
    ((flattenedPositionsEquiv X).apply_symm_apply (enumeration (literalFlattenedFamily X) i))
  exact (h.trans he).symm

/-- The actual original tensor comparison to the literal ordered input word. -/
noncomputable def orderedToWordIso {n : ℕ} (X : Fin n → FiniteFamily C) :
    finiteObj (literalFlattenedFamily X) ≅ obj (blocksOfFamily X).inputs :=
  isoEquiv (orderedToWordEquiv X) (fun i => eqToIso (orderedToWord_objects X i))

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The original outer and inner input bijections act on every literal ordered-word position. -/
noncomputable def orderedInputEquiv {m n : ℕ} {X : Fin m → FiniteFamily C} {Y : Fin n
  → FiniteFamily C}
    (F : literalOuterFamily X ⟶ literalOuterFamily Y) :
    Fin (blocksOfFamily X).totalArity ≃ Fin (blocksOfFamily Y).totalArity :=
  (flattenedPositionsEquiv X).trans
    (((FiniteFamily.flatten (C := C)).map F).equiv.trans (flattenedPositionsEquiv Y).symm)

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The literal ordered-word map has exactly its original flattened input target. -/
theorem orderedInput_positions {m n : ℕ} {X : Fin m → FiniteFamily C} {Y : Fin n → FiniteFamily C}
    (F : literalOuterFamily X ⟶ literalOuterFamily Y) (i : Fin (blocksOfFamily X).totalArity) :
    flattenedPositionsEquiv Y (orderedInputEquiv F i) =
      ((FiniteFamily.flatten (C := C)).map F).equiv (flattenedPositionsEquiv X i) :=
  (flattenedPositionsEquiv Y).apply_symm_apply _

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The literal ordered-word target object is the original flattened component target. -/
theorem orderedInput_target_objects {m n : ℕ} {X : Fin m → FiniteFamily C} {Y : Fin n
  → FiniteFamily C}
    (F : literalOuterFamily X ⟶ literalOuterFamily Y) (i : Fin (blocksOfFamily X).totalArity) :
    (blocksOfFamily Y).inputs (orderedInputEquiv F i) =
      (literalFlattenedFamily Y).obj (((FiniteFamily.flatten (C := C)).map F).equiv
        (flattenedPositionsEquiv X i)) := by
  exact (flattenedPositions_objects Y (orderedInputEquiv F i)).trans
    (congrArg (fun p : OriginalPositions Y => (Y p.1).obj p.2) (orderedInput_positions F i))

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- Every original inner component morphism occupies its actual literal ordered-word input. -/
noncomputable def orderedInputComponent {m n : ℕ} {X : Fin m →
  FiniteFamily C} {Y : Fin n → FiniteFamily C}
    (F : literalOuterFamily X ⟶ literalOuterFamily Y) (i : Fin (blocksOfFamily X).totalArity) :
    (blocksOfFamily X).inputs i ⟶ (blocksOfFamily Y).inputs (orderedInputEquiv F i) :=
  eqToHom (flattenedPositions_objects X i) ≫
    ((FiniteFamily.flatten (C := C)).map F).hom (flattenedPositionsEquiv X i) ≫
      eqToHom (orderedInput_target_objects F i).symm

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The literal ordered component map retains its complete original flattened component
after object transports. -/
theorem orderedInputComponent_heq {m n : ℕ} {X : Fin m → FiniteFamily C} {Y : Fin n →
  FiniteFamily C}
    (F : literalOuterFamily X ⟶ literalOuterFamily Y) (i : Fin (blocksOfFamily X).totalArity) :
    HEq (orderedInputComponent F i) (((FiniteFamily.flatten (C := C)).map F).hom
      (flattenedPositionsEquiv X i)) :=
  (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)

/-- The actual flattened tensor map on every original literal ordered-word input. -/
noncomputable def orderedInputMap {m n : ℕ} {X : Fin m → FiniteFamily C} {Y : Fin n →
  FiniteFamily C}
    (F : literalOuterFamily X ⟶ literalOuterFamily Y) :
    obj (blocksOfFamily X).inputs ⟶ obj (blocksOfFamily Y).inputs :=
  mapEquiv (orderedInputEquiv F) (orderedInputComponent F)

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- Literal ordered flattening retains every original flattened input position. -/
theorem flattenedPositions_orderedToWord {n : ℕ} (X : Fin n → FiniteFamily C)
    (i : Fin (arity (literalFlattenedFamily X))) :
    flattenedPositionsEquiv X (orderedToWordEquiv X i) = enumeration (literalFlattenedFamily X) i :=
  (flattenedPositionsEquiv X).apply_symm_apply _

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The original flattened and literal-word input bijections give their actual naturality square. -/
theorem orderedToWordEquiv_naturality {m n : ℕ} {X : Fin m → FiniteFamily C} {Y : Fin n
  → FiniteFamily C}
    (F : literalOuterFamily X ⟶ literalOuterFamily Y) :
    (enumeratedEquiv ((FiniteFamily.flatten (C := C)).map F)).trans (orderedToWordEquiv Y) =
      (orderedToWordEquiv X).trans (orderedInputEquiv F) := by
  apply Equiv.ext
  intro i
  change (flattenedPositionsEquiv Y).symm
      (enumeration (literalFlattenedFamily Y)
        ((enumeration (literalFlattenedFamily Y)).symm
          (((FiniteFamily.flatten (C := C)).map F).equiv (enumeration
            (literalFlattenedFamily X) i)))) =
    (flattenedPositionsEquiv Y).symm
      (((FiniteFamily.flatten (C := C)).map F).equiv (flattenedPositionsEquiv X
        ((flattenedPositionsEquiv X).symm (enumeration (literalFlattenedFamily X) i))))
  exact (congrArg (flattenedPositionsEquiv Y).symm
    ((enumeration (literalFlattenedFamily Y)).apply_symm_apply _)).trans
    (congrArg (fun p : OriginalPositions X => (flattenedPositionsEquiv Y).symm
      (((FiniteFamily.flatten (C := C)).map F).equiv p))
        ((flattenedPositionsEquiv X).apply_symm_apply _)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The original flattened tensor map commutes with its actual literal ordered-word comparison. -/
theorem orderedToWord_naturality {m n : ℕ} {X : Fin m → FiniteFamily C} {Y : Fin n → FiniteFamily C}
    (F : literalOuterFamily X ⟶ literalOuterFamily Y) :
    finiteMap ((FiniteFamily.flatten (C := C)).map F) ≫ (orderedToWordIso Y).hom =
      (orderedToWordIso X).hom ≫ orderedInputMap F := by
  simp only [orderedToWordIso, isoEquiv_hom]
  unfold finiteMap orderedInputMap
  rw [mapEquiv_comp, mapEquiv_comp]
  apply mapEquiv_congr (orderedToWordEquiv_naturality F)
  intro i
  have hLeft : HEq
      (enumeratedMap ((FiniteFamily.flatten (C := C)).map F) i ≫ eqToHom
        (orderedToWord_objects Y (enumeratedEquiv ((FiniteFamily.flatten (C := C)).map F) i)))
      (((FiniteFamily.flatten (C := C)).map F).hom (enumeration (literalFlattenedFamily X) i)) :=
    (comp_eqToHom_heq _ _).trans (enumeratedMap_heq ((FiniteFamily.flatten (C := C)).map F) i)
  have hRight : HEq
      (eqToHom (orderedToWord_objects X i) ≫ orderedInputComponent F (orderedToWordEquiv X i))
      (((FiniteFamily.flatten (C := C)).map F).hom (enumeration (literalFlattenedFamily X) i)) := by
    have hp : HEq (((FiniteFamily.flatten (C := C)).map F).hom
        (flattenedPositionsEquiv X (orderedToWordEquiv X i)))
        (((FiniteFamily.flatten (C := C)).map F).hom (enumeration (literalFlattenedFamily X)
          i)) := by
      rw [flattenedPositions_orderedToWord]
    exact (eqToHom_comp_heq _ _).trans ((orderedInputComponent_heq F _).trans hp)
  exact hLeft.trans hRight.symm

/-- Original literal ordered-word identities give the actual tensor identity. -/
theorem orderedInputMap_id {n : ℕ} (X : Fin n → FiniteFamily C) :
    orderedInputMap (𝟙 (literalOuterFamily X)) = 𝟙 (obj (blocksOfFamily X).inputs) := by
  apply (cancel_epi (orderedToWordIso X).hom).mp
  rw [← orderedToWord_naturality, Functor.map_id, finiteMap_id, Category.id_comp, Category.comp_id]

/-- Original consecutive literal ordered-word maps give their actual tensor map composition. -/
theorem orderedInputMap_comp {l m n : ℕ} {X : Fin l → FiniteFamily C}
    {Y : Fin m → FiniteFamily C} {Z : Fin n → FiniteFamily C}
    (F : literalOuterFamily X ⟶ literalOuterFamily Y) (G : literalOuterFamily Y ⟶
      literalOuterFamily Z) :
    orderedInputMap (F ≫ G) = orderedInputMap F ≫ orderedInputMap G := by
  apply (cancel_epi (orderedToWordIso X).hom).mp
  rw [← orderedToWord_naturality, Functor.map_comp, finiteMap_comp, Category.assoc,
    orderedToWord_naturality, ← Category.assoc, orderedToWord_naturality, Category.assoc]

/-- The original tensor of all original inner finite tensor maps, with the literal outer
input bijection. -/
noncomputable def orderedOutputMap {m n : ℕ} {X : Fin m → FiniteFamily C} {Y : Fin n →
  FiniteFamily C}
    (F : literalOuterFamily X ⟶ literalOuterFamily Y) :
    obj (fun i => finiteObj (X i)) ⟶ obj (fun i => finiteObj (Y i)) :=
  mapEquiv F.equiv (fun i => finiteMap (F.hom i))

/-- Original identity maps on all block tensors give the actual outer tensor identity. -/
theorem orderedOutputMap_id {n : ℕ} (X : Fin n → FiniteFamily C) :
    orderedOutputMap (𝟙 (literalOuterFamily X)) = 𝟙 (obj (fun i => finiteObj (X i))) := by
  unfold orderedOutputMap
  change mapEquiv (Equiv.refl (Fin n))
    (X := fun i => finiteObj (X i)) (Y := fun i => finiteObj (X i))
    (fun i => finiteMap (𝟙 (X i))) = _
  have h := mapEquiv_congr (X := fun i : Fin n => finiteObj (X i))
    (Y := fun i : Fin n => finiteObj (X i))
    (e := Equiv.refl (Fin n)) (d := Equiv.refl (Fin n)) rfl
    (fun i => finiteMap (𝟙 (X i))) (fun i => 𝟙 (finiteObj (X i)))
    (fun i => heq_of_eq (finiteMap_id (X i)))
  exact h.trans (mapEquiv_id (fun i => finiteObj (X i)))

/-- The original outer tensor maps compose with every original inner finite tensor map. -/
theorem orderedOutputMap_comp {l m n : ℕ} {X : Fin l → FiniteFamily C}
    {Y : Fin m → FiniteFamily C} {Z : Fin n → FiniteFamily C}
    (F : literalOuterFamily X ⟶ literalOuterFamily Y) (G : literalOuterFamily Y ⟶
      literalOuterFamily Z) :
    orderedOutputMap (F ≫ G) = orderedOutputMap F ≫ orderedOutputMap G := by
  unfold orderedOutputMap
  rw [mapEquiv_comp]
  apply mapEquiv_congr rfl
  intro i
  exact heq_of_eq (finiteMap_comp (F.hom i) (G.hom (F.equiv i)))

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedTensorWordMaps

/- Source proof segment: OrderedReindexNaturality -/
section source_OrderedReindexNaturality
/-!
# Original ordered tensor flattening reindexing squares

The fixed-slot square uses every original inner finite-family map.
The reindexing squares form a submonoid under the original finite
input bijection composition; membership is proved from original
binary block coherence in the subsequent generator construction.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The original literal ordered outer morphism retaining every original outer slot. -/
def orderedFixedHom {n : ℕ} {X Y : Fin n → FiniteFamily C} (f : ∀ i, X i ⟶ Y i) :
    literalOuterFamily X ⟶ literalOuterFamily Y where
  equiv := Equiv.refl _
  hom := f

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The actual fixed-slot input bijection is the original ordered inner block input bijection. -/
theorem orderedFixed_inputEquiv {n : ℕ} {X Y : Fin n → FiniteFamily C} (f : ∀ i, X i ⟶ Y i) :
    orderedInputEquiv (orderedFixedHom f) = (blocksOfFamilyFiberMap f).inputEquiv := by
  apply Equiv.ext
  intro i
  apply (flattenedPositionsEquiv Y).injective
  exact (orderedInput_positions (orderedFixedHom f) i).trans
    (blocksOfFamilyFiberMap_positions f i).symm

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- Every actual fixed-slot component is the original ordered inner block component. -/
theorem orderedFixed_components {n : ℕ} {X Y : Fin n → FiniteFamily C} (f : ∀ i, X i ⟶ Y i)
    (i : Fin (blocksOfFamily X).totalArity) :
    HEq (orderedInputComponent (orderedFixedHom f) i) ((blocksOfFamilyFiberMap
      f).inputComponents i) :=
  (orderedInputComponent_heq (orderedFixedHom f) i).trans (blocksOfFamilyFiberMap_components
    f i).symm

/-- The actual fixed-slot word tensor map is the original inner block tensor map. -/
theorem orderedFixed_inputMap {n : ℕ} {X Y : Fin n → FiniteFamily C} (f : ∀ i, X i ⟶ Y i) :
    orderedInputMap (orderedFixedHom f) = (blocksOfFamilyFiberMap f).inputMap := by
  unfold orderedInputMap Blocks.FiberMap.inputMap
  exact mapEquiv_congr (orderedFixed_inputEquiv f) _ _ (orderedFixed_components f)

/-- The actual fixed-slot outer tensor map is the original tensor of every original inner
tensor map. -/
theorem orderedFixed_outputMap {n : ℕ} {X Y : Fin n → FiniteFamily C} (f : ∀ i, X i ⟶ Y i) :
    orderedOutputMap (orderedFixedHom f) = map (fun i => finiteMap (f i)) := by
  unfold orderedOutputMap orderedFixedHom
  exact mapEquiv_refl _

/-- Every original fixed-slot inner morphism commutes with the actual original ordered block
split. -/
theorem orderedFixed_naturality {n : ℕ} {X Y : Fin n → FiniteFamily C} (f : ∀ i, X i ⟶ Y i) :
    orderedInputMap (orderedFixedHom f) ≫ (blocksOfFamilyIso Y).hom =
      (blocksOfFamilyIso X).hom ≫ orderedOutputMap (orderedFixedHom f) := by
  rw [orderedFixed_inputMap, orderedFixed_outputMap]
  exact blocksOfFamilyIso_fiber_naturality f

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The original ordered outer input bijection with its original inner object equality maps. -/
def orderedReindexHom {m n : ℕ} (e : Fin m ≃ Fin n)
    (X : Fin m → FiniteFamily C) (Y : Fin n → FiniteFamily C) (h : ∀ i, X i = Y (e i)) :
    literalOuterFamily X ⟶ literalOuterFamily Y where
  equiv := e
  hom i := eqToHom (h i)

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- Original ordered reindexing maps compose by the actual original outer input bijection. -/
theorem orderedReindexHom_comp {l m n : ℕ} (e : Fin l ≃ Fin m) (d : Fin m ≃ Fin n)
    (X : Fin l → FiniteFamily C) (Y : Fin m → FiniteFamily C) (Z : Fin n → FiniteFamily C)
    (h : ∀ i, X i = Y (e i)) (k : ∀ j, Y j = Z (d j)) :
    orderedReindexHom e X Y h ≫ orderedReindexHom d Y Z k =
      orderedReindexHom (e.trans d) X Z (fun i => (h i).trans (k (e i))) := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    exact heq_of_eq (eqToHom_trans (h i) (k (e i)))

/-- The actual ordered block split commutes with the specified original reindexing maps. -/
def OrderedReindexNatural {n : ℕ} (e : Equiv.Perm (Fin n)) : Prop :=
  ∀ (X Y : Fin n → FiniteFamily C) (h : ∀ i, X i = Y (e i)),
    orderedInputMap (orderedReindexHom e X Y h) ≫ (blocksOfFamilyIso Y).hom =
      (blocksOfFamilyIso X).hom ≫ orderedOutputMap (orderedReindexHom e X Y h)

/-- The original identity outer input bijection has its actual fixed-slot block split square. -/
theorem orderedReindexNatural_one (n : ℕ) : OrderedReindexNatural (C :=
  C) (1 : Equiv.Perm (Fin n)) := by
  intro X Y h
  exact orderedFixed_naturality (fun i => eqToHom (h i))

/-- Original ordered reindexing squares compose with every original object equality. -/
theorem orderedReindexNatural_mul {n : ℕ} (p q : Equiv.Perm (Fin n))
    (hp : OrderedReindexNatural (C := C) p) (hq : OrderedReindexNatural (C := C) q) :
    OrderedReindexNatural (C := C) (p * q) := by
  intro X Y h
  let Z := X ∘ q.symm
  have k : ∀ i, X i = Z (q i) := fun i => congrArg X (q.symm_apply_apply i).symm
  have l : ∀ i, Z i = Y (p i) := fun i =>
    (h (q.symm i)).trans (congrArg (fun j => Y (p j)) (q.apply_symm_apply i))
  let F := orderedReindexHom q X Z k
  let G := orderedReindexHom p Z Y l
  have hComp : orderedReindexHom (p * q) X Y h = F ≫ G := by
    dsimp only [F, G]
    rw [orderedReindexHom_comp]
    rfl
  rw [hComp, orderedInputMap_comp, orderedOutputMap_comp]
  have hF := hq X Z k
  have hG := hp Z Y l
  simp only [Category.assoc]
  change orderedInputMap F ≫ orderedInputMap G ≫ (blocksOfFamilyIso Y).hom =
    (blocksOfFamilyIso X).hom ≫ orderedOutputMap F ≫ orderedOutputMap G
  rw [hG, ← Category.assoc, hF, Category.assoc]

/-- Original outer permutations whose actual ordered input and output maps commute with
block flattening. -/
def orderedReindexSubmonoid (n : ℕ) : Submonoid (Equiv.Perm (Fin n)) where
  carrier := Set.ofPred (OrderedReindexNatural (C := C))
  one_mem' := orderedReindexNatural_one n
  mul_mem' := fun hp hq => orderedReindexNatural_mul _ _ hp hq

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedReindexNaturality

/- Source proof segment: BlockPairFlatten -/
section source_BlockPairFlatten
/-!
# Original two-final-block flattening maps

The full original block flattening is compared with the original
binary tensor map after its actual carrier equality. The three-block
reflection law is original binary associator naturality.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The original two-final-block tensor carrier is its original binary associated tensor. -/
theorem blockPair_obj_eq (B : Blocks C) {a d : ℕ} (A : Fin a → C) (D : Fin d → C) :
    obj (Blocks.blockTensors (Blocks.snoc (Blocks.snoc B A) D)) =
      (obj B.blockTensors ⊗ obj A) ⊗ obj D := by
  rw [Blocks.obj_blockTensors_snoc, Blocks.obj_blockTensors_snoc]

/-- The original binary map splitting the original two final blocks. -/
def blockPairSplit (B : Blocks C) {a d : ℕ} (A : Fin a → C) (D : Fin d → C) :
    obj (Fin.append (Fin.append B.inputs A) D) ⟶ (obj B.blockTensors ⊗ obj A) ⊗ obj D :=
  (appendIso (Fin.append B.inputs A) D).hom ≫
    (((appendIso B.inputs A).hom ≫ ((Blocks.flattenIso B).hom ⊗ₘ 𝟙 (obj A))) ⊗ₘ 𝟙 (obj D))

set_option backward.isDefEq.respectTransparency false in
/-- The original whole two-final-block flattening is its actual binary split after only the
carrier equality. -/
theorem blockPairSplit_heq (B : Blocks C) {a d : ℕ} (A : Fin a → C) (D : Fin d → C) :
    HEq (Blocks.flattenIso (Blocks.snoc (Blocks.snoc B A) D)).hom (blockPairSplit B A D) := by
  have hA : HEq (Blocks.flattenIso (Blocks.snoc B A)).hom
      ((appendIso B.inputs A).hom ≫ ((Blocks.flattenIso B).hom ⊗ₘ 𝟙 (obj A))) := by
    rw [Blocks.flattenIso_snoc_hom]
    simpa only [Category.assoc, Blocks.inputs] using comp_eqToHom_heq
      ((appendIso B.inputs A).hom ≫ ((Blocks.flattenIso B).hom ⊗ₘ 𝟙 (obj A)))
      (Blocks.obj_blockTensors_snoc B A).symm
  have hT := tensorMapBoundary_heq (D := obj D) (E := obj D) (D' := obj D) (E' := obj D)
    rfl (Blocks.obj_blockTensors_snoc B A) rfl rfl hA
    (HEq.rfl (a := 𝟙 (obj D)))
  have hC := heq_comp rfl rfl
    (congrArg (fun P : C => P ⊗ obj D) (Blocks.obj_blockTensors_snoc B A))
    (HEq.rfl (a := (appendIso (Fin.append B.inputs A) D).hom)) hT
  rw [Blocks.flattenIso_snoc_hom]
  have hStrip := comp_eqToHom_heq
    ((appendIso (Fin.append B.inputs A) D).hom ≫
      ((Blocks.flattenIso (Blocks.snoc B A)).hom ⊗ₘ 𝟙 (obj D)))
    (Blocks.obj_blockTensors_snoc (Blocks.snoc B A) D).symm
  simpa only [Category.assoc, blockPairSplit, Blocks.inputs] using hStrip.trans hC

set_option backward.isDefEq.respectTransparency false in
/-- The original carrier equality turns whole block flattening into its actual binary split map. -/
theorem blockPairSplit_eq (B : Blocks C) {a d : ℕ} (A : Fin a → C) (D : Fin d → C) :
    (Blocks.flattenIso (Blocks.snoc (Blocks.snoc B A) D)).hom ≫ eqToHom (blockPair_obj_eq B A D) =
      blockPairSplit B A D :=
  eq_of_heq ((comp_eqToHom_heq _ _).trans (blockPairSplit_heq B A D))

/-- Original splitting followed by prefix reflection obeys original binary associator naturality. -/
theorem splitPair_prefix_reflection {L M P T A D : C}
    (d : L ⟶ M ⊗ D) (c : M ⟶ P ⊗ A) (f : P ⟶ T) :
    (d ≫ ((c ≫ (f ⊗ₘ 𝟙 A)) ⊗ₘ 𝟙 D)) ≫ (α_ T A D).hom =
      (d ≫ (c ⊗ₘ 𝟙 D) ≫ (α_ P A D).hom) ≫ (f ⊗ₘ 𝟙 (A ⊗ D)) := by
  have hc := tensorHom_comp_tensorHom c (𝟙 D) (f ⊗ₘ 𝟙 A) (𝟙 D)
  simp only [Category.id_comp] at hc
  have hn := associator_naturality f (𝟙 A) (𝟙 D)
  simp only [id_tensorHom_id] at hn
  rw [← hc]
  simp only [Category.assoc]
  rw [hn]

/-- The original two-final-block split joins the original three-block append split naturally. -/
theorem blockPairSplit_assoc (B : Blocks C) {a d : ℕ} (A : Fin a → C) (D : Fin d → C) :
    blockPairSplit B A D ≫ (α_ (obj B.blockTensors) (obj A) (obj D)).hom =
      appendAssocRight B.inputs A D ≫ ((Blocks.flattenIso B).hom ⊗ₘ 𝟙 (obj A ⊗ obj D)) :=
  splitPair_prefix_reflection (appendIso (Fin.append B.inputs A) D).hom
    (appendIso B.inputs A).hom (Blocks.flattenIso B).hom

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_BlockPairFlatten

/- Source proof segment: LastPairFamilies -/
section source_LastPairFamilies
/-!
# Original last-pair outer input data

The literal finite snoc families retain their original unchanged
prefix and two final inputs under the original adjacent transposition.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

/-- The actual adjacent outer input transposition of the two final original blocks. -/
def lastOuterSwap (n : ℕ) : Equiv.Perm (Fin (n + 2)) :=
  Equiv.swap (Fin.last n).castSucc (Fin.last n).succ

/-- The original last outer input has its literal successor last-slot expression. -/
theorem lastOuterSwap_lastIndex (n : ℕ) : (Fin.last n).succ = Fin.last (n + 1) := Fin.ext rfl

/-- Every original prefix input is fixed by the actual final-pair transposition. -/
theorem lastOuterSwap_prefix {n : ℕ} (i : Fin n) :
    lastOuterSwap n i.castSucc.castSucc = i.castSucc.castSucc := by
  have ha : i.castSucc.castSucc ≠ (Fin.last n).castSucc := fun h =>
    (Fin.castSucc_ne_last i) ((Fin.castSucc_injective (n + 1)) h)
  have hd : i.castSucc.castSucc ≠ (Fin.last n).succ := by
    rw [lastOuterSwap_lastIndex]
    exact Fin.castSucc_ne_last i.castSucc
  exact Equiv.swap_apply_of_ne_of_ne ha hd

/-- The original penultimate block is moved to the literal last outer slot. -/
theorem lastOuterSwap_penultimate (n : ℕ) :
    lastOuterSwap n (Fin.last n).castSucc = Fin.last (n + 1) := by
  rw [lastOuterSwap, Equiv.swap_apply_left, lastOuterSwap_lastIndex]

/-- The original last block is moved to the literal penultimate outer slot. -/
theorem lastOuterSwap_last (n : ℕ) :
    lastOuterSwap n (Fin.last (n + 1)) = (Fin.last n).castSucc := by
  rw [← lastOuterSwap_lastIndex, lastOuterSwap, Equiv.swap_apply_right]

/-- The actual original last-pair outer map keeps every original object
in its actual target slot. -/
theorem lastOuterSwap_objects {n : ℕ} {α : Type u} (P : Fin n → α) (A D : α)
    (i : Fin (n + 2)) :
    Fin.snoc (α := fun _ => α) (Fin.snoc (α := fun _ => α) P A) D i =
      Fin.snoc (α := fun _ => α) (Fin.snoc (α := fun _ => α) P D) A (lastOuterSwap n i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last, lastOuterSwap_last, Fin.snoc_castSucc, Fin.snoc_last]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · rw [Fin.snoc_castSucc, Fin.snoc_last, lastOuterSwap_penultimate, Fin.snoc_last]
    · rw [lastOuterSwap_prefix]
      simp only [Fin.snoc_castSucc]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_LastPairFamilies

/- Source proof segment: InputMapTransport -/
section source_InputMapTransport
/-!
# Original input-count and family transport of ordered tensor maps

The complete original count, family, bijection and component data
are transported before choosing either outer-block reindexing map.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- Equal original input counts and every original component retain the whole tensor map. -/
theorem mapEquiv_input_heq {m m' n n' : ℕ} (hm : m = m') (hn : n = n')
    (X : Fin m → C) (X' : Fin m' → C) (Y : Fin n → C) (Y' : Fin n' → C)
    (hX : ∀ i, X i = X' (Fin.cast hm i)) (hY : ∀ i, Y i = Y' (Fin.cast hn i))
    (e : Fin m ≃ Fin n) (e' : Fin m' ≃ Fin n') (he : HEq e e')
    (f : ∀ i, X i ⟶ Y (e i)) (f' : ∀ i, X' i ⟶ Y' (e' i))
    (hf : ∀ i, HEq (f i) (f' (Fin.cast hm i))) : HEq (mapEquiv e f) (mapEquiv e' f') := by
  cases hm
  cases hn
  have hXX : X = X' := funext hX
  have hYY : Y = Y' := funext hY
  cases hXX
  cases hYY
  have heq : e = e' := eq_of_heq he
  cases heq
  have hff : f = f' := funext (fun i => eq_of_heq (hf i))
  cases hff
  rfl

omit [Category C] [MonoidalCategory C] [SymmetricCategory C] in
/-- A whole original block-word equality transports every actual original input. -/
theorem blocks_inputs_transport {B B' : Blocks C} (h : B = B') (i : Fin B.totalArity) :
    B.inputs i = B'.inputs (Fin.cast (congrArg Blocks.totalArity h) i) := by
  cases h
  rfl

omit [SymmetricCategory C] in
/-- The actual original tensor carrier respects a whole original block-word equality. -/
theorem blocks_obj_transport {B B' : Blocks C} (h : B = B') :
    obj B.inputs = obj B'.inputs := congrArg (fun B : Blocks C => obj B.inputs) h

/-- The literal count-conjugated input equivalence retains the original complete equivalence. -/
theorem equiv_count_transport_heq {m m' n n' : ℕ} (hm : m = m') (hn : n = n')
    (e : Fin m ≃ Fin n) :
    HEq ((finCongr hm).symm.trans (e.trans (finCongr hn))) e := by
  cases hm
  cases hn
  rfl

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_InputMapTransport

/- Source proof segment: SnocBlockGeometry -/
section source_SnocBlockGeometry
/-!
# Original full input positions after retaining a last finite block

The block word is its actual snoc. Its full original dependent input
positions split into the unchanged old positions and the retained
last block's original enumeration, including all empty arities.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

variable {C : Type u}

/-- Appending an original finite family retains the actual preceding block word. -/
theorem blocksOfFamily_snoc {n : ℕ} (X : Fin n → FiniteFamily C) (D : FiniteFamily C) :
    blocksOfFamily (Fin.snoc X D) = Blocks.snoc (blocksOfFamily X) (orderedFamily D) := by
  change Blocks.snoc (blocksOfFamily (Fin.init
    (Fin.snoc X D : Fin (n + 1) → FiniteFamily C)))
    (orderedFamily ((Fin.snoc X D : Fin (n + 1) → FiniteFamily C) (Fin.last n))) = _
  rw [Fin.init_snoc, Fin.snoc_last]

/-- The actual total input count after retaining a last original block. -/
theorem snocBlocks_totalArity {n : ℕ} (X : Fin n → FiniteFamily C) (D : FiniteFamily C) :
    (blocksOfFamily (Fin.snoc X D)).totalArity = (blocksOfFamily X).totalArity + arity D :=
  congrArg Blocks.totalArity (blocksOfFamily_snoc X D)

set_option backward.isDefEq.respectTransparency false in
/-- The full original flattened position retains the original preceding position. -/
theorem flattenedPositions_left_full {n : ℕ} (F : Fin (n + 1) → FiniteFamily C)
    (j : Fin (blocksOfFamily (Fin.init F)).totalArity) :
    flattenedPositionsEquiv F (Fin.castAdd (arity (F (Fin.last n))) j) =
      positionsSnocEquiv F (Sum.inl (flattenedPositionsEquiv (Fin.init F) j)) := by
  change (positionsSnocEquiv F
    ((Equiv.sumCongr (blockPositionsEquiv (Fin.init F)) (enumeration (F (Fin.last n))))
      ((Equiv.sumCongr (blocksOfFamily (Fin.init F)).positionEquiv
        (Equiv.refl (Fin (arity (F (Fin.last n))))))
        (finSumFinEquiv.symm (Fin.castAdd (arity (F (Fin.last n))) j))))) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The full original flattened position retains the original final block input. -/
theorem flattenedPositions_right_full {n : ℕ} (F : Fin (n + 1) → FiniteFamily C)
    (j : Fin (arity (F (Fin.last n)))) :
    flattenedPositionsEquiv F
        (Fin.natAdd (blocksOfFamily (Fin.init F)).totalArity j) =
      positionsSnocEquiv F (Sum.inr (enumeration (F (Fin.last n)) j)) := by
  change (positionsSnocEquiv F
    ((Equiv.sumCongr (blockPositionsEquiv (Fin.init F)) (enumeration (F (Fin.last n))))
      ((Equiv.sumCongr (blocksOfFamily (Fin.init F)).positionEquiv
        (Equiv.refl (Fin (arity (F (Fin.last n))))))
        (finSumFinEquiv.symm (Fin.natAdd (blocksOfFamily (Fin.init F)).totalArity j))))) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

/-- Original flattened positions respect equality of the entire original outer family. -/
theorem flattenedPositions_transport {n : ℕ} {F G : Fin n → FiniteFamily C} (h : F = G)
    (j : Fin (blocksOfFamily G).totalArity) :
    flattenedPositionsEquiv F
        (Fin.cast (congrArg (fun H => (blocksOfFamily H).totalArity) h).symm j) =
      cast (congrArg OriginalPositions h).symm (flattenedPositionsEquiv G j) := by
  subst G
  rfl

/-- The actual inner enumeration respects the full original finite-family equality. -/
theorem enumeration_family_transport {F G : FiniteFamily C} (h : F = G)
    (j : Fin (arity G)) :
    enumeration F (Fin.cast (congrArg arity h).symm j) =
      cast (congrArg (fun H : FiniteFamily C => (H.index : Type)) h).symm (enumeration G j) := by
  subst G
  rfl

/-- The original full dependent sum splits into the old positions and the retained last inputs. -/
noncomputable def snocPositionsEquiv {n : ℕ} (X : Fin n → FiniteFamily C)
    (D : FiniteFamily C) : OriginalPositions X ⊕ D.index ≃ OriginalPositions (Fin.snoc X D) :=
  (Equiv.sumCongr
    (Equiv.cast (congrArg OriginalPositions
      (Fin.init_snoc (α := fun _ : Fin (n + 1) => FiniteFamily C) D X)).symm)
    (Equiv.cast (congrArg (fun H : FiniteFamily C => (H.index : Type))
      (Fin.snoc_last (α := fun _ : Fin (n + 1) => FiniteFamily C) D X)).symm)).trans
        (positionsSnocEquiv (Fin.snoc X D))

/-- Inject the actual preceding ordered input into the retained-last block word. -/
noncomputable def snocInputLeft {n : ℕ} (X : Fin n → FiniteFamily C) (D : FiniteFamily C)
    (j : Fin (blocksOfFamily X).totalArity) : Fin (blocksOfFamily (Fin.snoc X D)).totalArity :=
  Fin.cast (snocBlocks_totalArity X D).symm (Fin.castAdd (arity D) j)

/-- Inject the actual final-block input into the retained-last block word. -/
noncomputable def snocInputRight {n : ℕ} (X : Fin n → FiniteFamily C) (D : FiniteFamily C)
    (j : Fin (arity D)) : Fin (blocksOfFamily (Fin.snoc X D)).totalArity :=
  Fin.cast (snocBlocks_totalArity X D).symm (Fin.natAdd (blocksOfFamily X).totalArity j)

/-- The actual old-input injection is the original recursive initial injection
with its count cast. -/
theorem snocInputLeft_recursive {n : ℕ} (X : Fin n → FiniteFamily C) (D : FiniteFamily C)
    (j : Fin (blocksOfFamily X).totalArity) :
    snocInputLeft X D j =
      Fin.castAdd (arity ((Fin.snoc X D : Fin (n + 1) → FiniteFamily C) (Fin.last n)))
        (Fin.cast (congrArg (fun H => (blocksOfFamily H).totalArity)
          (Fin.init_snoc (α := fun _ : Fin (n + 1) => FiniteFamily C) D X)).symm j) := by
  apply Fin.ext
  rfl

/-- The actual last-input injection is the original recursive final injection
with its count cast. -/
theorem snocInputRight_recursive {n : ℕ} (X : Fin n → FiniteFamily C) (D : FiniteFamily C)
    (j : Fin (arity D)) :
    snocInputRight X D j =
      Fin.natAdd (blocksOfFamily (Fin.init
        (Fin.snoc X D : Fin (n + 1) → FiniteFamily C))).totalArity
        (Fin.cast (congrArg arity
          (Fin.snoc_last (α := fun _ : Fin (n + 1) => FiniteFamily C) D X)).symm j) := by
  apply Fin.ext
  change (blocksOfFamily X).totalArity + j.val =
    (blocksOfFamily (Fin.init (Fin.snoc X D : Fin (n + 1) → FiniteFamily C))).totalArity + j.val
  rw [Fin.init_snoc]

/-- The retained-last flatten map retains the entire original preceding dependent input position. -/
theorem flattenedPositions_snoc_left {n : ℕ} (X : Fin n → FiniteFamily C)
    (D : FiniteFamily C) (j : Fin (blocksOfFamily X).totalArity) :
    flattenedPositionsEquiv (Fin.snoc X D) (snocInputLeft X D j) =
      snocPositionsEquiv X D (Sum.inl (flattenedPositionsEquiv X j)) := by
  rw [snocInputLeft_recursive, flattenedPositions_left_full,
    flattenedPositions_transport
      (Fin.init_snoc (α := fun _ : Fin (n + 1) => FiniteFamily C) D X) j]
  rfl

/-- The retained-last flatten map retains the entire original last-block input position. -/
theorem flattenedPositions_snoc_right {n : ℕ} (X : Fin n → FiniteFamily C)
    (D : FiniteFamily C) (j : Fin (arity D)) :
    flattenedPositionsEquiv (Fin.snoc X D) (snocInputRight X D j) =
      snocPositionsEquiv X D (Sum.inr (enumeration D j)) := by
  rw [snocInputRight_recursive, flattenedPositions_right_full,
    enumeration_family_transport
      (Fin.snoc_last (α := fun _ : Fin (n + 1) => FiniteFamily C) D X) j]
  rfl

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_SnocBlockGeometry

/- Source proof segment: LastPairWordShapes -/
section source_LastPairWordShapes
/-!
# Original block-word readbacks of the final outer pair

The source and target words are their literal two original snocs.
Every original input count, input object and tensor carrier is
transported through that actual word equality.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

variable {C : Type u}

/-- The original two-final-block outer family has its literal original block word. -/
theorem lastPair_word_eq {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C) :
    blocksOfFamily (Fin.snoc (Fin.snoc P A) D) =
      Blocks.snoc (Blocks.snoc (blocksOfFamily P) (orderedFamily A)) (orderedFamily D) := by
  rw [blocksOfFamily_snoc, blocksOfFamily_snoc]

/-- The actual original final-pair source retains its complete three-block input count. -/
theorem lastPair_count {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C) :
    (blocksOfFamily (Fin.snoc (Fin.snoc P A) D)).totalArity =
      (blocksOfFamily P).totalArity + arity A + arity D :=
  congrArg Blocks.totalArity (lastPair_word_eq P A D)

/-- Every original final-pair word input retains its original three-block object. -/
theorem lastPair_inputs {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C)
    (i : Fin (blocksOfFamily (Fin.snoc (Fin.snoc P A) D)).totalArity) :
    (blocksOfFamily (Fin.snoc (Fin.snoc P A) D)).inputs i =
      Fin.append (Fin.append (blocksOfFamily P).inputs (orderedFamily A)) (orderedFamily D)
        (Fin.cast (lastPair_count P A D) i) :=
  blocks_inputs_transport (lastPair_word_eq P A D) i

variable [Category.{v} C] [MonoidalCategory C]

/-- The actual original final-pair tensor carrier is the original three-block tensor carrier. -/
theorem lastPair_obj_eq {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C) :
    obj (blocksOfFamily (Fin.snoc (Fin.snoc P A) D)).inputs =
      obj (Fin.append (Fin.append (blocksOfFamily P).inputs (orderedFamily A)) (orderedFamily D)) :=
  blocks_obj_transport (lastPair_word_eq P A D)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_LastPairWordShapes

/- Source proof segment: OrderedFoldReadback -/
section source_OrderedFoldReadback
/-!
# Original ordered block fold source and target readbacks

The original finite-family block fold retains the actual block-tree
flattening map. A retained final block and a final pair are joined to
their original binary tensor maps using the full input block equalities.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

private theorem flattenBlockData_heq (B D : Blocks C) (h : B = D) :
    HEq (Blocks.flattenIso B).hom (Blocks.flattenIso D).hom := by
  cases h
  rfl

/-- The original finite-family block fold differs from the original block-tree fold only by
its carrier equality. -/
theorem blocksOfFamilyIso_fold_heq {n : ℕ} (X : Fin n → FiniteFamily C) :
    HEq (blocksOfFamilyIso X).hom (Blocks.flattenIso (blocksOfFamily X)).hom := by
  unfold blocksOfFamilyIso
  rw [Iso.trans_hom, eqToIso.hom]
  exact comp_eqToHom_heq _ _

/-- The original full block-data equality transports the actual finite-family block fold. -/
theorem blocksOfFamilyIso_shape_heq {n : ℕ} (X : Fin n → FiniteFamily C) (B : Blocks C)
    (h : blocksOfFamily X = B) : HEq (blocksOfFamilyIso X).hom (Blocks.flattenIso B).hom :=
  (blocksOfFamilyIso_fold_heq X).trans (flattenBlockData_heq _ _ h)

set_option backward.isDefEq.respectTransparency false in
/-- A retained final original block has its actual original append split and actual
preceding block fold. -/
theorem blocksOfFamilyIso_snoc_heq {n : ℕ} (X : Fin n → FiniteFamily C) (D : FiniteFamily C) :
    HEq (blocksOfFamilyIso (Fin.snoc X D)).hom
      ((appendIso (blocksOfFamily X).inputs (orderedFamily D)).hom ≫
        ((blocksOfFamilyIso X).hom ⊗ₘ 𝟙 (finiteObj D))) := by
  have hShape := blocksOfFamilyIso_shape_heq (Fin.snoc X D)
    (Blocks.snoc (blocksOfFamily X) (orderedFamily D)) (blocksOfFamily_snoc X D)
  have hSnoc : HEq (Blocks.flattenIso (Blocks.snoc (blocksOfFamily X) (orderedFamily D))).hom
      ((appendIso (blocksOfFamily X).inputs (orderedFamily D)).hom ≫
        ((Blocks.flattenIso (blocksOfFamily X)).hom ⊗ₘ 𝟙 (finiteObj D))) := by
    rw [Blocks.flattenIso_snoc_hom]
    simpa only [Category.assoc, Blocks.inputs, finiteObj] using comp_eqToHom_heq
      ((appendIso (blocksOfFamily X).inputs (orderedFamily D)).hom ≫
        ((Blocks.flattenIso (blocksOfFamily X)).hom ⊗ₘ 𝟙 (finiteObj D)))
      (Blocks.obj_blockTensors_snoc (blocksOfFamily X) (orderedFamily D)).symm
  have hT := tensorMapBoundary_heq
    (D := finiteObj D) (E := finiteObj D) (D' := finiteObj D) (E' := finiteObj D)
    rfl (blocksOfFamily_tensors X).symm rfl rfl (blocksOfFamilyIso_fold_heq X)
      (HEq.rfl (a := 𝟙 (finiteObj D)))
  have hC := heq_comp rfl rfl
    (congrArg (fun P : C => P ⊗ finiteObj D) (blocksOfFamily_tensors X).symm)
    (HEq.rfl (a := (appendIso (blocksOfFamily X).inputs (orderedFamily D)).hom)) hT
  exact hShape.trans (hSnoc.trans hC.symm)

set_option backward.isDefEq.respectTransparency false in
/-- The original ordered two-final-block fold is its full original binary pair split. -/
theorem blocksOfFamilyIso_pair_heq {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C) :
    HEq (blocksOfFamilyIso (Fin.snoc (Fin.snoc P A) D)).hom
      (blockPairSplit (blocksOfFamily P) (orderedFamily A) (orderedFamily D)) :=
  (blocksOfFamilyIso_shape_heq (Fin.snoc (Fin.snoc P A) D) _ (lastPair_word_eq P A D)).trans
    (blockPairSplit_heq (blocksOfFamily P) (orderedFamily A) (orderedFamily D))

/-- The original ordered pair output carrier is its original binary block tensor carrier. -/
theorem blocksOfFamily_pair_output_eq {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C) :
    obj (fun i : Fin (n + 2) => finiteObj
      ((Fin.snoc (Fin.snoc P A) D : Fin (n + 2) → FiniteFamily C) i)) =
      (obj (blocksOfFamily P).blockTensors ⊗ finiteObj A) ⊗ finiteObj D :=
  (blocksOfFamily_tensors (Fin.snoc (Fin.snoc P A) D)).symm.trans
    ((congrArg (fun B : Blocks C => obj B.blockTensors) (lastPair_word_eq P A D)).trans
      (blockPair_obj_eq (blocksOfFamily P) (orderedFamily A) (orderedFamily D)))

/-- The original retained-final output carrier is the tensor of the actual preceding outer
tensor and final block
  tensor. -/
theorem blocksOfFamily_snoc_output_eq {n : ℕ} (X : Fin n → FiniteFamily C) (D : FiniteFamily C) :
    obj (fun i : Fin (n + 1) => finiteObj ((Fin.snoc X D : Fin (n + 1) → FiniteFamily C) i)) =
      obj (fun i => finiteObj (X i)) ⊗ finiteObj D :=
  (blocksOfFamily_tensors (Fin.snoc X D)).symm.trans
    ((congrArg (fun B : Blocks C => obj B.blockTensors) (blocksOfFamily_snoc X D)).trans
      ((Blocks.obj_blockTensors_snoc (blocksOfFamily X) (orderedFamily D)).trans
        (congrArg (fun P : C => P ⊗ finiteObj D) (blocksOfFamily_tensors X))))

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedFoldReadback

/- Source proof segment: BlockFlipIso -/
section source_BlockFlipIso
/-!
# The original heterogeneous two-block tensor flip

The construction uses the actual finite input bijection and its
original component equality isomorphisms. Empty blocks use the
original count transports and binary unitors.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The original two-block input bijection and its original component isomorphisms. -/
noncomputable def blockFlipIso {m n : ℕ} (X : Fin m → C) (Y : Fin n → C) :
    obj (Fin.append X Y) ≅ obj (Fin.append Y X) :=
  isoEquiv (finAddFlip : Fin (m + n) ≃ Fin (n + m))
    (fun i => eqToIso (blockFlip_objects X Y i))

/-- The original two-block flip has precisely its original finite-bijection tensor map. -/
theorem blockFlipIso_hom {m n : ℕ} (X : Fin m → C) (Y : Fin n → C) :
    (blockFlipIso X Y).hom =
      mapEquiv (finAddFlip : Fin (m + n) ≃ Fin (n + m))
        (fun i => eqToHom (blockFlip_objects X Y i)) :=
  isoEquiv_hom _ _

/-- The actual block reindexing retains its original inverse family equality transport. -/
theorem blockFlipIso_reindex {m n : ℕ} (X : Fin m → C) (Y : Fin n → C) :
    blockFlipIso X Y =
      bijectionIso (finAddFlip : Fin (m + n) ≃ Fin (n + m)) (Fin.append X Y) ≪≫
        eqToIso (congrArg obj (reindexedFamily_eq
          (finAddFlip : Fin (m + n) ≃ Fin (n + m))
            (Fin.append X Y) (Fin.append Y X) (blockFlip_objects X Y))) :=
  isoEquiv_eqToIso _ _ _ _

omit [Category C] [MonoidalCategory C] [SymmetricCategory C] in
/-- Every original input is retained through the empty-right count transport. -/
theorem blockFlip_empty_right_objects {m : ℕ} (X : Fin m → C) (Y : Fin 0 → C)
    (i : Fin (m + 0)) :
    Fin.append X Y i = Fin.append Y X (Fin.cast (Nat.zero_add m).symm i) :=
  (blockFlip_objects X Y i).trans (congrArg (Fin.append Y X)
    (congrArg (fun e : Fin (m + 0) ≃ Fin (0 + m) => e i) (blockFlip_zero_right_equiv m)))

omit [Category C] [MonoidalCategory C] [SymmetricCategory C] in
/-- Every original input is retained through the empty-left count transport. -/
theorem blockFlip_empty_left_objects {n : ℕ} (X : Fin 0 → C) (Y : Fin n → C)
    (i : Fin (0 + n)) :
    Fin.append X Y i = Fin.append Y X (Fin.cast (Nat.zero_add n) i) :=
  (blockFlip_objects X Y i).trans (congrArg (Fin.append Y X)
    (congrArg (fun e : Fin (0 + n) ≃ Fin (n + 0) => e i) (blockFlip_zero_left_equiv n)))

/-- An empty right block has the actual original count/object transport isomorphism. -/
theorem blockFlipIso_empty_right_eqToIso {m : ℕ} (X : Fin m → C) (Y : Fin 0 → C) :
    blockFlipIso X Y = eqToIso (obj_congr (Nat.zero_add m).symm
      (Fin.append X Y) (Fin.append Y X) (blockFlip_empty_right_objects X Y)) :=
  isoEquiv_eqToIso_cast _ _ (blockFlip_zero_right_equiv m) _ _ (blockFlip_objects X Y)

/-- An empty left block has the actual original count/object transport isomorphism. -/
theorem blockFlipIso_empty_left_eqToIso {n : ℕ} (X : Fin 0 → C) (Y : Fin n → C) :
    blockFlipIso X Y = eqToIso (obj_congr (Nat.zero_add n)
      (Fin.append X Y) (Fin.append Y X) (blockFlip_empty_left_objects X Y)) :=
  isoEquiv_eqToIso_cast _ _ (blockFlip_zero_left_equiv n) _ _ (blockFlip_objects X Y)

set_option backward.isDefEq.respectTransparency false in
/-- The actual empty-right two-block flip is the ambient original unit braiding. -/
theorem blockFlipIso_empty_right {m : ℕ} (X : Fin m → C) (Y : Fin 0 → C) :
    (blockFlipIso X Y).hom ≫ (appendIso Y X).hom =
      (appendIso X Y).hom ≫ (β_ (obj X) (obj Y)).hom := by
  have hb : (β_ (obj X) (obj Y)).hom =
      (ρ_ (obj X)).hom ≫ (λ_ (obj X)).inv := by
    change (β_ (obj X) (𝟙_ C)).hom = _
    rw [braiding_tensorUnit_right]
  apply (cancel_mono (λ_ (obj X)).hom).mp
  simp only [Category.assoc]
  rw [appendIso_empty_left, blockFlipIso_empty_right_eqToIso, eqToIso.hom,
    eqToHom_trans, hb]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [appendIso_empty_right]

set_option backward.isDefEq.respectTransparency false in
/-- The actual empty-left two-block flip is the ambient original unit braiding. -/
theorem blockFlipIso_empty_left {n : ℕ} (X : Fin 0 → C) (Y : Fin n → C) :
    (blockFlipIso X Y).hom ≫ (appendIso Y X).hom =
      (appendIso X Y).hom ≫ (β_ (obj X) (obj Y)).hom := by
  have hb : (β_ (obj X) (obj Y)).hom =
      (λ_ (obj Y)).hom ≫ (ρ_ (obj Y)).inv := by
    change (β_ (𝟙_ C) (obj Y)).hom = _
    rw [braiding_tensorUnit_left]
  apply (cancel_mono (ρ_ (obj Y)).hom).mp
  simp only [Category.assoc]
  rw [appendIso_empty_right, blockFlipIso_empty_left_eqToIso, eqToIso.hom,
    eqToHom_trans, hb]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [appendIso_empty_left]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_BlockFlipIso

/- Source proof segment: AppendAssociatorInput -/
section source_AppendAssociatorInput
/-!
# Original append count transports as actual finite input isomorphisms

Both orientations of the original three-block count transport are
identified with their actual input bijections and original component
equality isomorphisms, for every finite block length.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The original append associator is the actual forward finite count/component transport. -/
theorem appendAssociator_input {m n p : ℕ}
    (X : Fin m → C) (Y : Fin n → C) (Z : Fin p → C) :
    isoEquiv (finCongr (Nat.add_assoc m n p))
        (fun i => eqToIso (congrFun (Fin.append_assoc X Y Z) i)) =
      appendAssociator X Y Z :=
  isoEquiv_finCongr _ _ _ _

/-- The original append inverse transports its actual inverse finite input components. -/
theorem appendAssociator_input_symm {m n p : ℕ}
    (X : Fin m → C) (Y : Fin n → C) (Z : Fin p → C) :
    isoEquiv (finCongr (Nat.add_assoc m n p)).symm
        (fun i => eqToIso (inverseInputEquality (finCongr (Nat.add_assoc m n p))
          (Fin.append (Fin.append X Y) Z) (Fin.append X (Fin.append Y Z))
            (congrFun (Fin.append_assoc X Y Z)) i)) =
      (appendAssociator X Y Z).symm :=
  (isoEquiv_eq_inverse _ _ _ _).symm.trans
    (congrArg Iso.symm (appendAssociator_input X Y Z))

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_AppendAssociatorInput

/- Source proof segment: InputIsoFactorFactory -/
section source_InputIsoFactorFactory
/-!
# Generic composition factory for original finite input transports

The complete finite input data and component equalities are handled
before choosing the five source factors of either actual block flip.
The factor equality is an equality of original input bijections.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- Original consecutive finite input factors tensor to their original whole input map. -/
theorem isoEquiv_eq_factor_five {n₀ n₁ n₂ n₃ n₄ n₅ : ℕ}
    (X₀ : Fin n₀ → C) (X₁ : Fin n₁ → C) (X₂ : Fin n₂ → C)
    (X₃ : Fin n₃ → C) (X₄ : Fin n₄ → C) (X₅ : Fin n₅ → C)
    (e₀ : Fin n₀ ≃ Fin n₁) (e₁ : Fin n₁ ≃ Fin n₂) (e₂ : Fin n₂ ≃ Fin n₃)
    (e₃ : Fin n₃ ≃ Fin n₄) (e₄ : Fin n₄ ≃ Fin n₅) (e : Fin n₀ ≃ Fin n₅)
    (he : e = (((e₀.trans e₁).trans e₂).trans e₃).trans e₄)
    (h₀ : ∀ i, X₀ i = X₁ (e₀ i)) (h₁ : ∀ i, X₁ i = X₂ (e₁ i))
    (h₂ : ∀ i, X₂ i = X₃ (e₂ i)) (h₃ : ∀ i, X₃ i = X₄ (e₃ i))
    (h₄ : ∀ i, X₄ i = X₅ (e₄ i)) (h : ∀ i, X₀ i = X₅ (e i)) :
    isoEquiv e (fun i => eqToIso (h i)) =
      isoEquiv e₀ (fun i => eqToIso (h₀ i)) ≪≫
        isoEquiv e₁ (fun i => eqToIso (h₁ i)) ≪≫
          isoEquiv e₂ (fun i => eqToIso (h₂ i)) ≪≫
            isoEquiv e₃ (fun i => eqToIso (h₃ i)) ≪≫
              isoEquiv e₄ (fun i => eqToIso (h₄ i)) := by
  symm
  simp only [← Iso.trans_assoc]
  rw [isoEquiv_eq_trans, isoEquiv_eq_trans, isoEquiv_eq_trans, isoEquiv_eq_trans]
  exact isoEquiv_eq_congr he.symm _ h

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_InputIsoFactorFactory

/- Source proof segment: BlockInputFactors -/
section source_BlockInputFactors
/-!
# All original input-count transports in the two block-flip factors

The two existing pure finite permutation factorizations are reused.
The additional identity count transports record every original
three-block interpretation needed by the heterogeneous tensor maps.
-/

@[expose] public section

set_option autoImplicit false

namespace CategoryTheory.MonoidalCategory.OrderedTensor

/-- The original inverse count transport retains precisely the reversed count equality. -/
theorem finCongr_inverse {m n : ℕ} (h : m = n) :
    (finCongr h).symm = finCongr h.symm := by
  cases h
  rfl

/-- The original append count transport ending in one input retains the actual input identity. -/
theorem finCongr_assoc_one (m n : ℕ) :
    (finCongr (Nat.add_assoc m n 1) : Fin ((m + n) + 1) ≃ Fin (m + (n + 1))) =
      Equiv.refl (Fin ((m + n) + 1)) := by
  apply Equiv.ext
  intro i
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The right-successor block flip keeps every original three-block count transport. -/
theorem blockFlip_right_input_factor (m n : ℕ) :
    (finAddFlip : Fin (m + (n + 1)) ≃ Fin ((n + 1) + m)) =
      ((((finCongr (Nat.add_assoc m n 1)).symm.trans
        (sumInputsEquiv (finAddFlip : Fin (m + n) ≃ Fin (n + m))
          (Equiv.refl (Fin 1)))).trans
        (finCongr (Nat.add_assoc n m 1))).trans
        (sumInputsEquiv (Equiv.refl (Fin n))
          (finAddFlip : Fin (m + 1) ≃ Fin (1 + m)))).trans
        (finCongr (Nat.add_assoc n 1 m)).symm := by
  rw [finCongr_assoc_one m n, finCongr_assoc_one n m]
  let E : Fin ((m + n) + 1) ≃ Fin ((n + m) + 1) :=
    sumInputsEquiv (finAddFlip : Fin (m + n) ≃ Fin (n + m)) (Equiv.refl (Fin 1))
  let F : Fin (n + (m + 1)) ≃ Fin (n + (1 + m)) :=
    sumInputsEquiv (Equiv.refl (Fin n)) (finAddFlip : Fin (m + 1) ≃ Fin (1 + m))
  let K : Fin (n + (1 + m)) ≃ Fin ((n + 1) + m) :=
    (finCongr (Nat.add_assoc n 1 m)).symm
  change (finAddFlip : Fin (m + (n + 1)) ≃ Fin ((n + 1) + m)) =
    (E.trans F).trans K
  dsimp only [E, F, K]
  rw [finCongr_inverse]
  simpa only [sumInputsEquiv, Equiv.trans_assoc] using
    CategoryTheory.MonoidalCategory.SymmetricTensorPower.finAddFlip_succ_right_factor m n

set_option backward.isDefEq.respectTransparency false in
/-- The left-successor singleton flip keeps every original three-block count transport. -/
theorem blockFlip_left_singleton_input_factor (m : ℕ) :
    (finAddFlip : Fin ((m + 1) + 1) ≃ Fin (1 + (m + 1))) =
      ((((finCongr (Nat.add_assoc m 1 1)).trans
        (sumInputsEquiv (Equiv.refl (Fin m))
          (finAddFlip : Fin (1 + 1) ≃ Fin (1 + 1)))).trans
        (finCongr (Nat.add_assoc m 1 1)).symm).trans
        (sumInputsEquiv (finAddFlip : Fin (m + 1) ≃ Fin (1 + m))
          (Equiv.refl (Fin 1)))).trans
        (finCongr (Nat.add_assoc 1 m 1)) := by
  rw [finCongr_assoc_one 1 m, Equiv.trans_refl]
  rw [finCongr_inverse]
  simpa only [sumInputsEquiv, Equiv.trans_assoc] using
    CategoryTheory.MonoidalCategory.SymmetricTensorPower.finAddFlip_succ_left_one_factor m

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_BlockInputFactors

/- Source proof segment: BlockFlipFactors -/
section source_BlockFlipFactors
/-!
# Actual heterogeneous block-flip factors

The original permutation action is factored using its actual finite
input bijections, original component equality maps, and all original
append count transports. No block braiding outcome is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The original right-successor block input route with all original append transports. -/
noncomputable def blockFlipRightRoute {m n : ℕ}
    (X : Fin m → C) (Y : Fin n → C) (Z : Fin 1 → C) :
    obj (Fin.append X (Fin.append Y Z)) ≅ obj (Fin.append (Fin.append Y Z) X) :=
  (appendAssociator X Y Z).symm ≪≫
    sumNamedIso (finAddFlip : Fin (m + n) ≃ Fin (n + m)) (Equiv.refl (Fin 1))
      (Fin.append X Y) Z (Fin.append Y X) Z (blockFlip_objects X Y) (fun _ => rfl) ≪≫
    appendAssociator Y X Z ≪≫
    sumNamedIso (Equiv.refl (Fin n)) (finAddFlip : Fin (m + 1) ≃ Fin (1 + m))
      Y (Fin.append X Z) Y (Fin.append Z X) (fun _ => rfl) (blockFlip_objects X Z) ≪≫
    (appendAssociator Y Z X).symm

set_option backward.isDefEq.respectTransparency false in
/-- The actual whole right-successor block action has its original five input factors. -/
theorem blockFlipIso_right_factor {m n : ℕ}
    (X : Fin m → C) (Y : Fin n → C) (Z : Fin 1 → C) :
    blockFlipIso X (Fin.append Y Z) = blockFlipRightRoute X Y Z := by
  have h := isoEquiv_eq_factor_five
    (Fin.append X (Fin.append Y Z)) (Fin.append (Fin.append X Y) Z)
    (Fin.append (Fin.append Y X) Z) (Fin.append Y (Fin.append X Z))
    (Fin.append Y (Fin.append Z X)) (Fin.append (Fin.append Y Z) X)
    (finCongr (Nat.add_assoc m n 1)).symm
    (sumInputsEquiv (finAddFlip : Fin (m + n) ≃ Fin (n + m)) (Equiv.refl (Fin 1)))
    (finCongr (Nat.add_assoc n m 1))
    (sumInputsEquiv (Equiv.refl (Fin n)) (finAddFlip : Fin (m + 1) ≃ Fin (1 + m)))
    (finCongr (Nat.add_assoc n 1 m)).symm
    (finAddFlip : Fin (m + (n + 1)) ≃ Fin ((n + 1) + m))
    (blockFlip_right_input_factor m n)
    (inverseInputEquality (finCongr (Nat.add_assoc m n 1))
      (Fin.append (Fin.append X Y) Z) (Fin.append X (Fin.append Y Z))
        (congrFun (Fin.append_assoc X Y Z)))
    (sumInputs_objects _ _ (Fin.append X Y) Z (Fin.append Y X) Z
      (blockFlip_objects X Y) (fun _ => rfl))
    (congrFun (Fin.append_assoc Y X Z))
    (sumInputs_objects _ _ Y (Fin.append X Z) Y (Fin.append Z X)
      (fun _ => rfl) (blockFlip_objects X Z))
    (inverseInputEquality (finCongr (Nat.add_assoc n 1 m))
      (Fin.append (Fin.append Y Z) X) (Fin.append Y (Fin.append Z X))
        (congrFun (Fin.append_assoc Y Z X)))
    (blockFlip_objects X (Fin.append Y Z))
  change blockFlipIso X (Fin.append Y Z) = _ at h
  rw [appendAssociator_input_symm, appendAssociator_input,
    appendAssociator_input_symm] at h
  exact h

/-- The original left-successor singleton input route with all original append transports. -/
noncomputable def blockFlipLeftSingletonRoute {m : ℕ}
    (X : Fin m → C) (Y Z : Fin 1 → C) :
    obj (Fin.append (Fin.append X Y) Z) ≅ obj (Fin.append Z (Fin.append X Y)) :=
  appendAssociator X Y Z ≪≫
    sumNamedIso (Equiv.refl (Fin m)) (finAddFlip : Fin (1 + 1) ≃ Fin (1 + 1))
      X (Fin.append Y Z) X (Fin.append Z Y) (fun _ => rfl) (blockFlip_objects Y Z) ≪≫
    (appendAssociator X Z Y).symm ≪≫
    sumNamedIso (finAddFlip : Fin (m + 1) ≃ Fin (1 + m)) (Equiv.refl (Fin 1))
      (Fin.append X Z) Y (Fin.append Z X) Y (blockFlip_objects X Z) (fun _ => rfl) ≪≫
    appendAssociator Z X Y

set_option backward.isDefEq.respectTransparency false in
/-- The actual left-successor singleton action has its original five input factors. -/
theorem blockFlipIso_left_singleton_factor {m : ℕ}
    (X : Fin m → C) (Y Z : Fin 1 → C) :
    blockFlipIso (Fin.append X Y) Z = blockFlipLeftSingletonRoute X Y Z := by
  have h := isoEquiv_eq_factor_five
    (Fin.append (Fin.append X Y) Z) (Fin.append X (Fin.append Y Z))
    (Fin.append X (Fin.append Z Y)) (Fin.append (Fin.append X Z) Y)
    (Fin.append (Fin.append Z X) Y) (Fin.append Z (Fin.append X Y))
    (finCongr (Nat.add_assoc m 1 1))
    (sumInputsEquiv (Equiv.refl (Fin m)) (finAddFlip : Fin (1 + 1) ≃ Fin (1 + 1)))
    (finCongr (Nat.add_assoc m 1 1)).symm
    (sumInputsEquiv (finAddFlip : Fin (m + 1) ≃ Fin (1 + m)) (Equiv.refl (Fin 1)))
    (finCongr (Nat.add_assoc 1 m 1))
    (finAddFlip : Fin ((m + 1) + 1) ≃ Fin (1 + (m + 1)))
    (blockFlip_left_singleton_input_factor m)
    (congrFun (Fin.append_assoc X Y Z))
    (sumInputs_objects _ _ X (Fin.append Y Z) X (Fin.append Z Y)
      (fun _ => rfl) (blockFlip_objects Y Z))
    (inverseInputEquality (finCongr (Nat.add_assoc m 1 1))
      (Fin.append (Fin.append X Z) Y) (Fin.append X (Fin.append Z Y))
        (congrFun (Fin.append_assoc X Z Y)))
    (sumInputs_objects _ _ (Fin.append X Z) Y (Fin.append Z X) Y
      (blockFlip_objects X Z) (fun _ => rfl))
    (congrFun (Fin.append_assoc Z X Y))
    (blockFlip_objects (Fin.append X Y) Z)
  change blockFlipIso (Fin.append X Y) Z = _ at h
  rw [appendAssociator_input, appendAssociator_input_symm,
    appendAssociator_input] at h
  exact h

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_BlockFlipFactors

/- Source proof segment: AppendSplitIso -/
section source_AppendSplitIso
/-!
# Complete original three-block append split isomorphisms

The original append associator is expressed through the original
two-block splits and the ambient binary associator. Both orientations
retain the actual original finite family count transport.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The complete original three-block count transport agrees with the ambient split associator. -/
theorem appendAssociator_split {m n p : ℕ}
    (X : Fin m → C) (Y : Fin n → C) (Z : Fin p → C) :
    appendAssociator X Y Z =
      appendIso (Fin.append X Y) Z ≪≫ tensorIso (appendIso X Y) (Iso.refl (obj Z)) ≪≫
        (α_ (obj X) (obj Y) (obj Z)) ≪≫
          tensorIso (Iso.refl (obj X)) (appendIso Y Z).symm ≪≫
            (appendIso X (Fin.append Y Z)).symm := by
  apply Iso.ext
  simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, Iso.symm_hom]
  have h := appendIso_assoc X Y Z
  apply (cancel_mono ((appendIso X (Fin.append Y Z)).hom ≫
    (𝟙 (obj X) ⊗ₘ (appendIso Y Z).hom))).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, id_tensorHom,
    whiskerLeft_inv_hom, Category.comp_id] using h

/-- The complete original inverse three-block count transport has its original split formula. -/
theorem appendAssociator_split_inv {m n p : ℕ}
    (X : Fin m → C) (Y : Fin n → C) (Z : Fin p → C) :
    (appendAssociator X Y Z).symm =
      appendIso X (Fin.append Y Z) ≪≫ tensorIso (Iso.refl (obj X)) (appendIso Y Z) ≪≫
        (α_ (obj X) (obj Y) (obj Z)).symm ≪≫
          tensorIso (appendIso X Y).symm (Iso.refl (obj Z)) ≪≫
            (appendIso (Fin.append X Y) Z).symm := by
  rw [appendAssociator_split]
  apply Iso.ext
  simp only [Iso.symm_hom, Iso.trans_inv, tensorIso_inv, Iso.refl_inv,
    Iso.symm_inv, Iso.trans_hom, tensorIso_hom, Iso.refl_hom, Category.assoc]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_AppendSplitIso

/- Source proof segment: BlockHexagonFactory -/
section source_BlockHexagonFactory
/-!
# Original append block comparison hexagon

The original two block comparison squares are joined through the
proved original append associator and ambient braided hexagon. This
is a generic proof join for actual input maps supplied later.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The original two successive block comparison squares give the original right hexagon. -/
theorem appendBlock_right_hexagon {m n p : ℕ}
    (X : Fin m → C) (Y : Fin n → C) (Z : Fin p → C)
    (B : obj (Fin.append (Fin.append X Y) Z) ≅ obj (Fin.append (Fin.append Y X) Z))
    (D : obj (Fin.append Y (Fin.append X Z)) ≅ obj (Fin.append Y (Fin.append Z X)))
    (hB : B ≪≫ appendIso (Fin.append Y X) Z =
      appendIso (Fin.append X Y) Z ≪≫
        tensorIso (appendIso X Y ≪≫ β_ (obj X) (obj Y) ≪≫ (appendIso Y X).symm)
          (Iso.refl (obj Z)))
    (hD : D ≪≫ appendIso Y (Fin.append Z X) =
      appendIso Y (Fin.append X Z) ≪≫ tensorIso (Iso.refl (obj Y))
        (appendIso X Z ≪≫ β_ (obj X) (obj Z) ≪≫ (appendIso Z X).symm)) :
    (appendAssociator X Y Z).symm ≪≫ B ≪≫ appendAssociator Y X Z ≪≫ D ≪≫
        (appendAssociator Y Z X).symm ≪≫ appendIso (Fin.append Y Z) X =
      appendIso X (Fin.append Y Z) ≪≫ β_ (obj X) (obj (Fin.append Y Z)) := by
  have hB' : B = appendIso (Fin.append X Y) Z ≪≫
      tensorIso (appendIso X Y ≪≫ β_ (obj X) (obj Y) ≪≫ (appendIso Y X).symm)
        (Iso.refl (obj Z)) ≪≫ (appendIso (Fin.append Y X) Z).symm := by
    simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using
      congrArg (fun K => K ≪≫ (appendIso (Fin.append Y X) Z).symm) hB
  have hD' : D = appendIso Y (Fin.append X Z) ≪≫ tensorIso (Iso.refl (obj Y))
      (appendIso X Z ≪≫ β_ (obj X) (obj Z) ≪≫ (appendIso Z X).symm) ≪≫
        (appendIso Y (Fin.append Z X)).symm := by
    simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using
      congrArg (fun K => K ≪≫ (appendIso Y (Fin.append Z X)).symm) hD
  rw [hB', hD', appendAssociator_split_inv, appendAssociator_split,
    appendAssociator_split_inv]
  apply Iso.ext
  simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  simp only [id_tensorHom, tensorHom_id, comp_whiskerRight, whiskerLeft_comp, Category.assoc,
    whiskerLeft_inv_hom_assoc, inv_hom_whiskerRight_assoc]
  simp only [Iso.inv_hom_id, Category.comp_id]
  rw [← BraidedCategory.braiding_tensor_right_hom_assoc]
  slice_lhs 2 3 =>
    rw [← id_tensorHom, BraidedCategory.braiding_naturality]
  simp only [tensorHom_id, Category.assoc, hom_inv_whiskerRight, Category.comp_id]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_BlockHexagonFactory

/- Source proof segment: BlockLeftHexagonFactory -/
section source_BlockLeftHexagonFactory
/-!
# Original left append block comparison hexagon

The original retained-prefix and retained-suffix comparison squares
join through the original append count transports and ambient left
braided hexagon.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The original two successive comparison squares give the original left block hexagon. -/
theorem appendBlock_left_hexagon {m n p : ℕ}
    (X : Fin m → C) (Y : Fin n → C) (Z : Fin p → C)
    (B : obj (Fin.append X (Fin.append Y Z)) ≅ obj (Fin.append X (Fin.append Z Y)))
    (D : obj (Fin.append (Fin.append X Z) Y) ≅ obj (Fin.append (Fin.append Z X) Y))
    (hB : B ≪≫ appendIso X (Fin.append Z Y) =
      appendIso X (Fin.append Y Z) ≪≫ tensorIso (Iso.refl (obj X))
        (appendIso Y Z ≪≫ β_ (obj Y) (obj Z) ≪≫ (appendIso Z Y).symm))
    (hD : D ≪≫ appendIso (Fin.append Z X) Y =
      appendIso (Fin.append X Z) Y ≪≫
        tensorIso (appendIso X Z ≪≫ β_ (obj X) (obj Z) ≪≫ (appendIso Z X).symm)
          (Iso.refl (obj Y))) :
    appendAssociator X Y Z ≪≫ B ≪≫ (appendAssociator X Z Y).symm ≪≫ D ≪≫
        appendAssociator Z X Y ≪≫ appendIso Z (Fin.append X Y) =
      appendIso (Fin.append X Y) Z ≪≫ β_ (obj (Fin.append X Y)) (obj Z) := by
  have hB' : B = appendIso X (Fin.append Y Z) ≪≫ tensorIso (Iso.refl (obj X))
      (appendIso Y Z ≪≫ β_ (obj Y) (obj Z) ≪≫ (appendIso Z Y).symm) ≪≫
        (appendIso X (Fin.append Z Y)).symm := by
    simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using
      congrArg (fun K => K ≪≫ (appendIso X (Fin.append Z Y)).symm) hB
  have hD' : D = appendIso (Fin.append X Z) Y ≪≫
      tensorIso (appendIso X Z ≪≫ β_ (obj X) (obj Z) ≪≫ (appendIso Z X).symm)
        (Iso.refl (obj Y)) ≪≫ (appendIso (Fin.append Z X) Y).symm := by
    simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using
      congrArg (fun K => K ≪≫ (appendIso (Fin.append Z X) Y).symm) hD
  rw [hB', hD', appendAssociator_split, appendAssociator_split_inv, appendAssociator_split]
  apply Iso.ext
  simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  simp only [id_tensorHom, tensorHom_id, comp_whiskerRight, whiskerLeft_comp, Category.assoc,
    whiskerLeft_inv_hom_assoc, inv_hom_whiskerRight_assoc]
  simp only [Iso.inv_hom_id, Category.comp_id]
  rw [← BraidedCategory.braiding_tensor_left_hom_assoc]
  slice_lhs 2 3 =>
    rw [← tensorHom_id, BraidedCategory.braiding_naturality]
  simp only [id_tensorHom, Category.assoc, whiskerLeft_hom_inv, Category.comp_id]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_BlockLeftHexagonFactory

/- Source proof segment: SplitConjugacy -/
section source_SplitConjugacy
/-!
# Generic original split-isomorphism conjugacy
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- A proved original split comparison retains its complete conjugated isomorphism. -/
theorem iso_split_conjugacy {A A' B B' : C} (s : A ≅ B) (t : A' ≅ B') (f : A ≅ A')
    (g : B ≅ B') (h : f.hom ≫ t.hom = s.hom ≫ g.hom) :
    f = s ≪≫ g ≪≫ t.symm := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom]
  apply (cancel_mono t.hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_SplitConjugacy

/- Source proof segment: BlockBraidingSteps -/
section source_BlockBraidingSteps
/-!
# Original heterogeneous block braiding successor steps

The actual five-factor input maps are joined to the complete original
sum comparison and the original binary hexagons. The induction uses
only already proved lower-block braiding comparisons.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- Original lower-block braiding comparisons give the actual right-successor block comparison. -/
theorem blockFlipIso_right_step {m n : ℕ}
    (X : Fin m → C) (Y : Fin n → C) (Z : Fin 1 → C)
    (hXY : (blockFlipIso X Y).hom ≫ (appendIso Y X).hom =
      (appendIso X Y).hom ≫ (β_ (obj X) (obj Y)).hom)
    (hXZ : (blockFlipIso X Z).hom ≫ (appendIso Z X).hom =
      (appendIso X Z).hom ≫ (β_ (obj X) (obj Z)).hom) :
    (blockFlipIso X (Fin.append Y Z)).hom ≫ (appendIso (Fin.append Y Z) X).hom =
      (appendIso X (Fin.append Y Z)).hom ≫ (β_ (obj X) (obj (Fin.append Y Z))).hom := by
  have hXYiso := iso_split_conjugacy (appendIso X Y) (appendIso Y X)
    (blockFlipIso X Y) (β_ (obj X) (obj Y)) hXY
  have hXZiso := iso_split_conjugacy (appendIso X Z) (appendIso Z X)
    (blockFlipIso X Z) (β_ (obj X) (obj Z)) hXZ
  let B := sumNamedIso (finAddFlip : Fin (m + n) ≃ Fin (n + m)) (Equiv.refl (Fin 1))
    (Fin.append X Y) Z (Fin.append Y X) Z (blockFlip_objects X Y) (fun _ => rfl)
  let D := sumNamedIso (Equiv.refl (Fin n)) (finAddFlip : Fin (m + 1) ≃ Fin (1 + m))
    Y (Fin.append X Z) Y (Fin.append Z X) (fun _ => rfl) (blockFlip_objects X Z)
  have hB : B ≪≫ appendIso (Fin.append Y X) Z =
      appendIso (Fin.append X Y) Z ≪≫ tensorIso
        (appendIso X Y ≪≫ β_ (obj X) (obj Y) ≪≫ (appendIso Y X).symm)
        (Iso.refl (obj Z)) := by
    have h := sumNamedIso_append
      (finAddFlip : Fin (m + n) ≃ Fin (n + m)) (Equiv.refl (Fin 1))
      (Fin.append X Y) Z (Fin.append Y X) Z
      (blockFlip_objects X Y) (fun _ => rfl)
    simp only [eqToIso_refl] at h
    rw [isoEquiv_refl_id] at h
    change B ≪≫ appendIso (Fin.append Y X) Z =
      appendIso (Fin.append X Y) Z ≪≫ tensorIso (blockFlipIso X Y) (Iso.refl (obj Z)) at h
    rw [hXYiso] at h
    exact h
  have hD : D ≪≫ appendIso Y (Fin.append Z X) =
      appendIso Y (Fin.append X Z) ≪≫ tensorIso (Iso.refl (obj Y))
        (appendIso X Z ≪≫ β_ (obj X) (obj Z) ≪≫ (appendIso Z X).symm) := by
    have h := sumNamedIso_append (Equiv.refl (Fin n))
      (finAddFlip : Fin (m + 1) ≃ Fin (1 + m)) Y (Fin.append X Z) Y (Fin.append Z X)
      (fun _ => rfl) (blockFlip_objects X Z)
    simp only [eqToIso_refl] at h
    rw [isoEquiv_refl_id] at h
    change D ≪≫ appendIso Y (Fin.append Z X) =
      appendIso Y (Fin.append X Z) ≪≫ tensorIso (Iso.refl (obj Y)) (blockFlipIso X Z) at h
    rw [hXZiso] at h
    exact h
  have h := appendBlock_right_hexagon X Y Z B D hB hD
  have hIso : blockFlipIso X (Fin.append Y Z) ≪≫ appendIso (Fin.append Y Z) X =
      appendIso X (Fin.append Y Z) ≪≫ β_ (obj X) (obj (Fin.append Y Z)) := by
    rw [blockFlipIso_right_factor]
    dsimp only [blockFlipRightRoute, B, D] at h ⊢
    simpa only [Iso.trans_assoc] using h
  exact congrArg Iso.hom hIso

set_option backward.isDefEq.respectTransparency false in
/-- Original lower singleton comparisons give the actual left-successor singleton comparison. -/
theorem blockFlipIso_left_singleton_step {m : ℕ}
    (X : Fin m → C) (Y Z : Fin 1 → C)
    (hYZ : (blockFlipIso Y Z).hom ≫ (appendIso Z Y).hom =
      (appendIso Y Z).hom ≫ (β_ (obj Y) (obj Z)).hom)
    (hXZ : (blockFlipIso X Z).hom ≫ (appendIso Z X).hom =
      (appendIso X Z).hom ≫ (β_ (obj X) (obj Z)).hom) :
    (blockFlipIso (Fin.append X Y) Z).hom ≫ (appendIso Z (Fin.append X Y)).hom =
      (appendIso (Fin.append X Y) Z).hom ≫ (β_ (obj (Fin.append X Y)) (obj Z)).hom := by
  have hYZiso := iso_split_conjugacy (appendIso Y Z) (appendIso Z Y)
    (blockFlipIso Y Z) (β_ (obj Y) (obj Z)) hYZ
  have hXZiso := iso_split_conjugacy (appendIso X Z) (appendIso Z X)
    (blockFlipIso X Z) (β_ (obj X) (obj Z)) hXZ
  let B := sumNamedIso (Equiv.refl (Fin m)) (finAddFlip : Fin (1 + 1) ≃ Fin (1 + 1))
    X (Fin.append Y Z) X (Fin.append Z Y) (fun _ => rfl) (blockFlip_objects Y Z)
  let D := sumNamedIso (finAddFlip : Fin (m + 1) ≃ Fin (1 + m)) (Equiv.refl (Fin 1))
    (Fin.append X Z) Y (Fin.append Z X) Y (blockFlip_objects X Z) (fun _ => rfl)
  have hB : B ≪≫ appendIso X (Fin.append Z Y) =
      appendIso X (Fin.append Y Z) ≪≫ tensorIso (Iso.refl (obj X))
        (appendIso Y Z ≪≫ β_ (obj Y) (obj Z) ≪≫ (appendIso Z Y).symm) := by
    have h := sumNamedIso_append (Equiv.refl (Fin m))
      (finAddFlip : Fin (1 + 1) ≃ Fin (1 + 1)) X (Fin.append Y Z) X (Fin.append Z Y)
      (fun _ => rfl) (blockFlip_objects Y Z)
    simp only [eqToIso_refl] at h
    rw [isoEquiv_refl_id] at h
    change B ≪≫ appendIso X (Fin.append Z Y) =
      appendIso X (Fin.append Y Z) ≪≫ tensorIso (Iso.refl (obj X)) (blockFlipIso Y Z) at h
    rw [hYZiso] at h
    exact h
  have hD : D ≪≫ appendIso (Fin.append Z X) Y =
      appendIso (Fin.append X Z) Y ≪≫ tensorIso
        (appendIso X Z ≪≫ β_ (obj X) (obj Z) ≪≫ (appendIso Z X).symm)
        (Iso.refl (obj Y)) := by
    have h := sumNamedIso_append
      (finAddFlip : Fin (m + 1) ≃ Fin (1 + m)) (Equiv.refl (Fin 1))
      (Fin.append X Z) Y (Fin.append Z X) Y
      (blockFlip_objects X Z) (fun _ => rfl)
    simp only [eqToIso_refl] at h
    rw [isoEquiv_refl_id] at h
    change D ≪≫ appendIso (Fin.append Z X) Y =
      appendIso (Fin.append X Z) Y ≪≫ tensorIso (blockFlipIso X Z) (Iso.refl (obj Y)) at h
    rw [hXZiso] at h
    exact h
  have h := appendBlock_left_hexagon X Y Z B D hB hD
  have hIso : blockFlipIso (Fin.append X Y) Z ≪≫ appendIso Z (Fin.append X Y) =
      appendIso (Fin.append X Y) Z ≪≫ β_ (obj (Fin.append X Y)) (obj Z) := by
    rw [blockFlipIso_left_singleton_factor]
    dsimp only [blockFlipLeftSingletonRoute, B, D] at h ⊢
    simpa only [Iso.trans_assoc] using h
  exact congrArg Iso.hom hIso

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_BlockBraidingSteps

/- Source proof segment: AdjacentInputIso -/
section source_AdjacentInputIso
/-!
# Original adjacent tensor maps at their original named target families

The inverse-reindexing convention is connected to the original
finite adjacent tensor map before selecting the degree-two block
flip. All actual equality transports are retained.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section Braided

variable [BraidedCategory C]

/-- The actual adjacent record retains the original forward swapped family. -/
theorem tensorGenerator_family {n : ℕ} (i : Fin n) (X : Fin (n + 1) → C) :
    familyEquiv (tensorGenerator (C := C) i).perm X = X ∘ Equiv.swap i.castSucc i.succ := by
  change X ∘ (Equiv.swap i.castSucc i.succ).symm = _
  rw [show (Equiv.swap i.castSucc i.succ).symm = Equiv.swap i.castSucc i.succ from
    Equiv.swap_inv _ _]

set_option backward.isDefEq.respectTransparency false in
/-- The original named-target adjacent comparison has its original adjacent map and transport. -/
theorem comparisonAlong_generator {n : ℕ} (i : Fin n) (X Y : Fin (n + 1) → C)
    (h : X ∘ Equiv.swap i.castSucc i.succ = Y) :
    (comparisonAlong (tensorGenerator i) X Y ((tensorGenerator_family i X).trans h)).hom =
      (adjacentIso X i).hom ≫ eqToHom (congrArg obj h) := by
  rw [comparisonAlong_hom]
  have ht : HEq
      (eqToHom (congrArg obj ((tensorGenerator_family i X).trans h)))
      (eqToHom (congrArg obj h)) :=
    (eqToHom_heq_id_cod _ _ _).trans (eqToHom_heq_id_cod _ _ _).symm
  exact eq_of_heq (heq_comp rfl (congrArg obj (tensorGenerator_family i X)) rfl
    (tensorGenerator_hom_app i X) ht)

end Braided

section Symmetric

variable [SymmetricCategory C]

/-- The actual rebased permutation record at an adjacent input is its original generator. -/
theorem firstPermutationRecord_adjacent {n : ℕ} (i : Fin n) :
    firstPermutationRecord (C := C) (Equiv.swap i.castSucc i.succ) = tensorGenerator i := by
  unfold firstPermutationRecord
  exact (rebaseRecord_eq _ _ (permutationHom_perm (n + 1)
    (Equiv.swap i.castSucc i.succ))).trans (permutationHom_adjacent i)

end Symmetric

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_AdjacentInputIso

/- Source proof segment: SingletonUnitBraiding -/
section source_SingletonUnitBraiding
/-!
# Original binary braiding after retaining both singleton units

The supplied braiding and associators commute with collapsing the
original unit factor in each of two different singleton tensors.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The original unit-prefix adjacent map collapses to the original binary braiding. -/
theorem swapLastIso_unit_collapse (A B : C) :
    (swapLastIso (𝟙_ C) A B).hom ≫ ((λ_ B).hom ⊗ₘ 𝟙 A) =
      ((λ_ A).hom ⊗ₘ 𝟙 B) ≫ (β_ A B).hom := by
  simp only [swapLastIso, Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom,
    Category.assoc]
  rw [← leftUnitor_tensor_hom' B A]
  rw [leftUnitor_naturality]
  rw [← Category.assoc]
  exact congrArg (fun k => k ≫ (β_ A B).hom) (leftUnitor_tensor_hom'' A B)

/-- Collapsing the right singleton unit identifies the original adjacent map
with the ambient braiding on the two actual singleton tensor carriers. -/
theorem singletonUnit_braiding (A B : C) :
    (𝟙 (𝟙_ C ⊗ A) ⊗ₘ (λ_ B).hom) ≫ (swapLastIso (𝟙_ C) A B).hom =
      (β_ (𝟙_ C ⊗ A) (𝟙_ C ⊗ B)).hom ≫
        (𝟙 (𝟙_ C ⊗ B) ⊗ₘ (λ_ A).hom) := by
  have hab : (𝟙 (𝟙_ C ⊗ A) ⊗ₘ (λ_ B).hom) ≫
      ((λ_ A).hom ⊗ₘ 𝟙 B) = (λ_ A).hom ⊗ₘ (λ_ B).hom := by
    rw [tensorHom_comp_tensorHom]
    simp only [Category.id_comp, Category.comp_id]
  have hba : (𝟙 (𝟙_ C ⊗ B) ⊗ₘ (λ_ A).hom) ≫
      ((λ_ B).hom ⊗ₘ 𝟙 A) = (λ_ B).hom ⊗ₘ (λ_ A).hom := by
    rw [tensorHom_comp_tensorHom]
    simp only [Category.id_comp, Category.comp_id]
  apply (cancel_mono ((λ_ B).hom ⊗ₘ 𝟙 A)).1
  calc
    ((𝟙 (𝟙_ C ⊗ A) ⊗ₘ (λ_ B).hom) ≫
        (swapLastIso (𝟙_ C) A B).hom) ≫ ((λ_ B).hom ⊗ₘ 𝟙 A) =
        (𝟙 (𝟙_ C ⊗ A) ⊗ₘ (λ_ B).hom) ≫
          (((λ_ A).hom ⊗ₘ 𝟙 B) ≫ (β_ A B).hom) := by
      rw [Category.assoc, swapLastIso_unit_collapse]
    _ = ((λ_ A).hom ⊗ₘ (λ_ B).hom) ≫ (β_ A B).hom := by
      rw [← Category.assoc, hab]
    _ = (β_ (𝟙_ C ⊗ A) (𝟙_ C ⊗ B)).hom ≫
        ((λ_ B).hom ⊗ₘ (λ_ A).hom) :=
      BraidedCategory.braiding_naturality (λ_ A).hom (λ_ B).hom
    _ = ((β_ (𝟙_ C ⊗ A) (𝟙_ C ⊗ B)).hom ≫
        (𝟙 (𝟙_ C ⊗ B) ⊗ₘ (λ_ A).hom)) ≫
          ((λ_ B).hom ⊗ₘ 𝟙 A) := by
      rw [Category.assoc, hba]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_SingletonUnitBraiding

/- Source proof segment: SingletonSwapShapes -/
section source_SingletonSwapShapes
/-!
# Exact original degree-two singleton block carriers

The input swap exchanges the actual two singleton slots. All carrier
equalities below refer to the original heterogeneous ordered families.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The actual degree-two transposition of the two singleton slots. -/
def singletonBlockSwap : Equiv.Perm (Fin (1 + 1)) :=
  Equiv.swap ((0 : Fin 1).castSucc) ((0 : Fin 1).succ)

omit [Category.{v} C] [MonoidalCategory C] in
/-- Swapping the original two singleton slots gives the actual opposite append family. -/
theorem singletonBlockSwap_family (X Y : Fin 1 → C) :
    Fin.append X Y ∘ singletonBlockSwap = Fin.append Y X := by
  funext i
  fin_cases i <;> rfl

/-- The original degree-two ordered carrier retains the unit preceding its first object. -/
theorem obj_singleton_append (X Y : Fin 1 → C) :
    obj (Fin.append X Y) = (𝟙_ C ⊗ X 0) ⊗ Y 0 := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The original append split of two singleton blocks has the original right-unit expansion. -/
theorem appendIso_singleton_hom (X Y : Fin 1 → C) :
    (appendIso X Y).hom =
      ((ρ_ (𝟙_ C ⊗ X 0)).inv ⊗ₘ 𝟙 (Y 0)) ≫
        (α_ (𝟙_ C ⊗ X 0) (𝟙_ C) (Y 0)).hom := by
  dsimp only [appendIso]
  simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
    Iso.symm_hom, eqToIso.hom, eqToHom_refl, Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The original inverse append split of two singleton blocks collapses the right unit. -/
theorem appendIso_singleton_inv (X Y : Fin 1 → C) :
    (appendIso X Y).inv =
      (α_ (𝟙_ C ⊗ X 0) (𝟙_ C) (Y 0)).inv ≫
        ((ρ_ (𝟙_ C ⊗ X 0)).hom ⊗ₘ 𝟙 (Y 0)) := by
  dsimp only [appendIso]
  simp only [Iso.trans_inv, tensorIso_inv, Iso.refl_inv,
    Iso.symm_inv, eqToIso.inv, eqToHom_refl, Category.comp_id]
  rfl

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_SingletonSwapShapes

/- Source proof segment: SingletonBlockBraiding -/
section source_SingletonBlockBraiding
/-!
# Original heterogeneous singleton block swap is the ambient braiding

The degree-two adjacent map, the original block split maps, and the
actual reindexed-family equality determine the original ambient braiding
on the two singleton ordered tensor carriers.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

omit [BraidedCategory C] in
/-- The original inverse append split of singleton blocks is the actual right-unit collapse. -/
theorem appendIso_singleton_inv_collapse (X Y : Fin 1 → C) :
    (appendIso X Y).inv = 𝟙 (𝟙_ C ⊗ X 0) ⊗ₘ (λ_ (Y 0)).hom := by
  rw [appendIso_singleton_inv, tensorHom_id, id_tensorHom]
  exact triangle_assoc_comp_right (𝟙_ C ⊗ X 0) (Y 0)

omit [BraidedCategory C] in
/-- The original append split of singleton blocks is the actual right-unit expansion. -/
theorem appendIso_singleton_hom_expand (X Y : Fin 1 → C) :
    (appendIso X Y).hom = 𝟙 (𝟙_ C ⊗ X 0) ⊗ₘ (λ_ (Y 0)).inv := by
  rw [appendIso_singleton_hom, tensorHom_id, id_tensorHom]
  exact triangle_assoc_comp_right_inv (𝟙_ C ⊗ X 0) (Y 0)

set_option backward.isDefEq.respectTransparency false in
/-- The original adjacent map has the original unit-prefix binary map after the actual
swapped-family equality transport. -/
theorem adjacentIso_singleton_transport (X Y : Fin 1 → C) :
    (adjacentIso (Fin.append X Y) (0 : Fin 1)).hom ≫
        eqToHom (congrArg obj (singletonBlockSwap_family X Y)) =
      (swapLastIso (𝟙_ C) (X 0) (Y 0)).hom := by
  change (adjacentIso (Fin.append X Y) (Fin.last 0)).hom ≫
    eqToHom (congrArg obj (singletonBlockSwap_family X Y)) = _
  rw [adjacentIso_last_hom]
  simp only [eqToHom_refl, Category.comp_id]
  rfl

/-- Original singleton block splitting intertwines the actual adjacent map
and ambient braiding. -/
theorem singletonBlockSwap_conjugacy (X Y : Fin 1 → C) :
    (appendIso X Y).inv ≫ (adjacentIso (Fin.append X Y) (0 : Fin 1)).hom ≫
        eqToHom (congrArg obj (singletonBlockSwap_family X Y)) =
      (β_ (obj X) (obj Y)).hom ≫ (appendIso Y X).inv := by
  rw [adjacentIso_singleton_transport, appendIso_singleton_inv_collapse,
    appendIso_singleton_inv_collapse]
  exact singletonUnit_braiding (X 0) (Y 0)

/-- The original heterogeneous degree-two block swap is the original ambient braiding. -/
theorem singletonBlockSwap_braiding (X Y : Fin 1 → C) :
    (appendIso X Y).inv ≫ (adjacentIso (Fin.append X Y) (0 : Fin 1)).hom ≫
        eqToHom (congrArg obj (singletonBlockSwap_family X Y)) ≫
          (appendIso Y X).hom = (β_ (obj X) (obj Y)).hom := by
  calc
    (appendIso X Y).inv ≫ (adjacentIso (Fin.append X Y) (0 : Fin 1)).hom ≫
        eqToHom (congrArg obj (singletonBlockSwap_family X Y)) ≫
          (appendIso Y X).hom =
        ((appendIso X Y).inv ≫ (adjacentIso (Fin.append X Y) (0 : Fin 1)).hom ≫
          eqToHom (congrArg obj (singletonBlockSwap_family X Y))) ≫
            (appendIso Y X).hom := by
      simp only [Category.assoc]
    _ = ((β_ (obj X) (obj Y)).hom ≫ (appendIso Y X).inv) ≫
        (appendIso Y X).hom := by
      rw [singletonBlockSwap_conjugacy]
    _ = (β_ (obj X) (obj Y)).hom := by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_SingletonBlockBraiding

/- Source proof segment: SingletonBlockAction -/
section source_SingletonBlockAction
/-!
# The actual heterogeneous tensor action on two singleton blocks

The original constructed permutation record is identified with its
actual adjacent generator before applying the original binary
singleton block braiding proof.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The original degree-two finite block flip is its actual adjacent input permutation. -/
theorem blockFlip_singleton_equiv :
    (finAddFlip : Equiv.Perm (Fin (1 + 1))) =
      Equiv.swap ((0 : Fin 1).castSucc) ((0 : Fin 1).succ) := by
  apply Equiv.ext
  intro i
  fin_cases i <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual heterogeneous singleton block action is the original ambient braiding. -/
theorem blockFlipIso_singleton (X Y : Fin 1 → C) :
    (blockFlipIso X Y).hom ≫ (appendIso Y X).hom =
      (appendIso X Y).hom ≫ (β_ (obj X) (obj Y)).hom := by
  let p : Equiv.Perm (Fin (1 + 1)) := finAddFlip
  let i : Fin 1 := 0
  let S := Fin.append X Y
  let T := Fin.append Y X
  have hr : firstPermutationRecord (C := C) p = tensorGenerator i :=
    (congrArg (firstPermutationRecord (C := C)) blockFlip_singleton_equiv).trans
      (firstPermutationRecord_adjacent i)
  have hTarget : familyEquiv (firstPermutationRecord (C := C) p).perm S = T :=
    reindexedFamily_eq p S T (blockFlip_objects X Y)
  have hForward : S ∘ Equiv.swap i.castSucc i.succ = T := singletonBlockSwap_family X Y
  have hGenTarget := (tensorGenerator_family i S).trans hForward
  have hActual := comparisonAlong_actual p S T (blockFlip_objects X Y) hTarget
  have hAlong := comparisonAlong_congr hr S T hTarget hGenTarget
  have hMap : (blockFlipIso X Y).hom =
      (adjacentIso S i).hom ≫ eqToHom (congrArg obj hForward) :=
    (congrArg (fun f : obj S ≅ obj T => f.hom) (hActual.symm.trans hAlong)).trans
      (comparisonAlong_generator i S T hForward)
  apply (cancel_epi (appendIso X Y).inv).mp
  rw [hMap]
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using singletonBlockSwap_braiding X Y

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_SingletonBlockAction

/- Source proof segment: HeterogeneousBlockSwap -/
section source_HeterogeneousBlockSwap
/-!
# Original heterogeneous two-block tensor flip is the ambient braiding

The actual original finite input action is identified with the
original ambient braiding for all finite heterogeneous blocks,
including either empty block. Both inductions retain the original
singleton and append input transports.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- Every original heterogeneous block versus one original input has the actual ambient braiding. -/
theorem blockFlipIso_singleton_right : ∀ {m : ℕ} (X : Fin m → C) (Z : Fin 1 → C),
    (blockFlipIso X Z).hom ≫ (appendIso Z X).hom =
      (appendIso X Z).hom ≫ (β_ (obj X) (obj Z)).hom := by
  intro m
  induction m with
  | zero =>
      intro X Z
      exact blockFlipIso_empty_left X Z
  | succ m ih =>
      intro X Z
      let Y : Fin 1 → C := fun _ => X (Fin.last m)
      have hX : Fin.append (Fin.init X) Y = X := by
        rw [Fin.append_right_eq_snoc]
        exact Fin.snoc_init_self X
      have h := blockFlipIso_left_singleton_step (Fin.init X) Y Z
        (blockFlipIso_singleton Y Z) (ih (Fin.init X) Z)
      rw [hX] at h
      exact h

set_option backward.isDefEq.respectTransparency false in
/-- The actual original finite two-block input map is the original ambient tensor braiding. -/
theorem blockFlipIso_braiding : ∀ {m n : ℕ} (X : Fin m → C) (Y : Fin n → C),
    (blockFlipIso X Y).hom ≫ (appendIso Y X).hom =
      (appendIso X Y).hom ≫ (β_ (obj X) (obj Y)).hom := by
  intro m n
  induction n with
  | zero =>
      intro X Y
      exact blockFlipIso_empty_right X Y
  | succ n ih =>
      intro X Y
      let Z : Fin 1 → C := fun _ => Y (Fin.last n)
      have hY : Fin.append (Fin.init Y) Z = Y := by
        rw [Fin.append_right_eq_snoc]
        exact Fin.snoc_init_self Y
      have h := blockFlipIso_right_step X (Fin.init Y) Z
        (ih X (Fin.init Y)) (blockFlipIso_singleton_right X Z)
      rw [hY] at h
      exact h

/-- The original finite-bijection map and original append splits give exactly ambient braiding. -/
theorem mapEquiv_blockFlip_braiding {m n : ℕ} (X : Fin m → C) (Y : Fin n → C) :
    (appendIso X Y).inv ≫
        mapEquiv (finAddFlip : Fin (m + n) ≃ Fin (n + m))
          (fun i => eqToHom (blockFlip_objects X Y i)) ≫
        (appendIso Y X).hom = (β_ (obj X) (obj Y)).hom := by
  rw [← blockFlipIso_hom]
  rw [blockFlipIso_braiding]
  simp only [Iso.inv_hom_id_assoc]

/-- The original two-block finite input isomorphism has the complete original braiding conjugacy. -/
theorem blockFlipIso_braiding_iso {m n : ℕ} (X : Fin m → C) (Y : Fin n → C) :
    (appendIso X Y).symm ≪≫ blockFlipIso X Y ≪≫ appendIso Y X = β_ (obj X) (obj Y) := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [blockFlipIso_hom]
  exact mapEquiv_blockFlip_braiding X Y

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_HeterogeneousBlockSwap

/- Source proof segment: BlockLastSwapCoherence -/
section source_BlockLastSwapCoherence
/-!
# Original whole-block adjacent tensor interchange

The original finite input bijection interchanges the two final blocks
through the actual append-count transports. Original block flattening
turns this map into the original binary adjacent tensor interchange.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The actual original two-final-block input interchange with its three-block count transports. -/
noncomputable def blockLastSwapIso {p a d : ℕ} (P : Fin p → C) (A : Fin a → C) (D : Fin d → C) :
    obj (Fin.append (Fin.append P A) D) ≅ obj (Fin.append (Fin.append P D) A) :=
  appendAssociator P A D ≪≫
    sumNamedIso (Equiv.refl (Fin p)) (finAddFlip : Fin (a + d) ≃ Fin (d + a))
      P (Fin.append A D) P (Fin.append D A) (fun _ => rfl) (blockFlip_objects A D) ≪≫
      (appendAssociator P D A).symm

set_option backward.isDefEq.respectTransparency false in
/-- The original unchanged-prefix/two-block flip intertwines the original outer append split. -/
theorem blockLastSwap_sum_split {p a d : ℕ} (P : Fin p → C) (A : Fin a → C) (D : Fin d → C) :
    (sumNamedIso (Equiv.refl (Fin p)) (finAddFlip : Fin (a + d) ≃ Fin (d + a))
      P (Fin.append A D) P (Fin.append D A) (fun _ => rfl) (blockFlip_objects A D)).hom ≫
      (appendIso P (Fin.append D A)).hom =
    (appendIso P (Fin.append A D)).hom ≫ (𝟙 (obj P) ⊗ₘ (blockFlipIso A D).hom) := by
  have h := sumNamedIso_append_hom (Equiv.refl (Fin p))
    (finAddFlip : Fin (a + d) ≃ Fin (d + a)) P (Fin.append A D) P (Fin.append D A)
    (fun _ => rfl) (blockFlip_objects A D)
  have hi : isoEquiv (Equiv.refl (Fin p)) (fun i => eqToIso (show P i = P i from rfl)) =
      Iso.refl (obj P) := isoEquiv_refl_id P
  rw [hi, Iso.refl_hom] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The actual two-final-block input map is the original braiding after the original
three-block split. -/
theorem blockLastSwap_threeSplit {p a d : ℕ} (P : Fin p → C) (A : Fin a → C) (D : Fin d → C) :
    (blockLastSwapIso P A D).hom ≫ appendAssocRight P D A =
      appendAssocRight P A D ≫ (𝟙 (obj P) ⊗ₘ (β_ (obj A) (obj D)).hom) := by
  rw [← appendSplit_associativity P D A, ← appendSplit_associativity P A D]
  unfold blockLastSwapIso appendAssocLeft
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  slice_lhs 2 3 => rw [blockLastSwap_sum_split P A D]
  have hl := tensorHom_comp_tensorHom (𝟙 (obj P)) (blockFlipIso A D).hom
    (𝟙 (obj P)) (appendIso D A).hom
  have hr := tensorHom_comp_tensorHom (𝟙 (obj P)) (appendIso A D).hom
    (𝟙 (obj P)) (β_ (obj A) (obj D)).hom
  simp only [Category.id_comp] at hl hr
  have hJoin := hl.trans
    ((congrArg (𝟙 (obj P) ⊗ₘ ·) (blockFlipIso_braiding A D)).trans hr.symm)
  slice_lhs 3 4 => rw [hJoin]

omit [SymmetricCategory C] in
/-- Original prefix and final-pair maps interchange by the original tensor map composition law. -/
theorem prefixMap_interchange {P T A D : C} (f : P ⟶ T) (b : A ⟶ D) :
    (𝟙 P ⊗ₘ b) ≫ (f ⊗ₘ 𝟙 D) = (f ⊗ₘ 𝟙 A) ≫ (𝟙 T ⊗ₘ b) := by
  have hl := tensorHom_comp_tensorHom (𝟙 P) b f (𝟙 D)
  have hr := tensorHom_comp_tensorHom f (𝟙 A) (𝟙 T) b
  simp only [Category.id_comp, Category.comp_id] at hl hr
  exact hl.trans hr.symm

set_option backward.isDefEq.respectTransparency false in
/-- Original block reflection turns the actual final-block input interchange into the
original binary tensor
  interchange. -/
theorem blockLastSwap_pairSplit (B : Blocks C) {a d : ℕ} (A : Fin a → C) (D : Fin d → C) :
    (blockLastSwapIso B.inputs A D).hom ≫ blockPairSplit B D A =
      blockPairSplit B A D ≫ (swapLastIso (obj B.blockTensors) (obj A) (obj D)).hom := by
  apply (cancel_mono (α_ (obj B.blockTensors) (obj D) (obj A)).hom).mp
  simp only [Category.assoc]
  rw [blockPairSplit_assoc]
  simp only [swapLastIso, Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom,
    Category.assoc]
  rw [← Category.assoc (blockLastSwapIso B.inputs A D).hom, blockLastSwap_threeSplit]
  simp only [Category.assoc]
  rw [prefixMap_interchange]
  rw [← Category.assoc (blockPairSplit B A D), blockPairSplit_assoc]
  rw [id_tensorHom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The actual original whole final-block swap commutes with full original block flattening. -/
theorem blockLastSwap_flatten (B : Blocks C) {a d : ℕ} (A : Fin a → C) (D : Fin d → C) :
    (blockLastSwapIso B.inputs A D).hom ≫
        (Blocks.flattenIso (Blocks.snoc (Blocks.snoc B D) A)).hom ≫
        eqToHom (blockPair_obj_eq B D A) =
      (Blocks.flattenIso (Blocks.snoc (Blocks.snoc B A) D)).hom ≫
        eqToHom (blockPair_obj_eq B A D) ≫
        (swapLastIso (obj B.blockTensors) (obj A) (obj D)).hom := by
  rw [blockPairSplit_eq]
  rw [blockLastSwap_pairSplit]
  rw [← blockPairSplit_eq]
  simp only [Category.assoc]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_BlockLastSwapCoherence

/- Source proof segment: BlockLastSwapInputs -/
section source_BlockLastSwapInputs
/-!
# Actual original finite inputs of the final-block interchange

The complete input bijection and every original object equality are
read back from the three actual append/flip input maps. Empty blocks
retain their original finite count transports.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The original final-block input bijection with its actual append-count transports. -/
def blockLastInputEquiv (p a d : ℕ) : Fin (p + a + d) ≃ Fin (p + d + a) :=
  (finCongr (Nat.add_assoc p a d)).trans
    ((sumInputsEquiv (Equiv.refl (Fin p)) (finAddFlip : Fin (a + d) ≃ Fin (d + a))).trans
      (finCongr (Nat.add_assoc p d a).symm))

omit [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] in
/-- The original inverse append-count transport retains each original three-block input. -/
theorem appendAssociator_reverse_objects {p a d : ℕ}
    (P : Fin p → C) (A : Fin a → C) (D : Fin d → C) (i : Fin (p + (a + d))) :
    Fin.append P (Fin.append A D) i =
      Fin.append (Fin.append P A) D (Fin.cast (Nat.add_assoc p a d).symm i) := by
  have h := congrFun (Fin.append_assoc P A D) (Fin.cast (Nat.add_assoc p a d).symm i)
  dsimp only [Function.comp_apply] at h
  have hc : Fin.cast (Nat.add_assoc p a d) (Fin.cast (Nat.add_assoc p a d).symm i) = i :=
    Fin.ext rfl
  rw [hc] at h
  exact h.symm

omit [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] in
/-- Every actual original input occupies its original final-block-interchanged target object. -/
theorem blockLastInput_objects {p a d : ℕ} (P : Fin p → C) (A : Fin a → C) (D : Fin d → C)
    (i : Fin (p + a + d)) :
    Fin.append (Fin.append P A) D i =
      Fin.append (Fin.append P D) A (blockLastInputEquiv p a d i) :=
  (congrFun (Fin.append_assoc P A D) i).trans
    ((sumInputs_objects (Equiv.refl (Fin p)) (finAddFlip : Fin (a + d) ≃ Fin (d + a))
      P (Fin.append A D) P (Fin.append D A) (fun _ => rfl) (blockFlip_objects A D)
      (Fin.cast (Nat.add_assoc p a d) i)).trans
        (appendAssociator_reverse_objects P D A _))

/-- The original append-count equality is its actual whole finite-bijection tensor isomorphism. -/
theorem appendAssociator_isoEquiv {p a d : ℕ} (P : Fin p → C) (A : Fin a → C) (D : Fin d → C) :
    appendAssociator P A D =
      isoEquiv (finCongr (Nat.add_assoc p a d)) (fun i => eqToIso (congrFun
        (Fin.append_assoc P A D) i)) :=
  (isoEquiv_finCongr (Nat.add_assoc p a d) _ _ (congrFun (Fin.append_assoc P A D))).symm

set_option backward.isDefEq.respectTransparency false in
/-- The original inverse append-count equality is its actual inverse whole finite input map. -/
theorem appendAssociator_inv_isoEquiv {p a d : ℕ} (P : Fin p → C) (A : Fin a → C) (D : Fin d → C) :
    (appendAssociator P A D).symm =
      isoEquiv (finCongr (Nat.add_assoc p a d).symm)
        (fun i => eqToIso (appendAssociator_reverse_objects P A D i)) := by
  rw [isoEquiv_finCongr]
  apply Iso.ext
  simp only [appendAssociator, congrIso, Iso.symm_hom, eqToIso.hom, eqToIso.inv]

set_option backward.isDefEq.respectTransparency false in
/-- The actual final-block interchange retains its complete original finite input bijection
and original component
  isomorphisms. -/
theorem blockLastSwapIso_input {p a d : ℕ} (P : Fin p → C) (A : Fin a → C) (D : Fin d → C) :
    blockLastSwapIso P A D =
      isoEquiv (blockLastInputEquiv p a d) (fun i => eqToIso (blockLastInput_objects P A D i)) := by
  unfold blockLastSwapIso
  rw [appendAssociator_isoEquiv, appendAssociator_inv_isoEquiv]
  unfold sumNamedIso
  rw [isoEquiv_trans, isoEquiv_trans]
  apply isoEquiv_congr rfl
  intro i
  apply heq_of_eq
  apply Iso.ext
  simp only [Iso.trans_hom, eqToIso.hom, eqToHom_trans]

/-- The actual original final-block interchange is the original finite-bijection tensor map. -/
theorem blockLastSwapIso_hom {p a d : ℕ} (P : Fin p → C) (A : Fin a → C) (D : Fin d → C) :
    (blockLastSwapIso P A D).hom =
      mapEquiv (blockLastInputEquiv p a d) (fun i => eqToHom (blockLastInput_objects P A D i)) := by
  rw [blockLastSwapIso_input]
  exact isoEquiv_hom _ _

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_BlockLastSwapInputs

/- Source proof segment: ActualTensorAdjacentReadback -/
section source_ActualTensorAdjacentReadback
/-!
# Actual adjacent input readbacks of the produced tensor permutation action

The actual finite permutation comparison is joined to its original
binary adjacent generator before projecting its component map. The
original finite tensor functor transports original family equalities.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The actual adjacent permutation natural comparison is its complete original binary
adjacent tensor generator. -/
theorem permutationNatIso_adjacent {n : ℕ} (i : Fin n) :
    permutationNatIso (C := C) (Equiv.swap i.castSucc i.succ) = (tensorGenerator (C :=
      C) i).comparison := by
  change rebase (permutationHom (C := C) (n + 1) (Equiv.swap i.castSucc i.succ))
    (Equiv.swap i.castSucc i.succ) (permutationHom_perm (n + 1) (Equiv.swap i.castSucc i.succ)) = _
  exact (rebase_congr (permutationHom_adjacent (C := C) i) (Equiv.swap i.castSucc i.succ)
    (permutationHom_perm (n + 1) (Equiv.swap i.castSucc i.succ)) rfl).trans
      (rebase_refl (tensorGenerator (C := C) i))

set_option backward.isDefEq.respectTransparency false in
/-- The actual adjacent finite permutation map retains exactly its original heterogeneous
binary tensor map. -/
theorem permutationIso_adjacent_heq {n : ℕ} (i : Fin n) (X : Fin (n + 1) → C) :
    HEq (permutationIso (Equiv.swap i.castSucc i.succ) X).hom (adjacentIso X i).hom := by
  change HEq ((permutationNatIso (C := C) (Equiv.swap i.castSucc i.succ)).hom.app X) _
  rw [permutationNatIso_adjacent]
  exact tensorGenerator_hom_app i X

/-- The actual finite tensor functor maps an original family equality to its original
tensor-carrier equality map. -/
theorem finiteMap_eqToHom {X Y : FiniteFamily C} (h : X = Y) :
    finiteMap (eqToHom h) = eqToHom (congrArg finiteObj h) :=
  eqToHom_map (finiteTensorFunctor (C := C)) h

set_option backward.isDefEq.respectTransparency false in
/-- The actual outer tensor map of original inner equality maps retains every original
tensor-carrier equality. -/
theorem orderedOutput_reindex {m n : ℕ} (e : Fin m ≃ Fin n)
    (X : Fin m → FiniteFamily C) (Y : Fin n → FiniteFamily C) (h : ∀ i, X i = Y (e i)) :
    orderedOutputMap (orderedReindexHom e X Y h) =
      mapEquiv e (X := fun i => finiteObj (X i)) (Y := fun i => finiteObj (Y i))
        (fun i => eqToHom (congrArg finiteObj (h i))) := by
  unfold orderedOutputMap orderedReindexHom
  apply mapEquiv_congr rfl
  intro i
  exact heq_of_eq (finiteMap_eqToHom (h i))

set_option backward.isDefEq.respectTransparency false in
/-- Original adjacent whole-block reindexing maps induce the original adjacent tensor map on
the actual block tensor
  carriers. -/
theorem orderedOutput_reindex_adjacent_heq {n : ℕ} (i : Fin n)
    (X Y : Fin (n + 1) → FiniteFamily C)
    (h : ∀ j, X j = Y (Equiv.swap i.castSucc i.succ j)) :
    HEq (orderedOutputMap (orderedReindexHom (Equiv.swap i.castSucc i.succ) X Y h))
      (adjacentIso (fun j => finiteObj (X j)) i).hom := by
  let e := Equiv.swap i.castSucc i.succ
  let Z : Fin (n + 1) → C := fun j => finiteObj (X j)
  let Z' : Fin (n + 1) → C := fun j => finiteObj (Y j)
  have hObj : ∀ j, Z j = Z' (e j) := fun j => congrArg finiteObj (h j)
  have hFamily : Z ∘ e.symm = Z' := reindexedFamily_eq e Z Z' hObj
  have hIso := isoEquiv_eqToIso_hom e Z Z' hObj hFamily
  rw [isoEquiv_hom] at hIso
  have hOut := orderedOutput_reindex e X Y h
  exact (heq_of_eq (hOut.trans hIso)).trans
    ((comp_eqToHom_heq _ _).trans (permutationIso_adjacent_heq i Z))

set_option backward.isDefEq.respectTransparency false in
/-- The actual last whole-block reindexing map is the original prefix-adjusted binary
braiding of both actual block
  carriers. -/
theorem orderedOutput_reindex_last_heq {n : ℕ} (X Y : Fin (n + 2) → FiniteFamily C)
    (h : ∀ j, X j = Y (Equiv.swap (Fin.last n).castSucc (Fin.last n).succ j)) :
    HEq (orderedOutputMap (orderedReindexHom
      (Equiv.swap (Fin.last n).castSucc (Fin.last n).succ) X Y h))
      (swapLastIso (obj (fun j : Fin n => finiteObj (X j.castSucc.castSucc)))
        (finiteObj (X (Fin.last n).castSucc)) (finiteObj (X (Fin.last (n + 1))))).hom :=
  (orderedOutput_reindex_adjacent_heq (Fin.last n) X Y h).trans
    (lastMap_heq (fun j => finiteObj (X j)))

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ActualTensorAdjacentReadback

/- Source proof segment: ActualTensorPrefixReadback -/
section source_ActualTensorPrefixReadback
/-!
# Original finite tensor output maps retaining the last block

The actual permutation action preserves a final original tensor
factor. The corresponding original finite-family reindexing output
maps retain their actual tensor maps and original object transports.
-/

@[expose] public section

set_option autoImplicit false

universe v u w

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [SymmetricCategory C] in
private theorem recordComponent_heq {n : ℕ} (r s : TensorReindexing C n) (h : r = s)
    (X : Fin n → C) : HEq (r.comparison.hom.app X) (s.comparison.hom.app X) := by
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual arbitrary tensor permutation retains the original final object and original
prefix permutation map. -/
theorem permutationIso_extend_heq {n : ℕ} (p : Equiv.Perm (Fin n)) (X : Fin (n + 1) → C) :
    HEq (permutationIso (extendPerm n p) X).hom
      ((permutationIso p (Fin.init X)).hom ⊗ₘ 𝟙 (X (Fin.last n))) := by
  have hBase : firstPermutationRecord (C := C) p = permutationHom n p :=
    rebaseRecord_eq _ _ (permutationHom_perm n p)
  have hUpper : firstPermutationRecord (C := C) (extendPerm n p) =
      permutationHom (n + 1) (extendPerm n p) :=
    rebaseRecord_eq _ _ (permutationHom_perm (n + 1) (extendPerm n p))
  have hAction := congrArg (fun f => f p) (permutationHom_extend (C := C) n)
  change permutationHom (C := C) (n + 1) (extendPerm n p) = extend (permutationHom n p) at hAction
  have hRecord : firstPermutationRecord (C := C) (extendPerm n p) =
    extend (firstPermutationRecord p) :=
    hUpper.trans (hAction.trans (congrArg extend hBase).symm)
  have hComponent := recordComponent_heq _ _ hRecord X
  have hTensor := tensorMapBoundary_heq
    (D := X (Fin.last n)) (E := X (Fin.last n)) (D' := X (Fin.last n)) (E' := X (Fin.last n))
    rfl rfl rfl rfl (heq_of_eq (firstPermutationRecord_hom_app p (Fin.init X)))
      (HEq.rfl (a := 𝟙 (X (Fin.last n))))
  exact (heq_of_eq (firstPermutationRecord_hom_app (extendPerm n p) X).symm).trans
    (hComponent.trans ((extend_hom_app_heq (firstPermutationRecord p) X).trans hTensor))

set_option backward.isDefEq.respectTransparency false in
/-- The original outer tensor equality reindexing map retains the actual constructed finite
permutation comparison. -/
theorem orderedOutput_reindex_permutation_heq {n : ℕ} (p : Equiv.Perm (Fin n))
    (X Y : Fin n → FiniteFamily C) (h : ∀ i, X i = Y (p i)) :
    HEq (orderedOutputMap (orderedReindexHom p X Y h))
      (permutationIso p (fun i => finiteObj (X i))).hom := by
  let Z : Fin n → C := fun i => finiteObj (X i)
  let Z' : Fin n → C := fun i => finiteObj (Y i)
  have hObj : ∀ i, Z i = Z' (p i) := fun i => congrArg finiteObj (h i)
  have hFamily : Z ∘ p.symm = Z' := reindexedFamily_eq p Z Z' hObj
  have hIso := isoEquiv_eqToIso_hom p Z Z' hObj hFamily
  rw [isoEquiv_hom] at hIso
  exact (heq_of_eq ((orderedOutput_reindex p X Y h).trans hIso)).trans (comp_eqToHom_heq _ _)

omit [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] in
/-- An original fixed-final input extension retains all original prefix objects and the
original final object. -/
theorem snoc_reindex_objects {α : Type w} {n : ℕ} (p : Equiv.Perm (Fin n))
    (X Y : Fin n → α) (D : α) (h : ∀ i, X i = Y (p i)) :
    ∀ i : Fin (n + 1),
      Fin.snoc (α := fun _ : Fin (n + 1) => α) X D i =
        Fin.snoc (α := fun _ : Fin (n + 1) => α) Y D (extendPerm n p i) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [extendPerm_last, Fin.snoc_last, Fin.snoc_last]
  · rw [extendPerm_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
    exact h j

set_option backward.isDefEq.respectTransparency false in
/-- The actual original outer output map under a retained final block tensors its original
prefix output map with the
  final identity. -/
theorem orderedOutput_reindex_snoc_heq {n : ℕ} (p : Equiv.Perm (Fin n))
    (X Y : Fin n → FiniteFamily C) (D : FiniteFamily C) (h : ∀ i, X i = Y (p i)) :
    HEq (orderedOutputMap (orderedReindexHom (extendPerm n p) (Fin.snoc X D) (Fin.snoc Y D)
      (snoc_reindex_objects p X Y D h)))
      (orderedOutputMap (orderedReindexHom p X Y h) ⊗ₘ 𝟙 (finiteObj D)) := by
  let Z : Fin n → C := fun i => finiteObj (X i)
  let Z' : Fin n → C := fun i => finiteObj (Y i)
  let S : Fin (n + 1) → C := fun i =>
    finiteObj (Fin.snoc (α := fun _ : Fin (n + 1) => FiniteFamily C) X D i)
  have hInit : Fin.init S = Z := by
    funext i
    exact congrArg finiteObj (Fin.snoc_castSucc (α := fun _ : Fin (n + 1) => FiniteFamily C) D X i)
  have hLast : S (Fin.last n) = finiteObj D :=
    congrArg finiteObj (Fin.snoc_last (α := fun _ : Fin (n + 1) => FiniteFamily C) D X)
  have hFull := orderedOutput_reindex_permutation_heq (extendPerm n p) (Fin.snoc X D) (Fin.snoc Y D)
    (snoc_reindex_objects p X Y D h)
  have hPrefix := permutationIso_extend_heq p S
  have hPrefixShape : HEq ((permutationIso p (Fin.init S)).hom ⊗ₘ 𝟙 (S (Fin.last n)))
      ((permutationIso p Z).hom ⊗ₘ 𝟙 (finiteObj D)) := by
    rw [hInit, hLast]
  have hBase := orderedOutput_reindex_permutation_heq p X Y h
  have hTarget : obj (Z ∘ p.symm) = obj Z' :=
    congrArg obj (reindexedFamily_eq p Z Z' (fun i => congrArg finiteObj (h i)))
  have hTensor := tensorMapBoundary_heq
    (D := finiteObj D) (E := finiteObj D) (D' := finiteObj D) (E' := finiteObj D)
    rfl hTarget rfl rfl hBase.symm (HEq.rfl (a := 𝟙 (finiteObj D)))
  exact hFull.trans (hPrefix.trans (hPrefixShape.trans hTensor))

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ActualTensorPrefixReadback

/- Source proof segment: OrderedGeneratorSquare -/
section source_OrderedGeneratorSquare
/-!
# Original binary diagram join for retained final blocks

The original prefix commuting square is tensorized with the actual
identity of the retained final block. Both original append splitting
isomorphisms and their inverse maps remain in the diagram.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- An actual original prefix square retains the original identity on a final tensor factor. -/
theorem tensorSquare_final {S S' T T' K : C} (f : S ⟶ S') (a : S ⟶ T) (a' : S' ⟶ T')
    (b : T ⟶ T') (h : f ≫ a' = a ≫ b) :
    (f ⊗ₘ 𝟙 K) ≫ (a' ⊗ₘ 𝟙 K) = (a ⊗ₘ 𝟙 K) ≫ (b ⊗ₘ 𝟙 K) := by
  have hl := tensorHom_comp_tensorHom f (𝟙 K) a' (𝟙 K)
  have hr := tensorHom_comp_tensorHom a (𝟙 K) b (𝟙 K)
  simp only [Category.id_comp] at hl hr
  exact hl.trans ((congrArg (· ⊗ₘ 𝟙 K) h).trans hr.symm)

/-- Original appended block splitting maps carry the actual original prefix square through a
retained final block. -/
theorem appendSquare_final {L R S S' T T' K : C} (d : L ≅ S ⊗ K) (e : R ≅ S' ⊗ K)
    (f : S ⟶ S') (a : S ⟶ T) (a' : S' ⟶ T') (b : T ⟶ T') (h : f ≫ a' = a ≫ b) :
    (d.hom ≫ (f ⊗ₘ 𝟙 K) ≫ e.inv) ≫ (e.hom ≫ (a' ⊗ₘ 𝟙 K)) =
      (d.hom ≫ (a ⊗ₘ 𝟙 K)) ≫ (b ⊗ₘ 𝟙 K) := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [tensorSquare_final f a a' b h]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedGeneratorSquare

/- Source proof segment: ReindexInputComponents -/
section source_ReindexInputComponents
/-!
# Original components of actual ordered block reindexing

The original finite-family equality component retains the identity
of each original inner input after its actual index transport. This
is proved for whole original input data before selecting an outer swap.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Original finite-family equality maps keep each original inner component identity. -/
theorem familyEquality_component_heq {X Y : FiniteFamily C} (h : X = Y) (i : X.index) :
    HEq ((eqToHom h).hom i) (𝟙 (X.obj i)) := by
  cases h
  rfl

/-- Original object equalities transport their original identity components. -/
theorem inputObject_identity_heq {X Y : C} (h : X = Y) : HEq (𝟙 X) (𝟙 Y) := by
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every actual ordered reindexing component keeps its original source input identity. -/
theorem orderedReindex_component_id {m n : ℕ} (e : Fin m ≃ Fin n)
    (X : Fin m → FiniteFamily C) (Y : Fin n → FiniteFamily C)
    (h : ∀ i, X i = Y (e i)) (j : Fin (blocksOfFamily X).totalArity) :
    HEq (orderedInputComponent (orderedReindexHom e X Y h) j)
      (𝟙 ((blocksOfFamily X).inputs j)) := by
  let p := flattenedPositionsEquiv X j
  have hf : HEq
      (((FiniteFamily.flatten (C := C)).map (orderedReindexHom e X Y h)).hom p)
      ((eqToHom (h p.1)).hom p.2) := HEq.rfl
  exact (orderedInputComponent_heq (orderedReindexHom e X Y h) j).trans
    (hf.trans ((familyEquality_component_heq (h p.1) p.2).trans
      (inputObject_identity_heq (flattenedPositions_objects X j).symm)))

/-- Original equal-object component data give exactly the actual ordered reindexing component. -/
theorem orderedReindex_component_eqToHom {m n a : ℕ} (e : Fin m ≃ Fin n)
    (X : Fin m → FiniteFamily C) (Y : Fin n → FiniteFamily C)
    (h : ∀ i, X i = Y (e i)) (j : Fin (blocksOfFamily X).totalArity)
    (Z : Fin a → C) (k : Fin (blocksOfFamily X).totalArity → Fin a)
    (hZ : (blocksOfFamily X).inputs j = Z (k j)) :
    HEq (orderedInputComponent (orderedReindexHom e X Y h) j) (eqToHom hZ) :=
  (orderedReindex_component_id e X Y h j).trans (eqToHom_heq_id_dom _ _ hZ).symm

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ReindexInputComponents

/- Source proof segment: SigmaInputTransport -/
section source_SigmaInputTransport
/-!
# Original dependent input transports of snoc finite block words

Every inner index is transported along its actual original finite
family equality. The sigma positions retain their original outer
slot independently of the objects of the tensor category.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory

variable {C : Type u}

/-- Whole original outer family equality transports every original dependent input position. -/
theorem originalPositions_cast {n : ℕ} {X Y : Fin n → FiniteFamily C} (h : X = Y)
    (p : OriginalPositions X) :
    cast (congrArg OriginalPositions h) p =
      ⟨p.1, cast (congrArg (fun F : Fin n → FiniteFamily C => ((F p.1).index : Type)) h) p.2⟩ := by
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The original retained-prefix sigma injection transports its original inner index exactly. -/
theorem snocPositions_left {n : ℕ} (X : Fin n → FiniteFamily C) (D : FiniteFamily C)
    (p : OriginalPositions X) :
    snocPositionsEquiv X D (Sum.inl p) =
      ⟨p.1.castSucc,
        cast (congrArg (fun F : FiniteFamily C => (F.index : Type))
          (Fin.snoc_castSucc (α := fun _ => FiniteFamily C) D X p.1).symm) p.2⟩ := by
  let F : Fin (n + 1) → FiniteFamily C := Fin.snoc X D
  have hc :
      cast (congrArg OriginalPositions
        (Fin.init_snoc (α := fun _ => FiniteFamily C) D X)).symm p =
        (⟨p.1, cast (congrArg (fun H : Fin n → FiniteFamily C => ((H p.1).index : Type))
          (Fin.init_snoc (α := fun _ => FiniteFamily C) D X).symm) p.2⟩ :
            OriginalPositions (Fin.init F)) :=
    originalPositions_cast (Fin.init_snoc (α := fun _ => FiniteFamily C) D X).symm p
  have hm := congrArg
    (fun q : OriginalPositions (Fin.init F) => positionsSnocEquiv F (Sum.inl q)) hc
  exact hm

set_option backward.isDefEq.respectTransparency false in
/-- The original retained-final sigma injection transports its original inner index exactly. -/
theorem snocPositions_right {n : ℕ} (X : Fin n → FiniteFamily C) (D : FiniteFamily C)
    (p : D.index) :
    snocPositionsEquiv X D (Sum.inr p) =
      ⟨Fin.last n,
        cast (congrArg (fun F : FiniteFamily C => (F.index : Type))
          (Fin.snoc_last (α := fun _ => FiniteFamily C) D X).symm) p⟩ := by
  rfl

variable [Category.{v} C]

/-- The original finite-family equality morphism transports its original input index exactly. -/
theorem familyEquality_index_cast {X Y : FiniteFamily C} (h : X = Y) (i : X.index) :
    (eqToHom h).equiv i = cast (congrArg (fun F : FiniteFamily C => (F.index : Type)) h) i := by
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Original equality reindexing retains each original input transported from its source label. -/
theorem reindexPosition_label {m n : ℕ} (e : Fin m ≃ Fin n)
    (X : Fin m → FiniteFamily C) (Y : Fin n → FiniteFamily C) (h : ∀ i, X i = Y (e i))
    (i : Fin m) (k : Fin n) (hi : e i = k) (A : FiniteFamily C)
    (hX : A = X i) (hY : A = Y k) (j : A.index) :
    ((FiniteFamily.flatten (C := C)).map (orderedReindexHom e X Y h)).equiv
        ⟨i, cast (congrArg (fun F : FiniteFamily C => (F.index : Type)) hX) j⟩ =
      ⟨k, cast (congrArg (fun F : FiniteFamily C => (F.index : Type)) hY) j⟩ := by
  subst k
  cases hX
  change (⟨e i, (eqToHom (h i)).equiv j⟩ : OriginalPositions Y) = _
  rw [familyEquality_index_cast]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_SigmaInputTransport

/- Source proof segment: LastPairPositionData -/
section source_LastPairPositionData
/-!
# Original labeled dependent positions of the final outer pair

The old prefix and both final original inner index types are retained
through the actual snoc sigma injections and equality transports.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

variable {C : Type u}

/-- The source label of an original unchanged-prefix block in the actual final-pair family. -/
theorem lastPair_prefix_label {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C)
    (i : Fin n) : P i = (Fin.snoc (Fin.snoc P A) D : Fin (n + 2) → FiniteFamily C)
      i.castSucc.castSucc :=
  (Fin.snoc_castSucc (α := fun _ => FiniteFamily C) A P i).symm.trans
    (Fin.snoc_castSucc (α := fun _ => FiniteFamily C) D (Fin.snoc P A) i.castSucc).symm

/-- The source label of the original penultimate block in the actual final-pair family. -/
theorem lastPair_middle_label {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C) :
    A = (Fin.snoc (Fin.snoc P A) D : Fin (n + 2) → FiniteFamily C) (Fin.last n).castSucc :=
  (Fin.snoc_last (α := fun _ => FiniteFamily C) A P).symm.trans
    (Fin.snoc_castSucc (α := fun _ => FiniteFamily C) D (Fin.snoc P A) (Fin.last n)).symm

/-- The source label of the original final block in the actual final-pair family. -/
theorem lastPair_last_label {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C) :
    D = (Fin.snoc (Fin.snoc P A) D : Fin (n + 2) → FiniteFamily C) (Fin.last (n + 1)) :=
  (Fin.snoc_last (α := fun _ => FiniteFamily C) D (Fin.snoc P A)).symm

/-- Retaining the original prefix twice keeps its complete original dependent input label. -/
theorem lastPair_positions_prefix {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C)
    (p : OriginalPositions P) :
    snocPositionsEquiv (Fin.snoc P A) D (Sum.inl (snocPositionsEquiv P A (Sum.inl p))) =
      ⟨p.1.castSucc.castSucc,
        cast (congrArg (fun F : FiniteFamily C => (F.index : Type))
          (lastPair_prefix_label P A D p.1)) p.2⟩ := by
  rw [snocPositions_left, snocPositions_left]
  simp only [cast_cast]
  rfl

/-- The original penultimate block keeps its complete original dependent input label. -/
theorem lastPair_positions_middle {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C)
    (p : A.index) :
    snocPositionsEquiv (Fin.snoc P A) D (Sum.inl (snocPositionsEquiv P A (Sum.inr p))) =
      ⟨(Fin.last n).castSucc,
        cast (congrArg (fun F : FiniteFamily C => (F.index : Type))
          (lastPair_middle_label P A D)) p⟩ := by
  rw [snocPositions_left, snocPositions_right]
  simp only [cast_cast]
  rfl

/-- The original final block keeps its complete original dependent input label. -/
theorem lastPair_positions_last {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C)
    (p : D.index) :
    snocPositionsEquiv (Fin.snoc P A) D (Sum.inr p) =
      ⟨Fin.last (n + 1),
        cast (congrArg (fun F : FiniteFamily C => (F.index : Type))
          (lastPair_last_label P A D)) p⟩ :=
  snocPositions_right _ _ _

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_LastPairPositionData

/- Source proof segment: LastPairWordInputs -/
section source_LastPairWordInputs
/-!
# All original input injections of a final outer block pair

The complete original prefix, penultimate and final-block inputs are
retained through both actual snoc input-count transports.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

variable {C : Type u}

/-- The original unchanged-prefix input injection through both retained final blocks. -/
noncomputable def lastPairInputPrefix {n : ℕ} (P : Fin n → FiniteFamily C)
    (A D : FiniteFamily C) (i : Fin (blocksOfFamily P).totalArity) :
    Fin (blocksOfFamily (Fin.snoc (Fin.snoc P A) D)).totalArity :=
  snocInputLeft (Fin.snoc P A) D (snocInputLeft P A i)

/-- The original penultimate-block input injection through its retained final block. -/
noncomputable def lastPairInputMiddle {n : ℕ} (P : Fin n → FiniteFamily C)
    (A D : FiniteFamily C) (i : Fin (arity A)) :
    Fin (blocksOfFamily (Fin.snoc (Fin.snoc P A) D)).totalArity :=
  snocInputLeft (Fin.snoc P A) D (snocInputRight P A i)

/-- The original last-block input injection. -/
noncomputable def lastPairInputLast {n : ℕ} (P : Fin n → FiniteFamily C)
    (A D : FiniteFamily C) (i : Fin (arity D)) :
    Fin (blocksOfFamily (Fin.snoc (Fin.snoc P A) D)).totalArity :=
  snocInputRight (Fin.snoc P A) D i

/-- The actual original unchanged-prefix input is its literal three-block prefix injection. -/
theorem lastPairInputPrefix_cast {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C)
    (i : Fin (blocksOfFamily P).totalArity) :
    Fin.cast (lastPair_count P A D) (lastPairInputPrefix P A D i) =
      Fin.castAdd (arity D) (Fin.castAdd (arity A) i) := Fin.ext rfl

/-- The actual original middle-block input is its literal three-block middle injection. -/
theorem lastPairInputMiddle_cast {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C)
    (i : Fin (arity A)) :
    Fin.cast (lastPair_count P A D) (lastPairInputMiddle P A D i) =
      Fin.castAdd (arity D) (Fin.natAdd (blocksOfFamily P).totalArity i) := Fin.ext rfl

/-- The actual original final-block input is its literal three-block final injection. -/
theorem lastPairInputLast_cast {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C)
    (i : Fin (arity D)) :
    Fin.cast (lastPair_count P A D) (lastPairInputLast P A D i) =
      Fin.natAdd ((blocksOfFamily P).totalArity + arity A) i := by
  apply Fin.ext
  change (blocksOfFamily (Fin.snoc P A)).totalArity + i.val =
    ((blocksOfFamily P).totalArity + arity A) + i.val
  rw [snocBlocks_totalArity]

/-- Every unchanged-prefix input retains its complete original dependent sigma label. -/
theorem lastPairInputPrefix_positions {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C)
    (i : Fin (blocksOfFamily P).totalArity) :
    flattenedPositionsEquiv (Fin.snoc (Fin.snoc P A) D) (lastPairInputPrefix P A D i) =
      ⟨(flattenedPositionsEquiv P i).1.castSucc.castSucc,
        cast (congrArg (fun F : FiniteFamily C => (F.index : Type))
          (lastPair_prefix_label P A D (flattenedPositionsEquiv P i).1))
            (flattenedPositionsEquiv P i).2⟩ := by
  unfold lastPairInputPrefix
  rw [flattenedPositions_snoc_left, flattenedPositions_snoc_left]
  exact lastPair_positions_prefix P A D _

/-- Every original penultimate-block input retains its complete dependent sigma label. -/
theorem lastPairInputMiddle_positions {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C)
    (i : Fin (arity A)) :
    flattenedPositionsEquiv (Fin.snoc (Fin.snoc P A) D) (lastPairInputMiddle P A D i) =
      ⟨(Fin.last n).castSucc,
        cast (congrArg (fun F : FiniteFamily C => (F.index : Type))
          (lastPair_middle_label P A D)) (enumeration A i)⟩ := by
  unfold lastPairInputMiddle
  rw [flattenedPositions_snoc_left, flattenedPositions_snoc_right]
  exact lastPair_positions_middle P A D _

/-- Every original final-block input retains its complete dependent sigma label. -/
theorem lastPairInputLast_positions {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C)
    (i : Fin (arity D)) :
    flattenedPositionsEquiv (Fin.snoc (Fin.snoc P A) D) (lastPairInputLast P A D i) =
      ⟨Fin.last (n + 1),
        cast (congrArg (fun F : FiniteFamily C => (F.index : Type))
          (lastPair_last_label P A D)) (enumeration D i)⟩ := by
  unfold lastPairInputLast
  rw [flattenedPositions_snoc_right]
  exact lastPair_positions_last P A D _

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_LastPairWordInputs

/- Source proof segment: LastPairInputIndices -/
section source_LastPairInputIndices
/-!
# Original finite input slots of the final block-pair interchange

All three original input injections are retained through the actual
append count transports and original two-block flip.
-/

@[expose] public section

set_option autoImplicit false

namespace CategoryTheory.MonoidalCategory.OrderedTensor

/-- The original prefix inputs are retained through the final-pair input map. -/
theorem blockLastInput_prefix {p a d : ℕ} (i : Fin p) :
    blockLastInputEquiv p a d (Fin.castAdd d (Fin.castAdd a i)) =
      Fin.castAdd a (Fin.castAdd d i) := by
  have h₀ : Fin.cast (Nat.add_assoc p a d) (Fin.castAdd d (Fin.castAdd a i)) =
      Fin.castAdd (a + d) i := Fin.ext rfl
  unfold blockLastInputEquiv
  simp only [Equiv.trans_apply, finCongr_apply]
  rw [h₀, sumInputsEquiv_left]
  exact Fin.ext rfl

/-- Every original penultimate-block input moves after the original final block. -/
theorem blockLastInput_middle {p a d : ℕ} (i : Fin a) :
    blockLastInputEquiv p a d (Fin.castAdd d (Fin.natAdd p i)) =
      Fin.natAdd (p + d) i := by
  have h₀ : Fin.cast (Nat.add_assoc p a d) (Fin.castAdd d (Fin.natAdd p i)) =
      Fin.natAdd p (Fin.castAdd d i) := Fin.ext (by simp only [Fin.val_cast, Fin.val_castAdd,
        Fin.val_natAdd])
  unfold blockLastInputEquiv
  simp only [Equiv.trans_apply, finCongr_apply]
  rw [h₀, sumInputsEquiv_right, finAddFlip_apply_castAdd]
  apply Fin.ext
  simp only [Fin.val_cast, Fin.val_natAdd, Nat.add_assoc]

/-- Every original last-block input moves to the original penultimate block position. -/
theorem blockLastInput_last {p a d : ℕ} (i : Fin d) :
    blockLastInputEquiv p a d (Fin.natAdd (p + a) i) =
      Fin.castAdd a (Fin.natAdd p i) := by
  have h₀ : Fin.cast (Nat.add_assoc p a d) (Fin.natAdd (p + a) i) =
      Fin.natAdd p (Fin.natAdd a i) := Fin.ext (by simp only [Fin.val_cast, Fin.val_natAdd,
        Nat.add_assoc])
  unfold blockLastInputEquiv
  simp only [Equiv.trans_apply, finCongr_apply]
  rw [h₀, sumInputsEquiv_right, finAddFlip_apply_natAdd]
  exact Fin.ext rfl

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_LastPairInputIndices

/- Source proof segment: LastPairFlatMapPositions -/
section source_LastPairFlatMapPositions
/-!
# Original sigma input action of the final outer-block swap

The actual ordered outer reindexing sends every original prefix and
final-block inner input to its actual target dependent position.
The full original inner index types and casts are retained.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The actual original ordered morphism interchanging the two final outer blocks. -/
def lastPairReindex {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C) :
    literalOuterFamily (Fin.snoc (Fin.snoc P A) D) ⟶
      literalOuterFamily (Fin.snoc (Fin.snoc P D) A) :=
  orderedReindexHom (lastOuterSwap n) (Fin.snoc (Fin.snoc P A) D)
    (Fin.snoc (Fin.snoc P D) A) (lastOuterSwap_objects P A D)

set_option backward.isDefEq.respectTransparency false in
/-- Every original prefix input is retained by the actual final-pair flattened input map. -/
theorem lastPairFlatMap_prefix {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C)
    (i : Fin (blocksOfFamily P).totalArity) :
    ((FiniteFamily.flatten (C := C)).map (lastPairReindex P A D)).equiv
        (flattenedPositionsEquiv (Fin.snoc (Fin.snoc P A) D) (lastPairInputPrefix P A D i)) =
      flattenedPositionsEquiv (Fin.snoc (Fin.snoc P D) A) (lastPairInputPrefix P D A i) := by
  rw [lastPairInputPrefix_positions, lastPairInputPrefix_positions]
  exact reindexPosition_label (lastOuterSwap n) _ _ (lastOuterSwap_objects P A D)
    _ _ (lastOuterSwap_prefix (flattenedPositionsEquiv P i).1)
    (P (flattenedPositionsEquiv P i).1)
    (lastPair_prefix_label P A D _) (lastPair_prefix_label P D A _) _

set_option backward.isDefEq.respectTransparency false in
/-- Every original penultimate-block input moves to the actual original final target block. -/
theorem lastPairFlatMap_middle {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C)
    (i : Fin (arity A)) :
    ((FiniteFamily.flatten (C := C)).map (lastPairReindex P A D)).equiv
        (flattenedPositionsEquiv (Fin.snoc (Fin.snoc P A) D) (lastPairInputMiddle P A D i)) =
      flattenedPositionsEquiv (Fin.snoc (Fin.snoc P D) A) (lastPairInputLast P D A i) := by
  rw [lastPairInputMiddle_positions, lastPairInputLast_positions]
  exact reindexPosition_label (lastOuterSwap n) _ _ (lastOuterSwap_objects P A D)
    _ _ (lastOuterSwap_penultimate n) A
    (lastPair_middle_label P A D) (lastPair_last_label P D A) _

set_option backward.isDefEq.respectTransparency false in
/-- Every original last-block input moves to the actual original penultimate target block. -/
theorem lastPairFlatMap_last {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C)
    (i : Fin (arity D)) :
    ((FiniteFamily.flatten (C := C)).map (lastPairReindex P A D)).equiv
        (flattenedPositionsEquiv (Fin.snoc (Fin.snoc P A) D) (lastPairInputLast P A D i)) =
      flattenedPositionsEquiv (Fin.snoc (Fin.snoc P D) A) (lastPairInputMiddle P D A i) := by
  rw [lastPairInputLast_positions, lastPairInputMiddle_positions]
  exact reindexPosition_label (lastOuterSwap n) _ _ (lastOuterSwap_objects P A D)
    _ _ (lastOuterSwap_last n) D
    (lastPair_last_label P A D) (lastPair_middle_label P D A) _

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_LastPairFlatMapPositions

/- Source proof segment: LastPairInputEquiv -/
section source_LastPairInputEquiv
/-!
# Actual original input equivalence of the final outer-block swap

The original ordered input equivalence is compared with the literal
three-block map through its exact source and target count transports.
Every original prefix and final-block input is retained.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory

variable {C : Type u} [Category.{v} C]

set_option backward.isDefEq.respectTransparency false in
/-- The actual last-pair ordered input map retains its original unchanged-prefix injection. -/
theorem lastPairInputEquiv_prefix {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C)
    (i : Fin (blocksOfFamily P).totalArity) :
    orderedInputEquiv (lastPairReindex P A D) (lastPairInputPrefix P A D i) =
      lastPairInputPrefix P D A i := by
  apply (flattenedPositionsEquiv (Fin.snoc (Fin.snoc P D) A)).injective
  exact (orderedInput_positions (lastPairReindex P A D) _).trans (lastPairFlatMap_prefix P A D i)

set_option backward.isDefEq.respectTransparency false in
/-- The actual last-pair ordered input map retains every original penultimate-block input. -/
theorem lastPairInputEquiv_middle {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C)
    (i : Fin (arity A)) :
    orderedInputEquiv (lastPairReindex P A D) (lastPairInputMiddle P A D i) =
      lastPairInputLast P D A i := by
  apply (flattenedPositionsEquiv (Fin.snoc (Fin.snoc P D) A)).injective
  exact (orderedInput_positions (lastPairReindex P A D) _).trans (lastPairFlatMap_middle P A D i)

set_option backward.isDefEq.respectTransparency false in
/-- The actual last-pair ordered input map retains every original final-block input. -/
theorem lastPairInputEquiv_last {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C)
    (i : Fin (arity D)) :
    orderedInputEquiv (lastPairReindex P A D) (lastPairInputLast P A D i) =
      lastPairInputMiddle P D A i := by
  apply (flattenedPositionsEquiv (Fin.snoc (Fin.snoc P D) A)).injective
  exact (orderedInput_positions (lastPairReindex P A D) _).trans (lastPairFlatMap_last P A D i)

set_option backward.isDefEq.respectTransparency false in
/-- The actual original ordered input equivalence is the full original final-block input map. -/
theorem lastPairInputEquiv_count_conjugate {n : ℕ}
    (P : Fin n → FiniteFamily C) (A D : FiniteFamily C) :
    (finCongr (lastPair_count P A D)).symm.trans
        ((orderedInputEquiv (lastPairReindex P A D)).trans
          (finCongr (lastPair_count P D A))) =
      blockLastInputEquiv (blocksOfFamily P).totalArity (arity A) (arity D) := by
  apply Equiv.ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · have hs := lastPairInputPrefix_cast P A D j
      have ht := lastPairInputPrefix_cast P D A j
      have hInject : Fin.cast (lastPair_count P A D).symm
          (Fin.castAdd (arity D) (Fin.castAdd (arity A) j)) = lastPairInputPrefix P A D j := by
        rw [← hs]
        exact Fin.ext rfl
      change Fin.cast (lastPair_count P D A)
        (orderedInputEquiv (lastPairReindex P A D) (Fin.cast (lastPair_count P A D).symm _)) = _
      rw [hInject, lastPairInputEquiv_prefix, ht, blockLastInput_prefix]
    · have hs := lastPairInputMiddle_cast P A D j
      have ht := lastPairInputLast_cast P D A j
      have hInject : Fin.cast (lastPair_count P A D).symm
          (Fin.castAdd (arity D) (Fin.natAdd (blocksOfFamily P).totalArity j)) =
            lastPairInputMiddle P A D j := by
        rw [← hs]
        exact Fin.ext rfl
      change Fin.cast (lastPair_count P D A)
        (orderedInputEquiv (lastPairReindex P A D) (Fin.cast (lastPair_count P A D).symm _)) = _
      rw [hInject, lastPairInputEquiv_middle, ht, blockLastInput_middle]
  · have hs := lastPairInputLast_cast P A D j
    have ht := lastPairInputMiddle_cast P D A j
    have hInject : Fin.cast (lastPair_count P A D).symm
        (Fin.natAdd ((blocksOfFamily P).totalArity + arity A) j) = lastPairInputLast P A D j := by
      rw [← hs]
      exact Fin.ext rfl
    change Fin.cast (lastPair_count P D A)
      (orderedInputEquiv (lastPairReindex P A D) (Fin.cast (lastPair_count P A D).symm _)) = _
    rw [hInject, lastPairInputEquiv_last, ht, blockLastInput_last]

/-- The exact count transports retain the original untransported ordered input equivalence. -/
theorem lastPairInputEquiv_heq {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C) :
    HEq (orderedInputEquiv (lastPairReindex P A D))
      (blockLastInputEquiv (blocksOfFamily P).totalArity (arity A) (arity D)) :=
  (equiv_count_transport_heq (lastPair_count P A D) (lastPair_count P D A) _).symm.trans
    (heq_of_eq (lastPairInputEquiv_count_conjugate P A D))

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_LastPairInputEquiv

/- Source proof segment: LastPairInputMap -/
section source_LastPairInputMap
/-!
# Complete original ordered input map of the final outer block swap

The actual input bijection and every original component are compared
with the original whole-block interchange. Exact source and target
word/carrier transports are retained, including every empty arity.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [MonoidalCategory C] [SymmetricCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- The actual original final-pair component is the original block-interchange equality map. -/
theorem lastPairInputComponent_heq {n : ℕ} (P : Fin n → FiniteFamily C)
    (A D : FiniteFamily C)
    (i : Fin (blocksOfFamily (Fin.snoc (Fin.snoc P A) D)).totalArity) :
    HEq (orderedInputComponent (lastPairReindex P A D) i)
      (eqToHom (blockLastInput_objects (blocksOfFamily P).inputs
        (orderedFamily A) (orderedFamily D) (Fin.cast (lastPair_count P A D) i))) :=
  (orderedReindex_component_id (lastOuterSwap n) _ _ (lastOuterSwap_objects P A D) i).trans
    ((inputObject_identity_heq (lastPair_inputs P A D i)).trans
      (eqToHom_heq_id_dom _ _ _).symm)

set_option backward.isDefEq.respectTransparency false in
/-- The full actual original final-pair word map is the original whole-block interchange. -/
theorem lastPairInputMap_heq {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C) :
    HEq (orderedInputMap (lastPairReindex P A D))
      (blockLastSwapIso (blocksOfFamily P).inputs (orderedFamily A) (orderedFamily D)).hom := by
  have h := mapEquiv_input_heq (lastPair_count P A D) (lastPair_count P D A)
    (blocksOfFamily (Fin.snoc (Fin.snoc P A) D)).inputs
    (Fin.append (Fin.append (blocksOfFamily P).inputs (orderedFamily A)) (orderedFamily D))
    (blocksOfFamily (Fin.snoc (Fin.snoc P D) A)).inputs
    (Fin.append (Fin.append (blocksOfFamily P).inputs (orderedFamily D)) (orderedFamily A))
    (lastPair_inputs P A D) (lastPair_inputs P D A)
    (orderedInputEquiv (lastPairReindex P A D))
    (blockLastInputEquiv (blocksOfFamily P).totalArity (arity A) (arity D))
    (lastPairInputEquiv_heq P A D) (orderedInputComponent (lastPairReindex P A D))
    (fun i => eqToHom (blockLastInput_objects (blocksOfFamily P).inputs
      (orderedFamily A) (orderedFamily D) i)) (lastPairInputComponent_heq P A D)
  rw [← blockLastSwapIso_hom] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Original source and target carriers turn the actual ordered word map into the block swap map. -/
theorem lastPairInputMap {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C) :
    eqToHom (lastPair_obj_eq P A D).symm ≫ orderedInputMap (lastPairReindex P A D) ≫
        eqToHom (lastPair_obj_eq P D A) =
      (blockLastSwapIso (blocksOfFamily P).inputs (orderedFamily A) (orderedFamily D)).hom :=
  ((conj_eqToHom_iff_heq' _ _ (lastPair_obj_eq P A D).symm (lastPair_obj_eq P D A)).mpr
    (lastPairInputMap_heq P A D).symm).symm

set_option backward.isDefEq.respectTransparency false in
/-- The actual ordered input map retains the original source and target block carriers. -/
theorem lastPairInputMap_original {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C) :
    orderedInputMap (lastPairReindex P A D) =
      eqToHom (lastPair_obj_eq P A D) ≫
        (blockLastSwapIso (blocksOfFamily P).inputs (orderedFamily A) (orderedFamily D)).hom ≫
          eqToHom (lastPair_obj_eq P D A).symm :=
  (conj_eqToHom_iff_heq' _ _ (lastPair_obj_eq P A D) (lastPair_obj_eq P D A).symm).mpr
    (lastPairInputMap_heq P A D)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_LastPairInputMap

/- Source proof segment: SnocPositionReadbacks -/
section source_SnocPositionReadbacks
/-!
# Original coordinates of retained-last dependent input positions

Every prefix position and last input retains its original outer slot
and full original inner input, including the actual family casts.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

variable {C : Type u}

/-- Equality of an original outer family preserves the original outer slot in its dependent sum. -/
theorem originalPositions_cast_first {n : ℕ} {F G : Fin n → FiniteFamily C}
    (h : F = G) (p : OriginalPositions F) :
    (cast (congrArg OriginalPositions h) p).1 = p.1 := by
  subst G
  rfl

/-- Equality of an original outer family preserves every original dependent inner input. -/
theorem originalPositions_cast_second_heq {n : ℕ} {F G : Fin n → FiniteFamily C}
    (h : F = G) (p : OriginalPositions F) :
    HEq (cast (congrArg OriginalPositions h) p).2 p.2 := by
  subst G
  rfl

/-- The original retained prefix position keeps its actual original outer coordinate. -/
theorem snocPositions_left_first {n : ℕ} (X : Fin n → FiniteFamily C) (D : FiniteFamily C)
    (p : OriginalPositions X) :
    (snocPositionsEquiv X D (Sum.inl p)).1 = p.1.castSucc := by
  change (cast (congrArg OriginalPositions
    (Fin.init_snoc (α := fun _ : Fin (n + 1) => FiniteFamily C) D X)).symm p).1.castSucc = _
  rw [originalPositions_cast_first
    (Fin.init_snoc (α := fun _ : Fin (n + 1) => FiniteFamily C) D X).symm p]

/-- The original retained prefix position keeps its complete original dependent inner input. -/
theorem snocPositions_left_second_heq {n : ℕ} (X : Fin n → FiniteFamily C)
    (D : FiniteFamily C) (p : OriginalPositions X) :
    HEq (snocPositionsEquiv X D (Sum.inl p)).2 p.2 := by
  change HEq (cast (congrArg OriginalPositions
    (Fin.init_snoc (α := fun _ : Fin (n + 1) => FiniteFamily C) D X)).symm p).2 _
  exact originalPositions_cast_second_heq
    (Fin.init_snoc (α := fun _ : Fin (n + 1) => FiniteFamily C) D X).symm p

/-- The original retained last input keeps the actual final outer slot. -/
theorem snocPositions_right_first {n : ℕ} (X : Fin n → FiniteFamily C) (D : FiniteFamily C)
    (p : D.index) : (snocPositionsEquiv X D (Sum.inr p)).1 = Fin.last n := rfl

/-- The original retained last input keeps its complete original inner input. -/
theorem snocPositions_right_second_heq {n : ℕ} (X : Fin n → FiniteFamily C)
    (D : FiniteFamily C) (p : D.index) :
    HEq (snocPositionsEquiv X D (Sum.inr p)).2 p := by
  exact cast_heq _ p

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_SnocPositionReadbacks

/- Source proof segment: RetainedLastReindexPositions -/
section source_RetainedLastReindexPositions
/-!
# Original reindexing of dependent positions with a retained last block

The actual finite-family flattening maps retain the original prefix
input bijection and fix every original input of the last block.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory TensorReindexing

variable {C : Type u} [Category.{v} C]

/-- The actual original outer reindexing map retaining the entire last finite family. -/
noncomputable def retainedLastHom {n : ℕ} (e : Equiv.Perm (Fin n))
    (X Y : Fin n → FiniteFamily C) (D : FiniteFamily C) (h : ∀ i, X i = Y (e i)) :
    literalOuterFamily (Fin.snoc X D) ⟶ literalOuterFamily (Fin.snoc Y D) :=
  orderedReindexHom (extendPerm n e) (Fin.snoc X D) (Fin.snoc Y D)
    (snoc_reindex_objects e X Y D h)

/-- The original finite-family equality input bijection retains its original input value. -/
theorem familyEquality_equiv_heq {X Y : FiniteFamily C} (h : X = Y) (p : X.index) :
    HEq ((eqToHom h).equiv p) p := by
  subst Y
  rfl

/-- The original flattened reindexing position map has its actual original outer coordinate. -/
theorem reindexPosition_first {m n : ℕ} (e : Fin m ≃ Fin n)
    (X : Fin m → FiniteFamily C) (Y : Fin n → FiniteFamily C)
    (h : ∀ i, X i = Y (e i)) (p : OriginalPositions X) :
    (((FiniteFamily.flatten (C := C)).map (orderedReindexHom e X Y h)).equiv p).1 =
      e p.1 := rfl

/-- The original flattened equality reindexing retains the complete original inner input. -/
theorem reindexPosition_second_heq {m n : ℕ} (e : Fin m ≃ Fin n)
    (X : Fin m → FiniteFamily C) (Y : Fin n → FiniteFamily C)
    (h : ∀ i, X i = Y (e i)) (p : OriginalPositions X) :
    HEq (((FiniteFamily.flatten (C := C)).map (orderedReindexHom e X Y h)).equiv p).2 p.2 :=
  familyEquality_equiv_heq (h p.1) p.2

/-- The actual retained-last reindexing map keeps the entire original prefix input action. -/
theorem retainedLast_positions_left {n : ℕ} (e : Equiv.Perm (Fin n))
    (X Y : Fin n → FiniteFamily C) (D : FiniteFamily C) (h : ∀ i, X i = Y (e i))
    (p : OriginalPositions X) :
    ((FiniteFamily.flatten (C := C)).map (retainedLastHom e X Y D h)).equiv
        (snocPositionsEquiv X D (Sum.inl p)) =
      snocPositionsEquiv Y D
        (Sum.inl (((FiniteFamily.flatten (C := C)).map (orderedReindexHom e X Y h)).equiv p)) := by
  apply Sigma.ext
  · change extendPerm n e (snocPositionsEquiv X D (Sum.inl p)).1 = _
    calc
      extendPerm n e (snocPositionsEquiv X D (Sum.inl p)).1 = (e p.1).castSucc :=
        (congrArg (extendPerm n e) (snocPositions_left_first X D p)).trans
          (extendPerm_castSucc e p.1)
      _ = (snocPositionsEquiv Y D
          (Sum.inl (((FiniteFamily.flatten (C := C)).map
            (orderedReindexHom e X Y h)).equiv p))).1 :=
        (congrArg Fin.castSucc (reindexPosition_first e X Y h p)).symm.trans
          (snocPositions_left_first Y D _).symm
  · exact ((reindexPosition_second_heq (extendPerm n e) (Fin.snoc X D) (Fin.snoc Y D)
      (snoc_reindex_objects e X Y D h) (snocPositionsEquiv X D (Sum.inl p))).trans
        (snocPositions_left_second_heq X D p)).trans
      ((snocPositions_left_second_heq Y D
        (((FiniteFamily.flatten (C := C)).map (orderedReindexHom e X Y h)).equiv p)).trans
          (reindexPosition_second_heq e X Y h p)).symm

/-- The actual retained-last reindexing map fixes every original input
of the retained last block. -/
theorem retainedLast_positions_right {n : ℕ} (e : Equiv.Perm (Fin n))
    (X Y : Fin n → FiniteFamily C) (D : FiniteFamily C) (h : ∀ i, X i = Y (e i))
    (p : D.index) :
    ((FiniteFamily.flatten (C := C)).map (retainedLastHom e X Y D h)).equiv
        (snocPositionsEquiv X D (Sum.inr p)) = snocPositionsEquiv Y D (Sum.inr p) := by
  apply Sigma.ext
  · change extendPerm n e (snocPositionsEquiv X D (Sum.inr p)).1 = _
    calc
      extendPerm n e (snocPositionsEquiv X D (Sum.inr p)).1 = Fin.last n :=
        (congrArg (extendPerm n e) (snocPositions_right_first X D p)).trans
          (extendPerm_last e)
      _ = (snocPositionsEquiv Y D (Sum.inr p)).1 := (snocPositions_right_first Y D p).symm
  · exact ((reindexPosition_second_heq (extendPerm n e) (Fin.snoc X D) (Fin.snoc Y D)
      (snoc_reindex_objects e X Y D h) (snocPositionsEquiv X D (Sum.inr p))).trans
        (snocPositions_right_second_heq X D p)).trans
      (snocPositions_right_second_heq Y D p).symm

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_RetainedLastReindexPositions

/- Source proof segment: RetainedLastInputEquiv -/
section source_RetainedLastInputEquiv
/-!
# Original literal input bijection retaining a last finite block

The actual input equivalence retains the prefix bijection and fixes
every original final-block input, with full original count transports.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Every original prefix input keeps its original literal reindexed target. -/
theorem retainedLast_inputEquiv_left {n : ℕ} (e : Equiv.Perm (Fin n))
    (X Y : Fin n → FiniteFamily C) (D : FiniteFamily C) (h : ∀ i, X i = Y (e i))
    (j : Fin (blocksOfFamily X).totalArity) :
    orderedInputEquiv (retainedLastHom e X Y D h) (snocInputLeft X D j) =
      snocInputLeft Y D (orderedInputEquiv (orderedReindexHom e X Y h) j) := by
  let f : OriginalPositions X ≃ OriginalPositions Y :=
    ((FiniteFamily.flatten (C := C)).map (orderedReindexHom e X Y h)).equiv
  let fext : OriginalPositions (Fin.snoc X D) ≃ OriginalPositions (Fin.snoc Y D) :=
    ((FiniteFamily.flatten (C := C)).map (retainedLastHom e X Y D h)).equiv
  apply (flattenedPositionsEquiv (Fin.snoc Y D)).injective
  calc
    flattenedPositionsEquiv (Fin.snoc Y D)
        (orderedInputEquiv (retainedLastHom e X Y D h) (snocInputLeft X D j)) =
        fext (flattenedPositionsEquiv (Fin.snoc X D) (snocInputLeft X D j)) :=
      orderedInput_positions (retainedLastHom e X Y D h) _
    _ = fext (snocPositionsEquiv X D (Sum.inl (flattenedPositionsEquiv X j))) :=
      congrArg fext (flattenedPositions_snoc_left X D j)
    _ = snocPositionsEquiv Y D
        (Sum.inl (f (flattenedPositionsEquiv X j))) :=
      retainedLast_positions_left e X Y D h _
    _ = snocPositionsEquiv Y D
        (Sum.inl (flattenedPositionsEquiv Y (orderedInputEquiv (orderedReindexHom e X Y h) j))) :=
      congrArg (fun p : OriginalPositions Y => snocPositionsEquiv Y D (Sum.inl p))
        (orderedInput_positions (orderedReindexHom e X Y h) j).symm
    _ = flattenedPositionsEquiv (Fin.snoc Y D)
        (snocInputLeft Y D (orderedInputEquiv (orderedReindexHom e X Y h) j)) :=
      (flattenedPositions_snoc_left Y D _).symm

/-- Every original input of the last retained block is fixed by the literal input bijection. -/
theorem retainedLast_inputEquiv_right {n : ℕ} (e : Equiv.Perm (Fin n))
    (X Y : Fin n → FiniteFamily C) (D : FiniteFamily C) (h : ∀ i, X i = Y (e i))
    (j : Fin (arity D)) :
    orderedInputEquiv (retainedLastHom e X Y D h) (snocInputRight X D j) =
      snocInputRight Y D j := by
  let fext : OriginalPositions (Fin.snoc X D) ≃ OriginalPositions (Fin.snoc Y D) :=
    ((FiniteFamily.flatten (C := C)).map (retainedLastHom e X Y D h)).equiv
  apply (flattenedPositionsEquiv (Fin.snoc Y D)).injective
  calc
    flattenedPositionsEquiv (Fin.snoc Y D)
        (orderedInputEquiv (retainedLastHom e X Y D h) (snocInputRight X D j)) =
        fext (flattenedPositionsEquiv (Fin.snoc X D) (snocInputRight X D j)) :=
      orderedInput_positions (retainedLastHom e X Y D h) _
    _ = fext (snocPositionsEquiv X D (Sum.inr (enumeration D j))) :=
      congrArg fext (flattenedPositions_snoc_right X D j)
    _ = snocPositionsEquiv Y D (Sum.inr (enumeration D j)) :=
      retainedLast_positions_right e X Y D h _
    _ = flattenedPositionsEquiv (Fin.snoc Y D) (snocInputRight Y D j) :=
      (flattenedPositions_snoc_right Y D j).symm

/-- The actual retained-last input equivalence with its endpoints in the original sum counts. -/
noncomputable def retainedLastSumEquiv {n : ℕ} (e : Equiv.Perm (Fin n))
    (X Y : Fin n → FiniteFamily C) (D : FiniteFamily C) (h : ∀ i, X i = Y (e i)) :
    Fin ((blocksOfFamily X).totalArity + arity D) ≃
      Fin ((blocksOfFamily Y).totalArity + arity D) :=
  (finCongr (snocBlocks_totalArity X D)).symm.trans
    ((orderedInputEquiv (retainedLastHom e X Y D h)).trans
      (finCongr (snocBlocks_totalArity Y D)))

/-- The actual retained-last input equivalence is precisely the original sum input bijection. -/
theorem retainedLast_inputEquiv_sum {n : ℕ} (e : Equiv.Perm (Fin n))
    (X Y : Fin n → FiniteFamily C) (D : FiniteFamily C) (h : ∀ i, X i = Y (e i)) :
    retainedLastSumEquiv e X Y D h =
      sumInputsEquiv (orderedInputEquiv (orderedReindexHom e X Y h))
        (Equiv.refl (Fin (arity D))) := by
  apply Equiv.ext
  intro j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · change Fin.cast (snocBlocks_totalArity Y D)
      (orderedInputEquiv (retainedLastHom e X Y D h) (snocInputLeft X D i)) = _
    rw [retainedLast_inputEquiv_left, sumInputsEquiv_left]
    apply Fin.ext
    rfl
  · change Fin.cast (snocBlocks_totalArity Y D)
      (orderedInputEquiv (retainedLastHom e X Y D h) (snocInputRight X D i)) = _
    rw [retainedLast_inputEquiv_right, sumInputsEquiv_right]
    apply Fin.ext
    rfl

/-- The original retained-last input equivalence retains the complete original sum input action. -/
theorem retainedLast_inputEquiv_heq {n : ℕ} (e : Equiv.Perm (Fin n))
    (X Y : Fin n → FiniteFamily C) (D : FiniteFamily C) (h : ∀ i, X i = Y (e i)) :
    HEq (orderedInputEquiv (retainedLastHom e X Y D h))
      (sumInputsEquiv (orderedInputEquiv (orderedReindexHom e X Y h))
        (Equiv.refl (Fin (arity D)))) :=
  (equiv_count_transport_heq (snocBlocks_totalArity X D) (snocBlocks_totalArity Y D)
    (orderedInputEquiv (retainedLastHom e X Y D h))).symm.trans
      (heq_of_eq (retainedLast_inputEquiv_sum e X Y D h))

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_RetainedLastInputEquiv

/- Source proof segment: SnocInputObjects -/
section source_SnocInputObjects
/-!
# Actual original objects of retained-last block inputs

The flattened input family is its actual original append after the
exact original total-count transport.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

variable {C : Type u}

/-- The actual input family after retaining a last block is the original appended input family. -/
theorem snocBlocks_inputs {n : ℕ} (X : Fin n → FiniteFamily C) (D : FiniteFamily C)
    (j : Fin ((blocksOfFamily X).totalArity + arity D)) :
    (blocksOfFamily (Fin.snoc X D)).inputs (Fin.cast (snocBlocks_totalArity X D).symm j) =
      Fin.append (blocksOfFamily X).inputs (orderedFamily D) j :=
  (blocks_inputs_transport (blocksOfFamily_snoc X D).symm j).symm

/-- Every original retained prefix input keeps its original source object. -/
theorem snocInputLeft_objects {n : ℕ} (X : Fin n → FiniteFamily C) (D : FiniteFamily C)
    (j : Fin (blocksOfFamily X).totalArity) :
    (blocksOfFamily (Fin.snoc X D)).inputs (snocInputLeft X D j) =
      (blocksOfFamily X).inputs j :=
  (snocBlocks_inputs X D (Fin.castAdd (arity D) j)).trans (Fin.append_left _ _ j)

/-- Every original retained last-block input keeps its original source object. -/
theorem snocInputRight_objects {n : ℕ} (X : Fin n → FiniteFamily C) (D : FiniteFamily C)
    (j : Fin (arity D)) :
    (blocksOfFamily (Fin.snoc X D)).inputs (snocInputRight X D j) = orderedFamily D j :=
  (snocBlocks_inputs X D (Fin.natAdd (blocksOfFamily X).totalArity j)).trans
    (Fin.append_right _ _ j)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_SnocInputObjects

/- Source proof segment: RetainedLastInputComponents -/
section source_RetainedLastInputComponents
/-!
# Original component maps of retained-last ordered reindexing

Every original prefix component is retained and every original input
of the last block carries its original identity map.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory TensorReindexing

variable {C : Type u} [Category.{v} C]

/-- Retaining the last original block keeps every original prefix component map. -/
theorem retainedLast_component_left {n : ℕ} (e : Equiv.Perm (Fin n))
    (X Y : Fin n → FiniteFamily C) (D : FiniteFamily C) (h : ∀ i, X i = Y (e i))
    (j : Fin (blocksOfFamily X).totalArity) :
    HEq (orderedInputComponent (retainedLastHom e X Y D h) (snocInputLeft X D j))
      (orderedInputComponent (orderedReindexHom e X Y h) j) :=
  ((orderedReindex_component_id (extendPerm n e) (Fin.snoc X D) (Fin.snoc Y D)
    (snoc_reindex_objects e X Y D h) (snocInputLeft X D j)).trans
      (inputObject_identity_heq (snocInputLeft_objects X D j))).trans
        (orderedReindex_component_id e X Y h j).symm

/-- Retaining the last original block keeps the identity of every original last-block input. -/
theorem retainedLast_component_right {n : ℕ} (e : Equiv.Perm (Fin n))
    (X Y : Fin n → FiniteFamily C) (D : FiniteFamily C) (h : ∀ i, X i = Y (e i))
    (j : Fin (arity D)) :
    HEq (orderedInputComponent (retainedLastHom e X Y D h) (snocInputRight X D j))
      (𝟙 (orderedFamily D j)) :=
  (orderedReindex_component_id (extendPerm n e) (Fin.snoc X D) (Fin.snoc Y D)
    (snoc_reindex_objects e X Y D h) (snocInputRight X D j)).trans
      (inputObject_identity_heq (snocInputRight_objects X D j))

/-- The complete actual retained-last component family is the original sum component family. -/
theorem retainedLast_components_sum {n : ℕ} (e : Equiv.Perm (Fin n))
    (X Y : Fin n → FiniteFamily C) (D : FiniteFamily C) (h : ∀ i, X i = Y (e i))
    (j : Fin ((blocksOfFamily X).totalArity + arity D)) :
    HEq (orderedInputComponent (retainedLastHom e X Y D h)
      (Fin.cast (snocBlocks_totalArity X D).symm j))
      (sumInputsComponent
        (X := (blocksOfFamily X).inputs) (X' := (blocksOfFamily Y).inputs)
        (Y := orderedFamily D) (Y' := orderedFamily D)
        (e := orderedInputEquiv (orderedReindexHom e X Y h)) (d := Equiv.refl (Fin (arity D)))
        (orderedInputComponent (orderedReindexHom e X Y h))
        (fun i => 𝟙 (orderedFamily D i)) j) := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · exact (retainedLast_component_left e X Y D h i).trans
      (sumInputsComponent_left_heq
        (d := Equiv.refl (Fin (arity D)))
        (orderedInputComponent (orderedReindexHom e X Y h))
        (fun i => 𝟙 (orderedFamily D i)) i).symm
  · exact (retainedLast_component_right e X Y D h i).trans
      (sumInputsComponent_right_heq
        (d := Equiv.refl (Fin (arity D)))
        (orderedInputComponent (orderedReindexHom e X Y h))
        (fun i => 𝟙 (orderedFamily D i)) i).symm

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_RetainedLastInputComponents

/- Source proof segment: RetainedLastInputMap -/
section source_RetainedLastInputMap
/-!
# Original retained-last ordered input map and append conjugacy

The original literal input map is the actual sum tensor map after
its complete count, family, bijection and component transports.
The original independent-block tensor square gives append conjugacy.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [SymmetricCategory C] in
/-- The actual retained-last tensor carrier is the original appended input carrier. -/
theorem snocBlocks_obj_eq {n : ℕ} (X : Fin n → FiniteFamily C) (D : FiniteFamily C) :
    obj (blocksOfFamily (Fin.snoc X D)).inputs =
      obj (Fin.append (blocksOfFamily X).inputs (orderedFamily D)) :=
  blocks_obj_transport (blocksOfFamily_snoc X D)

/-- The actual sum tensor map retaining the original prefix components
and original last identities. -/
noncomputable def retainedLastSumMap {n : ℕ} (e : Equiv.Perm (Fin n))
    (X Y : Fin n → FiniteFamily C) (D : FiniteFamily C) (h : ∀ i, X i = Y (e i)) :
    obj (Fin.append (blocksOfFamily X).inputs (orderedFamily D)) ⟶
      obj (Fin.append (blocksOfFamily Y).inputs (orderedFamily D)) :=
  mapEquiv
    (sumInputsEquiv (orderedInputEquiv (orderedReindexHom e X Y h))
      (Equiv.refl (Fin (arity D))))
    (sumInputsComponent
      (X := (blocksOfFamily X).inputs) (X' := (blocksOfFamily Y).inputs)
      (Y := orderedFamily D) (Y' := orderedFamily D)
      (e := orderedInputEquiv (orderedReindexHom e X Y h)) (d := Equiv.refl (Fin (arity D)))
      (orderedInputComponent (orderedReindexHom e X Y h)) (fun i => 𝟙 (orderedFamily D i)))

/-- The actual retained-last literal input map retains every original sum input and component. -/
theorem retainedLast_inputMap_sum_heq {n : ℕ} (e : Equiv.Perm (Fin n))
    (X Y : Fin n → FiniteFamily C) (D : FiniteFamily C) (h : ∀ i, X i = Y (e i)) :
    HEq (orderedInputMap (retainedLastHom e X Y D h)) (retainedLastSumMap e X Y D h) := by
  apply mapEquiv_input_heq
    (snocBlocks_totalArity X D) (snocBlocks_totalArity Y D)
    (blocksOfFamily (Fin.snoc X D)).inputs
    (Fin.append (blocksOfFamily X).inputs (orderedFamily D))
    (blocksOfFamily (Fin.snoc Y D)).inputs
    (Fin.append (blocksOfFamily Y).inputs (orderedFamily D))
    (blocks_inputs_transport (blocksOfFamily_snoc X D))
    (blocks_inputs_transport (blocksOfFamily_snoc Y D))
    (orderedInputEquiv (retainedLastHom e X Y D h))
    (sumInputsEquiv (orderedInputEquiv (orderedReindexHom e X Y h))
      (Equiv.refl (Fin (arity D)))) (retainedLast_inputEquiv_heq e X Y D h)
    (orderedInputComponent (retainedLastHom e X Y D h))
    (sumInputsComponent
      (X := (blocksOfFamily X).inputs) (X' := (blocksOfFamily Y).inputs)
      (Y := orderedFamily D) (Y' := orderedFamily D)
      (e := orderedInputEquiv (orderedReindexHom e X Y h)) (d := Equiv.refl (Fin (arity D)))
      (orderedInputComponent (orderedReindexHom e X Y h)) (fun i => 𝟙 (orderedFamily D i)))
  intro j
  have hc := retainedLast_components_sum e X Y D h (Fin.cast (snocBlocks_totalArity X D) j)
  have hj : Fin.cast (snocBlocks_totalArity X D).symm
      (Fin.cast (snocBlocks_totalArity X D) j) = j := by
    apply Fin.ext
    rfl
  rw [hj] at hc
  exact hc

/-- The actual retained-last sum tensor map satisfies the original append square. -/
theorem retainedLastSumMap_append {n : ℕ} (e : Equiv.Perm (Fin n))
    (X Y : Fin n → FiniteFamily C) (D : FiniteFamily C) (h : ∀ i, X i = Y (e i)) :
    retainedLastSumMap e X Y D h ≫
        (appendIso (blocksOfFamily Y).inputs (orderedFamily D)).hom =
      (appendIso (blocksOfFamily X).inputs (orderedFamily D)).hom ≫
        (orderedInputMap (orderedReindexHom e X Y h) ⊗ₘ 𝟙 (finiteObj D)) := by
  have hs := mapEquiv_sum
    (X := (blocksOfFamily X).inputs) (X' := (blocksOfFamily Y).inputs)
    (Y := orderedFamily D) (Y' := orderedFamily D)
    (orderedInputEquiv (orderedReindexHom e X Y h)) (Equiv.refl (Fin (arity D)))
    (orderedInputComponent (orderedReindexHom e X Y h)) (fun i => 𝟙 (orderedFamily D i))
  rw [mapEquiv_id] at hs
  exact hs

/-- The original retained-last sum tensor map is the exact original append conjugacy. -/
theorem retainedLastSumMap_conjugacy {n : ℕ} (e : Equiv.Perm (Fin n))
    (X Y : Fin n → FiniteFamily C) (D : FiniteFamily C) (h : ∀ i, X i = Y (e i)) :
    retainedLastSumMap e X Y D h =
      ((appendIso (blocksOfFamily X).inputs (orderedFamily D)).hom ≫
        (orderedInputMap (orderedReindexHom e X Y h) ⊗ₘ 𝟙 (finiteObj D))) ≫
          (appendIso (blocksOfFamily Y).inputs (orderedFamily D)).inv := by
  exact (Iso.eq_comp_inv (appendIso (blocksOfFamily Y).inputs (orderedFamily D))).mpr
    (retainedLastSumMap_append e X Y D h)

/-- The actual retained-last ordered input map keeps the complete original append conjugacy. -/
theorem retainedLast_inputMap_heq {n : ℕ} (e : Equiv.Perm (Fin n))
    (X Y : Fin n → FiniteFamily C) (D : FiniteFamily C) (h : ∀ i, X i = Y (e i)) :
    HEq (orderedInputMap (retainedLastHom e X Y D h))
      (((appendIso (blocksOfFamily X).inputs (orderedFamily D)).hom ≫
        (orderedInputMap (orderedReindexHom e X Y h) ⊗ₘ 𝟙 (finiteObj D))) ≫
          (appendIso (blocksOfFamily Y).inputs (orderedFamily D)).inv) :=
  (retainedLast_inputMap_sum_heq e X Y D h).trans
    (heq_of_eq (retainedLastSumMap_conjugacy e X Y D h))

/-- The exact actual retained-last input map, including every original
carrier equality transport. -/
theorem retainedLast_inputMap {n : ℕ} (e : Equiv.Perm (Fin n))
    (X Y : Fin n → FiniteFamily C) (D : FiniteFamily C) (h : ∀ i, X i = Y (e i)) :
    orderedInputMap (retainedLastHom e X Y D h) =
      eqToHom (snocBlocks_obj_eq X D) ≫
        (((appendIso (blocksOfFamily X).inputs (orderedFamily D)).hom ≫
          (orderedInputMap (orderedReindexHom e X Y h) ⊗ₘ 𝟙 (finiteObj D))) ≫
            (appendIso (blocksOfFamily Y).inputs (orderedFamily D)).inv) ≫
              eqToHom (snocBlocks_obj_eq Y D).symm := by
  have ht := (conj_eqToHom_iff_heq
    (orderedInputMap (retainedLastHom e X Y D h))
    (((appendIso (blocksOfFamily X).inputs (orderedFamily D)).hom ≫
      (orderedInputMap (orderedReindexHom e X Y h) ⊗ₘ 𝟙 (finiteObj D))) ≫
        (appendIso (blocksOfFamily Y).inputs (orderedFamily D)).inv)
    (snocBlocks_obj_eq X D) (snocBlocks_obj_eq Y D)).mpr (retainedLast_inputMap_heq e X Y D h)
  exact ht

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_RetainedLastInputMap

/- Source proof segment: OuterSwapInputGeometry -/
section source_OuterSwapInputGeometry
/-!
# Complete original outer-swap input geometry

Both the original final-pair interchange and a retained final block
keep their complete original input bijections, equality components,
and actual tensor maps with original count and carrier transports.
-/
end source_OuterSwapInputGeometry

/- Source proof segment: OrderedReindexSteps -/
section source_OrderedReindexSteps
/-!
# Original ordered block reindexing naturality steps

The complete original final-block input map and the complete original
retained-final input map are joined to their original tensor output
maps. Every input transport and all empty block cases are retained.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

private theorem swapPrefix_heq {P T : C} (h : P = T) (A D : C) :
    HEq (swapLastIso P A D).hom (swapLastIso T A D).hom := by
  cases h
  rfl

private theorem swapData_heq {P P' A A' D D' : C} (hP : P = P') (hA : A = A') (hD : D = D') :
    HEq (swapLastIso P A D).hom (swapLastIso P' A' D').hom := by
  cases hP
  cases hA
  cases hD
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual final outer-block input transposition commutes with the original full ordered
block fold. -/
theorem lastPairReindex_naturality {n : ℕ} (P : Fin n → FiniteFamily C) (A D : FiniteFamily C) :
    orderedInputMap (lastPairReindex P A D) ≫
        (blocksOfFamilyIso (Fin.snoc (Fin.snoc P D) A)).hom =
      (blocksOfFamilyIso (Fin.snoc (Fin.snoc P A) D)).hom ≫
        orderedOutputMap (lastPairReindex P A D) := by
  let X : Fin (n + 2) → FiniteFamily C := Fin.snoc (Fin.snoc P A) D
  let Y : Fin (n + 2) → FiniteFamily C := Fin.snoc (Fin.snoc P D) A
  have hRaw : HEq (orderedOutputMap (lastPairReindex P A D))
      (swapLastIso (obj (fun i : Fin n => finiteObj (P i))) (finiteObj A) (finiteObj D)).hom := by
    have h := orderedOutput_reindex_last_heq X Y (lastOuterSwap_objects P A D)
    have hP : (fun j : Fin n => finiteObj (X j.castSucc.castSucc)) = fun j => finiteObj (P j) :=
      funext (fun j => congrArg finiteObj (lastPair_prefix_label P A D j).symm)
    have hA : finiteObj (X (Fin.last n).castSucc) = finiteObj A :=
      congrArg finiteObj (lastPair_middle_label P A D).symm
    have hD : finiteObj (X (Fin.last (n + 1))) = finiteObj D :=
      congrArg finiteObj (lastPair_last_label P A D).symm
    exact h.trans (swapData_heq (congrArg obj hP) hA hD)
  have hOut := hRaw.trans (swapPrefix_heq (blocksOfFamily_tensors P).symm (finiteObj A)
    (finiteObj D))
  have hLeft := heq_comp (lastPair_obj_eq P A D) (lastPair_obj_eq P D A)
    (blocksOfFamily_pair_output_eq P D A) (lastPairInputMap_heq P A D)
      (blocksOfFamilyIso_pair_heq P D A)
  have hRight := heq_comp (lastPair_obj_eq P A D) (blocksOfFamily_pair_output_eq P A D)
    (blocksOfFamily_pair_output_eq P D A) (blocksOfFamilyIso_pair_heq P A D) hOut
  exact eq_of_heq (hLeft.trans
    ((heq_of_eq (blockLastSwap_pairSplit (blocksOfFamily P) (orderedFamily A) (orderedFamily
      D))).trans hRight.symm))

set_option backward.isDefEq.respectTransparency false in
/-- An actual original prefix reindexing square retains the original final block and its
original tensor identity. -/
theorem retainedLastReindex_naturality {n : ℕ} (e : Equiv.Perm (Fin n))
    (X Y : Fin n → FiniteFamily C) (D : FiniteFamily C) (h : ∀ i, X i = Y (e i))
    (hPrefix : orderedInputMap (orderedReindexHom e X Y h) ≫ (blocksOfFamilyIso Y).hom =
      (blocksOfFamilyIso X).hom ≫ orderedOutputMap (orderedReindexHom e X Y h)) :
    orderedInputMap (retainedLastHom e X Y D h) ≫ (blocksOfFamilyIso (Fin.snoc Y D)).hom =
      (blocksOfFamilyIso (Fin.snoc X D)).hom ≫ orderedOutputMap (retainedLastHom e X Y D h) := by
  have hLeft := heq_comp (snocBlocks_obj_eq X D) (snocBlocks_obj_eq Y D)
    (blocksOfFamily_snoc_output_eq Y D) (retainedLast_inputMap_heq e X Y D h)
      (blocksOfFamilyIso_snoc_heq Y D)
  have hRight := heq_comp (snocBlocks_obj_eq X D) (blocksOfFamily_snoc_output_eq X D)
    (blocksOfFamily_snoc_output_eq Y D) (blocksOfFamilyIso_snoc_heq X D)
      (orderedOutput_reindex_snoc_heq e X Y D h)
  let dSource : obj (Fin.append (blocksOfFamily X).inputs (orderedFamily D)) ≅
      obj (blocksOfFamily X).inputs ⊗ finiteObj D := appendIso (blocksOfFamily X).inputs
        (orderedFamily D)
  let dTarget : obj (Fin.append (blocksOfFamily Y).inputs (orderedFamily D)) ≅
      obj (blocksOfFamily Y).inputs ⊗ finiteObj D := appendIso (blocksOfFamily Y).inputs
        (orderedFamily D)
  have hCore := appendSquare_final dSource dTarget
    (orderedInputMap (orderedReindexHom e X Y h)) (blocksOfFamilyIso X).hom
    (blocksOfFamilyIso Y).hom (orderedOutputMap (orderedReindexHom e X Y h)) hPrefix
  simp only [dSource, dTarget, Category.assoc] at hCore
  simp only [Category.assoc, retainedLastHom] at hLeft hRight ⊢
  exact eq_of_heq (hLeft.trans ((heq_of_eq hCore).trans hRight.symm))

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedReindexSteps

/- Source proof segment: OrderedReindexFullNaturality -/
section source_OrderedReindexFullNaturality
/-!
# Full original ordered block tensor naturality

Original binary block interchange proves every original adjacent
outer reindexing square. The actual finite adjacent generators give
every finite permutation square, and original inner fiber maps give
the full square for arbitrary original ordered outer morphisms.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory TensorReindexing

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

private theorem reindexSquare_transport {n : ℕ} (e d : Equiv.Perm (Fin n)) (he : e = d)
    (X0 Y0 X Y : Fin n → FiniteFamily C) (hX : X0 = X) (hY : Y0 = Y)
    (h0 : ∀ i, X0 i = Y0 (e i)) (h : ∀ i, X i = Y (d i))
    (hn : orderedInputMap (orderedReindexHom e X0 Y0 h0) ≫ (blocksOfFamilyIso Y0).hom =
      (blocksOfFamilyIso X0).hom ≫ orderedOutputMap (orderedReindexHom e X0 Y0 h0)) :
    orderedInputMap (orderedReindexHom d X Y h) ≫ (blocksOfFamilyIso Y).hom =
      (blocksOfFamilyIso X).hom ≫ orderedOutputMap (orderedReindexHom d X Y h) := by
  cases he
  cases hX
  cases hY
  exact hn

set_option backward.isDefEq.respectTransparency false in
/-- Every original adjacent outer block reindexing commutes with the actual original ordered
block tensor split. -/
theorem orderedReindexNatural_adjacent : ∀ {n : ℕ} (i : Fin n),
    OrderedReindexNatural (C := C) (Equiv.swap i.castSucc i.succ) := by
  intro n
  induction n with
  | zero => intro i; exact i.elim0
  | succ n ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · intro X Y h
        let P : Fin n → FiniteFamily C := Fin.init (Fin.init X)
        let A := X (Fin.last n).castSucc
        let D := X (Fin.last (n + 1))
        let X0 : Fin (n + 2) → FiniteFamily C := Fin.snoc (Fin.snoc P A) D
        let Y0 : Fin (n + 2) → FiniteFamily C := Fin.snoc (Fin.snoc P D) A
        have hx1 : Fin.snoc P A = Fin.init X := Fin.snoc_init_self (Fin.init X)
        have hx0 : Fin.snoc (Fin.init X) D = X := Fin.snoc_init_self X
        have hx : X0 = X :=
          (congrArg (fun Q : Fin (n + 1) → FiniteFamily C =>
            Fin.snoc (α := fun _ : Fin (n + 2) => FiniteFamily C) Q D) hx1).trans hx0
        have hy : Y0 = Y :=
          (reindexedFamily_eq (lastOuterSwap n) X0 Y0 (lastOuterSwap_objects P A D)).symm.trans
            (reindexedFamily_eq (lastOuterSwap n) X0 Y (fun k => (congrFun hx k).trans (h k)))
        exact reindexSquare_transport (lastOuterSwap n)
          (Equiv.swap (Fin.last n).castSucc (Fin.last n).succ) rfl X0 Y0 X Y hx hy
          (lastOuterSwap_objects P A D) h (lastPairReindex_naturality P A D)
      · intro X Y h
        let e : Equiv.Perm (Fin (n + 1)) := Equiv.swap j.castSucc j.succ
        have hExtend : Equiv.swap j.castSucc.castSucc j.castSucc.succ = extendPerm (n + 1) e :=
          congrArg (fun r : TensorReindexing C (n + 2) => r.perm)
            (tensorGenerator_castSucc (C := C) j)
        have hLast : X (Fin.last (n + 1)) = Y (Fin.last (n + 1)) := by
          have hh := h (Fin.last (n + 1))
          rw [hExtend, extendPerm_last] at hh
          exact hh
        have hPrefix : ∀ k : Fin (n + 1), (Fin.init X) k = (Fin.init Y) (e k) := by
          intro k
          have hh := h k.castSucc
          rw [hExtend, extendPerm_castSucc] at hh
          exact hh
        let D := X (Fin.last (n + 1))
        let X0 : Fin (n + 2) → FiniteFamily C := Fin.snoc (Fin.init X) D
        let Y0 : Fin (n + 2) → FiniteFamily C := Fin.snoc (Fin.init Y) D
        have hx : X0 = X := Fin.snoc_init_self X
        have hy : Y0 = Y :=
          (congrArg (fun A : FiniteFamily C => Fin.snoc (Fin.init Y) A) hLast).trans
            (Fin.snoc_init_self Y)
        have hN := retainedLastReindex_naturality e (Fin.init X) (Fin.init Y) D hPrefix
          (ih j (Fin.init X) (Fin.init Y) hPrefix)
        exact reindexSquare_transport (extendPerm (n + 1) e)
          (Equiv.swap j.castSucc.castSucc j.castSucc.succ) hExtend.symm X0 Y0 X Y hx hy
          (snoc_reindex_objects e (Fin.init X) (Fin.init Y) D hPrefix) h hN

/-- All actual finite outer permutations commute with the original ordered block tensor split. -/
theorem orderedReindexSubmonoid_top (n : ℕ) : orderedReindexSubmonoid (C := C) n = ⊤ := by
  cases n with
  | zero =>
      apply le_antisymm le_top
      intro p _
      have hp : p = (1 : Equiv.Perm (Fin 0)) := Subsingleton.elim _ _
      rw [hp]
      exact (orderedReindexSubmonoid (C := C) 0).one_mem
  | succ n =>
      have hgen : Submonoid.closure
          (Set.range (fun i : Fin n => Equiv.swap i.castSucc i.succ)) ≤
          orderedReindexSubmonoid (C := C) (n + 1) := by
        apply Submonoid.closure_le.mpr
        rintro _ ⟨i, rfl⟩
        exact orderedReindexNatural_adjacent i
      rw [Equiv.Perm.mclosure_swap_castSucc_succ n] at hgen
      exact le_antisymm le_top hgen

/-- Original arbitrary finite outer input bijections and original object equality maps give
the full original block
  split square. -/
theorem orderedReindex_naturality {m n : ℕ} (e : Fin m ≃ Fin n)
    (X : Fin m → FiniteFamily C) (Y : Fin n → FiniteFamily C) (h : ∀ i, X i = Y (e i)) :
    orderedInputMap (orderedReindexHom e X Y h) ≫ (blocksOfFamilyIso Y).hom =
      (blocksOfFamilyIso X).hom ≫ orderedOutputMap (orderedReindexHom e X Y h) := by
  have hmn := equiv_arity_eq e
  cases hmn
  have he : e ∈ orderedReindexSubmonoid (C := C) m := by
    rw [orderedReindexSubmonoid_top]
    trivial
  exact he X Y h

set_option backward.isDefEq.respectTransparency false in
/-- All original outer finite input bijections, inner input bijections and inner component
maps commute with the actual
  full ordered block split. -/
theorem blocksOfFamilyIso_naturality {m n : ℕ} {X : Fin m → FiniteFamily C} {Y : Fin n
  → FiniteFamily C}
    (F : literalOuterFamily X ⟶ literalOuterFamily Y) :
    orderedInputMap F ≫ (blocksOfFamilyIso Y).hom = (blocksOfFamilyIso X).hom ≫
      orderedOutputMap F := by
  let Z : Fin m → FiniteFamily C := fun i => Y (F.equiv i)
  let G : literalOuterFamily X ⟶ literalOuterFamily Z := orderedFixedHom (fun i => F.hom i)
  let H : literalOuterFamily Z ⟶ literalOuterFamily Y :=
    orderedReindexHom F.equiv Z Y (fun _ => rfl)
  have hComp : G ≫ H = F := by
    apply FiniteFamily.Hom_ext
    · exact Equiv.refl_trans _
    · intro i
      exact heq_of_eq (Category.comp_id (F.hom i))
  have hG := orderedFixed_naturality (fun i => F.hom i)
  have hH := orderedReindex_naturality F.equiv Z Y (fun _ => rfl)
  rw [← hComp, orderedInputMap_comp, orderedOutputMap_comp]
  simp only [Category.assoc]
  rw [hH, ← Category.assoc, hG, Category.assoc]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedReindexFullNaturality

/- Source proof segment: FiniteTensorFixedIndexReadback -/
section source_FiniteTensorFixedIndexReadback
/-!
# Exact fixed-index readbacks of the produced binary finite tensor

The identity input-equivalence map of finite families is the original
componentwise ordered tensor map, through the same original finite
input enumeration used by the produced carrier.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

attribute [local instance] FintypeCat.fintype

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The actual finite-family morphism with unchanged original finite input indices. -/
def fixedIndexHom (I : FintypeCat.{0}) {X Y : I → C} (f : ∀ i, X i ⟶ Y i) :
    (⟨I, X⟩ : FiniteFamily C) ⟶ (⟨I, Y⟩ : FiniteFamily C) where
  equiv := Equiv.refl I
  hom := f

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The original fixed-index input map normalizes to the actual identity finite equivalence. -/
theorem enumeratedEquiv_fixedIndex (I : FintypeCat.{0}) {X Y : I → C}
    (f : ∀ i, X i ⟶ Y i) :
    enumeratedEquiv (fixedIndexHom I f) = Equiv.refl (Fin (Fintype.card I)) := by
  apply Equiv.ext
  intro i
  exact (Fintype.equivFin I).apply_symm_apply i

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The original component map of the fixed-index morphism retains its original tensor input. -/
theorem enumeratedMap_fixedIndex_heq (I : FintypeCat.{0}) {X Y : I → C}
    (f : ∀ i, X i ⟶ Y i) (i : Fin (Fintype.card I)) :
    HEq (enumeratedMap (fixedIndexHom I f) i) (f ((Fintype.equivFin I).symm i)) :=
  enumeratedMap_heq (fixedIndexHom I f) i

/-- The produced binary finite tensor maps identity input equivalences to the original
tensor maps. -/
theorem finiteTensorFunctor_map_fixedIndex (I : FintypeCat.{0}) {X Y : I → C}
    (f : ∀ i, X i ⟶ Y i) :
    finiteTensorFunctor.map (fixedIndexHom I f) = fixedIndexMap I f := by
  change mapEquiv (enumeratedEquiv (fixedIndexHom I f)) (enumeratedMap (fixedIndexHom I f)) = _
  have h := mapEquiv_congr (enumeratedEquiv_fixedIndex I f)
    (enumeratedMap (fixedIndexHom I f)) (fun i => f ((Fintype.equivFin I).symm i))
    (enumeratedMap_fixedIndex_heq I f)
  exact h.trans (mapEquiv_refl _)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FiniteTensorFixedIndexReadback

/- Source proof segment: FiniteTensorFiberNaturality -/
section source_FiniteTensorFiberNaturality
/-!
# Original finite tensor flattening naturality in every fixed outer fiber

The original outer finite index is retained while every inner input
bijection and every inner component morphism varies. Both sides are
the actual original finite tensor maps on those data.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

attribute [local instance] FintypeCat.fintype

variable {C : Type u} [Category.{v} C]

/-- The original nested morphism with fixed original outer finite indices and arbitrary
original inner morphisms. -/
def fixedOuterHom (I : FintypeCat) {X Y : I → FiniteFamily C} (f : ∀ i, X i ⟶ Y i) :
    (⟨I, X⟩ : FiniteFamily (FiniteFamily C)) ⟶ ⟨I, Y⟩ where
  equiv := Equiv.refl I
  hom := f

/-- Every original inner morphism occupies its chosen original outer enumeration slot. -/
noncomputable def orderedInnerHom (I : FintypeCat) {X Y : I → FiniteFamily C}
    (f : ∀ i, X i ⟶ Y i) :
    (i : Fin (Fintype.card I)) →
      (X ∘ (Fintype.equivFin I).symm) i ⟶ (Y ∘ (Fintype.equivFin I).symm) i :=
  fun i => f ((Fintype.equivFin I).symm i)

set_option backward.isDefEq.respectTransparency false in
/-- The actual fixed-outer word bijection is the original ordered inner-block input bijection. -/
theorem fixedOuter_word_equiv (I : FintypeCat) {X Y : I → FiniteFamily C}
    (f : ∀ i, X i ⟶ Y i) :
    wordInputEquiv (fixedOuterHom I f) = (blocksOfFamilyFiberMap (orderedInnerHom I
      f)).inputEquiv := by
  apply Equiv.ext
  intro i
  apply (nestedPositionsEquiv (⟨I, Y⟩ : FiniteFamily (FiniteFamily C))).injective
  have hL := wordInput_positions (fixedOuterHom I f) i
  have hR := congrArg (originalOuterPositionsEquiv (⟨I, Y⟩ : FiniteFamily (FiniteFamily C)))
    (blocksOfFamilyFiberMap_positions (orderedInnerHom I f) i)
  exact hL.trans hR.symm

set_option backward.isDefEq.respectTransparency false in
/-- Every actual word component is its original fixed-outer inner component morphism. -/
theorem fixedOuter_word_components (I : FintypeCat) {X Y : I → FiniteFamily C}
    (f : ∀ i, X i ⟶ Y i)
    (i : Fin (blocksOfFiniteFamily (⟨I, X⟩ : FiniteFamily (FiniteFamily C))).totalArity) :
    HEq (wordInputComponent (fixedOuterHom I f) i)
      ((blocksOfFamilyFiberMap (orderedInnerHom I f)).inputComponents i) := by
  have hR := blocksOfFamilyFiberMap_components (orderedInnerHom I f) i
  exact (wordInputComponent_heq (fixedOuterHom I f) i).trans hR.symm

variable [MonoidalCategory C] [SymmetricCategory C]

/-- The actual fixed-outer word tensor map is the original ordered inner fiber tensor map. -/
theorem fixedOuter_word_map (I : FintypeCat) {X Y : I → FiniteFamily C}
    (f : ∀ i, X i ⟶ Y i) :
    wordInputMap (fixedOuterHom I f) = (blocksOfFamilyFiberMap (orderedInnerHom I f)).inputMap := by
  unfold wordInputMap Blocks.FiberMap.inputMap
  exact mapEquiv_congr (fixedOuter_word_equiv I f) _ _ (fixedOuter_word_components I f)

set_option backward.isDefEq.respectTransparency false in
/-- The actual outer finite tensor map is the original ordered tensor of the original inner
finite tensor maps. -/
theorem fixedOuter_output_map (I : FintypeCat) {X Y : I → FiniteFamily C}
    (f : ∀ i, X i ⟶ Y i) :
    finiteMap ((FiniteFamily.map (finiteTensorFunctor (C := C))).map (fixedOuterHom I f)) =
      map (fun i => finiteMap (orderedInnerHom I f i)) := by
  change (finiteTensorFunctor (C := C)).map
      (fixedIndexHom I (fun i => finiteMap (f i))) = _
  rw [finiteTensorFunctor_map_fixedIndex]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- All original inner input bijections and component maps commute with the original finite
outer block comparison. -/
theorem finiteFamilyBlocks_fiber_naturality (I : FintypeCat) {X Y : I → FiniteFamily C}
    (f : ∀ i, X i ⟶ Y i) :
    wordInputMap (fixedOuterHom I f) ≫
        (finiteFamilyBlocksIso (⟨I, Y⟩ : FiniteFamily (FiniteFamily C))).hom =
      (finiteFamilyBlocksIso (⟨I, X⟩ : FiniteFamily (FiniteFamily C))).hom ≫
        finiteMap ((FiniteFamily.map (finiteTensorFunctor (C := C))).map (fixedOuterHom I f)) := by
  rw [fixedOuter_word_map, fixedOuter_output_map]
  exact blocksOfFamilyIso_fiber_naturality (orderedInnerHom I f)

set_option backward.isDefEq.respectTransparency false in
/-- The complete original finite tensor flattening square holds for every original inner
fiber morphism. -/
theorem finiteFlatten_fiber_naturality (I : FintypeCat) {X Y : I → FiniteFamily C}
    (f : ∀ i, X i ⟶ Y i) :
    finiteMap ((FiniteFamily.flatten (C := C)).map (fixedOuterHom I f)) ≫
        (finiteFlattenIso (⟨I, Y⟩ : FiniteFamily (FiniteFamily C))).hom =
      (finiteFlattenIso (⟨I, X⟩ : FiniteFamily (FiniteFamily C))).hom ≫
        finiteMap ((FiniteFamily.map (finiteTensorFunctor (C := C))).map (fixedOuterHom I f)) := by
  rw [finiteFlattenIso_hom, finiteFlattenIso_hom]
  unfold finiteFlattenHom
  rw [← Category.assoc, flattenToWord_naturality, Category.assoc,
    finiteFamilyBlocks_fiber_naturality, Category.assoc]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FiniteTensorFiberNaturality

/- Source proof segment: FiniteTensorOuterNormalization -/
section source_FiniteTensorOuterNormalization
/-!
# Original finite outer-family normalization

The two original outer enumerations normalize the original outer
input bijection and every original inner finite-family morphism. The
complete original sigma input positions and components are retained.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C]

/-- The actual original outer morphism on its two original ordered outer enumerations. -/
noncomputable def normalizedOuterHom {X Y : FiniteFamily (FiniteFamily C)} (f : X ⟶ Y) :
    literalOuterFamily (orderedFamily X) ⟶ literalOuterFamily (orderedFamily Y) where
  equiv := enumeratedEquiv f
  hom := enumeratedMap f

set_option backward.isDefEq.respectTransparency false in
/-- Every original nested input is retained under the complete original outer normalization. -/
theorem normalizedOuter_positions {X Y : FiniteFamily (FiniteFamily C)} (f : X ⟶ Y)
    (p : OriginalPositions (orderedFamily X)) :
    originalOuterPositionsEquiv Y (((FiniteFamily.flatten (C :=
      C)).map (normalizedOuterHom f)).equiv p) =
      nestedInputEquiv f (originalOuterPositionsEquiv X p) := by
  apply Sigma.ext
  · exact enumeration_enumeratedEquiv f p.1
  · change HEq
      ((eqToHom (congrArg Y.obj
        ((enumeration Y).apply_symm_apply (f.equiv (enumeration X p.1))).symm)).equiv
          ((f.hom (enumeration X p.1)).equiv p.2))
      ((f.hom (enumeration X p.1)).equiv p.2)
    exact familyEquality_equiv_heq _ _

set_option backward.isDefEq.respectTransparency false in
/-- The complete actual ordered input bijection is its original nested finite-family input
bijection. -/
theorem normalizedOuter_inputEquiv {X Y : FiniteFamily (FiniteFamily C)} (f : X ⟶ Y) :
    wordInputEquiv f = orderedInputEquiv (normalizedOuterHom f) := by
  apply Equiv.ext
  intro i
  apply (nestedPositionsEquiv Y).injective
  have hL := wordInput_positions f i
  have hR := (congrArg (originalOuterPositionsEquiv Y)
    (orderedInput_positions (normalizedOuterHom f) i)).trans
      (normalizedOuter_positions f (flattenedPositionsEquiv (orderedFamily X) i))
  exact hL.trans hR.symm

private theorem innerComponent_eq_transport {A B D : FiniteFamily C} (f : A ⟶ B)
    (h : B = D) (i : A.index) : HEq ((f ≫ eqToHom h).hom i) (f.hom i) := by
  cases h
  change HEq (f.hom i ≫ 𝟙 _) (f.hom i)
  exact heq_of_eq (Category.comp_id _)

set_option backward.isDefEq.respectTransparency false in
/-- Every original normalized flattened component retains the complete original inner
component map. -/
theorem normalizedOuter_flat_component_heq {X Y : FiniteFamily (FiniteFamily C)} (f : X ⟶ Y)
    (p : OriginalPositions (orderedFamily X)) :
    HEq (((FiniteFamily.flatten (C := C)).map (normalizedOuterHom f)).hom p)
      (nestedInputMap f (originalOuterPositionsEquiv X p)) :=
  innerComponent_eq_transport (f.hom (enumeration X p.1)) _ p.2

set_option backward.isDefEq.respectTransparency false in
/-- The actual original ordered input component is the original nested input component. -/
theorem normalizedOuter_inputComponents {X Y : FiniteFamily (FiniteFamily C)} (f : X ⟶ Y)
    (i : Fin (blocksOfFiniteFamily X).totalArity) :
    HEq (wordInputComponent f i) (orderedInputComponent (normalizedOuterHom f) i) := by
  have hL := wordInputComponent_heq f i
  have hR := (orderedInputComponent_heq (normalizedOuterHom f) i).trans
    (normalizedOuter_flat_component_heq f (flattenedPositionsEquiv (orderedFamily X) i))
  exact hL.trans hR.symm

variable [MonoidalCategory C] [SymmetricCategory C]

/-- The actual ordered original input tensor map is the full original nested word tensor map. -/
theorem normalizedOuter_inputMap {X Y : FiniteFamily (FiniteFamily C)} (f : X ⟶ Y) :
    wordInputMap f = orderedInputMap (normalizedOuterHom f) := by
  unfold wordInputMap orderedInputMap
  exact mapEquiv_congr (normalizedOuter_inputEquiv f) _ _ (normalizedOuter_inputComponents f)

set_option backward.isDefEq.respectTransparency false in
/-- Original outer normalization retains the actual tensor map of every original inner morphism. -/
theorem normalizedOuter_outputMap {X Y : FiniteFamily (FiniteFamily C)} (f : X ⟶ Y) :
    finiteMap ((FiniteFamily.map (finiteTensorFunctor (C := C))).map f) =
      orderedOutputMap (normalizedOuterHom f) := by
  unfold finiteMap orderedOutputMap normalizedOuterHom
  apply mapEquiv_congr rfl
  intro i
  have hL := enumeratedMap_heq ((FiniteFamily.map (finiteTensorFunctor (C := C))).map f) i
  have hR : HEq (finiteMap (enumeratedMap f i)) (finiteMap (f.hom (enumeration X i))) := by
    unfold enumeratedMap
    rw [finiteMap_comp, finiteMap_eqToHom]
    exact comp_eqToHom_heq _ _
  exact hL.trans hR.symm

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FiniteTensorOuterNormalization

/- Source proof segment: FiniteTensorFlattenNaturality -/
section source_FiniteTensorFlattenNaturality
/-!
# Full original finite tensor flattening naturality

Every original outer finite bijection, inner finite bijection and
component morphism commutes with the constructed tensor flattening.
The original component isomorphisms give the full natural isomorphism
between flattened tensoring and tensoring the original inner tensors.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- All original nested finite-family morphisms commute with the original outer block tensor
comparison. -/
theorem finiteFamilyBlocks_naturality {X Y : FiniteFamily (FiniteFamily C)} (f : X ⟶ Y) :
    wordInputMap f ≫ (finiteFamilyBlocksIso Y).hom =
      (finiteFamilyBlocksIso X).hom ≫ finiteMap ((FiniteFamily.map (finiteTensorFunctor (C
        := C))).map f) := by
  have hL := congrArg (fun a => a ≫ (finiteFamilyBlocksIso Y).hom) (normalizedOuter_inputMap f)
  have hR := congrArg (fun a => (finiteFamilyBlocksIso X).hom ≫ a) (normalizedOuter_outputMap f)
  exact hL.trans ((blocksOfFamilyIso_naturality (normalizedOuterHom f)).trans hR.symm)

set_option backward.isDefEq.respectTransparency false in
/-- The full constructed finite tensor flattening is natural in every original outer/inner
bijection and component
  morphism. -/
theorem finiteFlatten_naturality {X Y : FiniteFamily (FiniteFamily C)} (f : X ⟶ Y) :
    finiteMap ((FiniteFamily.flatten (C := C)).map f) ≫ (finiteFlattenIso Y).hom =
      (finiteFlattenIso X).hom ≫ finiteMap ((FiniteFamily.map (finiteTensorFunctor (C :=
        C))).map f) := by
  rw [finiteFlattenIso_hom, finiteFlattenIso_hom]
  unfold finiteFlattenHom
  rw [← Category.assoc, flattenToWord_naturality, Category.assoc,
    finiteFamilyBlocks_naturality, Category.assoc]

/-- The actual source-produced finite tensor flattening natural isomorphism. -/
noncomputable def finiteFlattenNatIso :
    FiniteFamily.flatten (C := C) ⋙ finiteTensorFunctor ≅ FiniteFamily.map
      finiteTensorFunctor ⋙ finiteTensorFunctor :=
  NatIso.ofComponents finiteFlattenIso (by
    intro X Y f
    exact finiteFlatten_naturality f)

/-- The full flattening natural isomorphism retains its original actual component map. -/
theorem finiteFlattenNatIso_hom_app (X : FiniteFamily (FiniteFamily C)) :
    (finiteFlattenNatIso (C := C)).hom.app X = (finiteFlattenIso X).hom := rfl

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FiniteTensorFlattenNaturality

/- Source proof segment: OrderedBlockUnitCoherence -/
section source_OrderedBlockUnitCoherence
/-!
# Original unit coherence of ordered tensor blocks

A single original input block is split by the original left unitor
inverse. Composing with the original outer singleton unitor retains
the actual finite input-count and object equality.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

private theorem tensorIdentities_transport_heq {U A B V : C}
    (d : U ⟶ A ⊗ B) (h : A ⊗ B = V) :
    HEq (d ≫ (𝟙 A ⊗ₘ 𝟙 B) ≫ eqToHom h) d := by
  rw [id_tensorHom_id, Category.id_comp]
  exact comp_eqToHom_heq _ _

/-- The original empty-first append map is the original left unitor inverse, with its exact
source transport. -/
theorem appendIso_empty_left_heq {n : ℕ} (X : Fin 0 → C) (Y : Fin n → C) :
    HEq (appendIso X Y).hom (λ_ (obj Y)).inv :=
  (prefixHistoryAppend_hom_heq X Y).symm.trans (prefixHistoryAppend_empty_left_heq X Y)

omit [Category.{v} C] [MonoidalCategory C] in
/-- The actual one-block word contains the original unique block and every original inner input. -/
theorem blocksOfFamily_one (X : Fin 1 → FiniteFamily C) :
    blocksOfFamily X = Blocks.snoc Blocks.nil (orderedFamily (X 0)) := rfl

/-- The original one-block word has the actual original inner tensor carrier. -/
theorem blocksOfFamily_one_obj_eq (X : Fin 1 → FiniteFamily C) :
    obj (blocksOfFamily X).inputs = finiteObj (X 0) :=
  appendLeftUnit_obj_eq (Fin.elim0 : Fin 0 → C) (orderedFamily (X 0))

set_option backward.isDefEq.respectTransparency false in
/-- The original one-block flattening is the original left unitor inverse, with the entire
inner block retained. -/
theorem blocksOfFamilyIso_one_heq (X : Fin 1 → FiniteFamily C) :
    HEq (blocksOfFamilyIso X).hom (λ_ (finiteObj (X 0))).inv := by
  have hFold : HEq (Blocks.flattenIso (blocksOfFamily X)).hom
      (appendIso (Fin.elim0 : Fin 0 → C) (orderedFamily (X 0))).hom := by
    change HEq (Blocks.flattenIso (Blocks.snoc Blocks.nil (orderedFamily (X 0)))).hom _
    rw [Blocks.flattenIso_snoc_hom, Blocks.flattenIso_nil]
    change HEq
      ((appendIso (Fin.elim0 : Fin 0 → C) (orderedFamily (X 0))).hom ≫
        (𝟙 (𝟙_ C) ⊗ₘ 𝟙 (finiteObj (X 0))) ≫
        eqToHom (show 𝟙_ C ⊗ finiteObj (X 0) =
            obj (Blocks.blockTensors (Blocks.snoc Blocks.nil (orderedFamily (X 0)))) from
          (Blocks.obj_blockTensors_snoc Blocks.nil (orderedFamily (X 0))).symm))
      (appendIso (Fin.elim0 : Fin 0 → C) (orderedFamily (X 0))).hom
    exact tensorIdentities_transport_heq
      (A := 𝟙_ C) (B := finiteObj (X 0))
      (appendIso (Fin.elim0 : Fin 0 → C) (orderedFamily (X 0))).hom _
  unfold blocksOfFamilyIso
  rw [Iso.trans_hom, eqToIso.hom]
  exact (comp_eqToHom_heq _ _).trans (hFold.trans (appendIso_empty_left_heq _ _))

set_option backward.isDefEq.respectTransparency false in
/-- Splitting an original unique block then applying its original singleton unitor
is the original carrier equality map.
-/
theorem blocksOfFamilyIso_one_unit (X : Fin 1 → FiniteFamily C) :
    (blocksOfFamilyIso X).hom ≫ (λ_ (finiteObj (X 0))).hom =
      eqToHom (blocksOfFamily_one_obj_eq X) := by
  have h : (blocksOfFamilyIso X).hom =
      eqToHom (blocksOfFamily_one_obj_eq X) ≫ (λ_ (finiteObj (X 0))).inv := by
    have ht := (conj_eqToHom_iff_heq (blocksOfFamilyIso X).hom
      (λ_ (finiteObj (X 0))).inv (blocksOfFamily_one_obj_eq X) rfl).mpr
        (blocksOfFamilyIso_one_heq X)
    simpa only [eqToHom_refl, Category.comp_id] using ht
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedBlockUnitCoherence

/- Source proof segment: FiniteTensorSingleton -/
section source_FiniteTensorSingleton
/-!
# The original natural singleton comparison of the binary finite tensor

The singleton carrier comparison is the original left unitor after
the original finite input count is identified with one. Its full
naturality uses the actual produced fixed-index tensor map.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

attribute [local instance] FintypeCat.fintype

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The actual original singleton tensor comparison is natural in every original morphism. -/
theorem finiteSingletonIso_naturality {X Y : C} (f : X ⟶ Y) :
    finiteTensorFunctor.map ((FiniteFamily.singleton (C := C)).map f) ≫
        (finiteSingletonIso Y).hom =
      (finiteSingletonIso X).hom ≫ f := by
  have hmap : (FiniteFamily.singleton (C := C)).map f =
      fixedIndexHom (FintypeCat.of PUnit.{1}) (fun _ => f) := rfl
  rw [hmap, finiteTensorFunctor_map_fixedIndex]
  unfold finiteSingletonIso
  have h : arity ((FiniteFamily.singleton (C := C)).obj X) = 1 := by
    exact @Fintype.card_unique PUnit.{1} (inferInstanceAs (Unique PUnit.{1}))
      (@FintypeCat.fintype (FintypeCat.of PUnit.{1}))
  let F : Fin (arity ((FiniteFamily.singleton (C := C)).obj X)) → C := fun _ => X
  let G : Fin (arity ((FiniteFamily.singleton (C := C)).obj X)) → C := fun _ => Y
  have aux {n : ℕ} (hn : n = 1) (F G : Fin n → C)
      (hF : ∀ i, F i = X) (hG : ∀ i, G i = Y)
      (g : ∀ i, F i ⟶ G i) (hg : ∀ i, HEq (g i) f) :
      map g ≫ (congrIso hn G (fun _ : Fin 1 => Y) (fun i => hG i) ≪≫
        singletonIso (fun _ : Fin 1 => Y)).hom =
      (congrIso hn F (fun _ : Fin 1 => X) (fun i => hF i) ≪≫
        singletonIso (fun _ : Fin 1 => X)).hom ≫ f := by
    subst n
    have hFeq : F = fun _ => X := funext hF
    have hGeq : G = fun _ => Y := funext hG
    subst F
    subst G
    have hgeq : g = fun _ => f := by
      funext i
      exact eq_of_heq (hg i)
    subst g
    simp only [congrIso, eqToIso_refl, Iso.refl_trans]
    exact singletonIso_naturality (fun _ => f)
  exact aux h F G (fun _ => rfl) (fun _ => rfl) (fun _ => f) (fun _ => HEq.rfl)

/-- The actual original natural singleton comparison of the produced finite tensor functor. -/
noncomputable def finiteSingletonNatIso :
    FiniteFamily.singleton (C := C) ⋙ finiteTensorFunctor ≅ 𝟭 C :=
  NatIso.ofComponents finiteSingletonIso (by
    intro X Y f
    exact finiteSingletonIso_naturality f)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FiniteTensorSingleton

/- Source proof segment: UniqueOuterBlock -/
section source_UniqueOuterBlock
/-!
# Original unique outer block of the constructed finite tensor

The original finite outer singleton has one input. Its complete
ordered block word retains every original inner input, including an
empty inner family. The maps use the original left unitor.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

attribute [local instance] FintypeCat.fintype

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

omit [Category C] [MonoidalCategory C] in
/-- An actual unique outer block retains the complete original inner input count. -/
theorem uniqueOuterBlock_count {n : ℕ} (hn : n = 1)
    (F : Fin n → FiniteFamily C) (X : FiniteFamily C) (hF : ∀ i, F i = X) :
    (blocksOfFamily F).totalArity = arity X := by
  cases hn
  have h : F = fun _ => X := funext hF
  cases h
  exact Nat.zero_add _

omit [Category C] [MonoidalCategory C] in
/-- An actual unique outer block retains every original inner input at its original ordered slot. -/
theorem uniqueOuterBlock_objects {n : ℕ} (hn : n = 1)
    (F : Fin n → FiniteFamily C) (X : FiniteFamily C) (hF : ∀ i, F i = X)
    (j : Fin (blocksOfFamily F).totalArity) :
    (blocksOfFamily F).inputs j =
      orderedFamily X (Fin.cast (uniqueOuterBlock_count hn F X hF) j) := by
  cases hn
  have h : F = fun _ => X := funext hF
  cases h
  exact congrFun (Fin.append_left_nil (Fin.elim0 : Fin 0 → C) (orderedFamily X) rfl) j

/-- The complete original unique-block word has the original inner tensor carrier. -/
theorem uniqueOuterBlock_obj_eq {n : ℕ} (hn : n = 1)
    (F : Fin n → FiniteFamily C) (X : FiniteFamily C) (hF : ∀ i, F i = X) :
    obj (blocksOfFamily F).inputs = finiteObj X :=
  obj_congr (uniqueOuterBlock_count hn F X hF) _ _ (uniqueOuterBlock_objects hn F X hF)

set_option backward.isDefEq.respectTransparency false in
/-- The actual one-block flattening and original outer singleton collapse form the unit map. -/
theorem uniqueOuterBlock_unit {n : ℕ} (hn : n = 1)
    (F : Fin n → FiniteFamily C) (X : FiniteFamily C) (hF : ∀ i, F i = X) :
    (blocksOfFamilyIso F).hom ≫
        (congrIso hn (fun i => finiteObj (F i)) (fun _ : Fin 1 => finiteObj X)
          (fun i => congrArg finiteObj (hF i)) ≪≫
            singletonIso (fun _ : Fin 1 => finiteObj X)).hom =
      eqToHom (uniqueOuterBlock_obj_eq hn F X hF) := by
  cases hn
  have h : F = fun _ => X := funext hF
  cases h
  simp only [congrIso, eqToIso_refl, Iso.refl_trans]
  exact blocksOfFamilyIso_one_unit (fun _ => X)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_UniqueOuterBlock

/- Source proof segment: UniqueOuterPositions -/
section source_UniqueOuterPositions
/-!
# Original input geometry of the singleton-flatten unit

The original dependent sum of one outer input and all inner inputs
is collapsed by its actual original sigma/PUnit map. The ordered
word keeps the original inner enumeration and count transport.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

variable {C : Type u} [Category.{v} C]

attribute [local instance] FintypeCat.fintype

/-- The original finite outer singleton has exactly one original outer input. -/
theorem singletonOuter_arity (X : FiniteFamily C) :
    arity ((FiniteFamily.singleton (C := FiniteFamily C)).obj X) = 1 := by
  unfold arity FiniteFamily.singleton
  exact @Fintype.card_unique PUnit.{1} (inferInstanceAs (Unique PUnit.{1}))
    (@FintypeCat.fintype (FintypeCat.of PUnit.{1}))

omit [Category C] in
set_option backward.isDefEq.respectTransparency false in
/-- Every original inner position is retained in the actual one-block ordered position map. -/
theorem uniqueOuterBlock_position {n : ℕ} (hn : n = 1) (X : FiniteFamily C)
    (j : Fin (blocksOfFamily (fun _ : Fin n => X)).totalArity) :
    flattenedPositionsEquiv (fun _ : Fin n => X) j =
      ⟨Fin.cast hn.symm (0 : Fin 1),
        enumeration X (Fin.cast (uniqueOuterBlock_count hn (fun _ => X) X (fun _ => rfl)) j)⟩ := by
  cases hn
  refine Fin.addCases (fun i => i.elim0) (fun i => ?_) j
  change flattenedPositionsEquiv (fun _ : Fin 1 => X) (Fin.natAdd 0 i) = _
  dsimp only [flattenedPositionsEquiv, blocksOfFamily, Blocks.positionEquiv,
    blockPositionsEquiv, Equiv.trans_apply, Blocks.position, Blocks.totalArity]
  rw [finSumFinEquiv_symm_apply_natAdd]
  simp only [Equiv.sumCongr_apply]
  dsimp only [positionsSnocEquiv, Equiv.refl_apply, Blocks.totalArity]
  have hi : Fin.cast (uniqueOuterBlock_count rfl (fun _ : Fin 1 => X) X (fun _ => rfl))
      (Fin.natAdd 0 i) = i := by
    apply Fin.ext
    change (Fin.natAdd 0 i).val = i.val
    exact Nat.zero_add _
  rw [hi]
  rfl

/-- The complete original singleton outer word retains its original inner input count. -/
theorem singletonOuter_word_count (X : FiniteFamily C) :
    (blocksOfFiniteFamily ((FiniteFamily.singleton (C := FiniteFamily C)).obj X)).totalArity =
      arity X :=
  uniqueOuterBlock_count (singletonOuter_arity X) _ X (fun _ => rfl)

/-- The actual original sigma/PUnit left collapse agrees with the original ordered inner slots. -/
theorem singletonOuter_position_collapse (X : FiniteFamily C)
    (j : Fin (blocksOfFiniteFamily
      ((FiniteFamily.singleton (C := FiniteFamily C)).obj X)).totalArity) :
    (FiniteFamily.singletonFlattenIso.hom.app X).equiv
        (nestedPositionsEquiv ((FiniteFamily.singleton (C := FiniteFamily C)).obj X) j) =
      enumeration X (Fin.cast (singletonOuter_word_count X) j) := by
  have h := uniqueOuterBlock_position (singletonOuter_arity X) X j
  change (flattenedPositionsEquiv
    (fun _ : Fin (arity ((FiniteFamily.singleton (C := FiniteFamily C)).obj X)) => X) j).2 = _
  exact congrArg Sigma.snd h

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_UniqueOuterPositions

/- Source proof segment: SingletonOuterWord -/
section source_SingletonOuterWord
/-!
# Actual singleton outer-word collapse

The original outer PUnit enumeration is retained while the complete
one-block flattening is followed by the actual finite singleton
comparison. No unit or flattening outcome is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [SymmetricCategory C] in
/-- The actual one-block word has the complete original inner tensor carrier. -/
theorem singletonOuter_word_obj_eq (X : FiniteFamily C) :
    obj (blocksOfFiniteFamily ((FiniteFamily.singleton (C := FiniteFamily C)).obj X)).inputs =
      finiteObj X :=
  uniqueOuterBlock_obj_eq (singletonOuter_arity X) _ X (fun _ => rfl)

set_option backward.isDefEq.respectTransparency false in
/-- Actual outer singleton flattening followed by singleton collapse
retains the entire inner block. -/
theorem singletonOuter_word_unit (X : FiniteFamily C) :
    (finiteFamilyBlocksIso ((FiniteFamily.singleton (C := FiniteFamily C)).obj X)).hom ≫
        (finiteSingletonNatIso (C := C)).hom.app (finiteObj X) =
      eqToHom (singletonOuter_word_obj_eq X) := by
  have h := uniqueOuterBlock_unit (singletonOuter_arity X)
    (fun _ : Fin (arity ((FiniteFamily.singleton (C := FiniteFamily C)).obj X)) => X)
    X (fun _ => rfl)
  change (blocksOfFamilyIso
    (fun _ : Fin (arity ((FiniteFamily.singleton (C := FiniteFamily C)).obj X)) => X)).hom ≫
      (finiteSingletonIso (finiteObj X)).hom = _
  unfold finiteSingletonIso
  exact h

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_SingletonOuterWord

/- Source proof segment: FiniteInputEqualityMap -/
section source_FiniteInputEqualityMap
/-!
# Actual finite tensor maps of original input equality components

The complete original input bijection and equality components are
retained before the sigma/PUnit unit maps are selected.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The actual finite input map retains its original normalized component equalities. -/
theorem finiteMap_equality_components {X Y : FiniteFamily C} (f : X ⟶ Y)
    (h : ∀ i, X.obj i = Y.obj (f.equiv i))
    (hf : ∀ i, HEq (f.hom i) (eqToHom (h i))) :
    finiteMap f = mapEquiv (enumeratedEquiv f)
      (fun i => eqToHom ((h (enumeration X i)).trans
        (orderedFamily_enumeratedEquiv f i).symm)) := by
  apply mapEquiv_congr rfl
  intro i
  exact (enumeratedMap_heq f i).trans ((hf (enumeration X i)).trans
    ((eqToHom_heq_id_dom _ _ _).trans (eqToHom_heq_id_dom _ _ _).symm))

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- Two original consecutive component equality maps retain their common original source. -/
theorem inputEquality_hom_chain {A B D E : C} (h : A = B) (k : B = D) (l : A = E) :
    HEq (eqToHom h ≫ eqToHom k) (eqToHom l) := by
  rw [eqToHom_trans]
  exact (eqToHom_heq_id_dom _ _ _).trans (eqToHom_heq_id_dom _ _ _).symm

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FiniteInputEqualityMap

/- Source proof segment: SingletonOuterInputGeometry -/
section source_SingletonOuterInputGeometry
/-!
# Exact original singleton-flatten input map

The original sigma/PUnit input collapse is identified with the
constructed flatten-word bijection followed by its original complete
inner count transport, including an empty inner family.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The original sigma/PUnit left-collapse keeps each original input object. -/
theorem singletonFlatten_objects (X : FiniteFamily C)
    (i : ((FiniteFamily.singletonFlatten (C := C)).obj X).index) :
    ((FiniteFamily.singletonFlatten (C := C)).obj X).obj i =
      X.obj ((FiniteFamily.singletonFlattenIso.hom.app X).equiv i) := rfl

omit [MonoidalCategory C] [SymmetricCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- The actual normalized left-unit input map has the original word and count factors. -/
theorem singletonFlatten_enumerated_equiv (X : FiniteFamily C) :
    enumeratedEquiv (FiniteFamily.singletonFlattenIso.hom.app X) =
      (flattenWordEquiv ((FiniteFamily.singleton (C := FiniteFamily C)).obj X)).trans
        (finCongr (singletonOuter_word_count X)) := by
  apply Equiv.ext
  intro i
  let O := (FiniteFamily.singleton (C := FiniteFamily C)).obj X
  let E := enumeration (flattenedOriginalFamily O)
  have h := singletonOuter_position_collapse X ((nestedPositionsEquiv O).symm (E i))
  change (FiniteFamily.singletonFlattenIso.hom.app X).equiv
    ((nestedPositionsEquiv O) ((nestedPositionsEquiv O).symm (E i))) = _ at h
  rw [Equiv.apply_symm_apply] at h
  change (enumeration X).symm
    ((FiniteFamily.singletonFlattenIso.hom.app X).equiv (E i)) =
      Fin.cast (singletonOuter_word_count X) ((nestedPositionsEquiv O).symm (E i))
  rw [h, Equiv.symm_apply_apply]

/-- The original singleton-flatten map keeps exactly its original equality components. -/
theorem singletonFlatten_finiteMap (X : FiniteFamily C) :
    finiteMap (FiniteFamily.singletonFlattenIso.hom.app X) =
      mapEquiv (enumeratedEquiv (FiniteFamily.singletonFlattenIso.hom.app X))
        (fun i => eqToHom ((singletonFlatten_objects X (enumeration _ i)).trans
          (orderedFamily_enumeratedEquiv (FiniteFamily.singletonFlattenIso.hom.app X) i).symm)) :=
  finiteMap_equality_components _ (singletonFlatten_objects X) (fun _ => HEq.rfl)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_SingletonOuterInputGeometry

/- Source proof segment: SingletonFlattenUnit -/
section source_SingletonFlattenUnit
/-!
# Original singleton-flatten unit map of the constructed finite tensor

The actual original sigma/PUnit collapse is the constructed flatten
comparison at the original outer singleton followed by its actual
finite singleton collapse. All original inputs are retained.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- Every original unique-block word input retains its actual original inner object. -/
theorem singletonOuter_word_objects (X : FiniteFamily C)
    (j : Fin (blocksOfFiniteFamily
      ((FiniteFamily.singleton (C := FiniteFamily C)).obj X)).totalArity) :
    (blocksOfFiniteFamily ((FiniteFamily.singleton (C := FiniteFamily C)).obj X)).inputs j =
      orderedFamily X (Fin.cast (singletonOuter_word_count X) j) :=
  uniqueOuterBlock_objects (singletonOuter_arity X) _ X (fun _ => rfl) j

/-- The actual original unique-block carrier transport is its original finite input map. -/
theorem singletonOuter_word_transport (X : FiniteFamily C) :
    eqToHom (singletonOuter_word_obj_eq X) =
      mapEquiv (finCongr (singletonOuter_word_count X))
        (fun i => eqToHom (singletonOuter_word_objects X i)) := by
  have h := isoEquiv_finCongr (singletonOuter_word_count X)
    (blocksOfFiniteFamily ((FiniteFamily.singleton (C := FiniteFamily C)).obj X)).inputs
    (orderedFamily X) (singletonOuter_word_objects X)
  have hh := congrArg Iso.hom h
  rw [isoEquiv_hom] at hh
  exact hh.symm

set_option backward.isDefEq.respectTransparency false in
/-- The actual original singleton-flatten finite map has its complete constructed unit composite. -/
theorem finiteSingletonFlatten_unit (X : FiniteFamily C) :
    finiteMap (FiniteFamily.singletonFlattenIso.hom.app X) =
      (finiteFlattenIso ((FiniteFamily.singleton (C := FiniteFamily C)).obj X)).hom ≫
        (finiteSingletonNatIso (C := C)).hom.app (finiteObj X) := by
  let O := (FiniteFamily.singleton (C := FiniteFamily C)).obj X
  rw [finiteFlattenIso, Iso.trans_hom, Category.assoc, singletonOuter_word_unit,
    flattenToWordIso_hom, singletonOuter_word_transport]
  change finiteMap (FiniteFamily.singletonFlattenIso.hom.app X) =
    mapEquiv (flattenWordEquiv O) (fun i => eqToHom (flattenWord_objects O i)) ≫
      mapEquiv (finCongr (singletonOuter_word_count X))
        (fun i => eqToHom (singletonOuter_word_objects X i))
  rw [mapEquiv_comp, singletonFlatten_finiteMap]
  apply mapEquiv_congr (singletonFlatten_enumerated_equiv X)
  intro i
  exact (inputEquality_hom_chain
    (flattenWord_objects O i)
    (singletonOuter_word_objects X (flattenWordEquiv O i))
    ((singletonFlatten_objects X (enumeration _ i)).trans
      (orderedFamily_enumeratedEquiv (FiniteFamily.singletonFlattenIso.hom.app X) i).symm)).symm

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_SingletonFlattenUnit

/- Source proof segment: UnaryBlockPositions -/
section source_UnaryBlockPositions
/-!
# Original outer positions of ordered arity-one input blocks

The original input bijection projects to the original outer slot after
the exact total-count transport. The proof uses indices only.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

variable {C : Type u}

/-- Original arity-one blocks contribute exactly one input per original outer slot. -/
theorem unaryBlocks_totalArity : ∀ {n : ℕ} (F : Fin n → FiniteFamily C)
    (_h : ∀ i, arity (F i) = 1), (blocksOfFamily F).totalArity = n
  | 0, _, _ => rfl
  | n + 1, F, h => by
      change (blocksOfFamily (Fin.init F)).totalArity + arity (F (Fin.last n)) = n + 1
      rw [h, unaryBlocks_totalArity (Fin.init F) (fun i => h i.castSucc)]

set_option backward.isDefEq.respectTransparency false in
/-- The original flattened position map retains each initial block's outer position. -/
theorem flattenedPositions_first_left {n : ℕ} (F : Fin (n + 1) → FiniteFamily C)
    (j : Fin (blocksOfFamily (Fin.init F)).totalArity) :
    (flattenedPositionsEquiv F (Fin.castAdd (arity (F (Fin.last n))) j)).1 =
      (flattenedPositionsEquiv (Fin.init F) j).1.castSucc := by
  change (positionsSnocEquiv F
    ((Equiv.sumCongr (blockPositionsEquiv (Fin.init F)) (enumeration (F (Fin.last n))))
      ((Equiv.sumCongr (blocksOfFamily (Fin.init F)).positionEquiv
        (Equiv.refl (Fin (arity (F (Fin.last n))))))
        (finSumFinEquiv.symm (Fin.castAdd (arity (F (Fin.last n))) j))))).1 = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The original flattened position map retains the final block's original outer position. -/
theorem flattenedPositions_first_right {n : ℕ} (F : Fin (n + 1) → FiniteFamily C)
    (j : Fin (arity (F (Fin.last n)))) :
    (flattenedPositionsEquiv F
      (Fin.natAdd (blocksOfFamily (Fin.init F)).totalArity j)).1 = Fin.last n := by
  change (positionsSnocEquiv F
    ((Equiv.sumCongr (blockPositionsEquiv (Fin.init F)) (enumeration (F (Fin.last n))))
      ((Equiv.sumCongr (blocksOfFamily (Fin.init F)).positionEquiv
        (Equiv.refl (Fin (arity (F (Fin.last n))))))
        (finSumFinEquiv.symm (Fin.natAdd (blocksOfFamily (Fin.init F)).totalArity j))))).1 = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

/-- The original first-coordinate position map is the actual initial/final input split. -/
theorem flattenedPositions_first_cases {n : ℕ} (F : Fin (n + 1) → FiniteFamily C) :
    (fun j => (flattenedPositionsEquiv F j).1) =
      Fin.addCases (fun j => (flattenedPositionsEquiv (Fin.init F) j).1.castSucc)
        (fun _ => Fin.last n) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Fin.addCases_left]
    exact flattenedPositions_first_left F i
  · rw [Fin.addCases_right]
    exact flattenedPositions_first_right F i

/-- The generic arity-one index split is exactly the original successor index transport. -/
theorem unaryAppendIndex_frame {a n k : ℕ} (ha : a = n) (hk : k = 1)
    (h : a + k = n + 1) (j : Fin (a + k)) :
    Fin.addCases (fun i => (Fin.cast ha i).castSucc) (fun _ : Fin k => Fin.last n) j =
      Fin.cast h j := by
  subst a
  subst k
  change Fin.addCases (fun i : Fin n => i.castSucc) (fun _ : Fin 1 => Fin.last n) j = j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Fin.addCases_left]
    rfl
  · rw [Fin.addCases_right]
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl

/-- The actual flattened input bijection of arity-one blocks projects to the original outer slot. -/
theorem unaryBlocks_outerPosition : ∀ {n : ℕ} (F : Fin n → FiniteFamily C)
    (h : ∀ i, arity (F i) = 1)
    (j : Fin (blocksOfFamily F).totalArity),
    (flattenedPositionsEquiv F j).1 = Fin.cast (unaryBlocks_totalArity F h) j
  | 0, _, _, j => Fin.elim0 j
  | n + 1, F, h, j => by
      have hc := congrArg (fun f => f j) (flattenedPositions_first_cases F)
      have hp : (fun i => (flattenedPositionsEquiv (Fin.init F) i).1.castSucc) =
          (fun i => (Fin.cast
            (unaryBlocks_totalArity (Fin.init F) (fun i => h i.castSucc)) i).castSucc) := by
        funext i
        exact congrArg Fin.castSucc
          (unaryBlocks_outerPosition (Fin.init F) (fun i => h i.castSucc) i)
      rw [hp] at hc
      exact hc.trans (unaryAppendIndex_frame
        (unaryBlocks_totalArity (Fin.init F) (fun i => h i.castSucc))
        (h (Fin.last n)) (unaryBlocks_totalArity F h) j)

/-- Original object equality in every unary block gives the actual flattened object readback. -/
theorem unaryBlocks_inputs {n : ℕ} (F : Fin n → FiniteFamily C) (X : Fin n → C)
    (h : ∀ i, arity (F i) = 1) (hX : ∀ i j, orderedFamily (F i) j = X i)
    (j : Fin (blocksOfFamily F).totalArity) :
    (blocksOfFamily F).inputs j = X (Fin.cast (unaryBlocks_totalArity F h) j) := by
  let p := flattenedPositionsEquiv F j
  have hp : (F p.1).obj p.2 = X p.1 := by
    have ht := hX p.1 ((enumeration (F p.1)).symm p.2)
    simpa only [orderedFamily, Function.comp_apply, Equiv.apply_symm_apply] using ht
  exact (flattenedPositions_objects F j).trans
    (hp.trans (congrArg X (unaryBlocks_outerPosition F h j)))

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_UnaryBlockPositions

/- Source proof segment: AllSingletonShape -/
section source_AllSingletonShape
/-!
# Actual arity and input readbacks of all singleton blocks

Every singleton contributes the original PUnit cardinality one and
exactly its original object to the ordered block word.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C]

/-- The actual ordered family of singleton blocks of an input word. -/
def singletonFamilies {n : ℕ} (X : Fin n → C) : Fin n → FiniteFamily C :=
  fun i => (FiniteFamily.singleton (C := C)).obj (X i)

/-- The original singleton PUnit input index has its original cardinality one. -/
theorem singleton_arity (A : C) : arity ((FiniteFamily.singleton (C := C)).obj A) = 1 := by
  unfold arity FiniteFamily.singleton
  exact @Fintype.card_unique PUnit.{1} (inferInstanceAs (Unique PUnit.{1}))
    (@FintypeCat.fintype (FintypeCat.of PUnit.{1}))

/-- Every enumerated input of an actual singleton block is its original object. -/
theorem singleton_orderedFamily (A : C)
    (j : Fin (arity ((FiniteFamily.singleton (C := C)).obj A))) :
    orderedFamily ((FiniteFamily.singleton (C := C)).obj A) j = A := rfl

/-- An ordered word of actual singleton blocks has exactly its original outer input count. -/
theorem singletonBlocks_totalArity : ∀ {n : ℕ} (X : Fin n → C),
    (blocksOfFamily (singletonFamilies X)).totalArity = n
  | _, X => unaryBlocks_totalArity (singletonFamilies X) (fun i => singleton_arity (X i))

/-- The actual original outer position of every flattened singleton input is retained. -/
theorem singletonBlocks_outerPosition {n : ℕ} (X : Fin n → C)
    (j : Fin (blocksOfFamily (singletonFamilies X)).totalArity) :
    (flattenedPositionsEquiv (singletonFamilies X) j).1 =
      Fin.cast (singletonBlocks_totalArity X) j :=
  unaryBlocks_outerPosition (singletonFamilies X) (fun i => singleton_arity (X i)) j

set_option backward.isDefEq.respectTransparency false in
/-- Every actual flattened singleton input is its original ordered outer input. -/
theorem singletonBlocks_inputs : ∀ {n : ℕ} (X : Fin n → C)
    (j : Fin (blocksOfFamily (singletonFamilies X)).totalArity),
    (blocksOfFamily (singletonFamilies X)).inputs j =
      X (Fin.cast (singletonBlocks_totalArity X) j)
  | _, X, j => (flattenedPositions_objects (singletonFamilies X) j).trans
      (congrArg X (singletonBlocks_outerPosition X j))

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_AllSingletonShape

/- Source proof segment: MappedSingletonInputGeometry -/
section source_MappedSingletonInputGeometry
/-!
# Original map-singleton-flatten input geometry

The complete original sigma/PUnit right collapse agrees with the
actual ordered singleton word and its original outer input count.
Every original input is retained, including the empty outer family.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The actual ordered outer family of mapped original singletons is its original singleton word. -/
theorem mappedSingleton_blocks (X : FiniteFamily C) :
    blocksOfFiniteFamily ((FiniteFamily.map (FiniteFamily.singleton (C := C))).obj X) =
      blocksOfFamily (singletonFamilies (orderedFamily X)) := rfl

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The complete original mapped-singleton word retains its original finite outer input count. -/
theorem mappedSingleton_word_count (X : FiniteFamily C) :
    (blocksOfFiniteFamily ((FiniteFamily.map (FiniteFamily.singleton (C := C))).obj X)).totalArity =
      arity X :=
  singletonBlocks_totalArity (orderedFamily X)

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The original sigma/PUnit right-collapse keeps each original input object. -/
theorem mapSingletonFlatten_objects (X : FiniteFamily C)
    (i : ((FiniteFamily.mapSingletonFlatten (C := C)).obj X).index) :
    ((FiniteFamily.mapSingletonFlatten (C := C)).obj X).obj i =
      X.obj ((FiniteFamily.mapSingletonFlattenIso.hom.app X).equiv i) := rfl

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The original sigma/PUnit right collapse retains the actual original outer position. -/
theorem mappedSingleton_position_collapse (X : FiniteFamily C)
    (j : Fin (blocksOfFiniteFamily
      ((FiniteFamily.map (FiniteFamily.singleton (C := C))).obj X)).totalArity) :
    (FiniteFamily.mapSingletonFlattenIso.hom.app X).equiv
        (nestedPositionsEquiv ((FiniteFamily.map (FiniteFamily.singleton (C := C))).obj X) j) =
      enumeration X (Fin.cast (mappedSingleton_word_count X) j) := by
  have h := singletonBlocks_outerPosition (orderedFamily X) j
  change enumeration X ((flattenedPositionsEquiv (singletonFamilies (orderedFamily X)) j).1) = _
  exact congrArg (enumeration X) h

omit [MonoidalCategory C] [SymmetricCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- The actual normalized right-unit input map has the original word and count factors. -/
theorem mapSingletonFlatten_enumerated_equiv (X : FiniteFamily C) :
    enumeratedEquiv (FiniteFamily.mapSingletonFlattenIso.hom.app X) =
      (flattenWordEquiv ((FiniteFamily.map (FiniteFamily.singleton (C := C))).obj X)).trans
        (finCongr (mappedSingleton_word_count X)) := by
  apply Equiv.ext
  intro i
  let O := (FiniteFamily.map (FiniteFamily.singleton (C := C))).obj X
  let E := enumeration (flattenedOriginalFamily O)
  have h := mappedSingleton_position_collapse X ((nestedPositionsEquiv O).symm (E i))
  change (FiniteFamily.mapSingletonFlattenIso.hom.app X).equiv
    ((nestedPositionsEquiv O) ((nestedPositionsEquiv O).symm (E i))) = _ at h
  rw [Equiv.apply_symm_apply] at h
  change (enumeration X).symm
    ((FiniteFamily.mapSingletonFlattenIso.hom.app X).equiv (E i)) =
      Fin.cast (mappedSingleton_word_count X) ((nestedPositionsEquiv O).symm (E i))
  rw [h, Equiv.symm_apply_apply]

/-- The original map-singleton-flatten tensor map retains its original equality components. -/
theorem mapSingletonFlatten_finiteMap (X : FiniteFamily C) :
    finiteMap (FiniteFamily.mapSingletonFlattenIso.hom.app X) =
      mapEquiv (enumeratedEquiv (FiniteFamily.mapSingletonFlattenIso.hom.app X))
        (fun i => eqToHom ((mapSingletonFlatten_objects X (enumeration _ i)).trans
          (orderedFamily_enumeratedEquiv
            (FiniteFamily.mapSingletonFlattenIso.hom.app X) i).symm)) :=
  finiteMap_equality_components _ (mapSingletonFlatten_objects X) (fun _ => HEq.rfl)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_MappedSingletonInputGeometry

/- Source proof segment: MappedSingletonCollapse -/
section source_MappedSingletonCollapse
/-!
# Actual finite tensor of the original singleton collapse components

The mapped natural singleton comparison keeps the complete original
finite input index and every actual singleton component map.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

attribute [local instance] FintypeCat.fintype

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- Mapping the original natural singleton collapse preserves its original finite input indices. -/
theorem mapSingletonCollapse_fixedIndex (X : FiniteFamily C) :
    (FiniteFamily.mapIso (finiteSingletonNatIso (C := C))).hom.app X =
      fixedIndexHom X.index (fun i => (finiteSingletonIso (X.obj i)).hom) := rfl

/-- The actual finite tensor of mapped singleton collapse is its original component tensor map. -/
theorem finiteMap_singletonCollapse (X : FiniteFamily C) :
    finiteMap ((FiniteFamily.mapIso (finiteSingletonNatIso (C := C))).hom.app X) =
      map (fun i : Fin (arity X) => (finiteSingletonIso (orderedFamily X i)).hom) := by
  rw [mapSingletonCollapse_fixedIndex]
  exact finiteTensorFunctor_map_fixedIndex X.index
    (fun i => (finiteSingletonIso (X.obj i)).hom)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_MappedSingletonCollapse

/- Source proof segment: MappedSingletonWord -/
section source_MappedSingletonWord
/-!
# Original tensor carrier and input map of mapped singleton words

The original ordered singleton inputs identify the actual complete
flattened word with the original outer tensor. The input map is the
original finite count/equality transport.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- Every original mapped-singleton word input retains its actual original outer object. -/
theorem mappedSingleton_word_objects (X : FiniteFamily C)
    (j : Fin (blocksOfFiniteFamily
      ((FiniteFamily.map (FiniteFamily.singleton (C := C))).obj X)).totalArity) :
    (blocksOfFiniteFamily ((FiniteFamily.map (FiniteFamily.singleton (C := C))).obj X)).inputs j =
      orderedFamily X (Fin.cast (mappedSingleton_word_count X) j) :=
  singletonBlocks_inputs (orderedFamily X) j

omit [SymmetricCategory C] in
/-- The actual complete original mapped-singleton word has the original outer tensor carrier. -/
theorem mappedSingleton_word_obj_eq (X : FiniteFamily C) :
    obj (blocksOfFiniteFamily ((FiniteFamily.map (FiniteFamily.singleton (C := C))).obj X)).inputs =
      finiteObj X :=
  obj_congr (mappedSingleton_word_count X) _ _ (mappedSingleton_word_objects X)

/-- The original mapped-singleton carrier equality is its actual original input tensor map. -/
theorem mappedSingleton_word_transport (X : FiniteFamily C) :
    eqToHom (mappedSingleton_word_obj_eq X) =
      mapEquiv (finCongr (mappedSingleton_word_count X))
        (fun j => eqToHom (mappedSingleton_word_objects X j)) := by
  have h := isoEquiv_finCongr (mappedSingleton_word_count X)
    (blocksOfFiniteFamily ((FiniteFamily.map (FiniteFamily.singleton (C := C))).obj X)).inputs
    (orderedFamily X) (mappedSingleton_word_objects X)
  have hh := congrArg Iso.hom h
  rw [isoEquiv_hom] at hh
  exact hh.symm

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_MappedSingletonWord

/- Source proof segment: UnaryAppendUnit -/
section source_UnaryAppendUnit
/-!
# Original append unit law for an arbitrary unary last block

The generic arity-one factory uses the original append maps, binary
triangle, and actual object equality transport.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The actual input carrier of an appended constant unary block. -/
theorem appendUnary_obj_eq {m : ℕ} (U : Fin m → C) (A : C) :
    obj (Fin.append U (fun _ : Fin 1 => A)) = obj U ⊗ A := by
  rw [append_step]
  change obj (Fin.append U (fun _ : Fin 0 => A)) ⊗ A = _
  rw [append_nil]

set_option backward.isDefEq.respectTransparency false in
/-- The original append map followed by its actual unary unitor is its carrier equality map. -/
theorem appendIso_unary_unit {m : ℕ} (U : Fin m → C) (A : C) :
    (appendIso U (fun _ : Fin 1 => A)).hom ≫
        (𝟙 (obj U) ⊗ₘ (λ_ A).hom) = eqToHom (appendUnary_obj_eq U A) := by
  rw [appendIso_succ_hom, appendIso_zero_hom]
  change (eqToHom (append_step U (fun _ : Fin 1 => A)) ≫
      ((eqToHom (congrArg obj (append_nil U (Fin.init (fun _ : Fin 1 => A)))) ≫
        (ρ_ (obj U)).inv) ⊗ₘ 𝟙 A) ≫ (α_ (obj U) (𝟙_ C) A).hom) ≫
      (𝟙 (obj U) ⊗ₘ (λ_ A).hom) = _
  rw [Category.assoc, Category.assoc, id_tensorHom, triangle]
  rw [tensorHom_id, comp_whiskerRight]
  simp only [Category.assoc]
  rw [← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight, Category.comp_id]
  rw [eqToHom_whiskerRight, eqToHom_trans]

/-- The generic arity-one comparison is formed from the original carrier
transport and original left unitor. -/
def unaryBlockIso {k : ℕ} (h : k = 1) (Y : Fin k → C) (A : C)
    (hY : ∀ j, Y j = A) : obj Y ≅ A :=
  congrIso h Y (fun _ : Fin 1 => A) hY ≪≫ λ_ A

set_option backward.isDefEq.respectTransparency false in
/-- Appending an arbitrary arity-one block and applying its constructed unary
comparison is heterogeneously the identity of the original successor carrier. -/
theorem appendIso_unary_unit_heq {m k : ℕ} (h : k = 1)
    (U : Fin m → C) (Y : Fin k → C) (A : C) (hY : ∀ j, Y j = A) :
    HEq ((appendIso U Y).hom ≫ (𝟙 (obj U) ⊗ₘ (unaryBlockIso h Y A hY).hom))
      (𝟙 (obj U ⊗ A)) := by
  subst k
  have hy : Y = (fun _ : Fin 1 => A) := funext hY
  subst Y
  dsimp only [unaryBlockIso, congrIso]
  simp only [Iso.trans_hom, eqToIso.hom,
    eqToHom_refl, Category.id_comp]
  exact (heq_of_eq (appendIso_unary_unit U A)).trans
    (eqToHom_heq_id_cod _ _ (appendUnary_obj_eq U A))

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_UnaryAppendUnit

/- Source proof segment: BlockFlattenStep -/
section source_BlockFlattenStep
/-!
# Original successor readback of finite block flattening

The original flatten maps are joined to their actual outer carrier
equality maps, retaining the original append and preceding flattening.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Tensoring actual morphisms respects full heterogeneous object and map equalities. -/
theorem unaryUnit_tensorHom_heq {A A' B B' P P' Q Q' : C}
    {f : A ⟶ B} {f' : A' ⟶ B'} {g : P ⟶ Q} {g' : P' ⟶ Q'}
    (ha : A = A') (hb : B = B') (hp : P = P') (hq : Q = Q')
    (hf : HEq f f') (hg : HEq g g') : HEq (f ⊗ₘ g) (f' ⊗ₘ g') := by
  subst A'
  subst B'
  subst P'
  subst Q'
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hg
  rfl

omit [MonoidalCategory C] in
/-- Original identities respect their actual object equality. -/
theorem unaryUnit_id_heq {A B : C} (h : A = B) : HEq (𝟙 A) (𝟙 B) := by
  subst B
  rfl

/-- The original finite-block carrier equality leaves the actual flatten map unchanged
in heterogeneous form. -/
theorem blocksOfFamilyIso_flatten_heq {n : ℕ} (F : Fin n → FiniteFamily C) :
    HEq (blocksOfFamilyIso F).hom (Blocks.flattenIso (blocksOfFamily F)).hom := by
  dsimp only [blocksOfFamilyIso]
  rw [Iso.trans_hom, eqToIso.hom]
  exact comp_eqToHom_heq _ _

/-- The original successor flattening retains its actual append and preceding flatten maps. -/
theorem flattenIso_snoc_core_heq (B : Blocks C) {k : ℕ} (Y : Fin k → C) :
    HEq (Blocks.flattenIso (Blocks.snoc B Y)).hom
      ((appendIso B.inputs Y).hom ≫ ((Blocks.flattenIso B).hom ⊗ₘ 𝟙 (obj Y))) := by
  rw [Blocks.flattenIso_snoc_hom]
  exact (heq_of_eq (Category.assoc _ _ _).symm).trans (comp_eqToHom_heq _ _)

set_option backward.isDefEq.respectTransparency false in
/-- Original finite-family successor flattening is its actual append and previous
finite-family flattening, with every original block retained. -/
theorem blocksOfFamilyIso_succ_heq {n : ℕ} (F : Fin (n + 1) → FiniteFamily C) :
    HEq (blocksOfFamilyIso F).hom
      ((appendIso (blocksOfFamily (Fin.init F)).inputs (orderedFamily (F (Fin.last n)))).hom ≫
        ((blocksOfFamilyIso (Fin.init F)).hom ⊗ₘ 𝟙 (finiteObj (F (Fin.last n))))) := by
  have ht := unaryUnit_tensorHom_heq rfl (blocksOfFamily_tensors (Fin.init F)) rfl rfl
    (blocksOfFamilyIso_flatten_heq (Fin.init F)).symm
    (HEq.rfl : HEq (𝟙 (finiteObj (F (Fin.last n)))) _)
  have hc := heq_comp rfl rfl
    (congrArg (fun A => A ⊗ finiteObj (F (Fin.last n)))
      (blocksOfFamily_tensors (Fin.init F)))
    (HEq.rfl : HEq
      (appendIso (blocksOfFamily (Fin.init F)).inputs
        (orderedFamily (F (Fin.last n)))).hom _) ht
  exact ((blocksOfFamilyIso_flatten_heq F).trans
    (flattenIso_snoc_core_heq (blocksOfFamily (Fin.init F))
      (orderedFamily (F (Fin.last n))))).trans hc

/-- The exact original finite-family successor flattening map. -/
theorem blocksOfFamilyIso_succ_hom {n : ℕ} (F : Fin (n + 1) → FiniteFamily C) :
    (blocksOfFamilyIso F).hom =
      (appendIso (blocksOfFamily (Fin.init F)).inputs (orderedFamily (F (Fin.last n)))).hom ≫
        ((blocksOfFamilyIso (Fin.init F)).hom ⊗ₘ 𝟙 (finiteObj (F (Fin.last n)))) :=
  eq_of_heq (blocksOfFamilyIso_succ_heq F)

/-- The actual input-count and object transports identify the carrier of unary blocks. -/
theorem unaryBlocks_obj_eq {n : ℕ} (F : Fin n → FiniteFamily C) (X : Fin n → C)
    (h : ∀ i, arity (F i) = 1) (hX : ∀ i j, orderedFamily (F i) j = X i) :
    obj (blocksOfFamily F).inputs = obj X :=
  obj_congr (unaryBlocks_totalArity F h) (blocksOfFamily F).inputs X
    (unaryBlocks_inputs F X h hX)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_BlockFlattenStep

/- Source proof segment: UnaryBlocksUnit -/
section source_UnaryBlocksUnit
/-!
# Original unit law of every ordered arity-one block

The full ordered block unit is proved from the actual successor
flattening, original unary comparisons, and original append triangle.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The actual tensor composite with an unchanged intermediate right factor. -/
theorem unaryUnit_tensor_comp {A B D K L : C}
    (f : A ⟶ B) (g : B ⟶ D) (s : K ⟶ L) :
    (f ⊗ₘ 𝟙 K) ≫ (g ⊗ₘ s) = (f ≫ g) ⊗ₘ s := by
  rw [tensorHom_comp_tensorHom, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Flattening actual unary blocks and applying their constructed original
unary comparisons is the original ordered input identity in heterogeneous form. -/
theorem unaryBlocks_unit_heq : ∀ {n : ℕ} (F : Fin n → FiniteFamily C) (X : Fin n → C)
    (h : ∀ i, arity (F i) = 1) (hX : ∀ i j, orderedFamily (F i) j = X i),
    HEq ((blocksOfFamilyIso F).hom ≫
      map (fun i => (unaryBlockIso (h i) (orderedFamily (F i)) (X i) (hX i)).hom))
      (𝟙 (obj X))
  | 0, _, _, _, _ => by
      change HEq ((𝟙 (𝟙_ C) ≫ 𝟙 (𝟙_ C)) ≫ 𝟙 (𝟙_ C)) (𝟙 (𝟙_ C))
      simp only [Category.id_comp]
      rfl
  | n + 1, F, X, h, hX => by
      let u : ∀ i : Fin n, obj (orderedFamily ((Fin.init F) i)) ⟶ (Fin.init X) i := fun i =>
        (unaryBlockIso (h i.castSucc) (orderedFamily (F i.castSucc))
          (X i.castSucc) (hX i.castSucc)).hom
      let s : obj (orderedFamily (F (Fin.last n))) ⟶ X (Fin.last n) :=
        (unaryBlockIso (h (Fin.last n)) (orderedFamily (F (Fin.last n)))
        (X (Fin.last n)) (hX (Fin.last n))).hom
      let a : obj (Fin.append (blocksOfFamily (Fin.init F)).inputs
          (orderedFamily (F (Fin.last n)))) ⟶
          obj (blocksOfFamily (Fin.init F)).inputs ⊗ obj (orderedFamily (F (Fin.last n))) :=
        (appendIso (blocksOfFamily (Fin.init F)).inputs (orderedFamily (F (Fin.last n)))).hom
      let f : obj (blocksOfFamily (Fin.init F)).inputs ⟶
          obj (fun i => obj (orderedFamily ((Fin.init F) i))) :=
        (blocksOfFamilyIso (Fin.init F)).hom
      let g : obj (fun i => obj (orderedFamily ((Fin.init F) i))) ⟶ obj (Fin.init X) := map u
      rw [blocksOfFamilyIso_succ_hom]
      change HEq ((a ≫ (f ⊗ₘ 𝟙 (obj (orderedFamily (F (Fin.last n)))))) ≫ (g ⊗ₘ s))
        (𝟙 (obj (Fin.init X) ⊗ X (Fin.last n)))
      rw [Category.assoc, unaryUnit_tensor_comp]
      have ho := unaryBlocks_obj_eq (Fin.init F) (Fin.init X)
        (fun i => h i.castSucc) (fun i => hX i.castSucc)
      have hi : HEq (f ≫ g)
          (𝟙 (obj (Fin.init X))) :=
        unaryBlocks_unit_heq (Fin.init F) (Fin.init X)
          (fun i => h i.castSucc) (fun i => hX i.castSucc)
      have ht := unaryUnit_tensorHom_heq rfl ho.symm rfl rfl
        (hi.trans (unaryUnit_id_heq ho.symm)) (HEq.rfl : HEq s _)
      have hc := heq_comp rfl rfl
        (congrArg (fun A => A ⊗ X (Fin.last n)) ho.symm)
        (HEq.rfl : HEq a _) ht
      have ha := appendIso_unary_unit_heq (h (Fin.last n))
        (blocksOfFamily (Fin.init F)).inputs (orderedFamily (F (Fin.last n)))
        (X (Fin.last n)) (hX (Fin.last n))
      exact hc.trans (ha.trans
        (unaryUnit_id_heq (congrArg (fun A => A ⊗ X (Fin.last n)) ho)))

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_UnaryBlocksUnit

/- Source proof segment: AllSingletonBlocksUnit -/
section source_AllSingletonBlocksUnit
/-!
# Full original all-singleton ordered block unit

The actual singleton block flattening followed by the actual finite
singleton maps is the original count-and-input carrier equality map.
The actual outer position readback is retained independently.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The actual finite singleton map is the constructed original arity-one comparison. -/
theorem finiteSingletonIso_unaryBlockIso (A : C) :
    finiteSingletonIso A =
      unaryBlockIso (singleton_arity A)
        (orderedFamily ((FiniteFamily.singleton (C := C)).obj A)) A
        (singleton_orderedFamily A) := by
  rfl

/-- The actual all-singleton block unit is the original ordered input identity
with the full original carrier equality retained in heterogeneous form. -/
theorem singletonBlocks_unit_heq {n : ℕ} (X : Fin n → C) :
    HEq ((blocksOfFamilyIso (singletonFamilies X)).hom ≫
      map (fun i => (finiteSingletonIso (X i)).hom)) (𝟙 (obj X)) := by
  simp only [finiteSingletonIso_unaryBlockIso]
  exact unaryBlocks_unit_heq (singletonFamilies X) X
    (fun i => singleton_arity (X i)) (fun i => singleton_orderedFamily (X i))

/-- The actual all-singleton block carrier equality from its original count and inputs. -/
theorem singletonBlocks_obj_eq {n : ℕ} (X : Fin n → C) :
    obj (blocksOfFamily (singletonFamilies X)).inputs = obj X :=
  obj_congr (singletonBlocks_totalArity X)
    (blocksOfFamily (singletonFamilies X)).inputs X (singletonBlocks_inputs X)

/-- Flattening every original singleton block and applying every actual finite
singleton map gives precisely the original count-and-input carrier equality map. -/
theorem singletonBlocks_unit {n : ℕ} (X : Fin n → C) :
    (blocksOfFamilyIso (singletonFamilies X)).hom ≫
        map (fun i => (finiteSingletonIso (X i)).hom) =
      eqToHom (obj_congr (singletonBlocks_totalArity X)
        (blocksOfFamily (singletonFamilies X)).inputs X (singletonBlocks_inputs X)) := by
  have ht := (conj_eqToHom_iff_heq
    ((blocksOfFamilyIso (singletonFamilies X)).hom ≫
      map (fun i => (finiteSingletonIso (X i)).hom))
    (𝟙 (obj X)) (singletonBlocks_obj_eq X) rfl).mpr (singletonBlocks_unit_heq X)
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using ht

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_AllSingletonBlocksUnit

/- Source proof segment: MapSingletonFlattenUnit -/
section source_MapSingletonFlattenUnit
/-!
# Original map-singleton-flatten unit map of the constructed tensor

The actual original sigma/PUnit right collapse is the constructed
flatten comparison at mapped original singletons followed by the
actual tensor of every original singleton-collapse component.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The original mapped singleton word and actual singleton maps retain
the outer tensor identity. -/
theorem mappedSingleton_word_unit (X : FiniteFamily C) :
    (finiteFamilyBlocksIso ((FiniteFamily.map (FiniteFamily.singleton (C := C))).obj X)).hom ≫
        finiteMap ((FiniteFamily.mapIso (finiteSingletonNatIso (C := C))).hom.app X) =
      eqToHom (mappedSingleton_word_obj_eq X) := by
  rw [finiteMap_singletonCollapse]
  exact singletonBlocks_unit (orderedFamily X)

set_option backward.isDefEq.respectTransparency false in
/-- The actual original map-singleton-flatten finite map is its complete
constructed unit composite. -/
theorem finiteMapSingletonFlatten_unit (X : FiniteFamily C) :
    finiteMap (FiniteFamily.mapSingletonFlattenIso.hom.app X) =
      (finiteFlattenIso ((FiniteFamily.map (FiniteFamily.singleton (C := C))).obj X)).hom ≫
        finiteMap ((FiniteFamily.mapIso (finiteSingletonNatIso (C := C))).hom.app X) := by
  let O := (FiniteFamily.map (FiniteFamily.singleton (C := C))).obj X
  rw [finiteFlattenIso, Iso.trans_hom, Category.assoc, mappedSingleton_word_unit,
    flattenToWordIso_hom, mappedSingleton_word_transport]
  change finiteMap (FiniteFamily.mapSingletonFlattenIso.hom.app X) =
    mapEquiv (flattenWordEquiv O) (fun i => eqToHom (flattenWord_objects O i)) ≫
      mapEquiv (finCongr (mappedSingleton_word_count X))
        (fun i => eqToHom (mappedSingleton_word_objects X i))
  rw [mapEquiv_comp, mapSingletonFlatten_finiteMap]
  apply mapEquiv_congr (mapSingletonFlatten_enumerated_equiv X)
  intro i
  exact (inputEquality_hom_chain
    (flattenWord_objects O i)
    (mappedSingleton_word_objects X (flattenWordEquiv O i))
    ((mapSingletonFlatten_objects X (enumeration _ i)).trans
      (orderedFamily_enumeratedEquiv (FiniteFamily.mapSingletonFlattenIso.hom.app X) i).symm)).symm

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_MapSingletonFlattenUnit

/- Source proof segment: UnbiasedUnitMaps -/
section source_UnbiasedUnitMaps
/-!
# Both original unit map laws of the constructed finite tensor

The original sigma/PUnit singleton and mapped-singleton collapse maps
are the actual constructed flattening and singleton composites. No
unbiased finite-tensor structure or unit outcome is assumed.
-/
end source_UnbiasedUnitMaps

/- Source proof segment: FiniteTensorUnitCoherence -/
section source_FiniteTensorUnitCoherence
/-!
# Exact original unit coherence of the constructed finite tensor

The proved original singleton and map-singleton component map laws
give the two exact functor-level unit equations required by the
original coherent unbiased tensor interface.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [MonoidalCategory C] [SymmetricCategory C] in
private theorem singletonLeftRoute_app (F : FiniteFamily C ⥤ C) (X : FiniteFamily C) :
    (Functor.isoWhiskerRight (FiniteFamily.singletonFlattenIso (C := C)) F ≪≫
      Functor.leftUnitor F).hom.app X = F.map (FiniteFamily.singletonFlattenIso.hom.app X) := by
  simp

omit [MonoidalCategory C] [SymmetricCategory C] in
private theorem singletonRightRoute_app (F : FiniteFamily C ⥤ C)
    (a : FiniteFamily.flatten (C := C) ⋙ F ≅ FiniteFamily.map F ⋙ F)
    (b : FiniteFamily.singleton (C := C) ⋙ F ≅ 𝟭 C) (X : FiniteFamily C) :
    (Functor.isoWhiskerLeft (FiniteFamily.singleton (C := FiniteFamily C)) a ≪≫
      Functor.isoWhiskerRight (FiniteFamily.singletonMapIso F) F ≪≫
      Functor.isoWhiskerLeft F b ≪≫ Functor.rightUnitor F).hom.app X =
        a.hom.app ((FiniteFamily.singleton (C := FiniteFamily C)).obj X) ≫ b.hom.app (F.obj X) := by
  simp only [Functor.comp_obj, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.id_obj,
    Functor.rightUnitor_hom_app, Category.comp_id]
  have hW := congrArg (fun e => e.hom.app X)
    (Functor.isoWhiskerRight_refl
      (FiniteFamily.singleton (C := FiniteFamily C) ⋙ FiniteFamily.map F) F)
  have hWC := congrArg
    (fun m => a.hom.app ((FiniteFamily.singleton (C := FiniteFamily C)).obj X) ≫ m ≫
      b.hom.app (F.obj X)) hW
  exact hWC.trans (congrArg
    (a.hom.app ((FiniteFamily.singleton (C := FiniteFamily C)).obj X) ≫ ·)
      (Category.id_comp (b.hom.app (F.obj X))))

/-- The actual constructed singleton and flatten natural isomorphisms satisfy the exact
original left unit equation. -/
theorem finiteTensor_singletonFlattenLaw :
    Functor.isoWhiskerRight (FiniteFamily.singletonFlattenIso (C :=
      C)) (finiteTensorFunctor (C := C)) ≪≫
      Functor.leftUnitor finiteTensorFunctor =
    Functor.isoWhiskerLeft (FiniteFamily.singleton (C := FiniteFamily C))
      (finiteFlattenNatIso (C := C)) ≪≫
      Functor.isoWhiskerRight (FiniteFamily.singletonMapIso finiteTensorFunctor)
        finiteTensorFunctor ≪≫
      Functor.isoWhiskerLeft finiteTensorFunctor (finiteSingletonNatIso (C := C)) ≪≫
      Functor.rightUnitor finiteTensorFunctor := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  exact (singletonLeftRoute_app finiteTensorFunctor X).trans
    ((finiteSingletonFlatten_unit X).trans
      (singletonRightRoute_app finiteTensorFunctor finiteFlattenNatIso finiteSingletonNatIso
        X).symm)

/-- The actual constructed singleton and flatten natural isomorphisms satisfy the exact
original right unit equation. -/
theorem finiteTensor_mapSingletonFlattenLaw :
    Functor.isoWhiskerRight (FiniteFamily.mapSingletonFlattenIso (C :=
      C)) (finiteTensorFunctor (C := C)) ≪≫
      Functor.leftUnitor finiteTensorFunctor =
    Functor.isoWhiskerLeft (FiniteFamily.map (FiniteFamily.singleton (C :=
      C))) (finiteFlattenNatIso (C := C)) ≪≫
      Functor.isoWhiskerRight (FiniteFamily.mapIso (finiteSingletonNatIso (C :=
        C))) finiteTensorFunctor ≪≫
      Functor.leftUnitor finiteTensorFunctor := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change finiteMap (FiniteFamily.mapSingletonFlattenIso.hom.app X) ≫ 𝟙 _ =
    (finiteFlattenIso ((FiniteFamily.map (FiniteFamily.singleton (C := C))).obj X)).hom ≫
      finiteMap ((FiniteFamily.mapIso (finiteSingletonNatIso (C := C))).hom.app X) ≫ 𝟙 _
  simp only [Category.comp_id]
  exact finiteMapSingletonFlatten_unit X

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FiniteTensorUnitCoherence

/- Source proof segment: AssocRouteFactories -/
section source_AssocRouteFactories
/-!
# Original associativity comparison component factories

Each source formula is checked for arbitrary functor and comparison
data before selecting the actual finite tensor construction. The
strict flatten/map transport contributes its original identity map.
-/

@[expose] public section

set_option autoImplicit false

universe v u v₁ u₁ v₂ u₂

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Lifting an original functor isomorphism keeps the complete original finite index. -/
theorem finiteFamily_mapIso_hom_app {A : Type u₁} {B : Type u₂}
    [Category.{v₁} A] [Category.{v₂} B] {F G : A ⥤ B} (a : F ≅ G) (X : FiniteFamily A) :
    (FiniteFamily.mapIso a).hom.app X =
      fixedIndexHom X.index (fun i => a.hom.app (X.obj i)) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The original left associativity route retains its two actual component maps. -/
theorem assocLeftRoute_app (F : FiniteFamily C ⥤ C)
    (a : FiniteFamily.flatten (C := C) ⋙ F ≅ FiniteFamily.map F ⋙ F)
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    (Functor.isoWhiskerLeft (FiniteFamily.map (FiniteFamily.flatten (C := C))) a ≪≫
        Functor.isoWhiskerRight (FiniteFamily.mapIso a) F).hom.app X =
      a.hom.app ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj X) ≫
        F.map ((FiniteFamily.mapIso a).hom.app X) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The original right associativity route retains its three effective component maps. -/
theorem assocRightRoute_app (F : FiniteFamily C ⥤ C)
    (a : FiniteFamily.flatten (C := C) ⋙ F ≅ FiniteFamily.map F ⋙ F)
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    (Functor.isoWhiskerRight (FiniteFamily.flattenAssocIso (C := C)) F ≪≫
        Functor.isoWhiskerLeft (FiniteFamily.flatten (C := FiniteFamily C)) a ≪≫
          Functor.isoWhiskerRight (FiniteFamily.flattenMapIso F) F ≪≫
            Functor.isoWhiskerLeft (FiniteFamily.map (FiniteFamily.map F)) a).hom.app X =
      F.map (FiniteFamily.flattenAssocIso.hom.app X) ≫
        a.hom.app ((FiniteFamily.flatten (C := FiniteFamily C)).obj X) ≫
          a.hom.app ((FiniteFamily.map (FiniteFamily.map F)).obj X) := by
  change F.map (FiniteFamily.flattenAssocIso.hom.app X) ≫
      a.hom.app ((FiniteFamily.flatten (C := FiniteFamily C)).obj X) ≫
        F.map ((FiniteFamily.flattenMapIso F).hom.app X) ≫
          a.hom.app ((FiniteFamily.map (FiniteFamily.map F)).obj X) = _
  have hId : (FiniteFamily.flattenMapIso F).hom.app X = 𝟙 _ := rfl
  have hMap := (congrArg F.map hId).trans (F.map_id _)
  have hComp := congrArg (fun m => F.map (FiniteFamily.flattenAssocIso.hom.app X) ≫
    a.hom.app ((FiniteFamily.flatten (C := FiniteFamily C)).obj X) ≫ m ≫
      a.hom.app ((FiniteFamily.map (FiniteFamily.map F)).obj X)) hMap
  exact hComp.trans (congrArg
    (F.map (FiniteFamily.flattenAssocIso.hom.app X) ≫
      a.hom.app ((FiniteFamily.flatten (C := FiniteFamily C)).obj X) ≫ ·)
      (Category.id_comp (a.hom.app ((FiniteFamily.map (FiniteFamily.map F)).obj X))))

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_AssocRouteFactories

/- Source proof segment: ActualAssocRoutes -/
section source_ActualAssocRoutes
/-!
# Actual original finite tensor associativity comparison routes

Both natural isomorphisms are built from the constructed finite tensor
flattening comparison and original finite-family sigma regrouping.
No equality between these routes is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The actual original triple-family input tensor functor. -/
noncomputable def finiteAssocSourceFunctor : FiniteFamily (FiniteFamily (FiniteFamily C)) ⥤ C :=
  FiniteFamily.map (FiniteFamily.flatten (C := C)) ⋙
    FiniteFamily.flatten (C := C) ⋙ finiteTensorFunctor

/-- The actual original outer tensor of middle tensors of inner tensors. -/
noncomputable def finiteAssocTargetFunctor : FiniteFamily (FiniteFamily (FiniteFamily C)) ⥤ C :=
  FiniteFamily.map (FiniteFamily.map (finiteTensorFunctor (C := C)) ⋙ finiteTensorFunctor) ⋙
    finiteTensorFunctor

/-- The actual original left associativity comparison route. -/
noncomputable def finiteAssocLeftNatIso :
    finiteAssocSourceFunctor (C := C) ≅ finiteAssocTargetFunctor :=
  Functor.isoWhiskerLeft (FiniteFamily.map (FiniteFamily.flatten (C := C))) finiteFlattenNatIso ≪≫
    Functor.isoWhiskerRight (FiniteFamily.mapIso finiteFlattenNatIso) finiteTensorFunctor

/-- The actual original right associativity route with its original
sigma regrouping orientation. -/
noncomputable def finiteAssocRightNatIso :
    finiteAssocSourceFunctor (C := C) ≅ finiteAssocTargetFunctor :=
  Functor.isoWhiskerRight (FiniteFamily.flattenAssocIso (C := C)) finiteTensorFunctor ≪≫
    Functor.isoWhiskerLeft (FiniteFamily.flatten (C := FiniteFamily C)) finiteFlattenNatIso ≪≫
      Functor.isoWhiskerRight (FiniteFamily.flattenMapIso finiteTensorFunctor)
        finiteTensorFunctor ≪≫
        Functor.isoWhiskerLeft (FiniteFamily.map (FiniteFamily.map finiteTensorFunctor))
          finiteFlattenNatIso

/-- The lifted actual flattening comparison retains every original outer component. -/
theorem finiteFlatten_mapIso_hom_app (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    (FiniteFamily.mapIso (finiteFlattenNatIso (C := C))).hom.app X =
      fixedIndexHom X.index (fun i => (finiteFlattenIso (X.obj i)).hom) := by
  rw [finiteFamily_mapIso_hom_app]
  rfl

/-- The actual left route is the original two-map associativity component. -/
theorem finiteAssocLeftNatIso_hom_app (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    (finiteAssocLeftNatIso (C := C)).hom.app X =
      (finiteFlattenIso ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj X)).hom ≫
        finiteMap (fixedIndexHom X.index (fun i => (finiteFlattenIso (X.obj i)).hom)) := by
  have h := assocLeftRoute_app (finiteTensorFunctor (C := C)) finiteFlattenNatIso X
  rw [finiteFlattenNatIso_hom_app, finiteFlatten_mapIso_hom_app] at h
  exact h

/-- The actual right route is the original three-map sigma-associative component. -/
theorem finiteAssocRightNatIso_hom_app (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    (finiteAssocRightNatIso (C := C)).hom.app X =
      finiteMap ((FiniteFamily.flattenAssocIso (C := C)).hom.app X) ≫
        (finiteFlattenIso ((FiniteFamily.flatten (C := FiniteFamily C)).obj X)).hom ≫
          (finiteFlattenIso ((FiniteFamily.map
            (FiniteFamily.map (finiteTensorFunctor (C := C)))).obj X)).hom := by
  have h := assocRightRoute_app (finiteTensorFunctor (C := C)) finiteFlattenNatIso X
  rw [finiteFlattenNatIso_hom_app, finiteFlattenNatIso_hom_app] at h
  exact h

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ActualAssocRoutes

/- Source proof segment: OrderedBlockConcat -/
section source_OrderedBlockConcat
/-!
# Original concatenation of ordered finite tensor blocks

Concatenation retains all original outer blocks and every original
inner input. Its input and block-tensor comparisons are the actual
finite count/object equality maps, including empty blocks.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

namespace Blocks

variable {C : Type u}

/-- Concatenate two original ordered sequences of finite tensor blocks. -/
def concat (B : Blocks C) : Blocks C → Blocks C
  | .nil => B
  | .snoc D X => .snoc (concat B D) X

/-- Concatenation retains the sum of the two original outer block counts. -/
theorem concat_length (B : Blocks C) : ∀ D : Blocks C, (concat B D).length = B.length + D.length
  | .nil => rfl
  | .snoc D X => by
      change (concat B D).length + 1 = B.length + (D.length + 1)
      rw [concat_length]
      exact Nat.add_assoc _ _ _

/-- Concatenation retains the sum of every original inner input count. -/
theorem concat_totalArity (B : Blocks C) :
    ∀ D : Blocks C, (concat B D).totalArity = B.totalArity + D.totalArity
  | .nil => rfl
  | .snoc D (arity := n) X => by
      change (concat B D).totalArity + n = B.totalArity + (D.totalArity + n)
      rw [concat_totalArity]
      exact Nat.add_assoc _ _ _

/-- Every concatenated original input has its original append position and object. -/
theorem concat_inputs (B : Blocks C) : ∀ (D : Blocks C) (i : Fin (concat B D).totalArity),
    (concat B D).inputs i = Fin.append B.inputs D.inputs (Fin.cast (concat_totalArity B D) i)
  | .nil, i => by
      exact (Fin.append_left B.inputs (Fin.elim0 : Fin 0 → C) i).symm
  | .snoc D (arity := n) X, i => by
      have hCount : (concat B D).totalArity + n = B.totalArity + (D.totalArity + n) :=
        (congrArg (· + n) (concat_totalArity B D)).trans (Nat.add_assoc _ _ _)
      change Fin ((concat B D).totalArity + n) at i
      change Fin.append (concat B D).inputs X i =
        Fin.append B.inputs (Fin.append D.inputs X) (Fin.cast hCount i)
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · have hc : Fin.cast hCount (Fin.castAdd n j) =
            Fin.cast (Nat.add_assoc B.totalArity D.totalArity n)
              (Fin.castAdd n (Fin.cast (concat_totalArity B D) j)) := Fin.ext rfl
        change Fin.append (concat B D).inputs X (Fin.castAdd n j) =
          Fin.append B.inputs (Fin.append D.inputs X)
            (Fin.cast hCount (Fin.castAdd n j))
        rw [Fin.append_left, hc]
        have ha := congrFun (Fin.append_assoc B.inputs D.inputs X)
          (Fin.castAdd n (Fin.cast (concat_totalArity B D) j))
        dsimp only [Function.comp_apply] at ha
        rw [Fin.append_left] at ha
        exact (concat_inputs B D j).trans ha
      · have hc : Fin.cast hCount
            (Fin.natAdd (concat B D).totalArity j) =
            Fin.natAdd B.totalArity (Fin.natAdd D.totalArity j) := by
          apply Fin.ext
          change (concat B D).totalArity + j.val = B.totalArity + (D.totalArity + j.val)
          have hPre := concat_totalArity B D
          omega
        change Fin.append (concat B D).inputs X (Fin.natAdd (concat B D).totalArity j) =
          Fin.append B.inputs (Fin.append D.inputs X)
            (Fin.cast hCount (Fin.natAdd (concat B D).totalArity j))
        rw [Fin.append_right, hc, Fin.append_right, Fin.append_right]

variable [Category.{v} C] [MonoidalCategory C]

/-- The original concatenated input tensor is its original appended input tensor. -/
theorem concat_inputs_obj_eq (B D : Blocks C) :
    obj (concat B D).inputs = obj (Fin.append B.inputs D.inputs) :=
  obj_congr (concat_totalArity B D) _ _ (concat_inputs B D)

/-- The actual original finite input equality comparison for block concatenation. -/
def concatInputsIso (B D : Blocks C) :
    obj (concat B D).inputs ≅ obj (Fin.append B.inputs D.inputs) :=
  eqToIso (concat_inputs_obj_eq B D)

/-- Every original concatenated block tensor retains its original appended outer position. -/
theorem concat_blockTensors (B : Blocks C) : ∀ (D : Blocks C) (i : Fin (concat B D).length),
    (concat B D).blockTensors i = Fin.append B.blockTensors D.blockTensors (Fin.cast
      (concat_length B D) i)
  | .nil, i => (Fin.append_left B.blockTensors (Fin.elim0 : Fin 0 → C) i).symm
  | .snoc D (arity := n) X, i => by
      have hCount : (concat B D).length + 1 = (B.length + D.length) + 1 :=
        congrArg (· + 1) (concat_length B D)
      change Fin ((concat B D).length + 1) at i
      change Fin.snoc (α := fun _ : Fin ((concat B D).length + 1) => C)
          (concat B D).blockTensors (obj X) i =
        Fin.append B.blockTensors
          (Fin.snoc (α := fun _ : Fin (D.length + 1) => C) D.blockTensors (obj X))
            (Fin.cast hCount i)
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have hc : Fin.cast hCount (Fin.last (concat B D).length) =
            Fin.last (B.length + D.length) := by
          apply Fin.ext
          change (concat B D).length = B.length + D.length
          exact concat_length B D
        rw [hc, Fin.append_snoc]
        exact (Fin.snoc_last (α := fun _ : Fin ((concat B D).length + 1) => C)
          (obj X) (concat B D).blockTensors).trans
            (Fin.snoc_last (α := fun _ : Fin (B.length + D.length + 1) => C)
              (obj X) (Fin.append B.blockTensors D.blockTensors)).symm
      · have hc : Fin.cast hCount j.castSucc =
            (Fin.cast (concat_length B D) j).castSucc := Fin.ext rfl
        rw [hc, Fin.append_snoc, Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact concat_blockTensors B D j

/-- The original concatenated block tensor word is its original appended outer block tensor word. -/
theorem concat_blockTensors_obj_eq (B D : Blocks C) :
    obj (concat B D).blockTensors = obj (Fin.append B.blockTensors D.blockTensors) :=
  obj_congr (concat_length B D) _ _ (concat_blockTensors B D)

/-- The actual original block tensor equality comparison for concatenation. -/
def concatBlockTensorsIso (B D : Blocks C) :
    obj (concat B D).blockTensors ≅ obj (Fin.append B.blockTensors D.blockTensors) :=
  eqToIso (concat_blockTensors_obj_eq B D)

end Blocks

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedBlockConcat

/- Source proof segment: BlockGroups -/
section source_BlockGroups
/-!
# Original ordered groups of finite tensor blocks

A group stores its original rows as block words. Flattening rows uses
the actual block concatenation; grouping inputs or block tensors keeps
each original row as one block, including empty rows.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

/-- An ordered finite sequence of original block-word rows, with no coherence outcomes as fields. -/
inductive Groups (C : Type u) where
  | nil : Groups C
  | snoc (initial : Groups C) (row : Blocks C) : Groups C

namespace Groups

variable {C : Type u}

/-- The number of original rows, including empty rows. -/
def length : Groups C → ℕ
  | .nil => 0
  | .snoc G _ => G.length + 1

/-- Concatenate every original row using the actual block concatenation. -/
def flat : Groups C → Blocks C
  | .nil => .nil
  | .snoc G B => Blocks.concat G.flat B

/-- Keep each original row's entire ordered input word as one original block. -/
def groupedInputs : Groups C → Blocks C
  | .nil => .nil
  | .snoc G B => .snoc G.groupedInputs B.inputs

/-- The original positions inside the original input word of each row. -/
def inputPositions : Groups C → Type
  | .nil => Empty
  | .snoc G B => G.inputPositions ⊕ Fin B.totalArity

/-- Evaluate an original row input in its original object. -/
def inputAt : (G : Groups C) → G.inputPositions → C
  | .nil => Empty.elim
  | .snoc G B => Sum.elim G.inputAt B.inputs

/-- The original positions of the middle blocks inside each original row. -/
def middlePositions : Groups C → Type
  | .nil => Empty
  | .snoc G B => G.middlePositions ⊕ Fin B.length

/-- Construct the actual ordered groups of a literal ordered family of original rows. -/
def ofRows : {n : ℕ} → (Fin n → Blocks C) → Groups C
  | 0, _ => .nil
  | n + 1, X => .snoc (ofRows (Fin.init X)) (X (Fin.last n))

/-- Every original ordered row is retained by the group producer. -/
theorem ofRows_length : ∀ {n : ℕ} (X : Fin n → Blocks C), (ofRows X).length = n
  | 0, _ => rfl
  | _n + 1, X => congrArg (· + 1) (ofRows_length (Fin.init X))

/-- Grouping every original row input retains its original outer row count. -/
theorem groupedInputs_length : ∀ G : Groups C, G.groupedInputs.length = G.length
  | .nil => rfl
  | .snoc G _ => congrArg (· + 1) (groupedInputs_length G)

/-- Concatenating original rows and grouping original row inputs have
the same actual input count. -/
theorem flat_groupedInputs_count : ∀ G : Groups C,
    G.flat.totalArity = G.groupedInputs.totalArity
  | .nil => rfl
  | .snoc G B => by
      change (Blocks.concat G.flat B).totalArity = G.groupedInputs.totalArity + B.totalArity
      rw [Blocks.concat_totalArity, flat_groupedInputs_count]

variable [Category.{v} C] [MonoidalCategory C]

open CategoryTheory MonoidalCategory

/-- Keep each original row's block tensor word as one original block. -/
def groupedTensors : Groups C → Blocks C
  | .nil => .nil
  | .snoc G B => .snoc G.groupedTensors B.blockTensors

/-- Evaluate an original middle-block position in its original tensor carrier. -/
def middleAt : (G : Groups C) → G.middlePositions → C
  | .nil => Empty.elim
  | .snoc G B => Sum.elim G.middleAt B.blockTensors

/-- The original outer tensor carrier of each original row. -/
def rowTensors : (G : Groups C) → Fin G.length → C
  | .nil => Fin.elim0
  | .snoc G B => Fin.snoc G.rowTensors (obj B.blockTensors)

/-- Grouping every original row tensor word retains every original row. -/
theorem groupedTensors_length : ∀ G : Groups C, G.groupedTensors.length = G.length
  | .nil => rfl
  | .snoc G _ => congrArg (· + 1) (groupedTensors_length G)

/-- Concatenated original middle blocks and grouped tensor inputs have the same actual count. -/
theorem flat_groupedTensors_count : ∀ G : Groups C,
    G.flat.length = G.groupedTensors.totalArity
  | .nil => rfl
  | .snoc G B => by
      change (Blocks.concat G.flat B).length = G.groupedTensors.totalArity + B.length
      rw [Blocks.concat_length, flat_groupedTensors_count]

end Groups

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_BlockGroups

/- Source proof segment: GroupInputPositions -/
section source_GroupInputPositions
/-!
# Full original input bijections for ordered row grouping

Both actual concatenated row inputs and actual grouped row inputs are
identified with the same original row input positions and objects.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace CategoryTheory.MonoidalCategory.OrderedTensor.Groups

variable {C : Type u}

/-- The actual concatenated original input word enumerates all original row input positions. -/
def flatInputEquiv : (G : Groups C) → Fin G.flat.totalArity ≃ G.inputPositions
  | .nil => Equiv.equivEmpty (Fin 0)
  | .snoc G B => (finCongr (Blocks.concat_totalArity G.flat B)).trans
      (finSumFinEquiv.symm.trans
        (Equiv.sumCongr G.flatInputEquiv (Equiv.refl (Fin B.totalArity))))

/-- The actual grouped original input word enumerates the same original row input positions. -/
def groupedInputEquiv : (G : Groups C) → Fin G.groupedInputs.totalArity ≃ G.inputPositions
  | .nil => Equiv.equivEmpty (Fin 0)
  | .snoc G B => finSumFinEquiv.symm.trans
      (Equiv.sumCongr G.groupedInputEquiv (Equiv.refl (Fin B.totalArity)))

set_option backward.isDefEq.respectTransparency false in
/-- Every concatenated original row input has its original object at its original row position. -/
theorem flatInput_objects : ∀ (G : Groups C) (i : Fin G.flat.totalArity),
    G.flat.inputs i = G.inputAt (G.flatInputEquiv i)
  | .nil, i => Fin.elim0 i
  | .snoc G B, i => by
      have ho := Blocks.concat_inputs G.flat B i
      let hp := finSumFinEquiv.symm (Fin.cast (Blocks.concat_totalArity G.flat B) i)
      change (Blocks.concat G.flat B).inputs i =
        Sum.elim G.inputAt B.inputs
          ((Equiv.sumCongr G.flatInputEquiv (Equiv.refl (Fin B.totalArity))) hp)
      rw [ho]
      have h : ∀ j : Fin (G.flat.totalArity + B.totalArity),
          Fin.append G.flat.inputs B.inputs j =
            Sum.elim G.inputAt B.inputs
              ((Equiv.sumCongr G.flatInputEquiv (Equiv.refl (Fin B.totalArity)))
                (finSumFinEquiv.symm j)) := by
        intro j
        refine Fin.addCases (fun k => ?_) (fun k => ?_) j
        · rw [Fin.append_left, finSumFinEquiv_symm_apply_castAdd]
          exact flatInput_objects G k
        · rw [Fin.append_right, finSumFinEquiv_symm_apply_natAdd]
          rfl
      exact h _

/-- Every grouped original row input has the same original object at its original row position. -/
theorem groupedInput_objects : ∀ (G : Groups C) (i : Fin G.groupedInputs.totalArity),
    G.groupedInputs.inputs i = G.inputAt (G.groupedInputEquiv i)
  | .nil, i => Fin.elim0 i
  | .snoc G B, i => by
      change Fin.append G.groupedInputs.inputs B.inputs i =
        Sum.elim G.inputAt B.inputs
          ((Equiv.sumCongr G.groupedInputEquiv (Equiv.refl (Fin B.totalArity)))
            (finSumFinEquiv.symm i))
      refine Fin.addCases (fun k => ?_) (fun k => ?_) i
      · rw [Fin.append_left, finSumFinEquiv_symm_apply_castAdd]
        exact groupedInput_objects G k
      · rw [Fin.append_right, finSumFinEquiv_symm_apply_natAdd]
        rfl

/-- The complete actual input bijection from grouped rows to the original
concatenated row inputs. -/
def groupedToFlatInputEquiv (G : Groups C) :
    Fin G.groupedInputs.totalArity ≃ Fin G.flat.totalArity :=
  G.groupedInputEquiv.trans G.flatInputEquiv.symm

/-- The original grouped-to-concatenated input bijection retains every original input object. -/
theorem groupedToFlatInput_objects (G : Groups C) (i : Fin G.groupedInputs.totalArity) :
    G.groupedInputs.inputs i = G.flat.inputs (G.groupedToFlatInputEquiv i) := by
  have hi := G.flatInput_objects (G.flatInputEquiv.symm (G.groupedInputEquiv i))
  have hp := congrArg G.inputAt (G.flatInputEquiv.apply_symm_apply (G.groupedInputEquiv i))
  exact (G.groupedInput_objects i).trans (hi.trans hp).symm

end CategoryTheory.MonoidalCategory.OrderedTensor.Groups
end
end source_GroupInputPositions

/- Source proof segment: GroupFiniteFamilies -/
section source_GroupFiniteFamilies
/-!
# Actual groups of original finite-family rows

Every original row retains its actual middle enumeration and inner
input enumeration. The full row input positions are identified with
the actual ordered dependent sum of original nested positions.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

variable {C : Type u}

/-- Group every original finite-family row in its literal original outer order. -/
noncomputable def groupsOfFamilies : {n : ℕ} → (Fin n → FiniteFamily (FiniteFamily C)) → Groups C
  | 0, _ => .nil
  | n + 1, X => .snoc (groupsOfFamilies (Fin.init X)) (blocksOfFiniteFamily (X (Fin.last n)))

/-- Group all original rows in the actual original outer finite enumeration. -/
noncomputable def groupsOfFiniteFamilies
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) : Groups C :=
  groupsOfFamilies (X.obj ∘ enumeration X)

/-- The actual row producer retains every original outer row, including empty rows. -/
theorem groupsOfFamilies_length : ∀ {n : ℕ} (X : Fin n → FiniteFamily (FiniteFamily C)),
    (groupsOfFamilies X).length = n
  | 0, _ => rfl
  | _n + 1, X => congrArg (· + 1) (groupsOfFamilies_length (Fin.init X))

/-- The original complete nested input positions of the literal original outer rows. -/
def OrderedRowPositions {n : ℕ} (X : Fin n → FiniteFamily (FiniteFamily C)) : Type :=
  Σ i : Fin n, NestedPositions (X i)

/-- Evaluate a complete original nested position in its original leaf object. -/
def orderedRowAt {n : ℕ} (X : Fin n → FiniteFamily (FiniteFamily C))
    (p : OrderedRowPositions X) : C := (X p.1).obj p.2.1 |>.obj p.2.2

variable [Category.{v} C]

/-- The actual original flattened finite family in each original row. -/
abbrev flattenedRows {n : ℕ} (X : Fin n → FiniteFamily (FiniteFamily C)) :
    Fin n → FiniteFamily C := fun i => (FiniteFamily.flatten (C := C)).obj (X i)

/-- The actual ordered dependent sum adds the entire original final row. -/
noncomputable def rowPositionsSnocEquiv {n : ℕ}
    (X : Fin (n + 1) → FiniteFamily (FiniteFamily C)) :
    OrderedRowPositions (Fin.init X) ⊕ NestedPositions (X (Fin.last n)) ≃ OrderedRowPositions X :=
  positionsSnocEquiv (flattenedRows X)

/-- The full original grouped input positions retain every original row and both inner indices. -/
noncomputable def groupsOriginalPositions : {n : ℕ} → (X : Fin n → FiniteFamily (FiniteFamily C)) →
    (groupsOfFamilies X).inputPositions ≃ OrderedRowPositions X
  | 0, X => by
      haveI : IsEmpty (OrderedRowPositions X) := ⟨fun p => p.1.elim0⟩
      exact (Equiv.equivEmpty (OrderedRowPositions X)).symm
  | n + 1, X =>
      (Equiv.sumCongr (groupsOriginalPositions (Fin.init X))
        (nestedPositionsEquiv (X (Fin.last n)))).trans (rowPositionsSnocEquiv X)

/-- The actual dependent original row input bijection retains every original leaf object. -/
theorem groupsOriginalPosition_objects : ∀ {n : ℕ} (X : Fin n → FiniteFamily (FiniteFamily C))
    (p : (groupsOfFamilies X).inputPositions),
    (groupsOfFamilies X).inputAt p = orderedRowAt X (groupsOriginalPositions X p)
  | 0, _, p => Empty.elim p
  | n + 1, X, p => by
      cases p with
      | inl p =>
          change (groupsOfFamilies (Fin.init X)).inputAt p =
            orderedRowAt (Fin.init X) (groupsOriginalPositions (Fin.init X) p)
          exact groupsOriginalPosition_objects (Fin.init X) p
      | inr p =>
          change (blocksOfFiniteFamily (X (Fin.last n))).inputs p =
            ((X (Fin.last n)).obj (nestedPositionsEquiv (X (Fin.last n)) p).1).obj
              (nestedPositionsEquiv (X (Fin.last n)) p).2
          exact nestedPositions_objects (X (Fin.last n)) p

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_GroupFiniteFamilies

/- Source proof segment: RowInputFiberMap -/
section source_RowInputFiberMap
/-!
# Actual input normalization on every original finite-family row

Each original flattened row maps to its actual original ordered block
word by its constructed flattenWordEquiv and equality components.
Every outer row is retained by the original fiber-map constructors.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [MonoidalCategory C] [SymmetricCategory C] in
set_option backward.isDefEq.respectTransparency false in
theorem groupsOriginalInput_left {n : ℕ} (R : Fin (n + 1) → FiniteFamily (FiniteFamily C))
    (i : Fin (groupsOfFamilies (Fin.init R)).groupedInputs.totalArity) :
    groupsOriginalPositions R ((groupsOfFamilies R).groupedInputEquiv
      (Fin.castAdd (blocksOfFiniteFamily (R (Fin.last n))).totalArity i)) =
        ⟨(groupsOriginalPositions (Fin.init R)
          ((groupsOfFamilies (Fin.init R)).groupedInputEquiv i)).1.castSucc,
          (groupsOriginalPositions (Fin.init R)
            ((groupsOfFamilies (Fin.init R)).groupedInputEquiv i)).2⟩ := by
  change rowPositionsSnocEquiv R
    (Equiv.sumCongr (groupsOriginalPositions (Fin.init R))
      (nestedPositionsEquiv (R (Fin.last n)))
        (Equiv.sumCongr (groupsOfFamilies (Fin.init R)).groupedInputEquiv
          (Equiv.refl (Fin (blocksOfFiniteFamily (R (Fin.last n))).totalArity))
            (finSumFinEquiv.symm (Fin.castAdd _ i)))) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

omit [MonoidalCategory C] [SymmetricCategory C] in
set_option backward.isDefEq.respectTransparency false in
theorem groupsOriginalInput_right {n : ℕ} (R : Fin (n + 1) → FiniteFamily (FiniteFamily C))
    (i : Fin (blocksOfFiniteFamily (R (Fin.last n))).totalArity) :
    groupsOriginalPositions R ((groupsOfFamilies R).groupedInputEquiv
      (Fin.natAdd (groupsOfFamilies (Fin.init R)).groupedInputs.totalArity i)) =
        ⟨Fin.last n, nestedPositionsEquiv (R (Fin.last n)) i⟩ := by
  change rowPositionsSnocEquiv R
    (Equiv.sumCongr (groupsOriginalPositions (Fin.init R))
      (nestedPositionsEquiv (R (Fin.last n)))
        (Equiv.sumCongr (groupsOfFamilies (Fin.init R)).groupedInputEquiv
          (Equiv.refl (Fin (blocksOfFiniteFamily (R (Fin.last n))).totalArity))
            (finSumFinEquiv.symm (Fin.natAdd _ i)))) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

/-- The complete actual input map from original flattened rows to grouped original row words. -/
noncomputable def rowInputFiberMap : {n : ℕ} → (R : Fin n → FiniteFamily (FiniteFamily C)) →
    Blocks.FiberMap (blocksOfFamily (flattenedRows R)) (groupsOfFamilies R).groupedInputs
  | 0, _ => .nil
  | n + 1, R => .snoc (rowInputFiberMap (Fin.init R)) (flattenWordEquiv (R (Fin.last n)))
      (fun i => eqToHom (flattenWord_objects (R (Fin.last n)) i))

omit [MonoidalCategory C] [SymmetricCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- Every original grouped row input keeps its original flattened-row input position. -/
theorem rowInputFiberMap_positions : ∀ {n : ℕ} (R : Fin n → FiniteFamily (FiniteFamily C))
    (i : Fin (blocksOfFamily (flattenedRows R)).totalArity),
    groupsOriginalPositions R
        ((groupsOfFamilies R).groupedInputEquiv ((rowInputFiberMap R).inputEquiv i)) =
      flattenedPositionsEquiv (flattenedRows R) i
  | 0, _, i => Fin.elim0 i
  | n + 1, R, i => by
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · change Fin (blocksOfFamily (flattenedRows (Fin.init R))).totalArity at j
        change groupsOriginalPositions R
          ((groupsOfFamilies R).groupedInputEquiv
            (sumInputsEquiv (rowInputFiberMap (Fin.init R)).inputEquiv
              (flattenWordEquiv (R (Fin.last n)))
                (Fin.castAdd (arity ((FiniteFamily.flatten (C := C)).obj (R (Fin.last n)))) j))) = _
        rw [sumInputsEquiv_left, flattenedPositions_left, groupsOriginalInput_left]
        have h := rowInputFiberMap_positions (Fin.init R) j
        exact congrArg (fun p : OrderedRowPositions (Fin.init R) =>
          (⟨p.1.castSucc, p.2⟩ : OrderedRowPositions R)) h
      · change groupsOriginalPositions R
          ((groupsOfFamilies R).groupedInputEquiv
            (sumInputsEquiv (rowInputFiberMap (Fin.init R)).inputEquiv
              (flattenWordEquiv (R (Fin.last n)))
                (Fin.natAdd (blocksOfFamily (flattenedRows (Fin.init R))).totalArity j))) = _
        rw [sumInputsEquiv_right, flattenedPositions_right, groupsOriginalInput_right]
        have h := (nestedPositionsEquiv (R (Fin.last n))).apply_symm_apply
          (enumeration ((FiniteFamily.flatten (C := C)).obj (R (Fin.last n))) j)
        exact congrArg (fun p : NestedPositions (R (Fin.last n)) =>
          (⟨Fin.last n, p⟩ : OrderedRowPositions R)) h

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_RowInputFiberMap

/- Source proof segment: TripleInputGeometry -/
section source_TripleInputGeometry
/-!
# Original triple-family input geometry and exact sigma regrouping

Both original right- and left-associated dependent sums are identified
with the same actual concatenated original row inputs. The original
reassociation is precisely the supplied sigma-association map.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The actual original outer enumeration on the complete original nested row positions. -/
noncomputable def tripleOuterPositionsEquiv
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    OrderedRowPositions (X.obj ∘ enumeration X) ≃
      ((FiniteFamily.mapFlattenFlatten (C := C)).obj X).index :=
  Equiv.sigmaCongr (enumeration X) (fun _ => Equiv.refl _)

/-- Every original concatenated row input identifies its original
right-associated triple position. -/
noncomputable def rightTripleInputEquiv
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    Fin (groupsOfFiniteFamilies X).flat.totalArity ≃
      ((FiniteFamily.mapFlattenFlatten (C := C)).obj X).index :=
  (groupsOfFiniteFamilies X).flatInputEquiv.trans
    ((groupsOriginalPositions (X.obj ∘ enumeration X)).trans (tripleOuterPositionsEquiv X))

/-- Every original concatenated row input identifies its original
left-associated triple position. -/
noncomputable def leftTripleInputEquiv
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    Fin (groupsOfFiniteFamilies X).flat.totalArity ≃
      ((FiniteFamily.flattenFlatten (C := C)).obj X).index :=
  (rightTripleInputEquiv X).trans ((FiniteFamily.flattenAssocIso (C := C)).hom.app X).equiv

/-- The actual original triple reassociation has precisely its original
sigma-association bijection. -/
theorem flattenAssoc_original_equiv
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    ((FiniteFamily.flattenAssocIso (C := C)).hom.app X).equiv =
      (Equiv.sigmaAssoc (fun a b => ((X.obj a).obj b).index)).symm := rfl

/-- The actual original triple reassociation keeps the identity of every original leaf object. -/
theorem flattenAssoc_original_component
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (p : ((FiniteFamily.mapFlattenFlatten (C := C)).obj X).index) :
    ((FiniteFamily.flattenAssocIso (C := C)).hom.app X).hom p =
      𝟙 (((FiniteFamily.mapFlattenFlatten (C := C)).obj X).obj p) := rfl

/-- The two original triple input bijections differ by exactly the original reassociation. -/
theorem tripleInput_regrouping
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    (rightTripleInputEquiv X).trans
      ((FiniteFamily.flattenAssocIso (C := C)).hom.app X).equiv = leftTripleInputEquiv X := rfl

/-- Every concatenated original row input has the original right-associated triple leaf object. -/
theorem rightTripleInput_objects
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (i : Fin (groupsOfFiniteFamilies X).flat.totalArity) :
    (groupsOfFiniteFamilies X).flat.inputs i =
      ((FiniteFamily.mapFlattenFlatten (C := C)).obj X).obj (rightTripleInputEquiv X i) :=
  ((groupsOfFiniteFamilies X).flatInput_objects i).trans
    (groupsOriginalPosition_objects (X.obj ∘ enumeration X)
      ((groupsOfFiniteFamilies X).flatInputEquiv i))

/-- Every concatenated original row input has the same original
left-associated triple leaf object. -/
theorem leftTripleInput_objects
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (i : Fin (groupsOfFiniteFamilies X).flat.totalArity) :
    (groupsOfFiniteFamilies X).flat.inputs i =
      ((FiniteFamily.flattenFlatten (C := C)).obj X).obj (leftTripleInputEquiv X i) := by
  exact rightTripleInput_objects X i

/-- The original right-associated finite input enumeration maps to the
actual concatenated row word. -/
noncomputable def rightTripleWordEquiv
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    Fin (arity ((FiniteFamily.mapFlattenFlatten (C := C)).obj X)) ≃
      Fin (groupsOfFiniteFamilies X).flat.totalArity :=
  (enumeration ((FiniteFamily.mapFlattenFlatten (C := C)).obj X)).trans
    (rightTripleInputEquiv X).symm

/-- The original left-associated finite input enumeration maps to the
same actual concatenated row word. -/
noncomputable def leftTripleWordEquiv
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    Fin (arity ((FiniteFamily.flattenFlatten (C := C)).obj X)) ≃
      Fin (groupsOfFiniteFamilies X).flat.totalArity :=
  (enumeration ((FiniteFamily.flattenFlatten (C := C)).obj X)).trans
    (leftTripleInputEquiv X).symm

/-- The complete original enumerated sigma reassociation gives the same
actual concatenated input word. -/
theorem tripleWord_regrouping
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    (enumeratedEquiv ((FiniteFamily.flattenAssocIso (C := C)).hom.app X)).trans
      (leftTripleWordEquiv X) = rightTripleWordEquiv X := by
  apply Equiv.ext
  intro i
  simp only [enumeratedEquiv, leftTripleWordEquiv, rightTripleWordEquiv,
    leftTripleInputEquiv, Equiv.trans_apply, Equiv.symm_trans_apply,
    Equiv.apply_symm_apply, Equiv.symm_apply_apply]

/-- Every original right-associated enumerated input retains its
original concatenated row object. -/
theorem rightTripleWord_objects
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (i : Fin (arity ((FiniteFamily.mapFlattenFlatten (C := C)).obj X))) :
    orderedFamily ((FiniteFamily.mapFlattenFlatten (C := C)).obj X) i =
      (groupsOfFiniteFamilies X).flat.inputs (rightTripleWordEquiv X i) := by
  change ((FiniteFamily.mapFlattenFlatten (C := C)).obj X).obj
      (enumeration ((FiniteFamily.mapFlattenFlatten (C := C)).obj X) i) =
    (groupsOfFiniteFamilies X).flat.inputs
      ((rightTripleInputEquiv X).symm
        (enumeration ((FiniteFamily.mapFlattenFlatten (C := C)).obj X) i))
  have h := rightTripleInput_objects X
    ((rightTripleInputEquiv X).symm
      (enumeration ((FiniteFamily.mapFlattenFlatten (C := C)).obj X) i))
  simpa only [Equiv.apply_symm_apply] using h.symm

/-- Every original left-associated enumerated input retains the same
original concatenated row object. -/
theorem leftTripleWord_objects
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (i : Fin (arity ((FiniteFamily.flattenFlatten (C := C)).obj X))) :
    orderedFamily ((FiniteFamily.flattenFlatten (C := C)).obj X) i =
      (groupsOfFiniteFamilies X).flat.inputs (leftTripleWordEquiv X i) := by
  change ((FiniteFamily.flattenFlatten (C := C)).obj X).obj
      (enumeration ((FiniteFamily.flattenFlatten (C := C)).obj X) i) =
    (groupsOfFiniteFamilies X).flat.inputs
      ((leftTripleInputEquiv X).symm
        (enumeration ((FiniteFamily.flattenFlatten (C := C)).obj X) i))
  have h := leftTripleInput_objects X
    ((leftTripleInputEquiv X).symm (enumeration ((FiniteFamily.flattenFlatten (C := C)).obj X) i))
  simpa only [Equiv.apply_symm_apply] using h.symm

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_TripleInputGeometry

/- Source proof segment: TripleRowsInputGeometry -/
section source_TripleRowsInputGeometry
/-!
# Original mapped-row inputs and triple grouping

The original map-flatten rows keep their actual nested enumerations.
Their literal block word is related by complete original input
bijections to both grouped and concatenated original row inputs.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The actual original finite family obtained by flattening each original row. -/
noncomputable def mappedFlattenRows
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) : FiniteFamily (FiniteFamily C) :=
  (FiniteFamily.map (FiniteFamily.flatten (C := C))).obj X

/-- The complete original grouped row input word identifies its
right-associated triple positions. -/
noncomputable def rightGroupedTripleInputEquiv
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    Fin (groupsOfFiniteFamilies X).groupedInputs.totalArity ≃
      ((FiniteFamily.mapFlattenFlatten (C := C)).obj X).index :=
  (groupsOfFiniteFamilies X).groupedInputEquiv.trans
    ((groupsOriginalPositions (X.obj ∘ enumeration X)).trans (tripleOuterPositionsEquiv X))

/-- Every grouped original row input retains its original right-associated triple leaf object. -/
theorem rightGroupedTripleInput_objects
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (i : Fin (groupsOfFiniteFamilies X).groupedInputs.totalArity) :
    (groupsOfFiniteFamilies X).groupedInputs.inputs i =
      ((FiniteFamily.mapFlattenFlatten (C := C)).obj X).obj (rightGroupedTripleInputEquiv X i) :=
  ((groupsOfFiniteFamilies X).groupedInput_objects i).trans
    (groupsOriginalPosition_objects (X.obj ∘ enumeration X)
      ((groupsOfFiniteFamilies X).groupedInputEquiv i))

/-- The actual mapped-row block word identifies its complete original triple positions. -/
noncomputable def mappedRowsOriginalEquiv
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    Fin (blocksOfFiniteFamily (mappedFlattenRows X)).totalArity ≃
      ((FiniteFamily.mapFlattenFlatten (C := C)).obj X).index :=
  nestedPositionsEquiv (mappedFlattenRows X)

/-- Every mapped-row block-word input retains its original triple leaf object. -/
theorem mappedRowsOriginal_objects
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (i : Fin (blocksOfFiniteFamily (mappedFlattenRows X)).totalArity) :
    (blocksOfFiniteFamily (mappedFlattenRows X)).inputs i =
      ((FiniteFamily.mapFlattenFlatten (C := C)).obj X).obj (mappedRowsOriginalEquiv X i) :=
  nestedPositions_objects (mappedFlattenRows X) i

/-- The original mapped-row block word maps to the same concatenated original triple input word. -/
noncomputable def mappedRowsToFlatInputEquiv
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    Fin (blocksOfFiniteFamily (mappedFlattenRows X)).totalArity ≃
      Fin (groupsOfFiniteFamilies X).flat.totalArity :=
  (mappedRowsOriginalEquiv X).trans (rightTripleInputEquiv X).symm

/-- The original mapped-row block word maps to the complete grouped original triple input word. -/
noncomputable def mappedRowsToGroupedInputEquiv
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    Fin (blocksOfFiniteFamily (mappedFlattenRows X)).totalArity ≃
      Fin (groupsOfFiniteFamilies X).groupedInputs.totalArity :=
  (mappedRowsOriginalEquiv X).trans (rightGroupedTripleInputEquiv X).symm

/-- The full mapped-row to concatenated input bijection retains every original leaf object. -/
theorem mappedRowsToFlatInput_objects
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (i : Fin (blocksOfFiniteFamily (mappedFlattenRows X)).totalArity) :
    (blocksOfFiniteFamily (mappedFlattenRows X)).inputs i =
      (groupsOfFiniteFamilies X).flat.inputs (mappedRowsToFlatInputEquiv X i) := by
  have ht := rightTripleInput_objects X
    ((rightTripleInputEquiv X).symm (mappedRowsOriginalEquiv X i))
  have hp := congrArg ((FiniteFamily.mapFlattenFlatten (C := C)).obj X).obj
    ((rightTripleInputEquiv X).apply_symm_apply (mappedRowsOriginalEquiv X i))
  exact (mappedRowsOriginal_objects X i).trans (ht.trans hp).symm

/-- The full mapped-row to grouped input bijection retains every original leaf object. -/
theorem mappedRowsToGroupedInput_objects
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (i : Fin (blocksOfFiniteFamily (mappedFlattenRows X)).totalArity) :
    (blocksOfFiniteFamily (mappedFlattenRows X)).inputs i =
      (groupsOfFiniteFamilies X).groupedInputs.inputs (mappedRowsToGroupedInputEquiv X i) := by
  have ht := rightGroupedTripleInput_objects X
    ((rightGroupedTripleInputEquiv X).symm (mappedRowsOriginalEquiv X i))
  have hp := congrArg ((FiniteFamily.mapFlattenFlatten (C := C)).obj X).obj
    ((rightGroupedTripleInputEquiv X).apply_symm_apply (mappedRowsOriginalEquiv X i))
  exact (mappedRowsOriginal_objects X i).trans (ht.trans hp).symm

/-- The original map-flatten enumeration gives exactly the complete concatenated triple word map. -/
theorem mappedRowsWord_regrouping
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    (flattenWordEquiv (mappedFlattenRows X)).trans (mappedRowsToFlatInputEquiv X) =
      rightTripleWordEquiv X := by
  apply Equiv.ext
  intro i
  change (rightTripleInputEquiv X).symm
      ((nestedPositionsEquiv (mappedFlattenRows X))
        ((nestedPositionsEquiv (mappedFlattenRows X)).symm
          (enumeration ((FiniteFamily.mapFlattenFlatten (C := C)).obj X) i))) =
    (rightTripleInputEquiv X).symm
      (enumeration ((FiniteFamily.mapFlattenFlatten (C := C)).obj X) i)
  exact congrArg (rightTripleInputEquiv X).symm
    ((nestedPositionsEquiv (mappedFlattenRows X)).apply_symm_apply
      (enumeration ((FiniteFamily.mapFlattenFlatten (C := C)).obj X) i))

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_TripleRowsInputGeometry

/- Source proof segment: RowInputWordMap -/
section source_RowInputWordMap
/-!
# Actual mapped-row input word map

The original row fiber map identifies the exact original nested
input positions and equality components of the mapped-flatten rows.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [MonoidalCategory C] [SymmetricCategory C] in
set_option backward.isDefEq.respectTransparency false in
theorem rowInputFiberMap_equiv
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    (rowInputFiberMap (X.obj ∘ enumeration X)).inputEquiv = mappedRowsToGroupedInputEquiv X := by
  apply Equiv.ext
  intro i
  apply (rightGroupedTripleInputEquiv X).injective
  have h := rowInputFiberMap_positions (X.obj ∘ enumeration X) i
  have hR := (rightGroupedTripleInputEquiv X).apply_symm_apply (mappedRowsOriginalEquiv X i)
  exact (congrArg (tripleOuterPositionsEquiv X) h).trans hR.symm

omit [MonoidalCategory C] [SymmetricCategory C] in
set_option backward.isDefEq.respectTransparency false in
theorem rowInputFiberMap_component_id : ∀ {n : ℕ} (R : Fin n → FiniteFamily (FiniteFamily C))
    (i : Fin (blocksOfFamily (flattenedRows R)).totalArity),
    HEq ((rowInputFiberMap R).inputComponents i) (𝟙 ((blocksOfFamily (flattenedRows R)).inputs i))
  | 0, _, i => Fin.elim0 i
  | n + 1, R, i => by
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · have h := sumInputsComponent_left_heq (rowInputFiberMap (Fin.init R)).inputComponents
          (fun i => eqToHom (flattenWord_objects (R (Fin.last n)) i)) j
        have hi := rowInputFiberMap_component_id (Fin.init R) j
        exact h.trans (hi.trans
          (inputObject_identity_heq (Fin.append_left _ _ j).symm))
      · have h := sumInputsComponent_right_heq (rowInputFiberMap (Fin.init R)).inputComponents
          (fun i => eqToHom (flattenWord_objects (R (Fin.last n)) i)) j
        exact h.trans ((eqToHom_heq_id_dom _ _ _).trans
          (inputObject_identity_heq (Fin.append_right _ _ j).symm))

set_option backward.isDefEq.respectTransparency false in
theorem rowInputFiberMap_wordMap
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    (rowInputFiberMap (X.obj ∘ enumeration X)).inputMap =
      mapEquiv (mappedRowsToGroupedInputEquiv X)
        (fun i => eqToHom (mappedRowsToGroupedInput_objects X i)) := by
  apply mapEquiv_congr (rowInputFiberMap_equiv X)
  intro i
  exact (rowInputFiberMap_component_id (X.obj ∘ enumeration X) i).trans
    (eqToHom_heq_id_dom _ _ _).symm

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_RowInputWordMap

/- Source proof segment: ConcatCountTransport -/
section source_ConcatCountTransport
/-!
# Original count transports in the block concatenation split

The actual concatenation input/count equalities transport the original
append split. Its empty-block maps are the original right unitors.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- An actual original input count/family equality transports the original append split. -/
theorem appendIso_count_transport {m m' n : ℕ} (hm : m = m')
    (X : Fin m → C) (X' : Fin m' → C) (Y : Fin n → C)
    (hX : ∀ i, X i = X' (Fin.cast hm i)) :
    eqToHom (append_obj_congr hm rfl X X' Y Y hX (fun _ => rfl)) ≫
        (appendIso X' Y).hom =
      (appendIso X Y).hom ≫ (eqToHom (obj_congr hm X X' hX) ⊗ₘ 𝟙 (obj Y)) := by
  cases hm
  have hXX : X = X' := funext hX
  cases hXX
  simp only [eqToHom_refl, Category.id_comp, id_tensorHom_id, Category.comp_id]

namespace Blocks

/-- The original concatenation input split. -/
def concatInputSplit (B D : Blocks C) : obj (B.concat D).inputs ≅ obj B.inputs ⊗ obj D.inputs :=
  concatInputsIso B D ≪≫ appendIso B.inputs D.inputs

/-- The original concatenation block-tensor split. -/
def concatTensorSplit (B D : Blocks C) :
    obj (B.concat D).blockTensors ≅ obj B.blockTensors ⊗ obj D.blockTensors :=
  concatBlockTensorsIso B D ≪≫ appendIso B.blockTensors D.blockTensors

set_option backward.isDefEq.respectTransparency false in
/-- An empty original final word has precisely the original input right-unitor inverse split. -/
theorem concatInputSplit_nil (B : Blocks C) : (concatInputSplit B Blocks.nil).hom =
    (ρ_ (obj B.inputs)).inv := by
  simp only [concatInputSplit, concatInputsIso, Iso.trans_hom, eqToIso.hom]
  rw [appendIso_zero_hom]
  dsimp only [concat, Blocks.inputs]
  rw [← Category.assoc, eqToHom_trans]
  change 𝟙 (obj B.inputs) ≫ (ρ_ (obj B.inputs)).inv = _
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
/-- An empty original final word has precisely the block-tensor right-unitor inverse split. -/
theorem concatTensorSplit_nil (B : Blocks C) : (concatTensorSplit B Blocks.nil).hom =
    (ρ_ (obj B.blockTensors)).inv := by
  simp only [concatTensorSplit, concatBlockTensorsIso, Iso.trans_hom, eqToIso.hom]
  rw [appendIso_zero_hom]
  dsimp only [concat, Blocks.blockTensors]
  rw [← Category.assoc, eqToHom_trans]
  change 𝟙 (obj B.blockTensors) ≫ (ρ_ (obj B.blockTensors)).inv = _
  exact Category.id_comp _

end Blocks

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ConcatCountTransport

/- Source proof segment: GroupCountGeometry -/
section source_GroupCountGeometry
/-!
# Original ordered count geometry of row grouping

The grouped and concatenated row inputs occupy the same original
ordered slots. Likewise every original middle block tensor occupies
its original grouped tensor slot, including all empty rows.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

/-- An original input-family/count equality retains every appended final input. -/
theorem append_family_count {m m' n : ℕ} {C : Type u} (h : m = m')
    (X : Fin m → C) (X' : Fin m' → C) (Y : Fin n → C)
    (hX : ∀ i, X i = X' (Fin.cast h i)) (i : Fin (m + n)) :
    Fin.append X Y i = Fin.append X' Y (Fin.cast (congrArg (· + n) h) i) := by
  cases h
  have hXX : X = X' := funext hX
  cases hXX
  rfl

namespace Groups

variable {C : Type u}

/-- Every original grouped input occupies the same original concatenated row input slot. -/
theorem groupedInput_count_objects : ∀ (G : Groups C) (i : Fin G.groupedInputs.totalArity),
    G.groupedInputs.inputs i = G.flat.inputs (Fin.cast G.flat_groupedInputs_count.symm i)
  | .nil, i => Fin.elim0 i
  | .snoc G B, i => by
      have hG := append_family_count G.flat_groupedInputs_count.symm
        G.groupedInputs.inputs G.flat.inputs B.inputs (groupedInput_count_objects G) i
      have hB := Blocks.concat_inputs G.flat B (Fin.cast
        (flat_groupedInputs_count (Groups.snoc G B)).symm i)
      have hc : Fin.cast (Blocks.concat_totalArity G.flat B)
          (Fin.cast (flat_groupedInputs_count (Groups.snoc G B)).symm i) =
        Fin.cast (congrArg (· + B.totalArity) G.flat_groupedInputs_count.symm) i := Fin.ext rfl
      rw [hc] at hB
      exact hG.trans hB.symm

variable [Category.{v} C] [MonoidalCategory C]

/-- Every original middle block tensor occupies its original grouped tensor input slot. -/
theorem flatMiddle_count_objects : ∀ (G : Groups C) (i : Fin G.flat.length),
    G.flat.blockTensors i = G.groupedTensors.inputs (Fin.cast G.flat_groupedTensors_count i)
  | .nil, i => Fin.elim0 i
  | .snoc G B, i => by
      have hG := append_family_count G.flat_groupedTensors_count
        G.flat.blockTensors G.groupedTensors.inputs B.blockTensors
          (flatMiddle_count_objects G) (Fin.cast (Blocks.concat_length G.flat B) i)
      have hB := Blocks.concat_blockTensors G.flat B i
      have hc : Fin.cast (congrArg (· + B.length) G.flat_groupedTensors_count)
          (Fin.cast (Blocks.concat_length G.flat B) i) =
        Fin.cast (flat_groupedTensors_count (Groups.snoc G B)) i := Fin.ext rfl
      rw [hc] at hG
      exact hB.trans hG

/-- The actual original grouped-input carrier is its original concatenated row carrier. -/
def groupedInputCountIso (G : Groups C) : obj G.groupedInputs.inputs ≅ obj G.flat.inputs :=
  congrIso G.flat_groupedInputs_count.symm _ _ (groupedInput_count_objects G)

/-- The actual original middle tensor carrier is its original grouped tensor-input carrier. -/
def groupedMiddleCountIso (G : Groups C) :
    obj G.flat.blockTensors ≅ obj G.groupedTensors.inputs :=
  congrIso G.flat_groupedTensors_count _ _ (flatMiddle_count_objects G)

end Groups

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_GroupCountGeometry

/- Source proof segment: ConcatInputSuccessor -/
section source_ConcatInputSuccessor
/-!
# Original input successor square for block concatenation

The original count transport is joined to the original heterogeneous
append associativity map, including an empty final inner block.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace Blocks

/-- The original input equality before splitting the last retained inner block. -/
theorem concatAppend_obj_eq (B D : Blocks C) {n : ℕ} (X : Fin n → C) :
    obj (Fin.append (B.concat D).inputs X) =
      obj (Fin.append (Fin.append B.inputs D.inputs) X) :=
  append_obj_congr (concat_totalArity B D) rfl _ _ X X (concat_inputs B D) (fun _ => rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The original successor input count map retains its complete three-block interpretation. -/
theorem concatInputsIso_snoc (B D : Blocks C) {n : ℕ} (X : Fin n → C) :
    (concatInputsIso B (Blocks.snoc D X)).hom =
      eqToHom (concatAppend_obj_eq B D X) ≫ (appendAssociator B.inputs D.inputs X).hom := by
  simp only [concatInputsIso, eqToIso.hom, appendAssociator, concat, Blocks.inputs,
    eqToHom_trans]

set_option backward.isDefEq.respectTransparency false in
/-- The actual concat input split obeys the original heterogeneous append associativity square. -/
theorem concatInputSplit_snoc_square (B D : Blocks C) {n : ℕ} (X : Fin n → C) :
    (concatInputSplit B (Blocks.snoc D X)).hom ≫
        (𝟙 (obj B.inputs) ⊗ₘ (appendIso D.inputs X).hom) =
      (appendIso (B.concat D).inputs X).hom ≫
        ((concatInputSplit B D).hom ⊗ₘ 𝟙 (obj X)) ≫
          (α_ (obj B.inputs) (obj D.inputs) (obj X)).hom := by
  simp only [concatInputSplit, Iso.trans_hom, Blocks.inputs, Category.assoc]
  change (concatInputsIso B (Blocks.snoc D X)).hom ≫
      (appendIso B.inputs (Fin.append D.inputs X)).hom ≫
        (𝟙 (obj B.inputs) ⊗ₘ (appendIso D.inputs X).hom) = _
  rw [concatInputsIso_snoc]
  simp only [Category.assoc]
  rw [appendIso_assoc]
  rw [← Category.assoc (eqToHom (concatAppend_obj_eq B D X))]
  have hc := appendIso_count_transport (concat_totalArity B D)
    (B.concat D).inputs (Fin.append B.inputs D.inputs) X (concat_inputs B D)
  rw [hc]
  simp only [Category.assoc]
  have ht := tensorHom_comp_tensorHom (concatInputsIso B D).hom (𝟙 (obj X))
    (appendIso B.inputs D.inputs).hom (𝟙 (obj X))
  simp only [Category.id_comp] at ht
  have hAll := congrArg
    (fun k => (appendIso (B.concat D).inputs X).hom ≫ k ≫
      (α_ (obj B.inputs) (obj D.inputs) (obj X)).hom) ht
  simpa only [concatInputsIso, eqToIso.hom, Category.assoc] using hAll

end Blocks

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ConcatInputSuccessor

/- Source proof segment: ConcatTensorSuccessor -/
section source_ConcatTensorSuccessor
/-!
# Original block-tensor successor square for concatenation

The original concatenated block-tensor count equality is reflected
through its original successor tensor and the ambient associator.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

theorem obj_snoc_eq {n : ℕ} (X : Fin n → C) (V : C) : obj (Fin.snoc X V) = obj X ⊗ V := by
  rw [obj_succ]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

set_option backward.isDefEq.respectTransparency false in
theorem append_successor_frame {p q : ℕ} (U : Fin p → C) (W : Fin (q + 1) → C)
    (V : Fin q → C) (A : C) (hi : Fin.init W = V) (hl : W (Fin.last q) = A)
    (ht : obj W = obj V ⊗ A)
    (hs : obj (Fin.append U W) = obj (Fin.append U V) ⊗ A) :
    (appendIso U W).hom ≫ (𝟙 (obj U) ⊗ₘ eqToHom ht) =
      eqToHom hs ≫ ((appendIso U V).hom ⊗ₘ 𝟙 A) ≫ (α_ (obj U) (obj V) A).hom := by
  cases hi
  cases hl
  have h : ht = (rfl : obj W = obj (Fin.init W) ⊗ W (Fin.last q)) := Subsingleton.elim _ _
  rw [h]
  simp only [eqToHom_refl, id_tensorHom_id, Category.comp_id]
  exact appendIso_succ_hom U W

namespace Blocks

/-- The original scalar successor appended after the two block-tensor words. -/
theorem concatTensorAppend_step (B D : Blocks C) {n : ℕ} (X : Fin n → C) :
    obj (Fin.append B.blockTensors (Blocks.snoc D X).blockTensors) =
      obj (Fin.append B.blockTensors D.blockTensors) ⊗ obj X := by
  change obj (Fin.append B.blockTensors (Fin.snoc D.blockTensors (obj X))) = _
  rw [Fin.append_snoc]
  rw [obj_succ]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

set_option backward.isDefEq.respectTransparency false in
/-- Original concatenated successor block tensors keep their original prefix equality map. -/
theorem concatBlockTensorsIso_snoc_transport (B D : Blocks C) {n : ℕ} (X : Fin n → C) :
    (concatBlockTensorsIso B (Blocks.snoc D X)).hom ≫
        eqToHom (concatTensorAppend_step B D X) =
      eqToHom (obj_blockTensors_snoc (B.concat D) X) ≫
        ((concatBlockTensorsIso B D).hom ⊗ₘ 𝟙 (obj X)) := by
  simp only [concatBlockTensorsIso, eqToIso.hom, tensorHom_id, eqToHom_whiskerRight,
    eqToHom_trans]

set_option backward.isDefEq.respectTransparency false in
/-- The original concat block-tensor split has its complete original successor associator square. -/
theorem concatTensorSplit_snoc_square (B D : Blocks C) {n : ℕ} (X : Fin n → C) :
    (concatTensorSplit B (Blocks.snoc D X)).hom ≫
        (𝟙 (obj B.blockTensors) ⊗ₘ eqToHom (obj_blockTensors_snoc D X)) =
      eqToHom (obj_blockTensors_snoc (B.concat D) X) ≫
        ((concatTensorSplit B D).hom ⊗ₘ 𝟙 (obj X)) ≫
          (α_ (obj B.blockTensors) (obj D.blockTensors) (obj X)).hom := by
  simp only [concatTensorSplit, Iso.trans_hom]
  have ha : (appendIso B.blockTensors (Blocks.snoc D X).blockTensors).hom ≫
      (𝟙 (obj B.blockTensors) ⊗ₘ eqToHom (obj_blockTensors_snoc D X)) =
    eqToHom (concatTensorAppend_step B D X) ≫
      ((appendIso B.blockTensors D.blockTensors).hom ⊗ₘ 𝟙 (obj X)) ≫
        (α_ (obj B.blockTensors) (obj D.blockTensors) (obj X)).hom := by
    change (appendIso B.blockTensors (Fin.snoc D.blockTensors (obj X))).hom ≫
      (𝟙 (obj B.blockTensors) ⊗ₘ eqToHom (obj_blockTensors_snoc D X)) = _
    exact append_successor_frame B.blockTensors (Fin.snoc D.blockTensors (obj X))
      D.blockTensors (obj X) (Fin.init_snoc _ _) (Fin.snoc_last _ _)
      (obj_snoc_eq _ _) (concatTensorAppend_step B D X)
  simp only [Category.assoc]
  rw [ha]
  have ht := concatBlockTensorsIso_snoc_transport B D X
  rw [← Category.assoc (concatBlockTensorsIso B (Blocks.snoc D X)).hom, ht]
  have hf := tensorHom_comp_tensorHom (concatBlockTensorsIso B D).hom (𝟙 (obj X))
    (appendIso B.blockTensors D.blockTensors).hom (𝟙 (obj X))
  simp only [Category.id_comp] at hf
  rw [Category.assoc]
  rw [← Category.assoc ((concatBlockTensorsIso B D).hom ⊗ₘ 𝟙 (obj X)), hf]

end Blocks

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ConcatTensorSuccessor

/- Source proof segment: ConcatSquareFactory -/
section source_ConcatSquareFactory
/-!
# Generic original successor square for concatenated block folds

The original two maps and their proved preceding comparison square
are joined through original tensor composition and associator naturality.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Original prefix folds retain their comparison square through one final original tensor. -/
theorem concat_successor_square {S T A B A' B' V E : C}
    (f : S ⟶ T) (a : A ⟶ A') (b : B ⟶ B') (s : S ⟶ A ⊗ B) (t : T ⟶ A' ⊗ B')
    (c : E ⟶ S ⊗ V) (q : C) (d : q ≅ B ⊗ V)
    (h : f ≫ t = s ≫ (a ⊗ₘ b)) :
    c ≫ (f ⊗ₘ 𝟙 V) ≫ (t ⊗ₘ 𝟙 V) ≫ (α_ A' B' V).hom =
      c ≫ (s ⊗ₘ 𝟙 V) ≫ (α_ A B V).hom ≫ (𝟙 A ⊗ₘ d.inv) ≫
        (a ⊗ₘ (d.hom ≫ (b ⊗ₘ 𝟙 V))) := by
  have hl := tensorHom_comp_tensorHom f (𝟙 V) t (𝟙 V)
  simp only [Category.id_comp] at hl
  have hn := associator_naturality a b (𝟙 V)
  have hr := tensorHom_comp_tensorHom (𝟙 A) d.inv a (d.hom ≫ (b ⊗ₘ 𝟙 V))
  simp only [Category.id_comp, Iso.inv_hom_id_assoc] at hr
  have hs := tensorHom_comp_tensorHom s (𝟙 V) (a ⊗ₘ b) (𝟙 V)
  simp only [Category.id_comp] at hs
  rw [← Category.assoc (f ⊗ₘ 𝟙 V) (t ⊗ₘ 𝟙 V), hl, h]
  rw [← hs]
  simp only [Category.assoc]
  rw [hn, hr]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ConcatSquareFactory

/- Source proof segment: ConcatFoldCoherence -/
section source_ConcatFoldCoherence
/-!
# Original block concatenation and fold map coherence

Every original inner block is retained. The proof uses the original
right-unit maps in the empty case and original tensor composition
and append associativity in each successor case.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace Blocks

set_option backward.isDefEq.respectTransparency false in
theorem flatten_snoc_cancel (D : Blocks C) {n : ℕ} (X : Fin n → C) :
    (flattenIso (Blocks.snoc D X)).hom ≫ eqToHom (obj_blockTensors_snoc D X) =
      (appendIso D.inputs X).hom ≫ ((flattenIso D).hom ⊗ₘ 𝟙 (obj X)) := by
  rw [flattenIso_snoc_hom]
  simp only [Category.assoc]
  slice_lhs 3 4 => rw [eqToHom_trans]
  simp only [eqToHom_refl, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
theorem tensor_snoc_cancel {A A' : C} (f : A ⟶ A') (D : Blocks C) {n : ℕ} (X : Fin n → C) :
    (f ⊗ₘ (flattenIso (Blocks.snoc D X)).hom) ≫
        (𝟙 A' ⊗ₘ eqToHom (obj_blockTensors_snoc D X)) =
      f ⊗ₘ ((appendIso D.inputs X).hom ≫ ((flattenIso D).hom ⊗ₘ 𝟙 (obj X))) := by
  rw [tensorHom_comp_tensorHom]
  simp only [Category.comp_id]
  rw [flatten_snoc_cancel]

set_option backward.isDefEq.respectTransparency false in
/-- The actual original concatenated block fold agrees with the two original independent folds. -/
theorem flattenIso_concat_split (B : Blocks C) : ∀ D : Blocks C,
    (flattenIso (B.concat D)).hom ≫ (concatTensorSplit B D).hom =
      (concatInputSplit B D).hom ≫ ((flattenIso B).hom ⊗ₘ (flattenIso D).hom)
  | .nil => by
      rw [concatTensorSplit_nil, concatInputSplit_nil]
      change (flattenIso B).hom ≫ (ρ_ (obj B.blockTensors)).inv =
        (ρ_ (obj B.inputs)).inv ≫ ((flattenIso B).hom ⊗ₘ 𝟙 (𝟙_ C))
      rw [tensorHom_id]
      exact rightUnitor_inv_naturality (flattenIso B).hom
  | .snoc D (arity := n) X => by
      let J := tensorIso (Iso.refl (obj B.blockTensors)) (eqToIso (obj_blockTensors_snoc D X))
      apply (cancel_mono J.hom).mp
      dsimp only [J, tensorIso_hom, Iso.refl_hom, eqToIso.hom]
      simp only [Category.assoc]
      rw [concatTensorSplit_snoc_square]
      dsimp only [concat] at *
      rw [← Category.assoc (flattenIso (Blocks.snoc (B.concat D) X)).hom,
        flatten_snoc_cancel]
      simp only [Category.assoc]
      rw [tensor_snoc_cancel]
      have h := concat_successor_square
        (flattenIso (B.concat D)).hom (flattenIso B).hom (flattenIso D).hom
        (concatInputSplit B D).hom (concatTensorSplit B D).hom
        (appendIso (B.concat D).inputs X).hom
        (obj (Fin.append D.inputs X)) (appendIso D.inputs X)
        (flattenIso_concat_split B D)
      have hInput := concatInputSplit_snoc_square B D X
      have hInput' : (concatInputSplit B (Blocks.snoc D X)).hom =
          (appendIso (B.concat D).inputs X).hom ≫
            ((concatInputSplit B D).hom ⊗ₘ 𝟙 (obj X)) ≫
              (α_ (obj B.inputs) (obj D.inputs) (obj X)).hom ≫
                (𝟙 (obj B.inputs) ⊗ₘ (appendIso D.inputs X).inv) := by
        have hm := congrArg (fun k => k ≫ (𝟙 (obj B.inputs) ⊗ₘ (appendIso D.inputs X).inv))
          hInput
        simpa only [Category.assoc, id_tensorHom, whiskerLeft_hom_inv, Category.comp_id] using hm
      rw [hInput']
      simpa only [Category.assoc] using h

/-- Complete original block concatenation compatibility, with both original count isomorphisms. -/
theorem flattenIso_concat (B D : Blocks C) :
    (flattenIso (B.concat D)).hom ≫ (concatBlockTensorsIso B D).hom ≫
        (appendIso B.blockTensors D.blockTensors).hom =
      (concatInputsIso B D).hom ≫ (appendIso B.inputs D.inputs).hom ≫
        ((flattenIso B).hom ⊗ₘ (flattenIso D).hom) := by
  have h := flattenIso_concat_split B D
  simpa only [concatTensorSplit, concatInputSplit, Iso.trans_hom, Category.assoc] using h

end Blocks

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ConcatFoldCoherence

/- Source proof segment: GroupFoldMap -/
section source_GroupFoldMap
/-!
# Original grouped row-fold map

The map tensors each original row fold in its original outer slot.
Its source and target are the actual block tensor carriers of grouped
inputs and grouped tensors, with all original successor transports.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor.Groups

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Tensor every original row fold, retaining its original outer block carrier. -/
def rowFoldMap : (G : Groups C) →
    obj G.groupedInputs.blockTensors ⟶ obj G.groupedTensors.blockTensors
  | .nil => 𝟙 (𝟙_ C)
  | .snoc G B => eqToHom (Blocks.obj_blockTensors_snoc G.groupedInputs B.inputs) ≫
      (rowFoldMap G ⊗ₘ (Blocks.flattenIso B).hom) ≫
        eqToHom (Blocks.obj_blockTensors_snoc G.groupedTensors B.blockTensors).symm

/-- The original row-fold tensor map at the empty outer group is the original unit identity. -/
theorem rowFoldMap_nil : rowFoldMap (Groups.nil : Groups C) = 𝟙 (𝟙_ C) := rfl

/-- The original successor tensor map retains its full original carrier equality transports. -/
theorem rowFoldMap_snoc (G : Groups C) (B : Blocks C) :
    rowFoldMap (Groups.snoc G B) =
      eqToHom (Blocks.obj_blockTensors_snoc G.groupedInputs B.inputs) ≫
        (rowFoldMap G ⊗ₘ (Blocks.flattenIso B).hom) ≫
          eqToHom (Blocks.obj_blockTensors_snoc G.groupedTensors B.blockTensors).symm := rfl

end CategoryTheory.MonoidalCategory.OrderedTensor.Groups
end
end source_GroupFoldMap

/- Source proof segment: GroupFoldCountSquares -/
section source_GroupFoldCountSquares
/-!
# Original count-transport squares for grouped row folds

The actual grouped-to-flat input map and flat-to-grouped middle map
retain the original appended row split. Their successor squares follow
from the complete original input family/count equalities.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor.Groups

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The original grouped input count map retains the complete original concatenated input split. -/
theorem groupedInputCount_split (G : Groups C) (B : Blocks C) :
    (groupedInputCountIso (Groups.snoc G B)).hom ≫ (Blocks.concatInputSplit G.flat B).hom =
      (appendIso G.groupedInputs.inputs B.inputs).hom ≫
        ((groupedInputCountIso G).hom ⊗ₘ 𝟙 (obj B.inputs)) := by
  have h := appendIso_count_transport G.flat_groupedInputs_count.symm
    G.groupedInputs.inputs G.flat.inputs B.inputs (groupedInput_count_objects G)
  simp only [Blocks.concatInputSplit, Iso.trans_hom]
  have hc : (groupedInputCountIso (Groups.snoc G B)).hom ≫
        (Blocks.concatInputsIso G.flat B).hom =
      eqToHom (append_obj_congr G.flat_groupedInputs_count.symm rfl
        G.groupedInputs.inputs G.flat.inputs B.inputs B.inputs
          (groupedInput_count_objects G) (fun _ => rfl)) := by
    simp only [groupedInputCountIso, congrIso, Blocks.concatInputsIso, eqToIso.hom, eqToHom_trans]
  rw [← Category.assoc, hc]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The original flat middle count map retains the complete original grouped row tensor split. -/
theorem groupedMiddleCount_split (G : Groups C) (B : Blocks C) :
    (groupedMiddleCountIso (Groups.snoc G B)).hom ≫
        (appendIso G.groupedTensors.inputs B.blockTensors).hom =
      (Blocks.concatTensorSplit G.flat B).hom ≫
        ((groupedMiddleCountIso G).hom ⊗ₘ 𝟙 (obj B.blockTensors)) := by
  have h := appendIso_count_transport G.flat_groupedTensors_count
    G.flat.blockTensors G.groupedTensors.inputs B.blockTensors (flatMiddle_count_objects G)
  have hc : (groupedMiddleCountIso (Groups.snoc G B)).hom =
      (Blocks.concatBlockTensorsIso G.flat B).hom ≫
        eqToHom (append_obj_congr G.flat_groupedTensors_count rfl
          G.flat.blockTensors G.groupedTensors.inputs B.blockTensors B.blockTensors
            (flatMiddle_count_objects G) (fun _ => rfl)) := by
    simp only [groupedMiddleCountIso, congrIso, Blocks.concatBlockTensorsIso,
      eqToIso.hom, eqToHom_trans]
  rw [hc, Category.assoc, h]
  simp only [Blocks.concatTensorSplit, Iso.trans_hom, Category.assoc]
  rfl

end CategoryTheory.MonoidalCategory.OrderedTensor.Groups
end
end source_GroupFoldCountSquares

/- Source proof segment: GroupFoldCoherence -/
section source_GroupFoldCoherence
/-!
# Original ordered grouping associativity of block folds

The actual grouped-input fold and tensor of row folds agree with the
actual concatenated-input fold followed by grouped middle tensoring.
Every original row, including an empty row, is retained.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor.Groups

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

theorem tensor_four_prefix_maps {A₀ A₁ A₂ A₃ A₄ B₀ B₁ : C}
    (f₀ : A₀ ⟶ A₁) (f₁ : A₁ ⟶ A₂) (f₂ : A₂ ⟶ A₃) (f₃ : A₃ ⟶ A₄) (g : B₀ ⟶ B₁) :
    (f₀ ⊗ₘ 𝟙 B₀) ≫ (f₁ ⊗ₘ g) ≫ (f₂ ⊗ₘ 𝟙 B₁) ≫ (f₃ ⊗ₘ 𝟙 B₁) =
      (f₀ ≫ f₁ ≫ f₂ ≫ f₃) ⊗ₘ g := by
  rw [tensorHom_comp_tensorHom]
  rw [tensorHom_comp_tensorHom]
  rw [tensorHom_comp_tensorHom]
  simp only [Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The complete original row grouping fold obeys its actual original associativity map law. -/
theorem grouping_fold : ∀ G : Groups C,
    (Blocks.flattenIso G.groupedInputs).hom ≫ rowFoldMap G =
      (groupedInputCountIso G).hom ≫ (Blocks.flattenIso G.flat).hom ≫
        (groupedMiddleCountIso G).hom ≫ (Blocks.flattenIso G.groupedTensors).hom
  | .nil => by
      simp only [Groups.groupedInputs, Groups.groupedTensors, Groups.flat,
        Blocks.flattenIso, rowFoldMap, groupedInputCountIso, groupedMiddleCountIso,
        congrIso, eqToIso.hom, eqToHom_refl, Iso.refl_hom, Category.id_comp]
      rfl
  | .snoc G B => by
      let J := eqToIso (Blocks.obj_blockTensors_snoc G.groupedTensors B.blockTensors)
      apply (cancel_mono J.hom).mp
      dsimp only [J, eqToIso.hom]
      simp only [Category.assoc]
      rw [rowFoldMap_snoc]
      simp only [Category.assoc]
      slice_lhs 4 5 => rw [eqToHom_trans]
      simp only [eqToHom_refl, Category.comp_id]
      dsimp only [Groups.groupedInputs, Groups.groupedTensors, Groups.flat] at *
      rw [← Category.assoc (Blocks.flattenIso (Blocks.snoc G.groupedInputs B.inputs)).hom,
        Blocks.flatten_snoc_cancel]
      dsimp only [Blocks.inputs] at *
      have ht := tensorHom_comp_tensorHom (Blocks.flattenIso G.groupedInputs).hom
        (𝟙 (obj B.inputs)) (rowFoldMap G) (Blocks.flattenIso B).hom
      simp only [Category.id_comp] at ht
      have hTensor := congrArg (fun k => (appendIso G.groupedInputs.inputs B.inputs).hom ≫ k) ht
      have hTensor' : (appendIso G.groupedInputs.inputs B.inputs).hom ≫
          ((Blocks.flattenIso G.groupedInputs).hom ⊗ₘ 𝟙 (obj B.inputs)) ≫
          (rowFoldMap G ⊗ₘ (Blocks.flattenIso B).hom) =
        (appendIso G.groupedInputs.inputs B.inputs).hom ≫
          (((Blocks.flattenIso G.groupedInputs).hom ≫ rowFoldMap G) ⊗ₘ
            (Blocks.flattenIso B).hom) := by
        simpa only [Category.assoc] using hTensor
      change ((appendIso G.groupedInputs.inputs B.inputs).hom ≫
        ((Blocks.flattenIso G.groupedInputs).hom ⊗ₘ 𝟙 (obj B.inputs))) ≫
          (rowFoldMap G ⊗ₘ (Blocks.flattenIso B).hom) = _
      simp only [Category.assoc]
      rw [hTensor']
      rw [grouping_fold G]
      have hCancel := congrArg
        (fun k => (groupedInputCountIso (Groups.snoc G B)).hom ≫
          (Blocks.flattenIso (Blocks.concat G.flat B)).hom ≫
            (groupedMiddleCountIso (Groups.snoc G B)).hom ≫ k)
        (Blocks.flatten_snoc_cancel G.groupedTensors B.blockTensors)
      have hCancel' : (groupedInputCountIso (Groups.snoc G B)).hom ≫
          (Blocks.flattenIso (Blocks.concat G.flat B)).hom ≫
            (groupedMiddleCountIso (Groups.snoc G B)).hom ≫
              (Blocks.flattenIso (Blocks.snoc G.groupedTensors B.blockTensors)).hom ≫
                eqToHom (Blocks.obj_blockTensors_snoc G.groupedTensors B.blockTensors) =
        (groupedInputCountIso (Groups.snoc G B)).hom ≫
          (Blocks.flattenIso (Blocks.concat G.flat B)).hom ≫
            (groupedMiddleCountIso (Groups.snoc G B)).hom ≫
              (appendIso G.groupedTensors.inputs B.blockTensors).hom ≫
                ((Blocks.flattenIso G.groupedTensors).hom ⊗ₘ 𝟙 (obj B.blockTensors)) := by
        simpa only [Category.assoc] using hCancel
      rw [hCancel']
      dsimp only [Groups.flat, Groups.groupedInputs, Groups.groupedTensors] at *
      have hMiddle := congrArg (fun k =>
        (groupedInputCountIso (Groups.snoc G B)).hom ≫
          (Blocks.flattenIso (G.flat.concat B)).hom ≫ k ≫
          ((Blocks.flattenIso G.groupedTensors).hom ⊗ₘ 𝟙 (obj B.blockTensors)))
        (groupedMiddleCount_split G B)
      have hConcat := congrArg (fun k =>
        (groupedInputCountIso (Groups.snoc G B)).hom ≫ k ≫
          ((groupedMiddleCountIso G).hom ⊗ₘ 𝟙 (obj B.blockTensors)) ≫
            ((Blocks.flattenIso G.groupedTensors).hom ⊗ₘ 𝟙 (obj B.blockTensors)))
        (Blocks.flattenIso_concat_split G.flat B)
      have hInput := congrArg (fun k => k ≫
        ((Blocks.flattenIso G.flat).hom ⊗ₘ (Blocks.flattenIso B).hom) ≫
          ((groupedMiddleCountIso G).hom ⊗ₘ 𝟙 (obj B.blockTensors)) ≫
            ((Blocks.flattenIso G.groupedTensors).hom ⊗ₘ 𝟙 (obj B.blockTensors)))
        (groupedInputCount_split G B)
      simp only [Category.assoc] at hMiddle hConcat hInput
      have hAll := hMiddle.trans (hConcat.trans hInput)
      symm
      calc
        _ = (appendIso G.groupedInputs.inputs B.inputs).hom ≫
            ((groupedInputCountIso G).hom ⊗ₘ 𝟙 (obj B.inputs)) ≫
              ((Blocks.flattenIso G.flat).hom ⊗ₘ (Blocks.flattenIso B).hom) ≫
                ((groupedMiddleCountIso G).hom ⊗ₘ 𝟙 (obj B.blockTensors)) ≫
                  ((Blocks.flattenIso G.groupedTensors).hom ⊗ₘ 𝟙 (obj B.blockTensors)) := by
          simpa only [Category.assoc] using hAll
        _ = _ := by
          have hf := tensor_four_prefix_maps (groupedInputCountIso G).hom
            (Blocks.flattenIso G.flat).hom (groupedMiddleCountIso G).hom
            (Blocks.flattenIso G.groupedTensors).hom (Blocks.flattenIso B).hom
          exact congrArg (fun k => (appendIso G.groupedInputs.inputs B.inputs).hom ≫ k) hf

end CategoryTheory.MonoidalCategory.OrderedTensor.Groups
end
end source_GroupFoldCoherence

/- Source proof segment: GroupTensorPositions -/
section source_GroupTensorPositions
/-!
# Original middle-block input bijections for ordered row grouping

The actual concatenated block tensor word and the actual grouped
row tensor inputs retain the same original middle-block positions.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor.Groups

variable {C : Type u}

/-- Concatenated original middle blocks enumerate their original row positions. -/
def flatMiddleEquiv : (G : Groups C) → Fin G.flat.length ≃ G.middlePositions
  | .nil => Equiv.equivEmpty (Fin 0)
  | .snoc G B => (finCongr (Blocks.concat_length G.flat B)).trans
      (finSumFinEquiv.symm.trans
        (Equiv.sumCongr G.flatMiddleEquiv (Equiv.refl (Fin B.length))))

variable [Category.{v} C] [MonoidalCategory C]

open CategoryTheory MonoidalCategory

/-- Grouped original row tensor inputs enumerate the same original middle-block positions. -/
def groupedMiddleEquiv : (G : Groups C) → Fin G.groupedTensors.totalArity ≃ G.middlePositions
  | .nil => Equiv.equivEmpty (Fin 0)
  | .snoc G B => finSumFinEquiv.symm.trans
      (Equiv.sumCongr G.groupedMiddleEquiv (Equiv.refl (Fin B.length)))

set_option backward.isDefEq.respectTransparency false in
/-- Every concatenated original middle block has its original row tensor carrier. -/
theorem flatMiddle_objects : ∀ (G : Groups C) (i : Fin G.flat.length),
    G.flat.blockTensors i = G.middleAt (G.flatMiddleEquiv i)
  | .nil, i => Fin.elim0 i
  | .snoc G B, i => by
      have ho := Blocks.concat_blockTensors G.flat B i
      let hp := finSumFinEquiv.symm (Fin.cast (Blocks.concat_length G.flat B) i)
      change (Blocks.concat G.flat B).blockTensors i =
        Sum.elim G.middleAt B.blockTensors
          ((Equiv.sumCongr G.flatMiddleEquiv (Equiv.refl (Fin B.length))) hp)
      rw [ho]
      have h : ∀ j : Fin (G.flat.length + B.length),
          Fin.append G.flat.blockTensors B.blockTensors j =
            Sum.elim G.middleAt B.blockTensors
              ((Equiv.sumCongr G.flatMiddleEquiv (Equiv.refl (Fin B.length)))
                (finSumFinEquiv.symm j)) := by
        intro j
        refine Fin.addCases (fun k => ?_) (fun k => ?_) j
        · rw [Fin.append_left, finSumFinEquiv_symm_apply_castAdd]
          exact flatMiddle_objects G k
        · rw [Fin.append_right, finSumFinEquiv_symm_apply_natAdd]
          rfl
      exact h _

/-- Every original grouped tensor input has its original middle-block carrier. -/
theorem groupedMiddle_objects : ∀ (G : Groups C) (i : Fin G.groupedTensors.totalArity),
    G.groupedTensors.inputs i = G.middleAt (G.groupedMiddleEquiv i)
  | .nil, i => Fin.elim0 i
  | .snoc G B, i => by
      change Fin.append G.groupedTensors.inputs B.blockTensors i =
        Sum.elim G.middleAt B.blockTensors
          ((Equiv.sumCongr G.groupedMiddleEquiv (Equiv.refl (Fin B.length)))
            (finSumFinEquiv.symm i))
      refine Fin.addCases (fun k => ?_) (fun k => ?_) i
      · rw [Fin.append_left, finSumFinEquiv_symm_apply_castAdd]
        exact groupedMiddle_objects G k
      · rw [Fin.append_right, finSumFinEquiv_symm_apply_natAdd]
        rfl

/-- The complete original middle-block bijection from grouped tensor
inputs to concatenated blocks. -/
def groupedToFlatMiddleEquiv (G : Groups C) :
    Fin G.groupedTensors.totalArity ≃ Fin G.flat.length :=
  G.groupedMiddleEquiv.trans G.flatMiddleEquiv.symm

/-- The original middle-block regrouping retains every original tensor carrier. -/
theorem groupedToFlatMiddle_objects (G : Groups C) (i : Fin G.groupedTensors.totalArity) :
    G.groupedTensors.inputs i = G.flat.blockTensors (G.groupedToFlatMiddleEquiv i) := by
  have hi := G.flatMiddle_objects (G.flatMiddleEquiv.symm (G.groupedMiddleEquiv i))
  have hp := congrArg G.middleAt (G.flatMiddleEquiv.apply_symm_apply (G.groupedMiddleEquiv i))
  exact (G.groupedMiddle_objects i).trans (hi.trans hp).symm

/-- The actual tensor of original row tensor carriers is the original outer row tensor word. -/
theorem groupedTensors_outer_obj_eq : ∀ G : Groups C,
    obj G.groupedTensors.blockTensors = obj G.rowTensors
  | .nil => rfl
  | .snoc G B => by
      rw [groupedTensors, Blocks.obj_blockTensors_snoc, groupedTensors_outer_obj_eq]
      change obj G.rowTensors ⊗ obj B.blockTensors =
        obj (Fin.snoc G.rowTensors (obj B.blockTensors))
      rw [obj_succ]
      change obj G.rowTensors ⊗ obj B.blockTensors =
        obj (Fin.init (Fin.snoc (α := fun _ : Fin (G.length + 1) => C)
          G.rowTensors (obj B.blockTensors))) ⊗
          Fin.snoc (α := fun _ : Fin (G.length + 1) => C)
            G.rowTensors (obj B.blockTensors) (Fin.last G.length)
      rw [Fin.init_snoc, Fin.snoc_last]

end CategoryTheory.MonoidalCategory.OrderedTensor.Groups
end
end source_GroupTensorPositions

/- Source proof segment: OriginalGroupCountEquivalences -/
section source_OriginalGroupCountEquivalences
/-!
# Actual count-cast input bijections of original ordered row groups

Both original group bijections preserve the complete input order.
Their exact maps are the original count transports, with every
empty row and block retained.
-/

@[expose] public section

set_option autoImplicit false

universe v u w

namespace CategoryTheory.MonoidalCategory.OrderedTensor

/-- The original sum input equivalence respects the actual whole and prefix count transports. -/
theorem snocIndexEquiv_count {a b k m : ℕ} {P : Type w}
    (hm : m = a + k) (ha : a = b) (hb : m = b + k)
    (e : Fin a ≃ P) (d : Fin b ≃ P)
    (he : ∀ i, e i = d (Fin.cast ha i)) (i : Fin m) :
    ((finCongr hm).trans
      (finSumFinEquiv.symm.trans (Equiv.sumCongr e (Equiv.refl (Fin k))))) i =
      (finSumFinEquiv.symm.trans (Equiv.sumCongr d (Equiv.refl (Fin k)))) (Fin.cast hb i) := by
  subst m
  subst b
  have hed : e = d := by
    apply Equiv.ext
    intro j
    exact he j
  subst d
  rfl

namespace Groups

variable {C : Type u}

/-- Every actual concatenated row input has its same original position
under the group count cast. -/
theorem flatInputEquiv_cast : ∀ (G : Groups C) (i : Fin G.flat.totalArity),
    G.flatInputEquiv i = G.groupedInputEquiv (Fin.cast G.flat_groupedInputs_count i)
  | .nil, i => Fin.elim0 i
  | .snoc G B, i =>
      snocIndexEquiv_count (Blocks.concat_totalArity G.flat B)
        G.flat_groupedInputs_count (Groups.snoc G B).flat_groupedInputs_count
        G.flatInputEquiv G.groupedInputEquiv (flatInputEquiv_cast G) i

/-- The complete actual grouped-to-flat input bijection is its original total-count cast. -/
theorem groupedToFlatInputEquiv_eq_count (G : Groups C) :
    G.groupedToFlatInputEquiv = finCongr G.flat_groupedInputs_count.symm := by
  apply Equiv.ext
  intro i
  apply G.flatInputEquiv.injective
  have h := flatInputEquiv_cast G (Fin.cast G.flat_groupedInputs_count.symm i)
  have hi : Fin.cast G.flat_groupedInputs_count
      (Fin.cast G.flat_groupedInputs_count.symm i) = i := by
    apply Fin.ext
    rfl
  rw [hi] at h
  exact (G.flatInputEquiv.apply_symm_apply (G.groupedInputEquiv i)).trans h.symm

variable [Category.{v} C] [MonoidalCategory C]

/-- Every actual concatenated middle-block position has the same original
grouped count-cast position. -/
theorem flatMiddleEquiv_cast : ∀ (G : Groups C) (i : Fin G.flat.length),
    G.flatMiddleEquiv i = G.groupedMiddleEquiv (Fin.cast G.flat_groupedTensors_count i)
  | .nil, i => Fin.elim0 i
  | .snoc G B, i =>
      snocIndexEquiv_count (Blocks.concat_length G.flat B)
        G.flat_groupedTensors_count (Groups.snoc G B).flat_groupedTensors_count
        G.flatMiddleEquiv G.groupedMiddleEquiv (flatMiddleEquiv_cast G) i

/-- The complete actual grouped-to-flat middle-block bijection is its original total-count cast. -/
theorem groupedToFlatMiddleEquiv_eq_count (G : Groups C) :
    G.groupedToFlatMiddleEquiv = finCongr G.flat_groupedTensors_count.symm := by
  apply Equiv.ext
  intro i
  apply G.flatMiddleEquiv.injective
  have h := flatMiddleEquiv_cast G (Fin.cast G.flat_groupedTensors_count.symm i)
  have hi : Fin.cast G.flat_groupedTensors_count
      (Fin.cast G.flat_groupedTensors_count.symm i) = i := by
    apply Fin.ext
    rfl
  rw [hi] at h
  exact (G.flatMiddleEquiv.apply_symm_apply (G.groupedMiddleEquiv i)).trans h.symm

end Groups

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OriginalGroupCountEquivalences

/- Source proof segment: TripleInputMaps -/
section source_TripleInputMaps
/-!
# Actual original triple input maps to ordered groups

The two original sigma input associations map to the same concatenated
word. The mapped-flatten route retains each original row input map.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The original right-associated triple tensor maps to its complete concatenated input word. -/
noncomputable def rightTripleWordIso
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    finiteObj ((FiniteFamily.mapFlattenFlatten (C := C)).obj X) ≅
      obj (groupsOfFiniteFamilies X).flat.inputs :=
  isoEquiv (rightTripleWordEquiv X) (fun i => eqToIso (rightTripleWord_objects X i))

/-- The original left-associated triple tensor maps to the same concatenated original input word. -/
noncomputable def leftTripleWordIso
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    finiteObj ((FiniteFamily.flattenFlatten (C := C)).obj X) ≅
      obj (groupsOfFiniteFamilies X).flat.inputs :=
  isoEquiv (leftTripleWordEquiv X) (fun i => eqToIso (leftTripleWord_objects X i))

/-- The actual mapped-flatten word maps to the complete original grouped row input word. -/
noncomputable def mappedRowsGroupedIso
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    obj (blocksOfFiniteFamily (mappedFlattenRows X)).inputs ≅
      obj (groupsOfFiniteFamilies X).groupedInputs.inputs :=
  isoEquiv (mappedRowsToGroupedInputEquiv X)
    (fun i => eqToIso (mappedRowsToGroupedInput_objects X i))

set_option backward.isDefEq.respectTransparency false in
theorem groupedInputCountIso_input (G : Groups C) :
    Groups.groupedInputCountIso G =
      isoEquiv G.groupedToFlatInputEquiv (fun i => eqToIso (G.groupedToFlatInput_objects i)) := by
  have h := isoEquiv_eq_congr G.groupedToFlatInputEquiv_eq_count
    G.groupedToFlatInput_objects (Groups.groupedInput_count_objects G)
  have hc := isoEquiv_finCongr G.flat_groupedInputs_count.symm
    G.groupedInputs.inputs G.flat.inputs (Groups.groupedInput_count_objects G)
  exact (h.trans hc).symm

set_option backward.isDefEq.respectTransparency false in
theorem mappedRows_grouped_then_flat
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    mappedRowsGroupedIso X ≪≫ Groups.groupedInputCountIso (groupsOfFiniteFamilies X) =
      isoEquiv (mappedRowsToFlatInputEquiv X)
        (fun i => eqToIso (mappedRowsToFlatInput_objects X i)) := by
  rw [groupedInputCountIso_input]
  unfold mappedRowsGroupedIso
  rw [isoEquiv_trans]
  have he : (mappedRowsToGroupedInputEquiv X).trans
      (groupsOfFiniteFamilies X).groupedToFlatInputEquiv = mappedRowsToFlatInputEquiv X := by
    apply Equiv.ext
    intro i
    simp only [mappedRowsToGroupedInputEquiv, mappedRowsToFlatInputEquiv,
      rightGroupedTripleInputEquiv, rightTripleInputEquiv, Groups.groupedToFlatInputEquiv,
      Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.apply_symm_apply]
  apply isoEquiv_congr he
  intro i
  exact eqToIso_chain_heq (mappedRowsToGroupedInput_objects X i)
    ((groupsOfFiniteFamilies X).groupedToFlatInput_objects (mappedRowsToGroupedInputEquiv X i))
    (mappedRowsToFlatInput_objects X i)

set_option backward.isDefEq.respectTransparency false in
theorem rightTripleWordIso_rows
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    flattenToWordIso (mappedFlattenRows X) ≪≫ mappedRowsGroupedIso X ≪≫
        Groups.groupedInputCountIso (groupsOfFiniteFamilies X) = rightTripleWordIso X := by
  rw [mappedRows_grouped_then_flat]
  unfold flattenToWordIso rightTripleWordIso
  rw [isoEquiv_trans]
  apply isoEquiv_congr (mappedRowsWord_regrouping X)
  intro i
  exact eqToIso_chain_heq (flattenWord_objects (mappedFlattenRows X) i)
    (mappedRowsToFlatInput_objects X (flattenWordEquiv (mappedFlattenRows X) i))
    (rightTripleWord_objects X i)

set_option backward.isDefEq.respectTransparency false in
theorem rowInputFiberMap_groupedIso
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    (rowInputFiberMap (X.obj ∘ enumeration X)).inputMap = (mappedRowsGroupedIso X).hom := by
  rw [rowInputFiberMap_wordMap]
  exact (isoEquiv_hom (mappedRowsToGroupedInputEquiv X)
    (fun i => eqToIso (mappedRowsToGroupedInput_objects X i))).symm

set_option backward.isDefEq.respectTransparency false in
/-- The original sigma reassociation retains exactly the same original triple tensor input map. -/
theorem tripleWordIso_regrouping
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    finiteMap ((FiniteFamily.flattenAssocIso (C := C)).hom.app X) ≫ (leftTripleWordIso X).hom =
      (rightTripleWordIso X).hom := by
  rw [leftTripleWordIso, rightTripleWordIso, isoEquiv_hom, isoEquiv_hom]
  unfold finiteMap
  rw [mapEquiv_comp]
  apply mapEquiv_congr (tripleWord_regrouping X)
  intro i
  have h := enumeratedMap_heq ((FiniteFamily.flattenAssocIso (C := C)).hom.app X) i
  have hi : HEq (enumeratedMap ((FiniteFamily.flattenAssocIso (C := C)).hom.app X) i)
      (𝟙 (orderedFamily ((FiniteFamily.mapFlattenFlatten (C := C)).obj X) i)) := h
  have ht := comp_eqToHom_heq
    (enumeratedMap ((FiniteFamily.flattenAssocIso (C := C)).hom.app X) i)
    (leftTripleWord_objects X
      (enumeratedEquiv ((FiniteFamily.flattenAssocIso (C := C)).hom.app X) i))
  exact (ht.trans hi).trans
    (eqToHom_heq_id_dom _ _ (rightTripleWord_objects X i)).symm

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_TripleInputMaps

/- Source proof segment: RowTensorFields -/
section source_RowTensorFields
/-!
# Actual pointwise tensor carriers of original ordered finite blocks

Every original outer slot retains the actual finite tensor carrier
of its original inner finite family, including empty inner blocks.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u}

/-- The generic original snoc input word respects its actual prefix count and fields. -/
theorem snocFamily_fields {a n : ℕ} (h : a = n) (U : Fin a → C)
    (V : Fin (n + 1) → C) (A : C)
    (hU : ∀ i, U i = V (Fin.cast h i).castSucc) (hA : A = V (Fin.last n))
    (j : Fin (a + 1)) :
    Fin.snoc (α := fun _ : Fin (a + 1) => C) U A j =
      V (Fin.cast (congrArg (fun k => k + 1) h) j) := by
  subst n
  change Fin.snoc (α := fun _ : Fin (a + 1) => C) U A j = V j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · exact (Fin.snoc_last (α := fun _ : Fin (a + 1) => C) A U).trans hA
  · exact (Fin.snoc_castSucc (α := fun _ : Fin (a + 1) => C) A U i).trans (hU i)

variable [Category.{v} C] [MonoidalCategory C]

/-- Every original block tensor is the actual finite tensor of its original input family. -/
theorem blocksOfFamily_blockTensors : ∀ {n : ℕ} (F : Fin n → FiniteFamily C)
    (j : Fin (blocksOfFamily F).length),
    (blocksOfFamily F).blockTensors j =
      finiteObj (F (Fin.cast (blocksOfFamily_length F) j))
  | 0, _, j => Fin.elim0 j
  | n + 1, F, j => by
      change Fin.snoc
        (α := fun _ : Fin ((blocksOfFamily (Fin.init F)).length + 1) => C)
        (blocksOfFamily (Fin.init F)).blockTensors (finiteObj (F (Fin.last n))) j = _
      exact snocFamily_fields (blocksOfFamily_length (Fin.init F))
        (blocksOfFamily (Fin.init F)).blockTensors (fun i => finiteObj (F i))
        (finiteObj (F (Fin.last n)))
        (fun i => blocksOfFamily_blockTensors (Fin.init F) i) rfl j

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_RowTensorFields

/- Source proof segment: RowMiddleTensor -/
section source_RowMiddleTensor
/-!
# Original middle index bijection and tensor carriers of a finite row

The row retains its original inner-family enumeration. The index
bijection and every tensor object use the actual original data.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u}

/-- An actual finite row retains exactly its original middle input count. -/
theorem blocksOfFiniteFamily_length (Y : FiniteFamily (FiniteFamily C)) :
    (blocksOfFiniteFamily Y).length = arity Y :=
  blocksOfFamily_length (Y.obj ∘ enumeration Y)

/-- The actual original middle input bijection of a finite row. -/
noncomputable def rowMiddleEquiv (Y : FiniteFamily (FiniteFamily C)) :
    Fin (blocksOfFiniteFamily Y).length ≃ Y.index :=
  (finCongr (blocksOfFiniteFamily_length Y)).trans (enumeration Y)

/-- Every actual row middle slot has its original enumerated input label. -/
theorem rowMiddleEquiv_apply (Y : FiniteFamily (FiniteFamily C))
    (j : Fin (blocksOfFiniteFamily Y).length) :
    rowMiddleEquiv Y j = enumeration Y (Fin.cast (blocksOfFiniteFamily_length Y) j) := rfl

/-- Every original middle input label has its actual original ordered row slot. -/
theorem rowMiddleEquiv_symm_apply (Y : FiniteFamily (FiniteFamily C)) (i : Y.index) :
    (rowMiddleEquiv Y).symm i =
      Fin.cast (blocksOfFiniteFamily_length Y).symm ((enumeration Y).symm i) := rfl

variable [Category.{v} C] [MonoidalCategory C]

/-- Every actual row block tensor is the finite tensor carrier of its original middle input. -/
theorem rowMiddleEquiv_blockTensors (Y : FiniteFamily (FiniteFamily C))
    (j : Fin (blocksOfFiniteFamily Y).length) :
    (blocksOfFiniteFamily Y).blockTensors j = finiteObj (Y.obj (rowMiddleEquiv Y j)) :=
  blocksOfFamily_blockTensors (Y.obj ∘ enumeration Y) j

/-- The actual tensor of row block tensors is the finite tensor of the original carrier family. -/
theorem rowMiddle_tensor_obj_eq (Y : FiniteFamily (FiniteFamily C)) :
    obj (blocksOfFiniteFamily Y).blockTensors =
      finiteObj (⟨Y.index, fun i => finiteObj (Y.obj i)⟩ : FiniteFamily C) :=
  blocksOfFamily_tensors (Y.obj ∘ enumeration Y)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_RowMiddleTensor

/- Source proof segment: GroupMiddleGeometry -/
section source_GroupMiddleGeometry
/-!
# Original middle-family geometry of ordered triple grouping

Every concatenated middle block and grouped tensor input identifies
its original outer and middle labels. Its object is the actual finite
tensor carrier of that original inner finite family.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u}

/-- The actual middle positions of original rows retain both original input labels. -/
noncomputable def groupsMiddleOriginalPositions :
    {n : ℕ} → (X : Fin n → FiniteFamily (FiniteFamily C)) →
      (groupsOfFamilies X).middlePositions ≃ OriginalPositions X
  | 0, X => by
      haveI : IsEmpty (OriginalPositions X) := ⟨fun p => p.1.elim0⟩
      exact (Equiv.equivEmpty (OriginalPositions X)).symm
  | n + 1, X =>
      (Equiv.sumCongr (groupsMiddleOriginalPositions (Fin.init X))
        (rowMiddleEquiv (X (Fin.last n)))).trans (positionsSnocEquiv X)

variable [Category.{v} C] [MonoidalCategory C]

/-- Every original middle position carries its original inner finite tensor object. -/
theorem groupsMiddleOriginalPosition_objects :
    ∀ {n : ℕ} (X : Fin n → FiniteFamily (FiniteFamily C))
      (p : (groupsOfFamilies X).middlePositions),
      (groupsOfFamilies X).middleAt p =
        finiteObj ((X (groupsMiddleOriginalPositions X p).1).obj
          (groupsMiddleOriginalPositions X p).2)
  | 0, _, p => Empty.elim p
  | n + 1, X, p => by
      cases p with
      | inl p =>
          change (groupsOfFamilies (Fin.init X)).middleAt p =
            finiteObj (((Fin.init X) (groupsMiddleOriginalPositions (Fin.init X) p).1).obj
              (groupsMiddleOriginalPositions (Fin.init X) p).2)
          exact groupsMiddleOriginalPosition_objects (Fin.init X) p
      | inr p =>
          change (blocksOfFiniteFamily (X (Fin.last n))).blockTensors p =
            finiteObj ((X (Fin.last n)).obj (rowMiddleEquiv (X (Fin.last n)) p))
          exact rowMiddleEquiv_blockTensors (X (Fin.last n)) p

/-- The actual original family of middle finite families in a triple family. -/
abbrev flattenedMiddleFamily (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    FiniteFamily (FiniteFamily C) := (FiniteFamily.flatten (C := FiniteFamily C)).obj X

/-- The actual finite tensor carrier in every original middle-family input. -/
noncomputable def middleCarrierFamily (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    FiniteFamily C :=
  ⟨(flattenedMiddleFamily X).index, fun p => finiteObj ((flattenedMiddleFamily X).obj p)⟩

/-- Every original concatenated middle block identifies its original outer and middle labels. -/
noncomputable def tripleMiddleInputEquiv
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    Fin (groupsOfFiniteFamilies X).flat.length ≃ (flattenedMiddleFamily X).index :=
  (groupsOfFiniteFamilies X).flatMiddleEquiv.trans
    ((groupsMiddleOriginalPositions (X.obj ∘ enumeration X)).trans
      (originalOuterPositionsEquiv (C := FiniteFamily C) X))

/-- Every original grouped tensor input identifies those same original outer and middle labels. -/
noncomputable def groupedTripleMiddleEquiv
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    Fin (groupsOfFiniteFamilies X).groupedTensors.totalArity ≃ (flattenedMiddleFamily X).index :=
  (groupsOfFiniteFamilies X).groupedMiddleEquiv.trans
    ((groupsMiddleOriginalPositions (X.obj ∘ enumeration X)).trans
      (originalOuterPositionsEquiv (C := FiniteFamily C) X))

/-- Every concatenated original middle block has its actual original finite tensor carrier. -/
theorem tripleMiddleInput_objects
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (j : Fin (groupsOfFiniteFamilies X).flat.length) :
    (groupsOfFiniteFamilies X).flat.blockTensors j =
      (middleCarrierFamily X).obj (tripleMiddleInputEquiv X j) :=
  ((groupsOfFiniteFamilies X).flatMiddle_objects j).trans
    (groupsMiddleOriginalPosition_objects (X.obj ∘ enumeration X)
      ((groupsOfFiniteFamilies X).flatMiddleEquiv j))

/-- Every grouped original tensor input has the same actual original finite tensor carrier. -/
theorem groupedTripleMiddle_objects
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (j : Fin (groupsOfFiniteFamilies X).groupedTensors.totalArity) :
    (groupsOfFiniteFamilies X).groupedTensors.inputs j =
      (middleCarrierFamily X).obj (groupedTripleMiddleEquiv X j) :=
  ((groupsOfFiniteFamilies X).groupedMiddle_objects j).trans
    (groupsMiddleOriginalPosition_objects (X.obj ∘ enumeration X)
      ((groupsOfFiniteFamilies X).groupedMiddleEquiv j))

/-- The original enumerated middle tensor carriers map to the actual concatenated middle word. -/
noncomputable def middleCarrierWordEquiv
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    Fin (arity (middleCarrierFamily X)) ≃ Fin (groupsOfFiniteFamilies X).flat.length :=
  (enumeration (middleCarrierFamily X)).trans (tripleMiddleInputEquiv X).symm

/-- The original enumerated middle tensor carriers map to the actual grouped tensor inputs. -/
noncomputable def groupedMiddleCarrierWordEquiv
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    Fin (arity (middleCarrierFamily X)) ≃
      Fin (groupsOfFiniteFamilies X).groupedTensors.totalArity :=
  (enumeration (middleCarrierFamily X)).trans (groupedTripleMiddleEquiv X).symm

/-- The original middle-carrier enumeration retains every concatenated original tensor object. -/
theorem middleCarrierWord_objects
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) (i : Fin (arity (middleCarrierFamily X))) :
    orderedFamily (middleCarrierFamily X) i =
      (groupsOfFiniteFamilies X).flat.blockTensors (middleCarrierWordEquiv X i) := by
  change (middleCarrierFamily X).obj (enumeration (middleCarrierFamily X) i) =
    (groupsOfFiniteFamilies X).flat.blockTensors
      ((tripleMiddleInputEquiv X).symm (enumeration (middleCarrierFamily X) i))
  have h := tripleMiddleInput_objects X
    ((tripleMiddleInputEquiv X).symm (enumeration (middleCarrierFamily X) i))
  have hp := congrArg (middleCarrierFamily X).obj
    ((tripleMiddleInputEquiv X).apply_symm_apply (enumeration (middleCarrierFamily X) i))
  exact (h.trans hp).symm

/-- The original middle-carrier enumeration retains every grouped original tensor object. -/
theorem groupedMiddleCarrierWord_objects
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) (i : Fin (arity (middleCarrierFamily X))) :
    orderedFamily (middleCarrierFamily X) i =
      (groupsOfFiniteFamilies X).groupedTensors.inputs (groupedMiddleCarrierWordEquiv X i) := by
  change (middleCarrierFamily X).obj (enumeration (middleCarrierFamily X) i) =
    (groupsOfFiniteFamilies X).groupedTensors.inputs
      ((groupedTripleMiddleEquiv X).symm (enumeration (middleCarrierFamily X) i))
  have h := groupedTripleMiddle_objects X
    ((groupedTripleMiddleEquiv X).symm (enumeration (middleCarrierFamily X) i))
  have hp := congrArg (middleCarrierFamily X).obj
    ((groupedTripleMiddleEquiv X).apply_symm_apply (enumeration (middleCarrierFamily X) i))
  exact (h.trans hp).symm

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_GroupMiddleGeometry

/- Source proof segment: GroupRowCarriers -/
section source_GroupRowCarriers
/-!
# Original outer row tensor carriers of triple grouping

Each original row tensor is the finite tensor of the original inner
finite tensor carriers. The entire outer row tensor word retains the
original outer enumeration and every empty row tensor unit.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The original family of finite tensor carriers in one original row. -/
noncomputable def rowCarrierFamily (Y : FiniteFamily (FiniteFamily C)) : FiniteFamily C :=
  ⟨Y.index, fun i => finiteObj (Y.obj i)⟩

/-- The original outer family retains each original row tensor carrier. -/
noncomputable def outerRowCarrierFamily
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) : FiniteFamily C :=
  ⟨X.index, fun i => finiteObj (rowCarrierFamily (X.obj i))⟩

/-- The tensor of actual row carriers retains the original literal outer row order. -/
theorem groupsOfFamilies_rowTensors_obj :
    ∀ {n : ℕ} (X : Fin n → FiniteFamily (FiniteFamily C)),
      obj (groupsOfFamilies X).rowTensors =
        obj (fun i => obj (blocksOfFiniteFamily (X i)).blockTensors)
  | 0, _ => rfl
  | n + 1, X => by
      change obj (Fin.snoc (α := fun _ : Fin ((groupsOfFamilies (Fin.init X)).length + 1) => C)
        (groupsOfFamilies (Fin.init X)).rowTensors
        (obj (blocksOfFiniteFamily (X (Fin.last n))).blockTensors)) = _
      rw [obj_succ]
      change obj (Fin.init (Fin.snoc
          (α := fun _ : Fin ((groupsOfFamilies (Fin.init X)).length + 1) => C)
          (groupsOfFamilies (Fin.init X)).rowTensors
          (obj (blocksOfFiniteFamily (X (Fin.last n))).blockTensors))) ⊗
          Fin.snoc (α := fun _ : Fin ((groupsOfFamilies (Fin.init X)).length + 1) => C)
            (groupsOfFamilies (Fin.init X)).rowTensors
            (obj (blocksOfFiniteFamily (X (Fin.last n))).blockTensors)
            (Fin.last (groupsOfFamilies (Fin.init X)).length) = _
      rw [Fin.init_snoc, Fin.snoc_last, groupsOfFamilies_rowTensors_obj]
      rfl

/-- Each actual original row tensor is exactly its original finite family of inner carriers. -/
theorem actualRowCarrier_eq (Y : FiniteFamily (FiniteFamily C)) :
    obj (blocksOfFiniteFamily Y).blockTensors = finiteObj (rowCarrierFamily Y) :=
  rowMiddle_tensor_obj_eq Y

/-- The original complete outer row tensor word is the original finite outer carrier family. -/
theorem groupsOuterRowCarrier_eq
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    obj (groupsOfFiniteFamilies X).rowTensors = finiteObj (outerRowCarrierFamily X) := by
  change obj (groupsOfFamilies (X.obj ∘ enumeration X)).rowTensors = _
  rw [groupsOfFamilies_rowTensors_obj]
  have hf : (fun i : Fin (arity X) =>
      obj (blocksOfFiniteFamily (X.obj (enumeration X i))).blockTensors) =
      (fun i : Fin (arity X) => finiteObj (rowCarrierFamily (X.obj (enumeration X i)))) := by
    funext i
    exact actualRowCarrier_eq _
  exact congrArg obj hf

/-- The original tensor of grouped row tensor carriers is the actual
original outer finite carrier. -/
theorem groupedOuterRowCarrier_eq
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    obj (groupsOfFiniteFamilies X).groupedTensors.blockTensors =
      finiteObj (outerRowCarrierFamily X) :=
  ((groupsOfFiniteFamilies X).groupedTensors_outer_obj_eq).trans (groupsOuterRowCarrier_eq X)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_GroupRowCarriers

/- Source proof segment: TripleCarrierFamilies -/
section source_TripleCarrierFamilies
/-!
# Actual intermediate finite tensor families of original triple grouping

The original map-tensor and flatten-map carrier families are the actual
families of original inner tensor objects. Their input words retain
the same original outer/middle indices as the concatenated row tensors.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The actual original finite family obtained by tensoring each original inner family. -/
noncomputable def mappedTensorRows
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) : FiniteFamily (FiniteFamily C) :=
  (FiniteFamily.map (FiniteFamily.map (finiteTensorFunctor (C := C)))).obj X

/-- The original row carrier family is the actual original map-tensor family. -/
theorem rowCarrierFamily_actual (Y : FiniteFamily (FiniteFamily C)) :
    rowCarrierFamily Y = (FiniteFamily.map (finiteTensorFunctor (C := C))).obj Y := rfl

/-- Mapping the actual tensor to the original flattened middle family
gives its original carriers. -/
theorem middleCarrierFamily_actual_map
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    middleCarrierFamily X =
      (FiniteFamily.map (finiteTensorFunctor (C := C))).obj (flattenedMiddleFamily X) := rfl

/-- Flattening the actual original mapped tensor rows gives that same
original middle carrier family. -/
theorem middleCarrierFamily_actual_flatten
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    middleCarrierFamily X = (FiniteFamily.flatten (C := C)).obj (mappedTensorRows X) := rfl

/-- The original outer row carriers are the actual original outer map-tensor family. -/
theorem outerRowCarrierFamily_actual
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    outerRowCarrierFamily X =
      (FiniteFamily.map (finiteTensorFunctor (C := C))).obj (mappedTensorRows X) := rfl

/-- The original mapped tensor row word keeps the complete original outer and middle labels. -/
noncomputable def mappedTensorRowsOriginalEquiv
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    Fin (blocksOfFiniteFamily (mappedTensorRows X)).totalArity ≃ (middleCarrierFamily X).index :=
  nestedPositionsEquiv (mappedTensorRows X)

/-- Every original mapped tensor row input is its original inner finite tensor carrier. -/
theorem mappedTensorRowsOriginal_objects
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (i : Fin (blocksOfFiniteFamily (mappedTensorRows X)).totalArity) :
    (blocksOfFiniteFamily (mappedTensorRows X)).inputs i =
      (middleCarrierFamily X).obj (mappedTensorRowsOriginalEquiv X i) :=
  nestedPositions_objects (mappedTensorRows X) i

/-- The complete original mapped tensor row word maps to concatenated original middle blocks. -/
noncomputable def mappedTensorRowsToFlatEquiv
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    Fin (blocksOfFiniteFamily (mappedTensorRows X)).totalArity ≃
      Fin (groupsOfFiniteFamilies X).flat.length :=
  (mappedTensorRowsOriginalEquiv X).trans (tripleMiddleInputEquiv X).symm

/-- The complete original mapped tensor row word maps to grouped original tensor inputs. -/
noncomputable def mappedTensorRowsToGroupedEquiv
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    Fin (blocksOfFiniteFamily (mappedTensorRows X)).totalArity ≃
      Fin (groupsOfFiniteFamilies X).groupedTensors.totalArity :=
  (mappedTensorRowsOriginalEquiv X).trans (groupedTripleMiddleEquiv X).symm

/-- Every original mapped tensor row input keeps its concatenated original middle tensor object. -/
theorem mappedTensorRowsToFlat_objects
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (i : Fin (blocksOfFiniteFamily (mappedTensorRows X)).totalArity) :
    (blocksOfFiniteFamily (mappedTensorRows X)).inputs i =
      (groupsOfFiniteFamilies X).flat.blockTensors (mappedTensorRowsToFlatEquiv X i) := by
  have ht := tripleMiddleInput_objects X
    ((tripleMiddleInputEquiv X).symm (mappedTensorRowsOriginalEquiv X i))
  have hp := congrArg (middleCarrierFamily X).obj
    ((tripleMiddleInputEquiv X).apply_symm_apply (mappedTensorRowsOriginalEquiv X i))
  exact (mappedTensorRowsOriginal_objects X i).trans (ht.trans hp).symm

/-- Every original mapped tensor row input keeps its grouped original tensor object. -/
theorem mappedTensorRowsToGrouped_objects
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (i : Fin (blocksOfFiniteFamily (mappedTensorRows X)).totalArity) :
    (blocksOfFiniteFamily (mappedTensorRows X)).inputs i =
      (groupsOfFiniteFamilies X).groupedTensors.inputs (mappedTensorRowsToGroupedEquiv X i) := by
  have ht := groupedTripleMiddle_objects X
    ((groupedTripleMiddleEquiv X).symm (mappedTensorRowsOriginalEquiv X i))
  have hp := congrArg (middleCarrierFamily X).obj
    ((groupedTripleMiddleEquiv X).apply_symm_apply (mappedTensorRowsOriginalEquiv X i))
  exact (mappedTensorRowsOriginal_objects X i).trans (ht.trans hp).symm

/-- The actual original mapped tensor row outer carrier is the original finite outer row carrier. -/
theorem mappedTensorRows_outerCarrier_eq
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    obj (blocksOfFiniteFamily (mappedTensorRows X)).blockTensors =
      finiteObj (outerRowCarrierFamily X) :=
  blocksOfFamily_tensors ((mappedTensorRows X).obj ∘ enumeration (mappedTensorRows X))

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_TripleCarrierFamilies

/- Source proof segment: TripleMiddleMaps -/
section source_TripleMiddleMaps
/-!
# Actual original middle tensor maps of triple grouping

Both middle word comparisons retain every original outer and middle
input label and its actual finite tensor carrier. Their group-count
comparison is the original order-preserving transport.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The actual original middle tensor carrier maps to the concatenated original block tensors. -/
noncomputable def middleCarrierWordIso
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    finiteObj (middleCarrierFamily X) ≅ obj (groupsOfFiniteFamilies X).flat.blockTensors :=
  isoEquiv (middleCarrierWordEquiv X) (fun i => eqToIso (middleCarrierWord_objects X i))

/-- The actual original middle tensor carrier maps to the grouped original tensor inputs. -/
noncomputable def groupedMiddleCarrierWordIso
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    finiteObj (middleCarrierFamily X) ≅ obj (groupsOfFiniteFamilies X).groupedTensors.inputs :=
  isoEquiv (groupedMiddleCarrierWordEquiv X)
    (fun i => eqToIso (groupedMiddleCarrierWord_objects X i))

set_option backward.isDefEq.respectTransparency false in
/-- The original middle count map is the exact inverse of its full original grouping input map. -/
theorem groupedMiddleCountIso_input (G : Groups C) :
    Groups.groupedMiddleCountIso G =
      (isoEquiv G.groupedToFlatMiddleEquiv
        (fun i => eqToIso (G.groupedToFlatMiddle_objects i))).symm := by
  have h := isoEquiv_eq_congr G.groupedToFlatMiddleEquiv_eq_count
    G.groupedToFlatMiddle_objects
    (fun i => (Groups.flatMiddle_count_objects G
      (Fin.cast G.flat_groupedTensors_count.symm i)).symm)
  rw [isoEquiv_finCongr] at h
  have hh := congrArg Iso.symm h
  exact hh.symm

set_option backward.isDefEq.respectTransparency false in
/-- Concatenated original middle tensors and grouped middle inputs form
the same actual carrier map. -/
theorem middleWordIso_grouping
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    middleCarrierWordIso X ≪≫ Groups.groupedMiddleCountIso (groupsOfFiniteFamilies X) =
      groupedMiddleCarrierWordIso X := by
  have hCount : Groups.groupedMiddleCountIso (groupsOfFiniteFamilies X) =
      isoEquiv (groupsOfFiniteFamilies X).groupedToFlatMiddleEquiv.symm
        (fun i => eqToIso ((congrArg (groupsOfFiniteFamilies X).flat.blockTensors
          ((groupsOfFiniteFamilies X).groupedToFlatMiddleEquiv.apply_symm_apply i)).symm.trans
            ((groupsOfFiniteFamilies X).groupedToFlatMiddle_objects
              ((groupsOfFiniteFamilies X).groupedToFlatMiddleEquiv.symm i)).symm)) := by
    rw [groupedMiddleCountIso_input, isoEquiv_eq_inverse]
  rw [hCount]
  unfold middleCarrierWordIso groupedMiddleCarrierWordIso
  rw [isoEquiv_trans]
  have he : (middleCarrierWordEquiv X).trans
      (groupsOfFiniteFamilies X).groupedToFlatMiddleEquiv.symm =
        groupedMiddleCarrierWordEquiv X := by
    apply Equiv.ext
    intro i
    simp only [middleCarrierWordEquiv, groupedMiddleCarrierWordEquiv,
      tripleMiddleInputEquiv, groupedTripleMiddleEquiv, Groups.groupedToFlatMiddleEquiv,
      Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  exact isoEquiv_congr he _ _ (fun i => eqToIso_chain_heq (middleCarrierWord_objects X i)
    (((congrArg (groupsOfFiniteFamilies X).flat.blockTensors
      ((groupsOfFiniteFamilies X).groupedToFlatMiddleEquiv.apply_symm_apply
        (middleCarrierWordEquiv X i))).symm).trans
      ((groupsOfFiniteFamilies X).groupedToFlatMiddle_objects
      ((groupsOfFiniteFamilies X).groupedToFlatMiddleEquiv.symm
        (middleCarrierWordEquiv X i))).symm)
    (groupedMiddleCarrierWord_objects X i))

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_TripleMiddleMaps

/- Source proof segment: ActualRowFoldTensor -/
section source_ActualRowFoldTensor
/-!
# Actual tensor map of the original finite-family row folds

Each actual input-normalized row is folded by its original block
flattening. Their original outer tensor map is precisely the tensor
of the constructed original finite flattening maps, with all source
and target carrier equalities retained.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [SymmetricCategory C] in
/-- The original tensor of grouped row tensor carriers is the actual original ordered outer
row carrier. -/
theorem rowFoldTarget_eq {n : ℕ} (R : Fin n → FiniteFamily (FiniteFamily C)) :
    obj (groupsOfFamilies R).groupedTensors.blockTensors =
      obj (fun i => finiteObj (rowCarrierFamily (R i))) :=
  ((groupsOfFamilies R).groupedTensors_outer_obj_eq).trans
    ((groupsOfFamilies_rowTensors_obj R).trans
      (congrArg obj (funext (fun i => actualRowCarrier_eq (R i)))))

omit [SymmetricCategory C] in
private theorem tensorJoin_transport_heq {L L' M A B D E A' D' : C}
    (hL : L = A ⊗ D) (hL' : B ⊗ E = L')
    (hM : M = A' ⊗ D')
    (f : A ⟶ A') (g : D ⟶ D') (a : A' ⟶ B) (b : D' ⟶ E) :
    HEq (eqToHom hL ≫ (f ⊗ₘ g) ≫ eqToHom hM.symm ≫ eqToHom hM ≫
      (a ⊗ₘ b) ≫ eqToHom hL') ((f ≫ a) ⊗ₘ (g ≫ b)) := by
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have ht := tensorHom_comp_tensorHom f g a b
  simp only [← Category.assoc]
  rw [Category.assoc (eqToHom hL) (f ⊗ₘ g), ht]
  simpa only [Category.assoc] using
    (eqToHom_comp_heq (((f ≫ a) ⊗ₘ (g ≫ b)) ≫ eqToHom hL') hL).trans
      (comp_eqToHom_heq ((f ≫ a) ⊗ₘ (g ≫ b)) hL')

/-- The actual original row input normalization and block fold are its constructed original
finite flattening map. -/
theorem actualRowFold_heq (R : FiniteFamily (FiniteFamily C)) :
    HEq (flattenToWord R ≫ (Blocks.flattenIso (blocksOfFiniteFamily R)).hom)
      (finiteFlattenIso R).hom := by
  have h : HEq (finiteFlattenIso R).hom
      (flattenToWord R ≫ (Blocks.flattenIso (blocksOfFiniteFamily R)).hom) := by
    rw [finiteFlattenIso_hom]
    unfold finiteFlattenHom
    change HEq (flattenToWord R ≫ ((Blocks.flattenIso (blocksOfFiniteFamily R)).hom ≫
      eqToHom (actualRowCarrier_eq R))) _
    simpa only [Category.assoc] using comp_eqToHom_heq
      (flattenToWord R ≫ (Blocks.flattenIso (blocksOfFiniteFamily R)).hom)
      (actualRowCarrier_eq R)
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
/-- The complete actual original row-normalization tensor map followed by row folds is the
original tensor of actual
  finite flattening maps. -/
theorem actualRowFoldTensor_heq : ∀ {n : ℕ} (R : Fin n → FiniteFamily (FiniteFamily C)),
    HEq ((rowInputFiberMap R).tensorMap ≫ Groups.rowFoldMap (groupsOfFamilies R))
      (map (fun i => (finiteFlattenIso (R i)).hom)) := by
  intro n
  induction n with
  | zero =>
      intro R
      change HEq (mapEquiv (Equiv.refl (Fin 0)) (X := Fin.elim0) (Y := Fin.elim0)
        (fun i => i.elim0) ≫ 𝟙 (𝟙_ C)) (𝟙 (𝟙_ C))
      rw [mapEquiv_refl]
      exact heq_of_eq (Category.id_comp _)
  | succ n ih =>
      intro R
      let P := Fin.init R
      let G := groupsOfFamilies P
      let B := blocksOfFiniteFamily (R (Fin.last n))
      change HEq ((Blocks.FiberMap.snoc (rowInputFiberMap P) (flattenWordEquiv (R (Fin.last n)))
        (fun i => eqToHom (flattenWord_objects (R (Fin.last n)) i))).tensorMap ≫
          Groups.rowFoldMap (Groups.snoc G B)) _
      rw [Blocks.FiberMap.tensorMap_snoc, Groups.rowFoldMap_snoc]
      have hJoin := tensorJoin_transport_heq
        (Blocks.obj_blockTensors_snoc (blocksOfFamily (flattenedRows P))
          (orderedFamily (flattenedOriginalFamily (R (Fin.last n)))))
        (Blocks.obj_blockTensors_snoc G.groupedTensors B.blockTensors).symm
        (Blocks.obj_blockTensors_snoc G.groupedInputs B.inputs)
        (rowInputFiberMap P).tensorMap (flattenToWord (R (Fin.last n)))
        (Groups.rowFoldMap G) (Blocks.flattenIso B).hom
      have hTensor := tensorMapBoundary_heq
        (blocksOfFamily_tensors (flattenedRows P)) (rowFoldTarget_eq P) rfl
        (actualRowCarrier_eq (R (Fin.last n))) (ih P) (actualRowFold_heq (R (Fin.last n)))
      have hSucc := map_succ_heq
        (X := fun i => finiteObj (flattenedOriginalFamily (R i)))
        (X' := fun i => finiteObj (rowCarrierFamily (R i)))
        (Y := fun i : Fin n => finiteObj (flattenedOriginalFamily (P i)))
        (Y' := fun i : Fin n => finiteObj (rowCarrierFamily (P i)))
        (A := finiteObj (flattenedOriginalFamily (R (Fin.last n))))
        (A' := finiteObj (rowCarrierFamily (R (Fin.last n)))) rfl rfl rfl rfl
        (fun i => (finiteFlattenIso (R i)).hom) (fun i => (finiteFlattenIso (P i)).hom)
        (finiteFlattenIso (R (Fin.last n))).hom (fun _ => HEq.rfl) HEq.rfl
      simpa only [Category.assoc, P, G, B, flattenToWord, Groups.groupedTensors,
        flattenedRows, rowCarrierFamily] using hJoin.trans (hTensor.trans hSucc.symm)

set_option backward.isDefEq.respectTransparency false in
/-- Exact original source/target carrier maps join the complete actual row tensor map to the
original finite flattening
  tensor map. -/
theorem actualRowFoldTensor {n : ℕ} (R : Fin n → FiniteFamily (FiniteFamily C)) :
    ((rowInputFiberMap R).tensorMap ≫ Groups.rowFoldMap (groupsOfFamilies R)) ≫
      eqToHom (rowFoldTarget_eq R) =
      eqToHom (blocksOfFamily_tensors (flattenedRows R)) ≫ map (fun i =>
        (finiteFlattenIso (R i)).hom) := by
  have hL := (comp_eqToHom_heq
    ((rowInputFiberMap R).tensorMap ≫ Groups.rowFoldMap (groupsOfFamilies R))
      (rowFoldTarget_eq R)).trans
      (actualRowFoldTensor_heq R)
  have hR := eqToHom_comp_heq (map (fun i => (finiteFlattenIso (R i)).hom))
    (blocksOfFamily_tensors (flattenedRows R))
  exact eq_of_heq (hL.trans hR.symm)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ActualRowFoldTensor

/- Source proof segment: AssociativityLeftReduction -/
section source_AssociativityLeftReduction
/-!
# Actual left associativity route reduced to original ordered row folds

The full original mapped-flatten comparison and tensor of original
row comparisons normalize through the actual row input FiberMap.
The original grouping fold law identifies their common word map.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The original tensor of row comparison components is its actual ordered component map. -/
theorem finiteMap_rowFlatten (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    finiteMap (fixedIndexHom X.index (fun i => (finiteFlattenIso (X.obj i)).hom)) =
      map (fun i : Fin (arity X) => (finiteFlattenIso (X.obj (enumeration X i))).hom) :=
  finiteTensorFunctor_map_fixedIndex X.index (fun i => (finiteFlattenIso (X.obj i)).hom)

set_option backward.isDefEq.respectTransparency false in
/-- The actual left associativity route is the original complete concatenated row fold route. -/
theorem associativityLeft_reduction
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    (finiteFlattenIso (mappedFlattenRows X)).hom ≫
        finiteMap (fixedIndexHom X.index (fun i => (finiteFlattenIso (X.obj i)).hom)) =
      (rightTripleWordIso X).hom ≫ (Blocks.flattenIso (groupsOfFiniteFamilies X).flat).hom ≫
        (Groups.groupedMiddleCountIso (groupsOfFiniteFamilies X)).hom ≫
          (Blocks.flattenIso (groupsOfFiniteFamilies X).groupedTensors).hom ≫
            eqToHom (groupedOuterRowCarrier_eq X) := by
  let R := X.obj ∘ enumeration X
  let G := groupsOfFiniteFamilies X
  let F := rowInputFiberMap R
  have hRows := actualRowFoldTensor R
  have hNat := Blocks.FiberMap.flatten_naturality F
  rw [finiteMap_rowFlatten, finiteFlattenIso, Iso.trans_hom]
  simp only [finiteFamilyBlocksIso, blocksOfFamilyIso, Iso.trans_hom, eqToIso.hom,
    Category.assoc]
  change (flattenToWordIso (mappedFlattenRows X)).hom ≫
    ((Blocks.flattenIso (blocksOfFamily (flattenedRows R))).hom ≫
      (eqToHom (blocksOfFamily_tensors (flattenedRows R)) ≫
        map (fun i : Fin (arity X) => (finiteFlattenIso (R i)).hom))) = _
  rw [← hRows]
  dsimp only [F] at hNat
  have hNatAll := congrArg (fun k => (flattenToWordIso (mappedFlattenRows X)).hom ≫
    k ≫ Groups.rowFoldMap (groupsOfFamilies R) ≫ eqToHom (rowFoldTarget_eq R)) hNat
  have hNatAll' : (flattenToWordIso (mappedFlattenRows X)).hom ≫
      ((Blocks.flattenIso (blocksOfFamily (flattenedRows R))).hom ≫
        (rowInputFiberMap R).tensorMap ≫ Groups.rowFoldMap (groupsOfFamilies R)) ≫
          eqToHom (rowFoldTarget_eq R) =
    (flattenToWordIso (mappedFlattenRows X)).hom ≫ (rowInputFiberMap R).inputMap ≫
      (Blocks.flattenIso (groupsOfFamilies R).groupedInputs).hom ≫
        Groups.rowFoldMap (groupsOfFamilies R) ≫ eqToHom (rowFoldTarget_eq R) := by
    simpa only [Category.assoc] using hNatAll.symm
  dsimp only [blocksOfFiniteFamily, mappedFlattenRows, flattenedRows, R] at hNatAll' ⊢
  simp only [Category.assoc] at hNatAll' ⊢
  rw [hNatAll']
  have hMap := rowInputFiberMap_groupedIso X
  have hGroup := congrArg (fun k => (flattenToWordIso (mappedFlattenRows X)).hom ≫
    (mappedRowsGroupedIso X).hom ≫ k ≫ eqToHom (groupedOuterRowCarrier_eq X))
      (Groups.grouping_fold (groupsOfFiniteFamilies X))
  have hInput := congrArg (fun k => k ≫
    (Blocks.flattenIso (groupsOfFiniteFamilies X).flat).hom ≫
      (Groups.groupedMiddleCountIso (groupsOfFiniteFamilies X)).hom ≫
        (Blocks.flattenIso (groupsOfFiniteFamilies X).groupedTensors).hom ≫
          eqToHom (groupedOuterRowCarrier_eq X))
    (congrArg Iso.hom (rightTripleWordIso_rows X))
  have hStart : (flattenToWordIso (mappedFlattenRows X)).hom ≫
      (rowInputFiberMap (X.obj ∘ enumeration X)).inputMap ≫
        (Blocks.flattenIso (groupsOfFiniteFamilies X).groupedInputs).hom ≫
          Groups.rowFoldMap (groupsOfFiniteFamilies X) ≫
            eqToHom (groupedOuterRowCarrier_eq X) =
    (flattenToWordIso (mappedFlattenRows X)).hom ≫ (mappedRowsGroupedIso X).hom ≫
      ((Blocks.flattenIso (groupsOfFiniteFamilies X).groupedInputs).hom ≫
        Groups.rowFoldMap (groupsOfFiniteFamilies X)) ≫
          eqToHom (groupedOuterRowCarrier_eq X) := by
    rw [hMap]
    simp only [Category.assoc]
  simp only [Category.assoc, Iso.trans_hom] at hStart hGroup hInput
  have hFinish := hStart.trans (hGroup.trans hInput)
  dsimp only [R, G, mappedFlattenRows, blocksOfFiniteFamily, groupsOfFiniteFamilies,
    outerRowCarrierFamily, rowCarrierFamily, finiteObj, orderedFamily,
    enumeration, arity] at hFinish ⊢
  exact hFinish

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_AssociativityLeftReduction

/- Source proof segment: OriginalFamilyWord -/
section source_OriginalFamilyWord
/-!
# Literal words of original middle finite-family members

The word stores the original finite-family members, before tensoring
their objects. Appending original member words produces exactly the
actual concatenation of their original block words.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

variable {C : Type u}

/-- An actual finite word of original finite-family members. -/
structure FamilyWord (C : Type u) where
  /-- The original member count. -/
  length : ℕ
  /-- The original finite-family member in every original word slot. -/
  members : Fin length → FiniteFamily C

namespace FamilyWord

/-- The actual empty original member word. -/
def nil : FamilyWord C := ⟨0, Fin.elim0⟩

/-- Append the original member data in its original order. -/
def append (P Q : FamilyWord C) : FamilyWord C :=
  ⟨P.length + Q.length, Fin.append P.members Q.members⟩

/-- The actual original member word of one finite-family row. -/
noncomputable def ofFamily (R : FiniteFamily (FiniteFamily C)) : FamilyWord C :=
  ⟨arity R, orderedFamily R⟩

/-- The actual block word formed from all original member data. -/
noncomputable def blocks (W : FamilyWord C) : Blocks C := blocksOfFamily W.members

end FamilyWord

/-- Appending actual original finite-family member arrays is their actual block concatenation. -/
theorem blocksOfFamily_append {m : ℕ} (P : Fin m → FiniteFamily C) :
    ∀ {n : ℕ} (Q : Fin n → FiniteFamily C),
    blocksOfFamily (Fin.append P Q) = Blocks.concat (blocksOfFamily P) (blocksOfFamily Q)
  | 0, Q => by
      rw [append_nil]
      rfl
  | n + 1, Q => by
      change Blocks.snoc (blocksOfFamily (Fin.init (n := m + n)
          (Fin.append (m := m) (n := n + 1) P Q)))
          (orderedFamily (Fin.append (m := m) (n := n + 1) P Q (Fin.last (m + n)))) =
        Blocks.snoc (Blocks.concat (blocksOfFamily P) (blocksOfFamily (Fin.init Q)))
          (orderedFamily (Q (Fin.last n)))
      rw [init_append, last_append, blocksOfFamily_append]

/-- The actual concatenated original member word of all literal ordered rows. -/
noncomputable def flatFamilyWord :
    {n : ℕ} → (Fin n → FiniteFamily (FiniteFamily C)) → FamilyWord C
  | 0, _ => FamilyWord.nil
  | n + 1, R => FamilyWord.append (flatFamilyWord (Fin.init R))
      (FamilyWord.ofFamily (R (Fin.last n)))

/-- The actual original middle finite-family members of the concatenated row word. -/
noncomputable abbrev flatMembers {n : ℕ} (R : Fin n → FiniteFamily (FiniteFamily C)) :
    Fin (flatFamilyWord R).length → FiniteFamily C := (flatFamilyWord R).members

/-- The actual block word of original concatenated members is the actual
original flattened row data. -/
theorem flatMembers_blocks : ∀ {n : ℕ} (R : Fin n → FiniteFamily (FiniteFamily C)),
    blocksOfFamily (flatMembers R) = (groupsOfFamilies R).flat
  | 0, _ => rfl
  | n + 1, R => by
      change blocksOfFamily (Fin.append (flatMembers (Fin.init R))
        (orderedFamily (R (Fin.last n)))) =
          Blocks.concat (groupsOfFamilies (Fin.init R)).flat (blocksOfFiniteFamily (R (Fin.last n)))
      rw [blocksOfFamily_append, flatMembers_blocks]
      rfl

/-- The original member count is the actual concatenated original middle-block count. -/
theorem flatMembers_length {n : ℕ} (R : Fin n → FiniteFamily (FiniteFamily C)) :
    (flatFamilyWord R).length = (groupsOfFamilies R).flat.length :=
  (blocksOfFamily_length (flatMembers R)).symm.trans (congrArg Blocks.length (flatMembers_blocks R))

/-- The complete original label bijection of the literal concatenated member word. -/
noncomputable def flatMembersLabelEquiv :
    {n : ℕ} → (R : Fin n → FiniteFamily (FiniteFamily C)) →
      Fin (flatFamilyWord R).length ≃ OriginalPositions R
  | 0, R => by
      haveI : IsEmpty (OriginalPositions R) := ⟨fun p => p.1.elim0⟩
      exact (Equiv.equivEmpty (Fin 0)).trans (Equiv.equivEmpty (OriginalPositions R)).symm
  | n + 1, R => finSumFinEquiv.symm.trans
      ((Equiv.sumCongr (flatMembersLabelEquiv (Fin.init R)) (enumeration (R (Fin.last n)))).trans
        (positionsSnocEquiv R))

set_option backward.isDefEq.respectTransparency false in
/-- Every original concatenated member keeps its complete original outer and middle labels. -/
theorem flatMembers_labels :
    ∀ {n : ℕ} (R : Fin n → FiniteFamily (FiniteFamily C)) (j : Fin (flatFamilyWord R).length),
    flatMembers R j = (R (flatMembersLabelEquiv R j).1).obj (flatMembersLabelEquiv R j).2
  | 0, _, j => Fin.elim0 j
  | n + 1, R, j => by
      have h : ∀ k : Fin ((flatFamilyWord (Fin.init R)).length + arity (R (Fin.last n))),
          Fin.append (flatMembers (Fin.init R)) (orderedFamily (R (Fin.last n))) k =
            (R (positionsSnocEquiv R
              ((Equiv.sumCongr (flatMembersLabelEquiv (Fin.init R))
                (enumeration (R (Fin.last n)))) (finSumFinEquiv.symm k))).1).obj
              (positionsSnocEquiv R
                ((Equiv.sumCongr (flatMembersLabelEquiv (Fin.init R))
                  (enumeration (R (Fin.last n)))) (finSumFinEquiv.symm k))).2 := by
        intro k
        refine Fin.addCases (fun i => ?_) (fun i => ?_) k
        · rw [Fin.append_left, finSumFinEquiv_symm_apply_castAdd]
          exact flatMembers_labels (Fin.init R) i
        · rw [Fin.append_right, finSumFinEquiv_symm_apply_natAdd]
          rfl
      exact h j

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OriginalFamilyWord

/- Source proof segment: TripleOriginalMembers -/
section source_TripleOriginalMembers
/-!
# Original triple-family member data in concatenated row order

The complete original outer and middle labels identify each original
finite-family member. The actual flattened middle family is reindexed
to that literal word using original family equalities.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The literal original member word of a triple family in its original outer row order. -/
noncomputable def tripleFamilyWord
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) : FamilyWord C :=
  flatFamilyWord (X.obj ∘ enumeration X)

/-- The complete original label bijection from literal row members to original flattened
middle labels. -/
noncomputable def flatMembersGlobalLabelEquiv
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    Fin (tripleFamilyWord X).length ≃ (flattenedMiddleFamily X).index :=
  (flatMembersLabelEquiv (X.obj ∘ enumeration X)).trans
    (originalOuterPositionsEquiv (C := FiniteFamily C) X)

/-- Every literal row member is its original finite family, with both original labels retained. -/
theorem flatMembers_global_member
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (j : Fin (tripleFamilyWord X).length) :
    (tripleFamilyWord X).members j =
      (flattenedMiddleFamily X).obj (flatMembersGlobalLabelEquiv X j) :=
  flatMembers_labels (X.obj ∘ enumeration X) j

/-- The exact original flattened-middle enumeration maps to the literal original member word. -/
noncomputable def flatMembersOriginalReindex
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    Fin (arity (flattenedMiddleFamily X)) ≃ Fin (tripleFamilyWord X).length :=
  (enumeration (flattenedMiddleFamily X)).trans (flatMembersGlobalLabelEquiv X).symm

/-- The actual reindexing compares original finite-family members before tensoring any objects. -/
theorem flatMembers_original_family
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (i : Fin (arity (flattenedMiddleFamily X))) :
    orderedFamily (flattenedMiddleFamily X) i =
      (tripleFamilyWord X).members (flatMembersOriginalReindex X i) := by
  have hm := flatMembers_global_member X
    ((flatMembersGlobalLabelEquiv X).symm (enumeration (flattenedMiddleFamily X) i))
  have hp := congrArg (flattenedMiddleFamily X).obj
    ((flatMembersGlobalLabelEquiv X).apply_symm_apply (enumeration (flattenedMiddleFamily X) i))
  exact (hm.trans hp).symm

omit [Category.{v} C] in
/-- The original member word produces exactly the actual concatenated original row block data. -/
theorem flatMembers_original_blocks
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    blocksOfFamily (tripleFamilyWord X).members = (groupsOfFiniteFamilies X).flat :=
  flatMembers_blocks (X.obj ∘ enumeration X)

omit [Category.{v} C] in
/-- The original member count is exactly the actual original concatenated middle-block count. -/
theorem flatMembers_original_length
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    (tripleFamilyWord X).length = (groupsOfFiniteFamilies X).flat.length :=
  flatMembers_length (X.obj ∘ enumeration X)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_TripleOriginalMembers

/- Source proof segment: OriginalMemberReindexMaps -/
section source_OriginalMemberReindexMaps
/-!
# Actual ordered maps of the original flattened row member word

The original flattened middle family and literal original row members
give an actual equality reindexing morphism. Its input and output maps
retain exact original target block data and tensor carrier transports.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C]

/-- The actual ordered original-family reindexing morphism to the literal concatenated row
members. -/
noncomputable def flatMembersOriginalHom
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    literalOuterFamily (orderedFamily (flattenedMiddleFamily X)) ⟶
      literalOuterFamily (tripleFamilyWord X).members :=
  orderedReindexHom (flatMembersOriginalReindex X)
    (orderedFamily (flattenedMiddleFamily X)) (tripleFamilyWord X).members
    (flatMembers_original_family X)

/-- The actual source blocks are the original blocks of the flattened original middle family. -/
theorem flatMembersHom_source_blocks
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    blocksOfFamily (orderedFamily (flattenedMiddleFamily X)) =
      blocksOfFiniteFamily (flattenedMiddleFamily X) := rfl

variable [MonoidalCategory C]

/-- The actual target input tensor carrier is the original concatenated row input carrier. -/
theorem flatMembersHom_input_target
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    obj (blocksOfFamily (tripleFamilyWord X).members).inputs =
      obj (groupsOfFiniteFamilies X).flat.inputs :=
  congrArg (fun B : Blocks C => obj B.inputs) (flatMembers_original_blocks X)

/-- The actual target outer tensor carrier is the original concatenated block tensor word. -/
theorem flatMembersHom_output_target
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    obj (fun i => finiteObj ((tripleFamilyWord X).members i)) =
      obj (groupsOfFiniteFamilies X).flat.blockTensors :=
  (blocksOfFamily_tensors (tripleFamilyWord X).members).symm.trans
    (congrArg (fun B : Blocks C => obj B.blockTensors) (flatMembers_original_blocks X))

variable [SymmetricCategory C]

/-- The actual original-family reindexing input map to the concatenated original row inputs. -/
noncomputable def flatMembersOriginalInputMap
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    obj (blocksOfFiniteFamily (flattenedMiddleFamily X)).inputs ⟶
      obj (groupsOfFiniteFamilies X).flat.inputs :=
  orderedInputMap (flatMembersOriginalHom X) ≫ eqToHom (flatMembersHom_input_target X)

/-- The actual original-family reindexing output map to the concatenated original block tensors. -/
noncomputable def flatMembersOriginalOutputMap
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    obj (fun i => finiteObj (orderedFamily (flattenedMiddleFamily X) i)) ⟶
      obj (groupsOfFiniteFamilies X).flat.blockTensors :=
  orderedOutputMap (flatMembersOriginalHom X) ≫ eqToHom (flatMembersHom_output_target X)

/-- The original member morphism has its actual original ordered input and output square. -/
theorem flatMembersOriginal_naturality
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    orderedInputMap (flatMembersOriginalHom X) ≫
        (blocksOfFamilyIso (tripleFamilyWord X).members).hom =
      (blocksOfFamilyIso (orderedFamily (flattenedMiddleFamily X))).hom ≫
        orderedOutputMap (flatMembersOriginalHom X) :=
  orderedReindex_naturality (flatMembersOriginalReindex X)
    (orderedFamily (flattenedMiddleFamily X)) (tripleFamilyWord X).members
    (flatMembers_original_family X)

/-- The actual original-member output map retains exactly its actual original tensor
equality components. -/
theorem flatMembersOriginal_output_components
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    orderedOutputMap (flatMembersOriginalHom X) =
      mapEquiv (flatMembersOriginalReindex X)
        (fun i => eqToHom (congrArg finiteObj (flatMembers_original_family X i))) :=
  orderedOutput_reindex (flatMembersOriginalReindex X)
    (orderedFamily (flattenedMiddleFamily X)) (tripleFamilyWord X).members
    (flatMembers_original_family X)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OriginalMemberReindexMaps

/- Source proof segment: SumLabelCountTransport -/
section source_SumLabelCountTransport
/-!
# Actual sum-label transport through both original finite counts

The generic index factory transports both prefix and final counts
and their complete label bijections before selecting original rows.
-/

@[expose] public section

set_option autoImplicit false

universe p q r

namespace CategoryTheory.MonoidalCategory.OrderedTensor

/-- The complete original sum labels respect both original count transports. -/
theorem sumLabels_count {a a' b b' : ℕ} {P : Type p} {Q : Type q}
    (ha : a = a') (hb : b = b') (h : a + b = a' + b')
    (e : Fin a ≃ P) (e' : Fin a' ≃ P) (d : Fin b ≃ Q) (d' : Fin b' ≃ Q)
    (he : ∀ i, e i = e' (Fin.cast ha i)) (hd : ∀ i, d i = d' (Fin.cast hb i))
    (j : Fin (a + b)) :
    (Equiv.sumCongr e d) (finSumFinEquiv.symm j) =
      (Equiv.sumCongr e' d') (finSumFinEquiv.symm (Fin.cast h j)) := by
  subst a'
  subst b'
  have heq : e = e' := Equiv.ext he
  have hdq : d = d' := Equiv.ext hd
  subst e'
  subst d'
  rfl

/-- Complete original sum labels respect both counts and the actual two-stage label map. -/
theorem sumLabels_count_comp {a a' b b' m t : ℕ}
    {P : Type p} {P' : Type q} {Q : Type r}
    (hm : m = a + b) (ha : a = a') (hb : b = b')
    (hmt : m = t) (ht : t = a' + b')
    (e : Fin a ≃ P') (f : Fin a' ≃ P) (g : P ≃ P')
    (d : Fin b ≃ Q) (d' : Fin b' ≃ Q)
    (he : ∀ i, e i = g (f (Fin.cast ha i)))
    (hd : ∀ i, d i = d' (Fin.cast hb i)) (j : Fin m) :
    (Equiv.sumCongr e d) (finSumFinEquiv.symm (Fin.cast hm j)) =
      (Equiv.sumCongr g d') ((Equiv.sumCongr f (Equiv.refl (Fin b')))
        (finSumFinEquiv.symm (Fin.cast ht (Fin.cast hmt j)))) := by
  subst hm
  subst hmt
  have hs := sumLabels_count ha hb ht e (f.trans g) d d' he hd j
  have hc := congrArg
    (fun E : (Fin a' ⊕ Fin b') ≃ (P' ⊕ Q) =>
      E (finSumFinEquiv.symm (Fin.cast ht j)))
    (Equiv.sumCongr_trans f (Equiv.refl (Fin b')) g d')
  have hc' : (Equiv.sumCongr g d') ((Equiv.sumCongr f (Equiv.refl (Fin b')))
      (finSumFinEquiv.symm (Fin.cast ht j))) =
      (Equiv.sumCongr (f.trans g) d') (finSumFinEquiv.symm (Fin.cast ht j)) := by
    simpa only [Equiv.trans_apply, Equiv.refl_trans] using hc
  exact hs.trans hc'.symm

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_SumLabelCountTransport

/- Source proof segment: FlatMembersLabelAlignment -/
section source_FlatMembersLabelAlignment
/-!
# Original family labels of the actual flat row group

The literal member word and actual concatenated row blocks retain
the same complete original outer and middle input labels.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

variable {C : Type u}

/-- Every actual concatenated member has the same original labels in the original flat row group. -/
theorem flatMembersLabel_group_position :
    ∀ {n : ℕ} (R : Fin n → FiniteFamily (FiniteFamily C))
    (j : Fin (flatFamilyWord R).length),
    flatMembersLabelEquiv R j =
      groupsMiddleOriginalPositions R
        ((groupsOfFamilies R).flatMiddleEquiv (Fin.cast (flatMembers_length R) j))
  | 0, _, j => Fin.elim0 j
  | n + 1, R, j => by
      have hd : ∀ k : Fin (arity (R (Fin.last n))),
          enumeration (R (Fin.last n)) k =
            rowMiddleEquiv (R (Fin.last n))
              (Fin.cast (blocksOfFiniteFamily_length (R (Fin.last n))).symm k) := by
        intro k
        rw [rowMiddleEquiv_apply]
        apply congrArg (enumeration (R (Fin.last n)))
        apply Fin.ext
        rfl
      have hs := sumLabels_count_comp
        (rfl : (flatFamilyWord R).length =
          (flatFamilyWord (Fin.init R)).length + arity (R (Fin.last n)))
        (flatMembers_length (Fin.init R))
        (blocksOfFiniteFamily_length (R (Fin.last n))).symm
        (flatMembers_length R)
        (Blocks.concat_length (groupsOfFamilies (Fin.init R)).flat
          (blocksOfFiniteFamily (R (Fin.last n))))
        (flatMembersLabelEquiv (Fin.init R))
        (groupsOfFamilies (Fin.init R)).flatMiddleEquiv
        (groupsMiddleOriginalPositions (Fin.init R))
        (enumeration (R (Fin.last n))) (rowMiddleEquiv (R (Fin.last n)))
        (flatMembersLabel_group_position (Fin.init R)) hd j
      exact congrArg (positionsSnocEquiv R) hs

/-- The complete original literal member label bijection is the actual
flat group label bijection. -/
theorem flatMembersLabel_group_equiv {n : ℕ} (R : Fin n → FiniteFamily (FiniteFamily C)) :
    flatMembersLabelEquiv R =
      (finCongr (flatMembers_length R)).trans
        ((groupsOfFamilies R).flatMiddleEquiv.trans (groupsMiddleOriginalPositions R)) := by
  apply Equiv.ext
  intro j
  exact flatMembersLabel_group_position R j

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FlatMembersLabelAlignment

/- Source proof segment: OriginalMemberOutputAlignment -/
section source_OriginalMemberOutputAlignment
/-!
# Exact original member-label and output-map alignment

The original family member labels agree with the actual concatenated
row labels independently of object equality. Their actual tensor
output map is the original middle-carrier word comparison.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C]

/-- The complete original member labels are the complete original concatenated middle labels. -/
theorem flatMembers_global_group_label
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (j : Fin (tripleFamilyWord X).length) :
    flatMembersGlobalLabelEquiv X j =
      tripleMiddleInputEquiv X (Fin.cast (flatMembers_original_length X) j) :=
  congrArg (originalOuterPositionsEquiv (C := FiniteFamily C) X)
    (flatMembersLabel_group_position (X.obj ∘ enumeration X) j)

/-- The complete original member-label bijection is the original counted concatenated middle
bijection. -/
theorem flatMembers_global_group_equiv
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    flatMembersGlobalLabelEquiv X =
      (finCongr (flatMembers_original_length X)).trans (tripleMiddleInputEquiv X) := by
  apply Equiv.ext
  intro j
  exact flatMembers_global_group_label X j

variable [MonoidalCategory C]

/-- The actual member carrier retains its original concatenated tensor position and object. -/
theorem flatMembers_original_tensor_object
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (j : Fin (tripleFamilyWord X).length) :
    finiteObj ((tripleFamilyWord X).members j) =
      (groupsOfFiniteFamilies X).flat.blockTensors (Fin.cast (flatMembers_original_length X)
        j) := by
  have ht := tripleMiddleInput_objects X (Fin.cast (flatMembers_original_length X) j)
  have hp := congrArg (middleCarrierFamily X).obj (flatMembers_global_group_label X j).symm
  exact (congrArg finiteObj (flatMembers_global_member X j)).trans (ht.trans hp).symm

/-- The actual original member reindexing has exactly the original middle-carrier word bijection. -/
theorem flatMembers_reindex_middle
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    (flatMembersOriginalReindex X).trans (finCongr (flatMembers_original_length X)) =
      middleCarrierWordEquiv X := by
  apply Equiv.ext
  intro i
  apply (tripleMiddleInputEquiv X).injective
  have hp := flatMembers_global_group_label X
    ((flatMembersGlobalLabelEquiv X).symm (enumeration (flattenedMiddleFamily X) i))
  have he := (flatMembersGlobalLabelEquiv X).apply_symm_apply
    (enumeration (flattenedMiddleFamily X) i)
  have hr := (tripleMiddleInputEquiv X).apply_symm_apply (enumeration (middleCarrierFamily X) i)
  exact (hp.symm.trans he).trans hr.symm

variable [SymmetricCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The original member output map is precisely the actual original middle-carrier word
comparison. -/
theorem flatMembersOriginalOutputMap_eq
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    flatMembersOriginalOutputMap X =
      mapEquiv (middleCarrierWordEquiv X) (fun i => eqToHom (middleCarrierWord_objects X i)) := by
  have he : HEq (flatMembersOriginalReindex X) (middleCarrierWordEquiv X) := by
    have ht := equiv_count_transport_heq
      (rfl : arity (flattenedMiddleFamily X) = arity (flattenedMiddleFamily X))
      (flatMembers_original_length X) (flatMembersOriginalReindex X)
    have ht' : HEq
        ((flatMembersOriginalReindex X).trans (finCongr (flatMembers_original_length X)))
        (flatMembersOriginalReindex X) := by
      simpa only [finCongr_refl, Equiv.refl_symm, Equiv.refl_trans] using ht
    exact ht'.symm.trans (heq_of_eq (flatMembers_reindex_middle X))
  have hf : ∀ i : Fin (arity (flattenedMiddleFamily X)),
      HEq (eqToHom (congrArg finiteObj (flatMembers_original_family X i)))
        (eqToHom (middleCarrierWord_objects X i)) := by
    intro i
    exact (eqToHom_heq_id_dom _ _ (congrArg finiteObj (flatMembers_original_family X i))).trans
      (eqToHom_heq_id_dom _ _ (middleCarrierWord_objects X i)).symm
  have hm := mapEquiv_input_heq rfl (flatMembers_original_length X)
    (fun i => finiteObj (orderedFamily (flattenedMiddleFamily X) i))
    (orderedFamily (middleCarrierFamily X))
    (fun j => finiteObj ((tripleFamilyWord X).members j))
    (groupsOfFiniteFamilies X).flat.blockTensors
    (fun _ => rfl) (flatMembers_original_tensor_object X)
    (flatMembersOriginalReindex X) (middleCarrierWordEquiv X) he
    (fun i => eqToHom (congrArg finiteObj (flatMembers_original_family X i)))
    (fun i => eqToHom (middleCarrierWord_objects X i)) hf
  have hraw := (heq_of_eq (flatMembersOriginal_output_components X)).trans hm
  exact eq_of_heq ((comp_eqToHom_heq
    (orderedOutputMap (flatMembersOriginalHom X)) (flatMembersHom_output_target X)).trans hraw)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OriginalMemberOutputAlignment

/- Source proof segment: OriginalMemberSigmaAction -/
section source_OriginalMemberSigmaAction
/-!
# Actual original labels and inner indices of the member morphism

The actual equality reindexing moves an original family label and
retains its complete original inner index through exact family casts.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The actual original member reindexing sends each enumerated source label
to its actual word slot. -/
theorem flatMembers_reindex_label
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) (p : (flattenedMiddleFamily X).index) :
    flatMembersOriginalReindex X ((enumeration (flattenedMiddleFamily X)).symm p) =
      (flatMembersGlobalLabelEquiv X).symm p := by
  change (flatMembersGlobalLabelEquiv X).symm
    (enumeration (flattenedMiddleFamily X) ((enumeration (flattenedMiddleFamily X)).symm p)) = _
  exact congrArg (flatMembersGlobalLabelEquiv X).symm
    ((enumeration (flattenedMiddleFamily X)).apply_symm_apply p)

/-- The actual source enumeration retains its original finite-family member. -/
theorem flatMembers_source_label
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) (p : (flattenedMiddleFamily X).index) :
    (flattenedMiddleFamily X).obj p =
      orderedFamily (flattenedMiddleFamily X) ((enumeration (flattenedMiddleFamily X)).symm p) :=
  congrArg (flattenedMiddleFamily X).obj
    ((enumeration (flattenedMiddleFamily X)).apply_symm_apply p).symm

/-- The actual original member word slot retains the original finite-family member at its label. -/
theorem flatMembers_target_label
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) (p : (flattenedMiddleFamily X).index) :
    (flattenedMiddleFamily X).obj p =
      (tripleFamilyWord X).members ((flatMembersGlobalLabelEquiv X).symm p) := by
  have hm := flatMembers_global_member X ((flatMembersGlobalLabelEquiv X).symm p)
  have hp := congrArg (flattenedMiddleFamily X).obj
    ((flatMembersGlobalLabelEquiv X).apply_symm_apply p)
  exact (hm.trans hp).symm

/-- The actual flattened member morphism transports the full original inner input
from its source label. -/
theorem flatMembers_reindex_inner_label
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) (p : (flattenedMiddleFamily X).index)
    (j : ((flattenedMiddleFamily X).obj p).index) :
    ((FiniteFamily.flatten (C := C)).map (flatMembersOriginalHom X)).equiv
      (⟨(enumeration (flattenedMiddleFamily X)).symm p,
        cast (congrArg (fun A : FiniteFamily C => (A.index : Type))
          (flatMembers_source_label X p)) j⟩) =
      ⟨(flatMembersGlobalLabelEquiv X).symm p,
        cast (congrArg (fun A : FiniteFamily C => (A.index : Type))
          (flatMembers_target_label X p)) j⟩ :=
  reindexPosition_label (flatMembersOriginalReindex X)
    (orderedFamily (flattenedMiddleFamily X)) (tripleFamilyWord X).members
    (flatMembers_original_family X)
    ((enumeration (flattenedMiddleFamily X)).symm p)
    ((flatMembersGlobalLabelEquiv X).symm p) (flatMembers_reindex_label X p)
    ((flattenedMiddleFamily X).obj p) (flatMembers_source_label X p)
    (flatMembers_target_label X p) j

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OriginalMemberSigmaAction

/- Source proof segment: OriginalMemberInputData -/
section source_OriginalMemberInputData
/-!
# Complete desired original input data for the member reindexing

The original nested middle-family positions and actual left-associated
triple positions construct the full concatenated-row input bijection
and every original source-input object equality.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C]

/-- The complete original nested-middle to concatenated-row input bijection. -/
noncomputable def flatMembersDesiredInputEquiv
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    Fin (blocksOfFiniteFamily (flattenedMiddleFamily X)).totalArity ≃
      Fin (groupsOfFiniteFamilies X).flat.totalArity :=
  (nestedPositionsEquiv (flattenedMiddleFamily X)).trans (leftTripleInputEquiv X).symm

/-- Every desired original concatenated input retains its complete original source object. -/
theorem flatMembersDesiredInput_objects
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (j : Fin (blocksOfFiniteFamily (flattenedMiddleFamily X)).totalArity) :
    (blocksOfFiniteFamily (flattenedMiddleFamily X)).inputs j =
      (groupsOfFiniteFamilies X).flat.inputs (flatMembersDesiredInputEquiv X j) := by
  have hs := nestedPositions_objects (flattenedMiddleFamily X) j
  have ht := leftTripleInput_objects X
    ((leftTripleInputEquiv X).symm (nestedPositionsEquiv (flattenedMiddleFamily X) j))
  have hp := congrArg ((FiniteFamily.flattenFlatten (C := C)).obj X).obj
    ((leftTripleInputEquiv X).apply_symm_apply (nestedPositionsEquiv (flattenedMiddleFamily X) j))
  exact hs.trans (ht.trans hp).symm

variable [MonoidalCategory C] [SymmetricCategory C]

/-- The original tensor map of the complete desired input bijection and equality components. -/
noncomputable def flatMembersDesiredInputMap
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    obj (blocksOfFiniteFamily (flattenedMiddleFamily X)).inputs ⟶
      obj (groupsOfFiniteFamilies X).flat.inputs :=
  mapEquiv (flatMembersDesiredInputEquiv X) (fun j => eqToHom (flatMembersDesiredInput_objects X j))

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OriginalMemberInputData

/- Source proof segment: AssociativityMiddleReduction -/
section source_AssociativityMiddleReduction
/-!
# Original middle-member word map normalization

The original left sigma input word and original middle carrier word
are joined to the actual member reindexing maps. The member fold
square is the proved source original ordered naturality square.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [SymmetricCategory C] in
theorem blockFold_transport {B B' : Blocks C} (h : B = B') :
    (Blocks.flattenIso B).hom ≫
        eqToHom (congrArg (fun B : Blocks C => obj B.blockTensors) h) =
      eqToHom (congrArg (fun B : Blocks C => obj B.inputs) h) ≫
        (Blocks.flattenIso B').hom := by
  cases h
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
theorem leftTripleWordIso_middle
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    (flattenToWordIso (flattenedMiddleFamily X)).hom ≫ flatMembersDesiredInputMap X =
      (leftTripleWordIso X).hom := by
  unfold flatMembersDesiredInputMap flattenToWordIso leftTripleWordIso
  rw [isoEquiv_hom, isoEquiv_hom, mapEquiv_comp]
  have he : (flattenWordEquiv (flattenedMiddleFamily X)).trans
      (flatMembersDesiredInputEquiv X) = leftTripleWordEquiv X := by
    apply Equiv.ext
    intro i
    change (leftTripleInputEquiv X).symm
      ((nestedPositionsEquiv (flattenedMiddleFamily X))
        ((nestedPositionsEquiv (flattenedMiddleFamily X)).symm
          (enumeration ((FiniteFamily.flattenFlatten (C := C)).obj X) i))) = _
    exact congrArg (leftTripleInputEquiv X).symm
      ((nestedPositionsEquiv (flattenedMiddleFamily X)).apply_symm_apply _)
  apply mapEquiv_congr he
  intro i
  exact inputEquality_hom_chain
    (flattenWord_objects (flattenedMiddleFamily X) i)
    (flatMembersDesiredInput_objects X (flattenWordEquiv (flattenedMiddleFamily X) i))
    (leftTripleWord_objects X i)

set_option backward.isDefEq.respectTransparency false in
theorem middleCarrierWordIso_output
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    flatMembersOriginalOutputMap X = (middleCarrierWordIso X).hom := by
  rw [flatMembersOriginalOutputMap_eq]
  exact (isoEquiv_hom (middleCarrierWordEquiv X)
    (fun i => eqToIso (middleCarrierWord_objects X i))).symm

set_option backward.isDefEq.respectTransparency false in
theorem flatMembersFold_naturality
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    flatMembersOriginalInputMap X ≫ (Blocks.flattenIso (groupsOfFiniteFamilies X).flat).hom =
      (finiteFamilyBlocksIso (flattenedMiddleFamily X)).hom ≫ flatMembersOriginalOutputMap X := by
  have h := flatMembersOriginal_naturality X
  have ht := blocksOfFamily_tensors (tripleFamilyWord X).members
  have hEq : (blocksOfFamilyIso (tripleFamilyWord X).members).hom ≫
      eqToHom (flatMembersHom_output_target X) =
    eqToHom (flatMembersHom_input_target X) ≫
      (Blocks.flattenIso (groupsOfFiniteFamilies X).flat).hom := by
    have hB := flatMembers_original_blocks X
    have hTransport := blockFold_transport hB
    simp only [blocksOfFamilyIso, Iso.trans_hom, eqToIso.hom]
    simp only [Category.assoc]
    slice_lhs 2 3 => rw [eqToHom_trans]
    exact hTransport
  have hAll := congrArg (fun k => k ≫ eqToHom (flatMembersHom_output_target X)) h
  rw [Category.assoc, hEq] at hAll
  dsimp only [flatMembersOriginalInputMap, flatMembersOriginalOutputMap, finiteFamilyBlocksIso]
  dsimp only [blocksOfFiniteFamily, orderedFamily] at hAll ⊢
  simp only [Category.assoc] at hAll ⊢
  exact hAll

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_AssociativityMiddleReduction

/- Source proof segment: MappedTensorRowFiber -/
section source_MappedTensorRowFiber
/-!
# Actual row-carrier input normalization for mapped tensor rows

The original finite row-carrier indices are related to the actual
ordered middle blocks by their original count casts and original
middle index labels. No input bijection is inferred from C object
equality or supplied as a tensor coherence outcome.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [SymmetricCategory C] in
/-- Each actual original row carrier retains its original middle count cast. -/
noncomputable def rowCarrierToMiddleEquiv (R : FiniteFamily (FiniteFamily C)) :
    Fin (arity (rowCarrierFamily R)) ≃ Fin (blocksOfFiniteFamily R).length :=
  finCongr (blocksOfFiniteFamily_length R).symm

omit [SymmetricCategory C] in
/-- The actual original row-carrier count cast retains the original row middle label. -/
theorem rowCarrierToMiddle_label (R : FiniteFamily (FiniteFamily C))
    (i : Fin (arity (rowCarrierFamily R))) :
    rowMiddleEquiv R (rowCarrierToMiddleEquiv R i) = enumeration R i := by
  change enumeration R
    (Fin.cast (blocksOfFiniteFamily_length R) (Fin.cast (blocksOfFiniteFamily_length R).symm i)) = _
  exact congrArg (enumeration R) (Fin.ext rfl)

omit [SymmetricCategory C] in
/-- Every original row-carrier object is the original tensor object of its actual original
middle block. -/
theorem rowCarrierToMiddle_objects (R : FiniteFamily (FiniteFamily C))
    (i : Fin (arity (rowCarrierFamily R))) :
    orderedFamily (rowCarrierFamily R) i = (blocksOfFiniteFamily R).blockTensors
      (rowCarrierToMiddleEquiv R i) :=
  ((rowMiddleEquiv_blockTensors R (rowCarrierToMiddleEquiv R i)).trans
    (congrArg (fun j => finiteObj (R.obj j)) (rowCarrierToMiddle_label R i))).symm

omit [SymmetricCategory C] in
/-- The original carrier family of every literal ordered row. -/
noncomputable def rowCarrierRows {n : ℕ} (R : Fin n → FiniteFamily (FiniteFamily C)) :
    Fin n → FiniteFamily C := fun i => rowCarrierFamily (R i)

/-- The actual original fiber map from every original row carrier word to its original
grouped middle tensor word. -/
noncomputable def mappedRowFiberMap : {n : ℕ} → (R : Fin n → FiniteFamily (FiniteFamily C)) →
    Blocks.FiberMap (blocksOfFamily (rowCarrierRows R)) (groupsOfFamilies R).groupedTensors
  | 0, _ => .nil
  | n + 1, R => .snoc (mappedRowFiberMap (Fin.init R)) (rowCarrierToMiddleEquiv (R (Fin.last n)))
      (fun i => eqToHom (rowCarrierToMiddle_objects (R (Fin.last n)) i))

omit [SymmetricCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- The original grouped middle tensor input retains its original preceding row and middle label. -/
theorem groupedMiddleOriginal_left {n : ℕ} (R : Fin (n + 1) → FiniteFamily (FiniteFamily C))
    (i : Fin (groupsOfFamilies (Fin.init R)).groupedTensors.totalArity) :
    groupsMiddleOriginalPositions R ((groupsOfFamilies R).groupedMiddleEquiv
      (Fin.castAdd (blocksOfFiniteFamily (R (Fin.last n))).length i)) =
      ⟨(groupsMiddleOriginalPositions (Fin.init R)
        ((groupsOfFamilies (Fin.init R)).groupedMiddleEquiv i)).1.castSucc,
        (groupsMiddleOriginalPositions (Fin.init R)
          ((groupsOfFamilies (Fin.init R)).groupedMiddleEquiv i)).2⟩ := by
  change positionsSnocEquiv R
    ((Equiv.sumCongr (groupsMiddleOriginalPositions (Fin.init R)) (rowMiddleEquiv (R (Fin.last n))))
      ((Equiv.sumCongr (groupsOfFamilies (Fin.init R)).groupedMiddleEquiv
        (Equiv.refl (Fin (blocksOfFiniteFamily (R (Fin.last n))).length)))
          (finSumFinEquiv.symm (Fin.castAdd _ i)))) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

omit [SymmetricCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- The original grouped middle tensor input retains its original final row and original
middle label. -/
theorem groupedMiddleOriginal_right {n : ℕ} (R : Fin (n + 1) → FiniteFamily (FiniteFamily C))
    (i : Fin (blocksOfFiniteFamily (R (Fin.last n))).length) :
    groupsMiddleOriginalPositions R ((groupsOfFamilies R).groupedMiddleEquiv
      (Fin.natAdd (groupsOfFamilies (Fin.init R)).groupedTensors.totalArity i)) =
      ⟨Fin.last n, rowMiddleEquiv (R (Fin.last n)) i⟩ := by
  change positionsSnocEquiv R
    ((Equiv.sumCongr (groupsMiddleOriginalPositions (Fin.init R)) (rowMiddleEquiv (R (Fin.last n))))
      ((Equiv.sumCongr (groupsOfFamilies (Fin.init R)).groupedMiddleEquiv
        (Equiv.refl (Fin (blocksOfFiniteFamily (R (Fin.last n))).length)))
          (finSumFinEquiv.symm (Fin.natAdd _ i)))) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

omit [SymmetricCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- The actual original mapped-row input map retains each original row and middle input label. -/
theorem mappedRowFiberMap_positions : ∀ {n : ℕ} (R : Fin n → FiniteFamily (FiniteFamily C))
    (i : Fin (blocksOfFamily (rowCarrierRows R)).totalArity),
    groupsMiddleOriginalPositions R
      ((groupsOfFamilies R).groupedMiddleEquiv ((mappedRowFiberMap R).inputEquiv i)) =
        flattenedPositionsEquiv (rowCarrierRows R) i
  | 0, _, i => i.elim0
  | n + 1, R, i => by
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · change Fin (blocksOfFamily (rowCarrierRows (Fin.init R))).totalArity at j
        change groupsMiddleOriginalPositions R ((groupsOfFamilies R).groupedMiddleEquiv
          (sumInputsEquiv (mappedRowFiberMap (Fin.init R)).inputEquiv
            (rowCarrierToMiddleEquiv (R (Fin.last n)))
              (Fin.castAdd (arity (rowCarrierFamily (R (Fin.last n)))) j))) = _
        rw [sumInputsEquiv_left, groupedMiddleOriginal_left, flattenedPositions_left]
        exact congrArg (fun p : OriginalPositions (Fin.init R) =>
          (⟨p.1.castSucc, p.2⟩ : OriginalPositions R)) (mappedRowFiberMap_positions (Fin.init R) j)
      · change groupsMiddleOriginalPositions R ((groupsOfFamilies R).groupedMiddleEquiv
          (sumInputsEquiv (mappedRowFiberMap (Fin.init R)).inputEquiv
            (rowCarrierToMiddleEquiv (R (Fin.last n)))
              (Fin.natAdd (blocksOfFamily (rowCarrierRows (Fin.init R))).totalArity j))) = _
        rw [sumInputsEquiv_right, groupedMiddleOriginal_right, flattenedPositions_right]
        exact congrArg (fun p : (R (Fin.last n)).index =>
          (⟨Fin.last n, p⟩ : OriginalPositions R)) (rowCarrierToMiddle_label (R (Fin.last n)) j)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_MappedTensorRowFiber

/- Source proof segment: MappedTensorRowMaps -/
section source_MappedTensorRowMaps
/-!
# Actual input and tensor equality maps of mapped tensor rows

Every original row-carrier input is mapped to its actual original
middle tensor block. The complete input map and outer tensor map
retain their original equality transports and original index labels.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [SymmetricCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- Every actual mapped-row input object is its original grouped middle tensor object. -/
theorem mappedRowFiberMap_objects {n : ℕ} (R : Fin n → FiniteFamily (FiniteFamily C))
    (i : Fin (blocksOfFamily (rowCarrierRows R)).totalArity) :
    (blocksOfFamily (rowCarrierRows R)).inputs i =
      (groupsOfFamilies R).groupedTensors.inputs ((mappedRowFiberMap R).inputEquiv i) := by
  have hSource := flattenedPositions_objects (rowCarrierRows R) i
  have hTarget := ((groupsOfFamilies R).groupedMiddle_objects ((mappedRowFiberMap
    R).inputEquiv i)).trans
    ((groupsMiddleOriginalPosition_objects R
      ((groupsOfFamilies R).groupedMiddleEquiv ((mappedRowFiberMap R).inputEquiv i))).trans
        (congrArg (fun p : OriginalPositions R => finiteObj ((R p.1).obj p.2))
          (mappedRowFiberMap_positions R i)))
  exact hSource.trans hTarget.symm

omit [SymmetricCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- The actual mapped-row component is its original input identity with its complete object
transports. -/
theorem mappedRowFiberMap_component_id : ∀ {n : ℕ} (R : Fin n → FiniteFamily (FiniteFamily C))
    (i : Fin (blocksOfFamily (rowCarrierRows R)).totalArity),
    HEq ((mappedRowFiberMap R).inputComponents i) (𝟙 ((blocksOfFamily (rowCarrierRows R)).inputs i))
  | 0, _, i => i.elim0
  | n + 1, R, i => by
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · have h := (sumInputsComponent_left_heq (mappedRowFiberMap (Fin.init R)).inputComponents
          (fun k => eqToHom (rowCarrierToMiddle_objects (R (Fin.last n)) k)) j).trans
            (mappedRowFiberMap_component_id (Fin.init R) j)
        have hId : HEq (𝟙 ((blocksOfFamily (rowCarrierRows R)).inputs
            (Fin.castAdd (arity (rowCarrierFamily (R (Fin.last n)))) j)))
            (𝟙 ((blocksOfFamily (rowCarrierRows (Fin.init R))).inputs j)) := by
          change HEq (𝟙 (Fin.append (blocksOfFamily (rowCarrierRows (Fin.init R))).inputs
            (orderedFamily (rowCarrierFamily (R (Fin.last n)))) (Fin.castAdd _ j))) _
          rw [Fin.append_left]
        exact h.trans hId.symm
      · have h := (sumInputsComponent_right_heq (mappedRowFiberMap (Fin.init R)).inputComponents
          (fun k => eqToHom (rowCarrierToMiddle_objects (R (Fin.last n)) k)) j).trans
            (eqToHom_heq_id_dom _ _ _)
        have hId : HEq (𝟙 ((blocksOfFamily (rowCarrierRows R)).inputs
            (Fin.natAdd (blocksOfFamily (rowCarrierRows (Fin.init R))).totalArity j)))
            (𝟙 (orderedFamily (rowCarrierFamily (R (Fin.last n))) j)) := by
          change HEq (𝟙 (Fin.append (blocksOfFamily (rowCarrierRows (Fin.init R))).inputs
            (orderedFamily (rowCarrierFamily (R (Fin.last n)))) (Fin.natAdd _ j))) _
          rw [Fin.append_right]
        exact h.trans hId.symm

set_option backward.isDefEq.respectTransparency false in
/-- The complete actual mapped-row input map is its original index-bijection equality
isomorphism. -/
theorem mappedRowFiberMap_inputIso {n : ℕ} (R : Fin n → FiniteFamily (FiniteFamily C)) :
    (mappedRowFiberMap R).inputMap =
      (isoEquiv (mappedRowFiberMap R).inputEquiv
        (fun i => eqToIso (mappedRowFiberMap_objects R i))).hom := by
  rw [isoEquiv_hom]
  unfold Blocks.FiberMap.inputMap
  apply mapEquiv_congr rfl
  intro i
  exact (mappedRowFiberMap_component_id R i).trans
    (eqToHom_heq_id_dom _ _ (mappedRowFiberMap_objects R i)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The actual original row-carrier input map is its original tensor-carrier equality map. -/
theorem rowCarrierToMiddle_map (R : FiniteFamily (FiniteFamily C)) :
    mapEquiv (rowCarrierToMiddleEquiv R) (fun i => eqToHom (rowCarrierToMiddle_objects R i)) =
      eqToHom (actualRowCarrier_eq R).symm := by
  have h := congrArg Iso.hom
    (isoEquiv_finCongr (blocksOfFiniteFamily_length R).symm
      (orderedFamily (rowCarrierFamily R)) (blocksOfFiniteFamily R).blockTensors
        (rowCarrierToMiddle_objects R))
  rw [isoEquiv_hom] at h
  exact h

omit [SymmetricCategory C] in
private theorem tensorTransport_heq {L L' A A' B B' : C}
    (hL : L = A ⊗ B) (hL' : A' ⊗ B' = L') (f : A ⟶ A') (g : B ⟶ B') :
    HEq (eqToHom hL ≫ (f ⊗ₘ g) ≫ eqToHom hL') (f ⊗ₘ g) :=
  (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)

omit [MonoidalCategory C] [SymmetricCategory C] in
private theorem identityObject_heq {A B : C} (h : A = B) : HEq (𝟙 A) (𝟙 B) := by
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual outer tensor map of original row-carrier identities is its original outer
tensor identity after carrier
  normalization. -/
theorem mappedRowFiberMap_tensor_id : ∀ {n : ℕ} (R : Fin n → FiniteFamily (FiniteFamily C)),
    HEq (mappedRowFiberMap R).tensorMap (𝟙 (obj (fun i =>
      finiteObj (rowCarrierFamily (R i))))) := by
  intro n
  induction n with
  | zero =>
      intro R
      change HEq (mapEquiv (Equiv.refl (Fin 0)) (X := Fin.elim0) (Y := Fin.elim0) (fun i =>
        i.elim0)) (𝟙 (𝟙_ C))
      rw [mapEquiv_refl]
      rfl
  | succ n ih =>
      intro R
      let P := Fin.init R
      let B := blocksOfFiniteFamily (R (Fin.last n))
      change HEq (Blocks.FiberMap.snoc (mappedRowFiberMap P) (rowCarrierToMiddleEquiv (R
        (Fin.last n)))
        (fun i => eqToHom (rowCarrierToMiddle_objects (R (Fin.last n)) i))).tensorMap _
      rw [Blocks.FiberMap.tensorMap_snoc]
      have hRow : HEq
          (mapEquiv (rowCarrierToMiddleEquiv (R (Fin.last n)))
            (fun i => eqToHom (rowCarrierToMiddle_objects (R (Fin.last n)) i)))
          (𝟙 (finiteObj (rowCarrierFamily (R (Fin.last n))))) :=
        (heq_of_eq (rowCarrierToMiddle_map (R (Fin.last n)))).trans (eqToHom_heq_id_dom _ _ _)
      have hStrip := tensorTransport_heq
        (Blocks.obj_blockTensors_snoc (blocksOfFamily (rowCarrierRows P))
          (orderedFamily (rowCarrierFamily (R (Fin.last n)))))
        (Blocks.obj_blockTensors_snoc (groupsOfFamilies P).groupedTensors B.blockTensors).symm
        (mappedRowFiberMap P).tensorMap
        (mapEquiv (rowCarrierToMiddleEquiv (R (Fin.last n)))
          (fun i => eqToHom (rowCarrierToMiddle_objects (R (Fin.last n)) i)))
      have hTensor := tensorMapBoundary_heq (blocksOfFamily_tensors (rowCarrierRows P))
        (rowFoldTarget_eq P)
        rfl (actualRowCarrier_eq (R (Fin.last n))) (ih P) hRow
      have hId := id_tensorHom_id (obj (fun i => finiteObj (rowCarrierFamily (P i))))
        (finiteObj (rowCarrierFamily (R (Fin.last n))))
      have hObj : (obj (fun i => finiteObj (rowCarrierFamily (P i)))) ⊗
          finiteObj (rowCarrierFamily (R (Fin.last n))) = obj (fun i =>
            finiteObj (rowCarrierFamily (R i))) := rfl
      simpa only [Category.assoc, P, B, rowCarrierRows, Groups.groupedTensors] using
        hStrip.trans (hTensor.trans ((heq_of_eq hId).trans (identityObject_heq hObj)))

set_option backward.isDefEq.respectTransparency false in
/-- The actual mapped-row outer tensor map retains the complete original source and target
carrier equality maps. -/
theorem mappedRowFiberMap_tensor {n : ℕ} (R : Fin n → FiniteFamily (FiniteFamily C)) :
    (mappedRowFiberMap R).tensorMap ≫ eqToHom (rowFoldTarget_eq R) =
      eqToHom (blocksOfFamily_tensors (rowCarrierRows R)) := by
  have hL := (comp_eqToHom_heq (mappedRowFiberMap R).tensorMap (rowFoldTarget_eq R)).trans
    (mappedRowFiberMap_tensor_id R)
  have hR := eqToHom_heq_id_cod _ _ (blocksOfFamily_tensors (rowCarrierRows R))
  exact eq_of_heq (hL.trans hR.symm)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_MappedTensorRowMaps

/- Source proof segment: MappedTensorRowsNormalization -/
section source_MappedTensorRowsNormalization
/-!
# Actual flattening of the original mapped tensor rows

The original middle carrier enumeration maps to its actual grouped
middle tensor word. The produced original flattening map is that
input comparison followed by the original grouped block fold and
the actual original outer row-carrier equality map.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The actual mapped tensor row word is the original ordered family of row carrier words. -/
theorem mappedTensorRows_sourceBlocks (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    blocksOfFiniteFamily (mappedTensorRows X) = blocksOfFamily (rowCarrierRows (X.obj ∘
      enumeration X)) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every actual mapped-row input retains its original outer and middle label in the grouped
word. -/
theorem mappedTensorRows_inputLabel (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (i : Fin (blocksOfFiniteFamily (mappedTensorRows X)).totalArity) :
    groupedTripleMiddleEquiv X ((mappedRowFiberMap (X.obj ∘ enumeration X)).inputEquiv i) =
      nestedPositionsEquiv (mappedTensorRows X) i :=
  congrArg (originalOuterPositionsEquiv (C := FiniteFamily C) X)
    (mappedRowFiberMap_positions (X.obj ∘ enumeration X) i)

set_option backward.isDefEq.respectTransparency false in
/-- The original mapped middle-carrier input maps compose to their actual grouped middle
input comparison. -/
theorem mappedTensorRows_inputEquiv (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    (flattenWordEquiv (mappedTensorRows X)).trans
        (mappedRowFiberMap (X.obj ∘ enumeration X)).inputEquiv =
          groupedMiddleCarrierWordEquiv X := by
  apply Equiv.ext
  intro i
  apply (groupedTripleMiddleEquiv X).injective
  have hL := (mappedTensorRows_inputLabel X (flattenWordEquiv (mappedTensorRows X) i)).trans
    (nestedPositions_flattenWord (mappedTensorRows X) i)
  have hR := (groupedTripleMiddleEquiv X).apply_symm_apply (enumeration (middleCarrierFamily X) i)
  exact hL.trans hR.symm

set_option backward.isDefEq.respectTransparency false in
/-- The complete original mapped row input tensor maps give the actual grouped middle
carrier word isomorphism. -/
theorem mappedTensorRows_inputMap (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    flattenToWord (mappedTensorRows X) ≫ (mappedRowFiberMap (X.obj ∘ enumeration X)).inputMap =
      (groupedMiddleCarrierWordIso X).hom := by
  rw [mappedRowFiberMap_inputIso, isoEquiv_hom]
  unfold flattenToWord groupedMiddleCarrierWordIso
  rw [isoEquiv_hom, mapEquiv_comp]
  apply mapEquiv_congr (mappedTensorRows_inputEquiv X)
  intro i
  exact inputEquality_hom_chain (flattenWord_objects (mappedTensorRows X) i)
    (mappedRowFiberMap_objects (X.obj ∘ enumeration X) (flattenWordEquiv (mappedTensorRows X) i))
    (groupedMiddleCarrierWord_objects X i)

set_option backward.isDefEq.respectTransparency false in
/-- The actual constructed original flattening of mapped tensor rows is the original grouped
middle-word map and grouped
  fold. -/
theorem finiteFlatten_mappedTensorRows (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    (finiteFlattenIso (mappedTensorRows X)).hom =
      (groupedMiddleCarrierWordIso X).hom ≫
        (Blocks.flattenIso (groupsOfFiniteFamilies X).groupedTensors).hom ≫
        eqToHom (groupedOuterRowCarrier_eq X) := by
  let R := X.obj ∘ enumeration X
  let G := groupsOfFamilies R
  let a := flattenToWord (mappedTensorRows X)
  let f := mappedRowFiberMap R
  have hFiber := congrArg (fun m => a ≫ m ≫ eqToHom (rowFoldTarget_eq R)) f.flatten_naturality
  have hTensor := congrArg (fun m => a ≫ (Blocks.flattenIso (blocksOfFamily
    (rowCarrierRows R))).hom ≫ m)
    (mappedRowFiberMap_tensor R)
  have hInput := congrArg (fun m => m ≫ (Blocks.flattenIso G.groupedTensors).hom ≫
    eqToHom (rowFoldTarget_eq R)) (mappedTensorRows_inputMap X)
  have hStart : (finiteFlattenIso (mappedTensorRows X)).hom =
      a ≫ (Blocks.flattenIso (blocksOfFamily (rowCarrierRows R))).hom ≫
        eqToHom (blocksOfFamily_tensors (rowCarrierRows R)) := by
    rw [finiteFlattenIso_hom]
    unfold finiteFlattenHom finiteFamilyBlocksIso blocksOfFamilyIso
    simp only [Iso.trans_hom, eqToIso.hom]
    rfl
  simp only [Category.assoc] at hFiber hTensor hInput
  exact hStart.trans (hTensor.symm.trans (hFiber.symm.trans hInput))

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_MappedTensorRowsNormalization

/- Source proof segment: OriginalMemberActualInputMap -/
section source_OriginalMemberActualInputMap
/-!
# Actual original member input map and its full equality components

The actual morphism is normalized only by its proved target block-word
count and carrier equality. Every component is its original object
equality map, before choosing the desired triple input identification.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C]

/-- The original family equality morphism preserves each original object
at its actual input target. -/
theorem familyEquality_input_objects {A B : FiniteFamily C} (h : A = B) (j : A.index) :
    A.obj j = B.obj ((eqToHom h).equiv j) := by
  cases h
  rfl

/-- Every original ordered equality reindexing preserves its actual complete input object. -/
theorem orderedReindex_input_objects {m n : ℕ} (e : Fin m ≃ Fin n)
    (X : Fin m → FiniteFamily C) (Y : Fin n → FiniteFamily C)
    (h : ∀ i, X i = Y (e i)) (j : Fin (blocksOfFamily X).totalArity) :
    (blocksOfFamily X).inputs j =
      (blocksOfFamily Y).inputs (orderedInputEquiv (orderedReindexHom e X Y h) j) := by
  let p := flattenedPositionsEquiv X j
  have hh := familyEquality_input_objects (h p.1) p.2
  exact (flattenedPositions_objects X j).trans
    (hh.trans (orderedInput_target_objects (orderedReindexHom e X Y h) j).symm)

/-- The actual original member input equivalence in the exact concatenated row target count. -/
noncomputable def flatMembersActualInputEquiv
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    Fin (blocksOfFiniteFamily (flattenedMiddleFamily X)).totalArity ≃
      Fin (groupsOfFiniteFamilies X).flat.totalArity :=
  (orderedInputEquiv (flatMembersOriginalHom X)).trans
    (finCongr (congrArg Blocks.totalArity (flatMembers_original_blocks X)))

/-- Every actual original member input keeps its source object in the concatenated target. -/
theorem flatMembersActualInput_objects
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (j : Fin (blocksOfFiniteFamily (flattenedMiddleFamily X)).totalArity) :
    (blocksOfFiniteFamily (flattenedMiddleFamily X)).inputs j =
      (groupsOfFiniteFamilies X).flat.inputs (flatMembersActualInputEquiv X j) :=
  (orderedReindex_input_objects (flatMembersOriginalReindex X)
    (orderedFamily (flattenedMiddleFamily X)) (tripleFamilyWord X).members
    (flatMembers_original_family X) j).trans
      (blocks_inputs_transport (flatMembers_original_blocks X)
        (orderedInputEquiv (flatMembersOriginalHom X) j))

variable [MonoidalCategory C] [SymmetricCategory C]

/-- The original tensor map of the actual complete input bijection
and original equality components. -/
noncomputable def flatMembersActualInputDataMap
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    obj (blocksOfFiniteFamily (flattenedMiddleFamily X)).inputs ⟶
      obj (groupsOfFiniteFamilies X).flat.inputs :=
  mapEquiv (flatMembersActualInputEquiv X) (fun j => eqToHom (flatMembersActualInput_objects X j))

/-- The original ordered member input map keeps the complete actual normalized map data. -/
theorem flatMembersActualInputMap_heq
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    HEq (orderedInputMap (flatMembersOriginalHom X)) (flatMembersActualInputDataMap X) := by
  have he : HEq (orderedInputEquiv (flatMembersOriginalHom X)) (flatMembersActualInputEquiv X) := by
    change HEq (orderedInputEquiv (flatMembersOriginalHom X))
      ((orderedInputEquiv (flatMembersOriginalHom X)).trans
        (finCongr (congrArg Blocks.totalArity (flatMembers_original_blocks X))))
    simpa only [finCongr_refl, Equiv.refl_symm, Equiv.refl_trans] using
      (equiv_count_transport_heq rfl
        (congrArg Blocks.totalArity (flatMembers_original_blocks X))
        (orderedInputEquiv (flatMembersOriginalHom X))).symm
  apply mapEquiv_input_heq rfl
    (congrArg Blocks.totalArity (flatMembers_original_blocks X))
    (blocksOfFiniteFamily (flattenedMiddleFamily X)).inputs
    (blocksOfFiniteFamily (flattenedMiddleFamily X)).inputs
    (blocksOfFamily (tripleFamilyWord X).members).inputs
    (groupsOfFiniteFamilies X).flat.inputs
    (fun _ => rfl) (blocks_inputs_transport (flatMembers_original_blocks X))
    (orderedInputEquiv (flatMembersOriginalHom X)) (flatMembersActualInputEquiv X) he
    (orderedInputComponent (flatMembersOriginalHom X))
    (fun j => eqToHom (flatMembersActualInput_objects X j))
  intro j
  exact (orderedReindex_component_id (flatMembersOriginalReindex X)
    (orderedFamily (flattenedMiddleFamily X)) (tripleFamilyWord X).members
    (flatMembers_original_family X) j).trans
      (eqToHom_heq_id_dom _ _ (flatMembersActualInput_objects X j)).symm

/-- The actual original member input map is the normalized actual bijection
with original equality components. -/
theorem flatMembersOriginalInputMap_actual_data
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    flatMembersOriginalInputMap X = flatMembersActualInputDataMap X := by
  exact eq_of_heq ((comp_eqToHom_heq_iff
    (orderedInputMap (flatMembersOriginalHom X)) (flatMembersActualInputDataMap X)
    (flatMembersHom_input_target X)).mpr (flatMembersActualInputMap_heq X))

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OriginalMemberActualInputMap

/- Source proof segment: OriginalConcatPositions -/
section source_OriginalConcatPositions
/-!
# Complete original input positions under block concatenation

The actual concatenation splits every original block input into its
original left or right word position. The index map agrees with the
actual total-count transport and original finite sum decomposition.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace CategoryTheory.MonoidalCategory.OrderedTensor

/-- The original finite sum decomposition respects its complete three-block associator. -/
theorem finiteSumPosition_assoc {a b c : ℕ} {P : Type u} {Q : Type v} {R : Type w}
    (e : Fin a ≃ P) (d : Fin b ≃ Q) (f : Fin c ≃ R) (i : Fin ((a + b) + c)) :
    Equiv.sumAssoc P Q R
        ((Equiv.sumCongr (finSumFinEquiv.symm.trans (Equiv.sumCongr e d)) f)
          (finSumFinEquiv.symm i)) =
      (Equiv.sumCongr e (finSumFinEquiv.symm.trans (Equiv.sumCongr d f)))
        (finSumFinEquiv.symm (Fin.cast (Nat.add_assoc a b c) i)) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · have hc : Fin.cast (Nat.add_assoc a b c)
          (Fin.castAdd c (Fin.castAdd b k)) = Fin.castAdd (b + c) k := Fin.ext rfl
      rw [hc, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd]
      change Equiv.sumAssoc P Q R
        (Sum.inl ((Equiv.sumCongr e d) (finSumFinEquiv.symm (Fin.castAdd b k)))) = Sum.inl (e k)
      rw [finSumFinEquiv_symm_apply_castAdd]
      rfl
    · have hc : Fin.cast (Nat.add_assoc a b c)
          (Fin.castAdd c (Fin.natAdd a k)) = Fin.natAdd a (Fin.castAdd c k) := Fin.ext rfl
      rw [hc, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
      change Equiv.sumAssoc P Q R
          (Sum.inl ((Equiv.sumCongr e d) (finSumFinEquiv.symm (Fin.natAdd a k)))) =
        Sum.inr ((Equiv.sumCongr d f) (finSumFinEquiv.symm (Fin.castAdd c k)))
      rw [finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_castAdd]
      rfl
  · have hc : Fin.cast (Nat.add_assoc a b c) (Fin.natAdd (a + b) j) =
        Fin.natAdd a (Fin.natAdd b j) := Fin.ext (Nat.add_assoc a b j.val)
    rw [hc, finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_natAdd]
    change Equiv.sumAssoc P Q R (Sum.inr (f j)) =
      Sum.inr ((Equiv.sumCongr d f) (finSumFinEquiv.symm (Fin.natAdd b j)))
    rw [finSumFinEquiv_symm_apply_natAdd]
    rfl

/-- The complete actual three-block position labels respect an original prefix count cast. -/
theorem finiteSumPosition_assoc_count {a b c m : ℕ} {P : Type u} {Q : Type v}
    (hm : m = a + b) (ht : m + c = a + (b + c))
    (e : Fin a ≃ P) (d : Fin b ≃ Q) (f : Fin m ≃ (P ⊕ Q))
    (hf : ∀ j, f j = (Equiv.sumCongr e d) (finSumFinEquiv.symm (Fin.cast hm j)))
    (i : Fin (m + c)) :
    Equiv.sumAssoc P Q (Fin c) ((Equiv.sumCongr f (Equiv.refl (Fin c))) (finSumFinEquiv.symm i)) =
      (Equiv.sumCongr e (finSumFinEquiv.symm.trans (Equiv.sumCongr d (Equiv.refl (Fin c)))))
        (finSumFinEquiv.symm (Fin.cast ht i)) := by
  subst m
  have hfe : f = finSumFinEquiv.symm.trans (Equiv.sumCongr e d) := by
    apply Equiv.ext
    intro j
    exact hf j
  subst f
  exact finiteSumPosition_assoc e d (Equiv.refl (Fin c)) i

namespace Blocks

variable {C : Type u}

/-- The complete original input-position decomposition of actual block concatenation. -/
def concatPositionEquiv (B : Blocks C) : (D : Blocks C) →
    (concat B D).position ≃ (B.position ⊕ D.position)
  | .nil => (Equiv.sumEmpty B.position Empty).symm
  | .snoc D (arity := n) _X =>
      (Equiv.sumCongr (concatPositionEquiv B D) (Equiv.refl (Fin n))).trans
        (Equiv.sumAssoc B.position D.position (Fin n))

set_option backward.isDefEq.respectTransparency false in
/-- The actual original concatenated input index has its complete original left/right position. -/
theorem concatPositionEquiv_inputs (B : Blocks C) :
    ∀ (D : Blocks C) (i : Fin (concat B D).totalArity),
    concatPositionEquiv B D ((concat B D).positionEquiv i) =
      (Equiv.sumCongr B.positionEquiv D.positionEquiv)
        (finSumFinEquiv.symm (Fin.cast (concat_totalArity B D) i))
  | .nil, i => by
      change Sum.inl (B.positionEquiv i) =
        (Equiv.sumCongr B.positionEquiv (Equiv.equivEmpty (Fin 0)))
          (finSumFinEquiv.symm (Fin.castAdd 0 i))
      rw [finSumFinEquiv_symm_apply_castAdd]
      rfl
  | .snoc D (arity := n) X, i => by
      let f : Fin (concat B D).totalArity ≃ (B.position ⊕ D.position) :=
        (concat B D).positionEquiv.trans (concatPositionEquiv B D)
      have hf : ∀ j, f j = (Equiv.sumCongr B.positionEquiv D.positionEquiv)
          (finSumFinEquiv.symm (Fin.cast (concat_totalArity B D) j)) :=
        concatPositionEquiv_inputs B D
      have hh := finiteSumPosition_assoc_count (concat_totalArity B D)
        (concat_totalArity B (Blocks.snoc D X)) B.positionEquiv D.positionEquiv f hf i
      have hfold : ∀ p : Fin (concat B D).totalArity ⊕ Fin n,
          (Equiv.sumCongr (concatPositionEquiv B D) (Equiv.refl (Fin n)))
            ((Equiv.sumCongr (concat B D).positionEquiv (Equiv.refl (Fin n)))
              p) = (Equiv.sumCongr f (Equiv.refl (Fin n))) p := by
        intro p
        cases p
        all_goals rfl
      change Equiv.sumAssoc B.position D.position (Fin n)
        ((Equiv.sumCongr (concatPositionEquiv B D) (Equiv.refl (Fin n)))
          ((Equiv.sumCongr (concat B D).positionEquiv (Equiv.refl (Fin n)))
            (finSumFinEquiv.symm i))) = _
      rw [hfold]
      exact hh

end Blocks

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OriginalConcatPositions

/- Source proof segment: OriginalBlockInputCoordinates -/
section source_OriginalBlockInputCoordinates
/-!
# Complete original block coordinates of a flattened input position

Every original block input retains its original middle block slot,
original input arity and original inner ordered slot. These coordinates
are defined from the actual original block word, independently of objects.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

namespace Blocks

variable {C : Type u}

/-- The original middle block slot of an actual original input position. -/
def inputBlockIndex : (B : Blocks C) → B.position → Fin B.length
  | .nil, p => Empty.elim p
  | .snoc B _, .inl p => (inputBlockIndex B p).castSucc
  | .snoc B _, .inr _ => Fin.last B.length

/-- The original input arity at an actual original block position. -/
def inputArity : (B : Blocks C) → B.position → ℕ
  | .nil, p => Empty.elim p
  | .snoc B _, .inl p => inputArity B p
  | .snoc _ (arity := n) _, .inr _ => n

/-- The complete original ordered slot inside the original input block. -/
def inputSlot : (B : Blocks C) → (p : B.position) → Fin (B.inputArity p)
  | .nil, p => Empty.elim p
  | .snoc B _, .inl p => inputSlot B p
  | .snoc _ _, .inr p => p

end Blocks

variable {C : Type u}

/-- Actual original family input labels identify their original middle block slots. -/
theorem blockPositions_inputBlockIndex : ∀ {n : ℕ} (F : Fin n → FiniteFamily C)
    (p : (blocksOfFamily F).position),
    Fin.cast (blocksOfFamily_length F) ((blocksOfFamily F).inputBlockIndex p) =
      (blockPositionsEquiv F p).1
  | 0, _, p => Empty.elim p
  | n + 1, F, .inl p => by
      change Fin.cast (blocksOfFamily_length F)
        ((blocksOfFamily (Fin.init F)).inputBlockIndex p).castSucc =
        (blockPositionsEquiv (Fin.init F) p).1.castSucc
      have hc : Fin.cast (blocksOfFamily_length F)
          ((blocksOfFamily (Fin.init F)).inputBlockIndex p).castSucc =
          (Fin.cast (blocksOfFamily_length (Fin.init F))
            ((blocksOfFamily (Fin.init F)).inputBlockIndex p)).castSucc := Fin.ext rfl
      exact hc.trans (congrArg Fin.castSucc (blockPositions_inputBlockIndex (Fin.init F) p))
  | n + 1, F, .inr _ => by
      change Fin.cast (blocksOfFamily_length F) (Fin.last (blocksOfFamily (Fin.init F)).length) =
        Fin.last n
      apply Fin.ext
      exact blocksOfFamily_length (Fin.init F)

/-- Every actual original family input position retains its original input arity. -/
theorem blockPositions_inputArity : ∀ {n : ℕ} (F : Fin n → FiniteFamily C)
    (p : (blocksOfFamily F).position),
    arity (F (blockPositionsEquiv F p).1) = (blocksOfFamily F).inputArity p
  | 0, _, p => Empty.elim p
  | _n + 1, F, .inl p => blockPositions_inputArity (Fin.init F) p
  | _n + 1, _F, .inr _ => rfl

/-- The complete original family inner input is the original enumeration
of its actual ordered slot. -/
theorem blockPositions_inputSlot : ∀ {n : ℕ} (F : Fin n → FiniteFamily C)
    (p : (blocksOfFamily F).position),
    (blockPositionsEquiv F p).2 =
      enumeration (F (blockPositionsEquiv F p).1)
        (Fin.cast (blockPositions_inputArity F p).symm ((blocksOfFamily F).inputSlot p))
  | 0, _, p => Empty.elim p
  | _n + 1, F, .inl p => blockPositions_inputSlot (Fin.init F) p
  | _n + 1, _F, .inr _ => rfl

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OriginalBlockInputCoordinates

/- Source proof segment: ConcatInputCoordinates -/
section source_ConcatInputCoordinates
/-!
# Complete original block-input coordinates under concatenation

The original left/right position decomposition retains both the
middle block slot and the full original ordered inner input slot.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

/-- The original finite two-block sum decomposition retains an added final block slot. -/
theorem finiteSum_castSucc_split {a b m : ℕ} (hm : m = a + b)
    (ht : m + 1 = a + (b + 1)) (j : Fin m) :
    finSumFinEquiv.symm (Fin.cast ht j.castSucc) =
      Sum.map id Fin.castSucc (finSumFinEquiv.symm (Fin.cast hm j)) := by
  subst hm
  change finSumFinEquiv.symm (Fin.cast ht j.castSucc) =
    Sum.map id Fin.castSucc (finSumFinEquiv.symm j)
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · have hi : Fin.cast ht (Fin.castAdd b i).castSucc = Fin.castAdd (b + 1) i := Fin.ext rfl
    rw [hi, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd]
    rfl
  · have hi : Fin.cast ht (Fin.natAdd a i).castSucc = Fin.natAdd a i.castSucc := Fin.ext rfl
    rw [hi, finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_natAdd]
    rfl

namespace Blocks

variable {C : Type u}

/-- The original input arity on the original left/right position sum. -/
def sumInputArity (B D : Blocks C) : B.position ⊕ D.position → ℕ :=
  Sum.elim B.inputArity D.inputArity

/-- The complete original inner slot on the original left/right position sum. -/
def sumInputSlot (B D : Blocks C) : (p : B.position ⊕ D.position) → Fin (sumInputArity B D p)
  | .inl p => B.inputSlot p
  | .inr p => D.inputSlot p

/-- The actual original concatenation retains the middle block index of each original input. -/
theorem concat_inputBlockIndex (B : Blocks C) : ∀ (D : Blocks C)
    (p : (concat B D).position),
    finSumFinEquiv.symm (Fin.cast (concat_length B D) ((concat B D).inputBlockIndex p)) =
      Sum.elim (fun q => Sum.inl (B.inputBlockIndex q))
        (fun q => Sum.inr (D.inputBlockIndex q)) (concatPositionEquiv B D p)
  | .nil, p => by
      change finSumFinEquiv.symm (Fin.castAdd 0 (B.inputBlockIndex p)) = Sum.inl _
      rw [finSumFinEquiv_symm_apply_castAdd]
  | .snoc D X, .inl p => by
      change finSumFinEquiv.symm
        (Fin.cast (concat_length B (Blocks.snoc D X)) ((concat B D).inputBlockIndex p).castSucc) = _
      have hs := finiteSum_castSucc_split (concat_length B D)
        (concat_length B (Blocks.snoc D X)) ((concat B D).inputBlockIndex p)
      have ht := congrArg (Sum.map id Fin.castSucc) (concat_inputBlockIndex B D p)
      have hr : Sum.map id Fin.castSucc
          (Sum.elim (fun q => Sum.inl (B.inputBlockIndex q))
            (fun q => Sum.inr (D.inputBlockIndex q)) (concatPositionEquiv B D p)) =
          Sum.elim (fun q => Sum.inl (B.inputBlockIndex q))
            (fun q => Sum.inr ((Blocks.snoc D X).inputBlockIndex q))
            (concatPositionEquiv B (Blocks.snoc D X) (Sum.inl p)) := by
        change _ = Sum.elim _ _
          (Equiv.sumAssoc B.position D.position _ (Sum.inl (concatPositionEquiv B D p)))
        cases h : concatPositionEquiv B D p <;> rfl
      exact hs.trans (ht.trans hr)
  | .snoc D X, .inr _ => by
      have hi : Fin.cast (concat_length B (Blocks.snoc D X)) (Fin.last (concat B D).length) =
          Fin.natAdd B.length (Fin.last D.length) := by
        apply Fin.ext
        exact concat_length B D
      change finSumFinEquiv.symm
        (Fin.cast (concat_length B (Blocks.snoc D X)) (Fin.last (concat B D).length)) =
          Sum.inr (Fin.last D.length)
      exact (congrArg finSumFinEquiv.symm hi).trans (finSumFinEquiv_symm_apply_natAdd _)

/-- Actual original concatenation preserves every original input arity. -/
theorem concat_inputArity (B : Blocks C) : ∀ (D : Blocks C)
    (p : (concat B D).position),
    (concat B D).inputArity p = sumInputArity B D (concatPositionEquiv B D p)
  | .nil, _p => rfl
  | .snoc D X, .inl p => by
      change (concat B D).inputArity p = sumInputArity B (Blocks.snoc D X)
        (Equiv.sumAssoc B.position D.position _ (Sum.inl (concatPositionEquiv B D p)))
      have hi := concat_inputArity B D p
      cases h : concatPositionEquiv B D p
      · rw [h] at hi
        exact hi
      · rw [h] at hi
        exact hi
  | .snoc _D _X, .inr _p => rfl

/-- Actual original concatenation preserves the complete original ordered inner input slot. -/
theorem concat_inputSlot_heq (B : Blocks C) : ∀ (D : Blocks C)
    (p : (concat B D).position),
    HEq ((concat B D).inputSlot p) (sumInputSlot B D (concatPositionEquiv B D p))
  | .nil, _p => HEq.rfl
  | .snoc D X, .inl p => by
      change HEq ((concat B D).inputSlot p) (sumInputSlot B (Blocks.snoc D X)
        (Equiv.sumAssoc B.position D.position _ (Sum.inl (concatPositionEquiv B D p))))
      have hi := concat_inputSlot_heq B D p
      cases h : concatPositionEquiv B D p
      · rw [h] at hi
        exact hi
      · rw [h] at hi
        exact hi
  | .snoc _D _X, .inr _p => HEq.rfl

end Blocks

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ConcatInputCoordinates

/- Source proof segment: GroupedPhysicalInput -/
section source_GroupedPhysicalInput
/-!
# Full original row inputs from actual block-word positions

The physical original block position identifies its complete original
row input. Its original inner slot is preserved under every concat.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory

variable {C : Type u}

/-- The full original middle and inner labels of an original row block position. -/
noncomputable def rowBlockOriginalPositions (Y : FiniteFamily (FiniteFamily C)) :
    (blocksOfFiniteFamily Y).position ≃ NestedPositions Y :=
  (blockPositionsEquiv (orderedFamily Y)).trans (originalOuterPositionsEquiv Y)

/-- The original middle finite-family member at a full original row input. -/
def orderedRowMember {n : ℕ} (R : Fin n → FiniteFamily (FiniteFamily C))
    (p : OrderedRowPositions R) : FiniteFamily C := (R p.1).obj p.2.1

/-- Equal complete original row positions retain their complete original inner inputs. -/
theorem orderedRowInner_heq {n : ℕ} {R : Fin n → FiniteFamily (FiniteFamily C)}
    {p q : OrderedRowPositions R} (h : p = q) : HEq p.2.2 q.2.2 := by
  cases h
  rfl

/-- Complete original family and slot equalities retain the actual original enumeration. -/
theorem familyEnumeration_slot_heq {a b : ℕ} (F G : FiniteFamily C) (h : F = G)
    (ha : a = arity F) (hb : b = arity G) (x : Fin a) (y : Fin b) (hxy : HEq x y) :
    HEq (enumeration F (Fin.cast ha x)) (enumeration G (Fin.cast hb y)) := by
  cases h
  subst ha
  subst hb
  exact heq_of_eq (congrArg (enumeration F) (eq_of_heq hxy))

variable [Category.{v} C]

/-- The full original row positions of the actual physical concatenated block word. -/
noncomputable def groupsPhysicalInputEquiv :
    {n : ℕ} → (R : Fin n → FiniteFamily (FiniteFamily C)) →
      (groupsOfFamilies R).flat.position ≃ OrderedRowPositions R
  | 0, R => by
      haveI : IsEmpty (OrderedRowPositions R) := ⟨fun p => p.1.elim0⟩
      exact (Equiv.equivEmpty (OrderedRowPositions R)).symm
  | n + 1, R =>
      (Blocks.concatPositionEquiv (groupsOfFamilies (Fin.init R)).flat
        (blocksOfFiniteFamily (R (Fin.last n)))).trans
        ((Equiv.sumCongr (groupsPhysicalInputEquiv (Fin.init R))
          (rowBlockOriginalPositions (R (Fin.last n)))).trans (rowPositionsSnocEquiv R))

/-- The physical original group position is the actual original ordered input position. -/
theorem groupsPhysicalInput_indices :
    ∀ {n : ℕ} (R : Fin n → FiniteFamily (FiniteFamily C))
    (i : Fin (groupsOfFamilies R).flat.totalArity),
    groupsPhysicalInputEquiv R ((groupsOfFamilies R).flat.positionEquiv i) =
      groupsOriginalPositions R ((groupsOfFamilies R).flatInputEquiv i)
  | 0, _, i => Fin.elim0 i
  | n + 1, R, i => by
      let B := (groupsOfFamilies (Fin.init R)).flat
      let D := blocksOfFiniteFamily (R (Fin.last n))
      let f : B.position ≃ OrderedRowPositions (Fin.init R) := groupsPhysicalInputEquiv (Fin.init R)
      let d : D.position ≃ NestedPositions (R (Fin.last n)) :=
        rowBlockOriginalPositions (R (Fin.last n))
      let z := finSumFinEquiv.symm (Fin.cast (Blocks.concat_totalArity B D) i)
      have hf : ∀ q : Fin B.totalArity ⊕ Fin D.totalArity,
          (Equiv.sumCongr f d) ((Equiv.sumCongr B.positionEquiv D.positionEquiv) q) =
            (Equiv.sumCongr (groupsOriginalPositions (Fin.init R))
              (nestedPositionsEquiv (R (Fin.last n))))
              ((Equiv.sumCongr (groupsOfFamilies (Fin.init R)).flatInputEquiv
                (Equiv.refl (Fin D.totalArity))) q) := by
        intro q
        cases q with
        | inl j => exact congrArg Sum.inl (groupsPhysicalInput_indices (Fin.init R) j)
        | inr j => rfl
      have hc := congrArg (fun p : B.position ⊕ D.position =>
        rowPositionsSnocEquiv R ((Equiv.sumCongr f d) p))
        (Blocks.concatPositionEquiv_inputs B D i)
      exact hc.trans (congrArg (rowPositionsSnocEquiv R) (hf z))

/-- The complete original group position associated with an arbitrary physical input. -/
theorem groupsPhysicalInput_actual {n : ℕ} (R : Fin n → FiniteFamily (FiniteFamily C))
    (p : (groupsOfFamilies R).flat.position) :
    groupsPhysicalInputEquiv R p = groupsOriginalPositions R
      ((groupsOfFamilies R).flatInputEquiv ((groupsOfFamilies R).flat.positionEquiv.symm p)) := by
  have h := groupsPhysicalInput_indices R ((groupsOfFamilies R).flat.positionEquiv.symm p)
  exact (congrArg (groupsPhysicalInputEquiv R)
    ((groupsOfFamilies R).flat.positionEquiv.apply_symm_apply p)).symm.trans h

/-- The actual original finite-family member of a physical original group input. -/
noncomputable def groupsPhysicalMember {n : ℕ} (R : Fin n → FiniteFamily (FiniteFamily C))
    (p : (groupsOfFamilies R).flat.position) : FiniteFamily C :=
  orderedRowMember R (groupsPhysicalInputEquiv R p)

/-- The complete original group member retains the original physical input arity. -/
theorem groupsPhysicalInput_arity :
    ∀ {n : ℕ} (R : Fin n → FiniteFamily (FiniteFamily C))
    (p : (groupsOfFamilies R).flat.position),
    arity (groupsPhysicalMember R p) = (groupsOfFamilies R).flat.inputArity p
  | 0, _, p => Empty.elim p
  | n + 1, R, p => by
      let B := (groupsOfFamilies (Fin.init R)).flat
      let D := blocksOfFiniteFamily (R (Fin.last n))
      have hc := Blocks.concat_inputArity B D p
      cases h : Blocks.concatPositionEquiv B D p with
      | inl q =>
          have hp := congrArg (fun s : B.position ⊕ D.position =>
            rowPositionsSnocEquiv R ((Equiv.sumCongr (groupsPhysicalInputEquiv (Fin.init R))
              (rowBlockOriginalPositions (R (Fin.last n)))) s)) h
          have hm : groupsPhysicalMember R p = groupsPhysicalMember (Fin.init R) q :=
            congrArg (orderedRowMember R) hp
          rw [h] at hc
          exact (congrArg arity hm).trans ((groupsPhysicalInput_arity (Fin.init R) q).trans hc.symm)
      | inr q =>
          have hp := congrArg (fun s : B.position ⊕ D.position =>
            rowPositionsSnocEquiv R ((Equiv.sumCongr (groupsPhysicalInputEquiv (Fin.init R))
              (rowBlockOriginalPositions (R (Fin.last n)))) s)) h
          have hm : groupsPhysicalMember R p =
              orderedFamily (R (Fin.last n))
                (blockPositionsEquiv (orderedFamily (R (Fin.last n))) q).1 :=
            congrArg (orderedRowMember R) hp
          rw [h] at hc
          exact (congrArg arity hm).trans
            ((blockPositions_inputArity (orderedFamily (R (Fin.last n))) q).trans hc.symm)

/-- The complete original inner input is the actual original member enumeration
at its physical slot. -/
theorem groupsPhysicalInput_slot :
    ∀ {n : ℕ} (R : Fin n → FiniteFamily (FiniteFamily C))
    (p : (groupsOfFamilies R).flat.position),
    HEq (groupsPhysicalInputEquiv R p).2.2
      (enumeration (groupsPhysicalMember R p)
        (Fin.cast (groupsPhysicalInput_arity R p).symm ((groupsOfFamilies R).flat.inputSlot p)))
  | 0, _, p => Empty.elim p
  | n + 1, R, p => by
      let B := (groupsOfFamilies (Fin.init R)).flat
      let D := blocksOfFiniteFamily (R (Fin.last n))
      have hs := Blocks.concat_inputSlot_heq B D p
      cases h : Blocks.concatPositionEquiv B D p with
      | inl q =>
          have hp := congrArg (fun s : B.position ⊕ D.position =>
            rowPositionsSnocEquiv R ((Equiv.sumCongr (groupsPhysicalInputEquiv (Fin.init R))
              (rowBlockOriginalPositions (R (Fin.last n)))) s)) h
          have hm : groupsPhysicalMember R p = groupsPhysicalMember (Fin.init R) q :=
            congrArg (orderedRowMember R) hp
          rw [h] at hs
          have he := familyEnumeration_slot_heq
            (groupsPhysicalMember (Fin.init R) q) (groupsPhysicalMember R p) hm.symm
            (groupsPhysicalInput_arity (Fin.init R) q).symm (groupsPhysicalInput_arity R p).symm
            (B.inputSlot q) ((Blocks.concat B D).inputSlot p) hs.symm
          exact (orderedRowInner_heq hp).trans ((groupsPhysicalInput_slot (Fin.init R) q).trans he)
      | inr q =>
          have hp := congrArg (fun s : B.position ⊕ D.position =>
            rowPositionsSnocEquiv R ((Equiv.sumCongr (groupsPhysicalInputEquiv (Fin.init R))
              (rowBlockOriginalPositions (R (Fin.last n)))) s)) h
          have hm : groupsPhysicalMember R p =
              orderedFamily (R (Fin.last n))
                (blockPositionsEquiv (orderedFamily (R (Fin.last n))) q).1 :=
            congrArg (orderedRowMember R) hp
          rw [h] at hs
          have he := familyEnumeration_slot_heq
            (orderedFamily (R (Fin.last n))
              (blockPositionsEquiv (orderedFamily (R (Fin.last n))) q).1)
            (groupsPhysicalMember R p) hm.symm
            (blockPositions_inputArity (orderedFamily (R (Fin.last n))) q).symm
            (groupsPhysicalInput_arity R p).symm (D.inputSlot q)
            ((Blocks.concat B D).inputSlot p) hs.symm
          exact (orderedRowInner_heq hp).trans
            ((heq_of_eq (blockPositions_inputSlot (orderedFamily (R (Fin.last n))) q)).trans he)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_GroupedPhysicalInput

/- Source proof segment: BlockPositionTransport -/
section source_BlockPositionTransport
/-!
# Full original coordinate transport along exact block-word equality

The actual original block-word equality transports its original
position, middle-block index and complete ordered inner input slot.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

namespace Blocks

variable {C : Type u}

/-- Exact original block-word equality preserves the full position equivalence. -/
theorem positionEquiv_transport {B D : Blocks C} (h : B = D) (i : Fin B.totalArity) :
    D.positionEquiv (Fin.cast (congrArg totalArity h) i) =
      cast (congrArg position h) (B.positionEquiv i) := by
  cases h
  rfl

/-- Exact original block-word equality preserves the original middle block slot. -/
theorem inputBlockIndex_transport {B D : Blocks C} (h : B = D) (p : B.position) :
    D.inputBlockIndex (cast (congrArg position h) p) =
      Fin.cast (congrArg length h) (B.inputBlockIndex p) := by
  cases h
  rfl

/-- Exact original block-word equality preserves every original inner input arity. -/
theorem inputArity_transport {B D : Blocks C} (h : B = D) (p : B.position) :
    D.inputArity (cast (congrArg position h) p) = B.inputArity p := by
  cases h
  rfl

/-- Exact original block-word equality preserves the complete original inner ordered slot. -/
theorem inputSlot_transport_heq {B D : Blocks C} (h : B = D) (p : B.position) :
    HEq (D.inputSlot (cast (congrArg position h) p)) (B.inputSlot p) := by
  cases h
  rfl

end Blocks

variable {C : Type u}

/-- Equal full original family positions preserve their complete original inner input. -/
theorem originalInputInner_heq {n : ℕ} {F : Fin n → FiniteFamily C}
    {p q : OriginalPositions F} (h : p = q) : HEq p.2 q.2 := by
  cases h
  rfl

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_BlockPositionTransport

/- Source proof segment: OriginalWordPhysicalLabels -/
section source_OriginalWordPhysicalLabels
/-!
# Actual complete middle-label transport from original word blocks to flat row blocks

The original word labels agree with the original flat group labels
at the same physical block position, independently of objects.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory

variable {C : Type u} [Category.{v} C]

omit [Category.{v} C] in
/-- The exact original word-to-flat block equality retains the actual middle block slot. -/
theorem flatMembers_word_block_index
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (p : (blocksOfFamily (tripleFamilyWord X).members).position) :
    Fin.cast (flatMembers_original_length X)
        (blockPositionsEquiv (tripleFamilyWord X).members p).1 =
      (groupsOfFiniteFamilies X).flat.inputBlockIndex
        (cast (congrArg Blocks.position (flatMembers_original_blocks X)) p) := by
  rw [Blocks.inputBlockIndex_transport (flatMembers_original_blocks X) p]
  apply Fin.ext
  exact (congrArg Fin.val (blockPositions_inputBlockIndex (tripleFamilyWord X).members p)).symm

/-- Every original word input middle label is its original physical flat group middle label. -/
theorem flatMembers_word_global_middle
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (p : (blocksOfFamily (tripleFamilyWord X).members).position) :
    flatMembersGlobalLabelEquiv X (blockPositionsEquiv (tripleFamilyWord X).members p).1 =
      originalOuterPositionsEquiv (C := FiniteFamily C) X
        (groupsMiddleOriginalPositions (X.obj ∘ enumeration X)
          ((groupsOfFiniteFamilies X).flatMiddleEquiv
            ((groupsOfFiniteFamilies X).flat.inputBlockIndex
              (cast (congrArg Blocks.position (flatMembers_original_blocks X)) p)))) := by
  have hl := flatMembersLabel_group_position (X.obj ∘ enumeration X)
    (blockPositionsEquiv (tripleFamilyWord X).members p).1
  have hg := congrArg (originalOuterPositionsEquiv (C := FiniteFamily C) X) hl
  have hi := flatMembers_word_block_index X p
  exact hg.trans (congrArg
    (fun i => originalOuterPositionsEquiv (C := FiniteFamily C) X
      (groupsMiddleOriginalPositions (X.obj ∘ enumeration X)
        ((groupsOfFiniteFamilies X).flatMiddleEquiv i))) hi)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OriginalWordPhysicalLabels

/- Source proof segment: TriplePhysicalInput -/
section source_TriplePhysicalInput
/-!
# Complete original left-triple labels of physical row inputs

The actual left-associated triple bijection is the original outer
enumeration of the full physical row position, with its complete
original inner label retained.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The original outer enumeration and sigma regroup of a complete physical row position. -/
noncomputable def physicalLeftTripleLabel
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (p : OrderedRowPositions (X.obj ∘ enumeration X)) :
    ((FiniteFamily.flattenFlatten (C := C)).obj X).index :=
  ⟨⟨enumeration X p.1, p.2.1⟩, p.2.2⟩

/-- The full original left-triple position is its actual physical row-position enumeration. -/
theorem physicalLeftTriple_input
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (i : Fin (groupsOfFiniteFamilies X).flat.totalArity) :
    physicalLeftTripleLabel X
        (groupsPhysicalInputEquiv (X.obj ∘ enumeration X)
          ((groupsOfFiniteFamilies X).flat.positionEquiv i)) = leftTripleInputEquiv X i :=
  congrArg (physicalLeftTripleLabel X) (groupsPhysicalInput_indices (X.obj ∘ enumeration X) i)

/-- The exact original word-to-flat input count cast retains the complete
left-triple input position. -/
theorem flatMembers_leftTriple_physical
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (i : Fin (blocksOfFamily (tripleFamilyWord X).members).totalArity) :
    leftTripleInputEquiv X
        (Fin.cast (congrArg Blocks.totalArity (flatMembers_original_blocks X)) i) =
      physicalLeftTripleLabel X
        (groupsPhysicalInputEquiv (X.obj ∘ enumeration X)
          (cast (congrArg Blocks.position (flatMembers_original_blocks X))
            ((blocksOfFamily (tripleFamilyWord X).members).positionEquiv i))) := by
  have hs := Blocks.positionEquiv_transport (flatMembers_original_blocks X) i
  have hp := congrArg
    (fun p => physicalLeftTripleLabel X (groupsPhysicalInputEquiv (X.obj ∘ enumeration X) p)) hs
  exact (physicalLeftTriple_input X _).symm.trans hp

/-- The original nested source middle-family inputs retain both complete original labels. -/
theorem flatMembers_source_nested_position
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (i : Fin (blocksOfFiniteFamily (flattenedMiddleFamily X)).totalArity) :
    nestedPositionsEquiv (flattenedMiddleFamily X) i =
      ⟨enumeration (flattenedMiddleFamily X)
          (flattenedPositionsEquiv (orderedFamily (flattenedMiddleFamily X)) i).1,
        (flattenedPositionsEquiv (orderedFamily (flattenedMiddleFamily X)) i).2⟩ := rfl

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_TriplePhysicalInput

/- Source proof segment: OriginalMemberInputPositions -/
section source_OriginalMemberInputPositions
/-!
# Complete original middle and inner labels of the actual member input action

The actual member morphism sends its input to the original global
middle-family label and preserves its complete original inner input.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The original member reindexing has exactly its original global middle label. -/
theorem flatMembers_reindex_global_label
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (i : Fin (arity (flattenedMiddleFamily X))) :
    flatMembersGlobalLabelEquiv X (flatMembersOriginalReindex X i) =
      enumeration (flattenedMiddleFamily X) i :=
  (flatMembersGlobalLabelEquiv X).apply_symm_apply _

/-- The actual member input action retains its complete original global middle label. -/
theorem flatMembers_input_global_middle
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (i : Fin (blocksOfFiniteFamily (flattenedMiddleFamily X)).totalArity) :
    flatMembersGlobalLabelEquiv X
        (flattenedPositionsEquiv (tripleFamilyWord X).members
          (orderedInputEquiv (flatMembersOriginalHom X) i)).1 =
      (nestedPositionsEquiv (flattenedMiddleFamily X) i).1 := by
  let p := flattenedPositionsEquiv (orderedFamily (flattenedMiddleFamily X)) i
  have ho := orderedInput_positions (flatMembersOriginalHom X) i
  have hf : (flattenedPositionsEquiv (tripleFamilyWord X).members
      (orderedInputEquiv (flatMembersOriginalHom X) i)).1 = flatMembersOriginalReindex X p.1 :=
    (congrArg Sigma.fst ho).trans
      (reindexPosition_first (flatMembersOriginalReindex X)
        (orderedFamily (flattenedMiddleFamily X)) (tripleFamilyWord X).members
        (flatMembers_original_family X) p)
  exact (congrArg (flatMembersGlobalLabelEquiv X) hf).trans (flatMembers_reindex_global_label X p.1)

/-- The actual member input action preserves its complete original inner input. -/
theorem flatMembers_input_inner_heq
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (i : Fin (blocksOfFiniteFamily (flattenedMiddleFamily X)).totalArity) :
    HEq (flattenedPositionsEquiv (tripleFamilyWord X).members
        (orderedInputEquiv (flatMembersOriginalHom X) i)).2
      (nestedPositionsEquiv (flattenedMiddleFamily X) i).2 := by
  have ho := orderedInput_positions (flatMembersOriginalHom X) i
  exact (originalInputInner_heq ho).trans
    (reindexPosition_second_heq (flatMembersOriginalReindex X)
      (orderedFamily (flattenedMiddleFamily X)) (tripleFamilyWord X).members
      (flatMembers_original_family X)
      (flattenedPositionsEquiv (orderedFamily (flattenedMiddleFamily X)) i))

/-- At the same original middle member, the actual physical group input retains
the complete original word inner input. -/
theorem flatMembers_physical_word_inner
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (p : (blocksOfFamily (tripleFamilyWord X).members).position)
    (h : groupsPhysicalMember (X.obj ∘ enumeration X)
        (cast (congrArg Blocks.position (flatMembers_original_blocks X)) p) =
      (tripleFamilyWord X).members (blockPositionsEquiv (tripleFamilyWord X).members p).1) :
    HEq (groupsPhysicalInputEquiv (X.obj ∘ enumeration X)
        (cast (congrArg Blocks.position (flatMembers_original_blocks X)) p)).2.2
      (blockPositionsEquiv (tripleFamilyWord X).members p).2 := by
  have hs := groupsPhysicalInput_slot (X.obj ∘ enumeration X)
    (cast (congrArg Blocks.position (flatMembers_original_blocks X)) p)
  have he := familyEnumeration_slot_heq
    (groupsPhysicalMember (X.obj ∘ enumeration X)
      (cast (congrArg Blocks.position (flatMembers_original_blocks X)) p))
    ((tripleFamilyWord X).members (blockPositionsEquiv (tripleFamilyWord X).members p).1) h
    (groupsPhysicalInput_arity (X.obj ∘ enumeration X)
      (cast (congrArg Blocks.position (flatMembers_original_blocks X)) p)).symm
    (blockPositions_inputArity (tripleFamilyWord X).members p).symm
    ((groupsOfFiniteFamilies X).flat.inputSlot
      (cast (congrArg Blocks.position (flatMembers_original_blocks X)) p))
    ((blocksOfFamily (tripleFamilyWord X).members).inputSlot p)
    (Blocks.inputSlot_transport_heq (flatMembers_original_blocks X) p)
  exact hs.trans
    (he.trans (heq_of_eq (blockPositions_inputSlot (tripleFamilyWord X).members p)).symm)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OriginalMemberInputPositions

/- Source proof segment: GroupInputMiddleLabels -/
section source_GroupInputMiddleLabels
/-!
# Original middle labels of complete physical row inputs

The actual input block coordinate and the actual complete row input
identify the same original outer and middle labels. The proof keeps
all original index maps independent of object equality.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory

variable {C : Type u}

/-- The original outer and middle labels in a complete original row input. -/
def orderedRowMiddleLabel {n : ℕ} (R : Fin n → FiniteFamily (FiniteFamily C))
    (p : OrderedRowPositions R) : OriginalPositions R := ⟨p.1, p.2.1⟩

/-- The actual input block index of an original row has its original middle family label. -/
theorem rowBlock_middle_label (Y : FiniteFamily (FiniteFamily C))
    (p : (blocksOfFiniteFamily Y).position) :
    (rowBlockOriginalPositions Y p).1 =
      rowMiddleEquiv Y ((blocksOfFiniteFamily Y).inputBlockIndex p) := by
  exact (congrArg (enumeration Y) (blockPositions_inputBlockIndex (orderedFamily Y) p)).symm

variable [Category.{v} C]

set_option backward.isDefEq.respectTransparency false in
/-- The actual input block coordinate retains the original physical outer and middle family
labels. -/
theorem groupsPhysicalInput_middle :
    ∀ {n : ℕ} (R : Fin n → FiniteFamily (FiniteFamily C))
      (p : (groupsOfFamilies R).flat.position),
      groupsMiddleOriginalPositions R
          ((groupsOfFamilies R).flatMiddleEquiv ((groupsOfFamilies R).flat.inputBlockIndex p)) =
        orderedRowMiddleLabel R (groupsPhysicalInputEquiv R p)
  | 0, _, p => Empty.elim p
  | n + 1, R, p => by
      let B := (groupsOfFamilies (Fin.init R)).flat
      let D := blocksOfFiniteFamily (R (Fin.last n))
      let f : (Fin B.length ⊕ Fin D.length) → OriginalPositions R := fun z =>
        positionsSnocEquiv R
          ((Equiv.sumCongr (groupsMiddleOriginalPositions (Fin.init R))
            (rowMiddleEquiv (R (Fin.last n))))
            ((Equiv.sumCongr (groupsOfFamilies (Fin.init R)).flatMiddleEquiv
              (Equiv.refl (Fin D.length))) z))
      let g : (B.position ⊕ D.position) → OrderedRowPositions R := fun z =>
        rowPositionsSnocEquiv R
          ((Equiv.sumCongr (groupsPhysicalInputEquiv (Fin.init R))
            (rowBlockOriginalPositions (R (Fin.last n)))) z)
      have hc := congrArg f (Blocks.concat_inputBlockIndex B D p)
      cases h : Blocks.concatPositionEquiv B D p with
      | inl q =>
          have hp := congrArg (fun z => orderedRowMiddleLabel R (g z)) h
          have hi := congrArg (fun z => positionsSnocEquiv R (Sum.inl z))
            (groupsPhysicalInput_middle (Fin.init R) q)
          rw [h] at hc
          exact hc.trans (hi.trans hp.symm)
      | inr q =>
          have hp := congrArg (fun z => orderedRowMiddleLabel R (g z)) h
          have hi := congrArg (fun z => positionsSnocEquiv R (Sum.inr z))
            (rowBlock_middle_label (R (Fin.last n)) q).symm
          rw [h] at hc
          exact hc.trans (hi.trans hp.symm)

/-- The original complete ordered row input and its actual input block coordinate retain
identical labels. -/
theorem groupsOriginalInput_middle {n : ℕ} (R : Fin n → FiniteFamily (FiniteFamily C))
    (p : (groupsOfFamilies R).flat.position) :
    groupsMiddleOriginalPositions R
        ((groupsOfFamilies R).flatMiddleEquiv ((groupsOfFamilies R).flat.inputBlockIndex p)) =
      orderedRowMiddleLabel R (groupsOriginalPositions R
        ((groupsOfFamilies R).flatInputEquiv ((groupsOfFamilies R).flat.positionEquiv.symm p))) :=
  (groupsPhysicalInput_middle R p).trans
    (congrArg (orderedRowMiddleLabel R) (groupsPhysicalInput_actual R p))

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_GroupInputMiddleLabels

/- Source proof segment: OriginalMemberInputAlignment -/
section source_OriginalMemberInputAlignment
/-!
# Full actual original member input equivalence and tensor map alignment

Every original input retains both original middle labels and its
complete original inner index. The actual member morphism therefore
has the exact desired triple-position input bijection and tensor map.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C]

/-- The complete actual original word middle label is its physical left-triple middle label. -/
theorem flatMembers_physical_middle
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (p : (blocksOfFamily (tripleFamilyWord X).members).position) :
    flatMembersGlobalLabelEquiv X (blockPositionsEquiv (tripleFamilyWord X).members p).1 =
      (physicalLeftTripleLabel X (groupsPhysicalInputEquiv (X.obj ∘ enumeration X)
        (cast (congrArg Blocks.position (flatMembers_original_blocks X)) p))).1 :=
  (flatMembers_word_global_middle X p).trans
    (congrArg (originalOuterPositionsEquiv (C := FiniteFamily C) X)
      (groupsPhysicalInput_middle (X.obj ∘ enumeration X)
        (cast (congrArg Blocks.position (flatMembers_original_blocks X)) p)))

/-- The complete original physical input belongs to its actual original
word finite-family member. -/
theorem flatMembers_physical_member
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (p : (blocksOfFamily (tripleFamilyWord X).members).position) :
    groupsPhysicalMember (X.obj ∘ enumeration X)
        (cast (congrArg Blocks.position (flatMembers_original_blocks X)) p) =
      (tripleFamilyWord X).members (blockPositionsEquiv (tripleFamilyWord X).members p).1 :=
  (congrArg (flattenedMiddleFamily X).obj (flatMembers_physical_middle X p).symm).trans
    (flatMembers_global_member X (blockPositionsEquiv (tripleFamilyWord X).members p).1).symm

/-- The original target word input retains its complete left-triple middle label. -/
theorem flatMembers_word_left_middle
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (i : Fin (blocksOfFamily (tripleFamilyWord X).members).totalArity) :
    flatMembersGlobalLabelEquiv X (flattenedPositionsEquiv (tripleFamilyWord X).members i).1 =
      (leftTripleInputEquiv X
        (Fin.cast (congrArg Blocks.totalArity (flatMembers_original_blocks X)) i)).1 :=
  (flatMembers_physical_middle X
    ((blocksOfFamily (tripleFamilyWord X).members).positionEquiv i)).trans
    (congrArg Sigma.fst (flatMembers_leftTriple_physical X i)).symm

/-- The original target word input retains its complete left-triple inner index. -/
theorem flatMembers_word_left_inner_heq
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (i : Fin (blocksOfFamily (tripleFamilyWord X).members).totalArity) :
    HEq (leftTripleInputEquiv X
        (Fin.cast (congrArg Blocks.totalArity (flatMembers_original_blocks X)) i)).2
      (flattenedPositionsEquiv (tripleFamilyWord X).members i).2 :=
  ((Sigma.ext_iff.mp (flatMembers_leftTriple_physical X i)).2).trans
    (flatMembers_physical_word_inner X
      ((blocksOfFamily (tripleFamilyWord X).members).positionEquiv i)
      (flatMembers_physical_member X _))

/-- The complete actual member input action retains exactly the original
nested middle-family position. -/
theorem flatMembers_actual_left_position
    (X : FiniteFamily (FiniteFamily (FiniteFamily C)))
    (i : Fin (blocksOfFiniteFamily (flattenedMiddleFamily X)).totalArity) :
    leftTripleInputEquiv X (flatMembersActualInputEquiv X i) =
      nestedPositionsEquiv (flattenedMiddleFamily X) i := by
  apply Sigma.ext
  · exact (flatMembers_word_left_middle X
      (orderedInputEquiv (flatMembersOriginalHom X) i)).symm.trans
      (flatMembers_input_global_middle X i)
  · exact (flatMembers_word_left_inner_heq X (orderedInputEquiv (flatMembersOriginalHom X) i)).trans
      (flatMembers_input_inner_heq X i)

/-- The actual original member input equivalence is the desired complete
triple-position bijection. -/
theorem flatMembersActualInputEquiv_desired
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    flatMembersActualInputEquiv X = flatMembersDesiredInputEquiv X := by
  apply Equiv.ext
  intro i
  apply (leftTripleInputEquiv X).injective
  exact (flatMembers_actual_left_position X i).trans
    ((leftTripleInputEquiv X).apply_symm_apply
      (nestedPositionsEquiv (flattenedMiddleFamily X) i)).symm

/-- The exact original ordered member input bijection with its actual target count transport. -/
theorem flatMembersOriginal_input_equiv
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    (orderedInputEquiv (flatMembersOriginalHom X)).trans
        (finCongr (congrArg Blocks.totalArity (flatMembers_original_blocks X))) =
      (nestedPositionsEquiv (flattenedMiddleFamily X)).trans (leftTripleInputEquiv X).symm :=
  flatMembersActualInputEquiv_desired X

variable [MonoidalCategory C] [SymmetricCategory C]

/-- Equality of complete actual input bijections retains their original
equality tensor components. -/
theorem equalityInputMap_congr {m n : ℕ} (A : Fin m → C) (B : Fin n → C)
    (e e' : Fin m ≃ Fin n) (he : e = e')
    (h : ∀ i, A i = B (e i)) (h' : ∀ i, A i = B (e' i)) :
    mapEquiv e (fun i => eqToHom (h i)) = mapEquiv e' (fun i => eqToHom (h' i)) := by
  cases he
  rfl

/-- The actual original member input map is the complete desired triple-position map
with every original source equality component. -/
theorem flatMembersOriginalInputMap_desired
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    flatMembersOriginalInputMap X = flatMembersDesiredInputMap X := by
  rw [flatMembersOriginalInputMap_actual_data]
  exact equalityInputMap_congr
    (blocksOfFiniteFamily (flattenedMiddleFamily X)).inputs (groupsOfFiniteFamilies X).flat.inputs
    (flatMembersActualInputEquiv X) (flatMembersDesiredInputEquiv X)
    (flatMembersActualInputEquiv_desired X)
    (flatMembersActualInput_objects X) (flatMembersDesiredInput_objects X)

/-- The exact actual original member input tensor map and its complete
original equality components. -/
theorem flatMembersOriginal_input_map
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    flatMembersOriginalInputMap X =
      mapEquiv ((nestedPositionsEquiv (flattenedMiddleFamily X)).trans
        (leftTripleInputEquiv X).symm)
        (fun i => eqToHom (flatMembersDesiredInput_objects X i)) :=
  flatMembersOriginalInputMap_desired X

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OriginalMemberInputAlignment

/- Source proof segment: AssociativityJoinFactory -/
section source_AssociativityJoinFactory
/-!
# Generic join of the actual triple-family map reductions

The three reduction equations are composed at the morphism level.
The actual source proof supplies each reduction separately; the
factory does not supply or assume a finite tensor structure.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Three original route reductions and their middle-word equality give
the original component map. -/
theorem associativity_map_join {A B D E F G H I : C}
    (l : A ⟶ I) (s : A ⟶ B) (m : B ⟶ D) (u : D ⟶ I)
    (a : A ⟶ E) (b : B ⟶ E) (f : E ⟶ F) (g : F ⟶ G) (h : G ⟶ H) (k : H ⟶ I)
    (w : D ⟶ F) (v : D ⟶ G)
    (hl : l = a ≫ f ≫ g ≫ h ≫ k)
    (hm : m ≫ w = b ≫ f) (hu : u = v ≫ h ≫ k)
    (hv : w ≫ g = v) (hs : s ≫ b = a) : l = s ≫ m ≫ u := by
  rw [hl, hu, ← hv]
  simp only [Category.assoc]
  rw [← Category.assoc m w, hm]
  simp only [Category.assoc]
  rw [← Category.assoc s b, hs]

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_AssociativityJoinFactory

/- Source proof segment: AssociativityComponent -/
section source_AssociativityComponent
/-!
# Original finite tensor associativity component map

The actual triple-family sigma reassociation and both constructed
flattening routes are identified with the same original ordered
concatenated row fold. All original finite input maps and carriers
are retained, including empty outer, middle and inner families.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

set_option backward.isDefEq.respectTransparency false in
theorem finiteFlatten_middle_reduction
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    (finiteFlattenIso (flattenedMiddleFamily X)).hom ≫ (middleCarrierWordIso X).hom =
      (leftTripleWordIso X).hom ≫ (Blocks.flattenIso (groupsOfFiniteFamilies X).flat).hom := by
  rw [finiteFlattenIso, Iso.trans_hom, Category.assoc, ← middleCarrierWordIso_output]
  rw [← flatMembersFold_naturality]
  rw [flatMembersOriginalInputMap_desired, ← Category.assoc, leftTripleWordIso_middle]

set_option backward.isDefEq.respectTransparency false in
/-- Both actual original finite tensor flattening routes obey the full
original associativity map. -/
theorem finiteFlatten_associativity_component
    (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    (finiteFlattenIso ((FiniteFamily.map (FiniteFamily.flatten (C := C))).obj X)).hom ≫
        finiteMap (fixedIndexHom X.index (fun i => (finiteFlattenIso (X.obj i)).hom)) =
      finiteMap ((FiniteFamily.flattenAssocIso (C := C)).hom.app X) ≫
        (finiteFlattenIso ((FiniteFamily.flatten (C := FiniteFamily C)).obj X)).hom ≫
          (finiteFlattenIso ((FiniteFamily.map (FiniteFamily.map
            (finiteTensorFunctor (C := C)))).obj X)).hom := by
  have hMiddle := congrArg Iso.hom (middleWordIso_grouping X)
  simp only [Iso.trans_hom] at hMiddle
  exact associativity_map_join _ _ _ _ _ _ _ _ _ _ _ _
    (associativityLeft_reduction X) (finiteFlatten_middle_reduction X)
    (finiteFlatten_mappedTensorRows X) hMiddle (tripleWordIso_regrouping X)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_AssociativityComponent

/- Source proof segment: OfSymmetric -/
section source_OfSymmetric
/-!
# Coherent finite tensors from the original binary symmetric tensor

The finite tensor functor, all finite reindexing maps, singleton comparison
and flattening comparison are constructed from the original tensor product,
unit, associators, unitors and symmetry. Both unit laws and the full triple
family associativity law are proved for those actual maps.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The actual source finite tensor satisfies the complete canonical functor pentagon. -/
theorem finiteTensor_flattenAssocLaw :
    Functor.isoWhiskerLeft (FiniteFamily.map (FiniteFamily.flatten (C := C)))
        finiteFlattenNatIso ≪≫
      Functor.isoWhiskerRight (FiniteFamily.mapIso finiteFlattenNatIso) finiteTensorFunctor =
      Functor.isoWhiskerRight FiniteFamily.flattenAssocIso finiteTensorFunctor ≪≫
        Functor.isoWhiskerLeft (FiniteFamily.flatten (C := FiniteFamily C))
          finiteFlattenNatIso ≪≫
        Functor.isoWhiskerRight (FiniteFamily.flattenMapIso finiteTensorFunctor)
          finiteTensorFunctor ≪≫
        Functor.isoWhiskerLeft (FiniteFamily.map (FiniteFamily.map finiteTensorFunctor))
          finiteFlattenNatIso := by
  change finiteAssocLeftNatIso (C := C) = finiteAssocRightNatIso
  apply Iso.ext
  apply NatTrans.ext
  funext X
  exact (finiteAssocLeftNatIso_hom_app X).trans
    ((finiteFlatten_associativity_component X).trans (finiteAssocRightNatIso_hom_app X).symm)

end CategoryTheory.MonoidalCategory.OrderedTensor

namespace CategoryTheory.FiniteTensor

open CategoryTheory MonoidalCategory

/-- The coherent unbiased finite tensor constructed from the original binary symmetric
monoidal category. -/
@[instance_reducible]
noncomputable def ofSymmetric (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [SymmetricCategory C] : FiniteTensor C where
  tensor := OrderedTensor.finiteTensorFunctor
  singletonIso := OrderedTensor.finiteSingletonNatIso
  flattenIso := OrderedTensor.finiteFlattenNatIso
  singletonFlattenLaw := OrderedTensor.finiteTensor_singletonFlattenLaw
  mapSingletonFlattenLaw := OrderedTensor.finiteTensor_mapSingletonFlattenLaw
  flattenAssocLaw := OrderedTensor.finiteTensor_flattenAssocLaw

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The produced tensor functor is the actual original finite-family tensor functor. -/
theorem ofSymmetric_tensor : (ofSymmetric C).tensor = OrderedTensor.finiteTensorFunctor := rfl

/-- The produced singleton comparison is the original constructed unitor comparison. -/
theorem ofSymmetric_singletonIso :
    (ofSymmetric C).singletonIso = OrderedTensor.finiteSingletonNatIso := rfl

/-- The produced flattening comparison is the original constructed block-fold comparison. -/
theorem ofSymmetric_flattenIso :
    (ofSymmetric C).flattenIso = OrderedTensor.finiteFlattenNatIso := rfl

/-- Every produced finite tensor object uses the original ordered family and original
enumeration. -/
theorem ofSymmetric_obj (X : FiniteFamily C) :
    (ofSymmetric C).tensor.obj X = OrderedTensor.obj (X.obj ∘ OrderedTensor.enumeration X) := rfl

/-- The produced tensor maps unchanged original input indices to the original ordered
component map. -/
theorem ofSymmetric_map_fixedIndex (I : FintypeCat.{0}) {X Y : I → C}
    (f : ∀ i, X i ⟶ Y i) :
    (ofSymmetric C).tensor.map (OrderedTensor.fixedIndexHom I f) =
      OrderedTensor.fixedIndexMap I f :=
  OrderedTensor.finiteTensorFunctor_map_fixedIndex I f

/-- The actual produced tensor of the empty original finite family is the original tensor unit. -/
theorem ofSymmetric_empty :
    (ofSymmetric C).tensor.obj (FiniteFamily.empty : FiniteFamily C) = 𝟙_ C :=
  OrderedTensor.finiteObj_empty

end CategoryTheory.FiniteTensor
end
end source_OfSymmetric

/- Source proof segment: OrderedTensorSlots -/
section source_OrderedTensorSlots
/-!
# Actual one-slot functors of the original ordered tensor

The functor changes precisely one original finite tensor input. Its
last and initial-slot computations use the actual original binary
left and right tensor functors, with every component map retained.
-/

@[expose] public section

set_option autoImplicit false

universe v u us

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory Limits

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Vary one original finite tensor input, keeping every other original input fixed. -/
def slotFunctor {n : ℕ} (X : Fin n → C) (i : Fin n) : C ⥤ C :=
  Pi.replaceFunctor X i ⋙ functor C n

omit [Category.{v} C] [MonoidalCategory C] in
/-- Varying the original last input retains every original initial input object. -/
theorem slot_last_initial {n : ℕ} (X : Fin (n + 1) → C) (A : C) :
    Fin.init (Function.update X (Fin.last n) A) = Fin.init X :=
  Function.update_comp_eq_of_forall_ne X A (fun j => Fin.castSucc_ne_last j)

omit [Category.{v} C] [MonoidalCategory C] in
/-- Varying an original initial input gives exactly the original initial replacement family. -/
theorem slot_initial_family {n : ℕ} (X : Fin (n + 1) → C) (i : Fin n) (A : C) :
    Fin.init (Function.update X i.castSucc A) = Function.update (Fin.init X) i A :=
  Function.update_comp_eq_of_injective X (Fin.castSucc_injective n) i A

set_option backward.isDefEq.respectTransparency false in
/-- Varying the original final input is the original left tensor functor on the complete
fixed prefix. -/
theorem slotFunctor_last {n : ℕ} (X : Fin (n + 1) → C) :
    slotFunctor X (Fin.last n) = tensorLeft (obj (Fin.init X)) := by
  apply Functor.hext
  · intro A
    change obj (Function.update X (Fin.last n) A) = obj (Fin.init X) ⊗ A
    rw [obj_succ]
    change obj (Fin.init (Function.update X (Fin.last n) A)) ⊗
      Function.update X (Fin.last n) A (Fin.last n) = _
    rw [slot_last_initial, Function.update_self]
  · intro A B f
    change HEq (map (Pi.replaceMap X (Fin.last n) f))
      ((tensorLeft (obj (Fin.init X))).map f)
    have h := map_succ_heq (slot_last_initial X A) (slot_last_initial X B)
      (Function.update_self (Fin.last n) A X) (Function.update_self (Fin.last n) B X)
      (Pi.replaceMap X (Fin.last n) f) (fun j => 𝟙 ((Fin.init X) j)) f
      (fun j => Pi.replaceMap_other X (Fin.last n) j.castSucc (Fin.castSucc_ne_last j) f)
      (Pi.replaceMap_at X (Fin.last n) f)
    simpa only [map_id, id_tensorHom, tensorLeft, curriedTensor] using h

set_option backward.isDefEq.respectTransparency false in
/-- Varying an original initial input retains the original final factor under the original
right tensor functor. -/
theorem slotFunctor_castSucc {n : ℕ} (X : Fin (n + 1) → C) (i : Fin n) :
    slotFunctor X i.castSucc = slotFunctor (Fin.init X) i ⋙ tensorRight (X (Fin.last n)) := by
  apply Functor.hext
  · intro A
    change obj (Function.update X i.castSucc A) =
      obj (Function.update (Fin.init X) i A) ⊗ X (Fin.last n)
    rw [obj_succ]
    change obj (Fin.init (Function.update X i.castSucc A)) ⊗
      Function.update X i.castSucc A (Fin.last n) = _
    rw [slot_initial_family, Function.update_of_ne (Fin.castSucc_ne_last i).symm]
  · intro A B f
    change HEq (map (Pi.replaceMap X i.castSucc f))
      ((tensorRight (X (Fin.last n))).map (map (Pi.replaceMap (Fin.init X) i f)))
    have hPrefix : ∀ j : Fin n,
        HEq (Pi.replaceMap X i.castSucc f j.castSucc) (Pi.replaceMap (Fin.init X) i f j) := by
      intro j
      by_cases hji : j = i
      · subst j
        exact (Pi.replaceMap_at X i.castSucc f).trans (Pi.replaceMap_at (Fin.init X) i f).symm
      · exact (Pi.replaceMap_other X i.castSucc j.castSucc
          ((Fin.castSucc_injective n).ne hji) f).trans (Pi.replaceMap_other (Fin.init X) i j
            hji f).symm
    have h := map_succ_heq (slot_initial_family X i A) (slot_initial_family X i B)
      (Function.update_of_ne (Fin.castSucc_ne_last i).symm A X)
      (Function.update_of_ne (Fin.castSucc_ne_last i).symm B X)
      (Pi.replaceMap X i.castSucc f) (Pi.replaceMap (Fin.init X) i f) (𝟙 (X (Fin.last n))) hPrefix
      (Pi.replaceMap_other X i.castSucc (Fin.last n) (Fin.castSucc_ne_last i).symm f)
    simpa only [tensorHom_id, tensorRight, Functor.flip, curriedTensor] using h

variable [∀ A : C, PreservesColimitsOfSize.{us, us} (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfSize.{us, us} (tensorRight A)]

/-- Actual ordered one-slot tensoring preserves the required source-sized colimits by the
original separate binary
  tensor preservation. -/
theorem slotFunctor_preserves : ∀ {n : ℕ} (X : Fin n → C) (i : Fin n),
    PreservesColimitsOfSize.{us, us} (slotFunctor X i) := by
  intro n
  induction n with
  | zero => intro X i; exact i.elim0
  | succ n ih =>
      intro X i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [slotFunctor_last]
        infer_instance
      · rw [slotFunctor_castSucc]
        have := ih (Fin.init X) j
        infer_instance

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedTensorSlots

/- Source proof segment: FiniteTensorSlotPreservation -/
section source_FiniteTensorSlotPreservation
/-!
# Source colimit preservation of every actual finite tensor slot

The original fixed finite index and original one-slot replacement
functor are reindexed through the original finite enumeration. The
actual source-produced tensor functor preserves the required small
colimits in each slot from separate original binary tensor preservation.
-/

@[expose] public section

set_option autoImplicit false

universe vi ui v u us

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory Limits

variable {C : Type u} [Category.{v} C]

private theorem piMap_heq {I : Type ui} {A B A' B' : I → C}
    (hA : A = A') (hB : B = B') (f : A ⟶ B) (g : A' ⟶ B')
    (hfg : ∀ i, HEq (f i) (g i)) : HEq f g := by
  cases hA
  cases hB
  exact heq_of_eq (funext (fun i => eq_of_heq (hfg i)))

private theorem piComponent_heq {I : Type ui} {A B : I → C} (f : A ⟶ B)
    {i j : I} (h : i = j) : HEq (f i) (f j) := by
  cases h
  rfl

/-- Original one-slot replacement commutes with an actual input-type bijection. -/
theorem replaceFunctor_comap {I : Type ui} {J : Type vi} [DecidableEq I] [DecidableEq J]
    (e : J ≃ I) (A : I → C) (i : I) :
    Pi.replaceFunctor A i ⋙ Pi.comap (fun _ : I => C) e =
      Pi.replaceFunctor (A ∘ e) (e.symm i) := by
  have hObj (X : C) : Function.update A i X ∘ e = Function.update (A ∘ e) (e.symm i) X := by
    have h := Function.update_comp_eq_of_injective A e.injective (e.symm i) X
    rw [e.apply_symm_apply] at h
    exact h
  apply Functor.hext
  · intro X
    exact hObj X
  · intro X Y f
    change HEq (fun j => Pi.replaceMap A i f (e j)) (Pi.replaceMap (A ∘ e) (e.symm i) f)
    apply piMap_heq (hObj X) (hObj Y)
    intro j
    by_cases hj : j = e.symm i
    · subst j
      exact (piComponent_heq (Pi.replaceMap A i f) (e.apply_symm_apply i)).trans
        ((Pi.replaceMap_at A i f).trans (Pi.replaceMap_at (A ∘ e) (e.symm i) f).symm)
    · have hji : e j ≠ i := fun he => hj ((e.symm_apply_apply j).symm.trans (congrArg e.symm he))
      exact (Pi.replaceMap_other A i (e j) hji f).trans
        (Pi.replaceMap_other (A ∘ e) (e.symm i) j hj f).symm

variable [MonoidalCategory C] [SymmetricCategory C]

attribute [local instance] FintypeCat.fintype

/-- The actual source-produced tensor functor on one original fixed finite input type. -/
noncomputable def producedFixedTensorFunctor (I : FintypeCat.{0}) : (I → C) ⥤ C :=
  FiniteFamily.fixedIndexFunctor I ⋙ finiteTensorFunctor

/-- The actual produced fixed-index tensor functor is its original ordered finite tensor
after the original input
  enumeration. -/
theorem producedFixedTensorFunctor_ordered (I : FintypeCat.{0}) :
    producedFixedTensorFunctor (C := C) I =
      Pi.comap (fun _ : I => C) (Fintype.equivFin I).symm ⋙ functor C (Fintype.card I) := by
  apply Functor.hext
  · intro A
    rfl
  · intro A B f
    exact heq_of_eq (finiteTensorFunctor_map_fixedIndex I f)

/-- Every original fixed-index varying slot is precisely its original ordered slot through
the original enumeration. -/
theorem producedFixedTensorFunctor_slot (I : FintypeCat.{0}) [DecidableEq I] (A : I → C) (i : I) :
    Pi.replaceFunctor A i ⋙ producedFixedTensorFunctor I =
      slotFunctor (A ∘ (Fintype.equivFin I).symm) (Fintype.equivFin I i) := by
  rw [producedFixedTensorFunctor_ordered]
  change (Pi.replaceFunctor A i ⋙ Pi.comap (fun _ : I => C) (Fintype.equivFin I).symm) ⋙
    functor C (Fintype.card I) = _
  rw [replaceFunctor_comap]
  rfl

variable [∀ A : C, PreservesColimitsOfSize.{us, us} (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfSize.{us, us} (tensorRight A)]

/-- The actual source-produced finite tensor preserves source-sized small colimits in every
original finite slot. -/
theorem producedFixedTensorFunctor_preserves_slot (I : FintypeCat.{0}) [DecidableEq I]
    (A : I → C) (i : I) :
    PreservesColimitsOfSize.{us, us} (Pi.replaceFunctor A i ⋙ producedFixedTensorFunctor I) := by
  rw [producedFixedTensorFunctor_slot]
  exact slotFunctor_preserves _ _

/-- The actual produced tensor has the source separate slot-colimit preservation condition
on every original fixed
  finite index. -/
theorem producedFixedTensorFunctor_preserves_eachSlot (I : FintypeCat.{0}) [DecidableEq I] :
    Functor.PreservesColimitsInEachSlot.{0, u, v, u, v, us} (producedFixedTensorFunctor (C
      := C) I) where
  preserves := producedFixedTensorFunctor_preserves_slot I

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FiniteTensorSlotPreservation

/- Source proof segment: ClosedTensorSlotPreservation -/
section source_ClosedTensorSlotPreservation
/-!
# Actual finite tensor slot preservation from source closedness

Source closedness makes the original left tensor functors left
adjoints. Original symmetry gives the original right tensor left
adjoints. Their actual small-colimit preservation supplies every
original finite tensor slot of the source-produced tensor functor.
-/

@[expose] public section

set_option autoImplicit false

universe v u us

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory Limits

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]

omit [SymmetricCategory C] in
/-- Each original left tensor functor preserves source-sized small colimits by the original
closed adjunction. -/
theorem source_tensorLeft_preserves (A : C) : PreservesColimitsOfSize.{us, us} (tensorLeft A) := by
  infer_instance

/-- Each original right tensor functor preserves source-sized small colimits by the original
closed/symmetric
  adjunction. -/
theorem source_tensorRight_preserves (A : C) : PreservesColimitsOfSize.{us,
  us} (tensorRight A) := by
  infer_instance

/-- The actual source-produced finite tensor preserves every original finite input slot from
source closed symmetric
  tensoring alone. -/
theorem producedFixedTensorFunctor_closedEachSlot (I : FintypeCat.{0}) [DecidableEq I] :
    Functor.PreservesColimitsInEachSlot.{0, u, v, u, v, us} (producedFixedTensorFunctor (C
      := C) I) := by
  have hL : ∀ A : C, PreservesColimitsOfSize.{us, us} (tensorLeft A) := source_tensorLeft_preserves
  have hR : ∀ A : C, PreservesColimitsOfSize.{us, us} (tensorRight A) :=
    source_tensorRight_preserves
  exact producedFixedTensorFunctor_preserves_eachSlot I

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_ClosedTensorSlotPreservation

/- Source proof segment: OfSymmetricSlotPreservation -/
section source_OfSymmetricSlotPreservation
/-!
# Source small colimit preservation for the actual coherent finite tensor

The coherent finite tensor is selected from the original binary symmetric
monoidal category. Its actual original one-slot replacement functors preserve
small colimits by source closedness and the original finite tensor recursion.
-/

@[expose] public section

set_option autoImplicit false

universe v u us

namespace CategoryTheory.FiniteTensor

open CategoryTheory MonoidalCategory Limits

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C]

/-- Source closed symmetric tensoring supplies every original finite input slot of the
actual coherent finite tensor. -/
theorem ofSymmetric_preservesColimitsInEachSlot :
    letI := ofSymmetric C
    FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C := by
  let _ := ofSymmetric C
  refine ⟨fun I => ?_⟩
  let _ : DecidableEq I := Classical.decEq I
  change Functor.PreservesColimitsInEachSlot.{0, u, v, u, v, us}
    (OrderedTensor.producedFixedTensorFunctor (C := C) I)
  exact OrderedTensor.producedFixedTensorFunctor_closedEachSlot I

end CategoryTheory.FiniteTensor
end
end source_OfSymmetricSlotPreservation

/- Source proof segment: OrderedConstantTensor -/
section source_OrderedConstantTensor
/-!
# Constant ordered families recover the original binary tensor powers

The heterogeneous ordered tensor is compared with the existing left-associated
tensor powers by their actual recursive object and morphism definitions. The
empty family gives the original tensor unit.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A constant ordered family is the existing binary tensor power, including degree zero. -/
theorem obj_constant (X : C) (n : ℕ) :
    obj (fun _ : Fin n => X) = TensorPower.tensorPowObj X n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change obj (fun _ : Fin n => X) ⊗ X = TensorPower.tensorPowObj X n ⊗ X
    exact congrArg (fun Z : C => Z ⊗ X) ih

/-- The actual constant component map is the existing binary tensor power map. -/
theorem map_constant_heq {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    HEq (map (fun _ : Fin n => f)) (TensorPower.tensorPowMap f n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change HEq (map (fun _ : Fin n => f) ⊗ₘ f)
      (TensorPower.tensorPowMap f n ⊗ₘ f)
    exact tensorMapBoundary_heq (obj_constant X n) (obj_constant Y n) rfl rfl ih HEq.rfl

/-- Equal original finite counts transport the original binary tensor power map. -/
theorem tensorPowMap_count_heq {m n : ℕ} (h : m = n) {X Y : C} (f : X ⟶ Y) :
    HEq (TensorPower.tensorPowMap f m) (TensorPower.tensorPowMap f n) := by
  cases h
  rfl

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedConstantTensor

/- Source proof segment: FiniteConstantTensor -/
section source_FiniteConstantTensor
/-!
# The produced finite tensor recovers the original homogeneous powers

The comparison uses the actual original finite index `Fin n` and the actual
identity-index morphism with constant components. It is independent of the
chosen finite enumeration and is natural in the original object.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- The original constant family indexed by all `n` finite inputs. -/
def constantFinFamily (n : ℕ) (X : C) : FiniteFamily C :=
  ⟨FintypeCat.of (Fin n), fun _ => X⟩

omit [MonoidalCategory C] [SymmetricCategory C] in
/-- Constant finite families with the actual identity-index constant component map. -/
def constantFinFamilyFunctor (n : ℕ) : C ⥤ FiniteFamily C where
  obj := constantFinFamily n
  map f := fixedIndexHom (FintypeCat.of (Fin n)) (fun _ => f)
  map_id _ := rfl
  map_comp _ _ := rfl

omit [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] in
/-- The actual chosen finite index cardinal of a constant `Fin n` family is `n`. -/
theorem constantFinFamily_arity (n : ℕ) (X : C) : arity (constantFinFamily n X) = n := by
  unfold arity constantFinFamily
  exact (@Fintype.card_congr (Fin n) (Fin n)
    (@FintypeCat.fintype (FintypeCat.of (Fin n)))
    (inferInstanceAs (Fintype (Fin n))) (Equiv.refl _)).trans (Fintype.card_fin n)

/-- The actual produced tensor on a constant original `Fin n` family is the stock tensor power. -/
theorem finiteTensorFunctor_constant_obj (n : ℕ) (X : C) :
    finiteTensorFunctor.obj (constantFinFamily n X) = TensorPower.tensorPowObj X n := by
  change obj (fun _ : Fin (arity (constantFinFamily n X)) => X) = _
  exact (obj_constant X _).trans
    (congrArg (TensorPower.tensorPowObj X) (constantFinFamily_arity n X))

/-- The actual produced map on constant original inputs is the stock tensor power map. -/
theorem finiteTensorFunctor_constant_map_heq (n : ℕ) {X Y : C} (f : X ⟶ Y) :
    HEq (finiteTensorFunctor.map ((constantFinFamilyFunctor n).map f))
      (TensorPower.tensorPowMap f n) := by
  change HEq (finiteTensorFunctor.map
    (fixedIndexHom (FintypeCat.of (Fin n)) (fun _ => f))) _
  rw [finiteTensorFunctor_map_fixedIndex]
  change HEq (map (fun _ : Fin (arity (constantFinFamily n X)) => f)) _
  exact (map_constant_heq f _).trans
    (tensorPowMap_count_heq (constantFinFamily_arity n X) f)

/-- The actual source homogeneous tensor functor obtained from the produced finite tensor. -/
noncomputable def finiteTensorPowerFunctor (n : ℕ) : C ⥤ C :=
  constantFinFamilyFunctor n ⋙ finiteTensorFunctor

/-- The actual original constant-family tensor functor agrees with the existing binary power
functor. -/
theorem finiteTensorPowerFunctor_eq (n : ℕ) :
    finiteTensorPowerFunctor (C := C) n = TensorPower.tensorPowFunctor n := by
  apply Functor.hext
  · intro X
    exact finiteTensorFunctor_constant_obj n X
  · intro X Y f
    exact finiteTensorFunctor_constant_map_heq n f

/-- Naturality of the exact carrier comparison with the existing binary tensor powers. -/
theorem finiteTensorPower_comparison_naturality (n : ℕ) {X Y : C} (f : X ⟶ Y) :
    (finiteTensorPowerFunctor n).map f ≫ eqToHom (finiteTensorFunctor_constant_obj n Y) =
      eqToHom (finiteTensorFunctor_constant_obj n X) ≫ TensorPower.tensorPowMap f n := by
  have h := finiteTensorFunctor_constant_map_heq n f
  apply eq_of_heq
  exact (comp_eqToHom_heq _ _).trans
    (h.trans (eqToHom_comp_heq _ _).symm)

/-- The produced finite tensor on original constant `Fin n` families is naturally the stock
power. -/
noncomputable def finiteTensorPowerNatIso (n : ℕ) :
    finiteTensorPowerFunctor (C := C) n ≅ TensorPower.tensorPowFunctor n :=
  NatIso.ofComponents (fun X => eqToIso (finiteTensorFunctor_constant_obj n X))
    (fun f => finiteTensorPower_comparison_naturality n f)

/-- In degree zero the actual produced constant-family tensor is the original tensor unit. -/
theorem finiteTensorFunctor_constant_zero (X : C) :
    finiteTensorFunctor.obj (constantFinFamily 0 X) = 𝟙_ C :=
  finiteTensorFunctor_constant_obj 0 X

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_FiniteConstantTensor
