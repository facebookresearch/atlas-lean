/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Sequence.Index
public import MathlibExt.CategoryTheory.Monoidal.TensorPowers

/-!
# Ordered words in a lax monoidal diagram

A degree-one arrow extends to every finite ordered word. These words
preserve the unit and every indexed multiplication.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.MonoidalCategory
open scoped MonoidalCategory

namespace CategoryTheory.Sequence.OrderedTensorWords
universe uV vV
local notation "N" => CategoryTheory.Sequence.Index
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  (F : N ⥤ V) [F.LaxMonoidal] {K : V} (g : K ⟶ F.obj (CategoryTheory.Sequence.index 1))

/-- Every original ordered word is built from the original unit and full indexed multiplication. -/
def word (n : ℕ) : TensorPower.tensorPowObj K n ⟶ F.obj (CategoryTheory.Sequence.index n) :=
  Nat.rec (motive := fun n => TensorPower.tensorPowObj K n ⟶ F.obj (CategoryTheory.Sequence.index n))
    (Functor.LaxMonoidal.ε F)
    (fun n previous => (previous ⊗ₘ g) ≫
      Functor.LaxMonoidal.μ F (CategoryTheory.Sequence.index n) (CategoryTheory.Sequence.index 1)) n

/-- The original empty word is exactly the full original unit. -/
theorem word_zero : word F g 0 = Functor.LaxMonoidal.ε F := rfl

/-- Every original nonempty word uses its full preceding word and the original generator. -/
theorem word_successor (n : ℕ) :
    word F g (n + 1) = (word F g n ⊗ₘ g) ≫
      Functor.LaxMonoidal.μ F (CategoryTheory.Sequence.index n) (CategoryTheory.Sequence.index 1) := rfl

/-- The original first word returns the entire supplied degree-one generator. -/
theorem word_one_generator : (λ_ K).inv ≫ word F g 1 = g := by
  have hi : F.map (λ_ (CategoryTheory.Sequence.index 1)).hom =
      𝟙 (F.obj (CategoryTheory.Sequence.index 1)) :=
    (congrArg (fun q : CategoryTheory.Sequence.index 1 ⟶ CategoryTheory.Sequence.index 1 => F.map q)
      (show (λ_ (CategoryTheory.Sequence.index 1)).hom = 𝟙 (CategoryTheory.Sequence.index 1) from
        Discrete.hom_eq)).trans (F.map_id _)
  let m : F.obj (𝟙_ N) ⊗ F.obj (CategoryTheory.Sequence.index 1) ⟶
      F.obj (CategoryTheory.Sequence.index 1) :=
    Functor.LaxMonoidal.μ F (𝟙_ N) (CategoryTheory.Sequence.index 1)
  let r : F.obj (CategoryTheory.Sequence.index 1) ⟶ F.obj (CategoryTheory.Sequence.index 1) :=
    F.map (λ_ (CategoryTheory.Sequence.index 1)).hom
  have hr : r = 𝟙 (F.obj (CategoryTheory.Sequence.index 1)) := hi
  have hu := Functor.LaxMonoidal.left_unitality F (CategoryTheory.Sequence.index 1)
  change (λ_ (F.obj (CategoryTheory.Sequence.index 1))).hom =
    (Functor.LaxMonoidal.ε F ▷ F.obj (CategoryTheory.Sequence.index 1)) ≫ m ≫
      r at hu
  have hu0 : (Functor.LaxMonoidal.ε F ▷ F.obj (CategoryTheory.Sequence.index 1)) ≫ m =
      (λ_ (F.obj (CategoryTheory.Sequence.index 1))).hom := by
    simpa only [hr, Category.comp_id] using hu.symm
  change (λ_ K).inv ≫ (Functor.LaxMonoidal.ε F ⊗ₘ g) ≫ m = g
  have hs : (Functor.LaxMonoidal.ε F ⊗ₘ g) =
      (𝟙_ V ◁ g) ≫ (Functor.LaxMonoidal.ε F ▷ F.obj (CategoryTheory.Sequence.index 1)) :=
    tensorHom_def' _ _
  have hl : (λ_ K).inv ≫ (𝟙_ V ◁ g) =
      g ≫ (λ_ (F.obj (CategoryTheory.Sequence.index 1))).inv := (leftUnitor_inv_naturality g).symm
  calc
    _ = (λ_ K).inv ≫ (𝟙_ V ◁ g) ≫
        (Functor.LaxMonoidal.ε F ▷ F.obj (CategoryTheory.Sequence.index 1)) ≫
          m := by
      simpa only [Category.assoc] using congrArg (fun q => (λ_ K).inv ≫ q ≫
        m) hs
    _ = g ≫ (λ_ (F.obj (CategoryTheory.Sequence.index 1))).inv ≫
        (Functor.LaxMonoidal.ε F ▷ F.obj (CategoryTheory.Sequence.index 1)) ≫
          m := by
      simpa only [Category.assoc] using congrArg (fun q => q ≫
        (Functor.LaxMonoidal.ε F ▷ F.obj (CategoryTheory.Sequence.index 1)) ≫
          m) hl
    _ = g ≫ (λ_ (F.obj (CategoryTheory.Sequence.index 1))).inv ≫
        (λ_ (F.obj (CategoryTheory.Sequence.index 1))).hom :=
      congrArg (fun q => g ≫ (λ_ (F.obj (CategoryTheory.Sequence.index 1))).inv ≫ q) hu0
    _ = g := (congrArg (fun q => g ≫ q)
      (Iso.inv_hom_id (λ_ (F.obj (CategoryTheory.Sequence.index 1))))).trans (Category.comp_id _)
end CategoryTheory.Sequence.OrderedTensorWords

namespace CategoryTheory.Sequence.OrderedTensorWords
universe uV vV
local notation "N" => CategoryTheory.Sequence.Index
local notation "idx" => CategoryTheory.Sequence.index
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  (F : N ⥤ V) [F.LaxMonoidal] {K : V} (g : K ⟶ F.obj (idx 1))

/-- The original indexed multiplication, with the whole degree-sum target typed first. -/
def pairing (p q : ℕ) : F.obj (idx p) ⊗ F.obj (idx q) ⟶ F.obj (idx (p + q)) :=
  LaxMonoidal.μ F (idx p) (idx q)

/-- Original indexed associativity before any word or concrete coefficient is supplied. -/
private theorem pairing_associativity (p q : ℕ) :
    (pairing F p q ▷ F.obj (idx 1)) ≫ pairing F (p + q) 1 =
      (α_ (F.obj (idx p)) (F.obj (idx q)) (F.obj (idx 1))).hom ≫
        (F.obj (idx p) ◁ pairing F q 1) ≫ pairing F p (q + 1) := by
  have h := LaxMonoidal.associativity F (idx p) (idx q) (idx 1)
  change (pairing F p q ▷ F.obj (idx 1)) ≫ pairing F (p + q) 1 ≫
      F.map (α_ (idx p) (idx q) (idx 1)).hom =
    (α_ (F.obj (idx p)) (F.obj (idx q)) (F.obj (idx 1))).hom ≫
      (F.obj (idx p) ◁ pairing F q 1) ≫ pairing F p (q + 1) at h
  have hi : F.map (α_ (idx p) (idx q) (idx 1)).hom = 𝟙 (F.obj (idx (p + q + 1))) :=
    (congrArg (fun f : idx (p + q + 1) ⟶ idx (p + q + 1) => F.map f)
      (show (α_ (idx p) (idx q) (idx 1)).hom = 𝟙 (idx (p + q + 1)) from
        Discrete.hom_eq)).trans (F.map_id _)
  let r : F.obj (idx (p + q + 1)) ⟶ F.obj (idx (p + q + 1)) :=
    F.map (α_ (idx p) (idx q) (idx 1)).hom
  have hr : r = 𝟙 (F.obj (idx (p + q + 1))) := hi
  change (pairing F p q ▷ F.obj (idx 1)) ≫ pairing F (p + q) 1 ≫ r = _ at h
  simpa only [hr, Category.comp_id] using h

/-- The full original unit law on the independently typed degree-zero multiplication. -/
private theorem pairing_right_unit (p : ℕ) :
    (F.obj (idx p) ◁ LaxMonoidal.ε F) ≫ pairing F p 0 =
      (ρ_ (F.obj (idx p))).hom := by
  have h := LaxMonoidal.right_unitality F (idx p)
  change (ρ_ (F.obj (idx p))).hom =
    (F.obj (idx p) ◁ LaxMonoidal.ε F) ≫ pairing F p 0 ≫ F.map (ρ_ (idx p)).hom at h
  have hi : F.map (ρ_ (idx p)).hom = 𝟙 (F.obj (idx p)) :=
    (congrArg (fun f : idx p ⟶ idx p => F.map f)
      (show (ρ_ (idx p)).hom = 𝟙 (idx p) from Discrete.hom_eq)).trans (F.map_id _)
  let r : F.obj (idx p) ⟶ F.obj (idx p) := F.map (ρ_ (idx p)).hom
  have hr : r = 𝟙 (F.obj (idx p)) := hi
  change (ρ_ (F.obj (idx p))).hom =
    (F.obj (idx p) ◁ LaxMonoidal.ε F) ≫ pairing F p 0 ≫ r at h
  let t : F.obj (idx p) ⊗ 𝟙_ V ⟶ F.obj (idx p) ⊗ F.obj (idx 0) :=
    F.obj (idx p) ◁ LaxMonoidal.ε F
  let m : F.obj (idx p) ⊗ F.obj (idx 0) ⟶ F.obj (idx p) := pairing F p 0
  change (ρ_ (F.obj (idx p))).hom = t ≫ m ≫ r at h
  change t ≫ m = (ρ_ (F.obj (idx p))).hom
  calc
    _ = t ≫ m ≫ 𝟙 (F.obj (idx p)) := (Category.comp_id (t ≫ m)).symm.trans (Category.assoc t m _)
    _ = t ≫ m ≫ r := congrArg (fun f => t ≫ m ≫ f) hr.symm
    _ = _ := h.symm

/-- The full original word family preserves all ordered multiplications. -/
theorem word_pairing (p q : ℕ) :
    (word F g p ⊗ₘ word F g q) ≫ pairing F p q =
      (TensorPower.tensorPowObj_add K p q).inv ≫ word F g (p + q) := by
  induction q with
  | zero =>
    change (word F g p ⊗ₘ LaxMonoidal.ε F) ≫ pairing F p 0 =
      (ρ_ (TensorPower.tensorPowObj K p)).hom ≫ word F g p
    calc
      _ = (word F g p ▷ 𝟙_ V) ≫
          (F.obj (idx p) ◁ LaxMonoidal.ε F) ≫ pairing F p 0 :=
        (congrArg (fun f => f ≫ pairing F p 0)
          (tensorHom_def (word F g p) (LaxMonoidal.ε F))).trans (Category.assoc _ _ _)
      _ = (word F g p ▷ 𝟙_ V) ≫ (ρ_ (F.obj (idx p))).hom :=
        congrArg (fun f => (word F g p ▷ 𝟙_ V) ≫ f) (pairing_right_unit F p)
      _ = _ := rightUnitor_naturality (word F g p)
  | succ q ih =>
    have hAdd : (TensorPower.tensorPowObj_add K p (q + 1)).inv =
        (α_ (TensorPower.tensorPowObj K p) (TensorPower.tensorPowObj K q) K).inv ≫
          (TensorPower.tensorPowObj_add K p q).inv ▷ K := by
      change (α_ (TensorPower.tensorPowObj K p) (TensorPower.tensorPowObj K q) K).inv ≫
          ((TensorPower.tensorPowObj_add K p q).inv ⊗ₘ 𝟙 K) = _
      exact congrArg (fun f =>
        (α_ (TensorPower.tensorPowObj K p) (TensorPower.tensorPowObj K q) K).inv ≫ f)
          (tensorHom_id _ _)
    have hNaturality : (word F g p ⊗ₘ (word F g q ⊗ₘ g)) =
        (α_ (TensorPower.tensorPowObj K p) (TensorPower.tensorPowObj K q) K).inv ≫
          ((word F g p ⊗ₘ word F g q) ⊗ₘ g) ≫
            (α_ (F.obj (idx p)) (F.obj (idx q)) (F.obj (idx 1))).hom := by
      have h := congrArg (fun f =>
        (α_ (TensorPower.tensorPowObj K p) (TensorPower.tensorPowObj K q) K).inv ≫ f)
          (associator_naturality (word F g p) (word F g q) g)
      simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h.symm
    have hSplit : (word F g p ⊗ₘ ((word F g q ⊗ₘ g) ≫ pairing F q 1)) =
        (word F g p ⊗ₘ (word F g q ⊗ₘ g)) ≫
          (F.obj (idx p) ◁ pairing F q 1) := by
      have h := tensorHom_comp_tensorHom (word F g p) (word F g q ⊗ₘ g)
        (𝟙 (F.obj (idx p))) (pairing F q 1)
      simpa only [Category.comp_id, id_tensorHom] using h.symm
    have hCombine : ((word F g p ⊗ₘ word F g q) ⊗ₘ g) ≫
        (pairing F p q ▷ F.obj (idx 1)) =
      ((word F g p ⊗ₘ word F g q) ≫ pairing F p q) ⊗ₘ g := by
      have h := tensorHom_comp_tensorHom (word F g p ⊗ₘ word F g q) g
        (pairing F p q) (𝟙 (F.obj (idx 1)))
      simpa only [Category.comp_id, tensorHom_id] using h
    have hEnd : ((TensorPower.tensorPowObj_add K p q).inv ≫ word F g (p + q)) ⊗ₘ g =
        ((TensorPower.tensorPowObj_add K p q).inv ▷ K) ≫ (word F g (p + q) ⊗ₘ g) := by
      have h := tensorHom_comp_tensorHom (TensorPower.tensorPowObj_add K p q).inv (𝟙 K)
        (word F g (p + q)) g
      simpa only [Category.id_comp, tensorHom_id] using h.symm
    change (word F g p ⊗ₘ ((word F g q ⊗ₘ g) ≫ pairing F q 1)) ≫
      pairing F p (q + 1) =
        (TensorPower.tensorPowObj_add K p (q + 1)).inv ≫
          ((word F g (p + q) ⊗ₘ g) ≫ pairing F (p + q) 1)
    calc
      _ = (word F g p ⊗ₘ (word F g q ⊗ₘ g)) ≫
          (F.obj (idx p) ◁ pairing F q 1) ≫ pairing F p (q + 1) :=
        (congrArg (fun f => f ≫ pairing F p (q + 1)) hSplit).trans (Category.assoc _ _ _)
      _ = (α_ (TensorPower.tensorPowObj K p) (TensorPower.tensorPowObj K q) K).inv ≫
          ((word F g p ⊗ₘ word F g q) ⊗ₘ g) ≫
            (α_ (F.obj (idx p)) (F.obj (idx q)) (F.obj (idx 1))).hom ≫
              (F.obj (idx p) ◁ pairing F q 1) ≫ pairing F p (q + 1) := by
        simpa only [Category.assoc] using congrArg (fun f => f ≫
          (F.obj (idx p) ◁ pairing F q 1) ≫ pairing F p (q + 1)) hNaturality
      _ = (α_ (TensorPower.tensorPowObj K p) (TensorPower.tensorPowObj K q) K).inv ≫
          ((word F g p ⊗ₘ word F g q) ⊗ₘ g) ≫
            (pairing F p q ▷ F.obj (idx 1)) ≫ pairing F (p + q) 1 :=
        congrArg (fun f =>
          (α_ (TensorPower.tensorPowObj K p) (TensorPower.tensorPowObj K q) K).inv ≫
            ((word F g p ⊗ₘ word F g q) ⊗ₘ g) ≫ f) (pairing_associativity F p q).symm
      _ = (α_ (TensorPower.tensorPowObj K p) (TensorPower.tensorPowObj K q) K).inv ≫
          (((word F g p ⊗ₘ word F g q) ≫ pairing F p q) ⊗ₘ g) ≫
            pairing F (p + q) 1 := by
        simpa only [Category.assoc] using congrArg (fun f =>
          (α_ (TensorPower.tensorPowObj K p) (TensorPower.tensorPowObj K q) K).inv ≫ f ≫
            pairing F (p + q) 1) hCombine
      _ = (α_ (TensorPower.tensorPowObj K p) (TensorPower.tensorPowObj K q) K).inv ≫
          (((TensorPower.tensorPowObj_add K p q).inv ≫ word F g (p + q)) ⊗ₘ g) ≫
            pairing F (p + q) 1 := by rw [ih]
      _ = (α_ (TensorPower.tensorPowObj K p) (TensorPower.tensorPowObj K q) K).inv ≫
          ((TensorPower.tensorPowObj_add K p q).inv ▷ K) ≫
            (word F g (p + q) ⊗ₘ g) ≫ pairing F (p + q) 1 := by
        simpa only [Category.assoc] using congrArg (fun f =>
          (α_ (TensorPower.tensorPowObj K p) (TensorPower.tensorPowObj K q) K).inv ≫ f ≫
            pairing F (p + q) 1) hEnd
      _ = _ := by
        exact (Category.assoc
          (α_ (TensorPower.tensorPowObj K p) (TensorPower.tensorPowObj K q) K).inv
          ((TensorPower.tensorPowObj_add K p q).inv ▷ K)
          ((word F g (p + q) ⊗ₘ g) ≫ pairing F (p + q) 1)).symm.trans
          (congrArg (fun f : TensorPower.tensorPowObj K p ⊗
              (TensorPower.tensorPowObj K q ⊗ K) ⟶ TensorPower.tensorPowObj K (p + q) ⊗ K =>
            f ≫ ((word F g (p + q) ⊗ₘ g) ≫ pairing F (p + q) 1)) hAdd.symm)


/-- The original literal lax multiplication is preserved at every ordered pair of word lengths. -/
theorem word_multiplication (p q : ℕ) :
    (word F g p ⊗ₘ word F g q) ≫ LaxMonoidal.μ F (idx p) (idx q) =
      (TensorPower.tensorPowObj_add K p q).inv ≫ word F g (p + q) :=
  word_pairing F g p q

end CategoryTheory.Sequence.OrderedTensorWords
