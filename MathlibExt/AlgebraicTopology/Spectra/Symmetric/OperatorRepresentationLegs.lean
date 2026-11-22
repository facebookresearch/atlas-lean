/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OperatorActionNaturality

/-!
# Every whole original operator coefficient acts on the representation

The labelled action laws use the actual coend generator relations and the
complete operator composition. Source and target naturality retain all
original finite-index arrows.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory BraidedCategory
open CategoryTheory.MonoidalCategory

namespace CategoryTheory.Spectra.Symmetric.OperatorCoend

local notation "I" => Operad.SmallFinBijGroupoid

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)] {T : V}

/-- The action of every entire original coefficient at its full finite label. -/
def representationLeg (X : Representation T) (a n k : I) (f : a ⊗ n ⟶ k) :
    representationObject X n ⊗ (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a ⟶
      representationObject X k :=
  (representationObject X n ◁ generator T a n k f) ≫ representationAction X n k

/-- Every original coefficient-index map imposes its full labelled action relation. -/
theorem representationLeg_relation (X : Representation T) {a b n k : I} (r : a ⟶ b)
    (f : b ⊗ n ⟶ k) :
    (representationObject X n ◁ (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).map r) ≫
      representationLeg X b n k f = representationLeg X a n k ((r ▷ n) ≫ f) := by
  let P := Operad.SmallFinBijGroupoid.tensorPowerFunctor T
  let s : P.obj a ⟶ P.obj b := P.map r
  let u : P.obj b ⟶ Hom T n k := generator T b n k f
  have hr : s ≫ u = generator T a n k ((r ▷ n) ≫ f) := generator_relation T r f
  have h := congrArg (fun t => (representationObject X n ◁ t) ≫ representationAction X n k) hr
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ representationAction X n k)
      (whiskerLeft_comp (representationObject X n) s u).symm).trans h)

/-- The original whole identity label acts by the actual value unitor. -/
theorem representationLeg_unit (X : Representation T) (n : I) :
    representationLeg X (𝟙_ I) n n (λ_ n).hom = (ρ_ (representationObject X n)).hom :=
  representationAction_unit X n

/-- The original whole coefficient in source module order is the full identity-labelled action. -/
theorem representationCoefficient_eq (X : Representation T) (a n : I) :
    representationCoefficient X a n =
      (β_ ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a) (representationObject X n)).hom ≫
        representationLeg X a n (a ⊗ n) (𝟙 (a ⊗ n)) := rfl

/-- Every original pair of full labelled coefficient actions satisfies genuine operator associativity. -/
theorem representationLeg_assoc (X : Representation T) (a b n k l : I)
    (f : a ⊗ n ⟶ k) (g : b ⊗ k ⟶ l) :
    (α_ (representationObject X n) ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a)
      ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj b)).inv ≫
      (representationLeg X a n k f ▷ (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj b) ≫
      representationLeg X b k l g =
    (representationObject X n ◁ reverseMultiplication T a b) ≫
      representationLeg X (b ⊗ a) n l ((α_ b a n).hom ≫ (b ◁ f) ≫ g) := by
  let P := Operad.SmallFinBijGroupoid.tensorPowerFunctor T
  let A := representationObject X n
  let u : P.obj a ⟶ Hom T n k := generator T a n k f
  let v : P.obj b ⟶ Hom T k l := generator T b k l g
  let z : P.obj (b ⊗ a) ⟶ Hom T n l :=
    generator T (b ⊗ a) n l ((α_ b a n).hom ≫ (b ◁ f) ≫ g)
  have ha : (A ◁ (u ⊗ₘ v)) ≫ (α_ A (Hom T n k) (Hom T k l)).inv =
      (α_ A (P.obj a) (P.obj b)).inv ≫ ((A ◁ u) ⊗ₘ v) := by
    simpa only [id_tensorHom] using associator_inv_naturality (𝟙 A) u v
  have hm : (u ⊗ₘ v) ≫ composition T n k l = reverseMultiplication T a b ≫ z :=
    generator_comp_label T n k l (CostructuredArrow.mk (Y := a) f) (CostructuredArrow.mk (Y := b) g)
  have hFull := congrArg (fun t => (A ◁ (u ⊗ₘ v)) ≫ t) (representationAction_assoc X n k l)
  have hL : (A ◁ (u ⊗ₘ v)) ≫ (α_ A (Hom T n k) (Hom T k l)).inv ≫
      (representationAction X n k ▷ Hom T k l) ≫ representationAction X k l =
      (α_ A (P.obj a) (P.obj b)).inv ≫ representationLeg X a n k f ▷ P.obj b ≫
        representationLeg X b k l g := by
    slice_lhs 1 2 => rw [ha]
    simp only [Category.assoc]
    slice_lhs 2 3 => rw [tensorHom_comp_whiskerRight, tensorHom_def]
    simp only [Category.assoc]
    rfl
  have hR : (A ◁ (u ⊗ₘ v)) ≫ (A ◁ composition T n k l) ≫ representationAction X n l =
      (A ◁ reverseMultiplication T a b) ≫
        representationLeg X (b ⊗ a) n l ((α_ b a n).hom ≫ (b ◁ f) ≫ g) := by
    slice_lhs 1 2 => rw [← whiskerLeft_comp, hm, whiskerLeft_comp]
    simp only [Category.assoc]
    rfl
  have h : (A ◁ (u ⊗ₘ v)) ≫ (α_ A (Hom T n k) (Hom T k l)).inv ≫
      (representationAction X n k ▷ Hom T k l) ≫ representationAction X k l =
      (A ◁ (u ⊗ₘ v)) ≫ (A ◁ composition T n k l) ≫ representationAction X n l := by
    simpa only [Category.assoc] using hFull
  exact hL.symm.trans (h.trans hR)

variable [MonoidalClosed V]

/-- Every original target map is natural on every whole coefficient action. -/
theorem representationLeg_target (X : Representation T) (a n k l : I)
    (f : a ⊗ n ⟶ k) (g : k ⟶ l) :
    representationLeg X a n k f ≫ (ordinaryDiagram X).map g =
      representationLeg X a n l (f ≫ g) := by
  let A := representationObject X n
  let u : (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a ⟶ Hom T n k := generator T a n k f
  let r : representationObject X k ⟶ representationObject X l := (ordinaryDiagram X).map g
  have hn : representationAction X n k ≫ r =
      (A ◁ targetMap T n g) ≫ representationAction X n l := representationAction_target X n g
  have hg : u ≫ targetMap T n g = generator T a n l (f ≫ g) := generator_targetMap T a n k l f g
  change (A ◁ u ≫ representationAction X n k) ≫ r = _
  rw [Category.assoc, hn, ← Category.assoc, ← whiskerLeft_comp, hg]
  rfl

/-- Every original source map is natural on every whole coefficient action. -/
theorem representationLeg_source (X : Representation T) (a n k l : I)
    (f : n ⟶ k) (g : a ⊗ k ⟶ l) :
    ((ordinaryDiagram X).map f ▷ (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a) ≫
      representationLeg X a k l g = representationLeg X a n l ((a ◁ f) ≫ g) := by
  let A := representationObject X n
  let B := representationObject X k
  let u : (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a ⟶ Hom T k l := generator T a k l g
  let r : A ⟶ B := (ordinaryDiagram X).map f
  have hn : (r ▷ Hom T k l) ≫ representationAction X k l =
      (A ◁ sourceMap T f l) ≫ representationAction X n l := representationAction_source X f l
  have hg : u ≫ sourceMap T f l = generator T a n l ((a ◁ f) ≫ g) :=
    generator_sourceMap T a n k l f g
  change (r ▷ (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a) ≫
    (B ◁ u ≫ representationAction X k l) = _
  slice_lhs 1 2 => rw [← whisker_exchange]
  simp only [Category.assoc]
  rw [hn]
  rw [← Category.assoc, ← whiskerLeft_comp, hg]
  rfl

/-- The original full module-order coefficient retains every coefficient-index map. -/
theorem representationCoefficient_natural (X : Representation T) {a b : I} (f : a ⟶ b) (n : I) :
    ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).map f ▷ representationObject X n) ≫
      representationCoefficient X b n =
      representationCoefficient X a n ≫ (ordinaryDiagram X).map (f ▷ n) := by
  let r : representationObject X (a ⊗ n) ⟶ representationObject X (b ⊗ n) :=
    (ordinaryDiagram X).map (f ▷ n)
  have hRel := representationLeg_relation X f (𝟙 (b ⊗ n))
  have hTarget : representationLeg X a n (a ⊗ n) (𝟙 (a ⊗ n)) ≫ r =
      representationLeg X a n (b ⊗ n) (f ▷ n) := by
    simpa only [Category.id_comp] using!
      representationLeg_target X a n (a ⊗ n) (b ⊗ n) (𝟙 (a ⊗ n)) (f ▷ n)
  simp only [Category.comp_id] at hRel
  change ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).map f ▷ representationObject X n) ≫
    representationCoefficient X b n = representationCoefficient X a n ≫ r
  simp only [representationCoefficient_eq, Category.assoc]
  slice_lhs 1 2 => rw [braiding_naturality_left]
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [hRel]
  rw [hTarget]

/-- The original full module-order coefficient retains every object-index map. -/
theorem representationCoefficient_index (X : Representation T) (a : I) {n k : I} (f : n ⟶ k) :
    ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a ◁ (ordinaryDiagram X).map f) ≫
      representationCoefficient X a k =
      representationCoefficient X a n ≫ (ordinaryDiagram X).map (a ◁ f) := by
  let A := representationObject X n
  let B := representationObject X k
  let r : A ⟶ B := (ordinaryDiagram X).map f
  let s : representationObject X (a ⊗ n) ⟶ representationObject X (a ⊗ k) :=
    (ordinaryDiagram X).map (a ◁ f)
  have hSource : (r ▷ (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a) ≫
      representationLeg X a k (a ⊗ k) (𝟙 (a ⊗ k)) = representationLeg X a n (a ⊗ k) (a ◁ f) := by
    simpa only [Category.comp_id] using! representationLeg_source X a n k (a ⊗ k) f (𝟙 (a ⊗ k))
  have hTarget : representationLeg X a n (a ⊗ n) (𝟙 (a ⊗ n)) ≫ s =
      representationLeg X a n (a ⊗ k) (a ◁ f) := by
    simpa only [Category.id_comp] using!
      representationLeg_target X a n (a ⊗ n) (a ⊗ k) (𝟙 (a ⊗ n)) (a ◁ f)
  change ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a ◁ r) ≫
    representationCoefficient X a k = representationCoefficient X a n ≫ s
  simp only [representationCoefficient_eq, Category.assoc]
  slice_lhs 1 2 => rw [braiding_naturality_right]
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [hSource]
  rw [hTarget]

end CategoryTheory.Spectra.Symmetric.OperatorCoend
