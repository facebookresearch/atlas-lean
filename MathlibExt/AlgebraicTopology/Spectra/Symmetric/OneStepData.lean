/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Sequential.ModulePresentation
public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.SphereDayMonoid

/-!
# Compatible one-step data for symmetric tensor-coordinate spectra

The one-step maps use the coefficient-first convention of the existing left
module carrier. All higher tensor-power maps are the original ordered iteration.
Compatibility says that those derived maps are natural in both complete finite
bijections. It supplies neither an action multiplication nor its associativity.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory MonoidalCategory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.TensorPower

namespace CategoryTheory.Spectra.Symmetric

local notation "I" => Operad.SmallFinBijGroupoid
local notation "idx" => Operad.SmallFinBijGroupoid.card

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]

/-- The original finite-index diagram and its coefficient-first one-step maps. -/
structure OneStep (T : V) where
  /-- The full original symmetric-sequence functor. -/
  diagram : I ⥤ V
  /-- The original one-step map at every degree, including degree zero. -/
  bonding (n : ℕ) : T ⊗ diagram.obj (idx n) ⟶ diagram.obj (idx (n + 1))

namespace OneStep

variable {T : V}

/-- Forget only the finite actions, preserving all original levels and one-step maps. -/
def sequential (X : OneStep T) : SequentialSpectrum V T where
  level n := X.diagram.obj (idx n)
  structureMap := X.bonding

/-- Every higher coefficient map is the original ordered iteration of the one-step maps. -/
def iterated (X : OneStep T) (p n : ℕ) :
    tensorPowObj T p ⊗ X.diagram.obj (idx n) ⟶ X.diagram.obj (idx (p + n)) :=
  SequentialSpectrum.iteratedStructureMap X.sequential p n

/-- The empty iteration is the actual unitor and the original degree transport. -/
theorem iterated_zero (X : OneStep T) (n : ℕ) :
    X.iterated 0 n =
      (λ_ (X.diagram.obj (idx n))).hom ≫
        eqToHom (congrArg (fun m => X.diagram.obj (idx m)) (Nat.zero_add n).symm) :=
  SequentialSpectrum.iteratedStructureMap_zero X.sequential n

/-- The complete successor iteration applies the original one-step map and keeps its degree cast. -/
theorem iterated_succ (X : OneStep T) (p n : ℕ) :
    X.iterated (p + 1) n =
      (α_ (tensorPowObj T p) T (X.diagram.obj (idx n))).hom ≫
        tensorPowObj T p ◁ X.bonding n ≫ X.iterated p (n + 1) ≫
        eqToHom (congrArg (fun m => X.diagram.obj (idx m))
          ((Nat.add_succ p n).trans (Nat.succ_add p n).symm)) := by
  simpa only [id_tensorHom] using!
    SequentialSpectrum.iteratedStructureMap_succ X.sequential p n

/-- All iterations associate by the original ordered block comparison, without an action-law premise. -/
theorem iterated_add (X : OneStep T) (p q n : ℕ) :
    (tensorPowObj_add T p q).inv ▷ X.diagram.obj (idx n) ≫
      X.iterated (p + q) n ≫
      eqToHom (congrArg (fun m => X.diagram.obj (idx m)) (Nat.add_assoc p q n)) =
    (α_ (tensorPowObj T p) (tensorPowObj T q) (X.diagram.obj (idx n))).hom ≫
      tensorPowObj T p ◁ X.iterated q n ≫ X.iterated p (q + n) := by
  have h := SequentialSpectrum.iteratedStructureMap_add X.sequential p q n
  have hp : TensorPower.laxTensorPowerPairing (𝟭 V) T p q =
      (tensorPowObj_add T p q).inv := Category.id_comp _
  simpa only [hp, tensorHom_id, id_tensorHom] using! h

end OneStep

variable [SymmetricCategory V]

/-- The source symmetric compatibility condition on the derived tensor-power iterations. -/
def OneStep.Compatible {T : V} (X : OneStep T) : Prop :=
  ∀ {A A' B B' : I} (f : A ⟶ A') (g : B ⟶ B'),
    ((genericSphereSequence T).functor.map f ⊗ₘ X.diagram.map g) ≫
      X.iterated A'.of.len B'.of.len =
    X.iterated A.of.len B.of.len ≫ X.diagram.map (f ⊗ₘ g)

/-- Compatible one-step symmetric spectrum data; all higher maps remain derived. -/
structure OneStepSpectrum (T : V) extends OneStep T where
  /-- Every finite block action respects the original iterated one-step maps. -/
  compatible : toOneStep.Compatible

namespace OneStepSpectrum

variable {T : V}

/-- A map consists of the entire original diagram map and its one-step compatibility. -/
@[ext]
structure Hom (X Y : OneStepSpectrum T) where
  /-- All original finite-index components and their naturality. -/
  map : X.diagram ⟶ Y.diagram
  /-- Compatibility with each original one-step map. -/
  bonding_comm (n : ℕ) :
    (T ◁ map.app (idx n)) ≫ Y.bonding n = X.bonding n ≫ map.app (idx (n + 1))

/-- The original one-step map supplies an actual sequential-spectrum morphism. -/
def Hom.sequential {X Y : OneStepSpectrum T} (f : Hom X Y) :
    X.toOneStep.sequential ⟶ Y.toOneStep.sequential where
  levelMap n := f.map.app (idx n)
  naturality := f.bonding_comm

/-- Every one-step-compatible diagram map preserves all of the derived tensor-power iterations. -/
theorem Hom.iterated_comm {X Y : OneStepSpectrum T} (f : Hom X Y) (p n : ℕ) :
    X.toOneStep.iterated p n ≫ f.map.app (idx (p + n)) =
      tensorPowObj T p ◁ f.map.app (idx n) ≫ Y.toOneStep.iterated p n := by
  simpa only [id_tensorHom] using!
    SequentialSpectrum.iteratedStructureMap_naturality f.sequential p n

/-- Compatible symmetric one-step data form a category with the original levelwise maps. -/
instance : Category.{vV} (OneStepSpectrum T) where
  Hom := Hom
  id X :=
    { map := 𝟙 X.diagram
      bonding_comm := by
        intro n
        simp only [NatTrans.id_app, whiskerLeft_id, Category.id_comp, Category.comp_id] }
  comp f g :=
    { map := f.map ≫ g.map
      bonding_comm := by
        intro n
        simp only [NatTrans.comp_app, whiskerLeft_comp, Category.assoc]
        rw [g.bonding_comm, ← Category.assoc, f.bonding_comm, Category.assoc] }
  id_comp := by
    intro X Y f
    apply Hom.ext
    exact Category.id_comp f.map
  comp_id := by
    intro X Y f
    apply Hom.ext
    exact Category.comp_id f.map
  assoc := by
    intro X Y Z W f g h
    apply Hom.ext
    exact Category.assoc f.map g.map h.map

/-- Every original finite component determines a map of the compatible one-step data. -/
theorem hom_ext {X Y : OneStepSpectrum T} (f g : X ⟶ Y)
    (h : ∀ A : I, f.map.app A = g.map.app A) : f = g := by
  apply Hom.ext
  apply NatTrans.ext
  funext A
  exact h A

/-- The unchanged one-step data forget to the existing sequential spectrum carrier. -/
def sequentialForget : OneStepSpectrum T ⥤ SequentialSpectrum V T where
  obj X := X.toOneStep.sequential
  map f := f.sequential
  map_id _ := rfl
  map_comp _ _ := rfl

end OneStepSpectrum

end CategoryTheory.Spectra.Symmetric
