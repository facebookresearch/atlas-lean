/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OneStepData

/-!
# The original one-step map is recovered from its first ordered iteration

The degree-one tensor-power unit is removed by the original left unitor.
The three original degree transports compose to the literal identity.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory MonoidalCategory
open CategoryTheory.MonoidalCategory

namespace CategoryTheory.Spectra.Symmetric.OneStep

local notation "idx" => Operad.SmallFinBijGroupoid.card

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] {T : V}

/-- The actual degree-one tensor unitor and index transport recover every original one-step map. -/
theorem recover_bonding (X : OneStep T) (n : ℕ) :
    ((λ_ T).inv ▷ X.diagram.obj (idx n)) ≫ X.iterated 1 n ≫
      eqToHom (congrArg (fun m => X.diagram.obj (idx m)) (Nat.one_add n)) = X.bonding n := by
  let F := fun m => X.diagram.obj (idx m)
  let A := F n
  let B := F (n + 1)
  let s : T ⊗ A ⟶ B := X.bonding n
  let c₀ := eqToHom (congrArg F (Nat.zero_add (n + 1)).symm)
  let c₁ := eqToHom (congrArg F ((Nat.add_succ 0 n).trans (Nat.succ_add 0 n).symm))
  let c₂ := eqToHom (congrArg F (Nat.one_add n))
  have hC : c₀ ≫ c₁ ≫ c₂ = 𝟙 B := by
    simp only [c₀, c₁, c₂, eqToHom_trans]
    rfl
  have hFirst : X.iterated 1 n =
      (α_ (𝟙_ V) T A).hom ≫ ((𝟙_ V) ◁ s) ≫ (λ_ B).hom ≫ c₀ ≫ c₁ := by
    have h := congrArg (fun t => (α_ (𝟙_ V) T A).hom ≫ ((𝟙_ V) ◁ s) ≫ t ≫ c₁)
      (X.iterated_zero (n + 1))
    have hm : (α_ (TensorPower.tensorPowObj T 0) T (X.diagram.obj (idx n))).hom ≫
        TensorPower.tensorPowObj T 0 ◁ X.bonding n ≫ X.iterated 0 (n + 1) ≫
        eqToHom (congrArg (fun m => X.diagram.obj (idx m))
          ((Nat.add_succ 0 n).trans (Nat.succ_add 0 n).symm)) =
        (α_ (𝟙_ V) T A).hom ≫ ((𝟙_ V) ◁ s) ≫ (λ_ B).hom ≫ c₀ ≫ c₁ := by
      simpa only [Category.assoc] using! h
    exact (X.iterated_succ 0 n).trans hm
  have hP : ((λ_ T).inv ▷ A) ≫ (α_ (𝟙_ V) T A).hom = (λ_ (T ⊗ A)).inv :=
    (leftUnitor_tensor_inv T A).symm
  have hN : (λ_ (T ⊗ A)).inv ≫ ((𝟙_ V) ◁ s) = s ≫ (λ_ B).inv :=
    (leftUnitor_inv_naturality s).symm
  have hCoherence : ((λ_ T).inv ▷ A) ≫ (α_ (𝟙_ V) T A).hom ≫
      ((𝟙_ V) ◁ s) ≫ (λ_ B).hom = s := by
    rw [← Category.assoc, hP]
    rw [← Category.assoc, hN, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h₁ := congrArg (fun t => ((λ_ T).inv ▷ A) ≫ t ≫ c₂) hFirst
  have h₂ := congrArg (fun t => ((λ_ T).inv ▷ A) ≫ (α_ (𝟙_ V) T A).hom ≫
    ((𝟙_ V) ◁ s) ≫ (λ_ B).hom ≫ t) hC
  have h₃ : (((λ_ T).inv ▷ A) ≫ (α_ (𝟙_ V) T A).hom ≫
      ((𝟙_ V) ◁ s) ≫ (λ_ B).hom) ≫ 𝟙 B = s :=
    (Category.comp_id _).trans hCoherence
  have h₃' : ((λ_ T).inv ▷ A) ≫ (α_ (𝟙_ V) T A).hom ≫
      ((𝟙_ V) ◁ s) ≫ (λ_ B).hom ≫ 𝟙 B = s := by
    simpa only [Category.assoc] using h₃
  have h₁' : ((λ_ T).inv ▷ A) ≫ X.iterated 1 n ≫ c₂ =
      ((λ_ T).inv ▷ A) ≫ (α_ (𝟙_ V) T A).hom ≫
        ((𝟙_ V) ◁ s) ≫ (λ_ B).hom ≫ c₀ ≫ c₁ ≫ c₂ := by
    simpa only [Category.assoc] using! h₁
  exact h₁'.trans (h₂.trans h₃')

end CategoryTheory.Spectra.Symmetric.OneStep
