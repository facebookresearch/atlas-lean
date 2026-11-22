/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OneStepToModule

/-!
# All sphere coefficients are recovered from their original one-step maps

The external unit gives the empty iteration. External associativity at the
degree-one sphere coefficient gives the recursive step. The whole index-map
naturality square retains every required ordinal transport.
-/

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.TensorPower
open scoped CategoryTheory.MonObj ExternalProduct

namespace CategoryTheory.Operad.SmallFinBijGroupoid

local notation "idx" => card

/-- The original one-step index square is exactly the inverse finite block associator. -/
theorem oneStep_index_composite (p n : ℕ) :
    (idx p ◁ eqToHom (congrArg idx (Nat.one_add n))) ≫
      eqToHom (congrArg idx ((Nat.add_succ p n).trans (Nat.succ_add p n).symm)) =
    (α_ (idx p) (idx 1) (idx n)).inv := by
  let e₁ := congrArg (fun a : SmallFinBijGroupoid => idx p ⊗ a) (congrArg idx (Nat.one_add n))
  let e₂ := congrArg idx ((Nat.add_succ p n).trans (Nat.succ_add p n).symm)
  let e₃ := congrArg idx (Nat.add_assoc p 1 n).symm
  have h₁ := congrArg (fun t => t ≫ eqToHom e₂)
    (whiskerLeft_eqToHom (idx p) (congrArg idx (Nat.one_add n)))
  have h₂ : eqToHom e₁ ≫ eqToHom e₂ = eqToHom (e₁.trans e₂) := eqToHom_trans e₁ e₂
  have h₃ : eqToHom (e₁.trans e₂) = eqToHom e₃ :=
    congrArg (fun h : idx p ⊗ (idx 1 ⊗ idx n) = (idx p ⊗ idx 1) ⊗ idx n => eqToHom h)
      (Subsingleton.elim _ _)
  exact h₁.trans (h₂.trans (h₃.trans (associator_inv_eqToHom p 1 n).symm))

end CategoryTheory.Operad.SmallFinBijGroupoid

namespace CategoryTheory.Spectra.Symmetric.OneStepSpectrum

local notation "I" => Operad.SmallFinBijGroupoid
local notation "idx" => Operad.SmallFinBijGroupoid.card

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {T : V}

/-- The external action at the empty coefficient is the actual ordered empty iteration. -/
theorem external_zero
    (d : DayFunctor.ExternalModule.Data (genericSphereDayMonoid T).X) (n : ℕ) :
    d.action.app (idx 0, idx n) =
      (λ_ (d.diagram.obj (idx n))).hom ≫
        eqToHom (congrArg (fun m => d.diagram.obj (idx m)) (Nat.zero_add n).symm) := by
  have h := d.unit (idx n)
  have hs := congrArg (fun t => (t ▷ d.diagram.obj (idx n)) ≫ d.action.app (idx 0, idx n))
    (genericSphereDayMonoid_unit T)
  have hi : (𝟙 (𝟙_ V) ▷ d.diagram.obj (idx n)) ≫ d.action.app (idx 0, idx n) =
      d.action.app (idx 0, idx n) :=
    (congrArg (fun t => t ≫ d.action.app (idx 0, idx n))
      (id_whiskerRight (𝟙_ V) (d.diagram.obj (idx n)))).trans (Category.id_comp _)
  have hm := (congrArg d.diagram.map (Operad.SmallFinBijGroupoid.leftUnitor_inv_eqToHom n)).trans
    (eqToHom_map d.diagram _)
  exact hi.symm.trans (hs.symm.trans h) |>.trans
    (congrArg (fun t => (λ_ (d.diagram.obj (idx n))).hom ≫ t) hm)

/-- External associativity at degree one produces the original full successor-action recursion. -/
theorem external_succ
    (d : DayFunctor.ExternalModule.Data (genericSphereDayMonoid T).X) (p n : ℕ) :
    d.action.app (idx (p + 1), idx n) =
      (α_ (tensorPowObj T p) T (d.diagram.obj (idx n))).hom ≫
        tensorPowObj T p ◁ (oneStepOfExternal d).bonding n ≫
        d.action.app (idx p, idx (n + 1)) ≫
        eqToHom (congrArg (fun m => d.diagram.obj (idx m))
          ((Nat.add_succ p n).trans (Nat.succ_add p n).symm)) := by
  let A := d.diagram.obj (idx n)
  let P := tensorPowObj T p
  let Q := 𝟙_ V ⊗ T
  let m : P ⊗ Q ⟶ tensorPowObj T (p + 1) := (tensorPowObj_add T p 1).inv
  let s : tensorPowObj T (p + 1) ⟶ P ⊗ Q := (tensorPowObj_add T p 1).hom
  let c := eqToHom (congrArg idx (Nat.one_add n))
  let e := (Nat.add_succ p n).trans (Nat.succ_add p n).symm
  let v := eqToHom (congrArg (fun r => d.diagram.obj (idx r)) e)
  let shifted : d.diagram.obj (idx (p + (1 + n))) ⟶ d.diagram.obj (idx (p + (n + 1))) :=
    d.diagram.map (idx p ◁ c)
  let reassociate : d.diagram.obj (idx (p + (1 + n))) ⟶ d.diagram.obj (idx ((p + 1) + n)) :=
    d.diagram.map (α_ (idx p) (idx 1) (idx n)).inv
  let first : Q ⊗ A ⟶ d.diagram.obj (idx (1 + n)) := d.action.app (idx 1, idx n)
  let old : P ⊗ d.diagram.obj (idx (1 + n)) ⟶ d.diagram.obj (idx (p + (1 + n))) :=
    d.action.app (idx p, idx (1 + n))
  let next : P ⊗ d.diagram.obj (idx (n + 1)) ⟶ d.diagram.obj (idx (p + (n + 1))) :=
    d.action.app (idx p, idx (n + 1))
  let L := (s ▷ A) ≫ (α_ P Q A).hom ≫ (P ◁ first) ≫
    old ≫ reassociate
  let R := (α_ P T A).hom ≫ (P ◁ (oneStepOfExternal d).bonding n) ≫
    next ≫ v
  have hs := congrArg (fun t => (t ▷ A) ≫ d.action.app (idx (p + 1), idx n))
    (genericSphereDayMonoid_multiplication T (idx p) (idx 1))
  have hAssoc : (m ▷ A) ≫ d.action.app (idx (p + 1), idx n) =
      (α_ P Q A).hom ≫ (P ◁ d.action.app (idx 1, idx n)) ≫
        d.action.app (idx p, idx (1 + n)) ≫ d.diagram.map (α_ (idx p) (idx 1) (idx n)).inv :=
    hs.symm.trans (d.assoc (idx p) (idx 1) (idx n))
  have hc : (s ▷ A) ≫ (m ▷ A) ≫ d.action.app (idx (p + 1), idx n) =
      d.action.app (idx (p + 1), idx n) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ d.action.app (idx (p + 1), idx n)) (comp_whiskerRight s m A).symm).trans
        ((congrArg (fun t => (t ▷ A) ≫ d.action.app (idx (p + 1), idx n))
          (tensorPowObj_add T p 1).hom_inv_id).trans
          ((congrArg (fun t => t ≫ d.action.app (idx (p + 1), idx n))
            (id_whiskerRight (tensorPowObj T (p + 1)) A)).trans (Category.id_comp _))))
  have hL : d.action.app (idx (p + 1), idx n) = L :=
    hc.symm.trans (congrArg (fun t => (s ▷ A) ≫ t) hAssoc)
  have hPre : (s ▷ A) ≫ (α_ P Q A).hom = (α_ P T A).hom ≫ (P ◁ ((λ_ T).inv ▷ A)) :=
    (congrArg (fun t => (t ▷ A) ≫ (α_ P Q A).hom)
      (Sequence.OrderedTensorAlgebra.tensorPower_add_one_hom T p)).trans
      (associator_naturality_middle P (λ_ T).inv A)
  have hNat : (P ◁ d.diagram.map c) ≫ next = old ≫ shifted := by
    have h := d.action.naturality
      ((𝟙 (idx p), c) : (idx p, idx (1 + n)) ⟶ (idx p, idx (n + 1)))
    simpa only [externalProductBifunctor_obj_map, Functor.comp_map,
      tensor_map, ← tensorHom_def, Functor.map_id, id_tensorHom] using! h
  have hMap : shifted ≫ v = reassociate :=
    (congrArg (fun t => d.diagram.map (idx p ◁ c) ≫ t)
      (eqToHom_map d.diagram (congrArg idx e)).symm).trans
      ((d.diagram.map_comp (idx p ◁ c) (eqToHom (congrArg idx e))).symm.trans
        (congrArg d.diagram.map (Operad.SmallFinBijGroupoid.oneStep_index_composite p n)))
  have hR : R = L := by
    have hb : (oneStepOfExternal d).bonding n = ((λ_ T).inv ▷ A) ≫ first ≫ d.diagram.map c := rfl
    let R' := (α_ P T A).hom ≫ (P ◁ (((λ_ T).inv ▷ A) ≫ first ≫ d.diagram.map c)) ≫ next ≫ v
    have hR' : R = R' := congrArg (fun t => (α_ P T A).hom ≫ (P ◁ t) ≫ next ≫ v) hb
    have hRL : R' = L := by
      dsimp only [R', L]
      simp only [whiskerLeft_comp, Category.assoc]
      slice_lhs 4 5 => rw [hNat]
      simp only [Category.assoc]
      slice_lhs 5 6 => rw [hMap]
      slice_lhs 1 2 => rw [hPre.symm]
      exact (Category.assoc (((s ▷ A) ≫ (α_ P Q A).hom) ≫ (P ◁ first)) old reassociate).trans
        ((Category.assoc ((s ▷ A) ≫ (α_ P Q A).hom) (P ◁ first) (old ≫ reassociate)).trans
          (Category.assoc (s ▷ A) (α_ P Q A).hom ((P ◁ first) ≫ old ≫ reassociate)))
    exact hR'.trans hRL
  exact hL.trans hR.symm

/-- Every full external sphere coefficient is recovered from the original one-step maps. -/
theorem iterated_recovery
    (d : DayFunctor.ExternalModule.Data (genericSphereDayMonoid T).X) (p n : ℕ) :
    (oneStepOfExternal d).iterated p n = d.action.app (idx p, idx n) := by
  induction p generalizing n with
  | zero =>
    exact ((oneStepOfExternal d).iterated_zero n).trans (external_zero d n).symm
  | succ p ih =>
    exact ((oneStepOfExternal d).iterated_succ p n).trans
      ((congrArg (fun t =>
        (α_ (tensorPowObj T p) T (d.diagram.obj (idx n))).hom ≫
          tensorPowObj T p ◁ (oneStepOfExternal d).bonding n ≫ t ≫
          eqToHom (congrArg (fun m => d.diagram.obj (idx m))
            ((Nat.add_succ p n).trans (Nat.succ_add p n).symm))) (ih (n + 1))).trans
        (external_succ d p n).symm)

end CategoryTheory.Spectra.Symmetric.OneStepSpectrum
