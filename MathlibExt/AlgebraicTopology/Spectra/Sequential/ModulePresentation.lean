/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Sequential.Basic
public import MathlibExt.CategoryTheory.Monoidal.Sequence.TensorPower

/-!
# Sequential spectra as modules over the tensor-power sequence

This module constructs the ordered iterated structure maps and the
equivalence between sequential spectra and tensor-power sequence modules.
-/

set_option autoImplicit false

noncomputable section

universe vC uC

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory.LawfulDayConvolutionMonoidalCategoryStruct
open scoped ExternalProduct MonoidalCategory MonObj MonoidalLeftAction

namespace CategoryTheory.SequentialSpectrum

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]

@[expose] public section

/-- The ordered `p`-fold left structure map from `K ^⊗ p ⊗ X_q` to `X_{p+q}`.
The recursion applies the structure maps from the rightmost copy of `K` inward. -/
noncomputable def iteratedStructureMap {K : C}
    (X : SequentialSpectrum C K) : ∀ (p q : ℕ),
      TensorPower.tensorPowObj K p ⊗ X.level q ⟶ X.level (p + q)
  | 0, q =>
      (λ_ (X.level q)).hom ≫
        eqToHom (congrArg X.level (Nat.zero_add q).symm)
  | p + 1, q =>
      (α_ (TensorPower.tensorPowObj K p) K (X.level q)).hom ≫
        (𝟙 _ ⊗ₘ X.structureMap q) ≫
        iteratedStructureMap X p (q + 1) ≫
        eqToHom (congrArg X.level
          ((Nat.add_succ p q).trans (Nat.succ_add p q).symm))

@[simp]
theorem iteratedStructureMap_zero {K : C}
    (X : SequentialSpectrum C K) (q : ℕ) :
    iteratedStructureMap X 0 q =
      (λ_ (X.level q)).hom ≫
        eqToHom (congrArg X.level (Nat.zero_add q).symm) :=
  rfl

theorem iteratedStructureMap_succ {K : C}
    (X : SequentialSpectrum C K) (p q : ℕ) :
    iteratedStructureMap X (p + 1) q =
      (α_ (TensorPower.tensorPowObj K p) K (X.level q)).hom ≫
        (𝟙 _ ⊗ₘ X.structureMap q) ≫
        iteratedStructureMap X p (q + 1) ≫
        eqToHom (congrArg X.level
          ((Nat.add_succ p q).trans (Nat.succ_add p q).symm)) :=
  rfl

/-- Iterated structure maps commute with morphisms of sequential spectra. -/
theorem iteratedStructureMap_naturality {K : C}
    {X Y : SequentialSpectrum C K} (f : X ⟶ Y) (p q : ℕ) :
    iteratedStructureMap X p q ≫ f.levelMap (p + q) =
      (𝟙 (TensorPower.tensorPowObj K p) ⊗ₘ f.levelMap q) ≫
        iteratedStructureMap Y p q := by
  let levelMap_eqToHom {a b : ℕ} (h : a = b) :
      eqToHom (congrArg X.level h) ≫ f.levelMap b =
        f.levelMap a ≫ eqToHom (congrArg Y.level h) := by
    subst b
    simp
  induction p generalizing q with
  | zero =>
      rw [iteratedStructureMap, iteratedStructureMap]
      simp only [TensorPower.tensorPowObj_zero,
        MonoidalCategory.id_tensorHom]
      calc
        _ = (λ_ (X.level q)).hom ≫ f.levelMap q ≫
              eqToHom (congrArg Y.level (Nat.zero_add q).symm) := by
            simp only [Category.assoc]
            rw [levelMap_eqToHom
              (h := (Nat.zero_add q).symm)]
        _ = _ := by
            rw [← Category.assoc,
              ← MonoidalCategory.leftUnitor_naturality]
            simp only [Category.assoc]
  | succ p ih =>
      rw [iteratedStructureMap, iteratedStructureMap]
      simp only [TensorPower.tensorPowObj_succ,
        MonoidalCategory.id_tensorHom]
      calc
        _ = (α_ (TensorPower.tensorPowObj K p) K (X.level q)).hom ≫
              (TensorPower.tensorPowObj K p ◁ X.structureMap q) ≫
              iteratedStructureMap X p (q + 1) ≫
              f.levelMap (p + (q + 1)) ≫
              eqToHom (congrArg Y.level
                ((Nat.add_succ p q).trans
                  (Nat.succ_add p q).symm)) := by
            simp only [Category.assoc]
            rw [levelMap_eqToHom
              (h := (Nat.add_succ p q).trans
                (Nat.succ_add p q).symm)]
        _ = (α_ (TensorPower.tensorPowObj K p) K (X.level q)).hom ≫
              (TensorPower.tensorPowObj K p ◁ X.structureMap q) ≫
              (TensorPower.tensorPowObj K p ◁ f.levelMap (q + 1)) ≫
              iteratedStructureMap Y p (q + 1) ≫
              eqToHom (congrArg Y.level
                ((Nat.add_succ p q).trans
                  (Nat.succ_add p q).symm)) := by
            slice_lhs 3 4 =>
              rw [ih]
            simp only [MonoidalCategory.id_tensorHom, Category.assoc]
        _ = (α_ (TensorPower.tensorPowObj K p) K (X.level q)).hom ≫
              (TensorPower.tensorPowObj K p ◁ K ◁ f.levelMap q) ≫
              (TensorPower.tensorPowObj K p ◁ Y.structureMap q) ≫
              iteratedStructureMap Y p (q + 1) ≫
              eqToHom (congrArg Y.level
                ((Nat.add_succ p q).trans
                  (Nat.succ_add p q).symm)) := by
            slice_lhs 2 3 =>
              rw [← MonoidalCategory.whiskerLeft_comp,
                ← f.naturality, MonoidalCategory.whiskerLeft_comp]
            simp only [Category.assoc]
        _ = ((TensorPower.tensorPowObj K p ⊗ K) ◁ f.levelMap q) ≫
              (α_ (TensorPower.tensorPowObj K p) K (Y.level q)).hom ≫
              (TensorPower.tensorPowObj K p ◁ Y.structureMap q) ≫
              iteratedStructureMap Y p (q + 1) ≫
              eqToHom (congrArg Y.level
                ((Nat.add_succ p q).trans
                  (Nat.succ_add p q).symm)) := by
            slice_lhs 1 2 =>
              rw [← MonoidalCategory.associator_naturality_right]
            simp only [Category.assoc]
        _ = _ := rfl

end

private theorem laxTensorPowerPairing_succ_right (K : C) (p r : ℕ) :
    (α_ (TensorPower.tensorPowObj K p)
      (TensorPower.tensorPowObj K r) K).hom ≫
        (TensorPower.tensorPowObj_add K p (r + 1)).inv =
      (TensorPower.tensorPowObj_add K p r).inv ⊗ₘ 𝟙 K := by
  let e :=
    (tensorIso (TensorPower.tensorPowObj_add K p r) (Iso.refl K)) ≪≫
      (α_ (TensorPower.tensorPowObj K p)
        (TensorPower.tensorPowObj K r) K)
  change (α_ _ _ _).hom ≫ e.inv = _
  apply (cancel_mono e.hom).1
  dsimp only [e, Iso.trans_hom, tensorIso]
  simp

private theorem iteratedStructureMap_eqToHom {K : C}
    (X : SequentialSpectrum C K) (p : ℕ) {q q' : ℕ} (h : q = q') :
    iteratedStructureMap X p q ≫
        eqToHom (congrArg X.level
          (congrArg (fun n => p + n) h)) =
      (𝟙 (TensorPower.tensorPowObj K p) ⊗ₘ
          eqToHom (congrArg X.level h)) ≫
        iteratedStructureMap X p q' := by
  cases h
  simp

public theorem iteratedStructureMap_add {K : C}
    (X : SequentialSpectrum C K) (p r q : ℕ) :
    (TensorPower.laxTensorPowerPairing (𝟭 C) K p r ⊗ₘ
        𝟙 (X.level q)) ≫
        iteratedStructureMap X (p + r) q ≫
        eqToHom (congrArg X.level (Nat.add_assoc p r q)) =
      (α_ (TensorPower.tensorPowObj K p)
        (TensorPower.tensorPowObj K r) (X.level q)).hom ≫
        (𝟙 _ ⊗ₘ iteratedStructureMap X r q) ≫
        iteratedStructureMap X p (r + q) := by
  let iteratedStepEq (n q : ℕ) : n + (q + 1) = (n + 1) + q :=
    (Nat.add_succ n q).trans (Nat.succ_add n q).symm
  let laxTensorPowerPairing_id (K : C) (p r : ℕ) :
      TensorPower.laxTensorPowerPairing (𝟭 C) K p r =
        (TensorPower.tensorPowObj_add K p r).inv := by
    unfold TensorPower.laxTensorPowerPairing
    change 𝟙 _ ≫ (TensorPower.tensorPowObj_add K p r).inv = _
    rw [Category.id_comp]
  let iteratedLevelTransport {K : C}
      (X : SequentialSpectrum C K) (p r q : ℕ) :
      (congrArg X.level (iteratedStepEq (p + r) q)).trans
          (congrArg X.level (Nat.add_assoc p (r + 1) q)) =
        (congrArg X.level (Nat.add_assoc p r (q + 1))).trans
          (congrArg X.level
            (congrArg (fun n => p + n) (iteratedStepEq r q))) := by
    apply Subsingleton.elim
  let iteratedScalarStep
      {A B D K Z Z' : C} (L : A ⊗ B ⟶ D) (σ : K ⊗ Z ⟶ Z') :
      ((L ⊗ₘ 𝟙 K) ⊗ₘ 𝟙 Z) ≫ (α_ D K Z).hom ≫
          (𝟙 D ⊗ₘ σ) =
        (α_ (A ⊗ B) K Z).hom ≫
          (𝟙 (A ⊗ B) ⊗ₘ σ) ≫ (L ⊗ₘ 𝟙 Z') := by
    rw [← Category.assoc, MonoidalCategory.associator_naturality]
    simp only [Category.assoc, tensorHom_comp_tensorHom,
      MonoidalCategory.id_tensorHom_id, Category.comp_id, Category.id_comp]
  let iteratedPentagonStep
      (A B K Z Z' : C) (σ : K ⊗ Z ⟶ Z') :
      ((α_ A B K).hom ▷ Z) ≫ (α_ A (B ⊗ K) Z).hom ≫
          (A ◁ (α_ B K Z).hom) ≫ (A ◁ (B ◁ σ)) =
        (α_ (A ⊗ B) K Z).hom ≫
          (𝟙 (A ⊗ B) ⊗ₘ σ) ≫ (α_ A B Z').hom := by
    rw [MonoidalCategory.pentagon_assoc]
    rw [← MonoidalCategory.associator_naturality_right A B σ]
    simp only [id_tensorHom]
  rw [laxTensorPowerPairing_id]
  simp only [tensorHom_id]
  induction r generalizing p q with
  | zero =>
      have hAddZero :
          (TensorPower.laxTensorPowerPairing (𝟭 C) K p 0 ⊗ₘ
              𝟙 (X.level q)) ≫
              iteratedStructureMap X (p + 0) q ≫
              eqToHom (congrArg X.level (Nat.add_assoc p 0 q)) =
            (α_ (TensorPower.tensorPowObj K p)
              (TensorPower.tensorPowObj K 0) (X.level q)).hom ≫
              (𝟙 _ ⊗ₘ iteratedStructureMap X 0 q) ≫
              iteratedStructureMap X p (0 + q) := by
        rw [laxTensorPowerPairing_id]
        simp only [tensorHom_id]
        have hPairZero :
            (TensorPower.tensorPowObj_add K p 0).inv =
              (ρ_ (TensorPower.tensorPowObj K p)).hom := by
          rfl
        rw [hPairZero, iteratedStructureMap_zero]
        simp only [Functor.id_obj, TensorPower.tensorPowObj_zero] at ⊢
        let h : q = 0 + q := (Nat.zero_add q).symm
        have hTransport :
            eqToHom (congrArg X.level (Nat.add_assoc p 0 q)) =
              eqToHom (congrArg X.level
                (congrArg (fun n => p + n) h)) := by
          congr 1
        rw [hTransport]
        have hpZero : iteratedStructureMap X (p + 0) q =
            iteratedStructureMap X p q := rfl
        rw [hpZero]
        rw [iteratedStructureMap_eqToHom X p h]
        simpa only [id_tensorHom, whiskerLeft_comp, Category.assoc] using
          congrArg
            (fun k => k ≫
              (𝟙 (TensorPower.tensorPowObj K p) ⊗ₘ
                eqToHom (congrArg X.level h)) ≫
              iteratedStructureMap X p (0 + q))
            (MonoidalCategory.triangle
              (TensorPower.tensorPowObj K p) (X.level q)).symm
      simpa only [laxTensorPowerPairing_id, tensorHom_id] using hAddZero
  | succ r ih =>
      dsimp only [TensorPower.tensorPowObj] at ⊢
      have hTransport :
          eqToHom (congrArg X.level (iteratedStepEq (p + r) q)) ≫
              eqToHom (congrArg X.level (Nat.add_assoc p (r + 1) q)) =
            eqToHom (congrArg X.level (Nat.add_assoc p r (q + 1))) ≫
              eqToHom (congrArg X.level
                (congrArg (fun n => p + n) (iteratedStepEq r q))) := by
        rw [eqToHom_trans, eqToHom_trans, iteratedLevelTransport]
      have hLeft :
          ((α_ (TensorPower.tensorPowObj K p)
              (TensorPower.tensorPowObj K r) K).hom ▷ X.level q) ≫
              (((TensorPower.tensorPowObj_add K p (r + 1)).inv ▷
                  X.level q) ≫
                iteratedStructureMap X (p + (r + 1)) q ≫
                eqToHom (congrArg X.level
                  (Nat.add_assoc p (r + 1) q))) =
            (α_ (TensorPower.tensorPowObj K p ⊗
                TensorPower.tensorPowObj K r) K (X.level q)).hom ≫
              (𝟙 _ ⊗ₘ X.structureMap q) ≫
              ((TensorPower.tensorPowObj_add K p r).inv ▷
                X.level (q + 1)) ≫
              iteratedStructureMap X (p + r) (q + 1) ≫
              eqToHom (congrArg X.level
                (Nat.add_assoc p r (q + 1))) ≫
              eqToHom (congrArg X.level
                (congrArg (fun n => p + n) (iteratedStepEq r q))) := by
        have hPairW := congrArg
          (fun k => k ▷ X.level q)
          (laxTensorPowerPairing_succ_right K p r)
        have hPairW' :
            ((α_ (TensorPower.tensorPowObj K p)
                (TensorPower.tensorPowObj K r) K).hom ▷ X.level q) ≫
                ((TensorPower.tensorPowObj_add K p (r + 1)).inv ▷
                  X.level q) =
              (((TensorPower.tensorPowObj_add K p r).inv ⊗ₘ 𝟙 K) ▷
                X.level q) := by
          exact (MonoidalCategory.comp_whiskerRight _ _ _).symm.trans hPairW
        have hIterSucc :
            iteratedStructureMap X (p + (r + 1)) q =
              (α_ (TensorPower.tensorPowObj K (p + r)) K
                (X.level q)).hom ≫
              (𝟙 _ ⊗ₘ X.structureMap q) ≫
              iteratedStructureMap X (p + r) (q + 1) ≫
              eqToHom (congrArg X.level (iteratedStepEq (p + r) q)) :=
          iteratedStructureMap_succ X (p + r) q
        have hScalarW :
            (((TensorPower.tensorPowObj_add K p r).inv ⊗ₘ 𝟙 K) ▷
                X.level q) ≫
                (α_ (TensorPower.tensorPowObj K (p + r)) K
                  (X.level q)).hom ≫
                (𝟙 (TensorPower.tensorPowObj K (p + r)) ⊗ₘ
                  X.structureMap q) =
              (α_ (TensorPower.tensorPowObj K p ⊗
                TensorPower.tensorPowObj K r) K (X.level q)).hom ≫
                (𝟙 (TensorPower.tensorPowObj K p ⊗
                  TensorPower.tensorPowObj K r) ⊗ₘ X.structureMap q) ≫
                ((TensorPower.tensorPowObj_add K p r).inv ▷
                  X.level (q + 1)) := by
          simpa only [tensorHom_id] using
            (iteratedScalarStep
              (L := (TensorPower.tensorPowObj_add K p r).inv)
              (σ := X.structureMap q))
        calc
          _ = (((TensorPower.tensorPowObj_add K p r).inv ⊗ₘ 𝟙 K) ▷
                  X.level q) ≫
                iteratedStructureMap X (p + (r + 1)) q ≫
                eqToHom (congrArg X.level
                  (Nat.add_assoc p (r + 1) q)) := by
              have hPost := congrArg
                (fun k => k ≫
                  iteratedStructureMap X (p + (r + 1)) q ≫
                  eqToHom (congrArg X.level
                    (Nat.add_assoc p (r + 1) q))) hPairW'
              exact (Category.assoc _ _ _).symm.trans hPost
          _ = (((TensorPower.tensorPowObj_add K p r).inv ⊗ₘ 𝟙 K) ▷
                  X.level q) ≫
                (α_ (TensorPower.tensorPowObj K (p + r)) K
                  (X.level q)).hom ≫
                (𝟙 _ ⊗ₘ X.structureMap q) ≫
                iteratedStructureMap X (p + r) (q + 1) ≫
                eqToHom (congrArg X.level (iteratedStepEq (p + r) q)) ≫
                eqToHom (congrArg X.level
                  (Nat.add_assoc p (r + 1) q)) := by
              simpa only [Category.assoc] using congrArg
                (fun k =>
                  (((TensorPower.tensorPowObj_add K p r).inv ⊗ₘ 𝟙 K) ▷
                    X.level q) ≫ k ≫
                  eqToHom (congrArg X.level
                    (Nat.add_assoc p (r + 1) q))) hIterSucc
          _ = (α_ (TensorPower.tensorPowObj K p ⊗
                  TensorPower.tensorPowObj K r) K (X.level q)).hom ≫
                (𝟙 _ ⊗ₘ X.structureMap q) ≫
                ((TensorPower.tensorPowObj_add K p r).inv ▷
                  X.level (q + 1)) ≫
                iteratedStructureMap X (p + r) (q + 1) ≫
                eqToHom (congrArg X.level (iteratedStepEq (p + r) q)) ≫
                eqToHom (congrArg X.level
                  (Nat.add_assoc p (r + 1) q)) := by
              simpa only [Category.assoc] using congrArg
                (fun k => k ≫
                  iteratedStructureMap X (p + r) (q + 1) ≫
                  eqToHom (congrArg X.level (iteratedStepEq (p + r) q)) ≫
                  eqToHom (congrArg X.level
                    (Nat.add_assoc p (r + 1) q))) hScalarW
          _ = _ := by
              simpa only [Category.assoc] using congrArg
                (fun k =>
                  (α_ (TensorPower.tensorPowObj K p ⊗
                    TensorPower.tensorPowObj K r) K (X.level q)).hom ≫
                  (𝟙 _ ⊗ₘ X.structureMap q) ≫
                  ((TensorPower.tensorPowObj_add K p r).inv ▷
                    X.level (q + 1)) ≫
                  iteratedStructureMap X (p + r) (q + 1) ≫ k)
                hTransport
      have hRight :
          ((α_ (TensorPower.tensorPowObj K p)
              (TensorPower.tensorPowObj K r) K).hom ▷ X.level q) ≫
              ((α_ (TensorPower.tensorPowObj K p)
                (TensorPower.tensorPowObj K (r + 1))
                (X.level q)).hom ≫
                (𝟙 _ ⊗ₘ iteratedStructureMap X (r + 1) q) ≫
                iteratedStructureMap X p ((r + 1) + q)) =
            (α_ (TensorPower.tensorPowObj K p ⊗
                TensorPower.tensorPowObj K r) K (X.level q)).hom ≫
              (𝟙 _ ⊗ₘ X.structureMap q) ≫
              (α_ (TensorPower.tensorPowObj K p)
                (TensorPower.tensorPowObj K r)
                (X.level (q + 1))).hom ≫
              (𝟙 _ ⊗ₘ iteratedStructureMap X r (q + 1)) ≫
              (𝟙 _ ⊗ₘ eqToHom
                (congrArg X.level (iteratedStepEq r q))) ≫
              iteratedStructureMap X p ((r + 1) + q) := by
        dsimp only [TensorPower.tensorPowObj]
        rw [iteratedStructureMap_succ]
        simp only [id_tensorHom]
        rw [whiskerLeft_comp, whiskerLeft_comp, whiskerLeft_comp]
        simp only [Category.assoc]
        have hPentagon := congrArg
          (fun k => k ≫
            (TensorPower.tensorPowObj K p ◁
              iteratedStructureMap X r (q + 1)))
          (iteratedPentagonStep
            (TensorPower.tensorPowObj K p)
            (TensorPower.tensorPowObj K r) K
            (X.level q) (X.level (q + 1)) (X.structureMap q))
        have hPentagonFull := congrArg
          (fun k => k ≫
            (TensorPower.tensorPowObj K p ◁
              eqToHom (congrArg X.level (iteratedStepEq r q))) ≫
            iteratedStructureMap X p ((r + 1) + q))
          hPentagon
        simpa only [Category.assoc, id_tensorHom] using hPentagonFull
      apply (cancel_epi
        ((α_ (TensorPower.tensorPowObj K p)
          (TensorPower.tensorPowObj K r) K).hom ▷ X.level q)).1
      calc
        _ = _ := hLeft
        _ = _ := by
          have hIHFull := congrArg
            (fun k =>
              (α_ (TensorPower.tensorPowObj K p ⊗
                TensorPower.tensorPowObj K r) K (X.level q)).hom ≫
              (𝟙 _ ⊗ₘ X.structureMap q) ≫ k ≫
              eqToHom (congrArg X.level
                (congrArg (fun n => p + n) (iteratedStepEq r q))))
            (ih (p := p) (q := q + 1))
          have hEqFull := congrArg
            (fun k =>
              (α_ (TensorPower.tensorPowObj K p ⊗
                TensorPower.tensorPowObj K r) K (X.level q)).hom ≫
              (𝟙 _ ⊗ₘ X.structureMap q) ≫
              (α_ (TensorPower.tensorPowObj K p)
                (TensorPower.tensorPowObj K r)
                (X.level (q + 1))).hom ≫
              (𝟙 _ ⊗ₘ iteratedStructureMap X r (q + 1)) ≫ k)
            (iteratedStructureMap_eqToHom
              X p (iteratedStepEq r q))
          calc
            _ = _ := by simpa only [Category.assoc] using hIHFull
            _ = _ := by simpa only [Category.assoc] using hEqFull
        _ = _ := hRight.symm

namespace ModuleReconstruction

variable {K : C}

@[expose] public section

/-- The sequence of the original levels of a sequential spectrum. -/
noncomputable def spectrumSequence
    (X : SequentialSpectrum C K) : Sequence C :=
  DayFunctor.mk <| Discrete.functor fun n : Multiplicative ℕ =>
    X.level n.toAdd

/-- The levelwise sequence map induced by a morphism of sequential spectra. -/
noncomputable def spectrumSequenceMap
    {X Y : SequentialSpectrum C K} (f : X ⟶ Y) :
    spectrumSequence X ⟶ spectrumSequence Y :=
  DayFunctor.Hom.mk <| Discrete.natTrans fun i =>
    f.levelMap (Sequence.degree i)

/-- Tensoring two sequence indices adds their natural degrees. -/
private theorem degree_tensor (i j : Sequence.Index) :
    Sequence.degree i + Sequence.degree j =
      Sequence.degree (i ⊗ j) := by
  cases i
  cases j
  rfl

/-- The natural Day action descent given by the ordered iterated structure maps. -/
noncomputable def spectrumActionDesc
    (X : SequentialSpectrum C K) :
    (Sequence.tensorPowerSequence K).functor ⊠
        (spectrumSequence X).functor ⟶
      tensor Sequence.Index ⋙ (spectrumSequence X).functor := {
  app i := iteratedStructureMap X
      (Sequence.degree i.1) (Sequence.degree i.2) ≫
    eqToHom (congrArg X.level (by rfl))
  naturality := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ f
    have h : (i, j) = (i', j') := Prod.ext
      (Discrete.ext (Discrete.eq_of_hom f.1))
      (Discrete.ext (Discrete.eq_of_hom f.2))
    cases h
    rw [show f = 𝟙 _ by ext <;> apply Discrete.hom_eq]
    simp }

/-- The Day action descent commutes with every original spectrum morphism. -/
theorem spectrumActionDesc_map
    {X Y : SequentialSpectrum C K} (f : X ⟶ Y)
    (i j : Sequence.Index) :
    (spectrumActionDesc X).app (i, j) ≫
        (spectrumSequenceMap f).natTrans.app (i ⊗ j) =
      ((Sequence.tensorPowerSequence K).functor.obj i ◁
          (spectrumSequenceMap f).natTrans.app j) ≫
        (spectrumActionDesc Y).app (i, j) := by
  let h := degree_tensor i j
  change
    (iteratedStructureMap X (Sequence.degree i) (Sequence.degree j) ≫
        eqToHom (congrArg X.level h)) ≫
          f.levelMap (Sequence.degree (i ⊗ j)) =
      (TensorPower.tensorPowObj K (Sequence.degree i) ◁
          f.levelMap (Sequence.degree j)) ≫
        (iteratedStructureMap Y (Sequence.degree i) (Sequence.degree j) ≫
          eqToHom (congrArg Y.level h))
  rw [Category.assoc, ← eqToHom_naturality (fun n => f.levelMap n) h]
  rw [← Category.assoc, iteratedStructureMap_naturality]
  simp only [MonoidalCategory.id_tensorHom, Category.assoc]

/-- The action descent at a canonical degree pair is its iterated structure map. -/
theorem spectrumActionDesc_index
    (X : SequentialSpectrum C K) (p q : ℕ) :
    (spectrumActionDesc X).app
        (Sequence.index p, Sequence.index q) =
      iteratedStructureMap X p q := by
  change iteratedStructureMap X p q ≫ eqToHom _ = _
  apply eq_of_heq
  exact comp_eqToHom_heq _ _

/-- The action descent on a tensor of scalar indices retains the ordered total degree. -/
theorem spectrumActionDesc_tensor_index
    (X : SequentialSpectrum C K) (p r q : ℕ) :
    (spectrumActionDesc X).app
        (Sequence.index p ⊗ Sequence.index r, Sequence.index q) =
      iteratedStructureMap X (p + r) q := by
  change iteratedStructureMap X (p + r) q ≫ eqToHom _ = _
  apply eq_of_heq
  exact comp_eqToHom_heq _ _

/-- The action descent on a tensor of level indices retains the ordered total degree. -/
theorem spectrumActionDesc_index_tensor
    (X : SequentialSpectrum C K) (p r q : ℕ) :
    (spectrumActionDesc X).app
        (Sequence.index p, Sequence.index r ⊗ Sequence.index q) =
      iteratedStructureMap X p (r + q) := by
  change iteratedStructureMap X p (r + q) ≫ eqToHom _ = _
  apply eq_of_heq
  exact comp_eqToHom_heq _ _


/-- The original ordered pairing with degree one is the scalar left-unitor whisker. -/
private theorem laxTensorPowerPairing_one (K : C) (p : ℕ) :
    TensorPower.laxTensorPowerPairing (𝟭 C) K p 1 =
      TensorPower.tensorPowObj K p ◁ (λ_ K).hom := by
  have hPairingRaw :
      TensorPower.laxTensorPowerPairing (𝟭 C) K p 1 =
        (TensorPower.tensorPowObj_add K p 1).inv := by
    change
      (Functor.LaxMonoidal.μ (𝟭 C)
          (TensorPower.tensorPowObj K p)
          (TensorPower.tensorPowObj K 1) ≫
        (𝟭 C).map (TensorPower.tensorPowObj_add K p 1).inv) = _
    simp only [Functor.LaxMonoidal.id_μ, Functor.id_obj,
      Functor.id_map, Category.id_comp]
  rw [hPairingRaw]
  calc
    _ = (α_ (TensorPower.tensorPowObj K p) (𝟙_ C) K).inv ≫
        ((ρ_ (TensorPower.tensorPowObj K p)).hom ⊗ₘ 𝟙 K) := by rfl
    _ = (α_ (TensorPower.tensorPowObj K p) (𝟙_ C) K).inv ≫
        ((ρ_ (TensorPower.tensorPowObj K p)).hom ▷ K) := by
      rw [MonoidalCategory.tensorHom_id]
    _ = _ := MonoidalCategory.triangle_assoc_comp_right
      (TensorPower.tensorPowObj K p) K

/-- The original degree-one pairing cancels the inverse-unitor prefix inside the associator. -/
private theorem laxTensorPowerPairing_one_prefix (K : C) (p : ℕ) (Z : C) :
    (TensorPower.laxTensorPowerPairing (𝟭 C) K p 1 ▷ Z) ≫
        (α_ (TensorPower.tensorPowObj K p) K Z).hom ≫
        (TensorPower.tensorPowObj K p ◁ ((λ_ K).inv ⊗ₘ 𝟙 Z)) =
      (α_ (TensorPower.tensorPowObj K p) (𝟙_ C ⊗ K) Z).hom := by
  let Pp := TensorPower.tensorPowObj K p
  let unitPrefixRaw : K ⊗ Z ⟶ (𝟙_ C ⊗ K) ⊗ Z :=
    (λ_ K).inv ⊗ₘ 𝟙 Z
  change (TensorPower.laxTensorPowerPairing (𝟭 C) K p 1 ▷ Z) ≫
      (α_ Pp K Z).hom ≫ (Pp ◁ unitPrefixRaw) =
    (α_ Pp (𝟙_ C ⊗ K) Z).hom
  have hPairingOneWhisker := congrArg
    (fun k => k ▷ Z) (laxTensorPowerPairing_one K p)
  have hAssocNat :
      ((Pp ◁ (λ_ K).hom) ▷ Z) ≫ (α_ Pp K Z).hom =
        (α_ Pp (𝟙_ C ⊗ K) Z).hom ≫
          (Pp ◁ ((λ_ K).hom ▷ Z)) := by
    simpa only [MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_id] using
      (MonoidalCategory.associator_naturality
        (𝟙 Pp) (λ_ K).hom (𝟙 Z))
  rw [hPairingOneWhisker]
  have hAssocNatPost := congrArg
    (fun k => k ≫ (Pp ◁ unitPrefixRaw)) hAssocNat
  calc
    _ = (((Pp ◁ (λ_ K).hom) ▷ Z) ≫ (α_ Pp K Z).hom) ≫
        (Pp ◁ unitPrefixRaw) := (Category.assoc _ _ _).symm
    _ = ((α_ Pp (𝟙_ C ⊗ K) Z).hom ≫
        (Pp ◁ ((λ_ K).hom ▷ Z))) ≫
        (Pp ◁ unitPrefixRaw) := hAssocNatPost
    _ = (α_ Pp (𝟙_ C ⊗ K) Z).hom ≫
        ((Pp ◁ ((λ_ K).hom ▷ Z)) ≫
          (Pp ◁ unitPrefixRaw)) := Category.assoc _ _ _
    _ = _ := by
      simp only [unitPrefixRaw, ← MonoidalCategory.whiskerLeft_comp]
      rw [MonoidalCategory.tensorHom_id]
      rw [← MonoidalCategory.comp_whiskerRight, Iso.hom_inv_id,
        MonoidalCategory.id_whiskerRight, MonoidalCategory.whiskerLeft_id,
        Category.comp_id]

end

end ModuleReconstruction

variable
  [∀ (F G : Sequence.Index ⥤ C),
    (tensor Sequence.Index).HasPointwiseLeftKanExtension (F ⊠ G)]
  [(Functor.fromPUnit.{0} (𝟙_ Sequence.Index)).HasPointwiseLeftKanExtension
    (Functor.fromPUnit.{0} (𝟙_ C))]
  [∀ (W : C) (d : Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow (tensor Sequence.Index) d) (tensorLeft W)]
  [∀ (W : C) (d : Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow (tensor Sequence.Index) d) (tensorRight W)]
  [∀ (W : C) (d : Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow
        (Functor.fromPUnit.{0} (𝟙_ Sequence.Index)) d) (tensorLeft W)]
  [∀ (W : C) (d : Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow
        (Functor.fromPUnit.{0} (𝟙_ Sequence.Index)) d) (tensorRight W)]
  [∀ (W : C) (d : Sequence.Index × Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow
        ((𝟭 Sequence.Index).prod
          (Functor.fromPUnit.{0} (𝟙_ Sequence.Index))) d)
      (tensorRight W)]
  [∀ (W : C) (d : Sequence.Index × Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow
        ((tensor Sequence.Index).prod (𝟭 Sequence.Index)) d)
      (tensorRight W)]

attribute [local instance] Sequence.tensorPowerSequenceMonObj

public section


namespace ModuleReconstruction

variable {K : C}

@[expose] public section

/-- The actual Day action obtained by descending the ordered structure maps. -/
noncomputable def spectrumAction
    (X : SequentialSpectrum C K) :
    Sequence.tensorPowerSequence K ⊗ spectrumSequence X ⟶
      spectrumSequence X :=
  DayFunctor.tensorDesc (spectrumActionDesc X)

/-- The descended Day action commutes with every original levelwise sequence map. -/
theorem spectrumAction_naturality
    {X Y : SequentialSpectrum C K} (f : X ⟶ Y) :
    spectrumAction X ≫ spectrumSequenceMap f =
      MonoidalLeftActionStruct.actionHomRight
          (Sequence.tensorPowerSequence K) (spectrumSequenceMap f) ≫
        spectrumAction Y := by
  apply DayFunctor.tensor_hom_ext
  intro i j
  simp only [DayFunctor.comp_natTrans, NatTrans.comp_app, spectrumAction]
  rw [← Category.assoc, DayFunctor.η_comp_tensorDesc_app]
  have hη :
      (DayFunctor.η (Sequence.tensorPowerSequence K)
          (spectrumSequence X)).app (i, j) ≫
          (MonoidalLeftActionStruct.actionHomRight
            (Sequence.tensorPowerSequence K)
            (spectrumSequenceMap f)).natTrans.app (i ⊗ j) =
        ((Sequence.tensorPowerSequence K).functor.obj i ◁
            (spectrumSequenceMap f).natTrans.app j) ≫
          (DayFunctor.η (Sequence.tensorPowerSequence K)
            (spectrumSequence Y)).app (i, j) := by
    have h :=
      convolutionExtensionUnit_comp_ι_map_whiskerLeft_app
        C (Sequence.tensorPowerSequence K) (spectrumSequenceMap f) i j
    convert h using 1 <;> rfl
  rw [← Category.assoc, hη, Category.assoc,
    DayFunctor.η_comp_tensorDesc_app]
  exact spectrumActionDesc_map f i j

/-- The Day tensor-power unit acts through the original left unitor. -/
theorem spectrumAction_one_smul
    (X : SequentialSpectrum C K) :
    ((Sequence.tensorPowerSequenceMonObj K).one ▷ spectrumSequence X) ≫
        spectrumAction X =
      (λ_ (spectrumSequence X)).hom := by
  apply DayFunctor.hom_ext
  apply Functor.hom_ext_of_isLeftKanExtension
    (F' := (𝟙_ (Sequence C) ⊗ spectrumSequence X).functor)
    (α := DayFunctor.η (𝟙_ (Sequence C)) (spectrumSequence X))
  let _ : ((𝟙_ (Sequence C)).functor ⊠
        (spectrumSequence X).functor).IsLeftKanExtension
      (ExternalProduct.extensionUnitLeft
        (𝟙_ (Sequence C)).functor
        (DayFunctor.νNatTrans Sequence.Index C)
        (spectrumSequence X).functor) :=
    ExternalProduct.isPointwiseLeftKanExtensionExtensionUnitLeft
      (𝟙_ (Sequence C)).functor
      (DayFunctor.νNatTrans Sequence.Index C)
      (spectrumSequence X).functor
      (isPointwiseLeftKanExtensionUnitUnit
        Sequence.Index C (Sequence C)) |>.isLeftKanExtension
  apply Functor.hom_ext_of_isLeftKanExtension
    (F' := (𝟙_ (Sequence C)).functor ⊠
      (spectrumSequence X).functor)
    (α := ExternalProduct.extensionUnitLeft
      (𝟙_ (Sequence C)).functor
      (DayFunctor.νNatTrans Sequence.Index C)
      (spectrumSequence X).functor)
  ext ⟨u, y⟩
  rcases u with ⟨u⟩
  rcases u with ⟨⟩
  dsimp [ExternalProduct.extensionUnitLeft, DayFunctor.νNatTrans]
  simp only [MonoidalCategory.whiskerLeft_id, Category.comp_id]
  have hwhisker :
      (DayFunctor.η (𝟙_ (Sequence C))
            (spectrumSequence X)).app (Sequence.index 0, y) ≫
        ((Sequence.tensorPowerSequenceMonObj K).one ▷
            spectrumSequence X).natTrans.app
          (Sequence.index 0 ⊗ y) =
      (Sequence.tensorPowerSequenceMonObj K).one.natTrans.app
            (Sequence.index 0) ▷
            (spectrumSequence X).functor.obj y ≫
        (DayFunctor.η (Sequence.tensorPowerSequence K)
            (spectrumSequence X)).app (Sequence.index 0, y) := by
    exact convolutionExtensionUnit_comp_ι_map_whiskerRight_app
      Sequence.Index C (Sequence.tensorPowerSequenceMonObj K).one
      (spectrumSequence X) (Sequence.index 0) y
  slice_lhs 2 3 =>
    rw [hwhisker]
  simp only [Category.assoc, spectrumAction]
  slice_lhs 3 4 =>
    rw [DayFunctor.η_comp_tensorDesc_app]
  have hcomp :
      (DayFunctor.ν Sequence.Index C ▷
            (spectrumSequence X).functor.obj y) ≫
          ((Sequence.tensorPowerSequenceMonObj K).one.natTrans.app
              (Sequence.index 0) ▷
            (spectrumSequence X).functor.obj y) =
        (DayFunctor.ν Sequence.Index C ≫
            (Sequence.tensorPowerSequenceMonObj K).one.natTrans.app
              (Sequence.index 0)) ▷
          (spectrumSequence X).functor.obj y :=
    (MonoidalCategory.comp_whiskerRight _ _ _).symm
  have hScalarUnit :
      DayFunctor.ν Sequence.Index C ≫
          (Sequence.tensorPowerSequenceMonObj K).one.natTrans.app
            (Sequence.index 0) =
        TensorPower.laxTensorPowerUnit (𝟭 C) K := by
    exact Sequence.tensorPowerSequenceOne_ν K
  have hScalarUnitTyped :
      DayFunctor.ν Sequence.Index C ≫
          (Sequence.tensorPowerSequenceMonObj K).one.natTrans.app
            (Sequence.index 0) =
        𝟙 (TensorPower.tensorPowObj K 0) := by
    rw [hScalarUnit]
    rfl
  have hfacWhisker := hcomp.trans (congrArg
    (fun f => f ▷ (spectrumSequence X).functor.obj y) hScalarUnitTyped)
  slice_lhs 1 2 =>
    exact hfacWhisker
  have hleft :
      DayFunctor.ν Sequence.Index C ▷
            (spectrumSequence X).functor.obj y ≫
          (DayFunctor.η (𝟙_ (Sequence C))
            (spectrumSequence X)).app (Sequence.index 0, y) ≫
          (λ_ (spectrumSequence X)).hom.natTrans.app
              (Sequence.index 0 ⊗ y) =
        (λ_ ((spectrumSequence X).functor.obj y)).hom ≫
          (spectrumSequence X).functor.map (λ_ y).inv := by
    exact leftUnitor_hom_unit_app C (spectrumSequence X) y
  slice_rhs 1 3 =>
    exact hleft
  rcases y with ⟨n⟩
  simp only [spectrumActionDesc, Sequence.degree_index]
  rw [iteratedStructureMap_zero]
  simp only [TensorPower.tensorPowObj_zero]
  let hZero : n.toAdd = 0 + n.toAdd := (Nat.zero_add n.toAdd).symm
  let hDegree : 0 + n.toAdd =
      Sequence.degree (Sequence.index 0 ⊗ (⟨n⟩ : Sequence.Index)) :=
    degree_tensor (Sequence.index 0) (⟨n⟩ : Sequence.Index)
  let hUnitor : n.toAdd =
      Sequence.degree (Sequence.index 0 ⊗ (⟨n⟩ : Sequence.Index)) :=
    congrArg Sequence.degree
      (Discrete.ext
        (Discrete.eq_of_hom (λ_ (⟨n⟩ : Sequence.Index)).inv))
  change
    (𝟙 (𝟙_ C) ▷ X.level n.toAdd) ≫
        ((λ_ (X.level n.toAdd)).hom ≫
          eqToHom (congrArg X.level hZero)) ≫
        eqToHom (congrArg X.level hDegree) =
      (λ_ (X.level n.toAdd)).hom ≫
        eqToHom (congrArg X.level hUnitor)
  rw [MonoidalCategory.id_whiskerRight, Category.id_comp]
  simp only [Category.assoc]
  apply (cancel_epi (λ_ (X.level n.toAdd)).hom).2
  rw [eqToHom_trans]

/-- The tensor-power Day multiplication generator before its canonical degree transport. -/
private theorem tensorPowerSequenceMul_fac (p r : ℕ) :
    (DayFunctor.η (Sequence.tensorPowerSequence K)
        (Sequence.tensorPowerSequence K)).app
          (Sequence.index p, Sequence.index r) ≫
        (Sequence.tensorPowerSequenceMonObj K).mul.natTrans.app
          (Sequence.index p ⊗ Sequence.index r) =
      TensorPower.laxTensorPowerPairing (𝟭 C) K p r := by
  have h := Sequence.tensorPowerSequenceMul_η K p r
  rw [← Category.assoc, eqToHom_map] at h
  apply eq_of_heq
  exact (comp_eqToHom_heq _ _).symm.trans (heq_of_eq h)

/-- The actual Day generator followed by the descended action is the action descent. -/
theorem spectrumAction_fac
    (X : SequentialSpectrum C K) (i j : Sequence.Index) :
    (DayFunctor.η (Sequence.tensorPowerSequence K)
        (spectrumSequence X)).app (i, j) ≫
        (spectrumAction X).natTrans.app (i ⊗ j) =
      (spectrumActionDesc X).app (i, j) := by
  unfold spectrumAction
  exact DayFunctor.η_comp_tensorDesc_app (spectrumActionDesc X) i j

/-- The additive law for iterated structure maps gives the full Day module associativity law. -/
theorem spectrumAction_mul_smul
    (X : SequentialSpectrum C K)
    (hAdd : ∀ (p r q : ℕ),
      (TensorPower.laxTensorPowerPairing (𝟭 C) K p r ⊗ₘ
          𝟙 (X.level q)) ≫
          iteratedStructureMap X (p + r) q ≫
          eqToHom (congrArg X.level (Nat.add_assoc p r q)) =
        (α_ (TensorPower.tensorPowObj K p)
          (TensorPower.tensorPowObj K r) (X.level q)).hom ≫
          (𝟙 _ ⊗ₘ iteratedStructureMap X r q) ≫
          iteratedStructureMap X p (r + q)) :
    ((Sequence.tensorPowerSequenceMonObj K).mul ▷
        spectrumSequence X) ≫ spectrumAction X =
      (α_ (Sequence.tensorPowerSequence K)
        (Sequence.tensorPowerSequence K) (spectrumSequence X)).hom ≫
        (Sequence.tensorPowerSequence K ◁ spectrumAction X) ≫
        spectrumAction X := by
  apply DayFunctor.hom_ext
  apply Functor.hom_ext_of_isLeftKanExtension
    (F' := ((Sequence.tensorPowerSequence K ⊗
      Sequence.tensorPowerSequence K) ⊗ spectrumSequence X).functor)
    (α := DayFunctor.η
      (Sequence.tensorPowerSequence K ⊗
        Sequence.tensorPowerSequence K) (spectrumSequence X))
  let _ : ((Sequence.tensorPowerSequence K ⊗
          Sequence.tensorPowerSequence K).functor ⊠
        (spectrumSequence X).functor).IsLeftKanExtension
      (ExternalProduct.extensionUnitLeft
        (Sequence.tensorPowerSequence K ⊗
          Sequence.tensorPowerSequence K).functor
        (DayFunctor.η (Sequence.tensorPowerSequence K)
          (Sequence.tensorPowerSequence K))
        (spectrumSequence X).functor) :=
    ExternalProduct.isPointwiseLeftKanExtensionExtensionUnitLeft
      (Sequence.tensorPowerSequence K ⊗
        Sequence.tensorPowerSequence K).functor
      (DayFunctor.η (Sequence.tensorPowerSequence K)
        (Sequence.tensorPowerSequence K))
      (spectrumSequence X).functor
      (isPointwiseLeftKanExtensionConvolutionExtensionUnit
        (Sequence.tensorPowerSequence K)
        (Sequence.tensorPowerSequence K)) |>.isLeftKanExtension
  apply Functor.hom_ext_of_isLeftKanExtension
    (F' := (Sequence.tensorPowerSequence K ⊗
      Sequence.tensorPowerSequence K).functor ⊠
      (spectrumSequence X).functor)
    (α := ExternalProduct.extensionUnitLeft
      (Sequence.tensorPowerSequence K ⊗
        Sequence.tensorPowerSequence K).functor
      (DayFunctor.η (Sequence.tensorPowerSequence K)
        (Sequence.tensorPowerSequence K))
      (spectrumSequence X).functor)
  ext ⟨⟨i, j⟩, k⟩
  dsimp [ExternalProduct.extensionUnitLeft]
  simp only [MonoidalCategory.whiskerLeft_id, Category.comp_id]
  have hrightWhisker :
      (DayFunctor.η
          (Sequence.tensorPowerSequence K ⊗
            Sequence.tensorPowerSequence K)
          (spectrumSequence X)).app (i ⊗ j, k) ≫
        ((Sequence.tensorPowerSequenceMonObj K).mul ▷
            spectrumSequence X).natTrans.app ((i ⊗ j) ⊗ k) =
      (Sequence.tensorPowerSequenceMonObj K).mul.natTrans.app
            (i ⊗ j) ▷ (spectrumSequence X).functor.obj k ≫
        (DayFunctor.η (Sequence.tensorPowerSequence K)
          (spectrumSequence X)).app (i ⊗ j, k) := by
    exact convolutionExtensionUnit_comp_ι_map_whiskerRight_app
      Sequence.Index C (Sequence.tensorPowerSequenceMonObj K).mul
      (spectrumSequence X) (i ⊗ j) k
  slice_lhs 2 3 =>
    rw [hrightWhisker]
  simp only [Category.assoc]
  slice_lhs 3 4 =>
    rw [spectrumAction_fac X (i ⊗ j) k]
  have hassoc :
      (DayFunctor.η (Sequence.tensorPowerSequence K)
            (Sequence.tensorPowerSequence K)).app (i, j) ▷
            (spectrumSequence X).functor.obj k ≫
          (DayFunctor.η
            (Sequence.tensorPowerSequence K ⊗
              Sequence.tensorPowerSequence K)
            (spectrumSequence X)).app (i ⊗ j, k) ≫
          (α_ (Sequence.tensorPowerSequence K)
            (Sequence.tensorPowerSequence K)
            (spectrumSequence X)).hom.natTrans.app ((i ⊗ j) ⊗ k) =
        (α_ ((Sequence.tensorPowerSequence K).functor.obj i)
          ((Sequence.tensorPowerSequence K).functor.obj j)
          ((spectrumSequence X).functor.obj k)).hom ≫
          ((Sequence.tensorPowerSequence K).functor.obj i ◁
            (DayFunctor.η (Sequence.tensorPowerSequence K)
              (spectrumSequence X)).app (j, k)) ≫
          (DayFunctor.η (Sequence.tensorPowerSequence K)
            (Sequence.tensorPowerSequence K ⊗
              spectrumSequence X)).app (i, j ⊗ k) ≫
          (Sequence.tensorPowerSequence K ⊗
            (Sequence.tensorPowerSequence K ⊗
              spectrumSequence X)).functor.map (α_ i j k).inv := by
    exact associator_hom_unit_unit C
      (Sequence.tensorPowerSequence K)
      (Sequence.tensorPowerSequence K) (spectrumSequence X) i j k
  slice_rhs 1 3 =>
    rw [hassoc]
  simp only [Category.assoc, NatTrans.naturality_assoc]
  rw [(spectrumAction X).natTrans.naturality]
  have hleftWhisker :
      (DayFunctor.η (Sequence.tensorPowerSequence K)
            (Sequence.tensorPowerSequence K ⊗
              spectrumSequence X)).app (i, j ⊗ k) ≫
        (Sequence.tensorPowerSequence K ◁
            spectrumAction X).natTrans.app
          ((tensor Sequence.Index).obj (i, j ⊗ k)) =
      (Sequence.tensorPowerSequence K).functor.obj i ◁
            (spectrumAction X).natTrans.app (j ⊗ k) ≫
        (DayFunctor.η (Sequence.tensorPowerSequence K)
          (spectrumSequence X)).app (i, j ⊗ k) := by
    exact convolutionExtensionUnit_comp_ι_map_whiskerLeft_app
      C (Sequence.tensorPowerSequence K) (spectrumAction X) i (j ⊗ k)
  slice_rhs 3 4 =>
    rw [hleftWhisker]
  simp only [Category.assoc]
  slice_rhs 2 3 =>
    rw [← MonoidalCategory.whiskerLeft_comp,
      spectrumAction_fac X j k]
  have hOuterAction :
      (DayFunctor.η (Sequence.tensorPowerSequence K)
          (spectrumSequence X)).app (i, j ⊗ k) ≫
        (spectrumAction X).natTrans.app
          ((tensor Sequence.Index).obj (i, j ⊗ k)) =
      (spectrumActionDesc X).app (i, j ⊗ k) := by
    exact spectrumAction_fac X i (j ⊗ k)
  slice_rhs 3 4 =>
    rw [hOuterAction]
  rcases i with ⟨p⟩
  rcases j with ⟨r⟩
  rcases k with ⟨q⟩
  have hMulRaw :
      (DayFunctor.η (Sequence.tensorPowerSequence K)
          (Sequence.tensorPowerSequence K)).app
            ((⟨p⟩ : Sequence.Index), (⟨r⟩ : Sequence.Index)) ≫
          (Sequence.tensorPowerSequenceMonObj K).mul.natTrans.app
            ((⟨p⟩ : Sequence.Index) ⊗ (⟨r⟩ : Sequence.Index)) =
        TensorPower.laxTensorPowerPairing
          (𝟭 C) K p.toAdd r.toAdd := by
    convert tensorPowerSequenceMul_fac p.toAdd r.toAdd using 1
    all_goals rfl
  have hMulWhisker := congrArg
    (fun f => f ▷
      (spectrumSequence X).functor.obj (⟨q⟩ : Sequence.Index)) hMulRaw
  slice_lhs 1 2 =>
    rw [← MonoidalCategory.comp_whiskerRight, hMulWhisker]
  have hDescLeft :
      (spectrumActionDesc X).app
          ((⟨p⟩ : Sequence.Index) ⊗ (⟨r⟩ : Sequence.Index),
            (⟨q⟩ : Sequence.Index)) =
        iteratedStructureMap X (p.toAdd + r.toAdd) q.toAdd := by
    convert spectrumActionDesc_tensor_index
      X p.toAdd r.toAdd q.toAdd using 1
    all_goals rfl
  have hDescInner :
      (spectrumActionDesc X).app
          ((⟨r⟩ : Sequence.Index), (⟨q⟩ : Sequence.Index)) =
        iteratedStructureMap X r.toAdd q.toAdd := by
    convert spectrumActionDesc_index X r.toAdd q.toAdd using 1
    all_goals rfl
  have hDescOuter :
      (spectrumActionDesc X).app
          ((⟨p⟩ : Sequence.Index),
            (⟨r⟩ : Sequence.Index) ⊗ (⟨q⟩ : Sequence.Index)) =
        iteratedStructureMap X p.toAdd (r.toAdd + q.toAdd) := by
    convert spectrumActionDesc_index_tensor
      X p.toAdd r.toAdd q.toAdd using 1
    all_goals rfl
  rw [hDescLeft, hDescInner, hDescOuter]
  change ℕ at p
  change ℕ at r
  change ℕ at q
  change
    (TensorPower.laxTensorPowerPairing (𝟭 C) K p r ▷ X.level q) ≫
        iteratedStructureMap X (p + r) q =
      (α_ (TensorPower.tensorPowObj K p)
        (TensorPower.tensorPowObj K r) (X.level q)).hom ≫
        (TensorPower.tensorPowObj K p ◁
          iteratedStructureMap X r q) ≫
        iteratedStructureMap X p (r + q) ≫
        (spectrumSequence X).functor.map
          (α_ (Sequence.index p) (Sequence.index r)
            (Sequence.index q)).inv
  have hmap :
      (spectrumSequence X).functor.map
          (α_ (Sequence.index p) (Sequence.index r)
            (Sequence.index q)).inv =
        eqToHom (congrArg X.level
          (Nat.add_assoc p r q).symm) := by
    rfl
  have hpost :
      iteratedStructureMap X p (r + q) ≫
          (spectrumSequence X).functor.map
            (α_ (Sequence.index p) (Sequence.index r)
              (Sequence.index q)).inv =
        iteratedStructureMap X p (r + q) ≫
          eqToHom (congrArg X.level
            (Nat.add_assoc p r q).symm) := by
    exact congrArg (fun g => iteratedStructureMap X p (r + q) ≫ g) hmap
  slice_rhs 3 4 =>
    exact hpost
  let e : X.level ((p + r) + q) ≅ X.level (p + (r + q)) :=
    eqToIso (congrArg X.level (Nat.add_assoc p r q))
  have he :
      eqToHom (congrArg X.level (Nat.add_assoc p r q).symm) = e.inv := by
    rfl
  rw [he]
  have hgoal :
      ((TensorPower.laxTensorPowerPairing (𝟭 C) K p r ▷
            X.level q) ≫ iteratedStructureMap X (p + r) q) ≫ e.hom =
        (α_ (TensorPower.tensorPowObj K p)
          (TensorPower.tensorPowObj K r) (X.level q)).hom ≫
          (TensorPower.tensorPowObj K p ◁
            iteratedStructureMap X r q) ≫
          iteratedStructureMap X p (r + q) := by
    simpa [e, MonoidalCategory.tensorHom_def] using hAdd p r q
  have hfinal := (Iso.eq_comp_inv e).2 hgoal
  calc
    _ = ((α_ (TensorPower.tensorPowObj K p)
          (TensorPower.tensorPowObj K r) (X.level q)).hom ≫
        (TensorPower.tensorPowObj K p ◁
          iteratedStructureMap X r q) ≫
        iteratedStructureMap X p (r + q)) ≫ e.inv := hfinal
    _ = _ := by
      simp only [Category.assoc]
      apply eq_of_heq
      rfl

/-- The tensor-power module with the original level sequence and its descended action. -/
noncomputable def spectrumModule
    (X : SequentialSpectrum C K) : Sequence.TensorPowerModule K := {
  X := spectrumSequence X
  mod :=
    { smul := spectrumAction X
      one_smul := spectrumAction_one_smul X
      mul_smul := spectrumAction_mul_smul X (iteratedStructureMap_add X) } }

/-- The module morphism given by the original levelwise maps and action naturality. -/
noncomputable def spectrumModuleMap
    {X Y : SequentialSpectrum C K} (f : X ⟶ Y) :
    spectrumModule X ⟶ spectrumModule Y :=
  CategoryTheory.Mod.Hom.mk' (spectrumSequenceMap f) (by
    change spectrumAction X ≫ spectrumSequenceMap f =
      MonoidalLeftActionStruct.actionHomRight
          (Sequence.tensorPowerSequence K) (spectrumSequenceMap f) ≫
        spectrumAction Y
    exact spectrumAction_naturality f)

end

end ModuleReconstruction

/-- The functor sending a sequential spectrum to its tensor-power module. -/
@[expose]
noncomputable def toTensorPowerModule (K : C) :
    SequentialSpectrum C K ⥤ Sequence.TensorPowerModule K where
  obj X := ModuleReconstruction.spectrumModule X
  map f := ModuleReconstruction.spectrumModuleMap f
  map_id X := by
    apply CategoryTheory.Mod.hom_ext
    apply DayFunctor.hom_ext
    apply NatTrans.ext
    funext i
    rfl
  map_comp f g := by
    apply CategoryTheory.Mod.hom_ext
    apply DayFunctor.hom_ext
    apply NatTrans.ext
    funext i
    rfl

/-- The converted module action on the canonical `(p, q)` Day generator is
the `p`-fold structure map. -/
theorem toTensorPowerModule_smul_η
    (K : C) (X : SequentialSpectrum C K) (p q : ℕ) :
    (DayFunctor.η (Sequence.tensorPowerSequence K)
          ((toTensorPowerModule K).obj X).X).app
        (Sequence.index p, Sequence.index q) ≫
      ((toTensorPowerModule K).obj X).mod.smul.natTrans.app
        (Sequence.index p ⊗ Sequence.index q) ≫
      ((toTensorPowerModule K).obj X).X.functor.map
        (eqToHom (Sequence.tensorObj_index p q)) =
      iteratedStructureMap X p q := by
  have hη :
    (DayFunctor.η (Sequence.tensorPowerSequence K)
          ((toTensorPowerModule K).obj X).X).app
        (Sequence.index p, Sequence.index q) ≫
      ((toTensorPowerModule K).obj X).mod.smul.natTrans.app
        (Sequence.index p ⊗ Sequence.index q) =
      iteratedStructureMap X p q := by
    change
      (DayFunctor.η (Sequence.tensorPowerSequence K)
          (ModuleReconstruction.spectrumSequence X)).app
          (Sequence.index p, Sequence.index q) ≫
        (ModuleReconstruction.spectrumAction X).natTrans.app
          (Sequence.index p ⊗ Sequence.index q) =
        iteratedStructureMap X p q
    rw [ModuleReconstruction.spectrumAction_fac,
      ModuleReconstruction.spectrumActionDesc_index]
  rw [← Category.assoc, eqToHom_map]
  apply eq_of_heq
  exact (comp_eqToHom_heq (C := C) _ _).trans (heq_of_eq hη)

/-- The functor recovering a sequential spectrum from a tensor-power module. -/
@[expose]
noncomputable def fromTensorPowerModule (K : C) :
    Sequence.TensorPowerModule K ⥤ SequentialSpectrum C K := by
  let moduleSpectrum
      (M : Sequence.TensorPowerModule K) : SequentialSpectrum C K := {
    level n := M.X.functor.obj (Sequence.index n)
    structureMap n := Sequence.TensorPowerModule.structureMap M n }
  let moduleSpectrumMap
      {M N : Sequence.TensorPowerModule K} (f : M ⟶ N) :
      moduleSpectrum M ⟶ moduleSpectrum N := {
    levelMap n := f.hom.natTrans.app (Sequence.index n)
    naturality n := by
      change (K ◁ f.hom.natTrans.app (Sequence.index n)) ≫
          Sequence.TensorPowerModule.structureMap N n =
        Sequence.TensorPowerModule.structureMap M n ≫
          f.hom.natTrans.app (Sequence.index (n + 1))
      simpa only [MonoidalCategory.id_tensorHom] using
        (Sequence.TensorPowerModule.structureMap_naturality f n).symm }
  let fromModule :
      Sequence.TensorPowerModule K ⥤ SequentialSpectrum C K := {
    obj M := moduleSpectrum M
    map f := moduleSpectrumMap f
    map_id M := by
      apply SequentialSpectrum.hom_ext
      intro n
      change ((𝟙 M : M ⟶ M).hom.natTrans.app (Sequence.index n)) = 𝟙 _
      simp
    map_comp f g := by
      apply SequentialSpectrum.hom_ext
      intro n
      change (f ≫ g).hom.natTrans.app (Sequence.index n) =
        f.hom.natTrans.app (Sequence.index n) ≫
          g.hom.natTrans.app (Sequence.index n)
      simp }
  exact fromModule

/-- The natural isomorphism from each sequential spectrum to the spectrum
recovered from its tensor-power module. -/
noncomputable def tensorPowerModuleUnitIso (K : C) :
    𝟭 (SequentialSpectrum C K) ≅
      toTensorPowerModule K ⋙ fromTensorPowerModule K := by
  let toModule := toTensorPowerModule K
  let fromModule := fromTensorPowerModule K
  let spectrumModule (X : SequentialSpectrum C K) :
      Sequence.TensorPowerModule K := toModule.obj X
  let moduleSpectrum (M : Sequence.TensorPowerModule K) :
      SequentialSpectrum C K := fromModule.obj M
  let spectrumSequence (X : SequentialSpectrum C K) : Sequence C :=
    (spectrumModule X).X
  let spectrumAction (X : SequentialSpectrum C K) :
      Sequence.tensorPowerSequence K ⊗ spectrumSequence X ⟶
        spectrumSequence X :=
    (spectrumModule X).mod.smul
  let degree_tensor (i j : Sequence.Index) :
      Sequence.degree i + Sequence.degree j =
        Sequence.degree (i ⊗ j) := by
    cases i
    cases j
    rfl
  let spectrumActionDesc
      (X : SequentialSpectrum C K) :
      (Sequence.tensorPowerSequence K).functor ⊠
          (spectrumSequence X).functor ⟶
        tensor Sequence.Index ⋙ (spectrumSequence X).functor := {
    app i := iteratedStructureMap X
        (Sequence.degree i.1) (Sequence.degree i.2) ≫
      eqToHom (congrArg X.level (degree_tensor i.1 i.2))
    naturality := by
      rintro ⟨i, j⟩ ⟨i', j'⟩ f
      have h : (i, j) = (i', j') := Prod.ext
        (Discrete.ext (Discrete.eq_of_hom f.1))
        (Discrete.ext (Discrete.eq_of_hom f.2))
      cases h
      rw [show f = 𝟙 _ by ext <;> apply Discrete.hom_eq]
      simp }
  let spectrumActionDesc_index
      (X : SequentialSpectrum C K) (p q : ℕ) :
      (spectrumActionDesc X).app
          (Sequence.index p, Sequence.index q) =
        iteratedStructureMap X p q := by
    change iteratedStructureMap X p q ≫ eqToHom _ = _
    apply eq_of_heq
    exact comp_eqToHom_heq _ _
  have spectrumAction_eq (X : SequentialSpectrum C K) :
      spectrumAction X =
        DayFunctor.tensorDesc (spectrumActionDesc X) := by
    rfl
  let spectrumAction_fac
      (X : SequentialSpectrum C K) (i j : Sequence.Index) :
      (DayFunctor.η (Sequence.tensorPowerSequence K)
          (spectrumSequence X)).app (i, j) ≫
          (spectrumAction X).natTrans.app (i ⊗ j) =
        (spectrumActionDesc X).app (i, j) := by
    rw [spectrumAction_eq]
    exact DayFunctor.η_comp_tensorDesc_app (spectrumActionDesc X) i j
  let spectrumModule_structureMap
      (X : SequentialSpectrum C K) (n : ℕ) :
      Sequence.TensorPowerModule.structureMap (spectrumModule X) n =
        X.structureMap n := by
    rw [Sequence.TensorPowerModule.structureMap_eq]
    have spectrumSequence_map_final :
        (spectrumSequence X).functor.map
            (eqToHom
              ((Sequence.tensorObj_index 1 n).trans
                (congrArg Sequence.index (Nat.one_add n)))) =
          eqToHom (congrArg X.level (Nat.one_add n)) := by
      unfold spectrumSequence
      rw [eqToHom_map]
      change eqToHom _ = eqToHom _
      congr 1
    let preMap : K ⊗ X.level n ⟶
        (((Sequence.tensorPowerSequence K).functor ⊠
          (spectrumSequence X).functor).obj
            (Sequence.index 1, Sequence.index n)) := by
      change K ⊗ X.level n ⟶ (𝟙_ C ⊗ K) ⊗ X.level n
      exact (λ_ K).inv ⊗ₘ 𝟙 (X.level n)
    change preMap ≫
        (DayFunctor.η (Sequence.tensorPowerSequence K)
          (spectrumSequence X)).app
            (Sequence.index 1, Sequence.index n) ≫
        (spectrumAction X).natTrans.app
          (Sequence.index 1 ⊗ Sequence.index n) ≫
        (spectrumSequence X).functor.map
          (eqToHom
            ((Sequence.tensorObj_index 1 n).trans
              (congrArg Sequence.index (Nat.one_add n)))) =
      X.structureMap n
    rw [spectrumAction_eq]
    slice_lhs 2 3 =>
      rw [DayFunctor.η_comp_tensorDesc_app]
    rw [spectrumActionDesc_index, spectrumSequence_map_final]
    change ((λ_ K).inv ⊗ₘ 𝟙 (X.level n)) ≫
        iteratedStructureMap X 1 n ≫
        eqToHom (congrArg X.level (Nat.one_add n)) =
      X.structureMap n
    rw [iteratedStructureMap_succ, iteratedStructureMap_zero]
    have hCore :
        ((λ_ K).inv ⊗ₘ 𝟙 (X.level n)) ≫
            (α_ (𝟙_ C) K (X.level n)).hom ≫
            (𝟙 (𝟙_ C) ⊗ₘ X.structureMap n) ≫
            (λ_ (X.level (n + 1))).hom =
          X.structureMap n := by
      simp only [MonoidalCategory.tensorHom_id,
        MonoidalCategory.id_tensorHom]
      rw [← MonoidalCategory.leftUnitor_tensor_inv_assoc]
      exact (MonoidalCategory.id_whiskerLeft_symm
        (X.structureMap n)).symm
    simp only [TensorPower.tensorPowObj_zero, Category.assoc]
    let tail : X.level (n + 1) ⟶ X.level (n + 1) :=
      eqToHom (congrArg X.level (Nat.zero_add (n + 1)).symm) ≫
        eqToHom (congrArg X.level
          ((Nat.add_succ 0 n).trans (Nat.succ_add 0 n).symm)) ≫
        eqToHom (congrArg X.level (Nat.one_add n))
    have hTailProof :
        (congrArg X.level (Nat.zero_add (n + 1)).symm).trans
            ((congrArg X.level
              ((Nat.add_succ 0 n).trans (Nat.succ_add 0 n).symm)).trans
              (congrArg X.level (Nat.one_add n))) = rfl :=
      Subsingleton.elim _ _
    have hTail : tail = 𝟙 (X.level (n + 1)) := by
      unfold tail
      simp only [eqToHom_trans]
      rw [hTailProof, eqToHom_refl]
    have hCorePost := congrArg (fun z : K ⊗ X.level n ⟶
        X.level (n + 1) => z ≫ tail) hCore
    calc
      _ = X.structureMap n ≫ tail := by
        rw [← hCorePost]
        unfold tail
        simp only [Category.assoc]
      _ = X.structureMap n := by rw [hTail, Category.comp_id]
  let spectrumUnitIsoApp (X : SequentialSpectrum C K) :
      X ≅ (toModule ⋙ fromModule).obj X := by
    let hom : X ⟶ (toModule ⋙ fromModule).obj X :=
      { levelMap := fun n => 𝟙 (X.level n)
        naturality := by
          intro n
          change (K ◁ 𝟙 (X.level n)) ≫
              Sequence.TensorPowerModule.structureMap
                  (spectrumModule X) n =
              X.structureMap n ≫ 𝟙 (X.level (n + 1))
          rw [spectrumModule_structureMap]
          calc
            _ = 𝟙 (K ⊗ X.level n) ≫ X.structureMap n := by
              rw [MonoidalCategory.whiskerLeft_id]
              rfl
            _ = X.structureMap n := Category.id_comp _
            _ = _ := (Category.comp_id _).symm }
    let inv : (toModule ⋙ fromModule).obj X ⟶ X :=
      { levelMap := fun n => 𝟙 (X.level n)
        naturality := by
          intro n
          change (K ◁ 𝟙 (X.level n)) ≫ X.structureMap n =
            Sequence.TensorPowerModule.structureMap
                (spectrumModule X) n ≫
              𝟙 (X.level (n + 1))
          rw [spectrumModule_structureMap]
          calc
            _ = 𝟙 (K ⊗ X.level n) ≫ X.structureMap n := by
              rw [MonoidalCategory.whiskerLeft_id]
            _ = X.structureMap n := Category.id_comp _
            _ = _ := (Category.comp_id _).symm }
    exact
      { hom := hom
        inv := inv
        hom_inv_id := by
          apply SequentialSpectrum.hom_ext
          intro n
          change 𝟙 (X.level n) ≫ 𝟙 (X.level n) = 𝟙 (X.level n)
          simp
        inv_hom_id := by
          apply SequentialSpectrum.hom_ext
          intro n
          change 𝟙 (X.level n) ≫ 𝟙 (X.level n) = 𝟙 (X.level n)
          simp }
  let spectrumUnitIso :
      𝟭 (SequentialSpectrum C K) ≅
        toModule ⋙ fromModule :=
    NatIso.ofComponents spectrumUnitIsoApp (fun f => by
      apply SequentialSpectrum.hom_ext
      intro n
      change f.levelMap n ≫ 𝟙 _ = 𝟙 _ ≫ f.levelMap n
      simp)
  exact spectrumUnitIso

namespace ModuleReconstruction

variable {K : C}

@[expose] public section

/-- The original Day-generator action, with its canonical forward degree transport. -/
noncomputable def originalAction
    (M : Sequence.TensorPowerModule K) (p q : ℕ) :
    TensorPower.tensorPowObj K p ⊗
        M.X.functor.obj (Sequence.index q) ⟶
      M.X.functor.obj (Sequence.index (p + q)) :=
  (DayFunctor.η (Sequence.tensorPowerSequence K) M.X).app
      (Sequence.index p, Sequence.index q) ≫
    M.mod.smul.natTrans.app
      (Sequence.index p ⊗ Sequence.index q) ≫
    M.X.functor.map (eqToHom (Sequence.tensorObj_index p q))

/-- Original Day associativity transports the degree-one generator to the recursive level. -/
theorem originalAction_succ_pairing
    (M : Sequence.TensorPowerModule K) (p q : ℕ) :
    (TensorPower.laxTensorPowerPairing (𝟭 C) K p 1 ▷
        M.X.functor.obj (Sequence.index q)) ≫ originalAction M (p + 1) q =
      ((α_ (TensorPower.tensorPowObj K p) (TensorPower.tensorPowObj K 1)
          (M.X.functor.obj (Sequence.index q))).hom ≫
        (TensorPower.tensorPowObj K p ◁
          (DayFunctor.η (Sequence.tensorPowerSequence K) M.X).app
            (Sequence.index 1, Sequence.index q)) ≫
        (TensorPower.tensorPowObj K p ◁
          M.mod.smul.natTrans.app (Sequence.index 1 ⊗ Sequence.index q)) ≫
        (TensorPower.tensorPowObj K p ◁
          M.X.functor.map (eqToHom ((Sequence.tensorObj_index 1 q).trans
            (congrArg Sequence.index (Nat.one_add q)))))) ≫
        (originalAction M p (q + 1) ≫
          M.X.functor.map (eqToHom (congrArg Sequence.index
            ((Nat.add_succ p q).trans (Nat.succ_add p q).symm)))) := by
  let A := Sequence.tensorPowerSequence K
  let x := Sequence.index p
  let y := Sequence.index 1
  let z := Sequence.index q
  let tauP1 : x ⊗ y = Sequence.index (p + 1) :=
    Sequence.tensorObj_index p 1
  let f : x ⊗ y ⟶ Sequence.index (p + 1) := eqToHom tauP1
  let h : (x ⊗ y) ⊗ z ⟶ Sequence.index (p + 1) ⊗ z :=
    f ▷ z
  let ai : x ⊗ (y ⊗ z) ⟶ (x ⊗ y) ⊗ z :=
    (α_ x y z).inv
  let innerEq : y ⊗ z = Sequence.index (q + 1) :=
    (Sequence.tensorObj_index 1 q).trans
      (congrArg Sequence.index (Nat.one_add q))
  let g : y ⊗ z ⟶ Sequence.index (q + 1) := eqToHom innerEq
  let hg : x ⊗ (y ⊗ z) ⟶ x ⊗ Sequence.index (q + 1) :=
    x ◁ g
  let outerEq : x ⊗ Sequence.index (q + 1) =
      Sequence.index (p + (q + 1)) :=
    Sequence.tensorObj_index p (q + 1)
  let outerMap : x ⊗ Sequence.index (q + 1) ⟶
      Sequence.index (p + (q + 1)) :=
    eqToHom outerEq
  let sigmaNat : p + (q + 1) = (p + 1) + q :=
    (Nat.add_succ p q).trans (Nat.succ_add p q).symm
  let sigma : Sequence.index (p + (q + 1)) ⟶
      Sequence.index ((p + 1) + q) :=
    eqToHom (congrArg Sequence.index sigmaNat)
  let targetEq : Sequence.index (p + 1) ⊗ z =
      Sequence.index ((p + 1) + q) :=
    Sequence.tensorObj_index (p + 1) q
  let targetMap : Sequence.index (p + 1) ⊗ z ⟶
      Sequence.index ((p + 1) + q) :=
    eqToHom targetEq
  have hIndex : ai ≫ h ≫ targetMap =
      hg ≫ outerMap ≫ sigma := by
    apply Subsingleton.elim
  have hMapTail :
      M.X.functor.map ai ≫ M.X.functor.map h ≫
          M.X.functor.map targetMap =
        M.X.functor.map hg ≫ M.X.functor.map outerMap ≫
          M.X.functor.map sigma := by
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg M.X.functor.map hIndex
  let etaOuterSource :=
    (DayFunctor.η A M.X).app (x, y ⊗ z)
  let actionOuterSource :=
    M.mod.smul.natTrans.app (x ⊗ (y ⊗ z))
  let etaOuterTarget :=
    (DayFunctor.η A M.X).app (x, Sequence.index (q + 1))
  let actionOuterTarget :=
    M.mod.smul.natTrans.app (x ⊗ Sequence.index (q + 1))
  have hEtaOuter :
      (A.functor.obj x ◁ M.X.functor.map g) ≫ etaOuterTarget =
        etaOuterSource ≫ (A ⊗ M.X).functor.map hg := by
    simpa [MonoidalCategory.tensorHom_def] using
      (DayFunctor.η A M.X).naturality (Prod.mkHom (𝟙 x) g)
  have hActionOuter :
      (A ⊗ M.X).functor.map hg ≫ actionOuterTarget =
        actionOuterSource ≫ M.X.functor.map hg :=
    M.mod.smul.natTrans.naturality hg
  have hInnerTransport :
      (A.functor.obj x ◁ M.X.functor.map g) ≫
          etaOuterTarget ≫ actionOuterTarget =
        etaOuterSource ≫ actionOuterSource ≫
          M.X.functor.map hg := by
    rw [← Category.assoc, hEtaOuter, Category.assoc, hActionOuter]
  let etaInner := (DayFunctor.η A M.X).app (y, z)
  let actionInner := M.mod.smul.natTrans.app (y ⊗ z)
  let Pp := TensorPower.tensorPowObj K p
  let Mq := M.X.functor.obj z
  have hOuter :
      etaOuterTarget ≫ actionOuterTarget ≫
          M.X.functor.map outerMap =
        originalAction M p (q + 1) := by
    rfl
  have hMulSmul := ModObj.mul_smul_self A M.X
  have hMul := Sequence.tensorPowerSequenceMul_η K p 1
  let generator :
      (A.functor.obj x ⊗ A.functor.obj y) ⊗ M.X.functor.obj z ⟶
        ((A ⊗ A) ⊗ M.X).functor.obj ((x ⊗ y) ⊗ z) :=
    ((DayFunctor.η A A).app (x, y) ▷ M.X.functor.obj z) ≫
      (DayFunctor.η (A ⊗ A) M.X).app (x ⊗ y, z)
  have hAssocRaw := congrArg
    (fun k : ((A ⊗ A) ⊗ M.X ⟶ M.X) =>
      generator ≫ k.natTrans.app ((x ⊗ y) ⊗ z))
    hMulSmul
  let a := (DayFunctor.η A A).app (x, y) ▷ M.X.functor.obj z
  let b := (DayFunctor.η (A ⊗ A) M.X).app (x ⊗ y, z)
  let c := ((Sequence.tensorPowerSequenceMonObj K).mul ▷
    M.X).natTrans.app ((x ⊗ y) ⊗ z)
  let c' := (Sequence.tensorPowerSequenceMonObj K).mul.natTrans.app
    (x ⊗ y) ▷ M.X.functor.obj z
  let eSource := (DayFunctor.η A M.X).app (x ⊗ y, z)
  let dSource := M.mod.smul.natTrans.app ((x ⊗ y) ⊗ z)
  let x1 := Sequence.index (p + 1)
  let eTarget := (DayFunctor.η A M.X).app (x1, z)
  let dTarget := M.mod.smul.natTrans.app (x1 ⊗ z)
  let etaAssocOuter :=
    (DayFunctor.η A (A ⊗ M.X)).app (x, y ⊗ z)
  have hrightWhisker : b ≫ c = c' ≫ eSource := by
    exact convolutionExtensionUnit_comp_ι_map_whiskerRight_app
      Sequence.Index C (Sequence.tensorPowerSequenceMonObj K).mul
      M.X (x ⊗ y) z
  have hassoc :
      a ≫ b ≫
          (α_ A A M.X).hom.natTrans.app ((x ⊗ y) ⊗ z) =
        (α_ (A.functor.obj x) (A.functor.obj y)
          (M.X.functor.obj z)).hom ≫
          (A.functor.obj x ◁
            (DayFunctor.η A M.X).app (y, z)) ≫
          etaAssocOuter ≫
          (A ⊗ (A ⊗ M.X)).functor.map ai := by
    exact associator_hom_unit_unit C A A M.X x y z
  let leftActionL := (A ◁ M.mod.smul).natTrans.app
    ((x ⊗ y) ⊗ z)
  let leftActionR := (A ◁ M.mod.smul).natTrans.app
    (x ⊗ (y ⊗ z))
  have hleftWhisker :
      etaAssocOuter ≫ leftActionR =
        (A.functor.obj x ◁ actionInner) ≫ etaOuterSource := by
    exact convolutionExtensionUnit_comp_ι_map_whiskerLeft_app
      C A M.mod.smul x (y ⊗ z)
  dsimp only [generator] at hAssocRaw
  simp only [DayFunctor.comp_natTrans, NatTrans.comp_app] at hAssocRaw
  simp only [Category.assoc] at hAssocRaw
  have hrightWhiskerPost :
      a ≫ (b ≫ c) ≫ dSource =
        a ≫ (c' ≫ eSource) ≫ dSource :=
    congrArg (fun k => a ≫ k ≫ dSource) hrightWhisker
  have hrightWhiskerBridge :
      a ≫ b ≫ c ≫ dSource =
        a ≫ (b ≫ c) ≫ dSource := by
    exact congrArg (fun k => a ≫ k)
      (Category.assoc b c dSource).symm
  rw [hrightWhiskerBridge, hrightWhiskerPost] at hAssocRaw
  have hEtaScalar :
      (A.functor.map f ▷ M.X.functor.obj z) ≫ eTarget =
        eSource ≫ (A ⊗ M.X).functor.map h := by
    simpa [MonoidalCategory.tensorHom_def] using
      (DayFunctor.η A M.X).naturality (Prod.mkHom f (𝟙 z))
  have hActionScalar :
      (A ⊗ M.X).functor.map h ≫ dTarget =
        dSource ≫ M.X.functor.map h :=
    M.mod.smul.natTrans.naturality h
  have hTransport :
      (A.functor.map f ▷ M.X.functor.obj z) ≫
          eTarget ≫ dTarget =
        eSource ≫ dSource ≫ M.X.functor.map h := by
    rw [← Category.assoc, hEtaScalar, Category.assoc, hActionScalar]
  have hMulWhiskeredRaw := congrArg
    (fun k => k ▷ M.X.functor.obj z) hMul
  have hMulWhiskered :
      a ≫ c' ≫
          (A.functor.map f ▷ M.X.functor.obj z) =
        TensorPower.laxTensorPowerPairing (𝟭 C) K p 1 ▷
          M.X.functor.obj z := by
    dsimp only [A, x, y, z, f, tauP1] at hMulWhiskeredRaw ⊢
    simp only [MonoidalCategory.comp_whiskerRight] at hMulWhiskeredRaw
    apply eq_of_heq
    exact heq_of_eq hMulWhiskeredRaw
  have hTransportApplied :
      (a ≫ c' ≫ eSource ≫ dSource) ≫
          M.X.functor.map h =
        (a ≫ c' ≫
          (A.functor.map f ▷ M.X.functor.obj z)) ≫
          eTarget ≫ dTarget := by
    simpa only [Category.assoc] using congrArg
      (fun k => a ≫ c' ≫ k) hTransport.symm
  have hMulAppliedRaw := congrArg
    (fun k => k ≫ eTarget ≫ dTarget) hMulWhiskered
  have hMulApplied :
      (a ≫ c' ≫
          (A.functor.map f ▷ M.X.functor.obj z)) ≫
          eTarget ≫ dTarget =
        (TensorPower.laxTensorPowerPairing (𝟭 C) K p 1 ▷
          M.X.functor.obj z) ≫ eTarget ≫ dTarget := by
    apply eq_of_heq
    exact heq_of_eq hMulAppliedRaw
  have hCombined := hTransportApplied.trans hMulApplied
  have hAssocPost := congrArg
    (fun k => k ≫ M.X.functor.map h) hAssocRaw
  let assocDay := (α_ A A M.X).hom.natTrans.app
    ((x ⊗ y) ⊗ z)
  let assocObj := (α_ (A.functor.obj x) (A.functor.obj y)
    (M.X.functor.obj z)).hom
  let wxEta := A.functor.obj x ◁ etaInner
  let wxAction := A.functor.obj x ◁ actionInner
  have hPostCanonical :
      (TensorPower.laxTensorPowerPairing (𝟭 C) K p 1 ▷
          M.X.functor.obj z) ≫ eTarget ≫ dTarget =
        (a ≫ b ≫ assocDay ≫ leftActionL ≫ dSource) ≫
          M.X.functor.map h := by
    calc
      _ = (a ≫ c' ≫ eSource ≫ dSource) ≫
          M.X.functor.map h := hCombined.symm
      _ = _ := by
        simpa only [assocDay, leftActionL, Category.assoc] using hAssocPost
  have hassocPost := congrArg
    (fun k => k ≫ leftActionL ≫ dSource ≫
      M.X.functor.map h) hassoc
  have hAssocApplied :
      (a ≫ b ≫ assocDay ≫ leftActionL ≫ dSource) ≫
          M.X.functor.map h =
        (assocObj ≫ wxEta ≫ etaAssocOuter ≫
          (A ⊗ (A ⊗ M.X)).functor.map ai ≫
          leftActionL ≫ dSource) ≫ M.X.functor.map h := by
    dsimp only [assocDay, assocObj, wxEta, leftActionL,
      etaAssocOuter]
    simpa only [Category.assoc] using hassocPost
  have hLeftNat :
      (A ⊗ (A ⊗ M.X)).functor.map ai ≫ leftActionL =
        leftActionR ≫ (A ⊗ M.X).functor.map ai :=
    (A ◁ M.mod.smul).natTrans.naturality ai
  have hOuterNat :
      (A ⊗ M.X).functor.map ai ≫ dSource =
        actionOuterSource ≫ M.X.functor.map ai :=
    M.mod.smul.natTrans.naturality ai
  have hLeftApplied :
      (assocObj ≫ wxEta ≫ etaAssocOuter ≫
          (A ⊗ (A ⊗ M.X)).functor.map ai ≫
        leftActionL ≫ dSource) ≫ M.X.functor.map h =
      (assocObj ≫ wxEta ≫ etaAssocOuter ≫
        leftActionR ≫ (A ⊗ M.X).functor.map ai ≫
        dSource) ≫ M.X.functor.map h := by
    simpa only [Category.assoc] using congrArg
      (fun k => assocObj ≫ wxEta ≫ etaAssocOuter ≫
        k ≫ dSource ≫ M.X.functor.map h) hLeftNat
  have hOuterApplied :
      (assocObj ≫ wxEta ≫ etaAssocOuter ≫
        leftActionR ≫ (A ⊗ M.X).functor.map ai ≫
        dSource) ≫ M.X.functor.map h =
      (assocObj ≫ wxEta ≫ etaAssocOuter ≫
        leftActionR ≫ actionOuterSource ≫
        M.X.functor.map ai) ≫ M.X.functor.map h := by
    simpa only [Category.assoc] using congrArg
      (fun k => assocObj ≫ wxEta ≫ etaAssocOuter ≫
        leftActionR ≫ k ≫ M.X.functor.map h) hOuterNat
  have hLeftWhiskerApplied :
      (assocObj ≫ wxEta ≫ etaAssocOuter ≫
        leftActionR ≫ actionOuterSource ≫
        M.X.functor.map ai) ≫ M.X.functor.map h =
      (assocObj ≫ wxEta ≫ wxAction ≫ etaOuterSource ≫
        actionOuterSource ≫ M.X.functor.map ai) ≫
        M.X.functor.map h := by
    simpa only [Category.assoc] using congrArg
      (fun k => assocObj ≫ wxEta ≫ k ≫
        actionOuterSource ≫ M.X.functor.map ai ≫
        M.X.functor.map h) hleftWhisker
  have hRightNormalized := hAssocApplied.trans
    (hLeftApplied.trans (hOuterApplied.trans hLeftWhiskerApplied))
  have hCanonicalNormalized := hPostCanonical.trans hRightNormalized
  have hOriginalSucc :
      originalAction M (p + 1) q =
        eTarget ≫ dTarget ≫ M.X.functor.map targetMap := by
    rfl
  have hNormalizedPost := congrArg
    (fun k => k ≫ M.X.functor.map targetMap)
    hCanonicalNormalized
  have hOriginalPostBridge :
      ((TensorPower.laxTensorPowerPairing (𝟭 C) K p 1 ▷
          M.X.functor.obj z) ≫ eTarget ≫ dTarget) ≫
          M.X.functor.map targetMap =
        (TensorPower.laxTensorPowerPairing (𝟭 C) K p 1 ▷
          M.X.functor.obj z) ≫ eTarget ≫ dTarget ≫
          M.X.functor.map targetMap := by
    calc
      _ = (TensorPower.laxTensorPowerPairing (𝟭 C) K p 1 ▷
            M.X.functor.obj z) ≫
          ((eTarget ≫ dTarget) ≫ M.X.functor.map targetMap) :=
        Category.assoc _ _ _
      _ = _ := congrArg
        (fun k => (TensorPower.laxTensorPowerPairing
          (𝟭 C) K p 1 ▷ M.X.functor.obj z) ≫ k)
        (Category.assoc eTarget dTarget
          (M.X.functor.map targetMap))
  have hPreStart :
      (TensorPower.laxTensorPowerPairing (𝟭 C) K p 1 ▷
          M.X.functor.obj z) ≫ originalAction M (p + 1) q =
        ((assocObj ≫ wxEta ≫ wxAction ≫ etaOuterSource ≫
          actionOuterSource ≫ M.X.functor.map ai) ≫
          M.X.functor.map h) ≫ M.X.functor.map targetMap := by
    rw [hOriginalSucc]
    calc
      _ = ((TensorPower.laxTensorPowerPairing (𝟭 C) K p 1 ▷
            M.X.functor.obj z) ≫ eTarget ≫ dTarget) ≫
          M.X.functor.map targetMap := hOriginalPostBridge.symm
      _ = _ := hNormalizedPost
  let normalizedPrefix :=
    assocObj ≫ wxEta ≫ wxAction ≫
      etaOuterSource ≫ actionOuterSource
  have hMapApplied :
      ((normalizedPrefix ≫ M.X.functor.map ai) ≫
          M.X.functor.map h) ≫ M.X.functor.map targetMap =
        normalizedPrefix ≫ M.X.functor.map hg ≫
          M.X.functor.map outerMap ≫ M.X.functor.map sigma := by
    simpa only [Category.assoc] using congrArg
      (fun k => normalizedPrefix ≫ k) hMapTail
  let wxMap := A.functor.obj x ◁ M.X.functor.map g
  have hInnerApplied :
      normalizedPrefix ≫ M.X.functor.map hg ≫
          M.X.functor.map outerMap ≫ M.X.functor.map sigma =
        assocObj ≫ wxEta ≫ wxAction ≫ wxMap ≫
          etaOuterTarget ≫ actionOuterTarget ≫
          M.X.functor.map outerMap ≫ M.X.functor.map sigma := by
    simpa only [normalizedPrefix, wxMap, Category.assoc] using congrArg
      (fun k => assocObj ≫ wxEta ≫ wxAction ≫ k ≫
        M.X.functor.map outerMap ≫ M.X.functor.map sigma)
      hInnerTransport.symm
  let outerTail :=
    etaOuterTarget ≫ actionOuterTarget ≫
      M.X.functor.map outerMap ≫ M.X.functor.map sigma
  let outerCore :=
    etaOuterTarget ≫ actionOuterTarget ≫ M.X.functor.map outerMap
  have hOuterCorePost := congrArg
    (fun k => k ≫ M.X.functor.map sigma) hOuter
  have hOuterTailBridge :
      outerCore ≫ M.X.functor.map sigma = outerTail := by
    dsimp only [outerCore, outerTail]
    calc
      _ = etaOuterTarget ≫
          ((actionOuterTarget ≫ M.X.functor.map outerMap) ≫
            M.X.functor.map sigma) := Category.assoc _ _ _
      _ = _ := congrArg (fun k => etaOuterTarget ≫ k)
        (Category.assoc actionOuterTarget
          (M.X.functor.map outerMap) (M.X.functor.map sigma))
  have hOuterTail :
      outerTail = originalAction M p (q + 1) ≫
        M.X.functor.map sigma :=
    hOuterTailBridge.symm.trans hOuterCorePost
  let innerPrefix := assocObj ≫ wxEta ≫ wxAction ≫ wxMap
  have hInnerOuterBridge :
      innerPrefix ≫ outerTail =
        assocObj ≫ wxEta ≫ wxAction ≫ wxMap ≫
          etaOuterTarget ≫ actionOuterTarget ≫
          M.X.functor.map outerMap ≫ M.X.functor.map sigma := by
    dsimp only [innerPrefix, outerTail]
    simp only [Category.assoc]
  have hNormalizedTransportBridge :
      ((normalizedPrefix ≫ M.X.functor.map ai) ≫
          M.X.functor.map h) ≫ M.X.functor.map targetMap =
        ((assocObj ≫ wxEta ≫ wxAction ≫ etaOuterSource ≫
          actionOuterSource ≫ M.X.functor.map ai) ≫
          M.X.functor.map h) ≫ M.X.functor.map targetMap := by
    dsimp only [normalizedPrefix]
    simp only [Category.assoc]
  have hPrecomposed := hPreStart.trans
    (hNormalizedTransportBridge.symm.trans
      (hMapApplied.trans (hInnerApplied.trans hInnerOuterBridge.symm)))
  have hFinal := hPrecomposed.trans
    (congrArg (fun k => innerPrefix ≫ k) hOuterTail)
  change _ = innerPrefix ≫
    (originalAction M p (q + 1) ≫ M.X.functor.map sigma)
  exact hFinal

/-- The original Day action at a successor degree obeys the structure-map recursion. -/
theorem originalAction_succ (M : Sequence.TensorPowerModule K) (p q : ℕ) :
    originalAction M (p + 1) q =
      (α_ (TensorPower.tensorPowObj K p) K
        (M.X.functor.obj (Sequence.index q))).hom ≫
        (𝟙 _ ⊗ₘ Sequence.TensorPowerModule.structureMap M q) ≫
        originalAction M p (q + 1) ≫
        M.X.functor.map
          (eqToHom (congrArg Sequence.index
            ((Nat.add_succ p q).trans
              (Nat.succ_add p q).symm))) := by
  let A := Sequence.tensorPowerSequence K
  let y := Sequence.index 1
  let z := Sequence.index q
  let innerEq : y ⊗ z = Sequence.index (q + 1) :=
    (Sequence.tensorObj_index 1 q).trans
      (congrArg Sequence.index (Nat.one_add q))
  let g : y ⊗ z ⟶ Sequence.index (q + 1) := eqToHom innerEq
  let actionInner := M.mod.smul.natTrans.app (y ⊗ z)
  let Pp := TensorPower.tensorPowObj K p
  let Mq := M.X.functor.obj z
  let unitPrefixRaw : K ⊗ Mq ⟶ (𝟙_ C ⊗ K) ⊗ Mq :=
    (λ_ K).inv ⊗ₘ 𝟙 Mq
  let etaInnerRaw :
      (𝟙_ C ⊗ K) ⊗ Mq ⟶
        (tensor Sequence.Index ⋙ (A ⊗ M.X).functor).obj (y, z) :=
    (DayFunctor.η A M.X).app (y, z)
  have hStructureRaw :
      unitPrefixRaw ≫ etaInnerRaw ≫ actionInner ≫
          M.X.functor.map g =
        Sequence.TensorPowerModule.structureMap M q := by
    dsimp only [unitPrefixRaw, etaInnerRaw, actionInner, g, innerEq,
      A, y, z, Mq]
    change
      ((λ_ K).inv ⊗ₘ 𝟙 (M.X.functor.obj (Sequence.index q))) ≫
          (DayFunctor.η (Sequence.tensorPowerSequence K) M.X).app
            (Sequence.index 1, Sequence.index q) ≫
          M.mod.smul.natTrans.app
            (Sequence.index 1 ⊗ Sequence.index q) ≫
          M.X.functor.map
            (eqToHom ((Sequence.tensorObj_index 1 q).trans
              (congrArg Sequence.index (Nat.one_add q)))) =
        Sequence.TensorPowerModule.structureMap M q
    exact (Sequence.TensorPowerModule.structureMap_eq M q).symm
  have hPairingOneWhisker := congrArg
    (fun k => k ▷ Mq) (laxTensorPowerPairing_one K p)
  have hPrefix :
      (TensorPower.laxTensorPowerPairing (𝟭 C) K p 1 ▷ Mq) ≫
        (α_ Pp K Mq).hom ≫ (Pp ◁ unitPrefixRaw) =
      (α_ Pp (𝟙_ C ⊗ K) Mq).hom := by
    exact laxTensorPowerPairing_one_prefix K p Mq
  have hStructureWhiskeredRaw := congrArg
    (fun k => Pp ◁ k) hStructureRaw
  have hStructureWhiskered :
      (Pp ◁ unitPrefixRaw) ≫
          (Pp ◁ etaInnerRaw) ≫
          (Pp ◁ actionInner) ≫
          (Pp ◁ M.X.functor.map g) =
        Pp ◁ Sequence.TensorPowerModule.structureMap M q := by
    have h := hStructureWhiskeredRaw
    rw [MonoidalCategory.whiskerLeft_comp] at h
    rw [MonoidalCategory.whiskerLeft_comp] at h
    rw [MonoidalCategory.whiskerLeft_comp] at h
    exact h
  let structureTail :=
    (Pp ◁ etaInnerRaw) ≫
      (Pp ◁ actionInner) ≫
      (Pp ◁ M.X.functor.map g)
  have hPrefixPost := congrArg
    (fun k => k ≫ structureTail) hPrefix.symm
  have hPrefixTailBridge :
      ((TensorPower.laxTensorPowerPairing (𝟭 C) K p 1 ▷ Mq) ≫
          (α_ Pp K Mq).hom ≫ (Pp ◁ unitPrefixRaw)) ≫
          structureTail =
        (TensorPower.laxTensorPowerPairing (𝟭 C) K p 1 ▷ Mq) ≫
          (α_ Pp K Mq).hom ≫
          ((Pp ◁ unitPrefixRaw) ≫ structureTail) := by
    calc
      _ = (TensorPower.laxTensorPowerPairing (𝟭 C) K p 1 ▷ Mq) ≫
          (((α_ Pp K Mq).hom ≫ (Pp ◁ unitPrefixRaw)) ≫
            structureTail) := Category.assoc _ _ _
      _ = _ := congrArg
        (fun k => (TensorPower.laxTensorPowerPairing
          (𝟭 C) K p 1 ▷ Mq) ≫ k)
        (Category.assoc (α_ Pp K Mq).hom
          (Pp ◁ unitPrefixRaw) structureTail)
  have hStructureTail :
      (Pp ◁ unitPrefixRaw) ≫ structureTail =
        Pp ◁ Sequence.TensorPowerModule.structureMap M q := by
    dsimp only [structureTail]
    exact hStructureWhiskered
  have hStructureTailPost := congrArg
    (fun k => (TensorPower.laxTensorPowerPairing
      (𝟭 C) K p 1 ▷ Mq) ≫
      (α_ Pp K Mq).hom ≫ k) hStructureTail
  have hPrefixStructure :
      (α_ Pp (𝟙_ C ⊗ K) Mq).hom ≫ structureTail =
        (TensorPower.laxTensorPowerPairing (𝟭 C) K p 1 ▷ Mq) ≫
          (α_ Pp K Mq).hom ≫
          (Pp ◁ Sequence.TensorPowerModule.structureMap M q) := by
    exact hPrefixPost.trans
      (hPrefixTailBridge.trans hStructureTailPost)
  let sigmaNat : p + (q + 1) = (p + 1) + q :=
    (Nat.add_succ p q).trans (Nat.succ_add p q).symm
  let sigma : Sequence.index (p + (q + 1)) ⟶
      Sequence.index ((p + 1) + q) :=
    eqToHom (congrArg Sequence.index sigmaNat)
  let recursiveTail := originalAction M p (q + 1) ≫ M.X.functor.map sigma
  let recursivePrefix :=
    (TensorPower.laxTensorPowerPairing (𝟭 C) K p 1 ▷ Mq) ≫
      (α_ Pp K Mq).hom ≫
      (Pp ◁ Sequence.TensorPowerModule.structureMap M q)
  have hSource := originalAction_succ_pairing M p q
  change (TensorPower.laxTensorPowerPairing (𝟭 C) K p 1 ▷ Mq) ≫
      originalAction M (p + 1) q =
    ((α_ Pp (𝟙_ C ⊗ K) Mq).hom ≫ structureTail) ≫ recursiveTail at hSource
  have hPrefixStructurePost := congrArg
    (fun k => k ≫ recursiveTail) hPrefixStructure
  have hPrecomposed := hSource.trans hPrefixStructurePost
  let recursivePairPrefix :=
    (α_ Pp K Mq).hom ≫
      (Pp ◁ Sequence.TensorPowerModule.structureMap M q)
  let recursiveBody := recursivePairPrefix ≫ recursiveTail
  have hRecursiveBridge :
      recursivePrefix ≫ recursiveTail =
        (TensorPower.laxTensorPowerPairing (𝟭 C) K p 1 ▷ Mq) ≫
          recursiveBody := by
    dsimp only [recursivePrefix, recursivePairPrefix, recursiveTail,
      recursiveBody]
    exact Category.assoc _ _ _
  let eLeft := MonoidalCategory.whiskerLeftIso Pp (λ_ K)
  let ePrefix := MonoidalCategory.whiskerRightIso eLeft Mq
  have hPrefixIso :
      TensorPower.laxTensorPowerPairing (𝟭 C) K p 1 ▷ Mq =
        ePrefix.hom := by
    dsimp only [ePrefix, eLeft]
    exact hPairingOneWhisker
  change _ = recursivePrefix ≫ recursiveTail at hPrecomposed
  rw [hRecursiveBridge] at hPrecomposed
  rw [hPrefixIso] at hPrecomposed
  have hCancelled := (cancel_epi ePrefix.hom).mp hPrecomposed
  dsimp only [recursiveBody, recursivePairPrefix, recursiveTail,
    Pp, Mq, z, sigma, sigmaNat] at hCancelled
  have hCancelledAssoc :
      originalAction M (p + 1) q =
        (α_ (TensorPower.tensorPowObj K p) K
          (M.X.functor.obj (Sequence.index q))).hom ≫
          (TensorPower.tensorPowObj K p ◁
            Sequence.TensorPowerModule.structureMap M q) ≫
          originalAction M p (q + 1) ≫
          M.X.functor.map
            (eqToHom (congrArg Sequence.index
              ((Nat.add_succ p q).trans
                (Nat.succ_add p q).symm))) := by
    calc
      _ = ((α_ (TensorPower.tensorPowObj K p) K
            (M.X.functor.obj (Sequence.index q))).hom ≫
          (TensorPower.tensorPowObj K p ◁
            Sequence.TensorPowerModule.structureMap M q)) ≫
          (originalAction M p (q + 1) ≫
            M.X.functor.map
              (eqToHom (congrArg Sequence.index
                ((Nat.add_succ p q).trans
                  (Nat.succ_add p q).symm)))) := hCancelled
      _ = _ := Category.assoc _ _ _
  simpa only [MonoidalCategory.id_tensorHom] using hCancelledAssoc

/-- The original Day action at degree zero is the recovered spectrum's original left unitor. -/
theorem originalAction_zero
    (M : Sequence.TensorPowerModule K) (q : ℕ) :
    originalAction M 0 q =
      iteratedStructureMap ((fromTensorPowerModule K).obj M) 0 q := by
  let A := Sequence.tensorPowerSequence K
  let one := (Sequence.tensorPowerSequenceMonObj K).one
  let i0 := Sequence.index 0
  let iq := Sequence.index q
  let Mq := M.X.functor.obj iq
  let a := DayFunctor.ν Sequence.Index C ▷ Mq
  let b := one.natTrans.app i0 ▷ Mq
  let c := (DayFunctor.η A M.X).app (i0, iq)
  let d := M.mod.smul.natTrans.app (i0 ⊗ iq)
  let e := M.X.functor.map
    (eqToHom (Sequence.tensorObj_index 0 q))
  let u := (DayFunctor.η (𝟙_ (Sequence C)) M.X).app (i0, iq)
  let w := (one ▷ M.X).natTrans.app (i0 ⊗ iq)
  let l := (λ_ M.X).hom.natTrans.app (i0 ⊗ iq)
  let lm := (λ_ Mq).hom
  let mi := M.X.functor.map (λ_ iq).inv
  let rest := c ≫ d ≫ e
  let cRaw : (𝟙_ C ⊗ Mq) ⟶
      (tensor Sequence.Index ⋙ (A ⊗ M.X).functor).obj (i0, iq) :=
    (DayFunctor.η A M.X).app (i0, iq)
  let restRaw := cRaw ≫ d ≫ e
  have hC : c = cRaw := by rfl
  have hRest : rest = restRaw := by
    dsimp only [rest, restRaw]
    rw [hC]
    rfl
  have hcomp : a ≫ b =
      (DayFunctor.ν Sequence.Index C ≫ one.natTrans.app i0) ▷ Mq :=
    (MonoidalCategory.comp_whiskerRight _ _ _).symm
  have hScalarUnit :
      DayFunctor.ν Sequence.Index C ≫ one.natTrans.app i0 =
        TensorPower.laxTensorPowerUnit (𝟭 C) K := by
    dsimp only [one, i0]
    exact Sequence.tensorPowerSequenceOne_ν K
  have hScalarUnitTyped :
      DayFunctor.ν Sequence.Index C ≫ one.natTrans.app i0 =
        𝟙 (𝟙_ C) := by
    rw [hScalarUnit]
    rfl
  have hfacWhisker := hcomp.trans (congrArg
    (fun f => f ▷ Mq) hScalarUnitTyped)
  have hInsertRaw : restRaw = (a ≫ b) ≫ restRaw := by
    calc
      _ = (𝟙 (𝟙_ C) ▷ Mq) ≫ restRaw := by
        rw [MonoidalCategory.id_whiskerRight, Category.id_comp]
      _ = _ := congrArg (fun z => z ≫ restRaw) hfacWhisker.symm
  have hInsert : rest = (a ≫ b) ≫ rest := by
    rw [hRest]
    exact hInsertRaw
  have hStart := congrArg (fun z => z ≫ d ≫ e)
    (Category.assoc a b c)
  have hStartBridge : (a ≫ b) ≫ rest =
      (a ≫ b ≫ c) ≫ d ≫ e := by
    dsimp only [rest]
    calc
      _ = (((a ≫ b) ≫ c) ≫ d ≫ e) :=
        (Category.assoc _ _ (d ≫ e)).symm
      _ = _ := hStart
  have hwhisker : u ≫ w = b ≫ c := by
    exact convolutionExtensionUnit_comp_ι_map_whiskerRight_app
      Sequence.Index C one M.X i0 iq
  have hWhiskerPost := congrArg
    (fun z => a ≫ z ≫ d ≫ e) hwhisker
  have hWhiskerPostBridge :
      (a ≫ b ≫ c) ≫ d ≫ e =
        a ≫ (u ≫ w) ≫ d ≫ e := by
    calc
      _ = a ≫ (b ≫ c) ≫ d ≫ e :=
        Category.assoc a (b ≫ c) (d ≫ e)
      _ = _ := hWhiskerPost.symm
  have hOneLaw : (one ▷ M.X) ≫ M.mod.smul = (λ_ M.X).hom := by
    exact ModObj.one_smul_self A M.X
  have hOneNat := congrArg DayFunctor.Hom.natTrans hOneLaw
  have hOneRaw := congrArg (fun k => k.app (i0 ⊗ iq)) hOneNat
  have hOneSmul : w ≫ d = l := by
    simpa only [DayFunctor.comp_natTrans, NatTrans.comp_app] using hOneRaw
  have hOnePost := congrArg (fun z => a ≫ u ≫ z ≫ e) hOneSmul
  have hleft : a ≫ u ≫ l = lm ≫ mi := by
    exact leftUnitor_hom_unit_app C M.X iq
  have hLeftPost := congrArg (fun z => z ≫ e) hleft
  have hMap : mi ≫ e =
      eqToHom (congrArg
        (fun n => M.X.functor.obj (Sequence.index n))
        (Nat.zero_add q).symm) := by
    let t := eqToHom (Sequence.tensorObj_index 0 q)
    let zt := eqToHom (congrArg Sequence.index (Nat.zero_add q).symm)
    have hIndex : (λ_ iq).inv ≫ t = zt := by
      apply Subsingleton.elim
    dsimp only [mi, e]
    calc
      _ = M.X.functor.map ((λ_ iq).inv ≫ t) :=
        (M.X.functor.map_comp _ _).symm
      _ = M.X.functor.map zt := congrArg M.X.functor.map hIndex
      _ = _ := eqToHom_map M.X.functor _
  rw [show originalAction M 0 q = rest from rfl]
  rw [iteratedStructureMap_zero]
  rw [hInsert, hStartBridge, hWhiskerPostBridge]
  calc
    _ = a ≫ u ≫ w ≫ d ≫ M.X.functor.map
          (eqToHom (Sequence.tensorObj_index 0 q)) :=
      congrArg (fun z => a ≫ z)
        (Category.assoc u w
          (d ≫ M.X.functor.map
            (eqToHom (Sequence.tensorObj_index 0 q))))
    _ = a ≫ u ≫ l ≫ M.X.functor.map
          (eqToHom (Sequence.tensorObj_index 0 q)) := by
      simpa only [Category.assoc] using hOnePost
    _ = a ≫ ((u ≫ l) ≫ M.X.functor.map
          (eqToHom (Sequence.tensorObj_index 0 q))) :=
      congrArg (fun z => a ≫ z)
        (Category.assoc u l
          (M.X.functor.map
            (eqToHom (Sequence.tensorObj_index 0 q)))).symm
    _ = (a ≫ (u ≫ l)) ≫ M.X.functor.map
          (eqToHom (Sequence.tensorObj_index 0 q)) :=
      (Category.assoc a (u ≫ l)
        (M.X.functor.map
          (eqToHom (Sequence.tensorObj_index 0 q)))).symm
    _ = (lm ≫ mi) ≫ M.X.functor.map
          (eqToHom (Sequence.tensorObj_index 0 q)) := hLeftPost
    _ = lm ≫ mi ≫ M.X.functor.map
          (eqToHom (Sequence.tensorObj_index 0 q)) :=
      Category.assoc lm mi
        (M.X.functor.map
          (eqToHom (Sequence.tensorObj_index 0 q)))
    _ = _ := congrArg (fun z => lm ≫ z) hMap

end

end ModuleReconstruction

/-- The action of a tensor-power module on a degree pair is recovered by
the iterated successor structure maps of its associated spectrum. -/
theorem module_action_recovery (K : C)
    (M : Sequence.TensorPowerModule K) (p q : ℕ) :
    (DayFunctor.η (Sequence.tensorPowerSequence K) M.X).app
        (Sequence.index p, Sequence.index q) ≫
      M.mod.smul.natTrans.app
        (Sequence.index p ⊗ Sequence.index q) ≫
      M.X.functor.map (eqToHom (Sequence.tensorObj_index p q)) =
    iteratedStructureMap ((fromTensorPowerModule K).obj M) p q := by
  change ModuleReconstruction.originalAction M p q = _
  induction p generalizing q with
  | zero =>
      exact ModuleReconstruction.originalAction_zero M q
  | succ p ih =>
      rw [ModuleReconstruction.originalAction_succ M p q]
      slice_lhs 3 4 => rw [ih (q := q + 1)]
      have hTransport :
          M.X.functor.map
              (eqToHom (congrArg Sequence.index
                ((Nat.add_succ p q).trans
                  (Nat.succ_add p q).symm))) =
            eqToHom (congrArg ((fromTensorPowerModule K).obj M).level
              ((Nat.add_succ p q).trans
                (Nat.succ_add p q).symm)) := by
        rw [eqToHom_map]
        rfl
      rw [hTransport]
      exact (iteratedStructureMap_succ
        ((fromTensorPowerModule K).obj M) p q).symm

/-- The actual module counit component, with the original degree-index map. -/
@[expose]
noncomputable def tensorPowerModuleCounitIsoApp (K : C)
    (M : Sequence.TensorPowerModule K) :
    ((fromTensorPowerModule K) ⋙ (toTensorPowerModule K)).obj M ≅ M := by
  let toModule := toTensorPowerModule K
  let fromModule := fromTensorPowerModule K
  let spectrumModule (X : SequentialSpectrum C K) :
      Sequence.TensorPowerModule K := toModule.obj X
  let moduleSpectrum (M : Sequence.TensorPowerModule K) :
      SequentialSpectrum C K := fromModule.obj M
  let spectrumSequence (X : SequentialSpectrum C K) : Sequence C :=
    (spectrumModule X).X
  let spectrumAction (X : SequentialSpectrum C K) :
      Sequence.tensorPowerSequence K ⊗ spectrumSequence X ⟶
        spectrumSequence X :=
    (spectrumModule X).mod.smul
  let degree_tensor (i j : Sequence.Index) :
      Sequence.degree i + Sequence.degree j =
        Sequence.degree (i ⊗ j) := by
    cases i
    cases j
    rfl
  let spectrumActionDesc
      (X : SequentialSpectrum C K) :
      (Sequence.tensorPowerSequence K).functor ⊠
          (spectrumSequence X).functor ⟶
        tensor Sequence.Index ⋙ (spectrumSequence X).functor := {
    app i := iteratedStructureMap X
        (Sequence.degree i.1) (Sequence.degree i.2) ≫
      eqToHom (congrArg X.level (degree_tensor i.1 i.2))
    naturality := by
      rintro ⟨i, j⟩ ⟨i', j'⟩ f
      have h : (i, j) = (i', j') := Prod.ext
        (Discrete.ext (Discrete.eq_of_hom f.1))
        (Discrete.ext (Discrete.eq_of_hom f.2))
      cases h
      rw [show f = 𝟙 _ by ext <;> apply Discrete.hom_eq]
      simp }
  let spectrumActionDesc_index
      (X : SequentialSpectrum C K) (p q : ℕ) :
      (spectrumActionDesc X).app
          (Sequence.index p, Sequence.index q) =
        iteratedStructureMap X p q := by
    change iteratedStructureMap X p q ≫ eqToHom _ = _
    apply eq_of_heq
    exact comp_eqToHom_heq _ _
  have spectrumAction_eq (X : SequentialSpectrum C K) :
      spectrumAction X =
        DayFunctor.tensorDesc (spectrumActionDesc X) := by
    rfl
  let spectrumAction_fac
      (X : SequentialSpectrum C K) (i j : Sequence.Index) :
      (DayFunctor.η (Sequence.tensorPowerSequence K)
          (spectrumSequence X)).app (i, j) ≫
          (spectrumAction X).natTrans.app (i ⊗ j) =
        (spectrumActionDesc X).app (i, j) := by
    rw [spectrumAction_eq]
    exact DayFunctor.η_comp_tensorDesc_app (spectrumActionDesc X) i j
  let originalAction
      (M : Sequence.TensorPowerModule K) (p q : ℕ) :
      TensorPower.tensorPowObj K p ⊗
          M.X.functor.obj (Sequence.index q) ⟶
        M.X.functor.obj (Sequence.index (p + q)) :=
    (DayFunctor.η (Sequence.tensorPowerSequence K) M.X).app
        (Sequence.index p, Sequence.index q) ≫
      M.mod.smul.natTrans.app
        (Sequence.index p ⊗ Sequence.index q) ≫
      M.X.functor.map (eqToHom (Sequence.tensorObj_index p q))
  let X := moduleSpectrum M
  let S := spectrumModule X
  let eNat : (spectrumSequence X).functor ≅ M.X.functor :=
    Discrete.natIso fun i =>
      M.X.functor.mapIso (eqToIso (Sequence.index_degree i))
  let eRaw : spectrumSequence X ≅ M.X :=
    (DayFunctor.equiv Sequence.Index C).inverse.mapIso eNat
  let e : S.X ≅ M.X := eRaw
  have hLinearRaw :
      spectrumAction X ≫ eRaw.hom =
        (Sequence.tensorPowerSequence K ◁ eRaw.hom) ≫ M.mod.smul := by
    apply DayFunctor.tensor_hom_ext
    intro i j
    simp only [DayFunctor.comp_natTrans, NatTrans.comp_app]
    rw [← Category.assoc, spectrumAction_fac]
    have hEta :
        (DayFunctor.η (Sequence.tensorPowerSequence K)
            (spectrumSequence X)).app (i, j) ≫
            ((Sequence.tensorPowerSequence K ◁ eRaw.hom).natTrans.app
              (i ⊗ j)) =
          ((Sequence.tensorPowerSequence K).functor.obj i ◁
              eRaw.hom.natTrans.app j) ≫
            (DayFunctor.η (Sequence.tensorPowerSequence K) M.X).app
              (i, j) := by
      exact convolutionExtensionUnit_comp_ι_map_whiskerLeft_app
        C (Sequence.tensorPowerSequence K) eRaw.hom i j
    rw [← Category.assoc, hEta, Category.assoc]
    rcases i with ⟨p⟩
    rcases j with ⟨q⟩
    let pn := p.toAdd
    let qn := q.toAdd
    have hp : (⟨p⟩ : Sequence.Index) = Sequence.index pn := by rfl
    have hq : (⟨q⟩ : Sequence.Index) = Sequence.index qn := by rfl
    rw [hp, hq]
    have hDesc :
        (spectrumActionDesc X).app
            (Sequence.index pn, Sequence.index qn) =
          iteratedStructureMap X pn qn := by
      convert spectrumActionDesc_index X pn qn using 1
    have hLevel :
        eRaw.hom.natTrans.app (Sequence.index qn) =
          𝟙 (M.X.functor.obj (Sequence.index qn)) := by
      change M.X.functor.map
          (eqToHom (Sequence.index_degree (Sequence.index qn))) = 𝟙 _
      simp
    have hTensor :
        eRaw.hom.natTrans.app
            (Sequence.index pn ⊗ Sequence.index qn) =
          M.X.functor.map
            (eqToHom
              (Sequence.tensorObj_index pn qn).symm) := by
      change M.X.functor.map
          (eqToHom (Sequence.index_degree
            (Sequence.index pn ⊗ Sequence.index qn))) =
        M.X.functor.map
          (eqToHom (Sequence.tensorObj_index pn qn).symm)
      apply congrArg M.X.functor.map
      apply Subsingleton.elim
    have hDescPost := congrArg
      (fun k => k ≫ eRaw.hom.natTrans.app
        (Sequence.index pn ⊗ Sequence.index qn)) hDesc
    have hTensorPost := congrArg
      (fun k => iteratedStructureMap X pn qn ≫ k) hTensor
    have hRecoveryPost := congrArg
      (fun k => k ≫ M.X.functor.map
        (eqToHom (Sequence.tensorObj_index pn qn).symm))
      (module_action_recovery K M pn qn).symm
    let aObj := (Sequence.tensorPowerSequence K).functor.obj
      (Sequence.index pn)
    let mObj := M.X.functor.obj (Sequence.index qn)
    let etaOrig : aObj ⊗ mObj ⟶
        (tensor Sequence.Index ⋙
          (Sequence.tensorPowerSequence K ⊗ M.X).functor).obj
            (Sequence.index pn, Sequence.index qn) :=
      (DayFunctor.η (Sequence.tensorPowerSequence K) M.X).app
        (Sequence.index pn, Sequence.index qn)
    let actionOrig :
        (Sequence.tensorPowerSequence K ⊗ M.X).functor.obj
            (Sequence.index pn ⊗ Sequence.index qn) ⟶
          M.X.functor.obj (Sequence.index pn ⊗ Sequence.index qn) :=
      M.mod.smul.natTrans.app
        (Sequence.index pn ⊗ Sequence.index qn)
    let tauMap := M.X.functor.map
      (eqToHom (Sequence.tensorObj_index pn qn))
    let tauInv := M.X.functor.map
      (eqToHom (Sequence.tensorObj_index pn qn).symm)
    have hOriginal : originalAction M pn qn =
        etaOrig ≫ actionOrig ≫ tauMap := by rfl
    have hMapCancel : tauMap ≫ tauInv = 𝟙 _ := by
      dsimp only [tauMap, tauInv]
      rw [← M.X.functor.map_comp]
      simp
    have hCancel :
        originalAction M pn qn ≫ M.X.functor.map
            (eqToHom (Sequence.tensorObj_index pn qn).symm) =
          (DayFunctor.η (Sequence.tensorPowerSequence K) M.X).app
              (Sequence.index pn, Sequence.index qn) ≫
            M.mod.smul.natTrans.app
              (Sequence.index pn ⊗ Sequence.index qn) := by
      rw [hOriginal]
      change (etaOrig ≫ actionOrig ≫ tauMap) ≫ tauInv =
        etaOrig ≫ actionOrig
      calc
        _ = etaOrig ≫ actionOrig ≫ (tauMap ≫ tauInv) := by
          simp only [Category.assoc]
        _ = _ := by rw [hMapCancel, Category.comp_id]
    have hLevelInsert :
        etaOrig ≫ actionOrig =
          (aObj ◁ eRaw.hom.natTrans.app (Sequence.index qn)) ≫
            etaOrig ≫ actionOrig := by
      have hLevelPost := congrArg
        (fun k => (aObj ◁ k) ≫ etaOrig ≫ actionOrig) hLevel
      have hIdInsert : etaOrig ≫ actionOrig =
          (aObj ◁ 𝟙 mObj) ≫ etaOrig ≫ actionOrig := by
        rw [MonoidalCategory.whiskerLeft_id, Category.id_comp]
      exact hIdInsert.trans hLevelPost.symm
    exact hDescPost.trans
      (hTensorPost.trans
        (hRecoveryPost.trans (hCancel.trans hLevelInsert)))
  have hLinear :
      S.mod.smul ≫ e.hom =
        (Sequence.tensorPowerSequence K ◁ e.hom) ≫ M.mod.smul := by
    dsimp only [S, e]
    exact hLinearRaw
  fail_if_success
    let _bad : IsModHom (Sequence.tensorPowerSequence K) e.hom :=
      ⟨hLinear.symm⟩
  fail_if_success
    let _bad : S ⟶ M := ⟨e.hom⟩
  letI : IsModHom (Sequence.tensorPowerSequence K) e.hom := ⟨hLinear⟩
  letI : IsModHom (Sequence.tensorPowerSequence K) e.inv := inferInstance
  let hom : S ⟶ M := ⟨e.hom⟩
  let inv : M ⟶ S := ⟨e.inv⟩
  exact
    { hom := hom
      inv := inv
      hom_inv_id := by
        apply CategoryTheory.Mod.hom_ext
        exact e.hom_inv_id
      inv_hom_id := by
        apply CategoryTheory.Mod.hom_ext
        exact e.inv_hom_id }

/-- The actual module counit as a natural isomorphism. -/
@[expose]
noncomputable def tensorPowerModuleCounitIso (K : C) :
    fromTensorPowerModule K ⋙ toTensorPowerModule K ≅
      𝟭 (Sequence.TensorPowerModule K) :=
  NatIso.ofComponents (tensorPowerModuleCounitIsoApp K) (fun {X Y} f => by
      apply CategoryTheory.Mod.hom_ext
      apply DayFunctor.hom_ext
      apply NatTrans.ext
      funext i
      change f.hom.natTrans.app
            (Sequence.index (Sequence.degree i)) ≫
            Y.X.functor.map (eqToHom (Sequence.index_degree i)) =
          X.X.functor.map (eqToHom (Sequence.index_degree i)) ≫
            f.hom.natTrans.app i
      exact (f.hom.natTrans.naturality
        (eqToHom (Sequence.index_degree i))).symm)

/-- Sequential spectra are equivalent to modules over the tensor-power
sequence. -/
@[expose]
noncomputable def moduleEquivalence (K : C) :
    SequentialSpectrum C K ≌ Sequence.TensorPowerModule K :=
  CategoryTheory.Equivalence.mk
    (toTensorPowerModule K) (fromTensorPowerModule K)
    (tensorPowerModuleUnitIso K) (tensorPowerModuleCounitIso K)

@[simp]
theorem moduleEquivalence_functor_obj_level
    (K : C) (X : SequentialSpectrum C K) (n : ℕ) :
    ((moduleEquivalence K).functor.obj X).X.functor.obj
        (Sequence.index n) = X.level n :=
  rfl

@[simp]
theorem moduleEquivalence_inverse_obj_level
    (K : C) (M : Sequence.TensorPowerModule K) (n : ℕ) :
    ((moduleEquivalence K).inverse.obj M).level n =
      M.X.functor.obj (Sequence.index n) :=
  rfl

@[simp]
theorem moduleEquivalence_inverse_obj_structureMap
    (K : C) (M : Sequence.TensorPowerModule K) (n : ℕ) :
    ((moduleEquivalence K).inverse.obj M).structureMap n =
      Sequence.TensorPowerModule.structureMap M n :=
  rfl

@[simp]
theorem moduleEquivalence_functor_map_app
    (K : C) {X Y : SequentialSpectrum C K} (f : X ⟶ Y) (n : ℕ) :
    ((moduleEquivalence K).functor.map f).hom.natTrans.app
        (Sequence.index n) = f.levelMap n :=
  rfl

/-- The original module counit retains its whole forward component. -/
theorem tensorPowerModuleCounitIsoApp_hom_app
    (K : C) (M : Sequence.TensorPowerModule K) (i : Sequence.Index) :
    (tensorPowerModuleCounitIsoApp K M).hom.hom.natTrans.app i =
      M.X.functor.map (eqToHom (Sequence.index_degree i)) := rfl

/-- The original module counit retains its whole inverse component. -/
theorem tensorPowerModuleCounitIsoApp_inv_app
    (K : C) (M : Sequence.TensorPowerModule K) (i : Sequence.Index) :
    (tensorPowerModuleCounitIsoApp K M).inv.hom.natTrans.app i =
      M.X.functor.map (eqToHom (Sequence.index_degree i).symm) := rfl


end

end CategoryTheory.SequentialSpectrum
