/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.RightHomotopyYonedaWeak

/-!
# Weak recognition on genuine cofibrant sources

Actual model factorizations of the two terminal maps and their original
lifting square reduce the right-class Yoneda test to bifibrant objects.
Neither source is assumed fibrant and no functorial replacement or weak
comparison is supplied as an input.
-/

noncomputable section
universe u v
open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopicalAlgebra

/-- Original right-class precomposition retains the actual composition of both source maps. -/
theorem RightHomotopyClass.precomp_comp {C : Type u} [Category.{v} C]
    [CategoryWithWeakEquivalences C] {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y)
    (a : RightHomotopyClass Y Z) : a.precomp (f ≫ g) = (a.precomp g).precomp f := by
  induction a using Quot.inductionOn with
  | _ a => exact congrArg RightHomotopyClass.mk (Category.assoc f g a)

/-- Fibrant-target tests on the SAME original right classes detect weak maps between arbitrary
cofibrant sources. -/
theorem weakEquivalence_iff_rightHomotopyClass_precomp_bijective_of_cofibrant
    {C : Type u} [Category.{v} C] [ModelCategory C] {X Y : C}
    [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) :
    WeakEquivalence f ↔ ∀ (Z : C) [IsFibrant Z],
      Function.Bijective (fun g : RightHomotopyClass Y Z => g.precomp f) := by
  constructor
  · intro hf Z _
    let _ : WeakEquivalence f := hf
    exact RightHomotopyClass.precomp_bijective_of_weakEquivalence Z f
  · intro h
    let dX := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C)
        (terminal.from X)
    let dY := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C)
        (terminal.from Y)
    let _ : Cofibration dX.i := (cofibration_iff _).mpr dX.hi.1
    let _ : WeakEquivalence dX.i := (weakEquivalence_iff _).mpr dX.hi.2
    let _ : Fibration dX.p := (fibration_iff _).mpr dX.hp
    let _ : Cofibration dY.i := (cofibration_iff _).mpr dY.hi.1
    let _ : WeakEquivalence dY.i := (weakEquivalence_iff _).mpr dY.hi.2
    let _ : Fibration dY.p := (fibration_iff _).mpr dY.hp
    let _ : IsCofibrant dX.Z := isCofibrant_of_cofibration dX.i
    let _ : IsCofibrant dY.Z := isCofibrant_of_cofibration dY.i
    let _ : IsFibrant dX.Z := (isFibrant_iff_of_isTerminal dX.p terminalIsTerminal).mpr
        inferInstance
    let _ : IsFibrant dY.Z := (isFibrant_iff_of_isTerminal dY.p terminalIsTerminal).mpr
        inferInstance
    let sq : CommSq (f ≫ dY.i) dX.i dY.p (terminal.from dX.Z) := ⟨by simp⟩
    let f' : dX.Z ⟶ dY.Z := sq.lift
    have hf' : dX.i ≫ f' = f ≫ dY.i := sq.fac_left
    have hpre (Z : C) [IsFibrant Z] :
        Function.Bijective (fun g : RightHomotopyClass dY.Z Z => g.precomp f') := by
      have hb := (h Z).comp (RightHomotopyClass.precomp_bijective_of_weakEquivalence Z dY.i)
      have hc : Function.Bijective ((fun g : RightHomotopyClass dX.Z Z => g.precomp dX.i) ∘
          (fun g : RightHomotopyClass dY.Z Z => g.precomp f')) := by
        convert hb using 1
        funext g
        dsimp only [Function.comp_def]
        rw [← RightHomotopyClass.precomp_comp, hf', RightHomotopyClass.precomp_comp]
      exact hc.of_comp_left
          (RightHomotopyClass.precomp_bijective_of_weakEquivalence Z dX.i).injective
    let _ : WeakEquivalence f' := (weakEquivalence_iff_rightHomotopyClass_precomp_bijective f').mpr
        hpre
    have hw : WeakEquivalence (f ≫ dY.i) := by
      rw [← hf']
      infer_instance
    exact (weakEquivalence_postcomp_iff f dY.i).mp hw

end HomotopicalAlgebra
