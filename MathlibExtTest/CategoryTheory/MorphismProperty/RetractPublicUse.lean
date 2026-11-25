/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.MorphismProperty.Retract
import Lean.Util.CollectAxioms
import Batteries.Tactic.Lint

/-!
# Public generic Arrow-retract clients

The original pushout legs, all four coproduct components, both Arrow squares
and actual splitting maps are checked through the low-level retract API.
Generic users require no cellular or coherent-absorption import.
-/

set_option autoImplicit false
noncomputable section

namespace MorphismPropertyRetractPublicUse

universe u v w κ
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

section ParticularPushouts

variable {C : Type u} [Category.{v} C]
  {A B U V X : C} {f : A ⟶ B} {g : U ⟶ V}
  (R : RetractArrow f g) (a : A ⟶ X)
  [HasPushout f a] [HasPushout g (R.r.left ≫ a)]

example : (pushoutRetract R a).i.left = 𝟙 X ∧
    (pushoutRetract R a).r.left = 𝟙 X := ⟨rfl, rfl⟩

example : pushout.inl f a ≫ (pushoutRetract R a).i.right =
    R.i.right ≫ pushout.inl g (R.r.left ≫ a) := by
  simp [pushoutRetract]

example : pushout.inr f a ≫ (pushoutRetract R a).i.right =
    pushout.inr g (R.r.left ≫ a) := by
  simp [pushoutRetract]

example : pushout.inl g (R.r.left ≫ a) ≫ (pushoutRetract R a).r.right =
    R.r.right ≫ pushout.inl f a := by
  simp [pushoutRetract]

example : pushout.inr g (R.r.left ≫ a) ≫ (pushoutRetract R a).r.right =
    pushout.inr f a := by
  simp [pushoutRetract]

example : (pushoutRetract R a).i.right ≫ (pushoutRetract R a).r.right =
    𝟙 (pushout f a) := (pushoutRetract R a).retract_right

end ParticularPushouts

section OriginalCoproductMaps

variable {C : Type u} [Category.{v} C] {I : Type κ}
  [HasColimitsOfShape (Discrete I) C]
  {A B U V : I → C} {f : ∀ i, A i ⟶ B i} {g : ∀ i, U i ⟶ V i}
  (R : ∀ i, RetractArrow (f i) (g i))

example : (coproductRetract R).i.left = Limits.Sigma.map (fun i => (R i).i.left) ∧
    (coproductRetract R).i.right = Limits.Sigma.map (fun i => (R i).i.right) ∧
    (coproductRetract R).r.left = Limits.Sigma.map (fun i => (R i).r.left) ∧
    (coproductRetract R).r.right = Limits.Sigma.map (fun i => (R i).r.right) :=
  ⟨rfl, rfl, rfl, rfl⟩

example (i : I) : Limits.Sigma.ι A i ≫ (coproductRetract R).i.left =
    (R i).i.left ≫ Limits.Sigma.ι U i := by
  simp [coproductRetract]

example (i : I) : Limits.Sigma.ι B i ≫ (coproductRetract R).i.right =
    (R i).i.right ≫ Limits.Sigma.ι V i := by
  simp [coproductRetract]

example (i : I) : Limits.Sigma.ι U i ≫ (coproductRetract R).r.left =
    (R i).r.left ≫ Limits.Sigma.ι A i := by
  simp [coproductRetract]

example (i : I) : Limits.Sigma.ι V i ≫ (coproductRetract R).r.right =
    (R i).r.right ≫ Limits.Sigma.ι B i := by
  simp [coproductRetract]

example : (coproductRetract R).i.left ≫ Limits.Sigma.map g =
      Limits.Sigma.map f ≫ (coproductRetract R).i.right ∧
    (coproductRetract R).r.left ≫ Limits.Sigma.map f =
      Limits.Sigma.map g ≫ (coproductRetract R).r.right ∧
    (coproductRetract R).i.right ≫ (coproductRetract R).r.right = 𝟙 (∐ B) :=
  ⟨(coproductRetract R).i_w, (coproductRetract R).r_w,
    (coproductRetract R).retract_right⟩

end OriginalCoproductMaps

section GenericClosure

variable {C : Type u} [Category.{v} C] (P : MorphismProperty C)

example : P.retracts.IsStableUnderRetracts := inferInstance

example [HasPushouts C] [P.IsStableUnderCobaseChange]
    {A B X Z : C} {f : A ⟶ B} {q : X ⟶ Z} {a : A ⟶ X} {b : B ⟶ Z}
    (sq : IsPushout a f q b) (hf : P.retracts f) : P.retracts q := by
  let _ : P.retracts.IsStableUnderCobaseChange := retractsIsStableUnderCobaseChange P
  exact MorphismProperty.of_isPushout sq hf

example [HasCoproducts.{w} C] [P.IsStableUnderCoproducts.{w}] :
    P.retracts.IsStableUnderCoproducts.{w} := retractsIsStableUnderCoproducts P

end GenericClosure

end MorphismPropertyRetractPublicUse

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless env.getModuleIdx?
      `MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.TransfiniteAbsorption == none do
    throwError "generic retract clients imported coherent transfinite absorption"
  let some idx := env.getModuleIdx? `MathlibExt.CategoryTheory.MorphismProperty.Retract
    | throwError "actual generic retract module missing"
  let names := env.constants.fold (init := #[]) fun xs n _ =>
    if env.getModuleIdxFor? n == some idx then xs.push n else xs
  unless names.size > 0 do throwError "empty generic retract module"
  for n in names do
    let axs ← Lean.collectAxioms n
    let bad := axs.filter fun a => a != ``propext && a != ``Quot.sound && a != ``Classical.choice
    unless bad.isEmpty do throwError "forbidden axioms in {n}: {bad}"
  logInfo m!"GENERIC_RETRACT_PUBLIC_AXIOMS {names.size} standard-three only; no absorption import"

#lint only unusedArguments in MathlibExt.CategoryTheory.MorphismProperty.Retract
