/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.IteratedAlgebra
public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.IteratedMatchingPaths

/-!
# Literal finite-stage homotopy classes

Two representatives `A → α^n B` are `n`-homotopic when they are the two
actual iterated endpoint evaluations of one homomorphism
`A → α^n C([0,1], B)`. Constant paths, interval reversal, and genuine
matching-path gluing prove that this is an equivalence relation.

The explicit quotient and its constant-stage transition are data only. This
file defines no product, direct limit, flattening, E-theory class, or
comparison with ordinary asymptotic homotopy.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra

attribute [local instance] AsymptoticAlgebra.cStarAlgebra

namespace IteratedAsymptoticAlgebra

universe uA uB

/-! ## Iterated constant paths and reversal -/

/-- Constant paths after applying the nth finite alpha iterate. -/
@[no_expose]
def constantPathHomN (n : ℕ)
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    IteratedAsymptoticAlgebra n B →⋆ₙₐ[ℂ]
      IteratedAsymptoticAlgebra n C(unitInterval, B) :=
  map n (ContinuousMap.IntervalGluing.constantHom B)

/-- Interval reversal after applying the nth finite alpha iterate. -/
@[no_expose]
def reversePathHomN (n : ℕ)
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    IteratedAsymptoticAlgebra n C(unitInterval, B) →⋆ₙₐ[ℂ]
      IteratedAsymptoticAlgebra n C(unitInterval, B) :=
  map n (ContinuousMap.IntervalGluing.reverseHom B)

private theorem evalAt_comp_constantHom (t : unitInterval)
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    (ContinuousMap.IntervalGluing.evalAt B t).comp
        (ContinuousMap.IntervalGluing.constantHom B) =
      NonUnitalStarAlgHom.id ℂ B := by
  apply NonUnitalStarAlgHom.ext
  intro b
  rfl

private theorem evalAt_zero_comp_reverseHom
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    (ContinuousMap.IntervalGluing.evalAt B 0).comp
        (ContinuousMap.IntervalGluing.reverseHom B) =
      ContinuousMap.IntervalGluing.evalAt B 1 := by
  apply NonUnitalStarAlgHom.ext
  intro f
  exact ContinuousMap.IntervalGluing.reverseHom_zero (B := B) f

private theorem evalAt_one_comp_reverseHom
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    (ContinuousMap.IntervalGluing.evalAt B 1).comp
        (ContinuousMap.IntervalGluing.reverseHom B) =
      ContinuousMap.IntervalGluing.evalAt B 0 := by
  apply NonUnitalStarAlgHom.ext
  intro f
  exact ContinuousMap.IntervalGluing.reverseHom_one (B := B) f

@[simp]
theorem endpointHom_comp_constantPathHomN (n : ℕ) (t : unitInterval)
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    (AsymptoticAlgebra.endpointHom n t B).comp (constantPathHomN n B) =
      NonUnitalStarAlgHom.id ℂ (IteratedAsymptoticAlgebra n B) := by
  unfold constantPathHomN
  rw [AsymptoticAlgebra.endpointHom_eq, ← map_comp,
    evalAt_comp_constantHom, map_id]

@[simp]
theorem endpointHom_zero_comp_reversePathHomN (n : ℕ)
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    (AsymptoticAlgebra.endpointHom n 0 B).comp (reversePathHomN n B) =
      AsymptoticAlgebra.endpointHom n 1 B := by
  unfold reversePathHomN
  rw [AsymptoticAlgebra.endpointHom_eq, ← map_comp,
    evalAt_zero_comp_reverseHom, ← AsymptoticAlgebra.endpointHom_eq]

@[simp]
theorem endpointHom_one_comp_reversePathHomN (n : ℕ)
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    (AsymptoticAlgebra.endpointHom n 1 B).comp (reversePathHomN n B) =
      AsymptoticAlgebra.endpointHom n 0 B := by
  unfold reversePathHomN
  rw [AsymptoticAlgebra.endpointHom_eq, ← map_comp,
    evalAt_one_comp_reverseHom, ← AsymptoticAlgebra.endpointHom_eq]

/-! ## The literal relation -/

/-- Literal `n`-homotopy of homomorphisms `A → α^n B`. -/
def HomotopicN (n : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ ψ : HomN n A B) : Prop :=
  ∃ H : HomN n A C(unitInterval, B),
    (AsymptoticAlgebra.endpointHom n 0 B).comp H = φ ∧
      (AsymptoticAlgebra.endpointHom n 1 B).comp H = ψ

namespace HomotopicN

variable {n : ℕ} {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- Every representative is `n`-homotopic to itself. -/
theorem refl (φ : HomN n A B) : HomotopicN n φ φ := by
  refine ⟨(constantPathHomN n B).comp φ, ?_, ?_⟩
  · rw [← NonUnitalStarAlgHom.comp_assoc,
      endpointHom_comp_constantPathHomN]
    rfl
  · rw [← NonUnitalStarAlgHom.comp_assoc,
      endpointHom_comp_constantPathHomN]
    rfl

/-- Reversing the interval reverses an `n`-homotopy. -/
theorem symm {φ ψ : HomN n A B} (h : HomotopicN n φ ψ) :
    HomotopicN n ψ φ := by
  obtain ⟨H, h0, h1⟩ := h
  refine ⟨(reversePathHomN n B).comp H, ?_, ?_⟩
  · rw [← NonUnitalStarAlgHom.comp_assoc,
      endpointHom_zero_comp_reversePathHomN]
    exact h1
  · rw [← NonUnitalStarAlgHom.comp_assoc,
      endpointHom_one_comp_reversePathHomN]
    exact h0

/-- Genuine matching-path gluing concatenates two `n`-homotopies. -/
theorem trans {φ ψ χ : HomN n A B}
    (hφψ : HomotopicN n φ ψ) (hψχ : HomotopicN n ψ χ) :
    HomotopicN n φ χ := by
  obtain ⟨H₀₁, h₀, h₁⟩ := hφψ
  obtain ⟨H₁₂, h₁', h₂⟩ := hψχ
  have hmatch :
      (AsymptoticAlgebra.endpointHom n 1 B).comp H₀₁ =
        (AsymptoticAlgebra.endpointHom n 0 B).comp H₁₂ :=
    h₁.trans h₁'.symm
  let P : A →⋆ₙₐ[ℂ] AsymptoticAlgebra.IteratedMatchingPaths n B :=
    NonUnitalCStarPullback.lift
      (AsymptoticAlgebra.endpointHom n 1 B)
      (AsymptoticAlgebra.endpointHom n 0 B) H₀₁ H₁₂ hmatch
  refine ⟨(AsymptoticAlgebra.glueHomN n B).comp P, ?_, ?_⟩
  · dsimp only [P]
    rw [← NonUnitalStarAlgHom.comp_assoc,
      AsymptoticAlgebra.endpointHom_zero_comp_glueHomN,
      NonUnitalStarAlgHom.comp_assoc,
      NonUnitalCStarPullback.fstHom_comp_lift, h₀]
  · dsimp only [P]
    rw [← NonUnitalStarAlgHom.comp_assoc,
      AsymptoticAlgebra.endpointHom_one_comp_glueHomN,
      NonUnitalStarAlgHom.comp_assoc,
      NonUnitalCStarPullback.sndHom_comp_lift, h₂]

end HomotopicN

/-! ## Explicit quotient data -/

/-- The explicit, non-global setoid of literal `n`-homotopy. -/
def homotopicNSetoid (n : ℕ)
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    Setoid (HomN n A B) where
  r := HomotopicN n
  iseqv :=
    { refl := HomotopicN.refl
      symm := HomotopicN.symm
      trans := HomotopicN.trans }

/-- Literal `n`-homotopy classes. This is an explicit quotient, not a global
setoid instance. -/
def NClasses (n : ℕ)
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :=
  Quotient (homotopicNSetoid n A B)

/-- The class of one representative. -/
def classOf (n : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ : HomN n A B) : NClasses n A B :=
  Quotient.mk _ φ

/-! ## Constant-stage transition -/

/-- Include a representative into the next finite alpha stage. -/
def stageTransitionRepresentative (n : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ : HomN n A B) : HomN (n + 1) A B :=
  (stageHom n B).comp φ

theorem stageTransitionRepresentative_apply (n : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ : HomN n A B) (a : A) :
    stageTransitionRepresentative n φ a = stageHom n B (φ a) :=
  rfl

/-- Constant-stage inclusion preserves literal `n`-homotopy. -/
theorem stageTransitionRepresentative_respects (n : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    {φ ψ : HomN n A B} (h : HomotopicN n φ ψ) :
    HomotopicN (n + 1)
      (stageTransitionRepresentative n φ)
      (stageTransitionRepresentative n ψ) := by
  obtain ⟨H, h0, h1⟩ := h
  have hnat (t : unitInterval) :
      (AsymptoticAlgebra.endpointHom (n + 1) t B).comp
          (stageHom n C(unitInterval, B)) =
        (stageHom n B).comp (AsymptoticAlgebra.endpointHom n t B) := by
    simpa only [AsymptoticAlgebra.endpointHom_eq] using
      stageHom_naturality n (ContinuousMap.IntervalGluing.evalAt B t)
  refine ⟨(stageHom n C(unitInterval, B)).comp H, ?_, ?_⟩
  · unfold stageTransitionRepresentative
    rw [← NonUnitalStarAlgHom.comp_assoc, hnat,
      NonUnitalStarAlgHom.comp_assoc, h0]
  · unfold stageTransitionRepresentative
    rw [← NonUnitalStarAlgHom.comp_assoc, hnat,
      NonUnitalStarAlgHom.comp_assoc, h1]

/-- The constant-stage map on literal `n`-homotopy classes. Naturality in
the source and target algebras is separate future work. -/
def stageTransition (n : ℕ)
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    NClasses n A B → NClasses (n + 1) A B :=
  Quotient.map (stageTransitionRepresentative n)
    (fun _ _ h ↦ stageTransitionRepresentative_respects n h)

@[simp]
theorem stageTransition_classOf (n : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (φ : HomN n A B) :
    stageTransition n A B (classOf n φ) =
      classOf (n + 1) (stageTransitionRepresentative n φ) :=
  rfl

end IteratedAsymptoticAlgebra
