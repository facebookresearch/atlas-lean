/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.TensorNetwork.GridExpansion
import Mathlib.Tactic.FinCases

namespace TensorNetwork

open Finset

def expansionLabeling : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) Nat := fun w w' =>
  if w = (0, 0) ∧ w' = (1, 1) then 1
  else if w = (1, 0) ∧ w' = (0, 1) then 1
  else 0

def expansionVertexWeight (w : Fin 2 × Fin 2) : ℤ :=
  if w = (0, 0) then 2
  else if w = (0, 1) then 3
  else if w = (1, 0) then 5
  else 7

def expansionTensor : Instance (Fin 2 × Fin 2) Nat := fun w h =>
  if h = expansionLabeling w then expansionVertexWeight w else 0

def expansionKernelLeft (x y _u _v : Nat) : ℤ := x + 2 * y

def expansionKernelRight (_x _y u v : Nat) : ℤ := 4 * u + 8 * v

def expansionKernel (x y u v : Nat) : ℤ :=
  expansionKernelLeft x y u v + expansionKernelRight x y u v

def expansionOriginalKernel (ω : (Fin 2 × Fin 2) × (Fin 2 × Fin 2)) :
    Nat → Nat → Nat → Nat → ℤ :=
  if ω ∈ gridRectangles (Fin 2) (Fin 2) then expansionKernel else fun _ _ _ _ => 37

def expansionKernelChoice
    (_ : { ω // ω ∈ gridRectangles (Fin 2) (Fin 2) }) (choice : Bool) :
    Nat → Nat → Nat → Nat → ℤ :=
  if choice then expansionKernelRight else expansionKernelLeft

example : rectangleApply expansionKernelLeft expansionLabeling (((0, 1), (0, 1))) = 1 := by
  decide

example : rectangleApply expansionKernelRight expansionLabeling (((0, 1), (0, 1))) = 4 := by
  decide

example : rectangleApply expansionKernel expansionLabeling (((0, 1), (0, 1))) = 5 := by
  decide

example : expansionOriginalKernel (((0, 0), (0, 0))) 0 0 0 0 = 37 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
example : gridValue {0, 1} {0} expansionTensor (fun _ => expansionKernelLeft) = 210 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
example : gridValue {0, 1} {0} expansionTensor (fun _ => expansionKernelRight) = 840 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
example : gridValue {0, 1} {0} expansionTensor expansionOriginalKernel = 1050 := by
  decide

example :
    gridValue {0, 1} {0} expansionTensor expansionOriginalKernel =
      ∑ choice ∈ Fintype.piFinset
          (fun _ : { ω // ω ∈ gridRectangles (Fin 2) (Fin 2) } => {false, true}),
        gridValue {0, 1} {0} expansionTensor fun ω =>
          if hω : ω ∈ gridRectangles (Fin 2) (Fin 2) then
            expansionKernelChoice ⟨ω, hω⟩ (choice ⟨ω, hω⟩)
          else expansionKernel := by
  apply gridValue_eq_sum_choices
  intro ω x y u v
  simp [expansionOriginalKernel, ω.property, expansionKernel, expansionKernelChoice]

def expansionUnitTensor {ρ γ : Type*} : Instance (ρ × γ) Nat := fun _ _ => 1

private def noRectangleKernelChoice
    (_ : {ω // ω ∈ gridRectangles (Fin 1) (Fin 1)}) (choice : Fin 0) :
    Nat → Nat → Nat → Nat → ℤ :=
  Fin.elim0 choice

example :
    (Fintype.piFinset
      (fun _ : {ω // ω ∈ gridRectangles (Fin 1) (Fin 1)} => (∅ : Finset (Fin 0)))).card =
        1 := by
  decide

example :
    gridValue {0} {0} (expansionUnitTensor (ρ := Fin 1) (γ := Fin 1))
      (fun _ _ _ _ _ => 37) = 1 := by
  decide

example :
    gridValue {0} {0} (expansionUnitTensor (ρ := Fin 1) (γ := Fin 1))
        (fun _ _ _ _ _ => 37) =
      ∑ choice ∈ Fintype.piFinset
          (fun _ : {ω // ω ∈ gridRectangles (Fin 1) (Fin 1)} => (∅ : Finset (Fin 0))),
        gridValue {0} {0} (expansionUnitTensor (ρ := Fin 1) (γ := Fin 1)) fun ω =>
          if hω : ω ∈ gridRectangles (Fin 1) (Fin 1) then
            noRectangleKernelChoice ⟨ω, hω⟩ (choice ⟨ω, hω⟩)
          else fun _ _ _ _ => 37 := by
  apply gridValue_eq_sum_choices
  rintro ⟨⟨⟨a, b⟩, ⟨i, j⟩⟩, hω⟩
  fin_cases a
  fin_cases b
  simp [gridRectangles, orderedPairs] at hω

def zeroExpansionKernel (_x _y _u _v : Nat) : ℤ := 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
example : gridValue {0, 1} {0} expansionTensor (fun _ => zeroExpansionKernel) = 0 := by
  decide

example :
    (Fintype.piFinset
      (fun _ : {ω // ω ∈ gridRectangles (Fin 2) (Fin 2)} => (∅ : Finset Unit))).card =
        0 := by
  decide

example :
    (∑ _choice ∈ Fintype.piFinset
        (fun _ : {ω // ω ∈ gridRectangles (Fin 2) (Fin 2)} => (∅ : Finset Unit)),
      gridValue {0, 1} {0} expansionTensor fun ω =>
        if _hω : ω ∈ gridRectangles (Fin 2) (Fin 2) then zeroExpansionKernel
        else expansionOriginalKernel ω) = 0 := by
  let _ : Nonempty {ω // ω ∈ gridRectangles (Fin 2) (Fin 2)} :=
    ⟨⟨(((0, 1), (0, 1))), by decide⟩⟩
  rw [Fintype.piFinset_empty]
  simp

def zeroExpansionTensor : Instance (Fin 1 × Fin 1) Nat := fun _ _ => 0

example : gridValue {0} {0} zeroExpansionTensor (fun _ _ _ _ _ => 37) = 0 := by
  simp [gridValue, zeroExpansionTensor]

private def sourceStylePattern {ρ γ : Type*} [Fintype ρ] [LinearOrder ρ]
    [Fintype γ] [LinearOrder γ]
    (choice : {ω // ω ∈ gridRectangles ρ γ} → Nat) : ((ρ × ρ) × (γ × γ)) → Nat :=
  fun ω => if hω : ω ∈ gridRectangles ρ γ then choice ⟨ω, hω⟩ else 0

private example {ρ γ : Type*} [Fintype ρ] [LinearOrder ρ]
    [Fintype γ] [LinearOrder γ]
    (choice : {ω // ω ∈ gridRectangles ρ γ} → Nat) (ω : (ρ × ρ) × (γ × γ))
    (hω : ω ∉ gridRectangles ρ γ) : sourceStylePattern choice ω = 0 := by
  simp [sourceStylePattern, hω]

private example
    (choice : {ω // ω ∈ gridRectangles (Fin 2) (Fin 2)} → Nat)
    (hchoice : choice ∈ Fintype.piFinset fun _ => range 1) :
    sourceStylePattern choice = fun _ => 0 := by
  funext ω
  by_cases hω : ω ∈ gridRectangles (Fin 2) (Fin 2)
  · have hc := (Fintype.mem_piFinset.mp hchoice) ⟨ω, hω⟩
    simp at hc
    rw [sourceStylePattern, dite_eq_left hω]
    exact hc
  · simp [sourceStylePattern, hω]

private example {ρ γ A : Type*} [Fintype ρ] [LinearOrder ρ]
    [Fintype γ] [LinearOrder γ] [DecidableEq A] (n : Nat)
    (labels diagonalLabels : Finset A) (R : Instance (ρ × γ) A)
    (G : ((ρ × ρ) × (γ × γ)) → A → A → A → A → ℤ)
    (K : {ω // ω ∈ gridRectangles ρ γ} → Nat → A → A → A → A → ℤ)
    (hG : ∀ (ω : {ω // ω ∈ gridRectangles ρ γ}) x y u v,
      G ω x y u v = ∑ k ∈ range (n + 1), K ω k x y u v) :
    gridValue labels diagonalLabels R G =
      ∑ choice ∈ Fintype.piFinset (fun _ : {ω // ω ∈ gridRectangles ρ γ} =>
          range (n + 1)),
        gridValue labels diagonalLabels R fun ω =>
          if hω : ω ∈ gridRectangles ρ γ then K ⟨ω, hω⟩ (choice ⟨ω, hω⟩) else G ω := by
  exact gridValue_eq_sum_choices labels diagonalLabels R G _ K hG

#print axioms gridValue_eq_sum_choices

end TensorNetwork
