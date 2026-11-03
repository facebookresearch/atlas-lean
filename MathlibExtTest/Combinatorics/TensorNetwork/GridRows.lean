/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.TensorNetwork.GridRows

namespace TensorNetwork

open Finset

variable {ρ γ A T : Type*}

private def asymmetricLabeling : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) Nat := fun w w' =>
  if w = (0, 0) ∧ w' = (1, 1) then 1
  else if w = (1, 0) ∧ w' = (0, 1) then 1
  else 0

private def asymmetricVertexWeight (w : Fin 2 × Fin 2) : ℤ :=
  if w = (0, 0) then 2
  else if w = (0, 1) then 3
  else if w = (1, 0) then 5
  else 7

private def asymmetricTensor : Instance (Fin 2 × Fin 2) Nat := fun w h =>
  if h = asymmetricLabeling w then asymmetricVertexWeight w else 0

private def asymmetricKernel (x y u v : Nat) : ℤ :=
  x + 2 * y + 4 * u + 8 * v

private def twoCuts (_ : (Fin 2 × Fin 2) × (Fin 2 × Fin 2)) : Finset Bool :=
  {false, true}

private def asymmetricTop (_ : (Fin 2 × Fin 2) × (Fin 2 × Fin 2))
    (x y : Nat) (θ : Bool) : ℤ :=
  if θ then 1 else x + 2 * y

private def asymmetricBottom (_ : (Fin 2 × Fin 2) × (Fin 2 × Fin 2))
    (u v : Nat) (θ : Bool) : ℤ :=
  if θ then 4 * u + 8 * v else 1

private theorem asymmetric_factors (ω : (Fin 2 × Fin 2) × (Fin 2 × Fin 2))
    (x y u v : Nat) :
    asymmetricKernel x y u v =
      ∑ θ ∈ twoCuts ω, asymmetricTop ω x y θ * asymmetricBottom ω u v θ := by
  simp [asymmetricKernel, twoCuts, asymmetricTop, asymmetricBottom]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem asymmetricGridValue :
    gridValue {0, 1} {0} asymmetricTensor (fun _ => asymmetricKernel) = 1050 := by
  decide

private example : ∏ w, asymmetricVertexWeight w = 210 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private example :
    (gridRowNetwork {0, 1} {0} asymmetricTensor twoCuts asymmetricTop
      asymmetricBottom (fun _ => 1) 1).value = 1050 := by
  rw [gridRowNetwork_value {0, 1} {0} asymmetricTensor (fun _ => asymmetricKernel)
    twoCuts asymmetricTop asymmetricBottom (fun _ => 1) 1 asymmetric_factors]
  exact asymmetricGridValue

private def oneTensor : Instance (Fin 2 × Fin 2) Nat := fun _ _ => 1

private def horizontalMismatch : Fin 2 → Fin 2 × Fin 2 → Nat := fun i w =>
  if i = 0 ∧ w = (0, 1) then 0
  else if i = 1 ∧ w = (0, 0) then 1
  else 0

private example :
    (gridRowNetwork {0, 1} {0} oneTensor twoCuts asymmetricTop asymmetricBottom
      (fun _ => 1) 1).W 0 horizontalMismatch = 0 := by
  decide

private def diagonalState : Fin 2 → Fin 2 × Fin 2 → Nat := fun i w =>
  if w = (0, i) then 1 else 0

private def diagonalTensor : Instance (Fin 2 × Fin 2) Nat := fun w h =>
  if h w = 1 then 2 else 0

private example :
    diagonalState ∈
      (gridRowNetwork {0} {0, 1} diagonalTensor twoCuts asymmetricTop asymmetricBottom
        (fun _ => 1) 1).S 0 := by
  decide

private example :
    (gridRowNetwork {0} {0, 1} diagonalTensor twoCuts asymmetricTop asymmetricBottom
      (fun _ => 1) 1).W 0 diagonalState = 4 := by
  decide

private def zeroState : Fin 2 → Fin 2 × Fin 2 → Nat := fun _ _ => 0

private def zeroRowLabel :
    (Fin 2 → Nat) × ({k : Fin 2 × Fin 2 // k ∈ orderedPairs (Fin 2)} → Bool) :=
  (fun _ => 0, fun _ => false)

private def constantTwoBottom
    (_ : (Fin 2 × Fin 2) × (Fin 2 × Fin 2)) (_ _ : Nat) (_ : Bool) : ℤ :=
  2

private example :
    (gridRowNetwork {0} {0} oneTensor twoCuts asymmetricTop constantTwoBottom
      (fun _ => 1) 1).f 0 0 zeroState zeroRowLabel = 2 := by
  decide

private def noCuts (_ : (Fin 2 × Fin 2) × (Fin 2 × Fin 2)) : Finset Bool := ∅

private example :
    (gridRowNetwork {0} {0} oneTensor noCuts asymmetricTop asymmetricBottom
      (fun _ => 1) 1).interaction 0 1 zeroState zeroState = 0 := by
  decide

private def outsideState : Fin 1 → Fin 2 × Fin 1 → Nat := fun _ _ => 7

private def noColumnCuts (_ : (Fin 2 × Fin 2) × (Fin 1 × Fin 1)) : Finset Bool :=
  {false}

private def constantOneTop
    (_ : (Fin 2 × Fin 2) × (Fin 1 × Fin 1)) (_ _ : Nat) (_ : Bool) : ℤ :=
  1

private def constantOneBottom
    (_ : (Fin 2 × Fin 2) × (Fin 1 × Fin 1)) (_ _ : Nat) (_ : Bool) : ℤ :=
  1

private def oneColumnTensor : Instance (Fin 2 × Fin 1) Nat := fun _ _ => 1

private def insideOneColumnState : Fin 1 → Fin 2 × Fin 1 → Nat := fun _ _ => 0

private def oneColumnKernel
    (_ : (Fin 2 × Fin 2) × (Fin 1 × Fin 1)) (_ _ _ _ : Nat) : ℤ :=
  1

private theorem oneColumn_factors (ω : (Fin 2 × Fin 2) × (Fin 1 × Fin 1))
    (x y u v : Nat) :
    oneColumnKernel ω x y u v =
      ∑ θ ∈ noColumnCuts ω, constantOneTop ω x y θ * constantOneBottom ω u v θ := by
  simp [oneColumnKernel, noColumnCuts, constantOneTop, constantOneBottom]

private example :
    (gridRowNetwork {0} {0} oneColumnTensor noColumnCuts constantOneTop
      constantOneBottom (fun _ => 1) 1).interaction
        0 1 insideOneColumnState outsideState = 0 := by
  rw [gridRowNetwork_interaction_of_mem {0} {0} oneColumnTensor noColumnCuts
    constantOneTop constantOneBottom (fun _ => 1) 1 oneColumnKernel oneColumn_factors
    (a := (0 : Fin 2)) (b := (1 : Fin 2)) (by decide)
    insideOneColumnState outsideState (by decide)]
  decide

private example :
    outsideState ∉
      (gridRowNetwork {0} {0} oneColumnTensor noColumnCuts constantOneTop
        constantOneBottom (fun _ => 1) 1).S 0 := by
  decide

private example :
    (gridRowNetwork {0} {0} oneColumnTensor noColumnCuts constantOneTop
      constantOneBottom (fun _ => 1) 1).interaction 0 1 outsideState outsideState = 0 := by
  decide

private example :
    (gridRowNetwork {0} {0} oneTensor twoCuts asymmetricTop asymmetricBottom
      (fun _ => 1) 1).totalCapacity = 6 := by
  decide

private def emptyRowTensor : Instance (Empty × Fin 2) Nat := fun w => nomatch w

private def emptyRowCuts (_ : (Empty × Empty) × (Fin 2 × Fin 2)) : Finset Bool :=
  {false}

private def emptyRowFactor
    (_ : (Empty × Empty) × (Fin 2 × Fin 2)) (_ _ : Nat) (_ : Bool) : ℤ :=
  1

private example :
    (gridRowNetwork {0} {0} emptyRowTensor emptyRowCuts emptyRowFactor emptyRowFactor
      (fun _ => 0) 0).value = 1 := by
  decide

private def emptyColumnTensor : Instance (Fin 2 × Empty) Nat := fun w => nomatch w.2

private def emptyColumnCuts (_ : (Fin 2 × Fin 2) × (Empty × Empty)) : Finset Bool :=
  {false}

private def emptyColumnFactor
    (_ : (Fin 2 × Fin 2) × (Empty × Empty)) (_ _ : Nat) (_ : Bool) : ℤ :=
  1

private example :
    (gridRowNetwork {0} {0} emptyColumnTensor emptyColumnCuts emptyColumnFactor
      emptyColumnFactor (fun _ => 0) 0).value = 1 := by
  decide

private def activeToPadded [Fintype γ] [LinearOrder γ]
    (t₀ : T) (θ : {k : γ × γ // k ∈ orderedPairs γ} → T) : γ × γ → T :=
  fun k => if hk : k ∈ orderedPairs γ then θ ⟨k, hk⟩ else t₀

private def paddedToActive [Fintype γ] [LinearOrder γ]
    (θ : γ × γ → T) : {k : γ × γ // k ∈ orderedPairs γ} → T :=
  fun k => θ k

private theorem paddedToActive_activeToPadded [Fintype γ] [LinearOrder γ]
    (t₀ : T) (θ : {k : γ × γ // k ∈ orderedPairs γ} → T) :
    paddedToActive (activeToPadded t₀ θ) = θ := by
  funext k
  simp [paddedToActive, activeToPadded, k.property]

private theorem activeToPadded_paddedToActive [Fintype γ] [LinearOrder γ]
    (t₀ : T) (θ : γ × γ → T)
    (hθ : ∀ k, k ∉ orderedPairs γ → θ k = t₀) :
    activeToPadded t₀ (paddedToActive θ) = θ := by
  funext k
  by_cases hk : k ∈ orderedPairs γ
  · simp [activeToPadded, paddedToActive, hk]
  · simp [activeToPadded, hk, hθ k hk]

private theorem active_mem_iff_padded_mem [Fintype γ] [LinearOrder γ]
    (cutLabels : γ × γ → Finset T) (t₀ : T)
    (θ : {k : γ × γ // k ∈ orderedPairs γ} → T) :
    θ ∈ Fintype.piFinset
      (fun k : {k : γ × γ // k ∈ orderedPairs γ} => cutLabels k) ↔
      activeToPadded t₀ θ ∈
        Fintype.piFinsetOn (fun k : γ × γ => k ∈ orderedPairs γ) cutLabels t₀ := by
  rw [Fintype.mem_piFinset, Fintype.mem_piFinsetOn]
  constructor
  · intro h k
    constructor
    · intro hk
      simpa [activeToPadded, hk] using h ⟨k, hk⟩
    · intro hk
      simp [activeToPadded, hk]
  · intro h k
    simpa [activeToPadded, k.property] using (h k).1 k.property

private example [Fintype A] [DecidableEq A]
    [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ]
    (R : Instance (ρ × γ) A)
    (G : ((ρ × ρ) × (γ × γ)) → A → A → A → A → ℤ)
    (cutLabels : ((ρ × ρ) × (γ × γ)) → Finset T)
    (top bottom : ((ρ × ρ) × (γ × γ)) → A → A → T → ℤ)
    (cap : ((ρ × ρ) × (γ × γ)) → ℕ) (L : ℕ)
    (hG : ∀ ω x y u v,
      G ω x y u v = ∑ θ ∈ cutLabels ω, top ω x y θ * bottom ω u v θ) :
    (gridRowNetwork univ univ R cutLabels top bottom cap L).value =
      gridValue univ univ R G :=
  gridRowNetwork_value univ univ R G cutLabels top bottom cap L hG

end TensorNetwork
