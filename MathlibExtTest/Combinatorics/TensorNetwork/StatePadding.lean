/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.TensorNetwork.StatePadding

namespace TensorNetwork

open Finset

def paddingSource : Factored (Fin 2) Bool Unit where
  S _ := {false, true}
  W v z := if v = 0 then if z then -3 else 2 else if z then 7 else 5
  Θ _ _ := {()}
  f _ _ _ _ := 1
  c a b := if a = b then 0 else 1

def padState (_ : Fin 2) (z : Bool) : Nat := if z then 2 else 0

def paddingTarget : Factored (Fin 2) Nat Unit where
  S _ := {0, 2, 9}
  W v y := if y = 0 then paddingSource.W v false
    else if y = 2 then paddingSource.W v true else 0
  Θ _ _ := {()}
  f _ _ y _ := if y = 9 then 4 else 1
  c a b := if a = b then 99 else 1

theorem paddingCertificate : Factored.StatePadding paddingSource paddingTarget padState where
  maps := by
    intro a z _
    cases z <;> simp [padState, paddingTarget]
  inj := by
    intro a z _ z' _ h
    cases z <;> cases z' <;> simp_all [padState]
  off := by
    intro a y _ h
    have h0 : y ≠ 0 := by
      simpa [padState, eq_comm] using h false (by simp [paddingSource])
    have h2 : y ≠ 2 := by
      simpa [padState, eq_comm] using h true (by simp [paddingSource])
    simp [paddingTarget, h0, h2]
  W := by
    intro a z _
    cases z <;> simp [paddingTarget, padState]
  interaction := by
    intro a b _ z _ z' _
    cases z <;> cases z' <;>
      norm_num [Factored.interaction, Factored.labelSet, paddingSource, paddingTarget, padState]
  c := by
    intro a b h
    simp [paddingSource, paddingTarget, h]
  f := by
    intro a b _ z _ θ _
    cases z <;> simp [paddingSource, paddingTarget, padState]

example : paddingTarget.value = paddingSource.value ∧
    paddingTarget.totalCapacity = paddingSource.totalCapacity :=
  paddingCertificate.value_totalCapacity

example : paddingSource.value = -12 := by decide
example : paddingTarget.value = -12 := by decide
example : paddingSource.totalCapacity = 2 := by decide
example : paddingTarget.totalCapacity = 2 := by decide
example : paddingSource.c 0 0 = 0 ∧ paddingTarget.c 0 0 = 99 := by decide
example : paddingTarget.f 0 1 9 () = 4 := by decide

def nonzeroJunk : Factored (Fin 2) Nat Unit :=
  { paddingTarget with W := fun v y => if v = 0 ∧ y = 9 then 1 else paddingTarget.W v y }

example : nonzeroJunk.value = 36 := by decide

example : ¬ Factored.StatePadding paddingSource nonzeroJunk padState := by
  intro h
  have hz := h.off 0 9 (by decide) (by intro z _; cases z <;> decide)
  norm_num [nonzeroJunk] at hz

def noVerticesSource : Factored (Fin 0) Bool Unit where
  S a := Fin.elim0 a
  W a := Fin.elim0 a
  Θ a := Fin.elim0 a
  f a := Fin.elim0 a
  c a := Fin.elim0 a

def noVerticesTarget : Factored (Fin 0) Nat Unit where
  S a := Fin.elim0 a
  W a := Fin.elim0 a
  Θ a := Fin.elim0 a
  f a := Fin.elim0 a
  c a := Fin.elim0 a

def noVerticesPad (a : Fin 0) : Bool → Nat := Fin.elim0 a

theorem noVerticesCertificate :
    Factored.StatePadding noVerticesSource noVerticesTarget noVerticesPad where
  maps := by
    intro a
    exact Fin.elim0 a
  inj := by
    intro a
    exact Fin.elim0 a
  off := by
    intro a
    exact Fin.elim0 a
  W := by
    intro a
    exact Fin.elim0 a
  interaction := by
    intro a
    exact Fin.elim0 a
  c := by
    intro a
    exact Fin.elim0 a
  f := by
    intro a
    exact Fin.elim0 a

example : noVerticesSource.value = 1 ∧ noVerticesTarget.value = 1 := by
  simp [Factored.value, orderedPairs]

example : noVerticesTarget.value = noVerticesSource.value ∧
    noVerticesTarget.totalCapacity = noVerticesSource.totalCapacity :=
  noVerticesCertificate.value_totalCapacity

def noStatesSource : Factored (Fin 1) Bool Unit where
  S _ := ∅
  W _ _ := 5
  Θ _ _ := {()}
  f _ _ _ _ := 3
  c _ _ := 0

def noStatesTarget : Factored (Fin 1) Nat Unit where
  S _ := {9}
  W _ _ := 0
  Θ _ _ := {()}
  f _ _ _ _ := 4
  c _ _ := 99

theorem noStatesCertificate :
    Factored.StatePadding noStatesSource noStatesTarget (fun _ _ => 0) where
  maps := by simp [noStatesSource]
  inj := by simp [noStatesSource]
  off := by simp [noStatesTarget]
  W := by simp [noStatesSource]
  interaction := by simp [noStatesSource]
  c := by
    intro a b h
    exact (h (Subsingleton.elim a b)).elim
  f := by simp [noStatesSource]

example : noStatesSource.value = 0 := by decide
example : noStatesTarget.value = 0 := by decide
example : noStatesTarget.value = noStatesSource.value ∧
    noStatesTarget.totalCapacity = noStatesSource.totalCapacity :=
  noStatesCertificate.value_totalCapacity

-- This raw kernel is independent of the fixture's rank-one, one-label interaction.
def rawSourceKernel (_ _ : Fin 2) (z z' : Bool) : ℤ := if z = z' then 1 else 0

def rawTargetKernel (_ _ : Fin 2) (y y' : Nat) : ℤ :=
  if y = 9 ∨ y' = 9 then 7 else if y = y' then 1 else 0

example : rawSourceKernel 0 1 false false * rawSourceKernel 0 1 true true -
    rawSourceKernel 0 1 false true * rawSourceKernel 0 1 true false = 1 := by decide

example : rawTargetKernel 0 1 9 0 = 7 := by decide

example :
    (∑ y ∈ Fintype.piFinset paddingTarget.S, (∏ a, paddingTarget.W a (y a)) *
      ∏ p ∈ orderedPairs (Fin 2), rawTargetKernel p.1 p.2 (y p.1) (y p.2)) =
    ∑ z ∈ Fintype.piFinset paddingSource.S, (∏ a, paddingSource.W a (z a)) *
      ∏ p ∈ orderedPairs (Fin 2), rawSourceKernel p.1 p.2 (z p.1) (z p.2) := by
  apply sum_statePadding _ _ _ _ _ _ padState paddingCertificate.maps
    paddingCertificate.inj paddingCertificate.off paddingCertificate.W
  intro a b _ z _ z' _
  cases z <;> cases z' <;> simp [rawSourceKernel, rawTargetKernel, padState]

example :
    (∑ z ∈ Fintype.piFinset paddingSource.S, (∏ a, paddingSource.W a (z a)) *
      ∏ p ∈ orderedPairs (Fin 2), rawSourceKernel p.1 p.2 (z p.1) (z p.2)) = -11 := by
  decide

example :
    (∑ y ∈ Fintype.piFinset paddingTarget.S, (∏ a, paddingTarget.W a (y a)) *
      ∏ p ∈ orderedPairs (Fin 2), rawTargetKernel p.1 p.2 (y p.1) (y p.2)) = -11 := by
  decide

-- Complete expansion of the source statement on Fin g and Bool-list states. The independent
-- kernels, capacity clause, and redundant directed-factor clause are all retained.
example {g : Nat} (S₀ S₁ : Fin g → Finset (List Bool))
    (W₀ W₁ : Fin g → List Bool → ℤ)
    (Ψ₀ Ψ₁ : Fin g → Fin g → List Bool → List Bool → ℤ)
    (c₀ c₁ : Fin g → Fin g → Nat)
    (f₀ f₁ : Fin g → Fin g → List Bool → List Bool → ℤ)
    (pad : Fin g → List Bool → List Bool)
    (maps : ∀ a, ∀ z ∈ S₀ a, pad a z ∈ S₁ a)
    (inj : ∀ a, ∀ z ∈ S₀ a, ∀ z' ∈ S₀ a, pad a z = pad a z' → z = z')
    (off : ∀ a, ∀ y ∈ S₁ a, (∀ z ∈ S₀ a, pad a z ≠ y) → W₁ a y = 0)
    (weights : ∀ a, ∀ z ∈ S₀ a, W₁ a (pad a z) = W₀ a z)
    (kernels : ∀ a b, a ≠ b → ∀ z ∈ S₀ a, ∀ z' ∈ S₀ b,
      Ψ₁ a b (pad a z) (pad b z') = Ψ₀ a b z z')
    (capacities : ∀ a b, a ≠ b → c₁ a b = c₀ a b)
    (_factors : ∀ a b, a ≠ b → ∀ z ∈ S₀ a, ∀ θ : List Bool, θ.length = c₀ a b →
      f₁ a b (pad a z) θ = f₀ a b z θ) :
    ((∑ y ∈ Fintype.piFinset S₁, (∏ a, W₁ a (y a)) *
      ∏ p ∈ (univ : Finset (Fin g × Fin g)).filter (fun p => p.1 < p.2),
        Ψ₁ p.1 p.2 (y p.1) (y p.2)) =
    ∑ z ∈ Fintype.piFinset S₀, (∏ a, W₀ a (z a)) *
      ∏ p ∈ (univ : Finset (Fin g × Fin g)).filter (fun p => p.1 < p.2),
        Ψ₀ p.1 p.2 (z p.1) (z p.2)) ∧
    (∑ a, ∑ b ∈ univ.erase a, c₁ a b) = ∑ a, ∑ b ∈ univ.erase a, c₀ a b := by
  constructor
  · exact sum_statePadding S₀ S₁ W₀ W₁ Ψ₀ Ψ₁ pad maps inj off weights kernels
  · exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb =>
      capacities a b (Finset.ne_of_mem_erase hb).symm

-- Constant padding on Nat is not globally injective, but is injective on the sole active state.
example :
    (∑ y ∈ Fintype.piFinset (fun _ : Fin 1 => ({0, 9} : Finset Nat)),
      (∏ a : Fin 1, (if y a = 0 then 2 else 0 : ℤ)) *
        ∏ _p ∈ orderedPairs (Fin 1), (3 : ℤ)) =
    ∑ _z ∈ Fintype.piFinset (fun _ : Fin 1 => ({0} : Finset Nat)),
      (∏ _a : Fin 1, (2 : ℤ)) * ∏ _p ∈ orderedPairs (Fin 1), (7 : ℤ) := by
  apply sum_statePadding (fun _ : Fin 1 => ({0} : Finset Nat)) (fun _ => {0, 9})
    (fun _ _ => 2) (fun _ y => if y = 0 then 2 else 0)
    (fun _ _ _ _ => 7) (fun _ _ _ _ => 3) (fun _ _ => 0)
  · simp
  · intro a z hz z' hz' _
    simp only [mem_singleton] at hz hz'
    exact hz.trans hz'.symm
  · intro a y _ h
    have h0 : (0 : Nat) ≠ y := h 0 (by simp)
    simp [Ne.symm h0]
  · simp
  · intro a b h
    exact (h (Subsingleton.elim a b)).elim

example :
    (∑ y ∈ Fintype.piFinset (fun _ : Fin 1 => ({0, 9} : Finset Nat)),
      (∏ a : Fin 1, (if y a = 0 then 2 else 0 : ℤ)) *
        ∏ _p ∈ orderedPairs (Fin 1), (3 : ℤ)) = 2 := by decide

#print axioms sum_statePadding
#print axioms Factored.StatePadding
#print axioms Factored.StatePadding.value_totalCapacity

end TensorNetwork
