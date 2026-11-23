/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.TensorNetwork.GridRowBounds

namespace TensorNetwork

open Finset

variable {ρ γ A T : Type*}

private def oneTensor {ρ γ : Type*} : Instance (ρ × γ) Nat := fun _ _ => 1

private def singletonCuts {ρ γ : Type*}
    (_ : (ρ × ρ) × (γ × γ)) : Finset Bool :=
  {false}

private def oneFactor {ρ γ : Type*}
    (_ : (ρ × ρ) × (γ × γ)) (_ _ : Nat) (_ : Bool) : ℤ :=
  1

private def oneKernel {ρ γ : Type*}
    (_ : (ρ × ρ) × (γ × γ)) (_ _ _ _ : Nat) : ℤ :=
  1

private def zeroCap {ρ γ : Type*} (_ : (ρ × ρ) × (γ × γ)) : ℕ :=
  0

private def oneCap {ρ γ : Type*} (_ : (ρ × ρ) × (γ × γ)) : ℕ :=
  1

private theorem one_factors {ρ γ : Type*} (ω : (ρ × ρ) × (γ × γ))
    (x y u v : Nat) :
    oneKernel ω x y u v =
      ∑ θ ∈ singletonCuts ω, oneFactor ω x y θ * oneFactor ω u v θ := by
  simp [oneKernel, singletonCuts, oneFactor]

private def boundedNetwork :=
  gridRowNetwork (ρ := Fin 2) (γ := Fin 2) {0} {0, 1} oneTensor singletonCuts
    oneFactor oneFactor oneCap 1

private theorem boundedNetwork_shaped : boundedNetwork.Shaped 8 := by
  exact gridRowNetwork_shaped (g := 2) (L := 1) (m := 1)
    (by decide) (by decide) (by decide) {0} {0, 1} (by decide) (by decide)
    oneTensor singletonCuts oneFactor oneFactor oneCap (by simp [singletonCuts, oneCap])
    (by simp [oneCap])

private theorem boundedNetwork_sized : boundedNetwork.Sized 8 0 := by
  exact gridRowNetwork_sized (g := 2) (L := 1) (m := 1) (B := 0) (b := 0)
    (by decide) (by decide) (by decide) {0} {0, 1} (by decide) (by decide)
    oneTensor (by simp [oneTensor]) oneKernel singletonCuts oneFactor oneFactor oneCap
    one_factors (by simp [singletonCuts, oneCap]) (by simp [oneCap])
    (by simp [oneFactor]) (by simp [oneFactor]) (by simp [oneKernel])

private def outsideState : Fin 2 → Fin 2 × Fin 2 → Nat := fun _ _ => 7

private def outsideRowLabel :
    (Fin 2 → Nat) × ({k : Fin 2 × Fin 2 // k ∈ orderedPairs (Fin 2)} → Bool) :=
  (fun _ => 7, fun _ => true)

private example : (boundedNetwork.S 0).card = 4 := by
  decide

private example : boundedNetwork.c 0 1 = 3 := by
  decide

private example : boundedNetwork.c 0 1 ≤ 4 := by
  exact gridRowNetwork_capacity_le (g := 2) (L := 1) (m := 1)
    (by decide) (by decide) {0} {0, 1} oneTensor singletonCuts oneFactor oneFactor
    oneCap (by simp [oneCap]) 0 1

private example : |boundedNetwork.W 0 outsideState| ≤ 1 :=
  boundedNetwork_sized.abs_W 0 outsideState

private example : true ∉ singletonCuts ((0, 0), (0, 1)) := by
  simp [singletonCuts]

private example : boundedNetwork.f 0 0 outsideState outsideRowLabel = 1 := by
  decide

private example : |boundedNetwork.f 0 0 outsideState outsideRowLabel| ≤ 1 :=
  boundedNetwork_sized.abs_f 0 0 outsideState outsideRowLabel

private example : boundedNetwork.interaction 0 1 outsideState outsideState = 0 := by
  decide

private example : |boundedNetwork.interaction 0 1 outsideState outsideState| ≤ 1 :=
  boundedNetwork_sized.abs_interaction 0 1 outsideState outsideState (by decide)

private example : boundedNetwork.totalCapacity = 6 := by
  change (gridRowNetwork (ρ := Fin 2) (γ := Fin 2) {0} {0, 1} oneTensor singletonCuts
    oneFactor oneFactor oneCap 1).totalCapacity = 6
  rw [gridRowNetwork_totalCapacity (g := 2) (by decide) (by decide)]
  decide

private example :
    ¬(gridRowNetwork (ρ := Fin 2) (γ := Fin 1) {0} {0} oneTensor singletonCuts
      oneFactor oneFactor zeroCap 1).c 0 1 ≤ 1 ^ 2 * (0 * 1) := by
  decide

private def emptyTensor : Instance (Empty × Empty) Nat := fun w => nomatch w.1

private def emptyCuts (_ : (Empty × Empty) × (Empty × Empty)) : Finset Bool :=
  {false}

private def emptyFactor
    (_ : (Empty × Empty) × (Empty × Empty)) (_ _ : Nat) (_ : Bool) : ℤ :=
  1

private def emptyKernel
    (_ : (Empty × Empty) × (Empty × Empty)) (_ _ _ _ : Nat) : ℤ :=
  1

private def emptyCap (_ : (Empty × Empty) × (Empty × Empty)) : ℕ :=
  0

private theorem empty_factors (ω : (Empty × Empty) × (Empty × Empty))
    (x y u v : Nat) :
    emptyKernel ω x y u v =
      ∑ θ ∈ emptyCuts ω, emptyFactor ω x y θ * emptyFactor ω u v θ := by
  simp [emptyKernel, emptyCuts, emptyFactor]

private example :
    (gridRowNetwork ∅ ∅ emptyTensor emptyCuts emptyFactor emptyFactor emptyCap 0).Sized 0 0 := by
  simpa using gridRowNetwork_sized (g := 0) (L := 0) (m := 1) (B := 0) (b := 0)
    (ρ := Empty) (γ := Empty) (by decide) (by decide) (by decide) ∅ ∅ (by decide)
    (by decide) emptyTensor (by intro w; nomatch w.1) emptyKernel emptyCuts emptyFactor
    emptyFactor emptyCap empty_factors (by intro ω; nomatch ω.1.1)
    (by intro ω; nomatch ω.1.1) (by intro ω; nomatch ω.1.1)
    (by intro ω; nomatch ω.1.1) (by intro ω; nomatch ω.1.1)

private theorem zeroBitNetwork_sized :
    (gridRowNetwork (ρ := Fin 1) (γ := Fin 1) {0} {0} oneTensor singletonCuts
      oneFactor oneFactor zeroCap 0).Sized 0 0 := by
  simpa using gridRowNetwork_sized (g := 1) (L := 0) (m := 1) (B := 0) (b := 0)
    (by decide) (by decide) (by decide) {0} {0} (by decide) (by decide)
    oneTensor (by simp [oneTensor]) oneKernel singletonCuts oneFactor oneFactor zeroCap
    one_factors (by simp [singletonCuts, zeroCap]) (by simp [zeroCap])
    (by simp [oneFactor]) (by simp [oneFactor]) (by simp [oneKernel])

private example [Fintype A] [DecidableEq A]
    [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ]
    {g L m : ℕ} (hm : 1 ≤ m) (hρ : Fintype.card ρ = g)
    (hγ : Fintype.card γ = g) (hA : Fintype.card A = 2 ^ L)
    (R : Instance (ρ × γ) A)
    (cutLabels : ((ρ × ρ) × (γ × γ)) → Finset T)
    (top bottom : ((ρ × ρ) × (γ × γ)) → A → A → T → ℤ)
    (cap : ((ρ × ρ) × (γ × γ)) → ℕ)
    (hcut : ∀ ω, (cutLabels ω).card ≤ 2 ^ cap ω)
    (hcap : ∀ ω, cap ω ≤ 2 * m * L) :
    (gridRowNetwork univ univ R cutLabels top bottom cap L).Shaped
      (m * (g ^ 3 * L)) := by
  apply gridRowNetwork_shaped hm hρ hγ univ univ
  · simp [hA]
  · simp [hA]
  · exact hcut
  · exact hcap

private example [Fintype A] [DecidableEq A]
    [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ]
    {g L m B b : ℕ} (hm : 1 ≤ m) (hρ : Fintype.card ρ = g)
    (hγ : Fintype.card γ = g) (hA : Fintype.card A = 2 ^ L)
    (R : Instance (ρ × γ) A) (hR : ∀ w h, |R w h| ≤ 2 ^ B)
    (G : ((ρ × ρ) × (γ × γ)) → A → A → A → A → ℤ)
    (cutLabels : ((ρ × ρ) × (γ × γ)) → Finset T)
    (top bottom : ((ρ × ρ) × (γ × γ)) → A → A → T → ℤ)
    (cap : ((ρ × ρ) × (γ × γ)) → ℕ)
    (hfactor : ∀ ω x y u v,
      G ω x y u v = ∑ θ ∈ cutLabels ω, top ω x y θ * bottom ω u v θ)
    (hcut : ∀ ω, (cutLabels ω).card ≤ 2 ^ cap ω)
    (hcap : ∀ ω, cap ω ≤ 2 * m * L)
    (htop : ∀ ω x y θ, |top ω x y θ| ≤ 2 ^ b)
    (hbottom : ∀ ω u v θ, |bottom ω u v θ| ≤ 2 ^ b)
    (hG : ∀ ω x y u v, |G ω x y u v| ≤ 2 ^ b) :
    (gridRowNetwork univ univ R cutLabels top bottom cap L).Sized
      (m * (g ^ 3 * L)) (g * B + g ^ 2 * b) := by
  apply gridRowNetwork_sized hm hρ hγ univ univ
  · simp [hA]
  · simp [hA]
  · exact hR
  · exact hfactor
  · exact hcut
  · exact hcap
  · exact htop
  · exact hbottom
  · exact hG

#print axioms gridRowNetwork_capacity_le
#print axioms gridRowNetwork_shaped
#print axioms gridRowNetwork_sized
#print axioms gridRowNetwork_totalCapacity

end TensorNetwork
