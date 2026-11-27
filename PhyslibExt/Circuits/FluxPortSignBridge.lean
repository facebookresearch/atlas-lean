/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.ArcPortSigns
public import PhyslibExt.Circuits.BoxTerminalFlux
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Ring

/-!
# Box terminal flux to nodal injection: the port sign bridge

## i. Overview

An axis-aligned conducting box has six oriented faces with
parametrized face domains. The terminal outward current `I f` of face
`f` is the flux integral of the outward-normal current density over
the face domain, and charge continuity says the six outward fluxes
sum to minus the enclosed-charge rate
(`PhyslibExt.Circuits.BoxTerminalFlux`, which derives it for the box
`Set.Icc a b` from the local continuity law). The box is also a node `b`
of an oriented branch network with the electrical incidence of
`PhyslibExt.Circuits.ArcPortSigns`: `+1` at a branch tail, `-1` at
its head, and node current balance
`electricalIncidence tail head *ᵥ i = j` with an independently
supplied nodal injection `j`.

Each face is carried by its own port branch joining `b` to another
node, and every branch incident to `b` is a port branch
(`IsTerminalWiring`). A port branch may be oriented either way: its
branch current is the face's outward current when its tail is at the
box and the negated outward current when its head is at the box
(`portSign`, `IsFluxPortCurrent`). Under this sign conversion the net
branch outflow at the box node equals the sum of the six outward
terminal currents, hence minus the enclosed-charge rate. When the
outward fluxes balance (continuity at rate zero) the outflow is zero,
so current balance at the box holds with zero supplied injection, and
every injection compatible with current balance vanishes at the box.
For the box `Set.Icc lo hi` that balance is derived rather than
assumed: constant enclosed charge and the local continuity law give it
through `boxTerminalCurrents_sum_eq_zero_of_constantCharge`. Reversing
the sign of a single port current with nonzero flux breaks that
equality.

This is a representation bridge between the two conventions, not an
identification of arbitrary electromagnetic fields with a lumped
circuit. No second conservation law is derived: continuity enters
through the `chargeContinuity` premise of the face-flux interface
`sum_terminalCurrent_eq_neg_chargeRate`, or, for the box, through the
local continuity law of `PhyslibExt.Circuits.BoxTerminalFlux`.

## ii. Key results

- `electricalIncidence_mulVec_box_eq_sum`: the electrical-incidence
  outflow at the box node is the sum of the outward terminal
  currents, for any orientation of the port branches.
- `injection_box_eq_neg_chargeRate`: every nodal injection compatible
  with current balance equals minus the enclosed-charge rate at the
  box node.
- `fluxPortSignBridge_correct`: the headline statement, assuming the
  zero flux balance (continuity at rate zero); the outflow is the flux
  sum, that sum is zero, and every compatible injection vanishes at the
  box node.
- `boxInjection_eq_zero_of_constantCharge`: for the box `Set.Icc lo hi`,
  constant enclosed charge and the local continuity law give zero
  outflow and zero injection at the box node.
- `reversedPortSign_breaks_injection`: negating one port current with
  nonzero flux makes the box outflow `-2 * I f₀`, which is nonzero.

## iii. Table of contents

- A. Terminal wiring and the sign conversion
- B. Net outflow and injection at the box node
- C. Validation

## iv. References

- L. O. Chua, C. A. Desoer and E. S. Kuh, *Linear and Nonlinear
  Circuits*, McGraw-Hill, 1987: the reduced incidence matrix,
  Kirchhoff's current law at a node, and port orientation.
- D. J. Griffiths, *Introduction to Electrodynamics*, fourth
  edition, Cambridge University Press, 2017: the continuity equation
  relating current flux through a closed surface to the rate of
  change of the enclosed charge.
-/

@[expose] public section

namespace PhyslibExt.Circuits.FluxPortSignBridge

open Matrix
open PhyslibExt.Circuits.ArcPortSigns
open PhyslibExt.Circuits.BoxTerminalFlux

/-! ## A. Terminal wiring and the sign conversion -/

/-- The six box terminals are wired into the branch network at the box node `b`: each face `f`
is carried by its own port branch `port f`, which has exactly one endpoint at `b` and is not a
loop, and every branch with an endpoint at `b` is a port branch. -/
structure IsTerminalWiring {V : Type*} {E : Type*} (tail head : E → V) (b : V)
    (port : Fin 6 → E) : Prop where
  /-- Distinct faces use distinct port branches. -/
  injective : Function.Injective port
  /-- Every port branch has an endpoint at the box. -/
  incident : ∀ f, tail (port f) = b ∨ head (port f) = b
  /-- No port branch is a loop. -/
  not_loop : ∀ f, tail (port f) ≠ head (port f)
  /-- Every branch with an endpoint at the box is a port branch. -/
  only_ports : ∀ e, (tail e = b ∨ head e = b) → ∃ f, port f = e

/-- Orientation sign of a branch relative to the box: `+1` when its tail is at the box (the
branch leaves the box), `-1` otherwise. -/
def portSign {V : Type*} [DecidableEq V] {E : Type*} (tail : E → V) (b : V) (e : E) : ℝ :=
  if tail e = b then 1 else -1

/-- Branch currents carry the outward terminal currents with the port orientation sign: on
the port branch of face `f` the branch current is `portSign * I f`. -/
def IsFluxPortCurrent {V : Type*} [DecidableEq V] {E : Type*} (tail : E → V) (b : V)
    (port : Fin 6 → E) (I : Fin 6 → ℝ) (i : E → ℝ) : Prop :=
  ∀ f, i (port f) = portSign tail b (port f) * I f

/-- On the port branch of face `f`, the box-node incidence entry times the sign-converted
branch current is the outward terminal current, for either orientation of the branch. -/
private lemma boxEntry_mul_portCurrent_eq {V : Type*} [Fintype V] [DecidableEq V]
    {E : Type*} [Fintype E] [DecidableEq E] (tail head : E → V) (b : V) (port : Fin 6 → E)
    (I : Fin 6 → ℝ) (i : E → ℝ) (hwire : IsTerminalWiring tail head b port)
    (hcur : IsFluxPortCurrent tail b port I i) (f : Fin 6) :
    electricalIncidence tail head b (port f) * i (port f) = I f := by
  rw [hcur f]
  by_cases h : tail (port f) = b
  · have hhead : head (port f) ≠ b := fun hh => hwire.not_loop f (h.trans hh.symm)
    have hs : portSign tail b (port f) = 1 := by simp [portSign, h]
    rw [electricalIncidence_apply, ite_eq_left h, ite_eq_right hhead, hs]
    ring
  · have hhead : head (port f) = b := (hwire.incident f).resolve_left h
    have hs : portSign tail b (port f) = -1 := by simp [portSign, h]
    rw [electricalIncidence_apply, ite_eq_right h, ite_eq_left hhead, hs]
    ring

/-- A branch that is not a port branch has a zero incidence entry at the box node. -/
private lemma boxEntry_eq_zero_of_not_port {V : Type*} [Fintype V] [DecidableEq V]
    {E : Type*} [Fintype E] [DecidableEq E] (tail head : E → V) (b : V) (port : Fin 6 → E)
    (hwire : IsTerminalWiring tail head b port) (e : E) (he : ∀ f, port f ≠ e) :
    electricalIncidence tail head b e = 0 := by
  have hne : ¬(tail e = b ∨ head e = b) := by
    intro h
    obtain ⟨f, hf⟩ := hwire.only_ports e h
    exact he f hf
  rw [electricalIncidence_apply, ite_eq_right (fun h => hne (Or.inl h)),
    ite_eq_right (fun h => hne (Or.inr h))]
  ring

/-! ## B. Net outflow and injection at the box node -/

/-- **Sign-correct outflow.** Under the terminal wiring and the sign conversion, the
electrical-incidence outflow at the box node is the sum of the six outward terminal currents,
whatever the orientation of each port branch. -/
lemma electricalIncidence_mulVec_box_eq_sum {V : Type*} [Fintype V] [DecidableEq V]
    {E : Type*} [Fintype E] [DecidableEq E] (tail head : E → V) (b : V) (port : Fin 6 → E)
    (I : Fin 6 → ℝ) (i : E → ℝ) (hwire : IsTerminalWiring tail head b port)
    (hcur : IsFluxPortCurrent tail b port I i) :
    (electricalIncidence tail head *ᵥ i) b = ∑ f : Fin 6, I f := by
  rw [Matrix.mulVec_apply_eq_sum]
  have hvanish : ∀ e ∈ (Finset.univ : Finset E),
      e ∉ Finset.univ.image port →
      electricalIncidence tail head b e * i e = 0 := by
    intro e _ he
    have hnp : ∀ f, port f ≠ e := fun f hf =>
      he (Finset.mem_image.mpr ⟨f, Finset.mem_univ f, hf⟩)
    rw [boxEntry_eq_zero_of_not_port tail head b port hwire e hnp, zero_mul]
  have hsub : Finset.sum (Finset.univ.image port)
      (fun e => electricalIncidence tail head b e * i e)
      = Finset.sum Finset.univ (fun e => electricalIncidence tail head b e * i e) :=
    Finset.sum_subset (Finset.subset_univ _) hvanish
  rw [← hsub, Finset.sum_image hwire.injective.injOn]
  exact Finset.sum_congr rfl
    (fun f _ => boxEntry_mul_portCurrent_eq tail head b port I i hwire hcur f)

/-- **Injection at the box.** With the box-terminal flux identification and charge
continuity at rate `chargeRate`, every nodal injection compatible with current balance equals
minus the enclosed-charge rate at the box node. -/
lemma injection_box_eq_neg_chargeRate {V : Type*} [Fintype V] [DecidableEq V]
    {E : Type*} [Fintype E] [DecidableEq E] (D : Fin 6 → Set (ℝ × ℝ))
    (density : Fin 6 → (ℝ × ℝ) → ℝ) (I : Fin 6 → ℝ) (chargeRate : ℝ)
    (hI : ∀ f : Fin 6, I f = faceFlux D density f)
    (hcont : chargeContinuity (faceFlux D density) chargeRate)
    (tail head : E → V) (b : V) (port : Fin 6 → E) (i : E → ℝ) (j : V → ℝ)
    (hwire : IsTerminalWiring tail head b port) (hcur : IsFluxPortCurrent tail b port I i)
    (hKCL : electricalIncidence tail head *ᵥ i = j) :
    j b = -chargeRate := by
  have hsum := electricalIncidence_mulVec_box_eq_sum tail head b port I i hwire hcur
  have hbox := sum_terminalCurrent_eq_neg_chargeRate D density I chargeRate hI hcont
  rw [← hKCL, hsum, hbox]

/-- **Flux-to-injection sign bridge (headline).** For six oriented box faces, with terminal
outward currents identified with the current-density flux integrals and the zero flux balance
assumed (continuity at rate zero), wired into the network at the box node with the port
orientation sign: the outflow at the box node is the sum of the outward terminal currents, that
sum is zero, and every nodal injection compatible with current balance vanishes at the box node.
`boxInjection_eq_zero_of_constantCharge` derives the same conclusion for the box `Set.Icc lo hi`
from constant enclosed charge and the local continuity law. -/
lemma fluxPortSignBridge_correct {V : Type*} [Fintype V] [DecidableEq V]
    {E : Type*} [Fintype E] [DecidableEq E] (D : Fin 6 → Set (ℝ × ℝ))
    (density : Fin 6 → (ℝ × ℝ) → ℝ) (I : Fin 6 → ℝ)
    (hI : ∀ f : Fin 6, I f = faceFlux D density f)
    (hsteady : chargeContinuity (faceFlux D density) 0)
    (tail head : E → V) (b : V) (port : Fin 6 → E) (i : E → ℝ)
    (hwire : IsTerminalWiring tail head b port) (hcur : IsFluxPortCurrent tail b port I i) :
    (electricalIncidence tail head *ᵥ i) b = ∑ f : Fin 6, I f ∧
      (electricalIncidence tail head *ᵥ i) b = 0 ∧
      ∀ j : V → ℝ, electricalIncidence tail head *ᵥ i = j → j b = 0 := by
  have hsum := electricalIncidence_mulVec_box_eq_sum tail head b port I i hwire hcur
  have hzero : ∑ f : Fin 6, I f = 0 :=
    (sum_terminalCurrent_eq_neg_chargeRate D density I 0 hI hsteady).trans neg_zero
  refine ⟨hsum, ?_, ?_⟩
  · rw [hsum, hzero]
  · intro j hj
    rw [← hj, hsum, hzero]

/-- **Steady enclosed charge gives zero injection at the box.** For the box `Set.Icc lo hi`, with
terminal outward currents identified with the outward face fluxes of a current density `J`, a
charge density `ρ` whose enclosed charge is constant in time, and the local continuity law
`ρdot + div J = 0` at time `t`: the outflow at the box node is zero, and every nodal injection
compatible with current balance vanishes there. The zero flux balance is derived by
`boxTerminalCurrents_sum_eq_zero_of_constantCharge`, not assumed. -/
lemma boxInjection_eq_zero_of_constantCharge {V : Type*} [Fintype V] [DecidableEq V]
    {E : Type*} [Fintype E] [DecidableEq E] (lo hi : Fin 3 → ℝ) (hle : lo ≤ hi)
    (ρ ρdot : ℝ → (Fin 3 → ℝ) → ℝ)
    (hρ : Continuous (Function.uncurry ρ)) (hρdot : Continuous (Function.uncurry ρdot))
    (hderiv : ∀ s x, HasDerivAt (fun s => ρ s x) (ρdot s x) s) (t : ℝ)
    (hconst : ∀ s, enclosedCharge lo hi ρ s = enclosedCharge lo hi ρ t)
    (J : (Fin 3 → ℝ) → Fin 3 → ℝ) (J' : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] Fin 3 → ℝ)
    (hc : ContinuousOn J (Set.Icc lo hi))
    (hd : ∀ x ∈ Set.pi Set.univ fun i => Set.Ioo (lo i) (hi i), HasFDerivAt J (J' x) x)
    (hlocal : ∀ x ∈ Set.Icc lo hi, ρdot t x + fderivDivergence J' x = 0)
    (I : Fin 6 → ℝ) (hI : ∀ f : Fin 6, I f = boxOutwardFlux lo hi J f)
    (tail head : E → V) (b : V) (port : Fin 6 → E) (i : E → ℝ)
    (hwire : IsTerminalWiring tail head b port) (hcur : IsFluxPortCurrent tail b port I i) :
    (electricalIncidence tail head *ᵥ i) b = 0 ∧
      ∀ j : V → ℝ, electricalIncidence tail head *ᵥ i = j → j b = 0 := by
  have hsum := electricalIncidence_mulVec_box_eq_sum tail head b port I i hwire hcur
  have hzero : ∑ f : Fin 6, I f = 0 :=
    boxTerminalCurrents_sum_eq_zero_of_constantCharge lo hi hle ρ ρdot hρ hρdot hderiv t hconst
      J J' hc hd hlocal I hI
  exact ⟨hsum.trans hzero, fun j hj => by rw [← hj, hsum, hzero]⟩

/-! ## C. Validation -/

/-- A single reversed terminal sign: if the current on the port branch of one face `f₀` with
nonzero outward current is negated, the outflow at the box node is `-2 * I f₀` and no longer
matches the zero injection of steady charge. -/
lemma reversedPortSign_breaks_injection {V : Type*} [Fintype V] [DecidableEq V]
    {E : Type*} [Fintype E] [DecidableEq E] (tail head : E → V) (b : V) (port : Fin 6 → E)
    (I : Fin 6 → ℝ) (i : E → ℝ) (hwire : IsTerminalWiring tail head b port)
    (hcur : IsFluxPortCurrent tail b port I i) (hsum : ∑ f : Fin 6, I f = 0) (f₀ : Fin 6)
    (hf₀ : I f₀ ≠ 0) :
    (electricalIncidence tail head *ᵥ Function.update i (port f₀) (-i (port f₀))) b =
        -2 * I f₀ ∧
      (electricalIncidence tail head *ᵥ Function.update i (port f₀) (-i (port f₀))) b ≠ 0 := by
  have hmain := electricalIncidence_mulVec_box_eq_sum tail head b port I i hwire hcur
  have hface := boxEntry_mul_portCurrent_eq tail head b port I i hwire hcur f₀
  rw [hsum] at hmain
  have hmainS : Finset.sum Finset.univ
      (fun e => electricalIncidence tail head b e * i e) = 0 := by
    simpa [Matrix.mulVec_apply_eq_sum] using hmain
  have hmem : port f₀ ∈ (Finset.univ : Finset E) := Finset.mem_univ _
  have herase : Finset.sum (Finset.univ.erase (port f₀))
        (fun e => electricalIncidence tail head b e * Function.update i (port f₀) (-i (port f₀)) e)
      = Finset.sum (Finset.univ.erase (port f₀))
        (fun e => electricalIncidence tail head b e * i e) := by
    apply Finset.sum_congr rfl
    intro e he
    rw [Function.update_of_ne (Finset.ne_of_mem_erase he)]
  have h1 : Finset.sum Finset.univ (fun e => electricalIncidence tail head b e * i e)
      = electricalIncidence tail head b (port f₀) * i (port f₀)
        + Finset.sum (Finset.univ.erase (port f₀))
          (fun e => electricalIncidence tail head b e * i e) :=
    (Finset.add_sum_erase _ _ hmem).symm
  have h2 : Finset.sum Finset.univ
      (fun e => electricalIncidence tail head b e * Function.update i (port f₀) (-i (port f₀)) e)
      = electricalIncidence tail head b (port f₀) * (-i (port f₀))
        + Finset.sum (Finset.univ.erase (port f₀))
          (fun e => electricalIncidence tail head b e * i e) := by
    have h := (Finset.add_sum_erase (Finset.univ : Finset E)
      (fun e => electricalIncidence tail head b e * Function.update i (port f₀) (-i (port f₀)) e)
      hmem).symm
    simp only [Function.update_self] at h
    rw [herase] at h
    exact h
  have hpart1 : (electricalIncidence tail head *ᵥ Function.update i (port f₀) (-i (port f₀))) b
      = -2 * I f₀ := by
    rw [Matrix.mulVec_apply_eq_sum, h2]
    have htot : electricalIncidence tail head b (port f₀) * i (port f₀)
        + Finset.sum (Finset.univ.erase (port f₀))
          (fun e => electricalIncidence tail head b e * i e) = 0 :=
      h1.symm.trans hmainS
    have hS : Finset.sum (Finset.univ.erase (port f₀))
          (fun e => electricalIncidence tail head b e * i e)
        = -(electricalIncidence tail head b (port f₀) * i (port f₀)) :=
      eq_neg_of_add_eq_zero_right htot
    have hneg : electricalIncidence tail head b (port f₀) * (-i (port f₀))
        = -(electricalIncidence tail head b (port f₀) * i (port f₀)) := by ring
    rw [hS, hneg, hface]
    ring
  exact ⟨hpart1, by rw [hpart1]; exact mul_ne_zero (neg_ne_zero.mpr two_ne_zero) hf₀⟩

end PhyslibExt.Circuits.FluxPortSignBridge
