/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.CRNDirect
public meta import CSLibExt.Bioinformatics.CRNDirect
public import Mathlib.Tactic.NormNum


namespace Cslib.Bioinformatics.CRN

open MathlibExt.Biology.Dynamics.ComplexBalanced

/-! ## Computed examples: birth reaction over `Fin 2` -/

/-- Birth network ∅ → A over two species (`Fin 2`, species `0` is `A`),
with a single reaction (`Unit`). -/
def birthNet : ReactionNetwork (Fin 2) Unit :=
  { src := fun _ _ => 0
    prod := fun _ s => if s = 0 then 1 else 0 }

/-- Rate function for the birth network: rate constant `2`. -/
def birthK : Unit → ℝ := fun _ => 2

/-- Empty initial state. -/
def initState : Fin 2 → ℕ := fun _ => 0

theorem birth_k : birthK () = 2 := rfl

theorem birth_reactants (s : Fin 2) : birthNet.src () s = 0 := rfl

theorem birth_products (s : Fin 2) :
    birthNet.prod () s = (if s = 0 then 1 else 0) := rfl

/-- A birth reaction fires at its rate constant regardless of state. -/
theorem birth_propensity (x : Fin 2 → ℕ) :
    birthNet.propensity birthK () x = 2 := by
  unfold ReactionNetwork.propensity
  simp [birth_k, birth_reactants, Nat.descFactorial_zero,
    Finset.prod_const_one]

/-- Firing the birth reaction from the empty state produces one `A`. -/
theorem birth_fire_empty :
    birthNet.fire () initState
      = fun s => if s = (0 : Fin 2) then 1 else 0 := by
  funext s
  simp [ReactionNetwork.fire, initState, birth_reactants, birth_products]

theorem birth_fire_zero : birthNet.fire () initState 0 = 1 := by
  simp [ReactionNetwork.fire, initState, birth_reactants, birth_products]

theorem birth_fire_ne (s : Fin 2) (hs : s ≠ 0) :
    birthNet.fire () initState s = 0 := by
  simp [ReactionNetwork.fire, initState, birth_reactants, birth_products, hs]

/-- Single-reaction selection: the birth reaction is selected and the new
state has one `A`; the waiting time stays symbolic. -/
theorem birth_step_some :
    step birthNet birthK [()] initState (1 / 2) (1 / 2) =
      some (Real.log (1 / (1 / 2)) / 2, (),
        birthNet.fire () initState) := by
  have ha0 : totalPropensity birthNet birthK [()] initState = 2 := by
    simp [totalPropensity, birth_propensity]
  have hle2 : (1 / 2 : ℝ) * 2 ≤ birthNet.propensity birthK () initState := by
    rw [birth_propensity]
    norm_num
  have hpos2 : 0 < birthNet.propensity birthK () initState := by
    rw [birth_propensity]
    norm_num
  have hsel2 : selectAux birthNet birthK [()] initState ((1 / 2 : ℝ) * 2) =
      some () := by
    rw [selectAux_cons, ite_eq_left ⟨hle2, hpos2⟩]
  rw [step_eq, ha0, ite_eq_right (by norm_num : (2 : ℝ) ≠ 0), hsel2]

/-- Absorbing example: the empty list never fires. -/
theorem empty_step_none (u1 u2 : ℝ) :
    step birthNet birthK ([] : List Unit) initState u1 u2 = none :=
  step_none_of_empty birthNet birthK initState u1 u2

/-- The waiting time from the birth example is nonnegative (via soundness). -/
theorem birth_tau_nonneg : 0 ≤ Real.log (1 / (1 / 2 : ℝ)) / 2 := by
  have hk : ∀ r, 0 ≤ birthK r := by
    intro r
    show (0 : ℝ) ≤ 2
    norm_num
  have h := step_some_sound birthNet birthK hk [()] initState (1 / 2) (1 / 2)
    _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    birth_step_some
  exact h.1

#print axioms birth_propensity
#print axioms ReactionNetwork.propensity_nonneg
#print axioms ReactionNetwork.propensity_eq_zero_of_not_le
#print axioms totalPropensity_eq_zero_iff
#print axioms selectAux_some_pos
#print axioms selectAux_mem
#print axioms selectAux_none_of_total_lt
#print axioms selectAux_some_of_le_total
#print axioms step_some_sound
#print axioms step_some_of_pos
#print axioms step_eq_none_iff
#print axioms step_none_of_empty
#print axioms birth_fire_empty
#print axioms birth_fire_zero
#print axioms birth_fire_ne
#print axioms birth_step_some
#print axioms empty_step_none
#print axioms birth_tau_nonneg

/-- Two-reaction network over `Fin 2` with no reactants, for the
boundary-selection example. Reaction `0` produces nothing; reaction `1`
produces one unit-species molecule, distinguishing the two reactions. -/
def boundaryNet : ReactionNetwork Unit (Fin 2) :=
  { src := fun _ _ => 0
    prod := fun i _ => if i = 0 then 0 else 1 }

/-- Unit rate function for the boundary network. -/
def boundaryK : Fin 2 → ℝ := fun _ => 1

theorem boundary_prop1 : boundaryNet.propensity boundaryK 0 (fun _ => 0) = 1 := by
  unfold ReactionNetwork.propensity boundaryNet boundaryK
  simp [Nat.descFactorial_zero]

theorem boundary_prop2 : boundaryNet.propensity boundaryK 1 (fun _ => 0) = 1 := by
  unfold ReactionNetwork.propensity boundaryNet boundaryK
  simp [Nat.descFactorial_zero]

theorem boundary_total :
    totalPropensity boundaryNet boundaryK [0, 1] (fun _ => 0) = 2 := by
  unfold totalPropensity
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [boundary_prop1, boundary_prop2]
  norm_num

theorem selectAux_boundary_first :
    selectAux boundaryNet boundaryK [0, 1] (fun _ => 0) 1 = some 0 := by
  rw [selectAux_cons, boundary_prop1]
  norm_num

theorem step_boundary_selects_first (u1 : ℝ) :
    Option.map (fun t => boundaryNet.prod t.2.1 ())
        (step boundaryNet boundaryK [0, 1] (fun _ => 0) u1 (1 / 2))
      = some 0 := by
  have hthresh : (1 / 2 : ℝ) * 2 = 1 := by norm_num
  rw [step_eq, boundary_total, hthresh, selectAux_boundary_first]
  simp [boundaryNet]

/-- Signed rates `1` and `-1` on the two source-free reactions of `boundaryNet`. -/
def signedK : Fin 2 → ℝ := fun i => if i = 0 then 1 else -1

/-- With signed rates the total cancels to zero although reaction `0` has positive
propensity, so `step` returns `none`; with signed rates `none` therefore does not mean that every
listed propensity is zero, which is why `step_eq_none_iff` needs nonnegative rates. -/
theorem signed_step_none (u1 u2 : ℝ) :
    0 < boundaryNet.propensity signedK 0 (fun _ => 0) ∧
      totalPropensity boundaryNet signedK [0, 1] (fun _ => 0) = 0 ∧
      step boundaryNet signedK [0, 1] (fun _ => 0) u1 u2 = none := by
  have h0 : boundaryNet.propensity signedK 0 (fun _ => 0) = 1 := by
    unfold ReactionNetwork.propensity boundaryNet signedK
    simp [Nat.descFactorial_zero]
  have h1 : boundaryNet.propensity signedK 1 (fun _ => 0) = -1 := by
    unfold ReactionNetwork.propensity boundaryNet signedK
    simp [Nat.descFactorial_zero]
  have htotal : totalPropensity boundaryNet signedK [0, 1] (fun _ => 0) = 0 := by
    unfold totalPropensity
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [h0, h1]
    norm_num
  refine ⟨?_, htotal, ?_⟩
  · rw [h0]
    norm_num
  · rw [step_eq, ite_eq_left htotal]

#print axioms signed_step_none

end Cslib.Bioinformatics.CRN
