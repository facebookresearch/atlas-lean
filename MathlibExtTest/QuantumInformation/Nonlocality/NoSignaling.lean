/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Tactic.NormNum
public import MathlibExt.QuantumInformation.Nonlocality.NoSignaling

/-!
# Issue #98 regression tests: singleton vs full multipartite no-signaling

Test-only home of the three-party binary signaling regression fixture
(`signalingExampleScenario`, `signalingExampleBehavior`, and helpers).
It lives here -- rather than in production
`MathlibExt.QuantumInformation.Nonlocality.NoSignaling` -- so the
`NoSignalingIssue98Test` namespace keeps example-specific names out of the
public production API. The production module keeps only the reusable API:
`Behavior.coalitionMarginal`, `HasSettingIndependentSingletonMarginals`,
`IsNoSignaling`, the singleton bridges, the two-party equivalence, and the
deterministic/local proofs.
-/

@[expose] public section

open Finset BigOperators

namespace QuantumInformation
namespace Nonlocality
namespace NoSignalingIssue98Test

open QuantumInformation.Nonlocality.BellScenario

/-! ## Issue #98 regression: singleton no-signaling without coalition no-signaling -/

/-- Three-party binary Bell scenario for the Issue #98 regression. -/
def signalingExampleScenario : BellScenario := ⟨3, 2, 2⟩

/-- Parties A, B, C of the regression scenario. -/
def exPartyA : Fin signalingExampleScenario.numParties := ⟨0, by decide⟩
def exPartyB : Fin signalingExampleScenario.numParties := ⟨1, by decide⟩
def exPartyC : Fin signalingExampleScenario.numParties := ⟨2, by decide⟩

/-- Binary settings of the regression scenario. -/
def exSetting0 : Fin signalingExampleScenario.numSettings := ⟨0, by decide⟩
def exSetting1 : Fin signalingExampleScenario.numSettings := ⟨1, by decide⟩

/-- Binary outcomes of the regression scenario. -/
def exOutcome0 : Fin signalingExampleScenario.numOutcomes := ⟨0, by decide⟩
def exOutcome1 : Fin signalingExampleScenario.numOutcomes := ⟨1, by decide⟩

private theorem exPartyA_val : exPartyA.val = 0 := rfl
private theorem exPartyB_val : exPartyB.val = 1 := rfl
private theorem exPartyC_val : exPartyC.val = 2 := rfl
private theorem exSetting0_val : exSetting0.val = 0 := rfl
private theorem exSetting1_val : exSetting1.val = 1 := rfl
private theorem exOutcome0_val : exOutcome0.val = 0 := rfl
private theorem exOutcome1_val : exOutcome1.val = 1 := rfl

private theorem exParty_lt (p : Fin signalingExampleScenario.numParties) :
    p.val < 3 :=
  p.is_lt

private theorem exSetting_lt (a : Fin signalingExampleScenario.numSettings) :
    a.val < 2 :=
  a.is_lt

private theorem exOutcome_lt (o : Fin signalingExampleScenario.numOutcomes) :
    o.val < 2 :=
  o.is_lt

private theorem exParty_eq (p : Fin signalingExampleScenario.numParties) :
    p = exPartyA ∨ p = exPartyB ∨ p = exPartyC := by
  have hlt := exParty_lt p
  have hv : p.val = 0 ∨ p.val = 1 ∨ p.val = 2 := by omega
  rcases hv with h0 | h1 | h2
  · left
    apply Fin.ext
    simp [exPartyA_val, h0]
  · right; left
    apply Fin.ext
    simp [exPartyB_val, h1]
  · right; right
    apply Fin.ext
    simp [exPartyC_val, h2]

private theorem exSetting_eq (a : Fin signalingExampleScenario.numSettings) :
    a = exSetting0 ∨ a = exSetting1 := by
  have hlt := exSetting_lt a
  have hv : a.val = 0 ∨ a.val = 1 := by omega
  rcases hv with h0 | h1
  · left
    apply Fin.ext
    simp [exSetting0_val, h0]
  · right
    apply Fin.ext
    simp [exSetting1_val, h1]

private theorem exOutcome_eq (o : Fin signalingExampleScenario.numOutcomes) :
    o = exOutcome0 ∨ o = exOutcome1 := by
  have hlt := exOutcome_lt o
  have hv : o.val = 0 ∨ o.val = 1 := by omega
  rcases hv with h0 | h1
  · left
    apply Fin.ext
    simp [exOutcome0_val, h0]
  · right
    apply Fin.ext
    simp [exOutcome1_val, h1]

/-- A constant-`1/4` if-sum equals the filtered card times `1/4`. -/
private theorem sum_if_quarter (s : Finset signalingExampleScenario.OutcomeAssignment)
    (P : signalingExampleScenario.OutcomeAssignment → Prop) [DecidablePred P] :
    (∑ y ∈ s, (if P y then (1 / 4 : ℝ) else 0))
      = ((s.filter P).card : ℝ) * (1 / 4) := by
  calc (∑ y ∈ s, (if P y then (1 / 4 : ℝ) else 0))
        = ∑ y ∈ s.filter P, (1 / 4 : ℝ) := (Finset.sum_filter P _).symm
      _ = ((s.filter P).card : ℝ) * (1 / 4) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- Parity-sector outcome counts over all joint outcomes. -/
private theorem exampleUnivCard (c : Fin signalingExampleScenario.numOutcomes) :
    (Finset.univ.filter
      (fun y : signalingExampleScenario.OutcomeAssignment =>
        ((y exPartyA).val + (y exPartyB).val) % 2 = c.val)).card = 4 := by
  rcases exOutcome_eq c with rfl | rfl <;> decide

/-- Parity-sector outcome counts at a fixed singleton outcome. -/
private theorem exampleMargCard (p : Fin signalingExampleScenario.numParties)
    (o c : Fin signalingExampleScenario.numOutcomes) :
    (((Finset.univ.filter
      (fun y : signalingExampleScenario.OutcomeAssignment => y p = o)).filter
      (fun y => ((y exPartyA).val + (y exPartyB).val) % 2 = c.val)).card = 2) := by
  rcases exParty_eq p with rfl | rfl | rfl <;>
    rcases exOutcome_eq o with rfl | rfl <;>
      rcases exOutcome_eq c with rfl | rfl <;>
        decide

/-- Issue #98 regression behavior: `P(a,b,c|x) = 1/4` when `a XOR b = x_C`
(i.e. `((y_A).val + (y_B).val) % 2 = (x_C).val` on binary `Fin 2` values)
and `0` otherwise. -/
noncomputable def signalingExampleBehavior : Behavior signalingExampleScenario where
  prob := fun x y =>
    if ((y exPartyA).val + (y exPartyB).val) % 2 = (x exPartyC).val then (1 / 4 : ℝ) else 0
  nonneg := by
    intro x y
    split_ifs with h
    · norm_num
    · exact le_rfl
  normalized := by
    intro x
    have hsum := sum_if_quarter Finset.univ
      (fun y : signalingExampleScenario.OutcomeAssignment =>
        ((y exPartyA).val + (y exPartyB).val) % 2 = (x exPartyC).val)
    rw [hsum]
    have hcard : (Finset.univ.filter
        (fun y : signalingExampleScenario.OutcomeAssignment =>
          ((y exPartyA).val + (y exPartyB).val) % 2 = (x exPartyC).val)).card = 4 := by
      rcases exOutcome_eq (x exPartyC) with hx | hx
      · rw [hx]
        exact exampleUnivCard exOutcome0
      · rw [hx]
        exact exampleUnivCard exOutcome1
    rw [hcard]
    norm_num

/-- Probability formula for the regression behavior. -/
theorem signalingExampleBehavior_prob
    (x : signalingExampleScenario.SettingAssignment)
    (y : signalingExampleScenario.OutcomeAssignment) :
    signalingExampleBehavior.prob x y =
      if ((y exPartyA).val + (y exPartyB).val) % 2 = (x exPartyC).val then (1 / 4 : ℝ) else 0 := rfl

/-- Every singleton marginal of the regression behavior is uniform. -/
theorem signalingExample_singletonMarginal
    (p : Fin signalingExampleScenario.numParties)
    (x : signalingExampleScenario.SettingAssignment)
    (o : Fin signalingExampleScenario.numOutcomes) :
    signalingExampleBehavior.marginal p x o = 1 / 2 := by
  unfold Behavior.marginal
  simp only [signalingExampleBehavior_prob]
  have hsum := sum_if_quarter
    (Finset.univ.filter
      (fun y : signalingExampleScenario.OutcomeAssignment => y p = o))
    (fun y : signalingExampleScenario.OutcomeAssignment =>
      ((y exPartyA).val + (y exPartyB).val) % 2 = (x exPartyC).val)
  rw [hsum]
  have hcard : (((Finset.univ.filter
      (fun y : signalingExampleScenario.OutcomeAssignment => y p = o)).filter
      (fun y : signalingExampleScenario.OutcomeAssignment =>
        ((y exPartyA).val + (y exPartyB).val) % 2 = (x exPartyC).val)).card = 2) := by
    rcases exOutcome_eq (x exPartyC) with hx | hx
    · rw [hx]
      exact exampleMargCard p o exOutcome0
    · rw [hx]
      exact exampleMargCard p o exOutcome1
  rw [hcard]
  norm_num

/-- The regression behavior satisfies the singleton-marginal condition. -/
theorem signalingExample_hasSingletonMarginals :
    HasSettingIndependentSingletonMarginals
      signalingExampleScenario signalingExampleBehavior := by
  intro p x x' o _
  rw [signalingExample_singletonMarginal, signalingExample_singletonMarginal]

/-- Settings agreeing on `{A,B}` but differing at `C`. -/
private def exX : signalingExampleScenario.SettingAssignment :=
  fun _ => exSetting0

private def exX' : signalingExampleScenario.SettingAssignment :=
  fun p => if p = exPartyC then exSetting1 else exSetting0

/-- All-zero outcome assignment selecting the `A,B` parity-zero sector. -/
private def exO : signalingExampleScenario.OutcomeAssignment :=
  fun _ => exOutcome0

private theorem exAgree :
    ∀ p ∈ ({exPartyA, exPartyB} : Finset (Fin signalingExampleScenario.numParties)),
      exX p = exX' p := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl <;> decide

private theorem exMarginal_lo :
    signalingExampleBehavior.coalitionMarginal
      {exPartyA, exPartyB} exX exO = 1 / 2 := by
  unfold Behavior.coalitionMarginal
  simp only [signalingExampleBehavior_prob]
  have hsum := sum_if_quarter
    (Finset.univ.filter
      (fun y : signalingExampleScenario.OutcomeAssignment =>
        ∀ p ∈ ({exPartyA, exPartyB} :
          Finset (Fin signalingExampleScenario.numParties)), y p = exO p))
    (fun y : signalingExampleScenario.OutcomeAssignment =>
      ((y exPartyA).val + (y exPartyB).val) % 2 = (exX exPartyC).val)
  rw [hsum]
  have hcard : (((Finset.univ.filter
      (fun y : signalingExampleScenario.OutcomeAssignment =>
        ∀ p ∈ ({exPartyA, exPartyB} :
          Finset (Fin signalingExampleScenario.numParties)), y p = exO p)).filter
      (fun y : signalingExampleScenario.OutcomeAssignment =>
        ((y exPartyA).val + (y exPartyB).val) % 2 = (exX exPartyC).val)).card = 2) := by
    decide
  rw [hcard]
  norm_num

private theorem exMarginal_hi :
    signalingExampleBehavior.coalitionMarginal
      {exPartyA, exPartyB} exX' exO = 0 := by
  unfold Behavior.coalitionMarginal
  simp only [signalingExampleBehavior_prob]
  have hsum := sum_if_quarter
    (Finset.univ.filter
      (fun y : signalingExampleScenario.OutcomeAssignment =>
        ∀ p ∈ ({exPartyA, exPartyB} :
          Finset (Fin signalingExampleScenario.numParties)), y p = exO p))
    (fun y : signalingExampleScenario.OutcomeAssignment =>
      ((y exPartyA).val + (y exPartyB).val) % 2 = (exX' exPartyC).val)
  rw [hsum]
  have hcard : (((Finset.univ.filter
      (fun y : signalingExampleScenario.OutcomeAssignment =>
        ∀ p ∈ ({exPartyA, exPartyB} :
          Finset (Fin signalingExampleScenario.numParties)), y p = exO p)).filter
      (fun y : signalingExampleScenario.OutcomeAssignment =>
        ((y exPartyA).val + (y exPartyB).val) % 2 = (exX' exPartyC).val)).card = 0) := by
    decide
  rw [hcard]
  norm_num

/-- The regression behavior violates full multipartite no-signaling:
the `A,B` coalition reads `C`'s setting through its joint parity. -/
theorem signalingExample_not_noSignaling :
    ¬ IsNoSignaling signalingExampleScenario signalingExampleBehavior := by
  intro h
  have hEq := h {exPartyA, exPartyB} exX exX' exAgree exO
  rw [exMarginal_lo, exMarginal_hi] at hEq
  norm_num at hEq

/-- Spot check: the behavior assigns `1/4` on a parity-matching outcome. -/
example (x : signalingExampleScenario.SettingAssignment)
    (y : signalingExampleScenario.OutcomeAssignment)
    (h : ((y exPartyA).val + (y exPartyB).val) % 2 = (x exPartyC).val) :
    signalingExampleBehavior.prob x y = 1 / 4 := by
  rw [signalingExampleBehavior_prob, ite_eq_left h]

/-- Spot check: singleton marginals are uniform. -/
example (p : Fin signalingExampleScenario.numParties)
    (x : signalingExampleScenario.SettingAssignment)
    (o : Fin signalingExampleScenario.numOutcomes) :
    signalingExampleBehavior.marginal p x o = 1 / 2 :=
  signalingExample_singletonMarginal p x o

end NoSignalingIssue98Test

end Nonlocality
end QuantumInformation
