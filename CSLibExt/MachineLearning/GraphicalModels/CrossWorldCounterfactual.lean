/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Fintype.BigOperators

/-!
# Cross-world counterfactuals are not identified by interventional laws

A finite recursive structural causal model on two observed binary nodes `X → Y` with shared
exogenous noise `u` (`BinarySCM`). For every intervention on the observed nodes (none, `do(X)`,
`do(Y)`, or both) it assigns weights to the values of `(X, Y)`, a probability law when the noise
weights form a probability mass function (`BinarySCM.IsNoiseLaw`); a cross-world quantity such
as `P(Y_1 = 1, Y_0 = 0)` evaluates the potential outcomes `Y_1` and `Y_0` at the same noise.

## Main definitions

* `BinarySCM`, `BinarySCM.law`: the model and the law of `(X, Y)` under an intervention
  (a probability law when the noise weights satisfy `BinarySCM.IsNoiseLaw`).
* `BinarySCM.probY1Y0`: the weight of the cross-world event `Y_1 = 1 ∧ Y_0 = 0`, the
  probability `P(Y_1 = 1, Y_0 = 0)` under `BinarySCM.IsNoiseLaw`.
* `constantResponse`, `switchingResponse`: an independent fair-coin exposure with outcome
  response types "always 1"/"always 0", respectively "helped"/"hurt".

## Main results

* `law_constantResponse_eq_switchingResponse`: the two models have the same observational law
  and the same law under every single- and multi-node intervention.
* `exists_same_law_ne_probY1Y0`: yet `P(Y_1 = 1, Y_0 = 0)` is `0` in one and `1 / 2` in the
  other, so the joint of the potential outcomes is not identified by interventional laws
  (Pearl, Glymour and Jewell 2016, §4.3; Pearl 2009, §1.4.4).

This is a self-contained two-node interface. The general finite SCMs of
`CSLibExt/MachineLearning/GraphicalModels/StructuralCausalModels.lean` do not yet have
interventions or counterfactual laws; unification with them is future work.

## References

* J. Pearl, *Causality: Models, Reasoning, and Inference*, 2nd ed., Cambridge University Press
  (2009), §1.4.4.
* J. Pearl, M. Glymour and N. P. Jewell, *Causal Inference in Statistics: A Primer*, Wiley
  (2016), §4.3.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels.CrossWorld

/-- A recursive structural causal model on two observed binary nodes `X → Y` with exogenous
noise in a finite type `U`: noise weights `pU`, structural equations `X = fX u` and
`Y = fY X u`. Counterfactuals use the same noise `u` in every intervened world. The structure
does not force `pU` to be a probability mass function; that is the predicate `IsNoiseLaw`,
which the two concrete witnesses below are proved to satisfy. -/
structure BinarySCM (U : Type*) where
  /-- The weight of each exogenous noise value (a probability mass function when
  `IsNoiseLaw` holds). -/
  pU : U → ℝ
  /-- The structural equation of `X`. -/
  fX : U → Bool
  /-- The structural equation of `Y`, given the value of `X`. -/
  fY : Bool → U → Bool

namespace BinarySCM

/-- `pU` is a probability mass function on the noise. -/
def IsNoiseLaw {U : Type*} [Fintype U] (M : BinarySCM U) : Prop :=
  (∀ u, 0 ≤ M.pU u) ∧ ∑ u, M.pU u = 1

/-- An intervention on the observed nodes: the first component `some x` sets `X := x`, the
second `some y` sets `Y := y`, and `none` keeps the structural equation. `(none, none)` is the
observational regime; the four kinds cover every single- and multi-node intervention. -/
abbrev Intervention := Option Bool × Option Bool

/-- The value of `X` in the regime `i` at noise `u`. -/
def solX {U : Type*} (M : BinarySCM U) (i : Intervention) (u : U) : Bool :=
  i.1.getD (M.fX u)

/-- The value of `Y` in the regime `i` at noise `u`. -/
def solY {U : Type*} (M : BinarySCM U) (i : Intervention) (u : U) : Bool :=
  i.2.getD (M.fY (M.solX i u) u)

/-- The `pU`-weight of the event `X = x ∧ Y = y` in the regime `i`; under `IsNoiseLaw` this is
the law `P_i(X = x, Y = y)` of the observed nodes. -/
noncomputable def law {U : Type*} [Fintype U] (M : BinarySCM U) (i : Intervention)
    (x y : Bool) : ℝ :=
  ∑ u, if M.solX i u = x ∧ M.solY i u = y then M.pU u else 0

/-- The `pU`-weight of the cross-world event `Y_1 = 1 ∧ Y_0 = 0`, where the potential outcomes
`Y_1 = fY true u` and `Y_0 = fY false u` are evaluated at the same noise `u`; under
`IsNoiseLaw` this is the probability `P(Y_1 = 1, Y_0 = 0)`. -/
noncomputable def probY1Y0 {U : Type*} [Fintype U] (M : BinarySCM U) : ℝ :=
  ∑ u, if M.fY true u = true ∧ M.fY false u = false then M.pU u else 0

end BinarySCM

open BinarySCM

/-- Constant response types: noise `u = (u_X, u_Y)` uniform on `Bool × Bool`, `X = u_X`, and
`Y = u_Y` regardless of `X` (the types "always 1" and "always 0"). -/
noncomputable def constantResponse : BinarySCM (Bool × Bool) where
  pU _ := 1 / 4
  fX u := u.1
  fY _ u := u.2

/-- Switching response types: noise `u = (u_X, u_Y)` uniform on `Bool × Bool`, `X = u_X`, and
`Y = X` if `u_Y` (type "helped") and `Y = !X` otherwise (type "hurt"). -/
noncomputable def switchingResponse : BinarySCM (Bool × Bool) where
  pU _ := 1 / 4
  fX u := u.1
  fY x u := if u.2 then x else !x

/-- Both noise laws are probability mass functions; in both, `u_X` and `u_Y` are independent
fair coins. -/
theorem isNoiseLaw_constantResponse_switchingResponse :
    constantResponse.IsNoiseLaw ∧ switchingResponse.IsNoiseLaw := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro u
    simp [constantResponse]
  · simp [constantResponse]
  · intro u
    simp [switchingResponse]
  · simp [switchingResponse]

/-- The two models have the same observational law and the same law of `(X, Y)` under every
single- and multi-node intervention. -/
theorem law_constantResponse_eq_switchingResponse (i : Intervention) (x y : Bool) :
    constantResponse.law i x y = switchingResponse.law i x y := by
  rcases i with ⟨_ | ⟨_ | _⟩, _ | ⟨_ | _⟩⟩ <;> cases x <;> cases y <;>
    simp [law, solX, solY, constantResponse, switchingResponse, Fintype.sum_prod_type]

/-- Under constant response types `Y_1 = Y_0`, so `P(Y_1 = 1, Y_0 = 0) = 0`. -/
theorem probY1Y0_constantResponse : constantResponse.probY1Y0 = 0 := by
  simp [probY1Y0, constantResponse]

/-- Under switching response types `P(Y_1 = 1, Y_0 = 0) = 1 / 2` (the "helped" type). -/
theorem probY1Y0_switchingResponse : switchingResponse.probY1Y0 = 1 / 2 := by
  simp [probY1Y0, switchingResponse, Fintype.sum_prod_type]
  norm_num

/-- **Cross-world counterfactuals are not identified by interventional laws.** Two finite
recursive SCMs on `X → Y` agree on the observational law and on every interventional law of
`(X, Y)`, yet assign different probabilities to `Y_1 = 1 ∧ Y_0 = 0`. -/
theorem exists_same_law_ne_probY1Y0 :
    ∃ M₁ M₂ : BinarySCM (Bool × Bool), M₁.IsNoiseLaw ∧ M₂.IsNoiseLaw ∧
      (∀ i x y, M₁.law i x y = M₂.law i x y) ∧ M₁.probY1Y0 ≠ M₂.probY1Y0 := by
  refine ⟨constantResponse, switchingResponse,
    isNoiseLaw_constantResponse_switchingResponse.1,
    isNoiseLaw_constantResponse_switchingResponse.2,
    law_constantResponse_eq_switchingResponse, ?_⟩
  rw [probY1Y0_constantResponse, probY1Y0_switchingResponse]
  norm_num

end Cslib.MachineLearning.GraphicalModels.CrossWorld
