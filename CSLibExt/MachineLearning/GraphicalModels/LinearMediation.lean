/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.LinearSEM

/-!
# Mediation effects in the additive linear mediation model

The no-interaction mediation model `X → M → Y`, `X → Y` with `M = a X + U_M` and
`Y = c' X + b M + U_Y`. Counterfactuals keep the noise `(U_M, U_Y)` fixed: the potential outcome
`Y_x` sets the exposure to `x`, and the nested counterfactual `Y_{x, M_{x'}}` sets the exposure
to `x` while the mediator takes its value under `do(X = x')` with the same noise.

## Main definitions

* `MediationModel`: the coefficients `a`, `b`, `c'`; `mediator`, `outcome`, `potentialOutcome`,
  `nestedOutcome`.
* `totalEffect`, `naturalDirectEffect`, `naturalIndirectEffect`, `controlledDirectEffect`:
  unit-level effects of the contrast `x₀ → x₁`.
* `coeffMatrix`: the model as a recursive linear SEM on `X = 0`, `M = 1`, `Y = 2`.

## Main results

* `doSolve_coeffMatrix`, `doSolve_coeffMatrix_nested`: the potential and nested outcomes are
  the solutions of the linear SEM under surgery (`LinearSEM.doSolve`, via
  `LinearSEM.eq_doSolve_iff`).
* `totalEffect_eq`: `(c' + a b)(x₁ - x₀)`; `naturalDirectEffect_eq` and
  `controlledDirectEffect_eq`: `c' (x₁ - x₀)`; `naturalIndirectEffect_eq`: `a b (x₁ - x₀)`;
  `totalEffect_eq_add`: total = natural direct + natural indirect.

These are identities of the structural model; identifying the effects from observational data
needs further assumptions (sequential ignorability) and is not claimed.

## References

* J. Pearl, M. Glymour and N. P. Jewell, *Causal Inference in Statistics: A Primer*, Wiley
  (2016), §§3.7, 4.4.5–4.5.
* J. Pearl, *Direct and indirect effects*, Proc. UAI (2001), 411–420.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels.LinearMediation

open Cslib.MachineLearning.GraphicalModels

/-- The additive, no-interaction mediation model `X → M → Y`, `X → Y`:
`M = a X + U_M` and `Y = c' X + b M + U_Y`. -/
structure MediationModel where
  /-- Coefficient of the exposure `X` in the mediator equation. -/
  a : ℝ
  /-- Coefficient of the mediator `M` in the outcome equation. -/
  b : ℝ
  /-- Direct coefficient of the exposure `X` in the outcome equation. -/
  c' : ℝ

namespace MediationModel

/-- The mediator equation `M = a x + U_M`. -/
def mediator (m : MediationModel) (x uM : ℝ) : ℝ :=
  m.a * x + uM

/-- The outcome equation `Y = c' x + b m + U_Y`. -/
def outcome (m : MediationModel) (x mv uY : ℝ) : ℝ :=
  m.c' * x + m.b * mv + uY

/-- The potential outcome `Y_x(u)` under `do(X = x)` for the noise `u = (U_M, U_Y)`. -/
def potentialOutcome (m : MediationModel) (x uM uY : ℝ) : ℝ :=
  m.outcome x (m.mediator x uM) uY

/-- The nested counterfactual `Y_{x, M_{x'}}(u)`: exposure set to `x` while the mediator takes
the value `M_{x'}(u)` it has under `do(X = x')`, with the same noise `u` in both. -/
def nestedOutcome (m : MediationModel) (x x' uM uY : ℝ) : ℝ :=
  m.outcome x (m.mediator x' uM) uY

/-- The unit-level total effect `Y_{x₁}(u) - Y_{x₀}(u)` of the contrast `x₀ → x₁`. -/
def totalEffect (m : MediationModel) (x₀ x₁ uM uY : ℝ) : ℝ :=
  m.potentialOutcome x₁ uM uY - m.potentialOutcome x₀ uM uY

/-- The unit-level natural direct effect `Y_{x₁, M_{x₀}}(u) - Y_{x₀}(u)`. -/
def naturalDirectEffect (m : MediationModel) (x₀ x₁ uM uY : ℝ) : ℝ :=
  m.nestedOutcome x₁ x₀ uM uY - m.potentialOutcome x₀ uM uY

/-- The unit-level natural indirect effect `Y_{x₁}(u) - Y_{x₁, M_{x₀}}(u)`. -/
def naturalIndirectEffect (m : MediationModel) (x₀ x₁ uM uY : ℝ) : ℝ :=
  m.potentialOutcome x₁ uM uY - m.nestedOutcome x₁ x₀ uM uY

/-- The unit-level controlled direct effect `Y_{x₁, M = mv}(u) - Y_{x₀, M = mv}(u)` with the
mediator held at `mv`. -/
def controlledDirectEffect (m : MediationModel) (x₀ x₁ mv uY : ℝ) : ℝ :=
  m.outcome x₁ mv uY - m.outcome x₀ mv uY

/-- The model as a recursive linear SEM on the nodes `X = 0`, `M = 1`, `Y = 2`:
`B 1 0 = a`, `B 2 0 = c'`, `B 2 1 = b`, all other coefficients `0`. -/
def coeffMatrix (m : MediationModel) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 0; m.a, 0, 0; m.c', m.b, 0]

/-- The coefficient matrix is strictly lower triangular (the model is recursive). -/
theorem coeffMatrix_strictLower (m : MediationModel) :
    ∀ i j, i ≤ j → m.coeffMatrix i j = 0 := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [coeffMatrix]

/-- **`do(X = x)` in the linear SEM gives the potential outcomes**: the surgical solution has
`M = M_x(u)` and `Y = Y_x(u)` for the noise `u = (e 1, e 2)`. -/
theorem doSolve_coeffMatrix (m : MediationModel) (x : ℝ) (e : Fin 3 → ℝ) :
    LinearSEM.doSolve m.coeffMatrix 0 x e 1 = m.mediator x (e 1) ∧
      LinearSEM.doSolve m.coeffMatrix 0 x e 2 = m.potentialOutcome x (e 1) (e 2) := by
  set v : Fin 3 → ℝ := ![x, m.mediator x (e 1), m.potentialOutcome x (e 1) (e 2)] with hv
  have hsol : v = LinearSEM.doSolve m.coeffMatrix 0 x e := by
    rw [← LinearSEM.eq_doSolve_iff m.coeffMatrix_strictLower 0 x e v]
    constructor
    · simp [hv]
    · intro i hi
      fin_cases i
      · exact absurd rfl hi
      · change v 1 = Matrix.mulVec m.coeffMatrix v 1 + e 1
        simp [hv, coeffMatrix, mediator, Matrix.mulVec]
      · change v 2 = Matrix.mulVec m.coeffMatrix v 2 + e 2
        simp [hv, coeffMatrix, potentialOutcome, outcome, mediator, Matrix.mulVec]
  rw [← hsol]
  constructor <;> simp [hv]

/-- **The nested counterfactual is a nested surgery with shared noise**: setting the root
`X := x` and then `do(M = M_{x'}(u))`, with the same noise `e 1` inside `M_{x'}`, gives
`Y = Y_{x, M_{x'}}(u)`. -/
theorem doSolve_coeffMatrix_nested (m : MediationModel) (x x' : ℝ) (e : Fin 3 → ℝ) :
    LinearSEM.doSolve m.coeffMatrix 1 (m.mediator x' (e 1)) (Function.update e 0 x) 2 =
      m.nestedOutcome x x' (e 1) (e 2) := by
  set w : Fin 3 → ℝ := ![x, m.mediator x' (e 1), m.nestedOutcome x x' (e 1) (e 2)] with hw
  have hsol :
      w = LinearSEM.doSolve m.coeffMatrix 1 (m.mediator x' (e 1)) (Function.update e 0 x) := by
    rw [← LinearSEM.eq_doSolve_iff m.coeffMatrix_strictLower 1 (m.mediator x' (e 1))
      (Function.update e 0 x) w]
    constructor
    · simp [hw]
    · intro i hi
      fin_cases i
      · change w 0 = Matrix.mulVec m.coeffMatrix w 0 + Function.update e 0 x 0
        simp [hw, coeffMatrix, Matrix.mulVec]
      · exact absurd rfl hi
      · change w 2 = Matrix.mulVec m.coeffMatrix w 2 + Function.update e 0 x 2
        simp [hw, coeffMatrix, nestedOutcome, outcome, mediator, Matrix.mulVec]
  rw [← hsol]
  simp [hw]

/-- **Total effect** of the contrast `x₀ → x₁`: `(c' + a b)(x₁ - x₀)`. -/
theorem totalEffect_eq (m : MediationModel) (x₀ x₁ uM uY : ℝ) :
    m.totalEffect x₀ x₁ uM uY = (m.c' + m.a * m.b) * (x₁ - x₀) := by
  simp [totalEffect, potentialOutcome, outcome, mediator]
  ring

/-- **Natural direct effect** of the contrast `x₀ → x₁`: `c' (x₁ - x₀)`. -/
theorem naturalDirectEffect_eq (m : MediationModel) (x₀ x₁ uM uY : ℝ) :
    m.naturalDirectEffect x₀ x₁ uM uY = m.c' * (x₁ - x₀) := by
  simp [naturalDirectEffect, nestedOutcome, potentialOutcome, outcome, mediator]
  ring

/-- **Natural indirect effect** of the contrast `x₀ → x₁`: `a b (x₁ - x₀)`. -/
theorem naturalIndirectEffect_eq (m : MediationModel) (x₀ x₁ uM uY : ℝ) :
    m.naturalIndirectEffect x₀ x₁ uM uY = m.a * m.b * (x₁ - x₀) := by
  simp [naturalIndirectEffect, nestedOutcome, potentialOutcome, outcome, mediator]
  ring

/-- Without interaction the controlled direct effect at any mediator level `mv` equals the
natural direct effect `c' (x₁ - x₀)`. -/
theorem controlledDirectEffect_eq (m : MediationModel) (x₀ x₁ mv uY : ℝ) :
    m.controlledDirectEffect x₀ x₁ mv uY = m.c' * (x₁ - x₀) := by
  simp [controlledDirectEffect, outcome]
  ring

/-- The total effect decomposes as natural direct plus natural indirect effect. -/
theorem totalEffect_eq_add (m : MediationModel) (x₀ x₁ uM uY : ℝ) :
    m.totalEffect x₀ x₁ uM uY =
      m.naturalDirectEffect x₀ x₁ uM uY + m.naturalIndirectEffect x₀ x₁ uM uY := by
  simp [totalEffect, naturalDirectEffect, naturalIndirectEffect]

end MediationModel

end Cslib.MachineLearning.GraphicalModels.LinearMediation
