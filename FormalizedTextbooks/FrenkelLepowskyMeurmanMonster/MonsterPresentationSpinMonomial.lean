/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Explicit quadratic signs and coordinate relabelings in the actual spin normalizer. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinHolomorph

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000

/-- A concrete binary quadratic polynomial, retaining its full matrix of coefficients. -/
def monsterMonomialQuadratic (M : Fin 12 → Fin 12 → ZMod 2)
    (a : SpinIndex) : ZMod 2 := ∑ i, ∑ j, a i * a j * M i j

/-- The modulation created by differentiating the concrete quadratic sign. -/
def monsterMonomialGradient (M : Fin 12 → Fin 12 → ZMod 2)
    (a : SpinIndex) : SpinIndex := fun j => ∑ i, a i * (M i j + M j i)

/-- The polarization identity for this actual quadratic polynomial. -/
theorem monsterMonomialQuadratic_add (M : Fin 12 → Fin 12 → ZMod 2)
    (a b : SpinIndex) :
    monsterMonomialQuadratic M (a + b) = monsterMonomialQuadratic M a +
      monsterMonomialQuadratic M b + spinDot (monsterMonomialGradient M a) b := by
  have hq : monsterMonomialQuadratic M (a + b) =
      monsterMonomialQuadratic M a + monsterMonomialQuadratic M b +
        (∑ i : Fin 12, ∑ j : Fin 12, a i * b j * M i j) +
        (∑ i : Fin 12, ∑ j : Fin 12, b i * a j * M i j) := by
    unfold monsterMonomialQuadratic
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.add_apply]
    ring
  have hg : spinDot (monsterMonomialGradient M a) b =
      (∑ i : Fin 12, ∑ j : Fin 12, a i * b j * M i j) +
        (∑ i : Fin 12, ∑ j : Fin 12, b i * a j * M i j) := by
    change (∑ j : Fin 12, (∑ i : Fin 12, a i * (M i j + M j i)) * b j) = _
    simp only [Finset.sum_mul, mul_add, add_mul, Finset.sum_add_distrib]
    apply congrArg₂ (fun x y : ZMod 2 => x + y)
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
  rw [hq, hg]
  abel

/-- Multiplication by the source quadratic sign, on actual spin functions. -/
def monsterMonomialDiagonal (M : Fin 12 → Fin 12 → ZMod 2) :
    SpinSpace →ₗ[ℝ] SpinSpace where
  toFun f t := qSign (monsterMonomialQuadratic M t) * f t
  map_add' f h := by ext t; simp [mul_add]
  map_smul' c f := by ext t; simp [mul_assoc, mul_comm]

/-- The signed diagonal is its own inverse. -/
theorem monsterMonomialDiagonal_involutive (M : Fin 12 → Fin 12 → ZMod 2) :
    Function.Involutive (monsterMonomialDiagonal M) := by
  intro f
  ext t
  change qSign _ * (qSign _ * f t) = f t
  rw [← mul_assoc, qSign_sq, one_mul]

/-- The explicit image of a genuine Q element under a quadratic signed diagonal. -/
def monsterMonomialDiagonalImage (M : Fin 12 → Fin 12 → ZMod 2) (q : Q) : Q :=
  ⟨ofAdd (Fin.append (spinTranslation q)
      (spinModulation q + monsterMonomialGradient M (spinTranslation q))),
    ofAdd (toAdd q.coeff + monsterMonomialQuadratic M (spinTranslation q))⟩

/-- Evaluation of the displayed quadratic diagonal. -/
theorem monsterMonomialDiagonal_apply (M : Fin 12 → Fin 12 → ZMod 2)
    (f : SpinSpace) (t : SpinIndex) :
    monsterMonomialDiagonal M f t = qSign (monsterMonomialQuadratic M t) * f t := rfl

/-- The signed diagonal keeps the genuine translation coordinates. -/
theorem monsterMonomialDiagonalImage_translation
    (M : Fin 12 → Fin 12 → ZMod 2) (q : Q) :
    spinTranslation (monsterMonomialDiagonalImage M q) = spinTranslation q := by
  ext i
  exact Fin.append_left _ _ i

/-- Its phase is the displayed quadratic derivative. -/
theorem monsterMonomialDiagonalImage_phase
    (M : Fin 12 → Fin 12 → ZMod 2) (q : Q) (t : SpinIndex) :
    spinPhase (monsterMonomialDiagonalImage M q) t =
      toAdd q.coeff + monsterMonomialQuadratic M (spinTranslation q) +
        spinDot (spinModulation q + monsterMonomialGradient M (spinTranslation q)) t := by
  have hm : spinModulation (monsterMonomialDiagonalImage M q) =
      spinModulation q + monsterMonomialGradient M (spinTranslation q) := by
    ext i
    exact Fin.append_right _ _ i
  have hc : toAdd (monsterMonomialDiagonalImage M q).coeff =
      toAdd q.coeff + monsterMonomialQuadratic M (spinTranslation q) := rfl
  simp only [spinPhase, hm, hc]

/-- This is an actual operator conjugation identity for every Q element. -/
theorem monsterMonomialDiagonal_conjugation
    (M : Fin 12 → Fin 12 → ZMod 2) (q : Q) :
    monsterMonomialDiagonal M * spinOperator q * monsterMonomialDiagonal M =
      spinOperator (monsterMonomialDiagonalImage M q) := by
  apply LinearMap.ext
  intro f
  ext t
  simp only [Module.End.mul_apply, monsterMonomialDiagonal_apply, xiSpinOperator_apply,
    monsterMonomialDiagonalImage_translation, monsterMonomialDiagonalImage_phase]
  rw [add_comm t (spinTranslation q),
    monsterMonomialQuadratic_add M (spinTranslation q) t]
  rw [add_comm (spinTranslation q) t]
  simp only [spinPhase, spinDot_add_left, qSign_add]
  have ht : qSign (monsterMonomialQuadratic M t) *
      qSign (monsterMonomialQuadratic M t) = 1 := qSign_sq _
  linear_combination (qSign (toAdd q.coeff) * qSign (spinDot (spinModulation q) t) *
    qSign (monsterMonomialQuadratic M (spinTranslation q)) *
    qSign (spinDot (monsterMonomialGradient M (spinTranslation q)) t) *
    f (t + spinTranslation q)) * ht

/-- The same signed diagonal, with its proved inverse. -/
def monsterMonomialDiagonalEquiv (M : Fin 12 → Fin 12 → ZMod 2) :
    SpinSpace ≃ₗ[ℝ] SpinSpace :=
  LinearEquiv.ofInvolutive (monsterMonomialDiagonal M) (monsterMonomialDiagonal_involutive M)

/-- Quadratic signs preserve the actual Euclidean spin pairing. -/
theorem monsterMonomialDiagonal_pairing
    (M : Fin 12 → Fin 12 → ZMod 2) (f h : SpinSpace) :
    spinPairing (monsterMonomialDiagonalEquiv M f) (monsterMonomialDiagonalEquiv M h) =
      spinPairing f h := by
  unfold spinPairing
  apply Finset.sum_congr rfl
  intro t _
  change (qSign _ * f t) * (qSign _ * h t) = f t * h t
  have hs := qSign_sq (monsterMonomialQuadratic M t)
  linear_combination (f t * h t) * hs

/-- The exact quadratic sign belongs to the actual spin holomorph. -/
noncomputable def monsterMonomialDiagonalHolomorph
    (M : Fin 12 → Fin 12 → ZMod 2) : SpinHolomorph :=
  ⟨monsterMonomialDiagonalEquiv M, by
    constructor
    · apply xiSpinImage_normalizer_of_involution _ ?_ (monsterMonomialDiagonalImage M)
      · intro q
        apply LinearEquiv.toLinearMap_injective
        exact monsterMonomialDiagonal_conjugation M q
      · apply LinearEquiv.ext
        exact monsterMonomialDiagonal_involutive M
    · exact monsterMonomialDiagonal_pairing M⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
