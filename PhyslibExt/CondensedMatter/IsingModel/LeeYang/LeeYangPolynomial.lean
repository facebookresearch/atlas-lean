/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Gibbs

/-!
# The Lee–Yang polynomial of a finite Ising model

The zero-field Ising partition function as a polynomial in the fugacity `z = exp (-2βh)`.

## i. Overview

For a finite graph `G` on `V` and inverse temperature `β`, the Ising partition function with
external field `h` equals `exp (β h |V|)` times a polynomial in `z = exp (-2βh)`: a
configuration with `k` minus spins contributes `exp (β ∑_e σ_x σ_y) z^k`. This file defines that
polynomial over `ℝ` and over `ℂ`, identifies its value at the physical fugacity with the
partition function `isingZ`, and shows that it is nonzero. The Lee–Yang circle
theorem (`finiteGraph_hasLeeYangCircle`) locates its complex zeros on the unit circle.

## ii. Key results

- `leeYangPolynomial` : the polynomial `∑_σ exp (β ∑_e σ_x σ_y) X^{#minus spins of σ}`.
- `eval_leeYangPolynomial_at_fugacity` : its value at `exp (-2βh)` is
  `exp (-β h |V|) · isingZ G β h`.
- `leeYangPolynomial_ne_zero` : the polynomial is nonzero.

## iii. Table of contents

- A. Definitions
- B. Evaluation and the partition function
- C. Nonvanishing

## iv. References

- T. D. Lee and C. N. Yang, *Statistical theory of equations of state and phase transitions. II.
  Lattice gas and Ising model*, Phys. Rev. 87 (1952) 410–419.
-/

@[expose] public section

open scoped BigOperators
open Finset Polynomial

namespace StatMech
namespace LeeYang

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. Definitions -/

/-- The number of minus spins (sites with value `false`) of a configuration. -/
def minusSpinCount (s : ConfigSpace V) : ℕ :=
  (Finset.univ.filter fun x => s x = false).card

/-- The zero-field Boltzmann weight `exp (β ∑_{e ∈ E(G)} σ_x σ_y)` of a configuration. -/
noncomputable def zeroFieldInteractionWeight (β : ℝ) (s : ConfigSpace V) : ℝ :=
  Real.exp (β * ∑ e ∈ G.edgeFinset, bond s e)

/-- The Lee–Yang polynomial `∑_σ exp (β ∑_e σ_x σ_y) X^k(σ)` of the Ising model on `G`, where `k(σ)`
is the number of minus spins; its variable is the fugacity `exp (-2βh)`. -/
noncomputable def leeYangPolynomial (β : ℝ) : ℝ[X] :=
  ∑ s : ConfigSpace V,
    Polynomial.C (zeroFieldInteractionWeight G β s) *
      Polynomial.X ^ minusSpinCount s

/-- The Lee–Yang polynomial with complex coefficients, whose zeros the Lee–Yang circle theorem
locates. -/
noncomputable def leeYangComplexPolynomial (β : ℝ) : ℂ[X] :=
  (leeYangPolynomial G β).map (algebraMap ℝ ℂ)

/-! ## B. Evaluation and the partition function -/

omit [DecidableEq V] in
lemma sum_spin_eq_card_sub_two_mul_minusSpinCount (s : ConfigSpace V) :
    (∑ x, spin s x) = (Fintype.card V : ℝ) - 2 * minusSpinCount s := by
  have hpoint (x : V) :
      spin s x = 1 - 2 * (if s x = false then (1 : ℝ) else 0) := by
    cases hx : s x
    · norm_num [spin, hx]
    · norm_num [spin, hx]
  calc
    (∑ x, spin s x) = ∑ x, (1 - 2 * (if s x = false then (1 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact hpoint x
    _ = (Fintype.card V : ℝ) -
        2 * ∑ x, (if s x = false then (1 : ℝ) else 0) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      rw [← Finset.mul_sum]
      ring
    _ = (Fintype.card V : ℝ) - 2 * minusSpinCount s := by
      simp [minusSpinCount]

lemma eval_leeYangPolynomial (β z : ℝ) :
    (leeYangPolynomial G β).eval z =
      ∑ s : ConfigSpace V, zeroFieldInteractionWeight G β s * z ^ minusSpinCount s := by
  unfold leeYangPolynomial
  calc
    Polynomial.eval z (∑ s : ConfigSpace V,
        Polynomial.C (zeroFieldInteractionWeight G β s) *
          Polynomial.X ^ minusSpinCount s) =
        ∑ s : ConfigSpace V, Polynomial.eval z
          (Polynomial.C (zeroFieldInteractionWeight G β s) *
            Polynomial.X ^ minusSpinCount s) := by
      change (Polynomial.evalRingHom z) (∑ s : ConfigSpace V,
          Polynomial.C (zeroFieldInteractionWeight G β s) *
            Polynomial.X ^ minusSpinCount s) =
        ∑ s : ConfigSpace V, (Polynomial.evalRingHom z)
          (Polynomial.C (zeroFieldInteractionWeight G β s) *
            Polynomial.X ^ minusSpinCount s)
      rw [map_sum]
    _ = ∑ s : ConfigSpace V,
        zeroFieldInteractionWeight G β s * z ^ minusSpinCount s := by
      apply Finset.sum_congr rfl
      intro s _
      simp

omit [DecidableEq V] in
lemma interactionWeight_mul_fugacity_pow (β h : ℝ) (s : ConfigSpace V) :
    zeroFieldInteractionWeight G β s *
        Real.exp (-2 * β * h) ^ minusSpinCount s =
      Real.exp (-β * h * Fintype.card V) * isingWeight G β h s := by
  rw [← Real.exp_nat_mul]
  unfold zeroFieldInteractionWeight isingWeight hamiltonian
  rw [← Real.exp_add, ← Real.exp_add]
  rw [sum_spin_eq_card_sub_two_mul_minusSpinCount s]
  congr 1
  ring

lemma eval_leeYangPolynomial_at_fugacity (β h : ℝ) :
    (leeYangPolynomial G β).eval (Real.exp (-2 * β * h)) =
      Real.exp (-β * h * Fintype.card V) * isingZ G β h := by
  rw [eval_leeYangPolynomial]
  unfold isingZ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  exact interactionWeight_mul_fugacity_pow G β h s

lemma eval_leeYangComplexPolynomial_ofReal (β z : ℝ) :
    (leeYangComplexPolynomial G β).eval (z : ℂ) =
      Complex.ofReal ((leeYangPolynomial G β).eval z) := by
  calc
    (leeYangComplexPolynomial G β).eval (z : ℂ) =
        Polynomial.eval₂ (algebraMap ℝ ℂ) (z : ℂ) (leeYangPolynomial G β) := by
      exact Polynomial.eval_map (algebraMap ℝ ℂ) (z : ℂ)
    _ = Complex.ofReal ((leeYangPolynomial G β).eval z) := by
      exact Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) z

/-! ## C. Nonvanishing -/

lemma leeYangPolynomial_ne_zero (β : ℝ) : leeYangPolynomial G β ≠ 0 := by
  intro hp
  have h := eval_leeYangPolynomial_at_fugacity G β 0
  rw [hp, Polynomial.eval_zero] at h
  simp only [mul_zero, zero_mul, Real.exp_zero, one_mul] at h
  exact isingZ_ne_zero G β 0 h.symm

lemma leeYangComplexPolynomial_ne_zero (β : ℝ) :
    leeYangComplexPolynomial G β ≠ 0 := by
  intro hp
  have h := eval_leeYangComplexPolynomial_ofReal G β 1
  rw [hp, Polynomial.eval_zero] at h
  have hr : (leeYangPolynomial G β).eval 1 ≠ 0 := by
    rw [show (1 : ℝ) = Real.exp (-2 * β * 0) by simp,
      eval_leeYangPolynomial_at_fugacity]
    exact mul_ne_zero (by positivity) (isingZ_ne_zero G β 0)
  exact hr (Complex.ofReal_eq_zero.mp h.symm)

end LeeYang
end StatMech
