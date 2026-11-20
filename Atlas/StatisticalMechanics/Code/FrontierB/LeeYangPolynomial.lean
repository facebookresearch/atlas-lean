/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Ising.Gibbs

open scoped BigOperators
open Finset Polynomial

namespace StatMech
namespace FrontierB

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def minusSpinCount (s : ConfigSpace V) : ℕ :=
  (Finset.univ.filter fun x => s x = false).card



noncomputable def zeroFieldInteractionWeight (β : ℝ) (s : ConfigSpace V) : ℝ :=
  Real.exp (β * ∑ e ∈ G.edgeFinset, bond s e)




noncomputable def leeYangPolynomial (β : ℝ) : ℝ[X] :=
  ∑ s : ConfigSpace V,
    Polynomial.C (zeroFieldInteractionWeight G β s) *
      Polynomial.X ^ minusSpinCount s


noncomputable def leeYangComplexPolynomial (β : ℝ) : ℂ[X] :=
  (leeYangPolynomial G β).map (algebraMap ℝ ℂ)

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


theorem eval_leeYangPolynomial_at_fugacity (β h : ℝ) :
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


theorem leeYangPolynomial_ne_zero (β : ℝ) : leeYangPolynomial G β ≠ 0 := by
  intro hp
  have h := eval_leeYangPolynomial_at_fugacity G β 0
  rw [hp, Polynomial.eval_zero] at h
  simp only [mul_zero, zero_mul, Real.exp_zero, one_mul] at h
  exact isingZ_ne_zero G β 0 h.symm


theorem leeYangComplexPolynomial_ne_zero (β : ℝ) :
    leeYangComplexPolynomial G β ≠ 0 := by
  intro hp
  have h := eval_leeYangComplexPolynomial_ofReal G β 1
  rw [hp, Polynomial.eval_zero] at h
  have hr : (leeYangPolynomial G β).eval 1 ≠ 0 := by
    rw [show (1 : ℝ) = Real.exp (-2 * β * 0) by simp,
      eval_leeYangPolynomial_at_fugacity]
    exact mul_ne_zero (by positivity) (isingZ_ne_zero G β 0)
  exact hr (Complex.ofReal_eq_zero.mp h.symm)

end FrontierB
end StatMech
