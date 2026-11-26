/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sequence.HiddenMarkovMeasure

@[expose] public section

namespace Cslib.MachineLearning.Sequence.HiddenMarkovMeasure

open Cslib.MachineLearning.Sequence.HiddenMarkov
open Cslib.MachineLearning.Sequence.HiddenMarkovLaw

variable {S O : Type*} [Fintype S] [Fintype O]

/-! ## Tests

Length one and multi-time, a zero transition cell, a zero emission
cell, normalization. Zero-cell hypotheses are abstract (`= 0` on one
matrix entry), as in the Atlas boundary tests. -/

/-- Length one (`t = 0`): the joint mass of the single-state path
and single observation is `init * emit`. -/
theorem test_length_one_joint (h : HMM S O ℝ) (hN : Normalized h)
    (s : S) (o : O) :
    (jointPMF h hN 0) ((fun _ => s), (fun _ => o)) =
      ENNReal.ofReal (h.init s * h.emit s o) := by
  have h2 : jointProb S O h 0 ((fun _ => s), (fun _ => o)) =
      h.init s * h.emit s o := rfl
  rw [jointPMF_apply, h2]

/-- Length one, real form: `jointProb` at `t = 0`. -/
theorem test_length_one_jointProb (h : HMM S O ℝ) (s : S) (o : O) :
    jointProb S O h 0 ((fun _ => s), (fun _ => o)) =
      h.init s * h.emit s o := by
  rfl

theorem test_length_one_marginal (h : HMM S O ℝ) (hN : Normalized h)
    (o : O) :
    (PMF.map Prod.snd (jointPMF h hN 0)) (fun _ => o) =
      ENNReal.ofReal (∑ s, h.init s * h.emit s o) := by
  haveI : Unique (Fin (0 + 1)) := Fin.instUnique
  have hlik : likelihood h (extend 0 (fun _ => o)) 0 =
      ∑ s : S, h.init s * h.emit s o := by
    simp only [likelihood]
    have hterm : ∀ z : Fin (0 + 1) → S,
        pathProb h (extend 0 (fun _ => o)) 0 z =
          h.init (z 0) * h.emit (z 0) o := by
      intro z
      simp only [pathProb]
      rw [extend_apply_le 0 _ 0 (by omega)]
    rw [Finset.sum_congr rfl (fun z _ => hterm z)]
    let e : S ≃ (Fin (0 + 1) → S) := (Equiv.funUnique _ _).symm
    rw [← Fintype.sum_equiv e (fun s : S => h.init s * h.emit s o)
      (fun z : Fin (0 + 1) → S => h.init (z 0) * h.emit (z 0) o)
      (fun s => rfl)]
  rw [obsMarginal_apply, hlik]

/-- Multi-time step: extending path and string by one step multiplies
the joint law by the transition and emission masses (the `snoc`
recurrence behind the factorization at every horizon). -/
theorem test_multi_time_snoc (h : HMM S O ℝ) (t : ℕ)
    (z : Fin (t + 1) → S) (x : Fin (t + 1) → O) (s : S) (o : O) :
    jointProb S O h (t + 1) (Fin.snoc z s, Fin.snoc x o) =
      jointProb S O h t (z, x) * h.trans (z (Fin.last t)) s *
        h.emit s o := by
  exact jointProb_snoc h t z x s o

/-- Zero transition cell: if `h.trans a b = 0`, every path stepping
`a -> b` at the last step has zero joint mass, jointly and in the
PMF. -/
theorem test_zero_transition (h : HMM S O ℝ) (hN : Normalized h)
    (t : ℕ) (z : Fin (t + 1) → S) (x : Fin (t + 1) → O)
    (a b : S) (o : O)
    (hz : z (Fin.last t) = a) (h0 : h.trans a b = 0) :
    jointProb S O h (t + 1) (Fin.snoc z b, Fin.snoc x o) = 0 ∧
      (jointPMF h hN (t + 1)) (Fin.snoc z b, Fin.snoc x o) = 0 := by
  have h1 : jointProb S O h (t + 1) (Fin.snoc z b, Fin.snoc x o) = 0 := by
    rw [jointProb_snoc, hz, h0, mul_zero, zero_mul]
  constructor
  · exact h1
  · rw [jointPMF_apply, h1]
    simp

/-- Zero emission cell: if `h.emit s o = 0`, every path visiting `s`
at a time where the string reads `o` has zero joint mass, at any
horizon and any time index. -/
theorem test_zero_emission (h : HMM S O ℝ) (hN : Normalized h)
    (t : ℕ) (z : Fin (t + 1) → S) (x : Fin (t + 1) → O)
    (i : Fin (t + 1)) (s : S) (o : O)
    (hz : z i = s) (hx : x i = o) (h0 : h.emit s o = 0) :
    jointProb S O h t (z, x) = 0 ∧ (jointPMF h hN t) (z, x) = 0 := by
  have hterm : h.emit (z i) (x i) = 0 := by rw [hz, hx, h0]
  have hJ : jointProb S O h t (z, x) = 0 := by
    rw [jointProb_factor]
    simp only [obsWeight]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hterm, mul_zero]
  constructor
  · exact hJ
  · rw [jointPMF_apply, hJ]
    simp

/-- Normalization test: real masses of the joint PMF sum to one,
and the likelihoods sum to one over observation strings. -/
theorem test_normalization (h : HMM S O ℝ) (hN : Normalized h)
    (t : ℕ) :
    (∑ zx : (Fin (t + 1) → S) × (Fin (t + 1) → O),
      ((jointPMF h hN t) zx).toReal = 1) ∧
      (∑ x : Fin (t + 1) → O, likelihood h (extend t x) t = 1) := by
  have g1 : (∑ zx : (Fin (t + 1) → S) × (Fin (t + 1) → O),
        ((jointPMF h hN t) zx).toReal)
      = ∑ zx : (Fin (t + 1) → S) × (Fin (t + 1) → O),
        jointProb S O h t zx :=
    Finset.sum_congr rfl
      (fun zx _ => jointPMF_apply_toReal h hN t zx.1 zx.2)
  constructor
  · rw [g1]
    exact HiddenMarkovLaw.sum_jointProb_eq_one S O h hN t
  · rw [Finset.sum_congr rfl
        (fun x _ => HiddenMarkovLaw.likelihood_eq_sum_jointProb S O h t x),
      Finset.sum_comm, ← Fintype.sum_prod_type]
    exact HiddenMarkovLaw.sum_jointProb_eq_one S O h hN t

end Cslib.MachineLearning.Sequence.HiddenMarkovMeasure
