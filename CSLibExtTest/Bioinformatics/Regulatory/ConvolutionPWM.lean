/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Regulatory.ConvolutionPWM
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Fin

/-!
# Convolution = PWM scan tests

DNA as `Fin 4` in the order `A, C, G, T`, so `Fin.rev` is the base complement. A width-2 filter
scoring the dinucleotide `CG` (`+2` per matching position, `-1` otherwise) on the sequence
`ACGT` (`m = 2`, three windows): the window responses are `-2, 4, -2`; max pooling returns `4`,
attained at window `1`; with bias `-1` and a ReLU the pooled output is `3`. The both-strand score
is unchanged by reverse complementing. The one-hot response is computed from the definition.
-/

namespace Cslib.Bioinformatics.Regulatory.ConvolutionPWM

/-- `+2` for `C` at position `0` and `G` at position `1`, `-1` otherwise. -/
def wCG : Fin 2 → Fin 4 → ℝ := fun k b => if (k = 0 ∧ b = 1) ∨ (k = 1 ∧ b = 2) then 2 else -1

/-- The sequence `ACGT…` (then `A` forever). -/
def acgt : ℕ → Fin 4 := fun j => if h : j < 4 then ⟨j, h⟩ else 0

example : conv wCG acgt 1 = 4 := by
  rw [conv_eq_pwmScore]
  norm_num [pwmScore, window, wCG, acgt, Fin.sum_univ_two]

example : conv wCG acgt 0 = -2 := by
  rw [conv_eq_pwmScore]
  norm_num [pwmScore, window, wCG, acgt, Fin.sum_univ_two]

/-- The one-hot response, from the definition of the convolution. -/
example : conv wCG acgt 2 = -2 := by
  simp [conv, oneHot, wCG, acgt, Fin.sum_univ_two, Fin.sum_univ_four]
  norm_num

/-- Max pooling finds the `CG` hit. -/
example : 4 ≤ maxPool wCG acgt 2 := by
  have h := le_maxPool wCG acgt (m := 2) (i := 1) (by norm_num)
  rw [← conv_eq_pwmScore] at h
  have : conv wCG acgt 1 = 4 := by
    rw [conv_eq_pwmScore]; norm_num [pwmScore, window, wCG, acgt, Fin.sum_univ_two]
  linarith

/-- The pooled ReLU output with bias `β` is `max (maxPool + β) 0`. -/
example (β : ℝ) :
    (Finset.range 3).sup' Finset.nonempty_range_add_one (fun i => max (conv wCG acgt i + β) 0) =
      max (maxPool wCG acgt 2 + β) 0 :=
  maxPool_relu wCG acgt 2 β

/-- `Fin.rev` on `Fin 4` is the complement `A ↔ T`, `C ↔ G`, an involution. -/
example : Function.Involutive (Fin.rev : Fin 4 → Fin 4) := Fin.rev_rev

/-- Scanning both strands is invariant under reverse complementing. -/
example : bothStrands Fin.rev wCG (rcSeq Fin.rev (2 + 2) acgt) 2 = bothStrands Fin.rev wCG acgt 2 :=
  bothStrands_rcSeq Fin.rev Fin.rev_rev wCG acgt 2

/-- `CG` is its own reverse complement: the reverse-complement filter of `wCG` is `wCG`. -/
example : rcFilter Fin.rev wCG = wCG := by
  funext k b
  fin_cases k <;> fin_cases b <;> simp [rcFilter, wCG]

end Cslib.Bioinformatics.Regulatory.ConvolutionPWM
