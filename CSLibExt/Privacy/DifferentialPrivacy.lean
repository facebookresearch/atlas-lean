/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Differential privacy core (Weeks 3-4 core, 90-day plan #7 DP)

Pointwise `ε`-DP for a kernel (database → mass function over
outputs), replace-one adjacency, and the post-processing theorem:
any deterministic function of an `ε`-DP mechanism is `ε`-DP.

The kernel assumes only nonnegativity and summability, not
`∑' o, prob d o = 1`, so post-processing needs no measure API.
The Laplace mechanism (which does need the normalizer, and the
bridge to SampCert's add/remove adjacency) is the next DP
deliverable. SampCert is external to Atlas; it is bridged, not
copied.
-/

@[expose] public section

set_option autoImplicit false

namespace CSLibExt.Privacy.DifferentialPrivacy

/-- A kernel: a database-dependent mass function over outputs. -/
structure Kernel (Database Output : Type) where
  prob : Database → Output → ℝ
  nonneg : ∀ d o, 0 ≤ prob d o
  summable : ∀ d, Summable (prob d)

/-- Replace-one adjacency: databases differ in at most one row. -/
def ReplaceOne {n : ℕ} {X : Type} (d d' : Fin n → X) : Prop :=
  ∃ i, ∀ j, j ≠ i → d j = d' j

/-- Pointwise `ε`-DP: adjacent databases give pointwise
`exp ε`-close mass functions. -/
def IsDP {Database Output : Type} (M : Kernel Database Output)
    (adj : Database → Database → Prop)
    (ε : ℝ) : Prop :=
  ∀ d d', adj d d' → ∀ o, M.prob d o ≤ Real.exp ε * M.prob d' o

/-- Deterministic post-processing of a kernel. -/
def postProcess {Database Output Output' : Type} (g : Output → Output')
    (M : Kernel Database Output) :
    Kernel Database Output' where
  prob d o' := ∑' o, if g o = o' then M.prob d o else 0
  nonneg d o' := by
    apply tsum_nonneg
    intro o
    by_cases h : g o = o'
    · rw [if_pos h]; exact M.nonneg d o
    · rw [if_neg h]; exact le_rfl
  summable d := by
    apply Summable.of_nonneg_of_le
      (f := M.prob d)
      (g := fun o => if g o = o' then M.prob d o else 0)
    · intro o
      by_cases h : g o = o'
      · rw [if_pos h]; exact M.nonneg d o
      · rw [if_neg h]; exact le_rfl
    · intro o
      by_cases h : g o = o'
      · rw [if_pos h]; exact le_rfl
      · rw [if_neg h]; exact M.nonneg d o
    · exact M.summable d

/-- Post-processing preserves `ε`-DP: any deterministic function of
an `ε`-DP mechanism is `ε`-DP. -/
theorem isDP_postProcess {Database Output Output' : Type}
    {M : Kernel Database Output}
    {adj : Database → Database → Prop} {ε : ℝ} (h : IsDP M adj ε)
    (g : Output → Output') : IsDP (postProcess g M) adj ε := by
  intro d d' hadj o'
  have hexp : Real.exp ε *
      (∑' o, if g o = o' then M.prob d' o else 0) =
      ∑' o, if g o = o' then Real.exp ε * M.prob d' o else 0 := by
    rw [tsum_mul_left]
    apply tsum_congr
    intro o
    by_cases h : g o = o'
    · rw [if_pos h]
    · rw [if_neg h, if_neg h]; exact mul_zero _
  rw [hexp]
  apply tsum_le_tsum
  · intro o
    by_cases hc : g o = o'
    · rw [if_pos hc, if_pos hc]; exact h d d' hadj o
    · rw [if_neg hc, if_neg hc]; exact le_rfl
  · exact (postProcess g M).summable d
  · apply Summable.of_nonneg_of_le
      (f := fun o => Real.exp ε * M.prob d' o)
      (g := fun o => if g o = o' then Real.exp ε * M.prob d' o else 0)
    · intro o
      by_cases hc : g o = o'
      · rw [if_pos hc]; exact mul_nonneg (Real.exp_nonneg _) (M.nonneg d' o)
      · rw [if_neg hc]; exact le_rfl
    · intro o
      by_cases hc : g o = o'
      · rw [if_pos hc]; exact le_rfl
      · rw [if_neg hc]; exact mul_nonneg (Real.exp_nonneg _) (M.nonneg d' o)
    · exact (M.summable d').mul_left _

end CSLibExt.Privacy.DifferentialPrivacy
