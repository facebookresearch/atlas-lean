/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Valuation.HenselianIntegralClosure
public import MathlibExt.RingTheory.Valuation.Henselian

@[expose] public section

-- Exact-source consumer, with the original binders.
private theorem exactSource
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (O : ValuationSubring K) [HenselianLocalRing O]
    (V : ValuationSubring L) (hV : ∀ x : K, algebraMap K L x ∈ V ↔ x ∈ O) :
    (∀ x : L, x ∈ V ↔ IsIntegral O x) ∧
      ∀ V' : ValuationSubring L, (∀ x : K, algebraMap K L x ∈ V' ↔ x ∈ O) → V' = V :=
  ValuationSubring.forall_mem_iff_isIntegral_and_eq_of_henselianLocalRing O V hV

-- Boundary: over an algebraically closed field, a valuation subring is
-- Henselian, so the characterization applies to the ring itself; in
-- particular an element outside the ring is not integral over it.
example {K : Type*} [Field K] [IsAlgClosed K] (O : ValuationSubring K) (x : K)
    (hx : x ∉ O) : ¬ IsIntegral O x := by
  haveI : HenselianLocalRing O := ValuationSubring.henselianLocalRing_of_isAlgClosed O
  have h := (ValuationSubring.forall_mem_iff_isIntegral_and_eq_of_henselianLocalRing
    O O (fun y => by simp)).1 x
  exact fun hint => hx (h.mpr hint)
