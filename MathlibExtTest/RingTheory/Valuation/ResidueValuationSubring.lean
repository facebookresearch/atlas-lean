/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Valuation.ResidueValuationSubring

@[expose] public section

universe u

/-- Consumer with the original binders. -/
private theorem exactSource {L : Type u} [Field L] (A S : ValuationSubring L) (h : A ≤ S) :
    ringKrullDim A = ringKrullDim (A.residueValuationSubring S h) + ringKrullDim S :=
  ValuationSubring.ringKrullDim_eq_ringKrullDim_residueValuationSubring_add A S h

/-- Higher-universe consumer. -/
private theorem exactSourceHigherUniverse {L : Type 2} [Field L]
    (A S : ValuationSubring L) (h : A ≤ S) :
    ringKrullDim A = ringKrullDim (A.residueValuationSubring S h) + ringKrullDim S :=
  ValuationSubring.ringKrullDim_eq_ringKrullDim_residueValuationSubring_add A S h

/-- Equal subrings: the residue valuation subring of the maximal ideal
quotient recovers the dimension formula with `S = A`. -/
example {L : Type*} [Field L] (A : ValuationSubring L) :
    ringKrullDim A =
      ringKrullDim (A.residueValuationSubring A le_rfl) + ringKrullDim A :=
  ValuationSubring.ringKrullDim_eq_ringKrullDim_residueValuationSubring_add A A le_rfl
