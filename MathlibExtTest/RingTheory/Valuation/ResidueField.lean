/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Valuation.ResidueField

@[expose] public section

example {K : Type*} [Field K] [IsAlgClosed K] (A : ValuationSubring K)
    (f : Polynomial A) (hf : f.Monic) (hd : f.natDegree ≠ 0) :
    ∃ x : A, Polynomial.aeval (x : K) f = 0 :=
  ValuationSubring.exists_root_mem_of_monic A f hf hd

example {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L) :
    IsAlgClosed (IsLocalRing.ResidueField ↥A) :=
  ValuationSubring.isAlgClosed_residueField A
