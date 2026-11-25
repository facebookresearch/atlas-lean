/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Polynomial.AevalHeightOne

@[expose] public section

/-- Exact-source consumer: the original binders and hypotheses. -/
private theorem exactSource
    {A C : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing C] [IsDomain C] [Algebra A C]
    (x : C) (hx : Function.Injective (Polynomial.aeval (R := A) x))
    (hint : (Polynomial.aeval (R := A) x).toRingHom.IsIntegral)
    (Q : Ideal C) [Q.IsPrime] (hQ : Q.height = 1)
    (hQm : (IsLocalRing.maximalIdeal A).map (algebraMap A C) ≤ Q)
    (P : Polynomial A) (hP : P.map (IsLocalRing.residue A) ≠ 0) :
    Polynomial.aeval x P ∉ Q :=
  Polynomial.aeval_notMem_of_height_eq_one_of_map_residue_ne_zero x hx hint Q hQ hQm P hP

/-- Boundary: without the nonzero-residue hypothesis the conclusion fails
already for `P = 0`, whose evaluation lies in every ideal. -/
example {A C : Type*} [CommRing A] [CommRing C] [Algebra A C]
    (x : C) (Q : Ideal C) :
    Polynomial.aeval x (0 : Polynomial A) ∈ Q := by
  simp
