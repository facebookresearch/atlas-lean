/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.IsGaloisGroup.IntegrallyClosed

/-- Consumer with the original binders: the fixed ring of a Galois group
action on an integrally closed domain is integrally closed. -/
example (G : Type*) [Group G] {A B : Type*} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
    [MulSemiringAction G B] [IsGaloisGroup G A B] [IsIntegrallyClosed B] :
    IsIntegrallyClosed A :=
  IsGaloisGroup.isIntegrallyClosed_of_isIntegrallyClosed (A := A) (B := B) G

/-- The same consumer in a higher universe for the acting group. -/
example (G : Type 1) [Group G] {A B : Type*} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
    [MulSemiringAction G B] [IsGaloisGroup G A B] [IsIntegrallyClosed B] :
    IsIntegrallyClosed A :=
  IsGaloisGroup.isIntegrallyClosed_of_isIntegrallyClosed (A := A) (B := B) G

