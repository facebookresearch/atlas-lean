/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.FinitePresentationNilpotentThickening

@[expose] public section

universe u v w

/-- `exactSource` consumer with the original binders. -/
example {P B' : Type u} [CommRing P] [CommRing B'] (p : P →+* B')
    (hp : Function.Surjective p) (hI : IsNilpotent (RingHom.ker p))
    {A : Type v} [CommRing A] [Algebra P A] [Module.Flat P A]
    {A' : Type w} [CommRing A'] [Algebra B' A']
    (q : A →+* A') (hq : Function.Surjective q)
    (hcomm : q.comp (algebraMap P A) = (algebraMap B' A').comp p)
    (hker : RingHom.ker q = (RingHom.ker p).map (algebraMap P A))
    (hfp' : Algebra.FinitePresentation B' A') :
    Algebra.FinitePresentation P A :=
  Algebra.FinitePresentation.of_surjective_of_isNilpotent_ker_of_flat_of_finitePresentation
    p hp hI q hq hcomm hker hfp'

/-- Higher-universe consumer (`Type 1` in place of the original universes). -/
example {P B' : Type 1} [CommRing P] [CommRing B'] (p : P →+* B')
    (hp : Function.Surjective p) (hI : IsNilpotent (RingHom.ker p))
    {A : Type 1} [CommRing A] [Algebra P A] [Module.Flat P A]
    {A' : Type 1} [CommRing A'] [Algebra B' A']
    (q : A →+* A') (hq : Function.Surjective q)
    (hcomm : q.comp (algebraMap P A) = (algebraMap B' A').comp p)
    (hker : RingHom.ker q = (RingHom.ker p).map (algebraMap P A))
    (hfp' : Algebra.FinitePresentation B' A') :
    Algebra.FinitePresentation P A :=
  Algebra.FinitePresentation.of_surjective_of_isNilpotent_ker_of_flat_of_finitePresentation
    p hp hI q hq hcomm hker hfp'

/-- Boundary case: when `B' = P` and both maps are identities, the conclusion
is the assumed finite presentation; the nilpotent kernel is `⊥`. -/
example {P A : Type*} [CommRing P] [CommRing A] [Algebra P A] [Module.Flat P A]
    (hfp : Algebra.FinitePresentation P A) : Algebra.FinitePresentation P A :=
  hfp
