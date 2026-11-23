/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.K0.Rank

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace MathlibExtTest.KTheory.RingK0Rank

open AlgebraicKTheory

variable (R : Type u) [CommRing R]

example (P : FGProjectiveCat.{u} R) (p : PrimeSpectrum R) :
    FGProjectiveCat.rankInt P p =
      (Module.rankAtStalk (R := R) P p : ℤ) := by
  simp

example (P : FGProjectiveCat.{u} R) :
    RingK0.rank R (K0.mk P) = FGProjectiveCat.rankInt P := by
  simp

example (P Q : FGProjectiveCat.{u} R) :
    RingK0.rank R (K0.mk P + K0.mk Q) =
      FGProjectiveCat.rankInt P + FGProjectiveCat.rankInt Q := by
  simp

example (P Q : FGProjectiveCat.{u} R) :
    RingK0.rank R (K0.mk P * K0.mk Q) =
      FGProjectiveCat.rankInt P * FGProjectiveCat.rankInt Q := by
  simp

example : RingK0.rank R 1 = 1 := by
  simp

example (x : RingK0 R) :
    x ∈ RingK0.reducedIdeal R ↔ RingK0.rank R x = 0 := by
  simp

example {S : Type u} [CommRing S] (f : R →+* S) :
    (RingK0.rank S).comp
        (RingK0.functor.map (CommRingCat.ofHom f)).hom =
      (LocallyConstant.comapRingHom
        (⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩ :
          C(PrimeSpectrum S, PrimeSpectrum R))).comp (RingK0.rank R) := by
  exact RingK0.rank_naturality R f

end MathlibExtTest.KTheory.RingK0Rank

end
