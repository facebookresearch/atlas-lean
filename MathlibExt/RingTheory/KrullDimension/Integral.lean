/-
Copyright (c) 2026 @junekim623, Muse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original contributors: @junekim623
-/

/-
Author: @toskua
-/


module

public import Mathlib.Order.KrullDimension
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import MathlibExt.RingTheory.Ideal.IntegralKrullDim

/-
Original 2026 development credited to @junekim623 and Muse.
-/

/-!
# Krull dimension of faithful integral extensions

Let S be a commutative integral R-algebra with faithful scalar action, equivalently an
injective scalar homomorphism R → S. Going-up lifts every finite chain of prime ideals of R to
one of the same length in S, giving ringKrullDim R ≤ ringKrullDim S.

Incomparability for integral extensions gives the reverse inequality, so ringKrullDim S =
ringKrullDim R. These statements use neither a Noetherian nor a finite-generation hypothesis;
the dimensions are those of the full prime spectra.
-/

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.IsIntegral R S]

/-- Krull dimension inequality from a faithful integral extension.

For commutative rings R,S with S integral over R and FaithfulSMul R S, ringKrullDim R ≤
ringKrullDim S. A prime above the first prime in each chain exists, and going-up lifts the
chain without changing its length. -/
theorem Algebra.IsIntegral.le_ringKrullDim_of_isIntegral [FaithfulSMul R S] :
    ringKrullDim R ≤ ringKrullDim S := by
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun l ↦ ?_
  obtain ⟨Q⟩ :=
    (inferInstance : Nonempty (Ideal.primesOver (RelSeries.head l).asIdeal S))
  obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l Q.1
  calc (l.length : WithBot ℕ∞) = (L.length : WithBot ℕ∞) := by rw [hlen]
    _ ≤ Order.krullDim (PrimeSpectrum S) := Order.LTSeries.length_le_krullDim L

/-- Krull dimension equality for faithful integral scalars.

If S is a commutative integral R-algebra and the scalar action is faithful, then ringKrullDim
S = ringKrullDim R. Going-up gives the inequality from R to S, and integral incomparability
gives the inequality from S to R. -/
theorem Algebra.IsIntegral.ringKrullDim_eq_of_isIntegral [FaithfulSMul R S] :
    ringKrullDim S = ringKrullDim R :=
  le_antisymm ringKrullDim_le_of_integral
    Algebra.IsIntegral.le_ringKrullDim_of_isIntegral

end
