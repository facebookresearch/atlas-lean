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
# Krull dimension is preserved under integral extensions

For an integral `R`-algebra `S`, `ringKrullDim S = ringKrullDim R`
(assuming `FaithfulSMul R S` for the `≤` direction from `R` to `S`).
Both directions go through prime-ideal chains: the inequality
`dim S ≤ dim R` is `ringKrullDim_le_of_integral`
(`MathlibExt/RingTheory/Ideal/IntegralKrullDim.lean`), from
incomparability making `PrimeSpectrum.comap` strictly monotone;
going-up
(`Ideal.exists_ltSeries_of_hasGoingUp`, available through the
`Algebra.HasGoingUp.of_isIntegral` instance) lifts every chain in `R`
to a chain of the same length in `S`, giving `dim R ≤ dim S`.

The faithful hypothesis is essential for the second direction: without
it, primes of `R` need not lift at all (e.g. `k[x] → k` sends a
one-dimensional ring to a zero-dimensional one).

This is the integral-transfer step toward the maximal-height fact for
finitely generated domains over a field (Hartshorne III.9
Corollary 9.6): combined with Noether normalization
(`exists_integral_inj_algHom_of_fg`) it gives `ringKrullDim A = s`
for a domain `A` finite over `k[X₁, ..., Xₛ]`. Per-prime height
equality needs further catenary input and is not attempted here.

## Main results

* `Algebra.IsIntegral.le_ringKrullDim_of_isIntegral`: `dim R ≤ dim S`
  under `FaithfulSMul`.
* `Algebra.IsIntegral.ringKrullDim_eq_of_isIntegral`: the equality.

-/

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.IsIntegral R S]

/-- An integral extension with faithful scalars does not decrease Krull
dimension: every chain in `R` lifts to a chain of the same length in
`S` by going-up. -/
theorem Algebra.IsIntegral.le_ringKrullDim_of_isIntegral [FaithfulSMul R S] :
    ringKrullDim R ≤ ringKrullDim S := by
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun l ↦ ?_
  obtain ⟨Q⟩ :=
    (inferInstance : Nonempty (Ideal.primesOver (RelSeries.head l).asIdeal S))
  obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l Q.1
  calc (l.length : WithBot ℕ∞) = (L.length : WithBot ℕ∞) := by rw [hlen]
    _ ≤ Order.krullDim (PrimeSpectrum S) := Order.LTSeries.length_le_krullDim L

/-- Krull dimension is preserved under integral extensions with faithful
scalars. -/
theorem Algebra.IsIntegral.ringKrullDim_eq_of_isIntegral [FaithfulSMul R S] :
    ringKrullDim S = ringKrullDim R :=
  le_antisymm ringKrullDim_le_of_integral
    Algebra.IsIntegral.le_ringKrullDim_of_isIntegral

end
