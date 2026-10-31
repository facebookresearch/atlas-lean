/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Dimension preservation under integral extensions
For an integral extension with injective structure map (`Algebra.IsIntegral R S`
plus `FaithfulSMul R S`), Krull dimension is preserved:
`ringKrullDim S = ringKrullDim R`. Both inequalities come from moving chains of
primes between the two rings:

* `ringKrullDim S ≤ ringKrullDim R`: contraction along an integral extension
  preserves strict inclusion (incomparability), so prime chains in `S` map to
  prime chains in `R` of the same length.
* `ringKrullDim R ≤ ringKrullDim S`: prime chains in `R` lift to prime chains in
  `S` of the same length, by lying-over at the bottom prime followed by going-up.

No Noetherian or domain hypotheses are needed. The corollaries below restate the
result for injective integral (resp. finite) `K`-algebra homs — the exact output
shape of Noether normalization that chunk B3 (`PolynomialCatenary.lean`) consumes
(instantiated at `A = MvPolynomial (Fin s) K`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-- Krull dimension is preserved under integral extensions with injective
structure map: prime chains push down by contraction (incomparability) and lift
up by lying-over plus going-up.

## References

* `Mathlib/RingTheory/KrullDimension/Basic.lean`, `ringKrullDim`
  (`ringKrullDim R = Order.krullDim (PrimeSpectrum R)`).
* `Mathlib/Order/KrullDimension.lean`, `Order.krullDim`
  (definition as supremum of chain lengths),
  `Order.krullDim_le_of_strictMono`
  (a `StrictMono` map gives `krullDim α ≤ krullDim β`),
  `Order.LTSeries.length_le_krullDim`, `Order.krullDim_eq_bot`.
* `Mathlib/RingTheory/Spectrum/Prime/Defs.lean`,
  `PrimeSpectrum.asIdeal_lt_asIdeal` (`x.asIdeal < y.asIdeal ↔ x < y`).
* `Mathlib/RingTheory/Spectrum/Prime/RingHom.lean`, `PrimeSpectrum.comap`,
  `PrimeSpectrum.comap_asIdeal`.
* `Mathlib/RingTheory/Ideal/GoingUp.lean`, `IsIntegral.under_lt_under`
  (incomparability: `I < J → I.under R < J.under R`),
  `Ideal.exists_ideal_over_prime_of_isIntegral` (lying-over).
* `Mathlib/RingTheory/Ideal/HasGoingUp.lean`,
  `Ideal.exists_ltSeries_of_hasGoingUp` (chain lifting),
  `Algebra.HasGoingUp.of_isIntegral` (integral algebras go up).
* `Mathlib/RingTheory/Ideal/Over.lean`, `Ideal.under_bot`
  (contraction of `⊥` is `⊥` under `FaithfulSMul`).

Deviation note: the original unmixedness plan §2 chunk B2 asks for this "between Noetherian
domains"; the proof uses only integrality plus injectivity, so the statement is
given in that generality (no `IsNoetherianRing`/`IsDomain` hypotheses). -/
theorem ringKrullDim_eq_of_isIntegral {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] [FaithfulSMul R S] :
    ringKrullDim S = ringKrullDim R := by
  apply le_antisymm
  · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
    intro x y hxy
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hxy ⊢
    exact Ideal.IsIntegral.under_lt_under hxy
  · have key : ∀ l : LTSeries (PrimeSpectrum R),
        ∃ L : LTSeries (PrimeSpectrum S), L.length = l.length := by
      intro l
      have hbot : (⊥ : Ideal S).under R ≤ (RelSeries.head l).asIdeal := by
        rw [Ideal.under_bot]
        exact bot_le
      obtain ⟨Q, -, hQprime, hQunder⟩ :=
        Ideal.exists_ideal_over_prime_of_isIntegral (RelSeries.head l).asIdeal ⊥ hbot
      have : Q.LiesOver (RelSeries.head l).asIdeal := ⟨hQunder.symm⟩
      have := hQprime
      obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l Q
      exact ⟨L, hlen⟩
    rcases isEmpty_or_nonempty (PrimeSpectrum R) with hempty | hne
    · have := hempty
      have hbot : ringKrullDim R = ⊥ := Order.krullDim_eq_bot
      rw [hbot]
      exact bot_le
    · unfold ringKrullDim Order.krullDim
      refine iSup_le fun l => ?_
      obtain ⟨L, hlen⟩ := key l
      rw [← hlen]
      exact Order.LTSeries.length_le_krullDim L

/-- Dimension preservation for an injective integral `K`-algebra hom, the output
shape of `exists_integral_inj_algHom_of_fg`: chunk B3 instantiates this at
`A = MvPolynomial (Fin s) K`.

## References

* `Mathlib/Algebra/Algebra/Defs.lean`, `RingHom.toAlgebra`,
  `RingHom.algebraMap_toAlgebra` (`@algebraMap _ _ _ _ i.toAlgebra = i`).
* `Mathlib/RingTheory/IntegralClosure/Algebra/Defs.lean`,
  `algebraMap_isIntegral_iff`
  (`(algebraMap R A).IsIntegral ↔ Algebra.IsIntegral R A`).
* `Mathlib/Algebra/Algebra/Basic.lean`,
  `faithfulSMul_iff_algebraMap_injective`
  (`FaithfulSMul R A ↔ Function.Injective (algebraMap R A)`). -/
theorem ringKrullDim_eq_of_algHom_isIntegral {K A B : Type*} [CommRing K]
    [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (g : A →ₐ[K] B) (hinj : Function.Injective g) (hint : g.IsIntegral) :
    ringKrullDim B = ringKrullDim A := by
  let : Algebra A B := g.toRingHom.toAlgebra
  have hInt : Algebra.IsIntegral A B := by
    rw [← algebraMap_isIntegral_iff, RingHom.algebraMap_toAlgebra]
    exact hint
  have hfaith : FaithfulSMul A B := by
    rw [faithfulSMul_iff_algebraMap_injective, RingHom.algebraMap_toAlgebra]
    exact hinj
  exact ringKrullDim_eq_of_isIntegral

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
