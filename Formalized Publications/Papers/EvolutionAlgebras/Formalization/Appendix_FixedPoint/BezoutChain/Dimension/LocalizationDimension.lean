/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Order.KrullDimension
import Mathlib.Order.Monotone.Defs
import Mathlib.RingTheory.Ideal.Lattice
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Localization-dimension API (finiteness-attack lane residuals)

Closes the three dimension-geometry residuals consumed by
`Geometry/AffineFinite.lean` (`affineZero_finite_of_successiveRegular`,
conditional on exactly `[hsucc, hambient, hglob]`):

1. **Localization dimension bound** (§1): `ringKrullDim S ≤ ringKrullDim R`
   for any localization (`ringKrullDim_localization_le`, general submonoid
   form), hence at primes (`ringKrullDim_atPrime_le`), with `KrullDimLE`
   corollaries. Instantiated, this discharges `AmbientLocalDimBound`
   (`ambientLocalDimBound_of_ringKrullDim_le` has exactly the consumed shape
   with `J := span (range (chartPoly m K F))`, `B := ↑(m+1)`; the remaining
   arithmetic input `ringKrullDim (MvPolynomial (Fin (m+1)) K) = ↑(m+1)` is
   `Dimension.PolynomialCatenary.mvPolynomial_ringKrullDim`, cited by name).
2. **Quotient-localization commutation at a general prime** (§2):
   `quotLocPrimeSpectrumOrderIso` identifies primes of `S ⧸ J.map f`
   (`S` a localization of `R` at `P ⊇ J`) with primes of `R` between `J`
   and `P`. This extends the maximal-only ring-level precedent
   `IsLocalization.AtPrime.equivQuotientMapOfIsMaximal` (which needs
   `P.IsMaximal`) to a general prime at spectrum level — the level every
   dimension argument consumes.
3. **Local-to-global dim-0 transfer** (§3):
   `krullDimLE_zero_quotient_of_localized` and the span-range exact-shape
   `krullDimLE_zero_quotient_span_of_localized` (antecedent and conclusion
   match `LocalToGlobalDimZero` with `q := chartPoly m K F`).

## Approach survey (Mathlib v4.34.0, grep-verified in `.lake/packages/mathlib`)

* `Order.krullDim_le_of_strictMono` (`Mathlib/Order/KrullDimension.lean`):
  dimension drops along a strictly monotone map of spectra.
* `PrimeSpectrum.comap` (`.../Spectrum/Prime/RingHom.lean`) is monotone and,
  for a localization, injective — the injectivity argument
  (`IsLocalization.map_under`) is reproduced inline from
  `PrimeSpectrum.localization_comap_injective`
  (`.../Spectrum/Prime/Topology.lean`, not imported) to keep imports narrow.
* `IsLocalization.AtPrime.primeSpectrumOrderIso`
  (`.../Localization/AtPrime/Basic.lean`): `Spec S ≃o ↥P`.
* `Ideal.primeSpectrumQuotientOrderIsoZeroLocus`
  (`.../Spectrum/Prime/RingHom.lean`): `Spec (R ⧸ I) ≃o zeroLocus I`.
* `Ring.krullDimLE_zero_iff`, `Ideal.isMaximal_of_isPrime`
  (`.../KrullDimension/Basic.lean`): dim-0 means every prime is maximal.
* `Ideal.exists_le_maximal`, `Ideal.IsMaximal.eq_of_le`
  (`.../Ideal/Maximal.lean`): Krull's theorem and maximality rigidity.

## Status

* `ringKrullDim (Localization.AtPrime P) ≤ ringKrullDim R`: unconditional.
* `AmbientLocalDimBound`-shape: unconditional (modulo the separately-proved
  `mvPolynomial_ringKrullDim` equation, by-name input).
* Quot-loc spectrum commutation at a general prime: unconditional.
* `LocalToGlobalDimZero`-shape transfer: unconditional.

## DAG safety

Mathlib-only imports. In particular this file never imports
`Geometry.MkSystemChart` (home of `chartPoly`) or `Geometry.AffineFinite`
(home of `AmbientLocalDimBound`/`LocalToGlobalDimZero`): the corollaries are
stated generally (arbitrary `J` / `q`) so that `AffineFinite` can instantiate
them — importing either would either invert the Dimension/Geometry layering
or forbid `AffineFinite` from importing this file. No other file imports this
one yet.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace LocalizationDimension

/-! ## §1 Localization dimension bound

`PrimeSpectrum.comap (algebraMap R S)` is strictly monotone for a
localization (monotone everywhere; injective by `IsLocalization.map_under`),
so Krull dimension drops. -/

/-- Localizing can only drop Krull dimension (general submonoid form).

## References

* `Mathlib/Order/KrullDimension.lean`, `Order.krullDim_le_of_strictMono`.
* `Mathlib/Order/Monotone/Defs.lean`, `Monotone.strictMono_of_injective`.
* `Mathlib/RingTheory/Spectrum/Prime/RingHom.lean`, `PrimeSpectrum.comap`,
  `PrimeSpectrum.comap_asIdeal`.
* `Mathlib/RingTheory/Localization/Ideal.lean`, `IsLocalization.map_under`
  (the injectivity argument of `PrimeSpectrum.localization_comap_injective`,
  `Mathlib/RingTheory/Spectrum/Prime/Topology.lean`, reproduced inline).
* `Mathlib/RingTheory/Ideal/Maps.lean`, `Ideal.comap_mono`. -/
theorem ringKrullDim_localization_le {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    ringKrullDim S ≤ ringKrullDim R := by
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) ?_
  refine Monotone.strictMono_of_injective (fun _ _ h => Ideal.comap_mono h) ?_
  intro p q h
  have h2 := congrArg
    (fun x : PrimeSpectrum R => Ideal.map (algebraMap R S) x.asIdeal) h
  simp only [PrimeSpectrum.comap_asIdeal] at h2
  have e1 : Ideal.map (algebraMap R S)
      (Ideal.comap (algebraMap R S) p.asIdeal) = p.asIdeal :=
    IsLocalization.map_under M S _
  have e2 : Ideal.map (algebraMap R S)
      (Ideal.comap (algebraMap R S) q.asIdeal) = q.asIdeal :=
    IsLocalization.map_under M S _
  rw [e1, e2] at h2
  exact PrimeSpectrum.ext h2

/-- Localizing at a prime can only drop Krull dimension.

## References

* This module,
  `Appendix_FixedPoint.BezoutChain.LocalizationDimension.ringKrullDim_localization_le` (proved
  above). -/
theorem ringKrullDim_atPrime_le {R : Type*} [CommRing R] (P : Ideal R)
    [P.IsPrime] :
    ringKrullDim (Localization.AtPrime P) ≤ ringKrullDim R :=
  ringKrullDim_localization_le P.primeCompl

/-- Ambient local-dimension bound in exactly the shape `AffineFinite`
consumes (`AmbientLocalDimBound` with `J := span (range q)`, `B := ↑(m+1)`):
every prime containing `J` localizes to dimension `≤ B` as soon as the
ambient ring has dimension `≤ B`. The by-name arithmetic input at the
`chartPoly` instantiation is
`Dimension.PolynomialCatenary.mvPolynomial_ringKrullDim`.


## References

* `Geometry.AffineFinite`, `Appendix_FixedPoint.BezoutChain.AmbientLocalDimBound` (consumer shape).
* `Dimension.PolynomialCatenary`, `Appendix_FixedPoint.BezoutChain.mvPolynomial_ringKrullDim`
  (by-name input for `hR`).
* This module, `Appendix_FixedPoint.BezoutChain.LocalizationDimension.ringKrullDim_atPrime_le`
  (proved above). -/
theorem ambientLocalDimBound_of_ringKrullDim_le {R : Type*} [CommRing R]
    (J : Ideal R) {B : WithBot ℕ∞} (hR : ringKrullDim R ≤ B) :
    ∀ (P : Ideal R) [P.IsPrime],
      J ≤ P → ringKrullDim (Localization.AtPrime P) ≤ B := by
  intro P _ _
  exact (ringKrullDim_atPrime_le P).trans hR

/-! ## §2 Quotient-localization commutation at a general prime

Primes of `S ⧸ J.map (algebraMap R S)` (`S` a localization of `R` at a prime
`P ⊇ J`) are exactly the primes of `R` between `J` and `P`: quotient
correspondence (`Ideal.primeSpectrumQuotientOrderIsoZeroLocus`) followed by
the localization correspondence
(`IsLocalization.AtPrime.primeSpectrumOrderIso`), with the bridge
`J.map f ≤ q ↔ J ≤ q.under R` (`Ideal.map_le_iff_le_comap`). -/

/-- The `zeroLocus` half of the quotient-localization correspondence: primes
of `S` containing `J.map f` are the primes of `R` between `J` and `P`.

## References

* `Mathlib/RingTheory/Localization/AtPrime/Basic.lean`,
  `IsLocalization.AtPrime.primeSpectrumOrderIso`.
* `Mathlib/RingTheory/Ideal/Maps.lean`, `Ideal.map_le_iff_le_comap`,
  `Ideal.map_mono`. -/
noncomputable def zeroLocusAtPrimeOrderIso {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (P : Ideal R) [P.IsPrime]
    [IsLocalization.AtPrime S P] (J : Ideal R) :
    ↥(PrimeSpectrum.zeroLocus (R := S) (↑(J.map (algebraMap R S)) : Set S)) ≃o
      {p : PrimeSpectrum R // J ≤ p.asIdeal ∧ p.asIdeal ≤ P} := by
  let e := IsLocalization.AtPrime.primeSpectrumOrderIso S P
  refine { toFun := fun q => ⟨(e q.1).1, ?_, ?_⟩,
           invFun := fun p => ⟨e.symm ⟨p.1, p.2.2⟩, ?_⟩,
           left_inv := ?_, right_inv := ?_, map_rel_iff' := ?_ }
  · have hq : (↑(J.map (algebraMap R S)) : Set S) ⊆ q.1.asIdeal := q.2
    have hle : J.map (algebraMap R S) ≤ q.1.asIdeal := hq
    exact (Ideal.map_le_iff_le_comap (f := algebraMap R S)).mp hle
  · exact (e q.1).2
  · have hmap : J.map (algebraMap R S)
        ≤ p.1.asIdeal.map (algebraMap R S) :=
      Ideal.map_mono p.2.1
    exact hmap
  · exact fun q => Subtype.ext (e.left_inv q.1)
  · intro p
    apply Subtype.ext
    have hrr : (e (e.symm ⟨p.1, p.2.2⟩)).1 = p.1 :=
      congrArg Subtype.val (e.right_inv ⟨p.1, p.2.2⟩)
    exact hrr
  · exact fun {a b} => e.map_rel_iff'

/-- Quotient-localization commutation at a general prime, spectrum level:
primes of the localized quotient `S ⧸ J.map f` correspond exactly to primes
of `R` between `J` and `P`. Extends the maximal-only ring-level precedent
`IsLocalization.AtPrime.equivQuotientMapOfIsMaximal` to a general prime.

## References

* `Mathlib/RingTheory/Spectrum/Prime/RingHom.lean`,
  `Ideal.primeSpectrumQuotientOrderIsoZeroLocus`.
* This module, `Appendix_FixedPoint.BezoutChain.LocalizationDimension.zeroLocusAtPrimeOrderIso`
  (proved above). -/
noncomputable def quotLocPrimeSpectrumOrderIso {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (P : Ideal R) [P.IsPrime]
    [IsLocalization.AtPrime S P] (J : Ideal R) :
    PrimeSpectrum (S ⧸ J.map (algebraMap R S)) ≃o
      {p : PrimeSpectrum R // J ≤ p.asIdeal ∧ p.asIdeal ≤ P} :=
  (Ideal.primeSpectrumQuotientOrderIsoZeroLocus
    (J.map (algebraMap R S))).trans
    (zeroLocusAtPrimeOrderIso (S := S) P J)

/-! ## §3 Local-to-global dimension-zero transfer

If every localization-quotient `R_P ⧸ J.map f` (over primes `P ⊇ J`) is
zero-dimensional, so is `R ⧸ J`: a prime `Q` of `R ⧸ J` strictly below `T`
pulls back to `comap Q < comap T` in `R` (strictness via
`Ideal.map_comap_of_surjective`); Krull's theorem extends `comap T` to a
maximal `M`, and §2 turns `comap Q < M` into a strict chain in the
zero-dimensional `R_M ⧸ J.map f`, contradicting maximality there. -/

/-- Local-to-global dimension-zero transfer (map form): `KrullDimLE 0` of
every localization-quotient over primes containing `J` implies `KrullDimLE 0`
of `R ⧸ J`.


## References

* `Mathlib/RingTheory/KrullDimension/Basic.lean`, `Ring.krullDimLE_zero_iff`,
  `Ideal.isMaximal_of_isPrime`.
* `Mathlib/RingTheory/Ideal/Maps.lean`, `Ideal.map_comap_of_surjective`,
  `Ideal.comap_mono`, `Ideal.ker_le_comap`, `Ideal.mem_comap`,
  `Ideal.IsPrime.comap` (instance).
* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`,
  `Ideal.Quotient.mk_surjective`.
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`, `Ideal.mk_ker`.
* `Mathlib/RingTheory/Ideal/Maximal.lean`, `Ideal.exists_le_maximal`,
  `Ideal.IsMaximal.eq_of_le`, `Ideal.IsMaximal.isPrime'` (instance).
* `Mathlib/RingTheory/Ideal/Lattice.lean`, `Ideal.eq_top_iff_one`.
* `Mathlib/RingTheory/Ideal/Prime.lean`, `Ideal.IsPrime.ne_top`.
* This module,
  `Appendix_FixedPoint.BezoutChain.LocalizationDimension.quotLocPrimeSpectrumOrderIso` (proved
  above). -/
theorem krullDimLE_zero_quotient_of_localized {R : Type*} [CommRing R]
    (J : Ideal R)
    (h : ∀ (P : Ideal R) [P.IsPrime], J ≤ P →
      Ring.KrullDimLE 0 (Localization.AtPrime P ⧸
        J.map (algebraMap R (Localization.AtPrime P)))) :
    Ring.KrullDimLE 0 (R ⧸ J) := by
  rw [Ring.krullDimLE_zero_iff]
  intro Q hQ
  have := hQ
  refine ⟨hQ.ne_top, fun T hQT => ?_⟩
  by_cases hT : T = ⊤
  · exact hT
  · have hsurj : Function.Surjective (Ideal.Quotient.mk J) :=
      Ideal.Quotient.mk_surjective
    have eQ : Ideal.map (Ideal.Quotient.mk J)
        (Ideal.comap (Ideal.Quotient.mk J) Q) = Q :=
      Ideal.map_comap_of_surjective _ hsurj Q
    have eT : Ideal.map (Ideal.Quotient.mk J)
        (Ideal.comap (Ideal.Quotient.mk J) T) = T :=
      Ideal.map_comap_of_surjective _ hsurj T
    have hne : Ideal.comap (Ideal.Quotient.mk J) Q
        ≠ Ideal.comap (Ideal.Quotient.mk J) T := by
      intro hcon
      apply hQT.ne
      rw [← eQ, ← eT, hcon]
    have hle : Ideal.comap (Ideal.Quotient.mk J) Q
        ≤ Ideal.comap (Ideal.Quotient.mk J) T :=
      Ideal.comap_mono hQT.le
    have hT₀ : Ideal.comap (Ideal.Quotient.mk J) T ≠ ⊤ := by
      intro hcon
      apply hT
      rw [Ideal.eq_top_iff_one]
      have h1 : (1 : R) ∈ Ideal.comap (Ideal.Quotient.mk J) T := by
        rw [hcon]
        trivial
      rw [Ideal.mem_comap, map_one] at h1
      exact h1
    obtain ⟨M, hMmax, hTM⟩ :=
      Ideal.exists_le_maximal (Ideal.comap (Ideal.Quotient.mk J) T) hT₀
    have := hMmax
    have hJQ : J ≤ Ideal.comap (Ideal.Quotient.mk J) Q := by
      have hker : RingHom.ker (Ideal.Quotient.mk J)
          ≤ Ideal.comap (Ideal.Quotient.mk J) Q :=
        Ideal.ker_le_comap _
      rwa [Ideal.mk_ker] at hker
    have hQM : Ideal.comap (Ideal.Quotient.mk J) Q ≤ M :=
      le_trans hle hTM
    have hQMn : Ideal.comap (Ideal.Quotient.mk J) Q ≠ M := by
      intro hcon
      apply hne
      apply le_antisymm hle
      rw [hcon]
      exact hTM
    have hJM : J ≤ M := le_trans hJQ hQM
    have hloc : Ring.KrullDimLE 0 (Localization.AtPrime M ⧸
        J.map (algebraMap R (Localization.AtPrime M))) :=
      h M hJM
    have := hloc
    let eM := quotLocPrimeSpectrumOrderIso (S := Localization.AtPrime M) M J
    let q₀ : PrimeSpectrum R :=
      ⟨Ideal.comap (Ideal.Quotient.mk J) Q, inferInstance⟩
    let m₀ : PrimeSpectrum R := ⟨M, inferInstance⟩
    have hQMn' : q₀ ≠ m₀ :=
      fun hcon => hQMn (congrArg PrimeSpectrum.asIdeal hcon)
    have hlt : q₀ < m₀ := lt_of_le_of_ne hQM hQMn'
    have hsub : (⟨q₀, hJQ, hQM⟩ :
        {p : PrimeSpectrum R // J ≤ p.asIdeal ∧ p.asIdeal ≤ M})
        < ⟨m₀, hJM, le_rfl⟩ :=
      hlt
    have hstrict : eM.symm ⟨q₀, hJQ, hQM⟩ < eM.symm ⟨m₀, hJM, le_rfl⟩ :=
      eM.symm.strictMono hsub
    have hmax : (eM.symm ⟨q₀, hJQ, hQM⟩).asIdeal.IsMaximal :=
      Ideal.isMaximal_of_isPrime _
    have heq : (eM.symm ⟨q₀, hJQ, hQM⟩).asIdeal
        = (eM.symm ⟨m₀, hJM, le_rfl⟩).asIdeal :=
      hmax.eq_of_le (eM.symm ⟨m₀, hJM, le_rfl⟩).isPrime.ne_top
        (le_of_lt hstrict)
    have hcon : eM.symm ⟨q₀, hJQ, hQM⟩ = eM.symm ⟨m₀, hJM, le_rfl⟩ :=
      PrimeSpectrum.ext heq
    exact absurd hcon (ne_of_lt hstrict)

/-- The `map`-`span` bridge: mapping a spanned range is spanning the mapped
range. Connects the `map` form of §2–§3 to the `span (range (f ∘ q))` shape
`AffineFinite` consumes.

## References

* `Mathlib/RingTheory/Ideal/Maps.lean`, `Ideal.map_span`. -/
theorem map_span_range_comp {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {k : ℕ} (q : Fin k → R) :
    (Ideal.span (Set.range q)).map (algebraMap R S)
      = Ideal.span (Set.range (algebraMap R S ∘ q)) := by
  rw [Ideal.map_span]
  congr 1
  ext y
  simp only [Set.mem_range, Set.mem_image]
  constructor
  · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨q i, ⟨i, rfl⟩, rfl⟩

/-- Local-to-global dimension-zero transfer in exactly the shape `AffineFinite`
consumes (`LocalToGlobalDimZero` with `q := chartPoly m K F`): `KrullDimLE 0`
of every `span`-shaped localization-quotient implies `KrullDimLE 0` of the
`span`-shaped global quotient.


## References

* `Geometry.AffineFinite`, `Appendix_FixedPoint.BezoutChain.LocalToGlobalDimZero` (consumer shape).
* This module,
  `Appendix_FixedPoint.BezoutChain.LocalizationDimension.krullDimLE_zero_quotient_of_localized`,
  `Appendix_FixedPoint.BezoutChain.LocalizationDimension.map_span_range_comp` (proved above). -/
theorem krullDimLE_zero_quotient_span_of_localized {R : Type*} [CommRing R]
    {k : ℕ} (q : Fin k → R)
    (h : ∀ (P : Ideal R) [P.IsPrime], Ideal.span (Set.range q) ≤ P →
      Ring.KrullDimLE 0 (Localization.AtPrime P ⧸
        Ideal.span (Set.range (algebraMap R (Localization.AtPrime P) ∘ q)))) :
    Ring.KrullDimLE 0 (R ⧸ Ideal.span (Set.range q)) := by
  apply krullDimLE_zero_quotient_of_localized
  intro P _ hJP
  have hEq := map_span_range_comp (S := Localization.AtPrime P) q
  rw [hEq]
  exact h P hJP

end LocalizationDimension
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
