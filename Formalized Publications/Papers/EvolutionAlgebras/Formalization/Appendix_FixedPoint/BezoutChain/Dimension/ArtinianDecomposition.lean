/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Geometry.LocalMultiplicity
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.OreLocalization.Ring
import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Artinian product-of-locals decomposition (G2 assembly)

This module assembles the Artinian input `haddLocal` consumes (`hdecomp`, gap
report G2 in `Geometry/LocalMultiplicity.lean`): the chart as the product of its local
rings over the locus. The exact consumed shape is `ChartDecomp`
(`Geometry/ChartFiltration.lean`):
`chartRing n K G ℓ ≃ₗ[K] ((p : ↥(locLocusFinset …)) → locFam … p)`.

## Mathlib v4.34.0 survey

* `Mathlib/RingTheory/Artinian/Module.lean`: `IsArtinianRing.of_finite`
  (finite over Artinian is Artinian), `Finite (MaximalSpectrum R)` for
  Artinian `R`, `IsArtinianRing.isMaximal_of_isPrime` (Artinian primes are
  maximal), `quotNilradicalEquivPi` / `quotNilradicalPowEquivPi` (CRT
  quotient decompositions), and `equivPi` (reduced Artinian
  `R ≃ₐ[R] ∀ m, R ⧸ m`).
* `Mathlib/RingTheory/Artinian/Ring.lean`: `localization_surjective`
  (`R → R[S⁻¹]` surjective for Artinian `R`), `isNilpotent_nilradical`.
* The full product-of-localizations is in-tree, via the discrete-spectrum
  route (this corrects the `LocalMultiplicity` G2 survey note, which predates the
  find): `Mathlib/RingTheory/Spectrum/Prime/Topology.lean`,
  `MaximalSpectrum.toPiLocalizationEquiv`
  (`R ≃ₐ[R] MaximalSpectrum.PiLocalization R` for discrete
  `PrimeSpectrum R`), with
  `Mathlib/RingTheory/Spectrum/Maximal/Localization.lean`,
  `MaximalSpectrum.PiLocalization R`
  (`Π I, Localization.AtPrime I.1`), and the
  `DiscreteTopology (PrimeSpectrum R)` instance for Artinian `R` in
  `Mathlib/RingTheory/Spectrum/Prime/Noetherian.lean` (which also proves
  the PrimeSpectrum analogue `finrank_eq_sum_primeSpectrum`).
* `Mathlib/Algebra/Ring/Idempotent.lean`: only elementary `IsIdempotentElem`
  algebra — no idempotent-lifting API (not needed: the spectrum route above
  bypasses lifting entirely).

## What is proved here

* §1 `isArtinianRing_of_moduleFinite` / `chartRing_isArtinianRing`: a finite
  `K`-algebra is Artinian (proved, discharges the algebraic precondition).
* §2 `maxSpecFintype`: the maximal spectrum of an Artinian ring is a fintype
  (proved).
* §3 reduced case: `equivPi_linearEquiv` (`R ≃ₗ[K] ∀ m, R ⧸ m`) and
  `finrank_eq_sum_quotients_of_reduced` (proved; needs `IsReduced R`,
  recorded as an independent fragment).
* §4 `equivPi_pow_of_nilpow` / `exists_pow_equivPi_quotient_pow`: some
  nilradical power gives `R ≃ₐ[R] ∀ m, R ⧸ m^n` (proved; quotient-level
  fragment).
* §5 `moduleFinite_localization_of_finite` /
  `chartLocFinite_of_chartFinite`: localizations of a finite chart are finite
  over `K` (proved; discharges `ChartLocFinite`, i.e. `haddLocal`'s
  `[hfinLoc]`, from `hfinA`).
* §6 `artinianPiLocalizationEquiv` (proved: the abstract Artinian structure
  core `R ≃ₗ[K] MaximalSpectrum.PiLocalization R`) and `chartDecomp_of`:
  the exact `ChartDecomp` shape, proved from `hfinA` plus the two-item
  conditional list below.

## Conditional remainder (narrowest list, for `chartDecomp_of`)

1. `hbij`: the locus↔`MaxSpec` bijection
   `MaximalSpectrum A ≃ ↥(locLocusFinset …)` (geometric; ChartFiltration
   owns the `hlift` bijection through the section presentation).
2. `hloc`: the fiber identification
   `∀ m, Localization.AtPrime m.asIdeal ≃ₗ[K] locFam … (hbij m)`
   (geometric; follows from `hbij` plus the `pointIdeal` coherence).

The former algebraic crux (`hstruct`, Artinian product-of-localizations) is
discharged in-file via `artinianPiLocalizationEquiv`; the remainder is purely
the geometric locus↔`MaxSpec` identification. Given `hfinA` + (1)–(2),
`chartDecomp_of` is proved by the structure equiv, fiberwise congruence
(`piCongrRight`), then reindexing (`piCongrLeft`).

## Import DAG

This module imports `Geometry.LocalMultiplicity` (exact consumer vocabulary
`locLocusFinset` / `locFam`, itself importing only `Statement.Definitions` plus
Mathlib) and Mathlib. It does not import `Geometry.ChartFiltration` (the
§6 consumer), so the edge
`ChartFiltration → ArtinianDecomposition` stays acyclic.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
open scoped BigOperators

/-! ## §1 Finite `K`-algebras are Artinian -/

/-- A module-finite algebra over a field is an Artinian ring: fields are
Artinian, and finiteness transports Artinian-ness down the tower.

## References

* `Mathlib/RingTheory/Artinian/Module.lean`, `IsArtinianRing.of_finite`
  (`(R S) [Ring R] [Ring S] [Module R S] [IsScalarTower R S S]
  [IsArtinianRing R] [Module.Finite R S]: IsArtinianRing S`),
  `DivisionRing.instIsArtinianRing`. -/
theorem isArtinianRing_of_moduleFinite (K A : Type*) [Field K] [CommRing A]
    [Algebra K A] [Module.Finite K A] : IsArtinianRing A :=
  IsArtinianRing.of_finite K A

/-- The chart is Artinian once it is finite over `K` (as an instance, so the
§2–§5 Artinian-side API resolves once `hfinA` is in context).

## References

* This module, `Appendix_FixedPoint.BezoutChain.isArtinianRing_of_moduleFinite`. -/
instance chartRing_isArtinianRing (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) [Module.Finite K (chartRing n K G ℓ)] :
    IsArtinianRing (chartRing n K G ℓ) :=
  isArtinianRing_of_moduleFinite K (chartRing n K G ℓ)

/-! ## §2 The maximal spectrum of an Artinian ring is a fintype -/

/-- Finiteness of the maximal spectrum, in `Fintype` form (the instance in
Mathlib is `Finite`; downstream `∑`/`piCongr` use needs `Fintype`).

## References

* `Mathlib/RingTheory/Artinian/Module.lean`,
  `IsArtinianRing.setOfPred_isMaximal_finite` and the
  `Finite (MaximalSpectrum R)` instance. -/
noncomputable abbrev maxSpecFintype (R : Type*) [CommRing R] [IsArtinianRing R] :
    Fintype (MaximalSpectrum R) :=
  Fintype.ofFinite _

/-! ## §3 Reduced case: product of residue fields -/

/-- The `K`-linear form of the reduced Artinian decomposition: `R`-linearity
restricts to `K`-linearity along the scalar tower.

## References

* `Mathlib/RingTheory/Artinian/Module.lean`, `IsArtinianRing.equivPi`
  (`[IsReduced R] : R ≃ₐ[R] ∀ I : MaximalSpectrum R, R ⧸ I.asIdeal`).
* `Mathlib/Algebra/Algebra/Equiv.lean`, `AlgEquiv.toLinearEquiv`.
* `Mathlib/Algebra/Module/Equiv/Basic.lean`, `LinearEquiv.restrictScalars`
  (via `Mathlib/Algebra/Module/LinearMap/Defs.lean`,
  `IsScalarTower.compatibleSMul`, with
  `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `Ideal.Quotient.algebra`, `Ideal.Quotient.isScalarTower`). -/
noncomputable def equivPi_linearEquiv (K R : Type*) [Field K] [CommRing R]
    [Algebra K R] [IsArtinianRing R] [IsReduced R] :
    R ≃ₗ[K] ∀ m : MaximalSpectrum R, R ⧸ m.asIdeal :=
  (IsArtinianRing.equivPi R).toLinearEquiv.restrictScalars K

/-- Quotients of a finite `K`-algebra are finite over `K` (via the surjective
`K`-algebra quotient map).

## References

* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `Ideal.Quotient.mkₐ` (`A →ₐ[R₁] A ⧸ I`),
  `Ideal.Quotient.mkₐ_surjective`.
* `Mathlib/RingTheory/Finiteness/Basic.lean`,
  `Module.Finite.of_surjective`. -/
theorem moduleFinite_quotient_of_finite (K R : Type*) [Field K] [CommRing R]
    [Algebra K R] [Module.Finite K R] (I : Ideal R) :
    Module.Finite K (R ⧸ I) := by
  have hsurj : Function.Surjective ⇑(Ideal.Quotient.mkₐ K I).toLinearMap :=
    Ideal.Quotient.mkₐ_surjective K I
  exact Module.Finite.of_surjective _ hsurj

/-- Reduced-case rank additivity: the `K`-length of a reduced Artinian
`K`-algebra is the sum of the residue-field lengths. (Needs `IsReduced`,
which fails at non-reduced chart points, so this is a fragment, not the
consumer discharge.)

## References

* This module, `Appendix_FixedPoint.BezoutChain.maxSpecFintype`,
  `Appendix_FixedPoint.BezoutChain.equivPi_linearEquiv`,
  `Appendix_FixedPoint.BezoutChain.moduleFinite_quotient_of_finite`.
* `Mathlib/LinearAlgebra/Dimension/Constructions.lean`,
  `Module.finrank_pi_fintype`.
* `Mathlib/LinearAlgebra/Basis/VectorSpace.lean`,
  `Module.Free.of_divisionRing`.
* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`,
  `LinearEquiv.finrank_eq`. -/
theorem finrank_eq_sum_quotients_of_reduced (K R : Type*) [Field K] [CommRing R]
    [Algebra K R] [IsArtinianRing R] [IsReduced R] [Module.Finite K R]
    [Fintype (MaximalSpectrum R)] :
    Module.finrank K R
      = ∑ m : MaximalSpectrum R, Module.finrank K (R ⧸ m.asIdeal) := by
  have hfin : ∀ m : MaximalSpectrum R, Module.Finite K (R ⧸ m.asIdeal) :=
    fun m => moduleFinite_quotient_of_finite K R m.asIdeal
  have hfree : ∀ m : MaximalSpectrum R, Module.Free K (R ⧸ m.asIdeal) :=
    fun m => Module.Free.of_divisionRing K _
  have hpi := Module.finrank_pi_fintype (R := K)
    (M := fun m : MaximalSpectrum R => R ⧸ m.asIdeal)
  rw [← hpi]
  exact LinearEquiv.finrank_eq (equivPi_linearEquiv K R)

/-! ## §4 Nilradical-power CRT decomposition -/

/-- Once a nilradical power is `⊥`, the chart-level CRT decomposition is a
product decomposition of `R` itself (quotient factors, not localizations).

## References

* `Mathlib/RingTheory/Artinian/Module.lean`,
  `IsArtinianRing.quotNilradicalPowEquivPi`
  (`(n : ℕ) : R ⧸ nilradical R ^ n ≃ₐ[R] ∀ I, R ⧸ I.asIdeal ^ n`).
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `AlgEquiv.quotientBot`, `Ideal.quotientEquivAlgOfEq`. -/
noncomputable def equivPi_pow_of_nilpow (R : Type*) [CommRing R]
    [IsArtinianRing R] (n : ℕ) (h : nilradical R ^ n = ⊥) :
    R ≃ₐ[R] ∀ m : MaximalSpectrum R, R ⧸ m.asIdeal ^ n :=
  (AlgEquiv.quotientBot R R).symm.trans
    ((Ideal.quotientEquivAlgOfEq R h.symm).trans
      (IsArtinianRing.quotNilradicalPowEquivPi R n))

/-- The nilradical of an Artinian ring is nilpotent, so some power gives the
§4 product decomposition unconditionally.

## References

* `Mathlib/RingTheory/Artinian/Ring.lean`,
  `IsArtinianRing.isNilpotent_nilradical`.
* This module, `Appendix_FixedPoint.BezoutChain.equivPi_pow_of_nilpow`. -/
theorem exists_pow_equivPi_quotient_pow (R : Type*) [CommRing R]
    [IsArtinianRing R] :
    ∃ n : ℕ, Nonempty (R ≃ₐ[R] ∀ m : MaximalSpectrum R, R ⧸ m.asIdeal ^ n) := by
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_nilradical (R := R)
  refine ⟨n, ⟨equivPi_pow_of_nilpow R n ?_⟩⟩
  simpa using hn

/-! ## §5 Localizations of a finite chart are finite (`hfinLoc`) -/

/-- A localization of a module-finite `K`-algebra is module-finite over `K`:
the `K`-algebra map is surjective for Artinian `R` (§1), and finiteness
pushes forward along surjections. This follows the exact assembly of
`IsArtinianRing.finrank_eq_sum_primeSpectrum` (same `algHom` +
`localization_surjective` + `of_surjective` chain).

## References

* This module, `Appendix_FixedPoint.BezoutChain.isArtinianRing_of_moduleFinite`.
* `Mathlib/Algebra/Algebra/Hom.lean`, `Algebra.algHom`
  (alias of `IsScalarTower.toAlgHom`).
* `Mathlib/RingTheory/Artinian/Ring.lean`,
  `IsArtinianRing.localization_surjective`.
* `Mathlib/RingTheory/Finiteness/Basic.lean`,
  `Module.Finite.of_surjective`.
* `Mathlib/RingTheory/Spectrum/Prime/Noetherian.lean`,
  `IsArtinianRing.finrank_eq_sum_primeSpectrum` (assembly pattern). -/
theorem moduleFinite_localization_of_finite (K R : Type*) [Field K]
    [CommRing R] [Algebra K R] [Module.Finite K R]
    (S : Submonoid R) :
    Module.Finite K (Localization S) := by
  have hAR : IsArtinianRing R := IsArtinianRing.of_finite K R
  exact Module.Finite.of_surjective
    (Algebra.algHom K R (Localization S)).toLinearMap
    (IsArtinianRing.localization_surjective S (Localization S))

/-- Every local ring over the locus is finite over `K`, from chart finiteness.
This discharges `ChartLocFinite` (i.e. `haddLocal`'s `[hfinLoc]`) from `hfinA`;
it is stated in `LocalMultiplicity`'s exact `locFam` vocabulary (not the
`ChartFiltration` wrapper name, which would need a heavier import).

## References

* This module, `Appendix_FixedPoint.BezoutChain.moduleFinite_localization_of_finite`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.LocalMultiplicity`,
  `Appendix_FixedPoint.BezoutChain.locLocusFinset`,
  `Appendix_FixedPoint.BezoutChain.locFam`. -/
theorem chartLocFinite_of_chartFinite (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (_hfin : (vanishingLocus n K G).Finite)
    (_hc : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hfinA : Module.Finite K (chartRing n K G ℓ))
    (_p : ↥(locLocusFinset n K G _hfin)) :
    Module.Finite K (locFam n K G ℓ _hfin _hc _p) := by
  have hfinA' := hfinA
  exact moduleFinite_localization_of_finite K (chartRing n K G ℓ) _

/-! ## §6 The abstract structure core and the exact `ChartDecomp` shape -/

/-- The abstract Artinian structure core as a `K`-linear equiv (proved): an
Artinian `K`-algebra is the product of its localizations at maximal ideals.
The `R`-algebra form is `MaximalSpectrum.toPiLocalizationEquiv` (via the
discrete-spectrum route; the `DiscreteTopology` instance for Artinian rings
resolves from `IsArtinianRing R`); `R`-linearity restricts to
`K`-linearity along the tower.

## References

* `Mathlib/RingTheory/Spectrum/Prime/Topology.lean`,
  `MaximalSpectrum.toPiLocalizationEquiv`
  (`R ≃ₐ[R] MaximalSpectrum.PiLocalization R`).
* `Mathlib/RingTheory/Spectrum/Prime/Noetherian.lean`, the
  `DiscreteTopology (PrimeSpectrum R)` instance for Artinian `R`.
* `Mathlib/RingTheory/Spectrum/Maximal/Localization.lean`,
  `MaximalSpectrum.PiLocalization`.
* `Mathlib/Algebra/Algebra/Equiv.lean`, `AlgEquiv.toLinearEquiv`.
* `Mathlib/Algebra/Module/Equiv/Basic.lean`, `LinearEquiv.restrictScalars`. -/
noncomputable def artinianPiLocalizationEquiv (K R : Type*) [Field K]
    [CommRing R] [Algebra K R] [IsArtinianRing R] :
    R ≃ₗ[K] MaximalSpectrum.PiLocalization R :=
  (MaximalSpectrum.toPiLocalizationEquiv R).toLinearEquiv.restrictScalars K

/-- The exact `ChartDecomp` shape (`LocalMultiplicity.haddLocal`'s `hdecomp` binder)
from `hfinA` plus the two-item conditional list: the locus↔`MaxSpec`
bijection `hbij` and the fiber identification `hloc`. The proof chains the
§6 structure equiv with fiberwise congruence (`piCongrRight`) and
reindexing (`piCongrLeft`).

Narrowness: `hbij` is the geometric bijection through the section
presentation (`ChartFiltration`'s `hlift` family); `hloc` is the per-point
localization identification (from `hbij` plus `pointIdeal` coherence). The
algebraic crux is discharged in-file (`artinianPiLocalizationEquiv` from
`hfinA` via §1); `hfinLoc` is discharged by §5.

## References

* This module, `Appendix_FixedPoint.BezoutChain.artinianPiLocalizationEquiv`,
  `Appendix_FixedPoint.BezoutChain.isArtinianRing_of_moduleFinite`.
* `Mathlib/LinearAlgebra/Pi.lean`, `LinearEquiv.piCongrLeft`,
  `LinearEquiv.piCongrRight`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.LocalMultiplicity`,
  `Appendix_FixedPoint.BezoutChain.locLocusFinset`,
  `Appendix_FixedPoint.BezoutChain.locFam` (the exact `haddLocal` binder vocabulary). -/
noncomputable def chartDecomp_of (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hfin : (vanishingLocus n K G).Finite)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hfinA : Module.Finite K (chartRing n K G ℓ))
    (hbij : MaximalSpectrum (chartRing n K G ℓ) ≃ ↥(locLocusFinset n K G hfin))
    (hloc : ∀ m : MaximalSpectrum (chartRing n K G ℓ),
      Localization.AtPrime m.asIdeal ≃ₗ[K] locFam n K G ℓ hfin hc (hbij m)) :
    chartRing n K G ℓ ≃ₗ[K]
      ((p : ↥(locLocusFinset n K G hfin)) → locFam n K G ℓ hfin hc p) := by
  have hAR : IsArtinianRing (chartRing n K G ℓ) :=
    isArtinianRing_of_moduleFinite K (chartRing n K G ℓ)
  have hfinA' := hfinA
  have hstruct : chartRing n K G ℓ ≃ₗ[K]
      MaximalSpectrum.PiLocalization (chartRing n K G ℓ) :=
    artinianPiLocalizationEquiv K (chartRing n K G ℓ)
  exact hstruct.trans ((LinearEquiv.piCongrRight hloc).trans
    (LinearEquiv.piCongrLeft K (fun p => locFam n K G ℓ hfin hc p) hbij))

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
