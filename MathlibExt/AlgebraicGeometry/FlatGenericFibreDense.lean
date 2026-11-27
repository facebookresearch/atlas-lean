/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# The generic fibre of a flat scheme over a domain is dense

Let `R` be a domain with fraction field `K` and let `f : X ⟶ Spec R` be flat. The generic fibre
`X_K = X ×_{Spec R} Spec K`, with its projection `X_K ⟶ X`, is scheme-theoretically dense in `X`:
the projection is scheme-theoretically dominant, so it is injective on sections over every open of
`X`, and it is dominant. Topologically, the fibre of `f` over the generic point of `Spec R` is dense
in `X`. When `R` is a discrete valuation ring, the projection `X_K ⟶ X` is moreover an open
immersion.

The proof: `Spec K ⟶ Spec R` hits the generic point of the integral scheme `Spec R`, so it is
dominant and hence scheme-theoretically dominant (`Spec R` is reduced); scheme-theoretic dominance
of a quasi-compact morphism is preserved by flat base change
(`AlgebraicGeometry.IsSchemeTheoreticallyDominant.pullbackFst`, Stacks Lemma 29.26.15, Tag 081H).

## Main results

* `AlgebraicGeometry.range_specMap_algebraMap_fractionRing`: `Spec K ⟶ Spec R` has image the
  generic point.
* `AlgebraicGeometry.isSchemeTheoreticallyDominant_pullback_fst_fractionRing`: `X_K ⟶ X` is
  scheme-theoretically dominant.
* `AlgebraicGeometry.isDominant_pullback_fst_fractionRing`: `X_K ⟶ X` is dominant.
* `AlgebraicGeometry.injective_app_pullback_fst_fractionRing`: restriction of sections from any
  open `U` of `X` to its preimage in `X_K` is injective.
* `AlgebraicGeometry.dense_preimage_genericPoint_of_flat`: the fibre of `f` over the generic point
  of `Spec R` is dense in `X`.
* `IsDiscreteValuationRing.isLocalization_away_of_irreducible`: the fraction field of a discrete
  valuation ring is its localization away from a uniformizer.
* `AlgebraicGeometry.isOpenImmersion_and_isSchemeTheoreticallyDominant_pullback_fst`: for `R` a
  discrete valuation ring, `X_K ⟶ X` is a scheme-theoretically dominant, dominant open immersion.

## References

* B. Conrad, *Minimal models for elliptic curves*, notes (version of 21 November 2015),
  Example 2.5, p. 2.
* The Stacks project, Lemma 31.14.4 (Tag 07ZU) and Lemma 29.26.15 (Tag 081H).
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Topology

universe u

/-- The fraction field `K` of a discrete valuation ring `R` is the localization of `R` away from
any uniformizer `ϖ`: every nonzero element of `R` is a unit times a power of `ϖ`. -/
theorem IsDiscreteValuationRing.isLocalization_away_of_irreducible {R : Type*} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) : IsLocalization.Away ϖ K := by
  refine IsLocalization.Away.mk ϖ ?_ ?_ ?_
  · exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)).isUnit
  · intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) z
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (nonZeroDivisors.ne_zero hb) hϖ
    refine ⟨n, a * ↑u⁻¹, ?_⟩
    have hu : algebraMap R K (u : R) ≠ 0 := (u.isUnit.map _).ne_zero
    have hp : algebraMap R K (ϖ ^ n) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hϖ.ne_zero))
    rw [map_mul, map_mul, ← map_pow]
    have hu' : algebraMap R K (↑u⁻¹ : R) * algebraMap R K (u : R) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    field_simp
    linear_combination (-(algebraMap R K) a) * hu'
  · intro a b hab
    exact ⟨0, by simpa using IsFractionRing.injective R K hab⟩

namespace AlgebraicGeometry

section FractionRing

variable {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- For a domain `R` with fraction field `K`, the morphism `Spec K ⟶ Spec R` sends the point of
`Spec K` to the generic point of `Spec R`. -/
theorem specMap_algebraMap_fractionRing_apply (y : Spec (CommRingCat.of K)) :
    Spec.map (CommRingCat.ofHom (algebraMap R K)) y = genericPoint (Spec (CommRingCat.of R)) := by
  have : IsDomain (CommRingCat.of R) := ‹_›
  rw [genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  have hy : (y : PrimeSpectrum K).asIdeal = ⊥ :=
    @Ideal.eq_bot_of_prime _ _ _ (PrimeSpectrum.isPrime (y : PrimeSpectrum K))
  have e : ((Spec.map (CommRingCat.ofHom (algebraMap R K))) y).asIdeal =
      Ideal.comap (CommRingCat.ofHom (algebraMap R K)).hom y.asIdeal :=
    Submodule.toSubMulAction_inj.mp rfl
  rw [e, hy, CommRingCat.hom_ofHom, PrimeSpectrum.asIdeal_bot]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)

/-- For a domain `R` with fraction field `K`, the image of `Spec K ⟶ Spec R` is the generic
point of `Spec R`. -/
theorem range_specMap_algebraMap_fractionRing :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      {genericPoint (Spec (CommRingCat.of R))} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact specMap_algebraMap_fractionRing_apply K y
  · rintro rfl
    obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
    exact ⟨y, specMap_algebraMap_fractionRing_apply K y⟩

/-- For a domain `R` with fraction field `K`, the morphism `Spec K ⟶ Spec R` is dominant. -/
instance isDominant_specMap_algebraMap_fractionRing :
    IsDominant (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  have : IsDomain (CommRingCat.of R) := ‹_›
  refine ⟨?_⟩
  rw [DenseRange, range_specMap_algebraMap_fractionRing, Dense, ← Set.eq_univ_iff_forall]
  exact genericPoint_spec _

/-- Let `R` be a domain with fraction field `K` and `f : X ⟶ Spec R` a flat morphism. Then the
projection `X ×_{Spec R} Spec K ⟶ X` from the generic fibre is scheme-theoretically dominant: its
kernel ideal sheaf is zero, i.e. its scheme-theoretic image is all of `X`.

This is the main statement of B. Conrad, *Minimal models for elliptic curves*, Example 2.5, p. 2
("`R`-flatness forces the `K`-fibers to be dense"), proved as in Stacks Lemma 31.14.4 (Tag 07ZU)
and Lemma 29.26.15 (Tag 081H); the latter is Mathlib's
`AlgebraicGeometry.IsSchemeTheoreticallyDominant.pullbackFst`. The source states it for `R` a
discrete valuation ring; here `R` is any domain. For a discrete valuation ring the projection is a
quasi-compact open immersion (`isOpenImmersion_and_isSchemeTheoreticallyDominant_pullback_fst`),
for which scheme-theoretic dominance is the scheme-theoretic density of the source. -/
theorem isSchemeTheoreticallyDominant_pullback_fst_fractionRing {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] :
    IsSchemeTheoreticallyDominant
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := by
  have : IsDomain (CommRingCat.of R) := ‹_›
  have := IsSchemeTheoreticallyDominant.of_isDominant
    (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  exact IsSchemeTheoreticallyDominant.pullbackFst _ _

/-- Let `R` be a domain with fraction field `K` and `f : X ⟶ Spec R` a flat morphism. Then the
projection `X ×_{Spec R} Spec K ⟶ X` from the generic fibre is dominant.

B. Conrad, *Minimal models for elliptic curves*, Example 2.5, p. 2 (stated there for `R` a discrete
valuation ring; here `R` is any domain). -/
theorem isDominant_pullback_fst_fractionRing {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] :
    IsDominant (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := by
  have := isSchemeTheoreticallyDominant_pullback_fst_fractionRing K f
  infer_instance

/-- Let `R` be a domain with fraction field `K` and `f : X ⟶ Spec R` a flat morphism. Then for
every open `U` of `X`, the map from sections of `X` over `U` to sections of the generic fibre
`X ×_{Spec R} Spec K` over the preimage of `U` is injective.

This is the concrete content of the scheme-theoretic density in B. Conrad, *Minimal models for
elliptic curves*, Example 2.5, p. 2 (stated there for `R` a discrete valuation ring; here `R` is
any domain). -/
theorem injective_app_pullback_fst_fractionRing {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] (U : X.Opens) :
    Function.Injective
      ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app U) := by
  have := isSchemeTheoreticallyDominant_pullback_fst_fractionRing K f
  exact Scheme.Hom.app_injective _ U

end FractionRing

/-- Let `R` be a domain and `f : X ⟶ Spec R` a flat morphism. Then the fibre of `f` over the
generic point of `Spec R` is dense in `X`.

This is the topological statement of B. Conrad, *Minimal models for elliptic curves*, Example 2.5,
p. 2 (stated there for `R` a discrete valuation ring; here `R` is any domain). -/
theorem dense_preimage_genericPoint_of_flat {R : Type u} [CommRing R] [IsDomain R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] :
    Dense (f ⁻¹' {genericPoint (Spec (CommRingCat.of R))}) := by
  have := isDominant_pullback_fst_fractionRing (FractionRing R) f
  have h := (pullback.fst f
    (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))).denseRange
  rwa [DenseRange, Scheme.Pullback.range_fst, range_specMap_algebraMap_fractionRing] at h

/-- Let `R` be a discrete valuation ring with fraction field `K` and `f : X ⟶ Spec R` a flat
morphism. Then the projection `X ×_{Spec R} Spec K ⟶ X` from the generic fibre is an open
immersion which is scheme-theoretically dominant and dominant: the generic fibre is a
scheme-theoretically dense open subscheme of `X`.

This is B. Conrad, *Minimal models for elliptic curves*, Example 2.5, p. 2, with the proof of
Stacks Lemma 31.14.4 (Tag 07ZU) and Lemma 29.26.15 (Tag 081H). Scheme-theoretic density is
expressed by Mathlib's `IsSchemeTheoreticallyDominant` (zero kernel ideal sheaf); for this
quasi-compact open immersion its sections-level content is
`injective_app_pullback_fst_fractionRing`. -/
theorem isOpenImmersion_and_isSchemeTheoreticallyDominant_pullback_fst {R : Type u} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] :
    IsOpenImmersion (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
      IsSchemeTheoreticallyDominant
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
      IsDominant (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have := IsDiscreteValuationRing.isLocalization_away_of_irreducible K hϖ
  have := IsOpenImmersion.of_isLocalization (S := K) ϖ
  exact ⟨inferInstance, isSchemeTheoreticallyDominant_pullback_fst_fractionRing K f,
    isDominant_pullback_fst_fractionRing K f⟩

end AlgebraicGeometry
