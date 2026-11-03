/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Bézout backbone: scheme data and numerical invariants (definitions only)

This module defines the four basic notions used by the Bézout statement:
`IsZeroDimensional`, `totalDegree`, `pointMultiplicity`, `IsSmoothPoint`,
plus the underlying rings
(`coneQuotient`, `sectionQuotient`, `chartRing`) and the linear-form
constructor (`mkLin`) Elimination needs. The Bézout theorems in
`Statement/Statement.lean` are closed conditionally on explicitly threaded
numerical and counting inputs — see that module's docstrings.

## Explicit section data (circularity resolution)

`totalDegree` needs a regular linear form `ℓ`, whose existence (R1) is proved
by a parallel development (`Regularity/Avoid/ResultantLemmas.lean`). We do not
assume R1 here: `ℓ` is an explicit argument (`totalDegree n K G ℓ`), and
likewise for `sectionQuotient`, `chartRing`, and the multiplicities. That the
value is `2 ^ (n + 1)` for every regular `ℓ` (hence `ℓ`-independent) is
`length_section_eq_two_pow` (`Geometry/HilbertFunctionCount.lean`, applied
directly by `bezout_quadratic`); that the chart choices for the multiplicity
agree on overlaps is Lemma C2 (`mult_chart_independent`, `Geometry/Counting.lean`).

## Canonical multiplicity vs backward-compat alias

The canonical point multiplicity is `localPointMultiplicity` below (local
`K`-length at `p.rep`, `0` off the locus; moved down from
`Geometry/LocalMultiplicity.lean` so the leaf module hosts it). The preliminary
global-length `pointMultiplicity` is retained byte-identical as a
backward-compat alias: every former call site (`Counting.lean`,
`Statement/Statement.lean`'s `hmult`, `BridgeToFixedPoint/MkSystemSmoothness.lean`) has migrated
to the canonical local form, so the alias currently has no code users — it is
kept only for interface stability.

## References

Mathlib v4.34.0 has no degree-of-variety or intersection-multiplicity API, so
the notions below are assembled from general-purpose commutative-algebra and
linear-algebra API. Each definition's docstring carries a `## References`
subsection citing the exact module path and declaration name used.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
open scoped BigOperators

/-! ## Affine cone quotient and linear forms -/

/-- The homogeneous coordinate ring (affine cone quotient) of the system `G`:
polynomials in the `n + 2` variables `(x₀, …, xₙ, z)` modulo the ideal cut out
by the `n + 1` equations `G₀, …, Gₙ`. An `abbrev` (reducible) so that the
quotient `CommRing` / `Algebra K` instances flow through to the section and
chart constructions below.

## References

* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial` (with
  `MvPolynomial.C`, `MvPolynomial.X` for the generators).
* `Mathlib/RingTheory/Ideal/Span.lean`, `Ideal.span` (the ideal cut out by
  `Set.range G`).
* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.Quotient.mk`
  (quotient ring structure on `MvPolynomial (Fin (n+2)) K ⧸ _`). -/
abbrev coneQuotient (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K) :=
  MvPolynomial (Fin (n + 2)) K ⧸ Ideal.span (Set.range G)

/-- The linear form with coefficients `ℓ`: `∑ j, ℓ j * X j`. The Elimination
strand sections the cone by `mkLin ℓ` (regular by R1) and localizes away from it
for the chart ring.

## References

* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.C`,
  `MvPolynomial.X`.
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`, `Finset.sum`
  (the `∑ j, …` notation over `Fin (n + 2)`). -/
noncomputable def mkLin (n : ℕ) (K : Type*) [Field K] (ℓ : Fin (n + 2) → K) :
    MvPolynomial (Fin (n + 2)) K :=
  ∑ j, MvPolynomial.C (ℓ j) * MvPolynomial.X j

/-- `K`-linear combinations with coefficient vector `c`: `∑ j, c j • q j`,
as a `K`-linear map in the coefficients.

## References

* `Mathlib/Algebra/Module/LinearMap/End.lean`, `LinearMap.smulRight`
  (scalar-weighted coordinate projections `LinearMap.proj`).
* `Mathlib/LinearAlgebra/Pi.lean`, `LinearMap.proj`. -/
noncomputable def comboLin (K : Type*) [CommSemiring K] {ι : Type*} [Fintype ι]
    {Q : Type*} [AddCommGroup Q] [Module K Q] (q : ι → Q) : (ι → K) →ₗ[K] Q :=
  ∑ j, (LinearMap.proj j).smulRight (q j)

/-- Applying `comboLin` is the explicit sum.

## References

* `Mathlib/Algebra/Module/LinearMap/End.lean`, `LinearMap.sum_apply`,
  `LinearMap.smulRight_apply`; `LinearMap.proj_apply`. -/
theorem comboLin_apply (K : Type*) [CommSemiring K] {ι : Type*} [Fintype ι]
    {Q : Type*} [AddCommGroup Q] [Module K Q] (q : ι → Q) (c : ι → K) :
    comboLin K q c = ∑ j, c j • q j := by
  simp only [comboLin, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply]

/-! ## Section quotient and chart ring -/

/-- The (regular) section `S ⧸ ℓS`: the cone quotient cut further by the image
of the linear form `mkLin ℓ`. Elimination's `section_artinian` shows
this is Artinian (hence of finite `K`-length) under R1-regularity of `ℓ` plus
`IsZeroDimensional`.

Equivalently, this is the polynomial-ring quotient by
`Ideal.span (Set.range G ∪ {mkLin n K ℓ})` (standard; proof sketched here: the
quotient-of-quotient is the quotient by the preimage ideal, and the preimage
of `Ideal.span {mk ℓ}` under the surjective `Ideal.Quotient.mk _` is
`Ideal.span (Set.range G ∪ {mkLin n K ℓ})`).

## References

* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.Quotient.mk`.
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `Ideal.Quotient.algebra` (the `Algebra K` structure on iterated quotients,
  used by `totalDegree` via `Module.finrank`). -/
abbrev sectionQuotient (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) :=
  coneQuotient n K G ⧸ Ideal.span
    ({Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)} :
      Set (coneQuotient n K G))

/-- The affine chart coordinate ring: the degree-0 part `A = (S_ℓ)₀` of the
homogeneous localization of the cone `S = coneQuotient n K G` at the powers of
`ℓ̄` (the image of `mkLin ℓ`). Concretely, the `K`-subalgebra of
`Localization (Submonoid.powers ℓ̄)` of fractions `s / ℓ̄ ^ d` whose numerator
`s` admits a homogeneous degree-`d` lift `p`
(`Ideal.Quotient.mk _ p = s`). This balanced presentation (`deg s = d`
against `ℓ̄ ^ d`) is exactly the classical degree-0 condition, stated via
homogeneous lifts so that no graded-quotient API is needed.

This replaces the former full localization `S_ℓ`: Elimination's
`chart_bridge` deviation note records that the bridge filtration
(`G_d = S_d / ℓ^d` exhausting the chart, `G_d / G_{d-1} ≅ (S / ℓS)_d`) lives in
the degree-0 part, while the full `S_ℓ` is infinite-dimensional over `K` under
`ℓ`-regularity — so the bridge equality is statable (and true) only for this
`A`. The `CommRing` / `Algebra K` instances flow from the ambient localization
through the `Subalgebra` API (see References), hence `Module.finrank K` and
`≃ₗ[K]` statements over `chartRing` (e.g. `pointMultiplicity`,
`chart_bridge`'s `hlin`) elaborate unchanged.

Named follow-ups (proved elsewhere): the filtration API the
Elimination/Counting strands build on — `chart_filtration_exhaust`
(`⋃ d, G_d = A`, since proved in `Geometry/ChartFiltration.lean`) and
`chart_graded_piece`
(`G_d / G_{d-1} ≃ (S / ℓS)_d` using `ℓ`-torsionfreeness from R1-regularity).

## References

* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.IsHomogeneous` (with `isHomogeneous_C`,
  `isHomogeneous_C_mul_X`, `IsHomogeneous.sum/add/mul/pow`; `mkLin ℓ` is
  homogeneous of degree `1` as a sum of `C (ℓ j) * X j` terms).
* `Mathlib/Algebra/Algebra/Subalgebra/Basic.lean`, `Subalgebra` (the ambient
  `K`-subalgebra structure), `Subalgebra.toCommRing`, `Subalgebra.toAlgebra`
  (the `CommRing` / `Algebra K` instances on `↥`, hence the `Module K`
  structure `Module.finrank` needs).
* `Mathlib/GroupTheory/MonoidLocalization/Basic.lean`, `Localization.mk`
  (the quotient-type constructor), `Localization.mk_mul`.
* `Mathlib/RingTheory/Localization/Defs.lean`, `Localization.add_mk`,
  `Localization.mk_algebraMap` (the `K`-scalar case of the subalgebra closure).
* `Mathlib/Algebra/Group/Submonoid/Membership.lean`, `Submonoid.powers`
  (the submonoid `{ℓ̄ ^ d}` localized away from), `Submonoid.mem_powers_iff`.
* `Mathlib/Algebra/Group/Submonoid/Defs.lean`, `Submonoid.mk_mul_mk`
  (denominator bookkeeping `ℓ̄ ^ d₁ * ℓ̄ ^ d₂ = ℓ̄ ^ (d₁ + d₂)`).
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `Ideal.Quotient.mk_algebraMap` (constant lifts land in the degree-0 part).
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.algebraMap_eq`.
* `Mathlib/RingTheory/OreLocalization/Ring.lean`, the
  `Algebra R₀ R[S⁻¹]` instance (with `R₀ := K`: the `Algebra K` structure on
  the ambient localization).
* `Mathlib/RingTheory/Localization/Defs.lean`, `IsLocalization`
  (the interface the Elimination/Counting strands reason through). -/
abbrev chartRing (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) : Type _ :=
  ↥({ carrier := {x : Localization (Submonoid.powers
              (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ) :
                coneQuotient n K G)) |
            ∃ d : ℕ, ∃ s : coneQuotient n K G,
              (∃ p : MvPolynomial (Fin (n + 2)) K, p.IsHomogeneous d ∧
                Ideal.Quotient.mk (Ideal.span (Set.range G)) p = s) ∧
              x = Localization.mk s ⟨(Ideal.Quotient.mk
                (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d,
                (Submonoid.mem_powers_iff _ _).mpr ⟨d, rfl⟩⟩},
        mul_mem' := by
          intro x y hx hy
          obtain ⟨d₁, s₁, ⟨p₁, hp₁hom, hp₁eq⟩, e₁⟩ := hx
          obtain ⟨d₂, s₂, ⟨p₂, hp₂hom, hp₂eq⟩, e₂⟩ := hy
          have hpow : (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d₁ *
              (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d₂ =
              (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ (d₁ + d₂) :=
            (pow_add _ _ _).symm
          rw [e₁, e₂]
          refine ⟨d₁ + d₂, (Ideal.Quotient.mk (Ideal.span (Set.range G)) p₁) *
              (Ideal.Quotient.mk (Ideal.span (Set.range G)) p₂),
              ⟨p₁ * p₂, hp₁hom.mul hp₂hom, by rw [map_mul]⟩, ?_⟩
          rw [Localization.mk_mul, ← hp₁eq, ← hp₂eq]
          have h1mem : (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d₁ ∈
              Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) :=
            (Submonoid.mem_powers_iff _ _).mpr ⟨d₁, rfl⟩
          have h2mem : (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d₂ ∈
              Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) :=
            (Submonoid.mem_powers_iff _ _).mpr ⟨d₂, rfl⟩
          have hprod : (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d₁ *
              (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d₂ ∈
              Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) :=
            mul_mem h1mem h2mem
          have hnew :
              (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ (d₁ + d₂) ∈
              Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) :=
            (Submonoid.mem_powers_iff _ _).mpr ⟨d₁ + d₂, rfl⟩
          have hden : ((⟨(Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d₁ *
              (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d₂, hprod⟩ :
              Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
              = ⟨(Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ (d₁ + d₂),
                hnew⟩) :=
            Subtype.ext hpow
          change Localization.mk ((Ideal.Quotient.mk (Ideal.span (Set.range G)) p₁) *
              (Ideal.Quotient.mk (Ideal.span (Set.range G)) p₂))
              ⟨(Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d₁ *
                (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d₂, hprod⟩
            = Localization.mk ((Ideal.Quotient.mk (Ideal.span (Set.range G)) p₁) *
              (Ideal.Quotient.mk (Ideal.span (Set.range G)) p₂))
              ⟨(Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ (d₁ + d₂),
                hnew⟩
          rw [hden],
        add_mem' := by
          intro x y hx hy
          obtain ⟨d₁, s₁, ⟨p₁, hp₁hom, hp₁eq⟩, e₁⟩ := hx
          obtain ⟨d₂, s₂, ⟨p₂, hp₂hom, hp₂eq⟩, e₂⟩ := hy
          have hlin : (mkLin n K ℓ).IsHomogeneous 1 := by
            unfold mkLin
            exact MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ =>
              MvPolynomial.isHomogeneous_C_mul_X _ _
          have e1 : 1 * d₁ + d₂ = d₁ + d₂ := by omega
          have e2 : 1 * d₂ + d₁ = d₁ + d₂ := by omega
          have h1 : ((mkLin n K ℓ) ^ d₁ * p₂).IsHomogeneous (d₁ + d₂) := by
            rw [← e1]
            exact (hlin.pow d₁).mul hp₂hom
          have h2 : ((mkLin n K ℓ) ^ d₂ * p₁).IsHomogeneous (d₁ + d₂) := by
            rw [← e2]
            exact (hlin.pow d₂).mul hp₁hom
          have hnum : Ideal.Quotient.mk (Ideal.span (Set.range G))
                ((mkLin n K ℓ) ^ d₁ * p₂ + (mkLin n K ℓ) ^ d₂ * p₁)
              = (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d₁ * s₂ +
                (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d₂ * s₁ := by
            rw [map_add, map_mul, map_mul, map_pow, map_pow, hp₁eq, hp₂eq]
          have hpow : (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d₁ *
              (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d₂ =
              (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ (d₁ + d₂) :=
            (pow_add _ _ _).symm
          rw [e₁, e₂, Localization.add_mk]
          refine ⟨d₁ + d₂,
              (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d₁ * s₂ +
              (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d₂ * s₁,
              ⟨(mkLin n K ℓ) ^ d₁ * p₂ + (mkLin n K ℓ) ^ d₂ * p₁, h1.add h2,
                hnum⟩, ?_⟩
          have h1mem : (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d₁ ∈
              Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) :=
            (Submonoid.mem_powers_iff _ _).mpr ⟨d₁, rfl⟩
          have h2mem : (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d₂ ∈
              Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) :=
            (Submonoid.mem_powers_iff _ _).mpr ⟨d₂, rfl⟩
          have hprod : (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d₁ *
              (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d₂ ∈
              Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) :=
            mul_mem h1mem h2mem
          have hnew :
              (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ (d₁ + d₂) ∈
              Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) :=
            (Submonoid.mem_powers_iff _ _).mpr ⟨d₁ + d₂, rfl⟩
          have hden : ((⟨(Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d₁ *
              (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d₂, hprod⟩ :
              Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)))
              = ⟨(Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ (d₁ + d₂),
                hnew⟩) :=
            Subtype.ext hpow
          change Localization.mk
              ((Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d₁ * s₂ +
              (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d₂ * s₁)
              ⟨(Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d₁ *
                (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d₂, hprod⟩
            = Localization.mk
              ((Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d₁ * s₂ +
              (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ d₂ * s₁)
              ⟨(Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ (d₁ + d₂),
                hnew⟩
          rw [hden],
        algebraMap_mem' := by
          intro r
          have hC : (MvPolynomial.C r : MvPolynomial (Fin (n + 2)) K)
              = algebraMap K (MvPolynomial (Fin (n + 2)) K) r := by
            rw [MvPolynomial.algebraMap_eq]
          have hmap : Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C r)
              = algebraMap K (coneQuotient n K G) r := by
            rw [hC]
            exact Ideal.Quotient.mk_algebraMap K _ _
          refine ⟨0, algebraMap K (coneQuotient n K G) r,
            ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C _ r, hmap⟩, ?_⟩
          exact (Localization.mk_algebraMap r).symm } : Subalgebra K (Localization (Submonoid.powers
            (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ) :
              coneQuotient n K G))))

/-! ## Zero-dimensionality and total degree -/

/-- `Z` is zero-dimensional: the affine cone quotient has Krull dimension
`≤ 1` (i.e. the projective locus is a finite set of closed points over the
algebraically closed field `K`).

Spec note: the spec writes this as
`Ring.krullDimLE (coneQuotient …) 1`; the in-tree declaration name and
argument order is `Ring.KrullDimLE 1 R`, used here.

## References

* `Mathlib/RingTheory/KrullDimension/Basic.lean`, `Ring.KrullDimLE`
  (`abbrev Ring.KrullDimLE (n : ℕ) (R : Type*) [CommSemiring R] : Prop`). -/
def IsZeroDimensional (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K) : Prop :=
  Ring.KrullDimLE 1 (coneQuotient n K G)

/-- The total degree of the zero-dimensional locus counted with multiplicity:
the `K`-length (`Module.finrank K`) of the regular section
`sectionQuotient n K G ℓ`.

The linear form `ℓ` is explicit (see the module docstring): R1-regularity is
not assumed. The value `2 ^ (n + 1)` (hence `ℓ`-independence) is
`length_section_eq_two_pow` (`Geometry/HilbertFunctionCount.lean`), applied directly by
`bezout_quadratic`; chart-agreement of the multiplicities is Lemma C2
(`mult_chart_independent`, `Geometry/Counting.lean`).

## References

* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`, `Module.finrank`
  (`noncomputable def finrank (R M: Type*) [Semiring R] [AddCommMonoid M]
  [Module R M]: ℕ`; `0` by convention when infinite). -/
noncomputable def totalDegree (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) : ℕ :=
  Module.finrank K (sectionQuotient n K G ℓ)

/-! ## Point multiplicity -/

/-- Backward-compat alias for the intersection multiplicity at `p`: the
`K`-length (`Module.finrank K`) of the degree-0 chart ring `A = (S_ℓ)₀`
(see `chartRing`) for the section data `ℓ`. The point argument is ignored
in this preliminary form (it is the global chart length, not a local one).

Preliminary global-length form, retained byte-identical (name, signature,
body) for interface stability: it currently has no code users — every call
site has migrated to the canonical `localPointMultiplicity` below (local
`K`-length at `p.rep`, `0` off the locus), which deliberately does not reuse
this name. New code must use `localPointMultiplicity`.

## References

* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`, `Module.finrank`. -/
noncomputable def pointMultiplicity (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (_p : Projectivization K (Fin (n + 2) → K)) : ℕ :=
  Module.finrank K (chartRing n K G ℓ)

/-! ## Projective locus scaffolding (moved down from `Statement`) -/

/-- The projective locus cut out by `G₀, …, Gₙ`: the set of points of
`ℙ K (Fin (n+2) → K)` on which every `Gᵢ` vanishes.

Defined by quantifying over *all* nonzero representatives above each
projective point, so no well-definedness (scale-invariance) proof is needed
here: for homogeneous `Gᵢ` this agrees with vanishing on any single
representative. Uses `MvPolynomial.eval` for evaluation at a representative. -/
def vanishingLocus (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K) :
    Set (Projectivization K (Fin (n + 2) → K)) :=
  { p | ∀ (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → ∀ i, MvPolynomial.eval v (G i) = 0 }

/-- The representative `(0, …, 0, 1)` of the distinguished point
`[0 : ⋯ : 0 : 1]`: `1` in the last (`z`) coordinate, `0` elsewhere. -/
def zRep (n : ℕ) (K : Type*) [Field K] : Fin (n + 2) → K :=
  Pi.single (Fin.last (n + 1)) 1

/-- The representative `zRep` is nonzero (its last coordinate is `1`). -/
theorem zRep_ne_zero (n : ℕ) (K : Type*) [Field K] : zRep n K ≠ 0 := by
  intro h
  have hcongr := congrFun h (Fin.last (n + 1))
  simp only [zRep, Pi.single_eq_same, Pi.zero_apply] at hcongr
  exact one_ne_zero hcongr

/-- The distinguished point `[0 : ⋯ : 0 : 1]` of `ℙⁿ⁺¹`: the class of `zRep`.
In our instance (`mkSystem`) this is the point at which the fixed-point
argument already knows a smooth (`multiplicity 1`) point of the locus sits. -/
def distinguishedPoint (n : ℕ) (K : Type*) [Field K] :
    Projectivization K (Fin (n + 2) → K) :=
  Projectivization.mk K (zRep n K) (zRep_ne_zero n K)

/-- Our instance: from quadratic forms `Fᵢ` in the `n + 1` variables `x`
build the system `Gᵢ = Fᵢ(x) − z·xᵢ` in the `n + 2` variables `(x, z)`.
Here `Fin.castSucc i` is the `xᵢ` variable and `Fin.last (n + 1)` is the `z`
variable; `Fᵢ` is transported along `Fin.castSucc`. -/
noncomputable def mkSystem (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) :
    Fin (n + 1) → MvPolynomial (Fin (n + 2)) K :=
  fun i => (MvPolynomial.rename Fin.castSucc) (F i)
    - MvPolynomial.X (Fin.last (n + 1)) * MvPolynomial.X (Fin.castSucc i)

/-! ## Smoothness (Jacobian criterion) -/

/-- `Z` is smooth at `p` in the Jacobian sense: there *exists* one nonzero
representative `v` of `p` at which the `(n + 1) × (n + 2)` Jacobian matrix
`(∂Gᵢ/∂xⱼ|ᵥ)` has full row rank `n + 1` — i.e. the gradients cut out the
expected tangent space. Note the two deliberate weakenings vs the classical
notion: no vanishing hypothesis (`v` need not annihilate the `Gᵢ`), and a
single existential representative (not all representatives above `p`);
smoothness here is purely the rank condition at one representative.

## References

* `Mathlib/LinearAlgebra/Projectivization/Basic.lean`, `Projectivization.mk`.
* `Mathlib/Algebra/MvPolynomial/PDeriv.lean`, `MvPolynomial.pderiv`
  (`def pderiv (i : σ) : Derivation R (MvPolynomial σ R) …`).
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval`
  (`def eval (f : σ → R) : MvPolynomial σ R →+* R`).
* `Mathlib/LinearAlgebra/Matrix/Defs.lean`, `Matrix.of`
  (function-to-matrix equivalence `(m → n → α) ≃ Matrix m n α`).
* `Mathlib/LinearAlgebra/Matrix/Rank.lean`, `Matrix.rank`
  (`noncomputable def rank [CommSemiring R] (A : Matrix m n R) : ℕ`). -/
noncomputable def IsSmoothPoint (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (p : Projectivization K (Fin (n + 2) → K)) : Prop :=
  ∃ (v : Fin (n + 2) → K) (hv : v ≠ 0),
    Projectivization.mk K v hv = p ∧
      Matrix.rank (Matrix.of (fun (i : Fin (n + 1)) (j : Fin (n + 2)) =>
        MvPolynomial.eval v (MvPolynomial.pderiv j (G i)))) = n + 1

/-! ## Evaluation of the chart at a point

The canonical local-multiplicity chain (`coneEval` through
`localPointMultiplicity`) was moved down from `Geometry/LocalMultiplicity.lean` so
the leaf module hosts it; `LocalMultiplicity` imports these definitions. -/

/-- Evaluation of the cone quotient at `v`, for a representative annihilating
every equation (same `Ideal.Quotient.lift` pattern as
`ChartFiltration.evalAtZero`, with `hvG` in place of `hG0`).

## References

* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.Quotient.lift`.
* `Mathlib/RingTheory/Ideal/Span.lean`, `Ideal.span_le`.
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval`. -/
noncomputable def coneEval (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0) :
    coneQuotient n K G →+* K :=
  Ideal.Quotient.lift _ (MvPolynomial.eval v) (fun a ha => by
    have hsub : Ideal.span (Set.range G)
        ≤ RingHom.ker (MvPolynomial.eval v : MvPolynomial _ _ →+* K) := by
      rw [Ideal.span_le]
      intro x hx
      obtain ⟨i, rfl⟩ := hx
      exact RingHom.mem_ker.mpr (hvG i)
    exact RingHom.mem_ker.mp (hsub ha))

/-- `coneEval` reads off the constant coefficient (same `lift_mk`-unfolding as
`ChartFiltration.evalAtZero_mk_C`).

## References

* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.Quotient.lift_mk`
  (used via definitional unfolding in `change`).
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_C`. -/
theorem coneEval_C (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0) (c : K) :
    coneEval n K G v hvG
        (Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c)) = c := by
  change MvPolynomial.eval v (MvPolynomial.C c) = c
  rw [MvPolynomial.eval_C]

/-- Evaluation of the ambient localization at `v`: since `ℓ(v) ≠ 0`, every
`ℓ̄`-power maps to a unit, so `coneEval` extends over the denominators by
`IsLocalization.lift`.

## References

* `Mathlib/RingTheory/Localization/Defs.lean`, `IsLocalization.lift`
  (`noncomputable def lift {g: R →+* P} (hg: ∀ y: M, IsUnit (g y)):
  S →+* P`).
* `Mathlib/RingTheory/Localization/Basic.lean`, `Localization.isLocalization`
  (the `IsLocalization M (Localization M)` instance, resolved by TC).
* `Mathlib/Algebra/Group/Submonoid/Membership.lean`,
  `Submonoid.mem_powers_iff`. -/
noncomputable def chartLocEval (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0) :
    Localization (Submonoid.powers
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ) :
        coneQuotient n K G)) →+* K :=
  IsLocalization.lift (M := Submonoid.powers
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ) :
        coneQuotient n K G))
    (S := Localization (Submonoid.powers
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ) :
        coneQuotient n K G)))
    (g := coneEval n K G v hvG)
    (fun y => by
      obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp y.2
      have he : coneEval n K G v hvG
          (Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ))
          = MvPolynomial.eval v (mkLin n K ℓ) := rfl
      rw [isUnit_iff_ne_zero]
      have hval : coneEval n K G v hvG (↑y)
          = (MvPolynomial.eval v (mkLin n K ℓ)) ^ k := by
        conv_lhs => rw [← hk]
        rw [map_pow, he]
      rw [hval]
      exact pow_ne_zero k hℓ)

/-- Evaluation of the chart ring `A = (S_ℓ)₀` at `v` (restriction of
`chartLocEval` along the subalgebra inclusion).

## References

* `Mathlib/Algebra/Algebra/Subalgebra/Basic.lean`, `Subalgebra.val`
  (`(S : Subalgebra R A) : S →ₐ[R] A`), `AlgHom.toRingHom`. -/
noncomputable def chartEval (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0) :
    chartRing n K G ℓ →+* K :=
  (chartLocEval n K G ℓ v hvG hℓ).comp (Subalgebra.val _).toRingHom

/-- Eval-surjectivity (the residue-field-`K` argument): constants land in the
chart (degree-`0` lift over `ℓ̄ ^ 0`), and `IsLocalization.lift` computes on
them via `lift_mk'_spec` to the constant value.

## References

* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.isHomogeneous_C`.
* `Mathlib/RingTheory/Localization/Defs.lean`,
  `Localization.mk_eq_mk'_apply`
  (`mk x y = IsLocalization.mk' (Localization M) x y`),
  `IsLocalization.lift_mk'_spec`
  (`lift hg (mk' S x y) = v ↔ g x = g y * v`).
* `Mathlib/Algebra/Group/Submonoid/Membership.lean`,
  `Submonoid.mem_powers_iff`. -/
theorem chartEval_surjective (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0) :
    Function.Surjective (chartEval n K G ℓ v hvG hℓ) := by
  intro c
  refine ⟨⟨Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c))
    ⟨(Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ 0,
      (Submonoid.mem_powers_iff _ _).mpr ⟨0, rfl⟩⟩,
    0, Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c),
    ⟨MvPolynomial.C c, MvPolynomial.isHomogeneous_C _ c, rfl⟩, rfl⟩, ?_⟩
  change (chartLocEval n K G ℓ v hvG hℓ)
    (Localization.mk (Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c))
      ⟨(Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ 0, _⟩) = c
  unfold chartLocEval
  rw [Localization.mk_eq_mk'_apply, IsLocalization.lift_mk'_spec]
  have e1 : coneEval n K G v hvG
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c)) = c :=
    coneEval_C n K G v hvG c
  have e2 : coneEval n K G v hvG
      ((Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ 0) = 1 := by
    rw [pow_zero]
    exact map_one _
  change coneEval n K G v hvG
      (Ideal.Quotient.mk (Ideal.span (Set.range G)) (MvPolynomial.C c))
    = coneEval n K G v hvG
      ((Ideal.Quotient.mk (Ideal.span (Set.range G)) (mkLin n K ℓ)) ^ 0) * c
  rw [e1, e2, one_mul]

/-! ## The maximal ideal of a point -/

/-- The maximal-ideal data for `p`: the kernel of chart evaluation at the
representative `v`. -/
noncomputable def pointIdeal (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0) :
    Ideal (chartRing n K G ℓ) :=
  RingHom.ker (chartEval n K G ℓ v hvG hℓ)

/-- The evaluation kernel is maximal (surjective map onto the field `K`).

## References

* `Mathlib/RingTheory/Ideal/Maps.lean`,
  `RingHom.ker_isMaximal_of_surjective`
  (`(f : F) (hf : Function.Surjective f) : (ker f).IsMaximal`, for
  `[Ring R] [DivisionRing K]`). -/
theorem pointIdeal_isMaximal (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0) :
    (pointIdeal n K G ℓ v hvG hℓ).IsMaximal := by
  unfold pointIdeal
  exact RingHom.ker_isMaximal_of_surjective _
    (chartEval_surjective n K G ℓ v hvG hℓ)

/-- Maximality as an instance, so `Ideal.primeCompl` (which needs
`[I.IsPrime]`, via `IsMaximal.isPrime'`) applies to `pointIdeal`.

## References

* `Mathlib/RingTheory/Ideal/Maximal.lean`, `IsMaximal.isPrime'`
  (`instance (priority := 100) … : ∀ [_H : I.IsMaximal], I.IsPrime`). -/
noncomputable instance pointIdeal_isMaximal_inst (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0) :
    (pointIdeal n K G ℓ v hvG hℓ).IsMaximal :=
  pointIdeal_isMaximal n K G ℓ v hvG hℓ

/-! ## The local ring and the local multiplicity -/

/-- The local ring of the chart at the point: localization away from the
maximal ideal. An `abbrev` (reducible) so the canonical `CommRing` /
`Module K` instances (via the `OreLocalization` API, from the `K`-algebra
structure on the chart) flow through to `finrank` statements.

## References

* `Mathlib/RingTheory/OreLocalization/Ring.lean`,
  `OreLocalization.instModuleOfIsScalarTower`
  (`[Module R₀ X] [Module R₀ R] [IsScalarTower R₀ R X] …:
  Module R₀ X[S⁻¹]`, with `R₀:= K`, `R:= X:= chartRing`). -/
noncomputable abbrev locRingAt (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0) : Type _ :=
  Localization (pointIdeal n K G ℓ v hvG hℓ).primeCompl

/-- The local multiplicity at the representative: the `K`-length
(`Module.finrank K`) of the localized chart.

## References

* `Mathlib/LinearAlgebra/Dimension/Finrank.lean`, `Module.finrank`. -/
noncomputable def localMultiplicity (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K) (v : Fin (n + 2) → K)
    (hvG : ∀ i, MvPolynomial.eval v (G i) = 0)
    (hℓ : MvPolynomial.eval v (mkLin n K ℓ) ≠ 0) : ℕ :=
  Module.finrank K (locRingAt n K G ℓ v hvG hℓ)

open Classical in
/-- The canonical point multiplicity (replacement for the preliminary
global-length `pointMultiplicity` above, which is retained as a
backward-compat alias): the local length at the canonical representative
`p.rep`, or `0` off the locus. The chart-nonvanishing input `hc` is the R1
nonvanishing conclusion (same shape as `Counting`'s `hc₁` in
`mult_chart_independent`); locus equations at `p.rep` come straight from
locus membership, so no extra hypothesis is needed for them.

## References

* `Mathlib/LinearAlgebra/Projectivization/Basic.lean`,
  `Projectivization.rep`, `Projectivization.rep_nonzero`,
  `Projectivization.mk_rep`. -/
noncomputable def localPointMultiplicity (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (ℓ : Fin (n + 2) → K)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K)) (_ : p ∈ vanishingLocus n K G)
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (p : Projectivization K (Fin (n + 2) → K)) : ℕ :=
  if h : p ∈ vanishingLocus n K G then
    localMultiplicity n K G ℓ p.rep
      (fun i => h p.rep p.rep_nonzero (Projectivization.mk_rep p) i)
      (hc p h p.rep p.rep_nonzero (Projectivization.mk_rep p))
  else 0

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
