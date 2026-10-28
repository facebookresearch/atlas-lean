/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.PositiveDimTower
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.QuotientKernelAvoidance

/-!
# The graded quotient comparison hom `gr(R) →+* gr(R ⧸ J')` (T2-phi)

The comparison hom `φ` that the K1a/K1c assemblies
(`supT1Data_of_quotAvoid`, `supT1Data_of_quotAvoid_repaired`,
QuotientKernelAvoidance:248/:664) take as explicit data: a graded ring
hom from `gr_𝔪(R)` to `gr(R ⧸ J')` (taken at the quotient adic ideal
`supQuotAdicIdeal J' = 𝔪.map (mk J')`), degree-wise induced by
`Ideal.Quotient.mk J'` on the `grPiece` quotients.

## Construction

* `grQuotComp_map_pow`: `mk J'` sends `𝔪 ^ n` into
  `(supQuotAdicIdeal J') ^ n` (via `Ideal.map_pow`).
* `grQuotComp_rep`: the representative `R`-linear map
  `↥(𝔪 ^ n) →ₗ[R] ↥(K ^ n)` (target an `R`-module via
  `Module.compHom` along `mk J'`).
* `grQuotComp_piece`: the per-degree map on `grPiece` quotients, by
  `Submodule.liftQ` (the kernel side: `mk` sends `𝔪 ^ (n+1)` into
  `K ^ (n+1)`).
* `grQuotComp`: the ring hom, assembled by `DirectSum.toSemiring`
  from per-degree multiplicativity (`grQuotComp_piece_mul`) and the
  unit law (`grQuotComp_piece_one`).

## Interface

* `grQuotComp_compat`: lift-compatibility, verbatim the `hcompat`
  binder shape of the assemblies (QuotAvoid:677-681).
* `grQuotComp_irr`: irrelevant-ideal non-containment pulls back,
  verbatim the `hirr` binder shape (QuotAvoid:682-687), via
  degree-wise surjectivity (`grQuotComp_piece_surjective`, from
  `Ideal.Quotient.mk_surjective` through `Ideal.map_pow`).

## Status

unconditional throughout.

## References

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only:
* `Algebra/DirectSum/Ring.lean`: `DirectSum.toSemiring` /
  `toSemiring_of` / `of_mul_of` (the assembly API).
* `Algebra/DirectSum/Basic.lean`: `DirectSum.of` (bundled
  `AddMonoidHom`), `toAddMonoid`.
* `RingTheory/Ideal/Maps.lean`: `Ideal.map_pow`,
  `Ideal.mem_map_iff_of_surjective`.
* `RingTheory/Ideal/Quotient/Defs.lean`:
  `Ideal.Quotient.mk_surjective`.
* `Algebra/Module/RingHom.lean`: `Module.compHom`.
* `LinearAlgebra/Quotient/Basic.lean`: `Submodule.liftQ`.

Project (read-only):
* `Regularity/Koszul/AssociatedGradedRing.lean` (`grPiece`:110, `associatedGraded`
  :548, the §5 `liftQ` pattern:771+, `grMul` API).
* `Regularity/HomologicalDepth/PositiveDimTower.lean` (`supDegOneLift`:207,
  `SupIrrelevantIdeal`:218).
* `Regularity/HomologicalDepth/QuotientKernelAvoidance.lean` (`supQuotAdicIdeal`:145,
  the `φ`-data binder shapes:248-267/:675-687).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace GradedQuotientComparison

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.PositiveDimTower
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.QuotientKernelAvoidance

variable {R : Type*} [CommRing R] [IsLocalRing R] (J' : Ideal R)

/-! ## §0. `mk` preserves powers into the quotient adic ideal -/

/-- The quotient adic powers are the pushed-forward maximal-ideal
powers: `Ideal.map_pow` unfolded at `supQuotAdicIdeal`.
-/
theorem grQuotComp_map_pow (n : ℕ) :
    Ideal.map (Ideal.Quotient.mk J')
        (IsLocalRing.maximalIdeal R ^ n) =
      (supQuotAdicIdeal J') ^ n := by
  unfold supQuotAdicIdeal
  exact Ideal.map_pow (Ideal.Quotient.mk J')
    (IsLocalRing.maximalIdeal R) n

#print axioms grQuotComp_map_pow

/-- `mk J'` sends `𝔪 ^ n` into `(supQuotAdicIdeal J') ^ n`.
-/
theorem grQuotComp_mem_pow (n : ℕ) (r : R)
    (hr : r ∈ IsLocalRing.maximalIdeal R ^ n) :
    Ideal.Quotient.mk J' r ∈ (supQuotAdicIdeal J') ^ n := by
  rw [← grQuotComp_map_pow]
  exact Ideal.mem_map_of_mem _ hr

#print axioms grQuotComp_mem_pow

/-! ## §1. The per-degree maps -/

/-- The `R`-module structure on quotient representatives, via
`mk J'`. -/
instance instModuleQuotPow (n : ℕ) :
    Module R ↥((supQuotAdicIdeal J') ^ n) :=
  Module.compHom _ (Ideal.Quotient.mk J')

/-- The `R`-module structure on quotient graded pieces, via
`mk J'`. -/
instance instModuleQuotPiece (n : ℕ) :
    Module R (grPiece (R ⧸ J') (supQuotAdicIdeal J') n) :=
  Module.compHom _ (Ideal.Quotient.mk J')

/-- The representative map `↥(𝔪 ^ n) →ₗ[R] ↥(K ^ n)`: `mk J'`
on representatives, `R`-linear for the `compHom` target action.
-/
def grQuotComp_rep (n : ℕ) :
    ↥(IsLocalRing.maximalIdeal R ^ n) →ₗ[R]
      ↥((supQuotAdicIdeal J') ^ n) where
  toFun r := ⟨Ideal.Quotient.mk J' r, grQuotComp_mem_pow J' n r r.2⟩
  map_add' a b := Subtype.ext (map_add _ (a : R) (b : R))
  map_smul' c a := Subtype.ext (map_mul _ c (a : R))

#print axioms grQuotComp_rep

/-- The representative map followed by the quotient projection, as an
`R`-linear map into the quotient piece (stated directly since the
target `mkQ` is `(R ⧸ J')`-linear, so `.comp` does not apply).
-/
def grQuotComp_toQuot (n : ℕ) :
    ↥(IsLocalRing.maximalIdeal R ^ n) →ₗ[R]
      grPiece (R ⧸ J') (supQuotAdicIdeal J') n where
  toFun r := Submodule.Quotient.mk ((grQuotComp_rep J' n) r)
  map_add' a b := by
    rw [map_add (grQuotComp_rep J' n)]
    exact (grPiece_mk_add (R ⧸ J') (supQuotAdicIdeal J') n _ _).symm
  map_smul' c a := by
    rw [map_smul (grQuotComp_rep J' n)]
    rfl

#print axioms grQuotComp_toQuot

/-- Kernel side of the per-degree lift: `mk J'` sends the relations
`𝔪 ^ (n + 1)` into `K ^ (n + 1)`.
-/
theorem grQuotComp_ker (n : ℕ) :
    grSub R (IsLocalRing.maximalIdeal R) n ≤
      LinearMap.ker (grQuotComp_toQuot J' n) := by
  intro a ha
  rw [mem_grSub_iff] at ha
  rw [LinearMap.mem_ker]
  change Submodule.Quotient.mk ((grQuotComp_rep J' n) a) = 0
  rw [Submodule.Quotient.mk_eq_zero, mem_grSub_iff]
  exact grQuotComp_mem_pow J' (n + 1) _ ha

#print axioms grQuotComp_ker

/-- The per-degree map on `grPiece` quotients, by `liftQ`
(the §5 `grPiece_zero_to_quotient_lin` pattern, Graded:771+).
-/
def grQuotComp_piece (n : ℕ) :
    grPiece R (IsLocalRing.maximalIdeal R) n →ₗ[R]
      grPiece (R ⧸ J') (supQuotAdicIdeal J') n :=
  (grSub R (IsLocalRing.maximalIdeal R) n).liftQ
    (grQuotComp_toQuot J' n) (grQuotComp_ker J' n)

#print axioms grQuotComp_piece

/-- Computation rule for the per-degree map. -/
@[simp]
theorem grQuotComp_piece_mk (n : ℕ)
    (r : ↥(IsLocalRing.maximalIdeal R ^ n)) :
    grQuotComp_piece J' n (Submodule.Quotient.mk r) =
      Submodule.Quotient.mk ((grQuotComp_rep J' n) r) :=
  rfl

/-- The per-degree maps are multiplicative (quotient induction on
both sides; both composites are `mk` of the representative
product).
-/
theorem grQuotComp_piece_mul (i j : ℕ)
    (a : grPiece R (IsLocalRing.maximalIdeal R) i)
    (b : grPiece R (IsLocalRing.maximalIdeal R) j) :
    grQuotComp_piece J' (i + j) (GradedMonoid.GMul.mul a b) =
      GradedMonoid.GMul.mul (grQuotComp_piece J' i a)
        (grQuotComp_piece J' j b) := by
  obtain ⟨ra, rfl⟩ :=
    grPiece_mk_surjective R (IsLocalRing.maximalIdeal R) i a
  obtain ⟨rb, rfl⟩ :=
    grPiece_mk_surjective R (IsLocalRing.maximalIdeal R) j b
  rw [grMul_mk_mk, grQuotComp_piece_mk, grQuotComp_piece_mk,
    grQuotComp_piece_mk, grMul_mk_mk]
  -- Both sides are `mk` of the representative product (quotient
  -- operations compute definitionally on `mk`).
  rfl

#print axioms grQuotComp_piece_mul

/-- The per-degree map sends the graded unit to the graded unit
(`mk 1 = 1` on representatives).
-/
theorem grQuotComp_piece_one :
    grQuotComp_piece J' 0 GradedMonoid.GOne.one =
      GradedMonoid.GOne.one := by
  rw [grOne_eq_mk R (IsLocalRing.maximalIdeal R),
    grQuotComp_piece_mk,
    grOne_eq_mk (R ⧸ J') (supQuotAdicIdeal J')]
  -- `mk 1 = 1` holds definitionally on the quotient.
  rfl

#print axioms grQuotComp_piece_one

/-- Degree-wise surjectivity: every quotient class lifts, since
`K ^ n` is the pushed-forward `𝔪 ^ n` (`Ideal.map_pow`) and `mk`
is surjective (`Ideal.Quotient.mk_surjective`).
-/
theorem grQuotComp_piece_surjective (n : ℕ)
    (x : grPiece (R ⧸ J') (supQuotAdicIdeal J') n) :
    ∃ a, grQuotComp_piece J' n a = x := by
  obtain ⟨t, rfl⟩ :=
    grPiece_mk_surjective (R ⧸ J') (supQuotAdicIdeal J') n x
  have hmap : (t : R ⧸ J') ∈ Ideal.map (Ideal.Quotient.mk J')
      (IsLocalRing.maximalIdeal R ^ n) := by
    rw [grQuotComp_map_pow]
    exact t.2
  obtain ⟨r, hr, hrt⟩ := (Ideal.mem_map_iff_of_surjective
    (Ideal.Quotient.mk J') Ideal.Quotient.mk_surjective).mp hmap
  refine ⟨Submodule.Quotient.mk
    (⟨r, hr⟩ : ↥(IsLocalRing.maximalIdeal R ^ n)), ?_⟩
  rw [grQuotComp_piece_mk]
  congr 1
  exact Subtype.ext hrt

#print axioms grQuotComp_piece_surjective

/-! ## §2. The ring hom -/

/-- The per-degree family into the target graded ring. -/
def grQuotComp_fam (n : ℕ) :
    grPiece R (IsLocalRing.maximalIdeal R) n →+
      associatedGraded (R ⧸ J') (supQuotAdicIdeal J') :=
  (DirectSum.of (grPiece (R ⧸ J') (supQuotAdicIdeal J')) n).comp
    (grQuotComp_piece J' n).toAddMonoidHom

/-- The family sends the graded unit to `1`. -/
theorem grQuotComp_fam_one :
    grQuotComp_fam J' _ GradedMonoid.GOne.one = 1 := by
  change (DirectSum.of (grPiece (R ⧸ J') (supQuotAdicIdeal J')) 0)
    ((grQuotComp_piece J' 0) GradedMonoid.GOne.one) = 1
  rw [grQuotComp_piece_one]
  rfl

#print axioms grQuotComp_fam_one

/-- The family is multiplicative across degrees. -/
theorem grQuotComp_fam_mul {i j : ℕ}
    (ai : grPiece R (IsLocalRing.maximalIdeal R) i)
    (aj : grPiece R (IsLocalRing.maximalIdeal R) j) :
    grQuotComp_fam J' (i + j) (GradedMonoid.GMul.mul ai aj) =
      grQuotComp_fam J' i ai * grQuotComp_fam J' j aj := by
  change (DirectSum.of (grPiece (R ⧸ J') (supQuotAdicIdeal J')) (i + j))
      ((grQuotComp_piece J' (i + j)) (GradedMonoid.GMul.mul ai aj)) =
    (DirectSum.of (grPiece (R ⧸ J') (supQuotAdicIdeal J')) i)
        ((grQuotComp_piece J' i) ai) *
      (DirectSum.of (grPiece (R ⧸ J') (supQuotAdicIdeal J')) j)
        ((grQuotComp_piece J' j) aj)
  rw [grQuotComp_piece_mul, DirectSum.of_mul_of]

#print axioms grQuotComp_fam_mul

/-- The graded quotient comparison hom
`gr_𝔪(R) →+* gr(R ⧸ J')`, assembled by `DirectSum.toSemiring`.
-/
def grQuotComp :
    associatedGraded R (IsLocalRing.maximalIdeal R) →+*
      associatedGraded (R ⧸ J') (supQuotAdicIdeal J') :=
  DirectSum.toSemiring (grQuotComp_fam J')
    (grQuotComp_fam_one J') (grQuotComp_fam_mul J')

#print axioms grQuotComp

/-- Computation rule on homogeneous elements. -/
@[simp]
theorem grQuotComp_of (n : ℕ)
    (a : grPiece R (IsLocalRing.maximalIdeal R) n) :
    grQuotComp J' (DirectSum.of (grPiece R (IsLocalRing.maximalIdeal R)) n a) =
      DirectSum.of (grPiece (R ⧸ J') (supQuotAdicIdeal J')) n
        (grQuotComp_piece J' n a) :=
  DirectSum.toSemiring_of _ _ _ _ _

/-! ## §3. The assembly interface (`hcompat` / `hirr`) -/

/-- Lift-compatibility, verbatim the `hcompat` binder shape of
`supT1Data_of_quotAvoid_repaired` (QuotAvoid:677-681).
-/
theorem grQuotComp_compat (y : R)
    (h1 : y ∈ IsLocalRing.maximalIdeal R ^ 1)
    (h2 : Ideal.Quotient.mk J' y ∈ (supQuotAdicIdeal J') ^ 1) :
    grQuotComp J' (supDegOneLift R (IsLocalRing.maximalIdeal R) y h1) =
      supDegOneLift (R ⧸ J') (supQuotAdicIdeal J')
        (Ideal.Quotient.mk J' y) h2 := by
  unfold supDegOneLift supInitForm
  rw [grQuotComp_of, grQuotComp_piece_mk]
  -- The representatives agree (`mk y`); only the membership
  -- proofs differ (proof irrelevance).
  rfl

#print axioms grQuotComp_compat

/-- Irrelevant-ideal non-containment pulls back, verbatim the
`hirr` binder shape of `supT1Data_of_quotAvoid_repaired`
(QuotAvoid:682-687): by contrapositive, every positive-degree
target generator is `grQuotComp` of a positive-degree source
generator (degree-wise surjectivity), hence lies in `Q`.
-/
theorem grQuotComp_irr (Q : Ideal (associatedGraded (R ⧸ J')
      (supQuotAdicIdeal J')))
    (_hQmem : Q ∈ associatedPrimes
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')))
    (hQirr : ¬ SupIrrelevantIdeal (R ⧸ J') (supQuotAdicIdeal J') ≤ Q) :
    ¬ SupIrrelevantIdeal R (IsLocalRing.maximalIdeal R)
      ≤ Ideal.comap (grQuotComp J') Q := by
  intro hle
  apply hQirr
  have hgen : ∀ x ∈ {x : associatedGraded (R ⧸ J') (supQuotAdicIdeal J') |
      ∃ i : ℕ, ∃ _ : 1 ≤ i, ∃ a : grPiece (R ⧸ J') (supQuotAdicIdeal J') i,
        DirectSum.of (grPiece (R ⧸ J') (supQuotAdicIdeal J')) i a = x},
      x ∈ Q := by
    intro x hx
    obtain ⟨i, hi, a, rfl⟩ := hx
    obtain ⟨b, hb⟩ := grQuotComp_piece_surjective J' i a
    have hmem : DirectSum.of (grPiece R (IsLocalRing.maximalIdeal R)) i b ∈
        SupIrrelevantIdeal R (IsLocalRing.maximalIdeal R) :=
      Ideal.subset_span ⟨i, hi, b, rfl⟩
    have hmemQ := (Ideal.mem_comap).mp (hle hmem)
    have himg : DirectSum.of (grPiece (R ⧸ J') (supQuotAdicIdeal J')) i a =
        grQuotComp J' (DirectSum.of
          (grPiece R (IsLocalRing.maximalIdeal R)) i b) := by
      rw [grQuotComp_of, hb]
    rw [himg]
    exact hmemQ
  exact Ideal.span_le.mpr hgen

#print axioms grQuotComp_irr

end GradedQuotientComparison
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
