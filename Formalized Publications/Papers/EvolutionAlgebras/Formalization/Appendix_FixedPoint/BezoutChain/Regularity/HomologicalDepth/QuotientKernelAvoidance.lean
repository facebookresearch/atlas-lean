/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Regular.IsSMulRegular
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.FiltrationStability
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SuperficialReduction
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.AssOfGradedFinite
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.ColonTransfer
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.JointAvoidance
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.PositiveDimTower

/-!
# Quotient-side kernel avoidance: the gap-2 Ass-pullback repair (K1a)

The old kernel `SupT1OfGrAvoid` (ColonDimDrop:378) asks the degree-1 lift to
avoid `Ass(gr_𝔪(R))`-relevant primes, but the scoped discharge passes through
the quotient `R ⧸ J'`, where the primes that matter are the relevant primes of
`Ass(gr(R ⧸ J'))`. Avoiding the ambient family does not imply avoiding the
quotient family (gap K1a).

## Repair

* (§0) The quotient adic ideal `supQuotAdicIdeal J' = 𝔪.map (mk J')` (no
  `IsLocalRing (R ⧸ J')` instance needed) and the lift-membership lemma
  `supQuot_mk_mem_powOne`.
* (§1) The quotient-family restatement `SupT1OfGrAvoidQuot`: avoidance is
  stated against `Ass(gr(R ⧸ J'))`-relevant primes, evaluated at the
  quotient degree-1 lift of `mk y`.
* (§2) The pullback bridge, unconditional for an arbitrary comparison hom
  `φ : gr_𝔪(R) →+* gr(R ⧸ J')`: `supAvoid_pullback` (avoiding pullbacks is
  exactly image-avoidance, by `Ideal.mem_comap`), `supPullback_finite`,
  `supPullback_isPrime`.
* (§3) The R1 re-plug `supT1Data_of_quotAvoid`: `SupJointHomAvoid` takes an
  arbitrary finite family (TowerPosDim:273), so feed it the pullback family
  `comap φ '' {relevant Q ∈ Ass(gr(R ⧸ J'))}`; the pullback bridge converts
  the joint element's avoidance to quotient-side avoidance, and the
  quotient kernel concludes `SupT1Data`. This is the verbatim shape of the
  old `supT1Data_of_graded` (ColonDimDrop:476) with the quotient family.

## Status

unconditional (from explicit data where noted): `supQuot_mk_mem_powOne`,
`supAvoid_pullback`, `supPullback_finite`, `supPullback_isPrime`,
`supT1Data_of_quotAvoid`.
SPEC (open, exact, true classically): `SupT1OfGrAvoidQuot` (repaired
further by the K1c appendix, §7); `SupAssFiniteGrQuot` closed by K1c §6.

## Residual

The comparison hom `φ` (graded, lift-compatible) is taken as explicit data
(`hcompat`, `hirr`); its construction from the `grPiece` infrastructure
(piece maps + `grMul` compatibility) is the remaining scoped work
(~80–120 lines). Nothing here assumes its existence.

## K1c appendix: the ungraded repair + R0-quotient close

The §1 quotient kernel is still false as stated: quotient-side graded
avoidance cannot imply T1 regularity. Witness (classical):
`S = k[[u,v]]/(u²,uv)`, `ȳ = v`: `V` avoids the relevant `(U)` in
`gr(S) = k[U,V]/(U²,UV)` while `u·v = 0` kills regularity. The appendix:

* (§4) Regularity mod `J'` is exactly ungraded avoidance (Noetherian),
  both directions unconditional: `supRegular_of_avoidAss`,
  `supAvoidAss_of_reg` (via Mathlib
  `biUnion_associatedPrimes_eq_zero_divisors`), `supNotRegular_of_mem_ideal`,
  `supAssFiniteQuot`.
* (§5) Necessity, unconditional: `supQuotKernel_implies_avoidAss` (the §1
  kernel forces ungraded avoidance — its false content) and
  `supSelectT1_incompatible_of_maximalAss` (at depth 0, selection and T1
  are incompatible, so the tower needs `depth ≥ 1`; the ∀`J'`
  `SupTowerExact` is false in `dim ≥ 2`).
* (§6) R0-quotient closed unconditionally: `supAssNoethGrQuot`,
  `supAssFiniteGrQuot_of_noetherian`, `supAssFiniteGrQuot_atPrime`
  (verbatim the R0 argument at `(R ⧸ J', supQuotAdicIdeal J')`).
* (§7) The fully repaired kernel `SupT1OfGrAvoidQuotRep` (§1 binders +
  ungraded avoidance), closed by `supT1QuotRep_of_trace` modulo the exact
  trace residual M1 (`SupT1TraceOfGrAvoidQuot`); the T2 assembly
  `supT1Data_of_quotAvoid_repaired` from R0-quot + R1 + M1 + M2
  (`SupJointUnhgradedRefine`, depth-gated) + `φ` data, and its narrow form
  with R0-quot/R1 discharged.
* (§8) Residual register (doc-only).

## K1c grades

unconditional (from explicit data where noted): all of §4, §5, §6,
`supT1QuotRep_of_trace`, `supT1Data_of_quotAvoid_repaired`,
`supT1Data_of_quotAvoid_repaired_narrow`.
SPEC (open, exact, true classically): `SupT1TraceOfGrAvoidQuot` (M1),
`SupJointUnhgradedRefine` (M2).

## K1c residual

[M1 trace kernel — initial-form calculus over `associatedGraded`, no API
in tree], [M2 ungraded refinement — R1 §4 line-argument extension],
[`φ` construction — sibling-scoped], [per-stage `depth ≥ 1` for
master-firing — CM induction along the tower path, no CM API in tree].
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace QuotientKernelAvoidance

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.FiltrationStability
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SuperficialReduction
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssOfGradedFinite
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ColonTransfer
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.JointAvoidance
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.PositiveDimTower

/-! ## §0. The quotient adic ideal -/

/-- The adic ideal for the quotient graded ring `gr(R ⧸ J')`: the image of
the maximal ideal under the quotient map. Stated with `Ideal.map` so no
`IsLocalRing (R ⧸ J')` instance is needed.
-/
def supQuotAdicIdeal {R : Type*} [CommRing R] [IsLocalRing R]
    (J' : Ideal R) : Ideal (R ⧸ J') :=
  (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk J')

#print axioms supQuotAdicIdeal

/-- The quotient lift input: `y ∈ 𝔪` gives `mk y ∈ (supQuotAdicIdeal J') ^ 1`.
-/
theorem supQuot_mk_mem_powOne {R : Type*} [CommRing R] [IsLocalRing R]
    (J' : Ideal R) (y : R) (hym : y ∈ IsLocalRing.maximalIdeal R) :
    Ideal.Quotient.mk J' y ∈ supQuotAdicIdeal J' ^ 1 := by
  rw [pow_one]
  exact Ideal.mem_map_of_mem _ hym

#print axioms supQuot_mk_mem_powOne

/-! ## §1. Quotient-family SPECs -/

/-- SPEC (residual R0-quot): the associated primes of the quotient graded
ring `gr(R ⧸ J')` (as a module over itself) are finite, uniformly in `J'`.
The exact `hfinQ` input of the re-plug `supT1Data_of_quotAvoid`.

Status: open (exact residual; true classically; same Noetherian-transfer price
as R0, applied to `gr(R ⧸ J')`). -/
def SupAssFiniteGrQuot (R : Type*) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ J' : Ideal R,
    (associatedPrimes
      (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
      (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))).Finite

#print axioms SupAssFiniteGrQuot

/-- SPEC (the repaired kernel): graded avoidance quotient-side plus positive
dimension yields `SupT1Data`. The binder shape is verbatim the old
`SupT1OfGrAvoid` (ColonDimDrop:378) with the avoidance family replaced by
the `Ass(gr(R ⧸ J'))`-relevant primes evaluated at the quotient degree-1
lift of `mk y`. This is the family the scoped discharge actually needs.

Status: open (exact residual; true classically). -/
def SupT1OfGrAvoidQuot (R : Type*) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ (J' : Ideal R) (y : R) (hym : y ∈ IsLocalRing.maximalIdeal R),
    ¬ Ring.KrullDimLE 0 (R ⧸ J') →
    (∀ Q ∈ associatedPrimes
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')),
      ¬ SupIrrelevantIdeal (R ⧸ J') (supQuotAdicIdeal J') ≤ Q →
        supDegOneLift (R ⧸ J') (supQuotAdicIdeal J')
          (Ideal.Quotient.mk J' y)
          (supQuot_mk_mem_powOne J' y hym) ∉ Q) →
    SupT1Data J' y

#print axioms SupT1OfGrAvoidQuot

/-! ## §2. The pullback bridge (arbitrary comparison hom) -/

/-- Avoiding pullbacks is exactly image-avoidance: `x` avoids `comap φ Q`
iff `φ x` avoids `Q`. This is `Ideal.mem_comap` (`Iff.rfl`), stated in the
avoidance direction the re-plug consumes.
-/
theorem supAvoid_pullback {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (x : A) (S : Set (Ideal B))
    (h : ∀ Q ∈ S, x ∉ Ideal.comap φ Q) :
    ∀ Q ∈ S, φ x ∉ Q := by
  intro Q hQ hmem
  exact h Q hQ (Ideal.mem_comap.mpr hmem)

#print axioms supAvoid_pullback

/-- The pullback family of a finite family is finite.
-/
theorem supPullback_finite {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (S : Set (Ideal B)) (hfin : S.Finite) :
    (S.image fun Q => Ideal.comap φ Q).Finite :=
  hfin.image _

#print axioms supPullback_finite

/-- Pullbacks of primes are prime (the `Ideal.IsPrime.comap` instance).
-/
theorem supPullback_isPrime {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (Q : Ideal B) (hQ : Q.IsPrime) :
    (Ideal.comap φ Q).IsPrime := by
  have := hQ
  infer_instance

#print axioms supPullback_isPrime

/-! ## §3. The R1 re-plug with the pullback family -/

/-- T2-data existence from R0-quot + R1 + quotient kernel: `SupJointHomAvoid`
takes an arbitrary finite family (TowerPosDim:258), so feed it the pullback
family `comap φ '' {relevant Q ∈ Ass(gr(R ⧸ J'))}`; the §2 bridge converts
the joint element's avoidance to quotient-side avoidance, and the quotient
kernel concludes `SupT1Data`. Verbatim shape of `supT1Data_of_graded`
(ColonDimDrop:462) with the quotient family; closes gap K1a.
The comparison hom `φ` and its lift-compatibility
(`hcompat`) and irrelevant-ideal behavior (`hirr`) are explicit data.
-/
theorem supT1Data_of_quotAvoid {R : Type*} [CommRing R] [IsLocalRing R]
    (hInf : Infinite (R ⧸ IsLocalRing.maximalIdeal R))
    (hfinQ : SupAssFiniteGrQuot (R := R))
    (havoid : SupJointHomAvoid (R := R))
    (hkerQ : SupT1OfGrAvoidQuot (R := R))
    (J' : Ideal R)
    (hpos : ¬ Ring.KrullDimLE 0 (R ⧸ J'))
    (φ : associatedGraded R (IsLocalRing.maximalIdeal R) →+*
      associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
    (hcompat : ∀ (y : R) (h1 : y ∈ IsLocalRing.maximalIdeal R ^ 1)
      (h2 : Ideal.Quotient.mk J' y ∈ supQuotAdicIdeal J' ^ 1),
      φ (supDegOneLift R (IsLocalRing.maximalIdeal R) y h1) =
        supDegOneLift (R ⧸ J') (supQuotAdicIdeal J')
          (Ideal.Quotient.mk J' y) h2)
    (hirr : ∀ Q ∈ associatedPrimes
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')),
      ¬ SupIrrelevantIdeal (R ⧸ J') (supQuotAdicIdeal J') ≤ Q →
        ¬ SupIrrelevantIdeal R (IsLocalRing.maximalIdeal R)
          ≤ Ideal.comap φ Q) :
    ∃ y : R, SupSelectData J' y ∧ SupT1Data J' y := by
  have hTfin : {Q : Ideal (associatedGraded (R ⧸ J')
      (supQuotAdicIdeal J')) |
      Q ∈ associatedPrimes
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')) ∧
        ¬ SupIrrelevantIdeal (R ⧸ J') (supQuotAdicIdeal J') ≤ Q}.Finite :=
    (hfinQ J').subset (fun Q hQ => hQ.1)
  have hSfin : ({Q : Ideal (associatedGraded (R ⧸ J')
      (supQuotAdicIdeal J')) |
      Q ∈ associatedPrimes
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')) ∧
        ¬ SupIrrelevantIdeal (R ⧸ J') (supQuotAdicIdeal J') ≤ Q}.image
      fun Q => Ideal.comap φ Q).Finite :=
    supPullback_finite φ _ hTfin
  have hprime : ∀ P ∈ ({Q : Ideal (associatedGraded (R ⧸ J')
      (supQuotAdicIdeal J')) |
      Q ∈ associatedPrimes
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')) ∧
        ¬ SupIrrelevantIdeal (R ⧸ J') (supQuotAdicIdeal J') ≤ Q}.image
      fun Q => Ideal.comap φ Q), P.IsPrime := by
    intro P hP
    obtain ⟨Q, hQmem, rfl⟩ := hP
    exact supPullback_isPrime φ Q
      (IsAssociatedPrime.isPrime hQmem.1)
  have hirrel : ∀ P ∈ ({Q : Ideal (associatedGraded (R ⧸ J')
      (supQuotAdicIdeal J')) |
      Q ∈ associatedPrimes
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')) ∧
        ¬ SupIrrelevantIdeal (R ⧸ J') (supQuotAdicIdeal J') ≤ Q}.image
      fun Q => Ideal.comap φ Q),
      ¬ SupIrrelevantIdeal R (IsLocalRing.maximalIdeal R) ≤ P := by
    intro P hP
    obtain ⟨Q, hQmem, rfl⟩ := hP
    exact hirr Q hQmem.1 hQmem.2
  obtain ⟨y, hym, hsel, hgr⟩ :=
    havoid hInf J' _ hSfin hprime hirrel
  refine ⟨y, hsel, hkerQ J' y hym hpos ?_⟩
  intro Q hQmem hQirr
  have hmem : Ideal.comap φ Q ∈
      ({Q : Ideal (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')) |
      Q ∈ associatedPrimes
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')) ∧
        ¬ SupIrrelevantIdeal (R ⧸ J') (supQuotAdicIdeal J') ≤ Q}.image
      fun Q => Ideal.comap φ Q) :=
    ⟨Q, ⟨hQmem, hQirr⟩, rfl⟩
  have hav : supDegOneLift R (IsLocalRing.maximalIdeal R) y
      (supMem_powOne _ _ hym) ∉ Ideal.comap φ Q :=
    hgr _ hmem
  have himg : φ (supDegOneLift R (IsLocalRing.maximalIdeal R) y
      (supMem_powOne _ _ hym)) ∉ Q :=
    fun hcon => hav (Ideal.mem_comap.mpr hcon)
  rw [hcompat y _ (supQuot_mk_mem_powOne J' y hym)] at himg
  exact himg

#print axioms supT1Data_of_quotAvoid

/-! ## §4. Regularity is ungraded avoidance (K1c) -/

/-- Regularity mod `J'` from ungraded avoidance: if `y` lies in no
associated prime of `R ⧸ J'`, it is regular on `R ⧸ J'`. Via Mathlib's
`biUnion_associatedPrimes_eq_zero_divisors` (over Noetherian rings the
union of `Ass` is the zerodivisor set): off the union, `y • x = 0`
forces `x = 0`, hence `y • a = y • b` forces `a = b` by subtraction.
-/
theorem supRegular_of_avoidAss {R : Type*} [CommRing R] [IsNoetherianRing R]
    (J' : Ideal R) (y : R)
    (hav : ∀ P ∈ associatedPrimes R (R ⧸ J'), y ∉ P) :
    IsSMulRegular (R ⧸ J') y := by
  have hunion : y ∉ ⋃ P ∈ associatedPrimes R (R ⧸ J'), (P : Set R) := by
    intro hmem
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨P, hP, hmem⟩ := hmem
    exact hav P hP hmem
  rw [biUnion_associatedPrimes_eq_zero_divisors] at hunion
  simp only [Set.mem_ofPred_eq] at hunion
  intro a b hab
  have hab' : y • a = y • b := hab
  have h0 : y • (a - b) = (0 : R ⧸ J') := by
    rw [smul_sub, hab', sub_self]
  have hsub : a - b = 0 := by
    by_contra hne
    exact hunion ⟨_, hne, h0⟩
  exact sub_eq_zero.mp hsub

#print axioms supRegular_of_avoidAss

/-- The converse: regularity mod `J'` forces ungraded avoidance. If
`y ∈ P` for some `P ∈ Ass(R ⧸ J')` then `y` is a zerodivisor,
contradicting regularity. Together with `supRegular_of_avoidAss`,
regularity mod `J'` is exactly ungraded avoidance (Noetherian) — so the
ungraded hypothesis in the §7 repair is both necessary and sufficient
for the T1 regularity half.
-/
theorem supAvoidAss_of_reg {R : Type*} [CommRing R] [IsNoetherianRing R]
    (J' : Ideal R) (y : R)
    (hreg : IsSMulRegular (R ⧸ J') y) :
    ∀ P ∈ associatedPrimes R (R ⧸ J'), y ∉ P := by
  have hmem : y ∉ ⋃ P ∈ associatedPrimes R (R ⧸ J'), (P : Set R) := by
    rw [biUnion_associatedPrimes_eq_zero_divisors]
    simp only [Set.mem_ofPred_eq]
    intro hcon
    obtain ⟨x, hx, h0⟩ := hcon
    have h0' : (y • ·) x = (y • ·) (0 : R ⧸ J') := by
      change y • x = y • (0 : R ⧸ J')
      rw [h0, smul_zero]
    exact hx (hreg h0')
  intro P hP hPy
  apply hmem
  simp only [Set.mem_iUnion]
  exact ⟨P, hP, hPy⟩

#print axioms supAvoidAss_of_reg

/-- Corollary: `y ∈ J'` kills regularity (at nontrivial quotient). The
`y = x ∈ (x)` instance is the witness that the original kernel
(ColonDimDrop:378) is false without a `J'`-linking hypothesis: such a
`y` can satisfy graded avoidance and positivity while acting as zero.
-/
theorem supNotRegular_of_mem_ideal {R : Type*} [CommRing R]
    (J' : Ideal R) (y : R) (hy : y ∈ J') [Nontrivial (R ⧸ J')] :
    ¬ IsSMulRegular (R ⧸ J') y := by
  intro hreg
  have h1 : (1 : R) ∈ J' := by
    have hsmul : y • (1 : R) ∈ ((J' : Ideal R) : Submodule R R) := by
      rw [smul_eq_mul, mul_one]
      exact hy
    exact mem_of_isSMulRegular_quotient_of_smul_mem hreg hsmul
  exact (Ideal.Quotient.nontrivial_iff.mp inferInstance)
    (J'.eq_top_iff_one.mpr h1)

#print axioms supNotRegular_of_mem_ideal

/-- The ungraded family is finite (Noetherian): `Ass(R ⧸ J')` is finite
since `R ⧸ J'` is a finite module. This is the finiteness input the M2
refinement (§7) needs to fold ungraded avoidance into the
joint-avoidance line argument.
-/
theorem supAssFiniteQuot {R : Type*} [CommRing R] [IsNoetherianRing R]
    (J' : Ideal R) : (associatedPrimes R (R ⧸ J')).Finite :=
  associatedPrimes.finite R (R ⧸ J')

#print axioms supAssFiniteQuot

/-! ## §5. The quotient kernel forces ungraded avoidance (K1c) -/

/-- The §1 quotient kernel's hidden content: if `SupT1OfGrAvoidQuot` held,
every quotient-avoiding `y` at positive dimension would avoid
`Ass(R ⧸ J')`. Contrapositively, any `y` with quotient-avoidance inside
some `P ∈ Ass(R ⧸ J')` refutes the kernel. Such `y` exist classically
(e.g. `S = k[[u,v]]/(u²,uv)`, `ȳ = v`: `V` avoids the relevant `(U)` in
`gr(S) = k[U,V]/(U²,UV)` while `u·v = 0` kills regularity), so the
kernel as stated is false; §7 adds exactly the missing ungraded
hypothesis. A formal `¬`-theorem would need `Ass(gr)` computation over
the project's `associatedGraded` (no such API in tree) and is not
attempted.
-/
theorem supQuotKernel_implies_avoidAss {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R]
    (hkerQ : SupT1OfGrAvoidQuot (R := R))
    (J' : Ideal R) (y : R) (hym : y ∈ IsLocalRing.maximalIdeal R)
    (hpos : ¬ Ring.KrullDimLE 0 (R ⧸ J'))
    (hgr : ∀ Q ∈ associatedPrimes
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')),
      ¬ SupIrrelevantIdeal (R ⧸ J') (supQuotAdicIdeal J') ≤ Q →
        supDegOneLift (R ⧸ J') (supQuotAdicIdeal J')
          (Ideal.Quotient.mk J' y)
          (supQuot_mk_mem_powOne J' y hym) ∉ Q) :
    ∀ P ∈ associatedPrimes R (R ⧸ J'), y ∉ P :=
  supAvoidAss_of_reg J' y (hkerQ J' y hym hpos hgr).1

#print axioms supQuotKernel_implies_avoidAss

/-- Depth-zero incompatibility: if the maximal ideal itself is associated
(`depth (R ⧸ J') = 0`), selection and T1 data are incompatible — no `y`
can satisfy both. Selection forces `y ∈ 𝔪`; T1 regularity forces
`y ∉ ⋃Ass ∋ 𝔪` (§4). Consequence: tower existence `∃ y, select ∧ T1` at
positive-dimensional `J'` needs `depth ≥ 1`; the ∀`J'` tower
(`SupTowerExact`, ColonTransfer:278) is false in `dim ≥ 2` (witness
`J' = (x₁², x₁x₂)` at `n = 2`: `dim R⧸J' = 1`, `ann(x₁) = 𝔪`), and the
§7 assembly carries an explicit depth hypothesis. A formal
`¬ SupTowerExact` would need dimension + `Ass` computation on the
explicit quotient and is not attempted.
-/
theorem supSelectT1_incompatible_of_maximalAss {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (J' : Ideal R)
    (hmax : IsLocalRing.maximalIdeal R ∈ associatedPrimes R (R ⧸ J')) :
    ¬ ∃ y : R, SupSelectData J' y ∧ SupT1Data J' y := by
  rintro ⟨y, hsel, hT1⟩
  exact (supAvoidAss_of_reg J' y hT1.1 _ hmax) hsel.1

#print axioms supSelectT1_incompatible_of_maximalAss

/-! ## §6. R0-quotient closed (K1c) -/

/-- `gr(R ⧸ J')` over the quotient adic ideal is Noetherian: the M4b
surjection (`polySurj`, stated generally over `(R, I)`) exhibits it as a
quotient of the Noetherian polynomial ring over
`(R ⧸ J') ⧸ supQuotAdicIdeal J'`. Verbatim the R0 argument
(`supAss_isNoetherianRing_gr`) at `(R ⧸ J', supQuotAdicIdeal J')`.
-/
theorem supAssNoethGrQuot {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (J' : Ideal R) :
    IsNoetherianRing
      (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')) := by
  obtain ⟨S, hS⟩ := Ideal.fg_of_isNoetherianRing (supQuotAdicIdeal J')
  have hgen : Ideal.span (Set.range (supAss_family S)) =
      supQuotAdicIdeal J' := by
    rw [supAss_family_range]
    exact hS
  have : IsNoetherianRing (MvPolynomial (Fin S.card)
      ((R ⧸ J') ⧸ supQuotAdicIdeal J')) := inferInstance
  exact isNoetherianRing_of_surjective _ _
    (polySurj (R ⧸ J') (supQuotAdicIdeal J') S.card (supAss_family S) hgen)
    (polySurj_surjective (R ⧸ J') (supQuotAdicIdeal J') S.card
      (supAss_family S) hgen)

#print axioms supAssNoethGrQuot

/-- R0-quotient (`SupAssFiniteGrQuot`, §1) at general Noetherian local `R`,
unconditional: `Ass(gr(R ⧸ J'))` is finite, uniformly in `J'`. Verbatim
the R0 argument (`supAssFiniteGr_of_noetherian`) at
`(R ⧸ J', supQuotAdicIdeal J')`, closing the §1 residual.
-/
theorem supAssFiniteGrQuot_of_noetherian {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] :
    SupAssFiniteGrQuot (R := R) := by
  intro J'
  have hNoeth : IsNoetherianRing
      (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')) :=
    supAssNoethGrQuot (R := R) J'
  have hFin : Module.Finite
      (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
      (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')) :=
    Module.Finite.self _
  exact @associatedPrimes.finite
    (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
    (instCommRing (R ⧸ J') (supQuotAdicIdeal J'))
    (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
    (@Ring.toAddCommGroup
      (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
      (@CommRing.toRing
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
        (instCommRing (R ⧸ J') (supQuotAdicIdeal J'))))
    (@Semiring.toModule
      (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
      (@CommSemiring.toSemiring
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
        (@CommRing.toCommSemiring
          (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
          (instCommRing (R ⧸ J') (supQuotAdicIdeal J')))))
    hNoeth
    hFin

#print axioms supAssFiniteGrQuot_of_noetherian

/-- R0-quotient at `R_Q`, unconditional: no hypotheses beyond `Q` prime.
Feeds the per-`Q` tower construction behind the H5 plugs.
-/
theorem supAssFiniteGrQuot_atPrime (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (J' : Ideal (Localization.AtPrime Q)) :
    (associatedPrimes
      (associatedGraded (Localization.AtPrime Q ⧸ J')
        (supQuotAdicIdeal J'))
      (associatedGraded (Localization.AtPrime Q ⧸ J')
        (supQuotAdicIdeal J'))).Finite := by
  have : IsNoetherianRing (Localization.AtPrime Q) :=
    isNoetherianRing_atPrime Q
  exact supAssFiniteGrQuot_of_noetherian (R := Localization.AtPrime Q) J'

#print axioms supAssFiniteGrQuot_atPrime

/-! ## §7. The fully repaired kernel and its conditional close (K1c) -/

/-- SPEC (residual M1): the Valabrega–Valla order-one trace from
quotient-side graded avoidance. The trace half of `SupT1Data`
(SupColonTransfer:169), with the quotient-avoidance binders of
`SupT1OfGrAvoidQuot` (§1). True classically (filter-regular ⟹ superficial
of order one); the scoped proof needs initial-form calculus over
`associatedGraded` (products of initial forms, `(0 : y*)`-torsion killed
by a power of the irrelevant ideal) — no such API in tree.

Status: open (exact residual; true classically). -/
def SupT1TraceOfGrAvoidQuot (R : Type*) [CommRing R] [IsLocalRing R] :
    Prop :=
  ∀ (J' : Ideal R) (y : R) (hym : y ∈ IsLocalRing.maximalIdeal R),
    ¬ Ring.KrullDimLE 0 (R ⧸ J') →
    (∀ Q ∈ associatedPrimes
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')),
      ¬ SupIrrelevantIdeal (R ⧸ J') (supQuotAdicIdeal J') ≤ Q →
        supDegOneLift (R ⧸ J') (supQuotAdicIdeal J')
          (Ideal.Quotient.mk J' y)
          (supQuot_mk_mem_powOne J' y hym) ∉ Q) →
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n → ∀ z : R,
      z ∈ IsLocalRing.maximalIdeal R ^ (n + 2) ⊔ J' →
      z ∈ Ideal.span {y} →
      ∃ a : R, a ∈ IsLocalRing.maximalIdeal R ^ (n + 1) ⊔ J' ∧ a * y = z

#print axioms SupT1TraceOfGrAvoidQuot

/-- SPEC (the fully repaired kernel): quotient-side graded avoidance plus
ungraded avoidance plus positive dimension yields `SupT1Data`. Verbatim
the §1 `SupT1OfGrAvoidQuot` binders with the ungraded-avoidance
hypothesis added — the hypothesis §4 shows is exactly regularity, and §5
shows is missing (the `v`-counterexample). Satisfiable only at
`depth ≥ 1` (cf. `supSelectT1_incompatible_of_maximalAss`), hence the
depth hypothesis in the assembly below and in M2.

Status: open modulo M1 only (closed by `supT1QuotRep_of_trace`). -/
def SupT1OfGrAvoidQuotRep (R : Type*) [CommRing R] [IsLocalRing R] :
    Prop :=
  ∀ (J' : Ideal R) (y : R) (hym : y ∈ IsLocalRing.maximalIdeal R),
    ¬ Ring.KrullDimLE 0 (R ⧸ J') →
    (∀ P ∈ associatedPrimes R (R ⧸ J'), y ∉ P) →
    (∀ Q ∈ associatedPrimes
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')),
      ¬ SupIrrelevantIdeal (R ⧸ J') (supQuotAdicIdeal J') ≤ Q →
        supDegOneLift (R ⧸ J') (supQuotAdicIdeal J')
          (Ideal.Quotient.mk J' y)
          (supQuot_mk_mem_powOne J' y hym) ∉ Q) →
    SupT1Data J' y

#print axioms SupT1OfGrAvoidQuotRep

/-- The fully repaired kernel from the trace residual: regularity is
`supRegular_of_avoidAss` (§4), the trace is M1. No R0/R1 input needed —
both halves are per-`y` consequences.
-/
theorem supT1QuotRep_of_trace {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    (htraceQ : SupT1TraceOfGrAvoidQuot (R := R)) :
    SupT1OfGrAvoidQuotRep (R := R) := by
  intro J' y hym hpos hungr hgr
  exact ⟨supRegular_of_avoidAss J' y hungr,
    htraceQ J' y hym hpos hgr⟩

#print axioms supT1QuotRep_of_trace

/-- SPEC (residual M2): ungraded refinement of an R1 joint element. Given
`depth ≥ 1` (`𝔪 ∉ Ass(R ⧸ J')` — load-bearing: at depth 0 the conclusion
is unsatisfiable, `supSelectT1_incompatible_of_maximalAss`), any R1-shape
element (selection + `S`-avoidance) refines to one that also avoids
`Ass(R ⧸ J')`. True classically: the R1 §4 line argument over the extended
finite family (minimal primes + `S` + `Ass(R ⧸ J')`, finite by
`supAssFiniteQuot`); the depth hypothesis keeps every ungraded prime
strictly below `𝔪`, so each kills at most one residue class per line.

Status: open (exact residual; true classically). -/
def SupJointUnhgradedRefine (R : Type*) [CommRing R] [IsLocalRing R] :
    Prop :=
  ∀ (J' : Ideal R),
    IsLocalRing.maximalIdeal R ∉ associatedPrimes R (R ⧸ J') →
    ∀ (S : Set (Ideal
        (associatedGraded R (IsLocalRing.maximalIdeal R)))),
      S.Finite →
      (∀ P ∈ S, P.IsPrime) →
      (∀ P ∈ S,
        ¬ SupIrrelevantIdeal R (IsLocalRing.maximalIdeal R) ≤ P) →
      ∀ (y₁ : R) (hym₁ : y₁ ∈ IsLocalRing.maximalIdeal R),
        SupSelectData J' y₁ →
        (∀ P ∈ S, supDegOneLift R (IsLocalRing.maximalIdeal R) y₁
          (supMem_powOne _ _ hym₁) ∉ P) →
        ∃ y : R, ∃ hym : y ∈ IsLocalRing.maximalIdeal R,
          SupSelectData J' y ∧
          (∀ P ∈ S, supDegOneLift R (IsLocalRing.maximalIdeal R) y
            (supMem_powOne _ _ hym) ∉ P) ∧
          (∀ P ∈ associatedPrimes R (R ⧸ J'), y ∉ P)

#print axioms SupJointUnhgradedRefine

/-- T2-data existence from R0-quot + R1 + M1 + M2: the §3 re-plug with the
fully repaired kernel. The R1 joint element over the pullback family
refines (M2) to also avoid `Ass(R ⧸ J')`; the §2 bridge converts its
avoidance to quotient-side avoidance; regularity is §4 and the trace is
M1. The depth hypothesis is load-bearing (§5).

depth). -/
theorem supT1Data_of_quotAvoid_repaired {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R]
    (hInf : Infinite (R ⧸ IsLocalRing.maximalIdeal R))
    (hfinQ : SupAssFiniteGrQuot (R := R))
    (havoid : SupJointHomAvoid (R := R))
    (htraceQ : SupT1TraceOfGrAvoidQuot (R := R))
    (hrefine : SupJointUnhgradedRefine (R := R))
    (J' : Ideal R)
    (hpos : ¬ Ring.KrullDimLE 0 (R ⧸ J'))
    (hdepth : IsLocalRing.maximalIdeal R
      ∉ associatedPrimes R (R ⧸ J'))
    (φ : associatedGraded R (IsLocalRing.maximalIdeal R) →+*
      associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
    (hcompat : ∀ (y : R) (h1 : y ∈ IsLocalRing.maximalIdeal R ^ 1)
      (h2 : Ideal.Quotient.mk J' y ∈ supQuotAdicIdeal J' ^ 1),
      φ (supDegOneLift R (IsLocalRing.maximalIdeal R) y h1) =
        supDegOneLift (R ⧸ J') (supQuotAdicIdeal J')
          (Ideal.Quotient.mk J' y) h2)
    (hirr : ∀ Q ∈ associatedPrimes
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')),
      ¬ SupIrrelevantIdeal (R ⧸ J') (supQuotAdicIdeal J') ≤ Q →
        ¬ SupIrrelevantIdeal R (IsLocalRing.maximalIdeal R)
          ≤ Ideal.comap φ Q) :
    ∃ y : R, SupSelectData J' y ∧ SupT1Data J' y := by
  have hTfin : {Q : Ideal (associatedGraded (R ⧸ J')
      (supQuotAdicIdeal J')) |
      Q ∈ associatedPrimes
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')) ∧
        ¬ SupIrrelevantIdeal (R ⧸ J') (supQuotAdicIdeal J') ≤ Q}.Finite :=
    (hfinQ J').subset (fun Q hQ => hQ.1)
  have hSfin : ({Q : Ideal (associatedGraded (R ⧸ J')
      (supQuotAdicIdeal J')) |
      Q ∈ associatedPrimes
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')) ∧
        ¬ SupIrrelevantIdeal (R ⧸ J') (supQuotAdicIdeal J') ≤ Q}.image
      fun Q => Ideal.comap φ Q).Finite :=
    supPullback_finite φ _ hTfin
  have hprime : ∀ P ∈ ({Q : Ideal (associatedGraded (R ⧸ J')
      (supQuotAdicIdeal J')) |
      Q ∈ associatedPrimes
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')) ∧
        ¬ SupIrrelevantIdeal (R ⧸ J') (supQuotAdicIdeal J') ≤ Q}.image
      fun Q => Ideal.comap φ Q), P.IsPrime := by
    intro P hP
    obtain ⟨Q, hQmem, rfl⟩ := hP
    exact supPullback_isPrime φ Q
      (IsAssociatedPrime.isPrime hQmem.1)
  have hirrel : ∀ P ∈ ({Q : Ideal (associatedGraded (R ⧸ J')
      (supQuotAdicIdeal J')) |
      Q ∈ associatedPrimes
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')) ∧
        ¬ SupIrrelevantIdeal (R ⧸ J') (supQuotAdicIdeal J') ≤ Q}.image
      fun Q => Ideal.comap φ Q),
      ¬ SupIrrelevantIdeal R (IsLocalRing.maximalIdeal R) ≤ P := by
    intro P hP
    obtain ⟨Q, hQmem, rfl⟩ := hP
    exact hirr Q hQmem.1 hQmem.2
  obtain ⟨y₁, hym₁, hsel₁, hgr₁⟩ :=
    havoid hInf J' _ hSfin hprime hirrel
  obtain ⟨y, hym, hsel, hgr, hungr⟩ :=
    hrefine J' hdepth _ hSfin hprime hirrel y₁ hym₁ hsel₁
      (fun P hP => hgr₁ P hP)
  refine ⟨y, hsel, ?_, ?_⟩
  · exact supRegular_of_avoidAss J' y hungr
  · apply htraceQ J' y hym hpos
    intro Q hQmem hQirr
    have hmem : Ideal.comap φ Q ∈
        ({Q : Ideal (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')) |
        Q ∈ associatedPrimes
          (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
          (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')) ∧
          ¬ SupIrrelevantIdeal (R ⧸ J') (supQuotAdicIdeal J') ≤ Q}.image
        fun Q => Ideal.comap φ Q) :=
      ⟨Q, ⟨hQmem, hQirr⟩, rfl⟩
    have hav : supDegOneLift R (IsLocalRing.maximalIdeal R) y
        (supMem_powOne _ _ hym) ∉ Ideal.comap φ Q :=
      hgr _ hmem
    have himg : φ (supDegOneLift R (IsLocalRing.maximalIdeal R) y
        (supMem_powOne _ _ hym)) ∉ Q :=
      fun hcon => hav (Ideal.mem_comap.mpr hcon)
    rw [hcompat y _ (supQuot_mk_mem_powOne J' y hym)] at himg
    exact himg

#print axioms supT1Data_of_quotAvoid_repaired

/-- The §7 assembly with R0-quot (§6) and R1 (proved
`supJointHomAvoid`) discharged: T2-data from M1 + M2 + `φ` data + depth
only. This is the exact input shape the tower masters consume, gated on
the two scoped residuals and the comparison hom.

Conditional on exactly
`[SupT1TraceOfGrAvoidQuot, SupJointUnhgradedRefine]` (+ `φ` data +
depth). -/
theorem supT1Data_of_quotAvoid_repaired_narrow {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R]
    (hInf : Infinite (R ⧸ IsLocalRing.maximalIdeal R))
    (htraceQ : SupT1TraceOfGrAvoidQuot (R := R))
    (hrefine : SupJointUnhgradedRefine (R := R))
    (J' : Ideal R)
    (hpos : ¬ Ring.KrullDimLE 0 (R ⧸ J'))
    (hdepth : IsLocalRing.maximalIdeal R
      ∉ associatedPrimes R (R ⧸ J'))
    (φ : associatedGraded R (IsLocalRing.maximalIdeal R) →+*
      associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
    (hcompat : ∀ (y : R) (h1 : y ∈ IsLocalRing.maximalIdeal R ^ 1)
      (h2 : Ideal.Quotient.mk J' y ∈ supQuotAdicIdeal J' ^ 1),
      φ (supDegOneLift R (IsLocalRing.maximalIdeal R) y h1) =
        supDegOneLift (R ⧸ J') (supQuotAdicIdeal J')
          (Ideal.Quotient.mk J' y) h2)
    (hirr : ∀ Q ∈ associatedPrimes
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J'))
        (associatedGraded (R ⧸ J') (supQuotAdicIdeal J')),
      ¬ SupIrrelevantIdeal (R ⧸ J') (supQuotAdicIdeal J') ≤ Q →
        ¬ SupIrrelevantIdeal R (IsLocalRing.maximalIdeal R)
          ≤ Ideal.comap φ Q) :
    ∃ y : R, SupSelectData J' y ∧ SupT1Data J' y :=
  supT1Data_of_quotAvoid_repaired (R := R) hInf
    supAssFiniteGrQuot_of_noetherian supJointHomAvoid
    htraceQ hrefine J' hpos hdepth φ hcompat hirr

#print axioms supT1Data_of_quotAvoid_repaired_narrow

/-! ## §8. K1c residual register (doc-only)

closed this lane: [regularity ⟺ ungraded avoidance, both directions],
[repair necessity — the §1 kernel forces ungraded avoidance],
[depth-zero select/T1 incompatibility], [R0-quotient, general + atPrime],
[fully repaired kernel modulo M1], [T2 assembly modulo M1 + M2 + `φ` +
depth, with R0-quot/R1 discharged].

open (exact) after this lane:

* M1 `SupT1TraceOfGrAvoidQuot` (§7): the order-one trace from
  quotient-side graded avoidance. True classically
  of initial-form calculus over `associatedGraded` (products of initial
  forms, `(0 : y*)`-torsion killed by irrelevant powers) — no such API
  in tree.
* M2 `SupJointUnhgradedRefine` (§7): ungraded refinement of the R1 joint
  element (depth-gated). True classically
  the R1 §4 line argument over the ungraded family (finite by
  `supAssFiniteQuot`).
* `φ` construction (comparison hom `gr_𝔪(R) →+* gr(R ⧸ J')`, §3 data):
  sibling-scoped ~80–120 lines from the `grPiece` infrastructure.
* Per-stage `depth ≥ 1` for master-firing: holds along the actual tower
  path (CM induction from `⊥` over a domain) but needs CM API absent
  from Mathlib and the project; alternatively re-shape `SupTowerExact`
  (ColonTransfer:278) to carry depth — a T2-file change. Note the ∀`J'`
  form is false in `dim ≥ 2` (§5 witness), so the masters cannot fire on
  it as stated.
-/

end QuotientKernelAvoidance
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
