/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SuperficialReduction
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.PositiveDimTower
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.JointAvoidance
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.QuotientKernelAvoidance
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.PrimeAvoidance

/-!
# M2: ungraded refinement of the R1 joint element
Target: `SupJointUnhgradedRefine` (`QuotientKernelAvoidance.lean`:634) — under
infinite residue field and Noetherian `R`, any R1-shape element (selection +
`S`-avoidance) refines to one that also avoids `Ass(R ⧸ J')`, given
`depth ≥ 1` (`𝔪 ∉ Ass(R ⧸ J')`).

## Proof architecture

* (§0) Ungraded seed (`supUngradedSeed_of_depth`): depth says
  `𝔪 ≤ U` is impossible for `U ∈ Ass(R ⧸ J')` (maximality would force
  `U = 𝔪`), so in-tree prime avoidance
  (`PrimeAvoidance.exists_mem_notMem_associatedPrimes`, a wrap of Mathlib
  `Ideal.subset_union_prime_finite`) gives `w₁ ∈ 𝔪` outside every
  `U ∈ Ass(R ⧸ J')`. No infiniteness needed.
* (§1) Joint line (`supJointUnhgradedRefine_of_noetherian`): rerun the R1
  §4 affine-line argument (`JointAvoidance.lean`, `supJointHomAvoid`)
  on the line `w₁ + t • y₁` (base = ungraded seed, direction = the M2
  input `y₁`) over three bad families:
  - minimal primes `Q ≠ 𝔪` (select half): `≤ 1` bad residue per `Q` via
    the quotient-by-`Q` domain argument, using `y₁ ∉ Q` (direction);
  - graded `P ∈ S`: `≤ 1` bad residue per `P` via the trace-subspace
    argument (`supDegOneTrace`, `supResMk_smul`), using `y₁`'s graded
    avoidance (direction);
  - ungraded `U ∈ Ass(R ⧸ J')`: `≤ 1` bad residue per `U` via the
    quotient-by-`U` domain argument, using `w₁ ∉ U` (base) — the second
    domain case (`y₁ ∈ U`) forces `w₁ ∈ U`, contradicting the seed.
    Finiteness is `supAssFiniteQuot` (T1QuotAvoid:414); depth keeps every
    `U` strictly below `𝔪` (so `U ≤ 𝔪`, giving the residue identification).
  `κ` infinite supplies a residue good for all three families.

## Status

* `supUngradedSeed_of_depth`: unconditional (given Noetherian `R` + depth).
* `supJointUnhgradedRefine_of_noetherian`: unconditional (given
  `[IsNoetherianRing R]` + `Infinite κ` + depth, all present at the §7
  assembly use site).
* Overall: M2 closed. Residual register: empty for this file.

## References

Project (read-only): `QuotientKernelAvoidance.lean` (`SupJointUnhgradedRefine`
:634, `supAssFiniteQuot`:414), `JointAvoidance.lean` (§4 line
argument, `supDegOneTrace`, `supResMk_smul`), `PrimeAvoidance.lean`
(`exists_mem_notMem_associatedPrimes`), `PositiveDimTower.lean`
(`supMem_powOne`, `supDegOneLift`), `SuperficialReduction.lean`
(`SupSelectData`), `AssociatedGradedRing.lean` (`grPiece_mk_add`,
`grPiece_mk_smul`), `GradedSurjection.lean` (`of_smul_eq`:198).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace JointRefinement

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SuperficialReduction
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.PositiveDimTower
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.JointAvoidance
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.QuotientKernelAvoidance
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.PrimeAvoidance

/-! ## §0. The ungraded seed from depth -/

/-- Depth (`𝔪 ∉ Ass(R ⧸ J')`) gives an ungraded-avoiding seed: `𝔪 ≤ U`
is impossible for `U ∈ Ass` (maximality would force `U = 𝔪`), so prime
avoidance supplies `w₁ ∈ 𝔪` outside every associated prime.
-/
theorem supUngradedSeed_of_depth {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (J' : Ideal R)
    (hdepth : IsLocalRing.maximalIdeal R
      ∉ associatedPrimes R (R ⧸ J')) :
    ∃ w₁ ∈ IsLocalRing.maximalIdeal R,
      ∀ U ∈ associatedPrimes R (R ⧸ J'), w₁ ∉ U := by
  have hle : ∀ P ∈ associatedPrimes R (R ⧸ J'),
      ¬ IsLocalRing.maximalIdeal R ≤ P := by
    intro P hP hle
    have hPprime : P.IsPrime := (AssociatedPrimes.mem_iff.mp hP).isPrime
    have heq : IsLocalRing.maximalIdeal R = P :=
      (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hPprime.ne_top hle
    rw [heq] at hdepth
    exact hdepth hP
  exact exists_mem_notMem_associatedPrimes (M := R ⧸ J')
    (IsLocalRing.maximalIdeal R) hle

#print axioms supUngradedSeed_of_depth

/-! ## §1. M2: the joint ungraded refinement -/

/-- M2 (`SupJointUnhgradedRefine`, T1QuotAvoid:634): the R1 §4 line
argument rerun over minimal primes + `S` + `Ass(R ⧸ J')`, with the
ungraded seed (§0) as base and the M2 input `y₁` as direction.

depth). -/
theorem supJointUnhgradedRefine_of_noetherian {R : Type*}
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hInf : Infinite (R ⧸ IsLocalRing.maximalIdeal R)) :
    SupJointUnhgradedRefine (R := R) := by
  classical
  intro J' hdepth S hS _hprime _hirr y₁ hym₁ hsel₁ hgr₁
  obtain ⟨w₁, hw₁m, hw₁U⟩ := supUngradedSeed_of_depth (R := R) J' hdepth
  let : Field (R ⧸ IsLocalRing.maximalIdeal R) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
  have hym_line : ∀ t : R, w₁ + t • y₁ ∈ IsLocalRing.maximalIdeal R := by
    intro t
    have hty : t • y₁ ∈ IsLocalRing.maximalIdeal R := by
      rw [smul_eq_mul]
      exact (IsLocalRing.maximalIdeal R).mul_mem_left _ hym₁
    exact add_mem hw₁m hty
  set v₀ : grPiece R (IsLocalRing.maximalIdeal R) 1 :=
    Submodule.Quotient.mk
      (⟨w₁, supMem_powOne _ _ hw₁m⟩ :
        ↥(IsLocalRing.maximalIdeal R ^ 1)) with hv₀
  set v₁ : grPiece R (IsLocalRing.maximalIdeal R) 1 :=
    Submodule.Quotient.mk
      (⟨y₁, supMem_powOne _ _ hym₁⟩ :
        ↥(IsLocalRing.maximalIdeal R ^ 1)) with hv₁
  have hv₁_mem : ∀ P ∈ S, DirectSum.of
      (grPiece R (IsLocalRing.maximalIdeal R)) 1 v₁ ∉ P := by
    intro P hPm
    exact hgr₁ P hPm
  have mk_line : ∀ t : R,
      (Submodule.Quotient.mk
        (⟨w₁ + t • y₁, supMem_powOne _ _ (hym_line t)⟩ :
          ↥(IsLocalRing.maximalIdeal R ^ 1)) :
        grPiece R (IsLocalRing.maximalIdeal R) 1) = v₀ + t • v₁ := by
    intro t
    have hsub : (⟨w₁ + t • y₁, supMem_powOne _ _ (hym_line t)⟩ :
        ↥(IsLocalRing.maximalIdeal R ^ 1))
        = ⟨w₁, supMem_powOne _ _ hw₁m⟩ +
          t • ⟨y₁, supMem_powOne _ _ hym₁⟩ :=
      Subtype.ext rfl
    rw [hsub, ← grPiece_mk_add, ← grPiece_mk_smul, ← hv₀, ← hv₁]
  have hmin : {Q : Ideal R |
      Q ∈ J'.minimalPrimes ∧ Q ≠ IsLocalRing.maximalIdeal R}.Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing R J').subset
      (fun Q hQ => hQ.1)
  have hTsub : ∀ Q : Ideal R, Q ∈ J'.minimalPrimes →
      Q ≠ IsLocalRing.maximalIdeal R →
      {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
          w₁ + t • y₁ ∈ Q}.Subsingleton := by
    intro Q hQ hQm c₁ hc₁ c₂ hc₂
    obtain ⟨t₁, ht₁, h₁⟩ := hc₁
    obtain ⟨t₂, ht₂, h₂⟩ := hc₂
    have hQprime : Q.IsPrime := Ideal.IsMinimalPrime.isPrime hQ
    have : Q.IsPrime := hQprime
    have hQle : Q ≤ IsLocalRing.maximalIdeal R :=
      IsLocalRing.le_maximalIdeal hQprime.ne_top
    have hmem : (t₁ - t₂) • y₁ ∈ Q := by
      have hsubm := sub_mem h₁ h₂
      have heq : (w₁ + t₁ • y₁) - (w₁ + t₂ • y₁)
          = (t₁ - t₂) • y₁ := by
        rw [sub_smul]
        abel
      rwa [heq] at hsubm
    have hzero : Ideal.Quotient.mk Q (t₁ - t₂)
        * Ideal.Quotient.mk Q y₁ = 0 := by
      have h0 : Ideal.Quotient.mk Q ((t₁ - t₂) • y₁) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      rwa [smul_eq_mul, map_mul] at h0
    rcases mul_eq_zero.mp hzero with htz | hwz
    · have hmemQ : t₁ - t₂ ∈ Q := Ideal.Quotient.eq_zero_iff_mem.mp htz
      have hmemM : t₁ - t₂ ∈ IsLocalRing.maximalIdeal R := hQle hmemQ
      have hmk : Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t₁ =
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t₂ :=
        Ideal.Quotient.eq.mpr hmemM
      exact ht₁.symm.trans (hmk.trans ht₂)
    · have hyQ : y₁ ∈ Q := Ideal.Quotient.eq_zero_iff_mem.mp hwz
      exact absurd hyQ (hsel₁.2 Q hQ hQm)
  have hUsub : ∀ P : Ideal (associatedGraded R (IsLocalRing.maximalIdeal R)),
      P ∈ S →
      {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
          DirectSum.of (grPiece R (IsLocalRing.maximalIdeal R)) 1
            (Submodule.Quotient.mk (⟨w₁ + t • y₁,
              supMem_powOne _ _ (hym_line t)⟩ :
              ↥(IsLocalRing.maximalIdeal R ^ 1))) ∈ P}.Subsingleton := by
    intro P hPm c₁ hc₁ c₂ hc₂
    obtain ⟨t₁, ht₁, h₁⟩ := hc₁
    obtain ⟨t₂, ht₂, h₂⟩ := hc₂
    rw [mk_line] at h₁ h₂
    have e₁ : v₀ + t₁ • v₁ = v₀ + c₁ • v₁ := by
      rw [← ht₁, supResMk_smul]
    have e₂ : v₀ + t₂ • v₁ = v₀ + c₂ • v₁ := by
      rw [← ht₂, supResMk_smul]
    rw [e₁] at h₁
    rw [e₂] at h₂
    have g₁ : v₀ + c₁ • v₁ ∈ supDegOneTrace (R := R) P := h₁
    have g₂ : v₀ + c₂ • v₁ ∈ supDegOneTrace (R := R) P := h₂
    have hsubm := sub_mem g₁ g₂
    have heq : (v₀ + c₁ • v₁) - (v₀ + c₂ • v₁) = (c₁ - c₂) • v₁ := by
      rw [sub_smul]
      abel
    rw [heq] at hsubm
    have hv₁out : v₁ ∉ supDegOneTrace (R := R) P := hv₁_mem P hPm
    have hzero : c₁ - c₂ = 0 := by
      by_contra hc
      exact hv₁out (((supDegOneTrace (R := R) P).smul_mem_iff hc).mp hsubm)
    exact sub_eq_zero.mp hzero
  have hVsub : ∀ U : Ideal R, U ∈ associatedPrimes R (R ⧸ J') →
      {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
          w₁ + t • y₁ ∈ U}.Subsingleton := by
    intro U hU c₁ hc₁ c₂ hc₂
    obtain ⟨t₁, ht₁, h₁⟩ := hc₁
    obtain ⟨t₂, ht₂, h₂⟩ := hc₂
    have hUprime : U.IsPrime := (AssociatedPrimes.mem_iff.mp hU).isPrime
    have : U.IsPrime := hUprime
    have hUle : U ≤ IsLocalRing.maximalIdeal R :=
      IsLocalRing.le_maximalIdeal hUprime.ne_top
    have hmem : (t₁ - t₂) • y₁ ∈ U := by
      have hsubm := sub_mem h₁ h₂
      have heq : (w₁ + t₁ • y₁) - (w₁ + t₂ • y₁)
          = (t₁ - t₂) • y₁ := by
        rw [sub_smul]
        abel
      rwa [heq] at hsubm
    have hzero : Ideal.Quotient.mk U (t₁ - t₂)
        * Ideal.Quotient.mk U y₁ = 0 := by
      have h0 : Ideal.Quotient.mk U ((t₁ - t₂) • y₁) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      rwa [smul_eq_mul, map_mul] at h0
    rcases mul_eq_zero.mp hzero with htz | hwz
    · have hmemU : t₁ - t₂ ∈ U := Ideal.Quotient.eq_zero_iff_mem.mp htz
      have hmemM : t₁ - t₂ ∈ IsLocalRing.maximalIdeal R := hUle hmemU
      have hmk : Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t₁ =
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t₂ :=
        Ideal.Quotient.eq.mpr hmemM
      exact ht₁.symm.trans (hmk.trans ht₂)
    · have hyU : y₁ ∈ U := Ideal.Quotient.eq_zero_iff_mem.mp hwz
      have htyU : t₁ • y₁ ∈ U := by
        rw [smul_eq_mul]
        exact U.mul_mem_left _ hyU
      have hwU : w₁ ∈ U := by
        have hsubm := sub_mem h₁ htyU
        have heq : (w₁ + t₁ • y₁) - t₁ • y₁ = w₁ := by abel
        rwa [heq] at hsubm
      exact absurd hwU (hw₁U U hU)
  have hB₁ : (⋃ Q ∈ {Q : Ideal R |
      Q ∈ J'.minimalPrimes ∧ Q ≠ IsLocalRing.maximalIdeal R},
      {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
          w₁ + t • y₁ ∈ Q}).Finite :=
    hmin.biUnion (fun Q hQ => (hTsub Q hQ.1 hQ.2).finite)
  have hB₂ : (⋃ P ∈ S, {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
        DirectSum.of (grPiece R (IsLocalRing.maximalIdeal R)) 1
          (Submodule.Quotient.mk (⟨w₁ + t • y₁,
            supMem_powOne _ _ (hym_line t)⟩ :
            ↥(IsLocalRing.maximalIdeal R ^ 1))) ∈ P}).Finite :=
    hS.biUnion (fun P hPm => (hUsub P hPm).finite)
  have hB₃ : (⋃ U ∈ associatedPrimes R (R ⧸ J'),
      {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
          w₁ + t • y₁ ∈ U}).Finite :=
    (supAssFiniteQuot (R := R) J').biUnion
      (fun U hU => (hVsub U hU).finite)
  have hBfin : ((⋃ Q ∈ {Q : Ideal R |
      Q ∈ J'.minimalPrimes ∧ Q ≠ IsLocalRing.maximalIdeal R},
      {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
          w₁ + t • y₁ ∈ Q}) ∪
      (⋃ P ∈ S, {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
          DirectSum.of (grPiece R (IsLocalRing.maximalIdeal R)) 1
            (Submodule.Quotient.mk (⟨w₁ + t • y₁,
              supMem_powOne _ _ (hym_line t)⟩ :
              ↥(IsLocalRing.maximalIdeal R ^ 1))) ∈ P}) ∪
      (⋃ U ∈ associatedPrimes R (R ⧸ J'),
        {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
            w₁ + t • y₁ ∈ U})).Finite :=
    (hB₁.union hB₂).union hB₃
  have hex : ∃ c : R ⧸ IsLocalRing.maximalIdeal R,
      c ∉ ((⋃ Q ∈ {Q : Ideal R |
        Q ∈ J'.minimalPrimes ∧ Q ≠ IsLocalRing.maximalIdeal R},
        {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
            w₁ + t • y₁ ∈ Q}) ∪
        (⋃ P ∈ S, {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
            DirectSum.of (grPiece R (IsLocalRing.maximalIdeal R)) 1
              (Submodule.Quotient.mk (⟨w₁ + t • y₁,
                supMem_powOne _ _ (hym_line t)⟩ :
                ↥(IsLocalRing.maximalIdeal R ^ 1))) ∈ P}) ∪
        (⋃ U ∈ associatedPrimes R (R ⧸ J'),
          {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
            Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
              w₁ + t • y₁ ∈ U})) := by
    by_contra hcon
    have hall : ∀ c : R ⧸ IsLocalRing.maximalIdeal R,
        c ∈ ((⋃ Q ∈ {Q : Ideal R |
          Q ∈ J'.minimalPrimes ∧ Q ≠ IsLocalRing.maximalIdeal R},
          {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
            Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
              w₁ + t • y₁ ∈ Q}) ∪
          (⋃ P ∈ S, {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
            Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
              DirectSum.of (grPiece R (IsLocalRing.maximalIdeal R)) 1
                (Submodule.Quotient.mk (⟨w₁ + t • y₁,
                  supMem_powOne _ _ (hym_line t)⟩ :
                  ↥(IsLocalRing.maximalIdeal R ^ 1))) ∈ P}) ∪
          (⋃ U ∈ associatedPrimes R (R ⧸ J'),
            {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
              Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
                w₁ + t • y₁ ∈ U})) :=
      fun c => by_contra (fun hc => hcon ⟨c, hc⟩)
    have hBeq : ((⋃ Q ∈ {Q : Ideal R |
        Q ∈ J'.minimalPrimes ∧ Q ≠ IsLocalRing.maximalIdeal R},
        {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
            w₁ + t • y₁ ∈ Q}) ∪
        (⋃ P ∈ S, {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
            DirectSum.of (grPiece R (IsLocalRing.maximalIdeal R)) 1
              (Submodule.Quotient.mk (⟨w₁ + t • y₁,
                supMem_powOne _ _ (hym_line t)⟩ :
                ↥(IsLocalRing.maximalIdeal R ^ 1))) ∈ P}) ∪
        (⋃ U ∈ associatedPrimes R (R ⧸ J'),
          {c : R ⧸ IsLocalRing.maximalIdeal R | ∃ t : R,
            Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) t = c ∧
              w₁ + t • y₁ ∈ U})) = Set.univ :=
      Set.eq_univ_of_forall hall
    have hfinU : (Set.univ : Set (R ⧸ IsLocalRing.maximalIdeal R)).Finite := by
      rw [← hBeq]
      exact hBfin
    exact (not_finite_iff_infinite.mpr hInf) (Set.finite_univ_iff.mp hfinU)
  obtain ⟨c, hcB⟩ := hex
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨w₁ + t • y₁, hym_line t, ?_, ?_, ?_⟩
  · refine ⟨hym_line t, ?_⟩
    intro Q hQ hQm hyQ
    exact hcB (Set.mem_union_left _
      (Set.mem_union_left _
        (Set.mem_biUnion ⟨hQ, hQm⟩ ⟨t, ht, hyQ⟩)))
  · intro P hPm hmemP
    exact hcB (Set.mem_union_left _
      (Set.mem_union_right _
        (Set.mem_biUnion hPm ⟨t, ht, hmemP⟩)))
  · intro U hU hmemU
    exact hcB (Set.mem_union_right _
      (Set.mem_biUnion hU ⟨t, ht, hmemU⟩))

#print axioms supJointUnhgradedRefine_of_noetherian

end JointRefinement
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
