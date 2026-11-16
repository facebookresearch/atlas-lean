/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.SemiperfectCrystallinePeriodRings
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Original residues and literal finite A_cris thickenings

The residue of A_cris is induced by the original PD hull residue and
the actual first p-adic projection. Finite rings are literally
A_cris/(p^(n+1)), including possible p-torsion. Their PD ideals are the
full kernels of reduction to R, without a uniform ideal-nilpotence bound.

Source: Scholze--Weinstein1211.6357v2, Proposition4.1.3 and Lemma4.1.8.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.RingTheory.SemiperfectCrystallineResidues

open SemiperfectWittPDEnvelopes SemiperfectCrystallinePeriodRings

variable (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
  (A : UniversalEnvelope p R) (E : ResidueIdentification A)

/-- The residue of the original hull, through its displayed quotient. -/
def hullResidue : A.algebra.ring →+* R :=
  E.equiv.toRingHom.comp (Ideal.Quotient.mk A.algebra.ideal)

/-- The residue of the literal p-adic completion. -/
def completedResidue : Acris p R A →+* R :=
  finiteEvaluation (hullResidue p R A E) 1 (by simp)

/-- The completion residue preserves every original hull coefficient. -/
theorem completedResidue_hull (x : A.algebra.ring) :
    completedResidue p R A E (hullToAcris p R A x) = hullResidue p R A E x :=
  finiteEvaluation_hull _ _ _ x

/-- The full original Witt residue is retained. -/
theorem completedResidue_witt (x : WittRing p R) :
    completedResidue p R A E (wittToAcris p R A x) = reduction p R x :=
  (finiteEvaluation_witt _ _ _ x).trans (E.coefficients x)

/-- The actual completed residue is surjective because the original hull residue is. -/
theorem completedResidue_surjective : Function.Surjective (completedResidue p R A E) := by
  intro r
  obtain ⟨q, hq⟩ := E.equiv.surjective r
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨hullToAcris p R A x, (completedResidue_hull p R A E x).trans hq⟩

/-- Only the p-adic ideal is used to form the finite stages. -/
def completedIdeal : Ideal (Acris p R A) := Ideal.span {(p : Acris p R A)}

/-- These are the original finite completed rings, rather than a PD-ideal completion. -/
abbrev FiniteRing (n : ℕ) := Acris p R A ⧸ completedIdeal p R A ^ (n + 1)

/-- The literal quotient projection from A_cris. -/
def finiteQuotient (n : ℕ) : Acris p R A →+* FiniteRing p R A n :=
  Ideal.Quotient.mk (completedIdeal p R A ^ (n + 1))

/-- The residue kills every positive p-adic ideal power. -/
theorem completedIdeal_le_kernel (n : ℕ) :
    completedIdeal p R A ^ (n + 1) ≤ RingHom.ker (completedResidue p R A E) := by
  rw [completedIdeal, Ideal.span_singleton_pow, Ideal.span_le]
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  change completedResidue p R A E ((p : Acris p R A) ^ (n + 1)) = 0
  simp only [map_pow, map_natCast, CharP.cast_eq_zero R p, zero_pow (Nat.succ_ne_zero n)]

/-- The finite residue is induced by that exact completed residue. -/
def finiteResidue (n : ℕ) : FiniteRing p R A n →+* R :=
  Ideal.Quotient.lift _ (completedResidue p R A E)
    (completedIdeal_le_kernel p R A E n)

/-- The finite hull coefficient map. -/
def finiteHullMap (n : ℕ) : A.algebra.ring →+* FiniteRing p R A n :=
  (finiteQuotient p R A n).comp (hullToAcris p R A)

/-- The finite residue preserves every original hull coefficient. -/
theorem finiteResidue_hull (n : ℕ) (x : A.algebra.ring) :
    finiteResidue p R A E n (finiteHullMap p R A n x) = hullResidue p R A E x :=
  completedResidue_hull p R A E x

/-- Every finite stage still surjects onto the original R. -/
theorem finiteResidue_surjective (n : ℕ) : Function.Surjective (finiteResidue p R A E n) := by
  intro r
  obtain ⟨x, hx⟩ := completedResidue_surjective p R A E r
  exact ⟨finiteQuotient p R A n x, hx⟩

/-- The PD ideal is the full original residue kernel. -/
def finiteIdeal (n : ℕ) : Ideal (FiniteRing p R A n) :=
  RingHom.ker (finiteResidue p R A E n)

/-- The reduction dictionary is the native first isomorphism theorem. -/
def finiteResidueEquiv (n : ℕ) :
    (FiniteRing p R A n ⧸ finiteIdeal p R A E n) ≃+* R :=
  (finiteResidue p R A E n).quotientKerEquivOfSurjective
    (finiteResidue_surjective p R A E n)

/-- The actual p-power transition of the literal completed rings. -/
def finiteTransition {n m : ℕ} (h : n ≤ m) :
    FiniteRing p R A m →+* FiniteRing p R A n :=
  Ideal.Quotient.factorPow (completedIdeal p R A) (Nat.add_le_add_right h 1)

/-- The p-power transitions preserve the original completed quotient projections. -/
theorem finiteTransition_quotient {n m : ℕ} (h : n ≤ m) :
    (finiteTransition p R A h).comp (finiteQuotient p R A m) =
      finiteQuotient p R A n := by
  ext x
  rfl

/-- The p-power transitions preserve the original hull coefficients. -/
theorem finiteTransition_hull {n m : ℕ} (h : n ≤ m) :
    (finiteTransition p R A h).comp (finiteHullMap p R A m) =
      finiteHullMap p R A n := by
  ext x
  rfl

/-- The same transitions preserve the original residue. -/
theorem finiteTransition_residue {n m : ℕ} (h : n ≤ m) :
    (finiteResidue p R A E n).comp (finiteTransition p R A h) =
      finiteResidue p R A E m := by
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The original hull PD ideal maps into this exact finite residue kernel. -/
theorem hullIdeal_le_finiteIdeal (n : ℕ) :
    A.algebra.ideal.map (finiteHullMap p R A n) ≤ finiteIdeal p R A E n := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change finiteResidue p R A E n (finiteHullMap p R A n x) = 0
  rw [finiteResidue_hull]
  change E.equiv (Ideal.Quotient.mk A.algebra.ideal x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/-- Each literal finite ring has its displayed p-power nilpotence. -/
theorem finite_p_power (n : ℕ) : (p : FiniteRing p R A n) ^ (n + 1) = 0 := by
  change (Ideal.Quotient.mk (completedIdeal p R A ^ (n + 1)))
    ((p : Acris p R A) ^ (n + 1)) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [completedIdeal, Ideal.span_singleton_pow]
  exact Ideal.subset_span (Set.mem_singleton _)

end MathlibExt.RingTheory.SemiperfectCrystallineResidues
