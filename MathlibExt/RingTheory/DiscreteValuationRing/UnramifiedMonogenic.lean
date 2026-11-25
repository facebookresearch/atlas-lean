/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import MathlibExt.NumberTheory.HenselFactorization
public import MathlibExt.RingTheory.DiscreteValuationRing.Monogenic
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.IsAdjoinRoot

/-!
# Unramified DVR extensions are monogenic with separable reduced
# minimal polynomial

Let `A → B` be a finite torsion-free extension of discrete valuation rings
with `A` complete. Corollary 10.15 of ATLAS `NumberTheoryI` says that
`B / A` is unramified (separable residue-field extension of the same
degree) if and only if `B = A[α]` for some `α : B` whose minimal polynomial
over `A` reduces to a separable polynomial over the residue field of `A`.

The forward direction identifies the reduced minimal polynomial with the
residue minimal polynomial by the degree equality. The reverse direction
needs the reduced minimal polynomial to be irreducible: a coprime
factorization of it would lift by Hensel factorization
(`Polynomial.exists_monic_coprime_factorization_of_isAdicComplete`,
using completeness of `A`) to a factorization of the minimal polynomial
over `A`, which is irreducible since `A` is integrally closed. The v1
proof (`v1/Atlas/NumberTheoryI/code/Cor1015.lean`) instead derives this
irreducibility from a Hensel-lifting lemma that is left unproved there
(`hensel_lemma_III` in `v1/Atlas/NumberTheoryI/code/HenselFactorization.lean`),
so the argument below does not follow v1 at that step.

A conditional root-of-unity consequence is included, corresponding to
the v1 helper `cor_10_16_of_adjoin`: if `B = A[ζ]` for a primitive `n`th
root of unity with `n` coprime to the residue characteristic, then the
extension is unramified. The generation equality is an input hypothesis.
The full Corollary 10.16 concerns the integral closure in `K(ζ) / K` and
first proves this generation equality; that setup and proof are outside
this module's coverage.

## Main results

* Corollary 10.15: unramifiedness iff monogenic with separable reduced
  minimal polynomial: the Corollary 10.15 equivalence, with unramifiedness
  stated as separable residue-field extension plus equality of degrees.
* `IsDiscreteValuationRing.unramified_of_primitive_root_of_unity_of_coprime`:
  the conditional helper `cor_10_16_of_adjoin`: if `B = A[ζ]` for a primitive
  `n`th root of
  unity `ζ` with `n` coprime to the residue characteristic, then `B / A`
  is unramified in the above sense.
-/

@[expose] public section

open IsLocalRing Polynomial

namespace IsDiscreteValuationRing

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A B] [Module.Finite A B] [IsLocalHom (algebraMap A B)]
  [Module.IsTorsionFree A B] [IsAdicComplete (maximalIdeal A) A]

set_option linter.unusedSectionVars false in
/-- The residue of a generator over `A` generates the residue field: if
`B = A[α]` then `ResidueField B = ResidueField A[residue B α]`. -/
private theorem adjoin_residue_top_of_adjoin_top (α : B)
    (htop : Algebra.adjoin A ({α} : Set B) = ⊤) :
    Algebra.adjoin (ResidueField A) ({residue B α} : Set (ResidueField B)) =
      ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨b, rfl⟩ := residue_surjective (R := B) x
  have hb : b ∈ Algebra.adjoin A ({α} : Set B) := htop ▸ Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hb ⊢
  obtain ⟨p, hp⟩ := hb
  rw [← hp]
  show residue B (Polynomial.aeval α p) ∈ (Polynomial.aeval (residue B α)).range
  rw [Polynomial.map_aeval_eq_aeval_map (ψ := residue B) (φ := residue A) rfl]
  exact ⟨p.map (residue A), rfl⟩

set_option linter.unusedSectionVars false in
/-- If the reduced minimal polynomial of `α : B` is separable, then it is
irreducible: a factorization into coprime factors, normalized to monic
factors, would lift by Hensel factorization to a factorization of the
minimal polynomial over `A`, contradicting its irreducibility (as `A` is
integrally closed). -/
private theorem reduced_minpoly_irreducible (α : B)
    (hsep : ((minpoly A α).map (residue A)).Separable) :
    Irreducible ((minpoly A α).map (residue A)) := by
  have hirr : Irreducible (minpoly A α) :=
    (minpoly.prime_of_isIntegrallyClosed (IsIntegral.of_finite A α)).irreducible
  have hmonic : (minpoly A α).Monic :=
    minpoly.monic (IsIntegral.of_finite A α)
  have hbar_monic : ((minpoly A α).map (residue A)).Monic := hmonic.map _
  have hdeg_pos : 0 < ((minpoly A α).map (residue A)).natDegree := by
    rw [hmonic.natDegree_map]
    exact minpoly.natDegree_pos (IsIntegral.of_finite A α)
  have hnu : ¬ IsUnit ((minpoly A α).map (residue A)) := by
    intro hu
    have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  constructor
  · exact hnu
  · intro p q hpq
    by_cases hp0 : p = 0
    · exfalso
      rw [hp0, zero_mul] at hpq
      exact hbar_monic.ne_zero hpq
    by_cases hq0 : q = 0
    · exfalso
      rw [hq0, mul_zero] at hpq
      exact hbar_monic.ne_zero hpq
    have hcop : IsCoprime p q := by
      rw [hpq] at hsep
      exact hsep.isCoprime
    -- Normalize the factors to be monic.
    set a := p.leadingCoeff with ha
    set b := q.leadingCoeff with hb
    have ha0 : a ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp0
    have hb0 : b ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq0
    have hab : a * b = 1 := by
      have h := congrArg Polynomial.leadingCoeff hpq
      rw [Polynomial.leadingCoeff_mul, hbar_monic.leadingCoeff] at h
      exact h.symm
    set p' : (ResidueField A)[X] := C a⁻¹ * p with hp'
    set q' : (ResidueField A)[X] := C b⁻¹ * q with hq'
    have hp'_monic : p'.Monic := by
      rw [hp']
      exact Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
        (by rw [← ha, inv_mul_cancel₀ ha0])
    have hq'_monic : q'.Monic := by
      rw [hq']
      exact Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
        (by rw [← hb, inv_mul_cancel₀ hb0])
    have hprod : p' * q' = (minpoly A α).map (residue A) := by
      have hC : (C a⁻¹ : (ResidueField A)[X]) * C b⁻¹ = 1 := by
        rw [← C_mul, ← mul_inv, hab, inv_one, C_1]
      calc p' * q' = (C a⁻¹ * C b⁻¹) * (p * q) := by rw [hp', hq']; ring
        _ = p * q := by rw [hC, one_mul]
        _ = (minpoly A α).map (residue A) := hpq.symm
    have hcop' : IsCoprime p' q' := by
      have h1 : IsCoprime (C a⁻¹ : (ResidueField A)[X]) q := by
        refine ⟨C a, 0, ?_⟩
        rw [← C_mul, mul_inv_cancel₀ ha0, C_1, zero_mul, add_zero]
      have h2 : IsCoprime (C a⁻¹ : (ResidueField A)[X]) p :=
        ⟨C a, 0, by rw [← C_mul, mul_inv_cancel₀ ha0, C_1, zero_mul, add_zero]⟩
      have h3 : IsCoprime p' q :=
        (IsCoprime.mul_left_iff).mpr ⟨h1, hcop⟩
      have h4 : IsCoprime p' (C b⁻¹ : (ResidueField A)[X]) := by
        refine ⟨0, C b, ?_⟩
        rw [← C_mul, mul_inv_cancel₀ hb0, C_1, zero_mul, zero_add]
      have h5 : IsCoprime p' (q * C b⁻¹) := IsCoprime.mul_right h3 h4
      rwa [mul_comm q (C b⁻¹)] at h5
    -- Lift the monic coprime factorization to `A` by Hensel factorization.
    obtain ⟨g, h, hg_monic, hh_monic, hgh, hg_map, hh_map⟩ :=
      Polynomial.exists_monic_coprime_factorization_of_isAdicComplete
        (maximalIdeal A)
        (minpoly A α) hmonic p' q' hp'_monic hq'_monic hprod.symm hcop'
    rcases hirr.isUnit_or_isUnit hgh with hgu | hhu
    · left
      have hg1 : g = 1 := hg_monic.eq_one_of_isUnit hgu
      have hp'_1 : p' = 1 := by
        rw [← hg_map, hg1]
        exact Polynomial.map_one _
      have hpC : p = C a := by
        calc p = C a * p' := by
              rw [hp', ← mul_assoc, ← C_mul, mul_inv_cancel₀ ha0, C_1, one_mul]
          _ = C a * 1 := by rw [hp'_1]
          _ = C a := mul_one _
      rw [hpC]
      exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ha0)
    · right
      have hh1 : h = 1 := hh_monic.eq_one_of_isUnit hhu
      have hq'_1 : q' = 1 := by
        rw [← hh_map, hh1]
        exact Polynomial.map_one _
      have hqC : q = C b := by
        calc q = C b * q' := by
              rw [hq', ← mul_assoc, ← C_mul, mul_inv_cancel₀ hb0, C_1, one_mul]
          _ = C b * 1 := by rw [hq'_1]
          _ = C b := mul_one _
      rw [hqC]
      exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hb0)

set_option linter.unusedSectionVars false in
/-- Forward direction of Corollary 10.15: if the residue-field extension is
separable and the degrees agree, then the generator produced by monogenicity
has separable reduced minimal polynomial. -/
private theorem reduced_minpoly_separable_of_separable_residue (α : B)
    (hα : Algebra.adjoin A ({α} : Set B) = ⊤)
    (hsep : Algebra.IsSeparable (ResidueField A) (ResidueField B))
    (hdeg : Module.finrank A B =
      Module.finrank (ResidueField A) (ResidueField B)) :
    ((minpoly A α).map (residue A)).Separable := by
  have := hsep
  have hres : Algebra.adjoin (ResidueField A) ({residue B α} : Set _) = ⊤ :=
    adjoin_residue_top_of_adjoin_top α hα
  have heq : (minpoly A α).map (residue A) =
      minpoly (ResidueField A) (residue B α) := by
    have hmonic : (minpoly A α).Monic :=
      minpoly.monic (IsIntegral.of_finite A α)
    refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic (Algebra.IsIntegral.isIntegral _)) (hmonic.map _)
      (minpoly.dvd _ _ ?_) ?_
    · rw [← Polynomial.map_aeval_eq_aeval_map (ψ := residue B)
        (φ := residue A) rfl]
      simp [minpoly.aeval]
    · rw [hmonic.natDegree_map,
        ← (IsAdjoinRootMonic.mkOfAdjoinEqTop' hα).finrank, hdeg,
        (IsAdjoinRootMonic.mkOfAdjoinEqTop' hres).finrank]
  rw [heq]
  exact Algebra.IsSeparable.isSeparable _ _

/-- **Characterization of unramified extensions of a complete DVR.** Let $A$ and $B$ be
discrete valuation rings, with $A$ complete with respect to its maximal ideal, and let $B$
be an $A$-algebra via a local homomorphism $A \to B$, such that $B$ is finitely generated
and torsion-free as an $A$-module. Let $k_A$ and $k_B$ be the residue fields of $A$ and $B$.
Then the following are equivalent: (a) $k_B$ is separable over $k_A$ and the rank of $B$
as an $A$-module equals $[k_B : k_A]$; (b) there is $\alpha \in B$ with $B = A[\alpha]$ such
that the reduction modulo the maximal ideal of $A$ of the minimal polynomial of $\alpha$
over $A$ is separable over $k_A$.

Source: ATLAS NumberTheoryI, Corollary 10.15. -/
theorem unramified_iff_exists_monogenic_separable_reduced_minpoly :
    (Algebra.IsSeparable (ResidueField A) (ResidueField B) ∧
      Module.finrank A B = Module.finrank (ResidueField A) (ResidueField B)) ↔
    ∃ α : B, Algebra.adjoin A ({α} : Set B) = ⊤ ∧
      ((minpoly A α).map (residue A)).Separable := by
  constructor
  · rintro ⟨hsep, hdeg⟩
    have : Algebra.IsSeparable (ResidueField A) (ResidueField B) := hsep
    obtain ⟨α, hα⟩ :=
      exists_adjoin_eq_top_of_separable_residueField (A := A) (B := B)
    exact ⟨α, hα, reduced_minpoly_separable_of_separable_residue α hα hsep hdeg⟩
  · rintro ⟨α, hα, hsep_red⟩
    have hres : Algebra.adjoin (ResidueField A) ({residue B α} : Set _) = ⊤ :=
      adjoin_residue_top_of_adjoin_top α hα
    have hirr_red := reduced_minpoly_irreducible α hsep_red
    have hā_sep : IsSeparable (ResidueField A) (residue B α) :=
      hsep_red.of_dvd (minpoly.dvd _ _ (by
        rw [← Polynomial.map_aeval_eq_aeval_map (ψ := residue B)
          (φ := residue A) rfl]
        simp [minpoly.aeval]))
    have hres_sep : Algebra.IsSeparable (ResidueField A) (ResidueField B) := by
      have htop : separableClosure (ResidueField A) (ResidueField B) = ⊤ := by
        rw [← IntermediateField.toSubalgebra_inj,
          IntermediateField.top_toSubalgebra]
        have hle : Algebra.adjoin (ResidueField A) ({residue B α} : Set _) ≤
            (separableClosure (ResidueField A) (ResidueField B)).toSubalgebra :=
          Algebra.adjoin_le_iff.mpr (by
            intro x hx
            rw [Set.mem_singleton_iff] at hx
            rw [hx]
            exact mem_separableClosure_iff.mpr hā_sep)
        exact top_le_iff.mp (hres ▸ hle)
      exact (separableClosure.eq_top_iff _ _).mp htop
    have hfin : Module.finrank A B =
        Module.finrank (ResidueField A) (ResidueField B) := by
      have hmonic : (minpoly A α).Monic :=
        minpoly.monic (IsIntegral.of_finite A α)
      have hbar_monic : ((minpoly A α).map (residue A)).Monic := hmonic.map _
      have heq : (minpoly A α).map (residue A) =
          minpoly (ResidueField A) (residue B α) :=
        minpoly.eq_of_irreducible_of_monic hirr_red (by
          rw [← Polynomial.map_aeval_eq_aeval_map (ψ := residue B)
            (φ := residue A) rfl]
          simp [minpoly.aeval]) hbar_monic
      calc Module.finrank A B
          = (minpoly A α).natDegree :=
            (IsAdjoinRootMonic.mkOfAdjoinEqTop' hα).finrank
        _ = ((minpoly A α).map (residue A)).natDegree :=
            (hmonic.natDegree_map _).symm
        _ = (minpoly (ResidueField A) (residue B α)).natDegree := by rw [heq]
        _ = Module.finrank (ResidueField A) (ResidueField B) :=
            (IsAdjoinRootMonic.mkOfAdjoinEqTop' hres).finrank.symm
    exact ⟨hres_sep, hfin⟩

/-- **Adjoining a root of unity of order coprime to the residue characteristic is unramified.**
Let $A$ and $B$ be discrete valuation rings, with $A$ complete with respect to its maximal
ideal, and let $B$ be an $A$-algebra via a local homomorphism $A \to B$, such that $B$ is
finitely generated and torsion-free as an $A$-module. Let $k_A$ and $k_B$ be the residue fields
of $A$ and $B$. Let $n$ be a natural number coprime to the characteristic of $k_A$, and let
$\zeta \in B$ be a primitive $n$-th root of unity with $B = A[\zeta]$. Then $k_B$ is separable
over $k_A$ and the rank of $B$ as an $A$-module equals $[k_B : k_A]$.

Coprimality is meant literally, with $\gcd(n, 0) = n$, so when $k_A$ has characteristic $0$
the hypothesis forces $n = 1$.

Source: ATLAS NumberTheoryI, the helper `cor_10_16_of_adjoin` for Corollary 10.16; the
generation $B = A[\zeta]$ is assumed here rather than proved from the integral-closure setup. -/
theorem unramified_of_primitive_root_of_unity_of_coprime {n : ℕ} {ζ : B}
    (hprim : IsPrimitiveRoot ζ n)
    (hcoprime : Nat.Coprime n (ringChar (IsLocalRing.ResidueField A)))
    (hgen : Algebra.adjoin A ({ζ} : Set B) = ⊤) :
    Algebra.IsSeparable (ResidueField A) (ResidueField B) ∧
      Module.finrank A B =
        Module.finrank (ResidueField A) (ResidueField B) := by
  have hsep_red : ((minpoly A ζ).map (residue A)).Separable := by
    have hdvd : minpoly A ζ ∣ X ^ n - C 1 :=
      minpoly.isIntegrallyClosed_dvd (IsIntegral.of_finite A ζ) (by
        simp [Polynomial.aeval_X_pow, hprim.pow_eq_one])
    have hdvd_map : (minpoly A ζ).map (residue A) ∣
        (X ^ n - C 1 : (ResidueField A)[X]) := by
      have h := Polynomial.map_dvd (residue A) hdvd
      simpa using h
    apply Polynomial.Separable.of_dvd _ hdvd_map
    have hn : (n : ResidueField A) ≠ 0 := by
      intro h
      have hchar : ringChar (IsLocalRing.ResidueField A) ∣ n :=
        (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField A)
          (ringChar (IsLocalRing.ResidueField A)) n).mp h
      have h1 : ringChar (IsLocalRing.ResidueField A) = 1 :=
        hcoprime.symm.eq_one_of_dvd hchar
      have : CharP (IsLocalRing.ResidueField A) 1 :=
        h1 ▸ ringChar.charP (IsLocalRing.ResidueField A)
      exact @CharP.false_of_nontrivial_of_char_one
        (IsLocalRing.ResidueField A) _ _ _
    exact separable_X_pow_sub_C 1 hn one_ne_zero
  exact (unramified_iff_exists_monogenic_separable_reduced_minpoly
    (A := A) (B := B)).mpr
    ⟨ζ, hgen, hsep_red⟩

end IsDiscreteValuationRing
