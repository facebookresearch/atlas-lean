/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Totally ramified extensions of discrete valuation rings are Eisenstein

Let `A ⊆ B` be an extension of discrete valuation rings, finite and local,
with fraction fields `K ⊆ L`. An element `π ∈ B` generates `B` over `A`
with Eisenstein minimal polynomial if and only if the ramification index
of the maximal ideal of `B` over `A` equals the degree `[L : K]`, i.e. the
extension is totally ramified. This is Theorem 11.5 of ATLAS `NumberTheoryI`
(Sutherland, MIT 18.785, Lecture 11).

Source-to-API mapping (source name ↦ name used here):

* source `residue_aeval_eq_residue_const` ↦ private
  `IsDiscreteValuationRing.residue_aeval_eq_residue_const`;
* source `residueField_map_surj_of_adjoin_uniformizer` ↦ private
  `IsDiscreteValuationRing.residueField_map_surj_of_adjoin_uniformizer`;
* source `finrank_eq_one_of_algebraMap_surjective` ↦ private
  `finrank_eq_one_of_algebraMap_surjective`;
* source `subalgebra_eq_top_of_mod_maximal` ↦ private
  `IsDiscreteValuationRing.subalgebra_eq_top_of_mod_maximal`;
* source `uniformizer_powers_span_mod_maximal` ↦ private
  `IsDiscreteValuationRing.uniformizer_powers_span_mod_maximal`;
* source `totally_ramified_adjoin_uniformizer` ↦ private
  `IsDiscreteValuationRing.adjoin_uniformizer_of_ramificationIdx_eq_finrank`;
* source `totally_ramified_minpoly_coeff_mem` ↦ private
  `IsDiscreteValuationRing.minpoly_coeff_mem_maximalIdeal`;
* source `totally_ramified_coeff0_image_not_in_pow_succ` ↦ private
  `IsDiscreteValuationRing.coeff_zero_image_not_mem_pow_succ`;
* source `totally_ramified_minpoly_coeff0_notMem_sq` ↦ private
  `IsDiscreteValuationRing.minpoly_coeff_zero_not_mem_sq`;
* source `totally_ramified_minpoly_eisenstein` ↦ private
  `IsDiscreteValuationRing.minpoly_eisenstein_of_ramificationIdx_eq_finrank`;
* source `eisenstein_implies_totally_ramified` ↦
  `IsDiscreteValuationRing.ramificationIdx_eq_finrank_of_eisenstein_adjoin`;
* source `totally_ramified_implies_eisenstein_and_adjoin` ↦
  `IsDiscreteValuationRing.eisenstein_adjoin_of_ramificationIdx_eq_finrank`;
* source `totally_ramified_iff_eisenstein_adjoin` ↦
  `IsDiscreteValuationRing.ramificationIdx_eq_finrank_iff_eisenstein_adjoin`.

Two adaptations from the source: the source's `AKLB` fundamental identity
`[L : K] = e * f` is proved here from Mathlib's
`Ideal.sum_ramification_inertia_eq_finrank`, using that the maximal ideal
of `B` is the unique prime of `B` lying over the maximal ideal of `A`; and
the source's `IsAdicComplete`, residue-separability, and separability
hypotheses are dropped, since no step of the proof uses them. The source
states the ramification index with the `sSup` definition
(`Ideal.ramificationIdx'`); the public statements here use Mathlib's
current length-based `Ideal.ramificationIdx`, converted once via
`Ideal.ramificationIdx'_eq_ramificationIdx`.
-/

@[expose] public section

namespace IsDiscreteValuationRing

open Ideal Polynomial

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
  [FaithfulSMul A B]
variable {K L : Type*} [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
  [IsScalarTower A B L] [IsScalarTower A K L] [FiniteDimensional K L]

/-- A subalgebra of a finite module over a local ring is everything if it
meets every coset modulo the maximal ideal. This is Nakayama's lemma. -/
private theorem subalgebra_eq_top_of_mod_maximal {A B : Type*} [CommRing A]
    [IsLocalRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    (S : Subalgebra A B)
    (h : (⊤ : Submodule A B) ≤ S.toSubmodule ⊔
      (IsLocalRing.maximalIdeal A) • ⊤) :
    S = ⊤ := by
  have hIJ : IsLocalRing.maximalIdeal A ≤ jacobson (⊥ : Ideal A) := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
  have hle : (⊤ : Submodule A B) ≤ S.toSubmodule :=
    Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hIJ h
  rw [eq_top_iff]
  intro b _
  exact hle Submodule.mem_top

/-- Evaluating a polynomial at a uniformizer has the same residue as
evaluating at its constant term. -/
private theorem residue_aeval_eq_residue_const {A : Type*} [CommRing A]
    {B : Type*}
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    (π : B) (hπ_mem : π ∈ IsLocalRing.maximalIdeal B) (p : A[X]) :
    (IsLocalRing.residue B) (Polynomial.aeval π p) =
      (IsLocalRing.residue B) (algebraMap A B (p.coeff 0)) := by
  simp only [Polynomial.aeval_def]
  rw [Polynomial.hom_eval₂]
  conv_lhs => rw [show (IsLocalRing.residue B) π = 0 from
    Ideal.Quotient.eq_zero_iff_mem.mpr hπ_mem]
  rw [Polynomial.eval₂_at_zero]
  rfl

/-- If a uniformizer generates `B` over `A`, the residue-field map is
surjective. -/
private theorem residueField_map_surj_of_adjoin_uniformizer {A : Type*}
    [CommRing A]
    [IsLocalRing A] {B : Type*} [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] (π : B) (hπ : Irreducible π)
    (hadj : Algebra.adjoin A ({π} : Set B) = ⊤) :
    Function.Surjective (IsLocalRing.ResidueField.map (algebraMap A B)) := by
  intro b
  obtain ⟨b₀, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hb₀ : b₀ ∈ Algebra.adjoin A ({π} : Set B) := by rw [hadj]; trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hb₀
  obtain ⟨p, rfl⟩ := hb₀
  have hπ_mem : π ∈ IsLocalRing.maximalIdeal B := by
    rw [hπ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self π
  refine ⟨IsLocalRing.residue A (p.coeff 0), ?_⟩
  rw [IsLocalRing.ResidueField.map_residue]
  change (IsLocalRing.residue B) (algebraMap A B (p.coeff 0)) =
    (IsLocalRing.residue B) (Polynomial.aeval π p)
  exact (residue_aeval_eq_residue_const π hπ_mem p).symm

/-- A surjective algebra map between fields has finrank one. -/
private theorem finrank_eq_one_of_algebraMap_surjective {k l : Type*}
    [Field k] [Field l]
    [Algebra k l] (hsurj : Function.Surjective (algebraMap k l)) :
    Module.finrank k l = 1 := by
  have hbij : Function.Bijective (Algebra.ofId k l) :=
    ⟨RingHom.injective (algebraMap k l), hsurj⟩
  let e : k ≃ₐ[k] l := AlgEquiv.ofBijective (Algebra.ofId k l) hbij
  have h := LinearEquiv.finrank_eq e.symm.toLinearEquiv
  linarith [Module.finrank_self k]

set_option linter.style.haveILetI false in
omit [FiniteDimensional K L] in
/-- The fundamental identity `e * f = [L : K]` for an extension of
discrete valuation rings, with `f` the residue-field degree. -/
private theorem finrank_eq_ramificationIdx_mul_finrank_residueField :
    Module.finrank K L = (IsLocalRing.maximalIdeal B).ramificationIdx A *
      Module.finrank (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField B) := by
  have hfin : Module.finrank K L = Module.finrank A B :=
    IsFractionRing.finrank_eq A K B L
  have hflat : Module.Flat A B := by
    infer_instance
  haveI : Fintype ((IsLocalRing.maximalIdeal A).primesOver B) :=
    (Algebra.QuasiFinite.finite_primesOver (IsLocalRing.maximalIdeal A)).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank
    (IsLocalRing.maximalIdeal A) B
  rw [hfin, ← hsum]
  have hmem : IsLocalRing.maximalIdeal B ∈
      (IsLocalRing.maximalIdeal A).primesOver B :=
    ⟨(IsLocalRing.maximalIdeal.isMaximal B).isPrime, inferInstance⟩
  have h0 : ∀ q : (IsLocalRing.maximalIdeal A).primesOver B, q ∈ Finset.univ →
      q ≠ ⟨IsLocalRing.maximalIdeal B, hmem⟩ →
      (q : Ideal B).ramificationIdx A * (q : Ideal B).inertiaDeg A = 0 := by
    intro q _ hq
    exfalso
    apply hq
    apply Subtype.ext
    exact IsLocalRing.eq_maximalIdeal (Ideal.primesOver.isMaximal q)
  rw [Finset.sum_eq_single_of_mem ⟨IsLocalRing.maximalIdeal B, hmem⟩
    (Finset.mem_univ _) h0]
  change (IsLocalRing.maximalIdeal B).ramificationIdx A *
      (IsLocalRing.maximalIdeal B).inertiaDeg A = _
  rw [Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal A)
    (IsLocalRing.maximalIdeal B)]
  rfl

/-- The two definitions of the ramification index agree for the maximal
ideals of an extension of discrete valuation rings. -/
private theorem ramificationIdx'_eq_ramificationIdx_of_dvr :
    (IsLocalRing.maximalIdeal A).ramificationIdx' (IsLocalRing.maximalIdeal B) =
      (IsLocalRing.maximalIdeal B).ramificationIdx A :=
  Ideal.ramificationIdx'_eq_ramificationIdx _ _
    (IsDiscreteValuationRing.not_a_field A)

/-- If the ramification index equals the degree, every element of `B`
is congruent modulo the maximal ideal of `A` to an `A`-polynomial in a
uniformizer. -/
private theorem uniformizer_powers_span_mod_maximal (π : B) (hπ : Irreducible π)
    (htotram : (IsLocalRing.maximalIdeal B).ramificationIdx A =
      Module.finrank K L) :
    (⊤ : Submodule A B) ≤ (Algebra.adjoin A ({π} : Set B)).toSubmodule ⊔
      (IsLocalRing.maximalIdeal A) • ⊤ := by
  have htotram' : (IsLocalRing.maximalIdeal A).ramificationIdx'
      (IsLocalRing.maximalIdeal B) = Module.finrank K L := by
    rw [ramificationIdx'_eq_ramificationIdx_of_dvr, htotram]
  set S := Algebra.adjoin A ({π} : Set B) with hS_def
  set n := Module.finrank K L with hn_def
  set e := (IsLocalRing.maximalIdeal A).ramificationIdx'
      (IsLocalRing.maximalIdeal B)
    with he_def
  set f := Module.finrank (IsLocalRing.ResidueField A)
    (IsLocalRing.ResidueField B) with hf_def
  have he_eq_n : e = n := htotram'
  have hefn : n = e * f := by
    rw [hn_def, he_def, hf_def,
      finrank_eq_ramificationIdx_mul_finrank_residueField (A := A) (B := B)
        (K := K) (L := L),
      ← ramificationIdx'_eq_ramificationIdx_of_dvr]
  have hf1 : f = 1 := by
    have hne : e ≠ 0 := by
      intro h
      rw [h] at he_eq_n
      exact absurd he_eq_n.symm (Module.finrank_pos (R := K) (M := L)).ne'
    have hfe : e * f = e * 1 := by rw [mul_one]; linarith
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) hfe
  have hres_surj : Function.Surjective
      (algebraMap (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField B)) := by
    have htop : (⊥ : Subalgebra (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField B)) = ⊤ :=
      Subalgebra.bot_eq_top_of_finrank_eq_one hf1
    intro x
    have hx : x ∈ (⊥ : Subalgebra (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField B)) := by
      rw [htop]
      exact Algebra.mem_top
    obtain ⟨a, ha⟩ := (Algebra.mem_bot (R := IsLocalRing.ResidueField A)
      (A := IsLocalRing.ResidueField B)).mp hx
    exact ⟨a, ha⟩
  have hlift : ∀ b : B, ∃ a : A,
      b - algebraMap A B a ∈ IsLocalRing.maximalIdeal B := by
    intro b
    obtain ⟨abar, habar⟩ := hres_surj (IsLocalRing.residue B b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective abar
    exact ⟨a, (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      (show (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B))
          (algebraMap A B a) =
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B)) b from by
        change (IsLocalRing.residue B) (algebraMap A B a) =
          (IsLocalRing.residue B) b
        rw [← IsLocalRing.ResidueField.map_residue (algebraMap A B) a]
        change (algebraMap (IsLocalRing.ResidueField A)
            (IsLocalRing.ResidueField B))
            ((IsLocalRing.residue A) a) = (IsLocalRing.residue B) b
        exact habar).symm⟩
  have hπ_span : IsLocalRing.maximalIdeal B = Ideal.span {π} :=
    hπ.maximalIdeal_eq
  have span_pow_eq : ∀ k : ℕ,
      (IsLocalRing.maximalIdeal B) ^ k = Ideal.span {π ^ k} := by
    intro k
    rw [hπ_span, Ideal.span_singleton_pow]
  have hind_step : ∀ k : ℕ,
      (((IsLocalRing.maximalIdeal B) ^ k).restrictScalars A : Submodule A B) ≤
        S.toSubmodule ⊔
          ((IsLocalRing.maximalIdeal B) ^ (k + 1)).restrictScalars A := by
    intro k m hm
    simp only [Submodule.restrictScalars_mem] at hm
    rw [span_pow_eq k, Ideal.mem_span_singleton'] at hm
    obtain ⟨c, hc⟩ := hm
    obtain ⟨a, ha⟩ := hlift c
    have hmdecomp : m =
        algebraMap A B a * π ^ k + (c - algebraMap A B a) * π ^ k := by
      rw [← add_mul, add_sub_cancel, hc]
    rw [hmdecomp]
    apply Submodule.add_mem_sup
    · exact Subalgebra.mul_mem S (S.algebraMap_mem a)
        (Subalgebra.pow_mem S (Algebra.subset_adjoin (Set.mem_singleton π)) k)
    · show (c - algebraMap A B a) * π ^ k ∈
        ((IsLocalRing.maximalIdeal B) ^ (k + 1)).restrictScalars A
      simp only [Submodule.restrictScalars_mem]
      have hd : c - algebraMap A B a ∈ IsLocalRing.maximalIdeal B := ha
      have hpk : π ^ k ∈ (IsLocalRing.maximalIdeal B) ^ k := by
        rw [span_pow_eq k]
        exact Ideal.mem_span_singleton_self _
      rw [pow_succ]
      exact mul_comm (c - algebraMap A B a) (π ^ k) ▸ Ideal.mul_mem_mul hpk hd
  have hiter : ∀ b : B,
      b ∈ S.toSubmodule ⊔
        ((IsLocalRing.maximalIdeal B) ^ n).restrictScalars A := by
    intro b
    suffices h : ∀ k : ℕ, b ∈ S.toSubmodule ⊔
        ((IsLocalRing.maximalIdeal B) ^ k).restrictScalars A from h n
    intro k
    induction k with
    | zero =>
      have : b ∈ ((IsLocalRing.maximalIdeal B) ^ 0).restrictScalars A := by simp
      exact Submodule.mem_sup_right this
    | succ k ih =>
      have hle : S.toSubmodule ⊔
          ((IsLocalRing.maximalIdeal B) ^ k).restrictScalars A ≤
          S.toSubmodule ⊔
            ((IsLocalRing.maximalIdeal B) ^ (k + 1)).restrictScalars A :=
        (sup_le_sup_left (hind_step k) S.toSubmodule).trans
          (by rw [← sup_assoc, sup_idem])
      exact hle ih
  have hmap_eq : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      (IsLocalRing.maximalIdeal B) ^ e := by
    set I := Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) with hI_def
    have hinj : Function.Injective (algebraMap A B) :=
      FaithfulSMul.algebraMap_injective A B
    have hIne : I ≠ ⊥ := by
      intro h
      have : IsLocalRing.maximalIdeal A = ⊥ := by
        rw [Ideal.map_eq_bot_iff_le_ker] at h
        have hker : RingHom.ker (algebraMap A B) = ⊥ :=
          (RingHom.injective_iff_ker_eq_bot _).mp hinj
        rw [hker] at h
        exact le_bot_iff.mp h
      exact IsDiscreteValuationRing.not_a_field A this
    obtain ⟨m, hm⟩ := exists_maximalIdeal_pow_eq_of_principal B
      (IsPrincipalIdealRing.principal _) I hIne
    have hgt : ¬(I ≤ (IsLocalRing.maximalIdeal B) ^ (m + 1)) := by
      intro hle
      have hle' : (IsLocalRing.maximalIdeal B) ^ m ≤
          (IsLocalRing.maximalIdeal B) ^ (m + 1) :=
        hm ▸ hle
      have : (IsLocalRing.maximalIdeal B : Ideal B) ^ m = ⊥ := by
        have key : ((IsLocalRing.maximalIdeal B) ^ m : Ideal B) ≤
            IsLocalRing.maximalIdeal B •
              ((IsLocalRing.maximalIdeal B) ^ m : Ideal B) := by
          calc ((IsLocalRing.maximalIdeal B) ^ m : Ideal B)
              ≤ (IsLocalRing.maximalIdeal B) ^ (m + 1) := hle'
            _ = (IsLocalRing.maximalIdeal B) ^ m *
              IsLocalRing.maximalIdeal B := pow_succ _ m
            _ = IsLocalRing.maximalIdeal B *
              (IsLocalRing.maximalIdeal B) ^ m := mul_comm _ _
            _ = IsLocalRing.maximalIdeal B • (IsLocalRing.maximalIdeal B) ^ m :=
                (Ideal.smul_eq_mul _ _).symm
        exact Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
          (IsLocalRing.maximalIdeal B)
          ((IsLocalRing.maximalIdeal B) ^ m : Ideal B)
          (IsNoetherian.noetherian _) key
          (by rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top])
      exact hIne (hm.trans this)
    have hme : m = e := by
      have h1 : I ≤ (IsLocalRing.maximalIdeal B) ^ m := hm ▸ le_refl _
      exact (Ideal.ramificationIdx'_spec h1 hgt).symm
    rw [← hme, hm]
  have hpow_le_smul : ((IsLocalRing.maximalIdeal B) ^ n).restrictScalars A ≤
      (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A B) := by
    rw [Ideal.smul_top_eq_map, ← he_eq_n, hmap_eq]
  intro b _
  have hb := hiter b
  exact (sup_le_sup_left hpow_le_smul S.toSubmodule) hb

/-- If the ramification index equals the degree, a uniformizer generates
`B` over `A`. -/
private theorem adjoin_uniformizer_of_ramificationIdx_eq_finrank (π : B)
    (hπ : Irreducible π)
    (htotram : (IsLocalRing.maximalIdeal B).ramificationIdx A =
      Module.finrank K L) :
    Algebra.adjoin A ({π} : Set B) = ⊤ :=
  subalgebra_eq_top_of_mod_maximal _
    (uniformizer_powers_span_mod_maximal π hπ htotram)

omit [IsFractionRing B L] in
/-- If the ramification index equals the degree, all non-leading
coefficients of the minimal polynomial of a uniformizer lie in the
maximal ideal of `A`. -/
private theorem minpoly_coeff_mem_maximalIdeal (π : B) (_hπ : Irreducible π)
    (_htotram : (IsLocalRing.maximalIdeal B).ramificationIdx A =
      Module.finrank K L)
    {n : ℕ} (_hn : n < (minpoly A π).natDegree) :
    (minpoly A π).coeff n ∈ IsLocalRing.maximalIdeal A := by
  have htotram' : (IsLocalRing.maximalIdeal A).ramificationIdx'
      (IsLocalRing.maximalIdeal B) = Module.finrank K L := by
    rw [ramificationIdx'_eq_ramificationIdx_of_dvr, _htotram]
  set f := minpoly A π with hf_def
  set 𝔭 := IsLocalRing.maximalIdeal A with h𝔭_def
  set 𝔪 := IsLocalRing.maximalIdeal B with h𝔪_def
  set d := f.natDegree with hd_def
  set e := 𝔭.ramificationIdx' 𝔪 with he_def
  have hπ_int : IsIntegral A π := IsIntegral.of_finite A π
  have heval : ∑ i ∈ Finset.range (d + 1),
      (algebraMap A B) (f.coeff i) * π ^ i = 0 := by
    have h := minpoly.aeval A π
    rw [Polynomial.aeval_eq_sum_range] at h
    simp only [Algebra.smul_def] at h
    exact h
  have hπ_span : 𝔪 = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp _hπ
  have hπ_mem : π ∈ 𝔪 := hπ_span ▸ Ideal.mem_span_singleton_self π
  have hram : Ideal.map (algebraMap A B) 𝔭 ≤ 𝔪 ^ e :=
    Ideal.le_pow_ramificationIdx'
  have hde : d ≤ e := by
    rw [htotram']
    calc d = ((minpoly A π).map (algebraMap A K)).natDegree := by
            rw [(minpoly.monic hπ_int).natDegree_map]
      _ = (minpoly K (algebraMap B L π)).natDegree := by
            rw [minpoly.isIntegrallyClosed_eq_field_fractions K L hπ_int]
      _ ≤ Module.finrank K L := minpoly.natDegree_le (algebraMap B L π)
  suffices h_strong : ∀ k, k < d → f.coeff k ∈ 𝔭 by exact h_strong n _hn
  intro k hk
  induction k using Nat.strongRecOn with
  | _ k ih =>
  have hk_mem : k ∈ Finset.range (d + 1) := Finset.mem_range.mpr (by omega)
  have heval' := heval
  rw [← Finset.add_sum_erase _ _ hk_mem] at heval'
  have heq := eq_neg_of_add_eq_zero_left heval'
  have h_prod : (algebraMap A B) (f.coeff k) * π ^ k ∈ 𝔪 ^ (k + 1) := by
    rw [heq]
    apply Submodule.neg_mem
    apply Ideal.sum_mem
    intro i hi
    rw [Finset.mem_erase] at hi
    obtain ⟨hne, hi_range⟩ := hi
    rw [Finset.mem_range] at hi_range
    by_cases hlt : i < k
    · have hcoeff_mem : f.coeff i ∈ 𝔭 := ih i hlt (by omega)
      have hprod : (algebraMap A B) (f.coeff i) * π ^ i ∈ 𝔪 ^ (e + i) := by
        rw [pow_add]
        exact Ideal.mul_mem_mul (hram (Ideal.mem_map_of_mem _ hcoeff_mem))
          (Ideal.pow_mem_pow hπ_mem i)
      exact Ideal.pow_le_pow_right (by omega) hprod
    · have hprod : (algebraMap A B) (f.coeff i) * π ^ i ∈ 𝔪 ^ i :=
        Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hπ_mem i)
      exact Ideal.pow_le_pow_right (by omega) hprod
  have h_in_𝔪 : (algebraMap A B) (f.coeff k) ∈ 𝔪 := by
    rw [hπ_span, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h_prod
    rw [hπ_span, Ideal.mem_span_singleton']
    obtain ⟨c, hc⟩ := h_prod
    refine ⟨c, ?_⟩
    have hcan : c * π * π ^ k = (algebraMap A B) (f.coeff k) * π ^ k := by
      rw [← hc]
      ring
    exact mul_right_cancel₀ (pow_ne_zero k _hπ.ne_zero) hcan
  rwa [IsLocalRing.mem_maximalIdeal, ← map_mem_nonunits_iff (algebraMap A B),
    ← IsLocalRing.mem_maximalIdeal]

omit [IsFractionRing B L] in
/-- If the ramification index equals the degree, the image of the
constant term of the minimal polynomial of a uniformizer lies outside
the `(n + 1)`-st power of the maximal ideal of `B`, where `n = [L : K]`. -/
private theorem coeff_zero_image_not_mem_pow_succ (π : B) (_hπ : Irreducible π)
    (_htotram : (IsLocalRing.maximalIdeal B).ramificationIdx A =
      Module.finrank K L) :
    algebraMap A B ((minpoly A π).coeff 0) ∉
      (IsLocalRing.maximalIdeal B) ^ (Module.finrank K L + 1) := by
  have htotram' : (IsLocalRing.maximalIdeal A).ramificationIdx'
      (IsLocalRing.maximalIdeal B) = Module.finrank K L := by
    rw [ramificationIdx'_eq_ramificationIdx_of_dvr, _htotram]
  set f := minpoly A π with hf_def
  set 𝔭 := IsLocalRing.maximalIdeal A with h𝔭_def
  set 𝔮 := IsLocalRing.maximalIdeal B with h𝔮_def
  set n := Module.finrank K L with hn_def
  set d := f.natDegree with hd_def
  have hπ_int : IsIntegral A π := IsIntegral.of_finite A π
  have heval : ∑ i ∈ Finset.range (d + 1),
      (algebraMap A B) (f.coeff i) * π ^ i = 0 := by
    have h := minpoly.aeval A π
    rw [Polynomial.aeval_eq_sum_range] at h
    simp only [Algebra.smul_def] at h
    exact h
  have hπ_span : 𝔮 = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp _hπ
  have hπ_mem : π ∈ 𝔮 := hπ_span ▸ Ideal.mem_span_singleton_self π
  have hram : Ideal.map (algebraMap A B) 𝔭 ≤ 𝔮 ^ n := by
    have h := @Ideal.le_pow_ramificationIdx' A _ B _ _ 𝔭 𝔮
    rwa [htotram'] at h
  have hde : d ≤ n := by
    calc d = ((minpoly A π).map (algebraMap A K)).natDegree := by
            rw [(minpoly.monic hπ_int).natDegree_map]
      _ = (minpoly K (algebraMap B L π)).natDegree := by
            rw [minpoly.isIntegrallyClosed_eq_field_fractions K L hπ_int]
      _ ≤ Module.finrank K L := minpoly.natDegree_le (algebraMap B L π)
  have hfmonic : f.Monic := minpoly.monic hπ_int
  have hcoeff_d : f.coeff d = 1 := hfmonic.leadingCoeff
  intro ha₀_mem
  have hπd_not : π ^ d ∉ 𝔮 ^ (d + 1) := by
    rw [hπ_span, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨c, hc⟩
    have hπd_ne : π ^ d ≠ 0 := pow_ne_zero d _hπ.ne_zero
    have h0 : π ^ d = π ^ d * (π * c) := by
      have h2 : π ^ d * (π * c) = π ^ (d + 1) * c := by ring
      rw [h2, ← hc]
    have h1 : π ^ d * 1 = π ^ d * (π * c) := by
      rw [mul_one]
      exact h0
    have hmul : π * c = 1 := (mul_left_cancel₀ hπd_ne h1).symm
    exact _hπ.not_isUnit ⟨⟨π, c, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩
  apply hπd_not
  have hd_mem : d ∈ Finset.range (d + 1) := Finset.mem_range.mpr (by omega)
  rw [← Finset.add_sum_erase _ _ hd_mem] at heval
  rw [show (algebraMap A B) (f.coeff d) * π ^ d = π ^ d from by
    rw [hcoeff_d, map_one, one_mul]] at heval
  have hπd_eq : π ^ d = -(∑ x ∈ (Finset.range (d + 1)).erase d,
      (algebraMap A B) (f.coeff x) * π ^ x) :=
    eq_neg_of_add_eq_zero_left heval
  rw [hπd_eq]
  apply Submodule.neg_mem
  apply Ideal.sum_mem
  intro i hi
  rw [Finset.mem_erase] at hi
  obtain ⟨hne, hi_range⟩ := hi
  rw [Finset.mem_range] at hi_range
  have hi_lt_d : i < d := by omega
  have hcoeff_mem : f.coeff i ∈ 𝔭 :=
    minpoly_coeff_mem_maximalIdeal π _hπ _htotram hi_lt_d
  have himage_mem : (algebraMap A B) (f.coeff i) ∈ 𝔮 ^ n :=
    hram (Ideal.mem_map_of_mem _ hcoeff_mem)
  by_cases hi0 : i = 0
  · subst hi0
    simp only [pow_zero, mul_one]
    exact Ideal.pow_le_pow_right (by omega) ha₀_mem
  · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
    have hprod : (algebraMap A B) (f.coeff i) * π ^ i ∈ 𝔮 ^ (n + i) := by
      rw [pow_add]
      exact Ideal.mul_mem_mul himage_mem (Ideal.pow_mem_pow hπ_mem i)
    exact Ideal.pow_le_pow_right (by omega : d + 1 ≤ n + i) hprod

omit [IsFractionRing B L] in
/-- If the ramification index equals the degree, the constant term of
the minimal polynomial of a uniformizer lies outside the square of the
maximal ideal of `A`. -/
private theorem minpoly_coeff_zero_not_mem_sq (π : B) (_hπ : Irreducible π)
    (_htotram : (IsLocalRing.maximalIdeal B).ramificationIdx A =
      Module.finrank K L) :
    (minpoly A π).coeff 0 ∉ (IsLocalRing.maximalIdeal A) ^ 2 := by
  set 𝔭 := IsLocalRing.maximalIdeal A with h𝔭_def
  set 𝔮 := IsLocalRing.maximalIdeal B with h𝔮_def
  set n := Module.finrank K L with hn_def
  have hval := coeff_zero_image_not_mem_pow_succ π _hπ _htotram
  intro ha₀_sq
  apply hval
  have h1 : algebraMap A B ((minpoly A π).coeff 0) ∈
      Ideal.map (algebraMap A B) (𝔭 ^ 2) :=
    Ideal.mem_map_of_mem _ ha₀_sq
  rw [Ideal.map_pow] at h1
  have hle_ram : Ideal.map (algebraMap A B) 𝔭 ≤ 𝔮 ^ 𝔭.ramificationIdx' 𝔮 :=
    Ideal.le_pow_ramificationIdx'
  have htotram' : (IsLocalRing.maximalIdeal A).ramificationIdx'
      (IsLocalRing.maximalIdeal B) = Module.finrank K L := by
    rw [ramificationIdx'_eq_ramificationIdx_of_dvr, _htotram]
  rw [htotram'] at hle_ram
  have h2 : (Ideal.map (algebraMap A B) 𝔭) ^ 2 ≤ (𝔮 ^ n) ^ 2 :=
    Ideal.pow_right_mono hle_ram 2
  rw [← pow_mul, mul_comm] at h2
  have hn_pos : 0 < n := Module.finrank_pos
  have h3 : 𝔮 ^ (2 * n) ≤ 𝔮 ^ (n + 1) := by
    apply Ideal.pow_le_pow_right
    omega
  exact h3 (h2 h1)

omit [IsFractionRing B L] in
/-- If the ramification index equals the degree, the minimal polynomial
of a uniformizer is Eisenstein at the maximal ideal of `A`. -/
private theorem minpoly_eisenstein_of_ramificationIdx_eq_finrank
    (π : B) (hπ : Irreducible π)
    (htotram : (IsLocalRing.maximalIdeal B).ramificationIdx A =
      Module.finrank K L) :
    (minpoly A π).IsEisensteinAt (IsLocalRing.maximalIdeal A) := by
  have hπ_int : IsIntegral A π := IsIntegral.of_finite A π
  exact (minpoly.monic hπ_int).isEisensteinAt_of_mem_of_notMem
    (IsLocalRing.maximalIdeal.isMaximal A).ne_top
    (fun hn => minpoly_coeff_mem_maximalIdeal π hπ htotram hn)
    (minpoly_coeff_zero_not_mem_sq π hπ htotram)

omit [FiniteDimensional K L] in
/-- The Eisenstein direction: if a uniformizer generates `B` over `A`
with Eisenstein minimal polynomial, then the ramification index equals
the degree. -/
theorem ramificationIdx_eq_finrank_of_eisenstein_adjoin (π : B)
    (hπ : Irreducible π)
    (hadj : Algebra.adjoin A ({π} : Set B) = ⊤)
    (_heis : (minpoly A π).IsEisensteinAt (IsLocalRing.maximalIdeal A)) :
    (IsLocalRing.maximalIdeal B).ramificationIdx A = Module.finrank K L := by
  have hsurj : Function.Surjective
      (IsLocalRing.ResidueField.map (algebraMap A B)) :=
    residueField_map_surj_of_adjoin_uniformizer π hπ hadj
  have hsurj' : Function.Surjective
      (algebraMap (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField B)) := by
    intro y
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective (R := B) y
    obtain ⟨a, ha⟩ := hsurj (IsLocalRing.residue B b)
    obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective (R := A) a
    refine ⟨IsLocalRing.residue A a₀, ?_⟩
    rw [IsLocalRing.ResidueField.algebraMap_residue,
      ← IsLocalRing.ResidueField.map_residue]
    exact ha
  have hf1 : Module.finrank (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField B) = 1 :=
    finrank_eq_one_of_algebraMap_surjective hsurj'
  have hfund : Module.finrank K L =
      (IsLocalRing.maximalIdeal B).ramificationIdx A *
        Module.finrank (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField B) :=
    finrank_eq_ramificationIdx_mul_finrank_residueField
  rw [hf1, mul_one] at hfund
  exact hfund.symm

/-- The totally-ramified direction: if the ramification index equals
the degree, then a uniformizer generates `B` over `A` with Eisenstein
minimal polynomial. -/
theorem eisenstein_adjoin_of_ramificationIdx_eq_finrank (π : B)
    (hπ : Irreducible π)
    (htotram : (IsLocalRing.maximalIdeal B).ramificationIdx A =
      Module.finrank K L) :
    Algebra.adjoin A ({π} : Set B) = ⊤ ∧
      (minpoly A π).IsEisensteinAt (IsLocalRing.maximalIdeal A) :=
  ⟨adjoin_uniformizer_of_ramificationIdx_eq_finrank π hπ htotram,
    minpoly_eisenstein_of_ramificationIdx_eq_finrank π hπ htotram⟩

/-- **Theorem 11.5.** Let `A ⊆ B` be an extension of discrete valuation
rings, finite and local, with fraction fields `K ⊆ L`. For a uniformizer
`π` of `B`, the extension is totally ramified, in the sense that the
ramification index equals `[L : K]`, if and only if `π` generates `B`
over `A` and its minimal polynomial is Eisenstein at the maximal ideal
of `A`. -/
theorem ramificationIdx_eq_finrank_iff_eisenstein_adjoin (π : B)
    (hπ : Irreducible π) :
    (IsLocalRing.maximalIdeal B).ramificationIdx A = Module.finrank K L ↔
      Algebra.adjoin A ({π} : Set B) = ⊤ ∧
        (minpoly A π).IsEisensteinAt (IsLocalRing.maximalIdeal A) :=
  ⟨eisenstein_adjoin_of_ramificationIdx_eq_finrank π hπ,
    fun ⟨hadj, heis⟩ =>
      ramificationIdx_eq_finrank_of_eisenstein_adjoin π hπ hadj heis⟩

end IsDiscreteValuationRing
