/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_FormallySmooth_linearIndepOn_pow_of_linearIndepOn_id.lean`
and
`P2M/Sol/S_Algebra_FormallySmooth_linearIndepOn_pow_of_linearIndepOn_id.lean`
and
`Theorems/Thm_KaehlerDifferential_D_ne_zero_of_forall_pow_ne.lean`
and
`P2M/Sol/S_KaehlerDifferential_D_ne_zero_of_forall_pow_ne.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Etale.Field

@[expose] public section

open TensorProduct Polynomial IntermediateField
open scoped IntermediateField

namespace Algebra.FormallySmooth

private theorem kaehlerD_ne_zero_of_forall_pow_ne
    {k : Type*} [Field k] (p : ℕ) (hp : p.Prime) [ExpChar k p]
    (c : k) (hc : ∀ b : k, b ^ p ≠ c) :
    KaehlerDifferential.D (⊥ : Subfield k) k c ≠ 0 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hchark : CharP k p := by
    cases ‹ExpChar k p› with
    | zero => exact absurd hp Nat.not_prime_one
    | prime _ => assumption
  haveI := hchark
  set 𝒮 : Set (Set k) :=
    {F | (∃ F' : Subfield k, (F' : Set k) = F) ∧ (∀ y : k, y ^ p ∈ F) ∧ c ∉ F} with h𝒮
  set F₀ : Subfield k := (frobenius k p).fieldRange with hF₀
  have hF₀S : (F₀ : Set k) ∈ 𝒮 := by
    refine ⟨⟨F₀, rfl⟩, fun y => ⟨y, frobenius_def p y⟩, ?_⟩
    rintro ⟨b, hb⟩
    exact hc b (by rw [← hb, frobenius_def])
  have hchain : ∀ C ⊆ 𝒮, IsChain (fun x1 x2 => x1 ⊆ x2) C → C.Nonempty →
      ∃ ub ∈ 𝒮, ∀ s ∈ C, s ⊆ ub := by
    intro C hC hCc hCne
    let T : Set (Subfield k) := {F' | (F' : Set k) ∈ C}
    have hTne : T.Nonempty := by
      obtain ⟨s, hs⟩ := hCne
      obtain ⟨⟨F', rfl⟩, -, -⟩ := hC hs
      exact ⟨F', hs⟩
    have hTdir : DirectedOn (fun x1 x2 => x1 ≤ x2) T := by
      rintro F₁ h₁ F₂ h₂
      rcases hCc.total h₁ h₂ with h | h
      · exact ⟨F₂, h₂, SetLike.coe_subset_coe.mp h, le_rfl⟩
      · exact ⟨F₁, h₁, le_rfl, SetLike.coe_subset_coe.mp h⟩
    have hcoe : ((sSup T : Subfield k) : Set k) = ⋃ s ∈ T, (s : Set k) :=
      Subfield.coe_sSup_of_directedOn hTne hTdir
    refine ⟨(sSup T : Subfield k), ⟨⟨_, rfl⟩, ?_, ?_⟩, ?_⟩
    · intro y
      obtain ⟨F', hF'⟩ := hTne
      obtain ⟨-, hpow, -⟩ := hC hF'
      rw [hcoe]; exact Set.mem_biUnion hF' (hpow y)
    · intro hcm
      rw [hcoe] at hcm
      obtain ⟨F', hF', hcF'⟩ := Set.mem_iUnion₂.mp hcm
      exact (hC hF').2.2 hcF'
    · intro s hs
      obtain ⟨⟨F', rfl⟩, -, -⟩ := hC hs
      rw [hcoe]
      exact Set.subset_biUnion_of_mem (u := fun x : Subfield k => (x : Set k)) hs
  obtain ⟨Fset, -, hFmax⟩ := zorn_subset_nonempty 𝒮 hchain _ hF₀S
  obtain ⟨⟨F, rfl⟩, hFpow, hcF⟩ := hFmax.prop
  have hpF : ((p : ℕ) : F) = 0 :=
    (algebraMap F k).injective (by rw [map_natCast, map_zero, CharP.cast_eq_zero])
  have hpoly : ∀ y : k, (aeval y) (X ^ p - C (⟨y ^ p, hFpow y⟩ : F)) = 0 := by
    intro y; simp [sub_eq_zero]; rfl
  have hmonic : ∀ y : k, (X ^ p - C (⟨y ^ p, hFpow y⟩ : F)).Monic := fun y =>
    (monic_X_pow p).sub_of_left (by
      rw [degree_X_pow]
      exact lt_of_le_of_lt degree_C_le (by exact_mod_cast hp.pos))
  have hint : ∀ y : k, IsIntegral F y := fun y =>
    ⟨_, hmonic y, by rw [← aeval_def]; exact hpoly y⟩
  have hirr : ∀ y : k, y ∉ F → Irreducible (X ^ p - C (⟨y ^ p, hFpow y⟩ : F)) := by
    intro y hy
    rw [X_pow_sub_C_irreducible_iff_of_prime hp]
    intro b hb
    apply hy
    have hb' : ((b : F) : k) ^ p = y ^ p := by
      have := congrArg (fun z : F => (z : k)) hb; simpa using this
    rw [← frobenius_def, ← frobenius_def] at hb'
    rw [← frobenius_inj k p hb']
    exact b.2
  have hmin : ∀ y : k, y ∉ F → minpoly F y = X ^ p - C (⟨y ^ p, hFpow y⟩ : F) :=
    fun y hy => (minpoly.eq_of_irreducible_of_monic (hirr y hy) (hpoly y) (hmonic y)).symm
  have hdeg : ∀ y : k, y ∉ F → Module.finrank F F⟮y⟯ = p := by
    intro y hy
    rw [IntermediateField.adjoin.finrank (hint y), hmin y hy, natDegree_X_pow_sub_C]
  have htop : F⟮c⟯ = ⊤ := by
    apply top_unique
    intro a _
    by_cases ha : a ∈ F
    · exact (F⟮c⟯).algebraMap_mem ⟨a, ha⟩
    · have hca : c ∈ F⟮a⟯ := by
        by_contra hca
        have hmem : ((F⟮a⟯.toSubfield : Subfield k) : Set k) ∈ 𝒮 := by
          refine ⟨⟨_, rfl⟩, fun y => ?_, hca⟩
          exact (F⟮a⟯).algebraMap_mem ⟨y ^ p, hFpow y⟩
        have hle : (F : Set k) ⊆ ((F⟮a⟯.toSubfield : Subfield k) : Set k) :=
          fun y hy => (F⟮a⟯).algebraMap_mem ⟨y, hy⟩
        have heq := hFmax.eq_of_subset hmem hle
        have : a ∈ (F : Set k) := by rw [heq]; exact mem_adjoin_simple_self F a
        exact ha this
      haveI : FiniteDimensional F F⟮a⟯ := adjoin.finiteDimensional (hint a)
      have hle : F⟮c⟯ ≤ F⟮a⟯ := adjoin_simple_le_iff.mpr hca
      have heq : F⟮c⟯ = F⟮a⟯ :=
        eq_of_le_of_finrank_eq hle (by rw [hdeg c hcF, hdeg a ha])
      rw [heq]; exact mem_adjoin_simple_self F a
  have hDF : KaehlerDifferential.D F k c ≠ 0 := by
    intro h0
    have hall : ∀ x : k, KaehlerDifferential.D F k x = 0 := by
      intro x
      have hx : x ∈ (F⟮c⟯).toSubalgebra := by rw [htop]; exact Algebra.mem_top
      rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (hint c).isAlgebraic,
        Algebra.adjoin_singleton_eq_range_aeval] at hx
      obtain ⟨f, rfl⟩ := hx
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Derivation.map_aeval, h0, smul_zero]
    have hsub : Subsingleton Ω[k⁄F] := by
      have htop' := KaehlerDifferential.span_range_derivation F k
      have hbot : (⊤ : Submodule k Ω[k⁄F]) = ⊥ := by
        rw [← htop', Submodule.span_eq_bot]
        rintro _ ⟨x, rfl⟩; exact hall x
      refine ⟨fun a b => ?_⟩
      have ha : a ∈ (⊤ : Submodule k Ω[k⁄F]) := Submodule.mem_top
      have hb : b ∈ (⊤ : Submodule k Ω[k⁄F]) := Submodule.mem_top
      rw [hbot, Submodule.mem_bot] at ha hb
      rw [ha, hb]
    haveI : Algebra.FormallyUnramified F k := ⟨hsub⟩
    have hfr : Module.finrank F k = p := by
      rw [← IntermediateField.finrank_top', ← htop, hdeg c hcF]
    haveI : Module.Finite F k := Module.finite_of_finrank_pos (by rw [hfr]; exact hp.pos)
    haveI : Algebra.EssFiniteType F k := inferInstance
    haveI := Algebra.FormallyEtale.of_formallyUnramified_of_field F k
    have hsep : Algebra.IsSeparable F k := (Algebra.FormallyEtale.iff_isSeparable F k).mp ‹_›
    have hcsep : IsSeparable F c := Algebra.IsSeparable.isSeparable F c
    rw [IsSeparable, hmin c hcF, Polynomial.Separable] at hcsep
    have hder : derivative (X ^ p - C (⟨c ^ p, hFpow c⟩ : F)) = 0 := by
      rw [derivative_sub, derivative_X_pow, derivative_C, sub_zero, hpF, C_0, zero_mul]
    rw [hder, isCoprime_zero_right] at hcsep
    have h1 := natDegree_eq_zero_of_isUnit hcsep
    rw [natDegree_X_pow_sub_C] at h1
    exact hp.ne_zero h1
  letI : Algebra (⊥ : Subfield k) F := (Subfield.inclusion (bot_le)).toAlgebra
  haveI : IsScalarTower (⊥ : Subfield k) F k := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  intro h0
  apply hDF
  have := KaehlerDifferential.map_D (⊥ : Subfield k) F k k c
  rw [h0, map_zero, Algebra.algebraMap_self, RingHom.id_apply] at this
  exact this.symm

/-- If `K/k` is a formally smooth extension of fields of exponent
characteristic `p`, then raising to the `p`-th power preserves `k`-linear
independence of finite subsets of `K`. -/
public theorem linearIndepOn_pow_of_linearIndepOn_id
    {k K : Type*} [Field k] [Field K] [Algebra k K] [Algebra.FormallySmooth k K]
    (p : ℕ) (hp : p.Prime) [ExpChar k p]
    (s : Finset K) (hs : LinearIndepOn k _root_.id (s : Set K)) :
    LinearIndepOn k (· ^ p) (s : Set K) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hchark : CharP k p := by
    cases ‹ExpChar k p› with
    | zero => exact absurd hp Nat.not_prime_one
    | prime _ => assumption
  haveI := hchark
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  let k₀ : Subfield k := ⊥
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange k₀ k K) := by
    have hex := Algebra.H1Cotangent.exact_δ_mapBaseChange k₀ k K
    haveI : Subsingleton (Algebra.H1Cotangent k K) :=
      Algebra.FormallySmooth.subsingleton_h1Cotangent
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨y, rfl⟩ := (hex x).mp hx
    rw [Subsingleton.elim y 0, map_zero]
  let B := Module.Free.chooseBasis k (Ω[k⁄k₀])
  let BK := B.baseChange K
  induction s using Finset.strongInduction with
  | H s IH =>
    refine linearIndepOn_finset_iffₛ.mpr ?_
    intro g zg hg
    by_contra hne
    push Not at hne
    obtain ⟨x₀, hx₀, hgx₀⟩ := hne
    set c : K → k := fun x => (g x₀ - zg x₀)⁻¹ * (g x - zg x) with hc
    have hc₀ : c x₀ = 1 := by
      simp [hc, inv_mul_cancel₀ (sub_ne_zero.mpr hgx₀)]
    have hrel : ∑ x ∈ s, c x • x ^ p = 0 := by
      have h0 : ∑ x ∈ s, (g x - zg x) • x ^ p = 0 := by
        simp_rw [sub_smul]
        rw [Finset.sum_sub_distrib, sub_eq_zero]
        exact hg
      simp only [hc, mul_smul, ← Finset.smul_sum, h0, smul_zero]
    have hD : ∀ x ∈ s, KaehlerDifferential.D k₀ k (c x) = 0 := by
      set T : K ⊗[k] Ω[k⁄k₀] :=
        ∑ x ∈ s, (x ^ p) ⊗ₜ[k] KaehlerDifferential.D k₀ k (c x) with hT
      have hT0 : T = 0 := by
        apply hinj
        rw [map_zero, hT, map_sum]
        simp_rw [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]
        have hDrel := congrArg (KaehlerDifferential.D k₀ K) hrel
        rw [map_zero, map_sum] at hDrel
        rw [← hDrel]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Algebra.smul_def, Derivation.leibniz, Derivation.leibniz_pow,
          ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul, smul_zero, zero_add]
      have hcoord : ∀ j, ∑ x ∈ s, (B.repr (KaehlerDifferential.D k₀ k (c x)) j) • x ^ p = 0 := by
        intro j
        have := congrArg (fun t => BK.repr t j) hT0
        simp only [hT, map_sum, map_zero, Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_finsetSum,
          Finset.sum_apply, Module.Basis.baseChange_repr_tmul, BK] at this
        exact this
      have hsub : s.erase x₀ ⊂ s := Finset.erase_ssubset hx₀
      have hind' : LinearIndepOn k (· ^ p) ((s.erase x₀ : Finset K) : Set K) :=
        IH _ hsub (hs.mono (by
          intro y hy; exact Finset.mem_of_mem_erase (Finset.mem_coe.mp hy)))
      have hind'' := linearIndepOn_finset_iffₛ.mp hind'
      have hzero : ∀ j, ∀ x ∈ s, B.repr (KaehlerDifferential.D k₀ k (c x)) j = 0 := by
        intro j x hx
        by_cases hxx : x = x₀
        · subst hxx; rw [hc₀, Derivation.map_one_eq_zero, map_zero, Finsupp.zero_apply]
        · have h0 : B.repr (KaehlerDifferential.D k₀ k (c x₀)) j • x₀ ^ p = 0 := by
            rw [hc₀, Derivation.map_one_eq_zero, map_zero, Finsupp.zero_apply, zero_smul]
          have hsum : ∑ x ∈ s.erase x₀,
              B.repr (KaehlerDifferential.D k₀ k (c x)) j • x ^ p = 0 := by
            have h := Finset.add_sum_erase s
              (fun x => B.repr (KaehlerDifferential.D k₀ k (c x)) j • x ^ p) hx₀
            rw [hcoord j, h0, zero_add] at h
            exact h
          have := hind'' (fun x => B.repr (KaehlerDifferential.D k₀ k (c x)) j) 0
            (by simpa using hsum) x (Finset.mem_erase.mpr ⟨hxx, hx⟩)
          simpa using this
      intro x hx
      apply B.repr.injective
      rw [map_zero]
      ext j
      rw [hzero j x hx, Finsupp.zero_apply]
    have hroot : ∀ x ∈ s, ∃ b : k, b ^ p = c x := by
      intro x hx
      by_contra h
      push Not at h
      exact kaehlerD_ne_zero_of_forall_pow_ne p hp (c x) h (hD x hx)
    choose! b hb using hroot
    have hsum : (∑ x ∈ s, b x • x) ^ p = 0 := by
      rw [sum_pow_char, ← hrel]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Algebra.smul_def, Algebra.smul_def, mul_pow, ← map_pow, hb x hx]
    have hsum0 : ∑ x ∈ s, b x • x = 0 := pow_eq_zero_iff hp.ne_zero |>.mp hsum
    have hs' := linearIndepOn_finset_iffₛ.mp hs
    have hb0 : b x₀ = 0 := by
      simpa using hs' b 0 (by simpa using hsum0) x₀ hx₀
    have : c x₀ = 0 := by rw [← hb x₀ hx₀, hb0, zero_pow hp.ne_zero]
    rw [hc₀] at this
    exact one_ne_zero this

end Algebra.FormallySmooth
