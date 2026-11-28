/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from:

`Theorems/Thm_KaehlerDifferential_D_ne_zero_of_forall_pow_ne.lean` and
`P2M/Sol/S_KaehlerDifferential_D_ne_zero_of_forall_pow_ne.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Kaehler.Polynomial

@[expose] public section

open Polynomial IntermediateField

/-!
# Kähler differentials of a non-`p`-th power

For a prime `p` and a field `k` of exponential characteristic `p`, an element of
`k` that is not a `p`-th power has nonzero differential in `Ω[k⁄⊥]`, the Kähler
differentials of `k` over its prime subfield `⊥`.
-/

namespace KaehlerDifferential

/-- **Non-$p$-th powers have nonzero differential.** Let $p$ be a prime and let $k$ be a
field of exponential characteristic $p$, so that $k$ has characteristic $p$. If $c \in k$ is
not a $p$-th power in $k$, then $dc \neq 0$ in $\Omega_{k/\mathbb{F}_p}$, the Kähler
differentials of $k$ over its prime subfield $\mathbb{F}_p$. -/
public theorem D_ne_zero_of_forall_pow_ne
    {k : Type*} [Field k] (p : ℕ) (hp : p.Prime) [ExpChar k p]
    (c : k) (hc : ∀ b : k, b ^ p ≠ c) :
    KaehlerDifferential.D (⊥ : Subfield k) k c ≠ 0 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : CharP k p := (expChar_prime_iff k hp).mp ‹_›
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
    (monic_X_pow p).sub_of_left
      (by rw [degree_X_pow]; exact lt_of_le_of_lt degree_C_le (by exact_mod_cast hp.pos))
  have hint : ∀ y : k, IsIntegral F y :=
    fun y => ⟨_, hmonic y, by rw [← aeval_def]; exact hpoly y⟩
  have hirr : ∀ y : k, y ∉ F → Irreducible (X ^ p - C (⟨y ^ p, hFpow y⟩ : F)) := by
    intro y hy
    rw [irreducible_X_pow_sub_C_iff_of_prime hp]
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
    rw [adjoin.finrank (hint y), hmin y hy, natDegree_X_pow_sub_C]
  have htop : F⟮c⟯ = ⊤ := by
    rw [eq_top_iff]
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
      have : FiniteDimensional F F⟮a⟯ := adjoin.finiteDimensional (hint a)
      have hle : F⟮c⟯ ≤ F⟮a⟯ := adjoin_simple_le_iff.mpr hca
      have heq : F⟮c⟯ = F⟮a⟯ :=
        eq_of_le_of_finrank_eq hle (by rw [hdeg c hcF, hdeg a ha])
      rw [heq]; exact mem_adjoin_simple_self F a
  have hDF : KaehlerDifferential.D F k c ≠ 0 := by
    intro h0
    have hall : ∀ x : k, KaehlerDifferential.D F k x = 0 := by
      intro x
      have hx : x ∈ (F⟮c⟯).toSubalgebra := by rw [htop]; exact Algebra.mem_top
      rw [adjoin_simple_toSubalgebra_of_isAlgebraic (hint c).isAlgebraic,
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
    have : Algebra.FormallyUnramified F k := ⟨hsub⟩
    have hfr : Module.finrank F k = p := by
      rw [← IntermediateField.finrank_top', ← htop, hdeg c hcF]
    have : Module.Finite F k := Module.finite_of_finrank_pos (by rw [hfr]; exact hp.pos)
    have hsep : Algebra.IsSeparable F k := Algebra.FormallyUnramified.isSeparable F k
    have hcsep : IsSeparable F c := Algebra.IsSeparable.isSeparable F c
    rw [IsSeparable, hmin c hcF, Polynomial.Separable] at hcsep
    have hder : derivative (X ^ p - C (⟨c ^ p, hFpow c⟩ : F)) = 0 := by
      rw [derivative_sub, derivative_X_pow, derivative_C, sub_zero, hpF, C_0, zero_mul]
    rw [hder, isCoprime_zero_right] at hcsep
    have h1 := natDegree_eq_zero_of_isUnit hcsep
    rw [natDegree_X_pow_sub_C] at h1
    exact hp.ne_zero h1
  let : Algebra (⊥ : Subfield k) F :=
    (Subfield.inclusion (bot_le : (⊥ : Subfield k) ≤ F)).toAlgebra
  have : IsScalarTower (⊥ : Subfield k) F k :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  intro h0
  apply hDF
  have := KaehlerDifferential.map_D (⊥ : Subfield k) F k k c
  rw [h0, map_zero, Algebra.algebraMap_self, RingHom.id_apply] at this
  exact this.symm

end KaehlerDifferential
