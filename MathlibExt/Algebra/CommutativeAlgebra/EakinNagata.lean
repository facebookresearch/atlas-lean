/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.FiniteType
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Noetherian.Basic

@[expose] public section

section
/-!
# Eakin–Nagata theorem

The Eakin–Nagata theorem on descent of Noetherianness.
-/

namespace MathlibExt.Algebra.CommutativeAlgebra.EakinNagataWanted

open Submodule

/-- If `N` becomes finitely generated after adjoining `a • M` (as the range of the scalar
multiplication `lsmul a`) and the submodule `{x | a • x ∈ N}` is finitely generated, then `N`
itself is finitely generated. -/
private theorem fg_of_sup_range_comap {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {N : Submodule R M} {a : R}
    (h1 : (N ⊔ LinearMap.range (LinearMap.lsmul R M a)).FG)
    (h2 : (N.comap (LinearMap.lsmul R M a)).FG) : N.FG := by
  apply Submodule.fg_of_fg_map_of_fg_inf_ker (LinearMap.range (LinearMap.lsmul R M a)).mkQ
  · have hmap : N.map (LinearMap.range (LinearMap.lsmul R M a)).mkQ
        = (N ⊔ LinearMap.range (LinearMap.lsmul R M a)).map
            (LinearMap.range (LinearMap.lsmul R M a)).mkQ := by
      rw [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]
    rw [hmap]
    exact h1.map _
  · rw [Submodule.ker_mkQ, inf_comm, ← Submodule.map_comap_eq]
    exact h2.map _

/-- Cohen-type criterion for a finite module (the `S = {1}` case of the Parkash–Kour theorem):
a finitely generated module `M` is Noetherian as soon as `p • M` is finitely generated for every
prime ideal `p`. The proof takes a maximal non-finitely-generated submodule `N` (Zorn), shows its
conductor `p = (N : M)` is prime, and derives that `N` is finitely generated after all. -/
private theorem isNoetherian_of_prime_smul_top_fg {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module.Finite R M]
    (hP : ∀ p : Ideal R, p.IsPrime → (p • (⊤ : Submodule R M)).FG) :
    IsNoetherian R M := by
  rw [isNoetherian_def]
  by_contra hcon
  rw [not_forall] at hcon
  obtain ⟨N₀, hN₀⟩ := hcon
  -- Zorn: there is a maximal non-finitely-generated submodule.
  have key : ∀ c ⊆ {S : Submodule R M | ¬ S.FG}, IsChain (· ≤ ·) c →
      ∃ ub ∈ {S : Submodule R M | ¬ S.FG}, ∀ z ∈ c, z ≤ ub := by
    intro c hcsub hchain
    rcases c.eq_empty_or_nonempty with rfl | hne
    · exact ⟨N₀, hN₀, by simp⟩
    · refine ⟨sSup c, ?_, fun z hz => le_sSup hz⟩
      intro hfg
      have hcomp := (Submodule.fg_iff_compact _).mp hfg
      obtain ⟨x, hxc, hx⟩ := (isCompactElement_iff_le_of_directed_sSup_le _).mp hcomp c hne
        hchain.directedOn le_rfl
      have hxeq : x = sSup c := le_antisymm (le_sSup hxc) hx
      exact hcsub hxc (by rw [hxeq]; exact hfg)
  obtain ⟨N, hNmax⟩ := zorn_le₀ {S : Submodule R M | ¬ S.FG} key
  have hNmem : ¬ N.FG := hNmax.1
  have maxfg : ∀ S : Submodule R M, N < S → S.FG := by
    intro S hlt
    by_contra hSfg
    have hSN : S ≤ N := hNmax.2 hSfg hlt.le
    exact (ne_of_lt hlt) (le_antisymm hlt.le hSN)
  -- The conductor ideal `p = (N : M)`.
  set 𝔭 : Ideal R := N.colon (Set.univ : Set M) with h𝔭def
  have mem𝔭 : ∀ a : R, a ∈ 𝔭 ↔ ∀ x : M, a • x ∈ N := by
    intro a
    rw [h𝔭def, Submodule.mem_colon]
    simp
  have range_le_iff : ∀ a : R, LinearMap.range (LinearMap.lsmul R M a) ≤ N ↔ a ∈ 𝔭 := by
    intro a
    rw [mem𝔭 a]
    constructor
    · intro h x
      exact h (LinearMap.mem_range.mpr ⟨x, rfl⟩)
    · intro h y hy
      obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
      exact h x
  have h𝔭ne : 𝔭 ≠ ⊤ := by
    rw [h𝔭def, Ne, Submodule.colon_eq_top_iff_subset]
    intro hsub
    apply hNmem
    have hNtop : N = ⊤ := eq_top_iff.mpr (fun x _ => hsub (Set.mem_univ x))
    rw [hNtop]; exact Module.Finite.fg_top
  have h𝔭prime : 𝔭.IsPrime := by
    rw [Ideal.isPrime_iff]
    refine ⟨h𝔭ne, ?_⟩
    intro a b hab
    by_contra hcon2
    rw [not_or] at hcon2
    obtain ⟨ha, hb⟩ := hcon2
    have hsupFG : (N ⊔ LinearMap.range (LinearMap.lsmul R M a)).FG := by
      apply maxfg
      apply left_lt_sup.mpr
      exact fun h => ha ((range_le_iff a).mp h)
    have hbex : ∃ x : M, b • x ∉ N := by
      by_contra hc
      rw [not_exists] at hc
      exact hb ((mem𝔭 b).mpr (fun x => not_not.mp (hc x)))
    obtain ⟨x, hx⟩ := hbex
    have hNle : N ≤ N.comap (LinearMap.lsmul R M a) := by
      intro n hn
      rw [Submodule.mem_comap, LinearMap.lsmul_apply]
      exact N.smul_mem a hn
    have hbxmem : b • x ∈ N.comap (LinearMap.lsmul R M a) := by
      rw [Submodule.mem_comap, LinearMap.lsmul_apply, smul_smul]
      exact (mem𝔭 (a * b)).mp hab x
    have hcomapFG : (N.comap (LinearMap.lsmul R M a)).FG := by
      apply maxfg
      refine lt_of_le_of_ne hNle ?_
      intro heq
      exact hx (heq.symm ▸ hbxmem)
    exact hNmem (fg_of_sup_range_comap hsupFG hcomapFG)
  -- Finish: derive that `N` is finitely generated, contradiction.
  obtain ⟨G, hG⟩ := (Module.Finite.fg_top : (⊤ : Submodule R M).FG)
  have h𝔭inf : 𝔭 = G.inf (fun m => N.colon {m}) := by
    apply le_antisymm
    · refine Finset.le_inf ?_
      intro m _ r hr
      rw [Submodule.mem_colon_singleton]
      exact (mem𝔭 r).mp hr m
    · intro r hr
      rw [mem𝔭 r]
      intro x
      have hx : x ∈ span R (↑G : Set M) := by rw [hG]; exact Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem y hy =>
          have hle : G.inf (fun m => N.colon {m}) ≤ N.colon {y} :=
            Finset.inf_le (Finset.mem_coe.mp hy)
          exact Submodule.mem_colon_singleton.mp (hle hr)
      | zero => rw [smul_zero]; exact N.zero_mem
      | add u v _ _ ihu ihv => rw [smul_add]; exact N.add_mem ihu ihv
      | smul c u _ ihu => rw [smul_comm]; exact N.smul_mem c ihu
  obtain ⟨m₀, _, hm₀eq⟩ := Ideal.eq_inf_of_isPrime_inf (h𝔭inf ▸ h𝔭prime)
  have hcolonm₀ : N.colon {m₀} = 𝔭 := hm₀eq.trans h𝔭inf.symm
  have hm₀N : m₀ ∉ N := by
    intro hmem
    apply h𝔭ne
    rw [← hcolonm₀, Submodule.colon_eq_top_iff_subset, Set.singleton_subset_iff]
    exact hmem
  have hKfg : (𝔭 • (⊤ : Submodule R M)).FG := hP 𝔭 h𝔭prime
  have hKle : 𝔭 • (⊤ : Submodule R M) ≤ N := by
    rw [Submodule.smul_le]
    intro r hr x _
    exact (mem𝔭 r).mp hr x
  have hQfg : (N ⊔ span R {m₀}).FG := by
    apply maxfg
    apply left_lt_sup.mpr
    intro hle
    exact hm₀N (hle (Submodule.mem_span_singleton_self m₀))
  set K : Submodule R M := 𝔭 • (⊤ : Submodule R M) with hKdef
  have hNfg : N.FG := by
    apply Submodule.fg_of_fg_map_of_fg_inf_ker K.mkQ
    · apply Submodule.fg_of_fg_map_of_fg_inf_ker (span R {K.mkQ m₀}).mkQ
      · have h1 : ((N ⊔ span R {m₀}).map K.mkQ).map (span R {K.mkQ m₀}).mkQ
            = (N.map K.mkQ).map (span R {K.mkQ m₀}).mkQ := by
          rw [Submodule.map_sup, Submodule.map_span, Set.image_singleton,
              Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]
        rw [← h1]
        exact (hQfg.map K.mkQ).map _
      · rw [Submodule.ker_mkQ]
        have hbot : (N.map K.mkQ) ⊓ span R {K.mkQ m₀} = ⊥ := by
          rw [eq_bot_iff]
          intro v hv
          rw [Submodule.mem_inf] at hv
          obtain ⟨hvN, hvs⟩ := hv
          rw [Submodule.mem_span_singleton] at hvs
          obtain ⟨c, rfl⟩ := hvs
          obtain ⟨n, hn, hnq⟩ := Submodule.mem_map.mp hvN
          have hsub : n - c • m₀ ∈ K := by
            rw [← Submodule.Quotient.eq]
            rw [Submodule.mkQ_apply, ← map_smul, Submodule.mkQ_apply] at hnq
            exact hnq
          have hcN : c • m₀ ∈ N := by
            have hmem := N.sub_mem hn (hKle hsub)
            rwa [sub_sub_cancel] at hmem
          have hc𝔭 : c ∈ 𝔭 := by
            rw [← hcolonm₀, Submodule.mem_colon_singleton]; exact hcN
          rw [Submodule.mem_bot, ← map_smul, Submodule.mkQ_apply,
              Submodule.Quotient.mk_eq_zero]
          exact Submodule.smul_mem_smul hc𝔭 Submodule.mem_top
        rw [hbot]
        exact Submodule.fg_bot
    · rw [Submodule.ker_mkQ, inf_eq_right.mpr hKle]
      exact hKfg
  exact hNmem hNfg

/--
**Eakin–Nagata theorem.** Let $A$ and $B$ be commutative rings and let $B$ be an $A$-algebra
that is finitely generated as an $A$-module. If the structure map $A \to B$ is injective and $B$
is Noetherian, then $A$ is Noetherian.

Proves `Wanted` entry `eakin_nagata`.

Source: P. M. Eakin Jr., 'The converse to a well known theorem on Noetherian rings', Mathematische
Annalen 177 (1968), 278-282, DOI 10.1007/BF01350720.
-/
theorem eakin_nagata
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] (hAB : Function.Injective (algebraMap A B))
    [IsNoetherianRing B] : IsNoetherianRing A := by
  have hB : IsNoetherian A B := by
    apply isNoetherian_of_prime_smul_top_fg
    intro p _
    rw [Ideal.smul_top_eq_map]
    exact (IsNoetherian.noetherian (p.map (algebraMap A B))).restrictScalars
  rw [isNoetherianRing_iff]
  exact isNoetherian_of_injective (Algebra.linearMap A B) hAB

end MathlibExt.Algebra.CommutativeAlgebra.EakinNagataWanted
