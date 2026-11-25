/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.Solvable
import Mathlib.Algebra.Torsor.Defs
import Mathlib.Order.CompletePartialOrder

@[expose] public section

section
/-!
# Schur–Zassenhaus theorem

Records conjugacy of complements for the Schur–Zassenhaus theorem: any two complements of
a normal Hall subgroup in a finite group are conjugate under the standard solvability
hypothesis. Hall is `Nat.Coprime (Nat.card N) N.index`. Complement existence is already
in `Mathlib.GroupTheory.SchurZassenhaus`.
-/

namespace MathlibExt.GroupTheory.SchurZassenhausWanted

open scoped Pointwise
open MulAction MulOpposite Subgroup QuotientGroup Function

private def clsC {G : Type*} [Group G] (H : Subgroup G) [IsMulCommutative H] [H.FiniteIndex]
    (K : Subgroup G) (hK : H.IsComplement' K) : H.QuotientDiff :=
  Quotient.mk'' ⟨(K : Set G), hK.symm⟩

private theorem stabilizer_clsC {G : Type*} [Group G] [Finite G] (H : Subgroup G) [H.Normal]
    [IsMulCommutative H] (hH : Nat.Coprime (Nat.card H) H.index)
    (K : Subgroup G) (hK : H.IsComplement' K) :
    stabilizer G (clsC H K hK) = K := by
  have hle : K ≤ stabilizer G (clsC H K hK) := by
    intro k hk
    have hset : (MulOpposite.op k⁻¹) • (K : Set G) = (K : Set G) := by
      ext x
      simp only [Set.mem_smul_set, smul_eq_mul_unop, MulOpposite.unop_op, SetLike.mem_coe]
      exact ⟨by rintro ⟨y, hy, rfl⟩; exact K.mul_mem hy (K.inv_mem hk),
             fun hx => ⟨x * k, K.mul_mem hx hk, by group⟩⟩
    rw [mem_stabilizer_iff]; change Quotient.mk'' _ = Quotient.mk'' _
    congr 1; exact Subtype.ext hset
  have hcompl : H.IsComplement' (stabilizer G (clsC H K hK)) :=
    isComplement'_stabilizer_of_coprime hH
  have e1 : Nat.card H * Nat.card (stabilizer G (clsC H K hK)) = Nat.card G := hcompl.card_mul_card
  have e2 : Nat.card H * Nat.card K = Nat.card G := hK.card_mul_card
  have hcard : Nat.card (stabilizer G (clsC H K hK)) = Nat.card K :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos (e1.trans e2.symm)
  exact (eq_of_le_of_card_ge hle (le_of_eq hcard)).symm

private theorem abelian_conj {G : Type*} [Group G] [Finite G] (H : Subgroup G) [H.Normal]
    [IsMulCommutative H] (hH : Nat.Coprime (Nat.card H) H.index)
    (K₁ K₂ : Subgroup G) (h₁ : H.IsComplement' K₁) (h₂ : H.IsComplement' K₂) :
    ∃ g : G, g ∈ H ∧ K₁.map (MulAut.conj g).toMonoidHom = K₂ := by
  obtain ⟨h, hh⟩ := exists_smul_eq hH (clsC H K₁ h₁) (clsC H K₂ h₂)
  refine ⟨(h : G), h.2, ?_⟩
  have hg : (h : G) • (clsC H K₁ h₁) = clsC H K₂ h₂ := hh
  have key : stabilizer G (clsC H K₂ h₂)
      = (stabilizer G (clsC H K₁ h₁)).map (MulAut.conj (h : G)).toMonoidHom := by
    rw [← hg, stabilizer_smul_eq_stabilizer_map_conj]
  rw [stabilizer_clsC H hH K₁ h₁, stabilizer_clsC H hH K₂ h₂] at key
  exact key.symm

private theorem card_map_mk'_of_disjoint {G : Type*} [Group G] [Finite G] (K M : Subgroup G)
    [M.Normal] (h : K ⊓ M = ⊥) : Nat.card (K.map (QuotientGroup.mk' M)) = Nat.card K := by
  have hinj : Set.InjOn (QuotientGroup.mk' M) (K : Set G) := by
    intro x hx y hy hxy
    have hm : x * y⁻¹ ∈ M := by
      have : (QuotientGroup.mk' M) (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
      rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at this
    have hmem : x * y⁻¹ ∈ K ⊓ M := ⟨K.mul_mem hx (K.inv_mem hy), hm⟩
    rw [h, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hmem
  change Nat.card ((QuotientGroup.mk' M) '' (K : Set G)) = Nat.card (K : Set G)
  exact Nat.card_image_of_injOn hinj

private theorem isMulComm_map {G : Type*} [Group G] (N : Subgroup G) [N.Normal] :
    IsMulCommutative (N.map (QuotientGroup.mk' ⁅N, N⁆)) := by
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  obtain ⟨a, ha, hax⟩ := x.2
  obtain ⟨b, hb, hby⟩ := y.2
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hax, ← hby, ← map_mul, ← map_mul,
      QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have hmem := commutator_mem_commutator (N.inv_mem hb) (N.inv_mem ha)
  rw [commutatorElement_def] at hmem
  convert hmem using 1
  group

private theorem map_isComplement {G : Type*} [Group G] [Finite G] (N M K : Subgroup G)
    [N.Normal] [M.Normal] (hMleN : M ≤ N) (hN : Nat.Coprime (Nat.card N) N.index)
    (hdisj : K ⊓ M = ⊥) (h : N.IsComplement' K) :
    (N.map (QuotientGroup.mk' M)).IsComplement' (K.map (QuotientGroup.mk' M)) := by
  have hcardK : Nat.card (K.map (QuotientGroup.mk' M)) = Nat.card K :=
    card_map_mk'_of_disjoint K M hdisj
  have hNindexK : N.index = Nat.card K := h.symm.index_eq_card
  have hindexN : (N.map (QuotientGroup.mk' M)).index = N.index :=
    index_map_eq N (QuotientGroup.mk'_surjective M) (by rw [QuotientGroup.ker_mk']; exact hMleN)
  have hlagr : Nat.card (N.map (QuotientGroup.mk' M)) * (N.map (QuotientGroup.mk' M)).index
      = Nat.card (G ⧸ M) := Subgroup.card_mul_index _
  have hdvd : Nat.card (N.map (QuotientGroup.mk' M)) ∣ Nat.card N := card_map_dvd N
      (QuotientGroup.mk' M)
  refine isComplement'_of_coprime ?_ ?_
  · rw [hcardK, ← hNindexK, ← hindexN]; exact hlagr
  · rw [hcardK, ← hNindexK]; exact hN.coprime_dvd_left hdvd

private theorem quotient_reduce {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hN : Nat.Coprime (Nat.card N) N.index) (K₁ K₂ : Subgroup G)
    (h₁ : N.IsComplement' K₁) (h₂ : N.IsComplement' K₂) :
    ∃ n : G, n ∈ N ∧
      (K₁.map (MulAut.conj n).toMonoidHom) ⊔ ⁅N, N⁆ = K₂ ⊔ ⁅N, N⁆ := by
  set M : Subgroup G := ⁅N, N⁆ with hMdef
  have hMnorm : M.Normal := commutator_normal N N
  have hMleN : M ≤ N := commutator_le_right N N
  have hcard : Nat.Coprime (Nat.card (N.map (mk' M))) (N.map (mk' M)).index := by
    rw [index_map_eq N (mk'_surjective M) (by rw [ker_mk']; exact hMleN)]
    exact hN.coprime_dvd_left (card_map_dvd N (mk' M))
  have hdisj : ∀ K : Subgroup G, N.IsComplement' K → K ⊓ M = ⊥ := by
    intro K hK
    have hNK : N ⊓ K = ⊥ := disjoint_iff.mp hK.disjoint
    apply le_bot_iff.mp
    calc K ⊓ M ≤ N ⊓ K := le_inf (le_trans inf_le_right hMleN) inf_le_left
      _ = ⊥ := hNK
  have h₁' := map_isComplement N M K₁ hMleN hN (hdisj K₁ h₁) h₁
  have h₂' := map_isComplement N M K₂ hMleN hN (hdisj K₂ h₂) h₂
  have hcomm : IsMulCommutative (N.map (mk' M)) := isMulComm_map N
  obtain ⟨gb, hgbmem, hgbeq⟩ := abelian_conj (N.map (mk' M)) hcard _ _ h₁' h₂'
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hgbmem
  refine ⟨n, hn, ?_⟩
  have hcomp : (MulAut.conj ((mk' M) n)).toMonoidHom.comp (mk' M)
      = (mk' M).comp (MulAut.conj n).toMonoidHom := by
    ext x; simp [QuotientGroup.mk'_apply]
  have hconj : (K₁.map (mk' M)).map (MulAut.conj ((mk' M) n)).toMonoidHom
      = (K₁.map (MulAut.conj n).toMonoidHom).map (mk' M) := by
    rw [Subgroup.map_map, Subgroup.map_map, hcomp]
  rw [hconj] at hgbeq
  have := congrArg (Subgroup.comap (mk' M)) hgbeq
  rwa [Subgroup.comap_map_eq, Subgroup.comap_map_eq, ker_mk'] at this

private theorem conj_preserves_complement {G : Type*} [Group G] [Finite G] (N K : Subgroup G)
    [hNn : N.Normal] (h : N.IsComplement' K) (g : G) :
    N.IsComplement' (K.map (MulAut.conj g).toMonoidHom) := by
  have hNK : N ⊓ K = ⊥ := disjoint_iff.mp h.disjoint
  apply isComplement'_of_card_mul_and_disjoint
  · rw [card_map_of_injective (MulAut.conj g).injective]; exact h.card_mul_card
  · rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hxN, y, hyK, rfl⟩
    have hyN : y ∈ N := by
      have h2 := hNn.conj_mem _ hxN g⁻¹
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h2
      have he : g⁻¹ * (g * y * g⁻¹) * g = y := by group
      rwa [he] at h2
    have : y ∈ N ⊓ K := ⟨hyN, hyK⟩
    rw [hNK, Subgroup.mem_bot] at this
    subst this; simp

private theorem card_sup_of_disjoint {G : Type*} [Group G] [Finite G] (M K : Subgroup G)
    [M.Normal] (h : M ⊓ K = ⊥) :
    Nat.card (M ⊔ K : Subgroup G) = Nat.card M * Nat.card K := by
  have hdisj : Disjoint M K := disjoint_iff.mpr h
  have hinj : Injective (fun p : M × K => (p.1 : G) * (p.2 : G)) := mul_injective_of_disjoint hdisj
  let f : M × K → (M ⊔ K : Subgroup G) := fun p => ⟨(p.1 : G) * (p.2 : G), mul_mem_sup p.1.2 p.2.2⟩
  have hfinj : Injective f := fun a b hab => hinj (by simpa [f, Subtype.ext_iff] using hab)
  have hfsurj : Surjective f := by
    rintro ⟨x, hx⟩
    have : x ∈ (↑M * ↑K : Set G) := by rw [← Subgroup.normal_mul]; exact hx
    obtain ⟨m, hm, k, hk, rfl⟩ := this
    exact ⟨(⟨m, hm⟩, ⟨k, hk⟩), by simp [f]⟩
  have := Nat.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)
  rw [Nat.card_prod] at this
  exact this.symm

private theorem subgroupOf_isComplement {G : Type*} [Group G] [Finite G] (M K L : Subgroup G)
    [M.Normal] (hML : M ≤ L) (hdisj : M ⊓ K = ⊥) (hsup : M ⊔ K = L) :
    (M.subgroupOf L).IsComplement' (K.subgroupOf L) := by
  have hcardM : Nat.card (M.subgroupOf L) = Nat.card M := by
    have := card_map_of_injective (K := M.subgroupOf L) L.subtype_injective
    rwa [map_subgroupOf_eq_of_le hML, eq_comm] at this
  have hKL : K ≤ L := by rw [← hsup]; exact le_sup_right
  have hcardK : Nat.card (K.subgroupOf L) = Nat.card K := by
    have := card_map_of_injective (K := K.subgroupOf L) L.subtype_injective
    rwa [map_subgroupOf_eq_of_le hKL, eq_comm] at this
  apply isComplement'_of_card_mul_and_disjoint
  · rw [hcardM, hcardK, ← card_sup_of_disjoint M K hdisj, hsup]
  · rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hxM, hxK⟩
    have : (x : G) ∈ M ⊓ K := ⟨hxM, hxK⟩
    rw [hdisj, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]; exact Subtype.ext this

private theorem conj_subgroupOf_translate {G : Type*} [Group G] (L : Subgroup G) (g' : L)
    (A : Subgroup G) (hA : A ≤ L) :
    map L.subtype ((A.subgroupOf L).map (MulAut.conj g').toMonoidHom)
      = A.map (MulAut.conj (g' : G)).toMonoidHom := by
  have hcomp : L.subtype.comp (MulAut.conj g').toMonoidHom
      = (MulAut.conj (g' : G)).toMonoidHom.comp L.subtype := by
    ext x; simp [MulAut.conj_apply, Subgroup.coe_mul]
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hA]

private theorem solvable_of_le {G : Type*} [Group G] (N M : Subgroup G) [Group.IsSolvable N]
    (h : M ≤ N) : Group.IsSolvable M := by
  have : Group.IsSolvable (M.subgroupOf N) := inferInstance
  exact Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe h).symm.toMonoidHom) (subgroupOfEquivOfLe h).symm.injective

private theorem commutator_lt {G : Type*} [Group G] [Finite G] (N : Subgroup G)
    [Group.IsSolvable N] (hN : N ≠ ⊥) : ⁅N, N⁆ < N := by
  have : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN
  rw [← N.range_subtype, MonoidHom.range_eq_map, ← map_commutator, map_subtype_lt_map_subtype]
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (G := N)
  rwa [commutator_def] at hlt

universe u

private theorem szcc_aux : ∀ n : ℕ, ∀ {G : Type u} [Group G] [Finite G] (N : Subgroup G)
    [N.Normal] [Group.IsSolvable N], Nat.card G = n → Nat.Coprime (Nat.card N) N.index →
    ∀ (K₁ K₂ : Subgroup G), N.IsComplement' K₁ → N.IsComplement' K₂ →
    ∃ g : G, g ∈ N ∧ K₁.map (MulAut.conj g).toMonoidHom = K₂ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ N _ _ hcard hN K₁ K₂ h₁ h₂
  by_cases hNbot : N = ⊥
  · subst hNbot
    rw [Subgroup.isComplement'_bot_left] at h₁ h₂
    subst h₁; subst h₂
    exact ⟨1, Subgroup.one_mem _, by simp⟩
  · set M : Subgroup G := ⁅N, N⁆ with hMdef
    have hMnorm : M.Normal := commutator_normal N N
    have hMleN : M ≤ N := commutator_le_right N N
    have hMltN : M < N := commutator_lt N hNbot
    obtain ⟨n₀, hn₀, hLeq⟩ := quotient_reduce N hN K₁ K₂ h₁ h₂
    set K₁' : Subgroup G := K₁.map (MulAut.conj n₀).toMonoidHom with hK₁'def
    have h₁' : N.IsComplement' K₁' := conj_preserves_complement N K₁ h₁ n₀
    set L : Subgroup G := K₁' ⊔ M with hLdef
    have hdisjOf : ∀ K : Subgroup G, N.IsComplement' K → M ⊓ K = ⊥ := by
      intro K hK
      have hNK : N ⊓ K = ⊥ := disjoint_iff.mp hK.disjoint
      apply le_bot_iff.mp
      calc M ⊓ K ≤ N ⊓ K := le_inf (le_trans inf_le_left hMleN) inf_le_right
        _ = ⊥ := hNK
    have hdisj₁ : M ⊓ K₁' = ⊥ := hdisjOf K₁' h₁'
    have hdisj₂ : M ⊓ K₂ = ⊥ := hdisjOf K₂ h₂
    have hMleL : M ≤ L := le_sup_right
    have hK₁'leL : K₁' ≤ L := le_sup_left
    have hsup₁ : M ⊔ K₁' = L := by rw [sup_comm]
    have hsup₂ : M ⊔ K₂ = L := by rw [sup_comm]; exact hLeq.symm
    have hK₂leL : K₂ ≤ L := by rw [← hsup₂]; exact le_sup_right
    have hc₁ : (M.subgroupOf L).IsComplement' (K₁'.subgroupOf L) :=
      subgroupOf_isComplement M K₁' L hMleL hdisj₁ hsup₁
    have hc₂ : (M.subgroupOf L).IsComplement' (K₂.subgroupOf L) :=
      subgroupOf_isComplement M K₂ L hMleL hdisj₂ hsup₂
    have hsolvM : Group.IsSolvable M := solvable_of_le N M hMleN
    have : Group.IsSolvable (M.subgroupOf L) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe hMleL).toMonoidHom) (subgroupOfEquivOfLe hMleL).injective
    -- coprimality in ↥L
    have hcardM : Nat.card (M.subgroupOf L) = Nat.card M := by
      have := card_map_of_injective (K := M.subgroupOf L) L.subtype_injective
      rwa [map_subgroupOf_eq_of_le hMleL, eq_comm] at this
    have hindexM : (M.subgroupOf L).index = Nat.card (K₁'.subgroupOf L) := hc₁.symm.index_eq_card
    have hcardK₁' : Nat.card (K₁'.subgroupOf L) = Nat.card K₁ := by
      have h1 : Nat.card (K₁'.subgroupOf L) = Nat.card K₁' := by
        have := card_map_of_injective (K := K₁'.subgroupOf L) L.subtype_injective
        rwa [map_subgroupOf_eq_of_le hK₁'leL, eq_comm] at this
      rw [h1, hK₁'def, card_map_of_injective (MulAut.conj n₀).injective]
    have hcop : Nat.Coprime (Nat.card (M.subgroupOf L)) (M.subgroupOf L).index := by
      rw [hcardM, hindexM, hcardK₁', ← h₁.symm.index_eq_card]
      exact hN.coprime_dvd_left (Subgroup.card_dvd_of_le hMleN)
    -- card L < card G
    have hcardL : Nat.card L < Nat.card G := by
      have hLcard : Nat.card L = Nat.card M * Nat.card K₁ := by
        rw [← hsup₁, card_sup_of_disjoint M K₁' hdisj₁, hK₁'def,
            card_map_of_injective (MulAut.conj n₀).injective]
      have hGcard : Nat.card N * Nat.card K₁ = Nat.card G := h₁.card_mul_card
      rw [hLcard, ← hGcard]
      exact (Nat.mul_lt_mul_right Nat.card_pos).mpr (Subgroup.card_lt_of_lt hMltN)
    -- recurse
    obtain ⟨g', hg', hgeq⟩ := ih (Nat.card L) (hcard ▸ hcardL) (M.subgroupOf L) rfl hcop
      (K₁'.subgroupOf L) (K₂.subgroupOf L) hc₁ hc₂
    -- translate
    have htrans := congrArg (Subgroup.map L.subtype) hgeq
    rw [conj_subgroupOf_translate L g' K₁' hK₁'leL, map_subgroupOf_eq_of_le hK₂leL] at htrans
    have hg'M : (g' : G) ∈ M := by
      have := (Subgroup.mem_subgroupOf).mp hg'
      simpa using this
    refine ⟨(g' : G) * n₀, N.mul_mem (hMleN hg'M) hn₀, ?_⟩
    have hconjcomp : (MulAut.conj ((g' : G) * n₀)).toMonoidHom
        = (MulAut.conj (g' : G)).toMonoidHom.comp (MulAut.conj n₀).toMonoidHom := by
      ext x; simp [MulAut.conj_apply, mul_assoc]
    rw [hconjcomp, ← Subgroup.map_map]
    exact htrans

/--
**Schur–Zassenhaus theorem: conjugacy of complements.** Let $G$ be a finite group and $N$ a normal
subgroup of $G$ whose order is coprime to its index, and suppose $N$ is solvable. If $K_1$ and
$K_2$ are complements of $N$ in $G$, then there is an element $g \in N$ with $g K_1 g^{-1} = K_2$.

Proves `Wanted` entry `schur_zassenhaus_conjugate_complements`.

Source: I. Schur (1904); H. Zassenhaus, Lehrbuch der Gruppentheorie (1937); Isaacs, Finite Group
Theory; standard solvability hypothesis for conjugacy.
-/
theorem schur_zassenhaus_conjugate_complements
    {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal]
    (hN : Nat.Coprime (Nat.card N) N.index)
    [Group.IsSolvable N]
    (K₁ K₂ : Subgroup G)
    (h₁ : N.IsComplement' K₁) (h₂ : N.IsComplement' K₂) :
    ∃ g : G, g ∈ N ∧ K₁.map (MulAut.conj g).toMonoidHom = K₂ :=
  szcc_aux (Nat.card G) N rfl hN K₁ K₂ h₁ h₂

end MathlibExt.GroupTheory.SchurZassenhausWanted

end
