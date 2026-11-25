/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Module.ZMod
import Mathlib.GroupTheory.Transfer
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import MathlibExt.GroupTheory.SchurZassenhaus

/-!
# Uncomplemented maximal subgroups of Sylow subgroups (Kourovka Notebook Problem 15.81)

This module proves that a finite non-supersoluble group has a non-cyclic Sylow subgroup with
a maximal subgroup admitting no proper complement.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.81 (A. N.
Skiba). UnsolvedMath record UM-00701169 (`KOU-15.81`), dataset ulamai/UnsolvedMath v1.8.0.

Supersoluble means a series of normal subgroups of `G` from `1` to `G` with cyclic factors. A
complement of `M` is a subgroup `K` with `M K = G` (product of sets) and `M ∩ K = 1`; "proper" is
kept as `K ≠ G`, automatic when `M ≠ 1`. A maximal subgroup of `P` is a subgroup `M < P` with no
subgroup strictly between `M` and `P`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.NonSupersolubleUncomplementedMaximalKourovka15Problem81Wanted

open scoped Pointwise

/-- **Supersoluble group (Kourovka 15.81).** A group $G$ is supersoluble when it has a series
$1 = H_0 \le H_1 \le \cdots \le H_n = G$ of subgroups, each normal in $G$, such that every factor
$H_{i+1}/H_i$ is cyclic. -/
def IsSupersoluble (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (H : Fin (n + 1) → Subgroup G), H 0 = ⊥ ∧ H (Fin.last n) = ⊤ ∧ (∀ i, (H i).Normal) ∧
    ∀ i : Fin n, H i.castSucc ≤ H i.succ ∧
      ∃ g ∈ H i.succ, ∀ x ∈ H i.succ, ∃ k : ℤ, x * (g ^ k)⁻¹ ∈ H i.castSucc

/-- **Uncomplemented maximal subgroups of Sylow subgroups (Kourovka 15.81, Skiba).** The statement
that every finite group $G$ that is not supersoluble has, for some prime $p$, a non-cyclic Sylow
$p$-subgroup $P$ with a maximal subgroup $M$ of $P$ that has no proper complement in $G$, that is,
there is no subgroup $K \ne G$ with $MK = G$ and $M \cap K = 1$. -/
def nonSupersolubleHasUncomplementedSylowMaximal : Prop :=
  ∀ (G : Type) [Group G] [Finite G], ¬ IsSupersoluble G →
    ∃ p : ℕ, p.Prime ∧ ∃ P : Sylow p G, ¬ IsCyclic (P : Subgroup G) ∧
      ∃ M : Subgroup G, M < P ∧ (∀ L : Subgroup G, M < L → L ≤ P → L = P) ∧
        ¬ ∃ K : Subgroup G, K ≠ ⊤ ∧ (M : Set G) * (K : Set G) = Set.univ ∧ M ⊓ K = ⊥

open Subgroup
open scoped IsMulCommutative

universe u

private def ComplementedMaximals (G : Type u) [Group G] : Prop :=
  ∀ p : ℕ, ∀ [Fact p.Prime] (P : Sylow p G), ¬ IsCyclic P →
    ∀ M : Subgroup P, IsCoatom M → ∃ K : Subgroup G, (M.map P.1.subtype).IsComplement' K

private theorem coatom_of_map {G : Type u} [Group G] {P : Subgroup G} {M : Subgroup P}
    (hM : IsCoatom M) :
    M.map P.subtype < P ∧ ∀ L : Subgroup G, M.map P.subtype < L → L ≤ P → L = P := by
  refine ⟨lt_of_le_of_ne (map_subtype_le M) ?_, ?_⟩
  · intro h
    apply hM.1
    apply map_injective P.subtype_injective
    rwa [Subgroup.map_top, range_subtype]
  · intro L hL hLP
    have he := hM.2 (L.subgroupOf P) (by
      rwa [← map_subtype_lt_map_subtype, map_subgroupOf_eq_of_le hLP])
    simpa [map_subgroupOf_eq_of_le hLP, Subgroup.map_top, range_subtype] using
      congrArg (map P.subtype) he

private theorem complement_of_restrict {G : Type u} [Group G] {H M K : Subgroup G}
    (h : M.IsComplement' K) (hMH : M ≤ H) :
    (M.subgroupOf H).IsComplement' (K.subgroupOf H) := by
  refine isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [disjoint_iff_inf_le]
    intro x hx
    exact Subtype.ext (h.disjoint.le_bot hx)
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨⟨m, k⟩, heq⟩ := h.2 (x : G)
    change (m : G) * (k : G) = (x : G) at heq
    have hk : (k : G) ∈ H := by
      rw [← inv_mul_cancel_left (m : G) (k : G), heq]
      exact H.mul_mem (H.inv_mem (hMH m.2)) x.2
    exact ⟨⟨m, hMH m.2⟩, m.2, ⟨k, hk⟩, k.2, Subtype.ext heq⟩

private theorem restrict_complement_to_sylow {G : Type u} [Group G] {p : ℕ}
    (P : Sylow p G) (M : Subgroup P) {K : Subgroup G}
    (hK : (M.map P.1.subtype).IsComplement' K) :
    M.IsComplement' (K.subgroupOf P.1) := by
  simpa only [subgroupOf, comap_map_eq_self_of_injective P.1.subtype_injective] using
    complement_of_restrict hK (map_subtype_le M)

private theorem exists_mem_complement_outside_coatom {G : Type u} [Group G] {p : ℕ}
    (P : Sylow p G) {M : Subgroup P} (hM : IsCoatom M) {K : Subgroup G}
    (hK : (M.map P.1.subtype).IsComplement' K) :
    ∃ x : P, (x : G) ∈ K ∧ x ∉ M := by
  have hcomp := restrict_complement_to_sylow P M hK
  have h_nle : ¬ K.subgroupOf P.1 ≤ M := by
    intro hle
    exact hM.1 ((sup_eq_left.mpr hle).symm.trans hcomp.sup_eq_top)
  exact IsConcreteLE.not_le_iff_exists.mp h_nle

private theorem sylow_le_of_index {G : Type u} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (H : Subgroup G) (hH : ¬ p ∣ H.index) (Q : Sylow p H) :
    ∃ P : Sylow p G, ∃ hP : P ≤ H, P.subtype hP = Q := by
  let P := (Q.isPGroup.map H.subtype).toSylow (by
    rw [index_map_subtype]
    exact (Fact.out : p.Prime).not_dvd_mul Q.not_dvd_index hH)
  have hP : P ≤ H := map_subtype_le Q.1
  exact ⟨P, hP, Sylow.ext (comap_map_eq_self_of_injective H.subtype_injective _)⟩

private theorem complemented_maximals_subgroup {G : Type u} [Group G] [Finite G]
    (h : ComplementedMaximals G) (H : Subgroup G)
    (hH : ∀ p : ℕ, p.Prime → p ∣ Nat.card H → ¬ p ∣ H.index) : ComplementedMaximals H := by
  intro p hp Q hQ M hM
  have hpH : p ∣ Nat.card H := by
    rcases Q.isPGroup.card_eq_or_dvd with heq | hd
    · exact (hQ (@isCyclic_of_subsingleton _ _ (Nat.card_eq_one_iff_unique.mp heq).1)).elim
    · exact hd.trans (card_subgroup_dvd_card _)
  obtain ⟨P, hPH, rfl⟩ := sylow_le_of_index H (hH p Fact.out hpH) Q
  let e : (P.subtype hPH : Subgroup H) ≃* (P : Subgroup G) := subgroupOfEquivOfLe hPH
  let E := e.mapSubgroup
  obtain ⟨K, hK⟩ := h p P (fun hc => hQ (e.isCyclic.mpr hc)) (E M) ((E.isCoatom_iff M).mpr hM)
  have he : ((E M).map P.1.subtype) = (M.map (P.subtype hPH).1.subtype).map H.subtype := by
    change (M.map e.toMonoidHom).map P.1.subtype = _
    rw [map_map, map_map]
    rfl
  rw [he] at hK
  refine ⟨K.subgroupOf H, ?_⟩
  simpa only [subgroupOf, comap_map_eq_self_of_injective H.subtype_injective] using
    complement_of_restrict hK (map_subtype_le _)

private theorem intersection_card {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (M : Subgroup P) (hM : IsCoatom M) (K : Subgroup G)
    (hK : (M.map P.1.subtype).IsComplement' K) :
    Nat.card (K.subgroupOf (P : Subgroup G)) = p := by
  have := P.isPGroup.isNilpotent
  have hc := (restrict_complement_to_sylow P M hK).card_mul_card
  exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos (hc.trans (card_mul_index M).symm)).trans
    (P.isPGroup.isCoatom_iff_index_eq_prime.mp hM)

private theorem complement_has_small_sylow {G : Type u} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (P : Sylow p G) (M : Subgroup P) (hM : IsCoatom M)
    (K : Subgroup G) (hK : (M.map P.1.subtype).IsComplement' K) :
    ∃ T : Sylow p K, (T : Subgroup K) = (P : Subgroup G).subgroupOf K ∧ Nat.card T = p := by
  let T := (P : Subgroup G).subgroupOf K
  have hc : Nat.card T = p := by
    rw [← card_map_of_injective (K := T) K.subtype_injective]
    change Nat.card ((P : Subgroup G).subgroupOf K |>.map K.subtype) = p
    rw [subgroupOf_map_subtype, inf_comm, ← subgroupOf_map_subtype (K := (P : Subgroup G)),
      card_map_of_injective P.1.subtype_injective]
    exact intersection_card P M hM K hK
  have := P.isPGroup.isNilpotent
  have hPM : Nat.card (M.map P.1.subtype) * p = Nat.card P := by
    rw [card_map_of_injective P.1.subtype_injective]
    exact (congrArg (Nat.card M * ·) (P.isPGroup.isCoatom_iff_index_eq_prime.mp hM).symm).trans
      (card_mul_index M)
  have heq : T.index = P.index := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥(M.map P.1.subtype)) : 0 < _)
    apply Nat.eq_of_mul_eq_mul_left (Fact.out : p.Prime).pos
    calc
      p * (Nat.card (M.map P.1.subtype) * T.index) =
          Nat.card (M.map P.1.subtype) * (Nat.card T * T.index) := by rw [hc]; ac_rfl
      _ = Nat.card G := by rw [card_mul_index, hK.card_mul_card]
      _ = Nat.card P * P.index := (card_mul_index (P : Subgroup G)).symm
      _ = p * (Nat.card (M.map P.1.subtype) * P.index) := by rw [← hPM]; ac_rfl
  exact ⟨(P.isPGroup.comap_subtype (K := K)).toSylow (heq.symm ▸ P.not_dvd_index), rfl, hc⟩

private theorem lift_complement {G : Type u} [Group G] {p : ℕ} (P : Sylow p G)
    (M : Subgroup P) {K : Subgroup G} (hK : (M.map P.1.subtype).IsComplement' K)
    {T H : Subgroup K} (hT : T = P.1.subgroupOf K) (hH : H.IsComplement' T) :
    P.1.IsComplement' (H.map K.subtype) := by
  refine isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [disjoint_iff_inf_le]
    rintro x ⟨hxP, y, hyH, rfl⟩
    have hyT : y ∈ T := by
      rw [hT]
      exact hxP
    exact congrArg Subtype.val (hH.disjoint.le_bot ⟨hyH, hyT⟩)
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨⟨m, k⟩, hx⟩ := hK.2 x
    obtain ⟨⟨t, h⟩, hk⟩ := hH.symm.2 k
    have ht : ((t : K) : G) ∈ P := by
      exact (congrArg (fun L : Subgroup K => (t : K) ∈ L) hT).mp t.2
    have hm : (m : G) ∈ P := map_subtype_le M m.2
    refine ⟨(m : G) * ((t : K) : G), P.1.mul_mem hm ht, (h : K), ⟨h, h.2, rfl⟩, ?_⟩
    change (m : G) * (k : G) = x at hx
    change (t : K) * (h : K) = k at hk
    change (m : G) * ((t : K) : G) * ((h : K) : G) = x
    rw [mul_assoc, ← K.coe_mul, hk, hx]

private theorem hall_of_complement {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hp : (Nat.card G).minFac = p) (M : Subgroup P)
    (hM : IsCoatom M) :
    ∀ (K : Subgroup G), (M.map P.1.subtype).IsComplement' K →
      ∃ H : Subgroup K, (P : Subgroup G).IsComplement' (H.map K.subtype) ∧ H.Normal := by
  intro K hK
  obtain ⟨T, hT, hc⟩ := complement_has_small_sylow P M hM K hK
  have hpK : (Nat.card K).minFac = p := by
    have hpd : p ∣ Nat.card K := hc ▸ card_subgroup_dvd_card T.1
    have hne : Nat.card K ≠ 1 := fun heq => (Fact.out : p.Prime).not_dvd_one (heq ▸ hpd)
    refine le_antisymm (Nat.minFac_le_of_dvd (Fact.out : p.Prime).two_le hpd) ?_
    rw [← hp]
    exact Nat.minFac_le_of_dvd (Nat.minFac_prime hne).two_le
      ((Nat.minFac_dvd _).trans (card_subgroup_dvd_card K))
  let H := (MonoidHom.transferSylow T ((isCyclic_of_prime_card hc).normalizer_le_centralizer
    hpK)).ker
  have hH : H.IsComplement' T := (isCyclic_of_prime_card hc).isComplement' hpK
  exact ⟨H, lift_complement P M hK hT hH, inferInstance⟩

private theorem hall_index_support {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {H : Subgroup G} (hH : P.1.IsComplement' H) :
    ∀ q : ℕ, q.Prime → q ∣ Nat.card H → ¬ q ∣ H.index := by
  intro q hq hqH hqd
  obtain ⟨n, hn⟩ := P.isPGroup.exists_card_eq
  have hqp := hq.dvd_of_dvd_pow (hn ▸ hH.index_eq_card ▸ hqd)
  have heq := (Nat.prime_dvd_prime_iff_eq hq Fact.out).mp hqp
  exact P.not_dvd_index (hH.symm.index_eq_card ▸ heq ▸ hqH)

private theorem hall_card_lt {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hp : p ∣ Nat.card G) {H : Subgroup G} (hH : P.1.IsComplement' H) :
    Nat.card H < Nat.card G := by
  rw [← hH.card_mul_card]
  simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right
    (Nat.lt_of_lt_of_le (Fact.out : p.Prime).one_lt
      (Nat.le_of_dvd Nat.card_pos (P.dvd_card_of_dvd_card hp))) Nat.card_pos

private theorem largest_sylow_normal {G : Type u} [Group G] [Finite G]
    (h : ComplementedMaximals G) {q : ℕ} [Fact q.Prime] (hq : q ∣ Nat.card G)
    (hmax : ∀ r, r.Prime → r ∣ Nat.card G → r ≤ q) (Q : Sylow q G) : Q.Normal := by
  classical
  generalize hn : Nat.card G = n at hq hmax ⊢
  induction n using Nat.strong_induction_on generalizing G with
  | ind n ih =>
    subst n
    let p := (Nat.card G).minFac
    have hcard : Nat.card G ≠ 1 := fun heq => (Fact.out : q.Prime).not_dvd_one (heq ▸ hq)
    have : Fact p.Prime := ⟨Nat.minFac_prime hcard⟩
    have hp : p ∣ Nat.card G := Nat.minFac_dvd _
    by_cases hpq : p = q
    · have hPG : IsPGroup q G := by
        apply (isPGroup_iff_primeFactors_card_subset (Fact.out : q.Prime).ne_zero).mpr
        intro r hr
        obtain ⟨hrp, hrd, _⟩ := Nat.mem_primeFactors.mp hr
        have hrq := hmax r hrp hrd
        have hqr : q ≤ r := hpq ▸ Nat.minFac_le_of_dvd hrp.two_le hrd
        rw [hrq.antisymm hqr]
        exact Nat.mem_primeFactors.mpr ⟨Fact.out, dvd_rfl, (Fact.out : q.Prime).ne_zero⟩
      have ht : IsPGroup q (⊤ : Subgroup G) := hPG.to_subgroup _
      have heq := Q.maximal_isPGroup.eq_of_ge ht le_top
      exact heq ▸ normal_top
    -- Induction makes the largest Sylow subgroup of each Hall complement characteristic.
    have from_hall : ∀ (H : Subgroup G), (∃ P : Sylow p G, P.1.IsComplement' H) →
        ∃ R : Sylow q H, R.Characteristic ∧
          ∃ S : Sylow q G, S.1 = R.1.map H.subtype := by
      rintro H ⟨P, hH⟩
      obtain ⟨k, hk⟩ := P.isPGroup.exists_card_eq
      have hqP : ¬ q ∣ Nat.card P := by
        intro hd
        exact hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) (Fact.out : p.Prime)).mp
          ((Fact.out : q.Prime).dvd_of_dvd_pow (hk ▸ hd))).symm
      have hqH : q ∣ Nat.card H :=
        ((Fact.out : q.Prime).dvd_mul.mp (hH.card_mul_card ▸ hq)).resolve_left hqP
      have hi := hall_index_support P hH
      let R : Sylow q H := default
      have hRn := ih (Nat.card H) (hall_card_lt P hp hH) (complemented_maximals_subgroup h H hi)
        R rfl hqH (fun r hr hrd => hmax r hr (hrd.trans (card_subgroup_dvd_card H)))
      let S := (R.isPGroup.map H.subtype).toSylow (by
        rw [index_map_subtype]
        exact (Fact.out : q.Prime).not_dvd_mul R.not_dvd_index (hi q Fact.out hqH))
      exact ⟨R, R.characteristic_of_normal hRn, S, rfl⟩
    let P : Sylow p G := default
    by_cases hPc : IsCyclic P
    · let H := (MonoidHom.transferSylow P (hPc.normalizer_le_centralizer rfl)).ker
      obtain ⟨R, hR, S, hS⟩ := from_hall H ⟨P, (hPc.isComplement' rfl).symm⟩
      have hSn : S.Normal := hS.symm ▸ (inferInstance : (R.1.map H.subtype).Normal)
      let := S.unique_of_normal hSn
      exact Q.normal_of_subsingleton
    have := P.isPGroup.isNilpotent
    have hnormalizer : ∀ (M : Subgroup P), IsCoatom M →
        ∃ S : Sylow q G, ∃ x : P, x ∉ M ∧ x.1 ∈ normalizer (S : Set G) ∧
          ∃ H : Subgroup G, P.1.IsComplement' H ∧ H ≤ normalizer (S : Set G) := by
      intro M hM
      obtain ⟨K, hK⟩ := h p P hPc M hM
      obtain ⟨H, hH, hHn⟩ := hall_of_complement P rfl M hM K hK
      obtain ⟨R, hR, S, hS⟩ := from_hall (H.map K.subtype) ⟨P, hH⟩
      let e : H ≃* (H.map K.subtype) := H.equivMapOfInjective K.subtype K.subtype_injective
      let U := R.1.comap e.toMonoidHom
      have he : Function.Surjective e.toMonoidHom := e.surjective
      have hU : U.Characteristic := by
        apply characteristic_iff_le_comap.mpr
        intro f x hx
        have he' := characteristic_iff_le_comap.mp hR (e.symm.trans (f.trans e)) hx
        change e (f (e.symm (e x))) ∈ R.1 at he'
        change e (f x) ∈ R.1
        simpa only [e.symm_apply_apply] using he'
      have hV : (U.map H.subtype).Normal := inferInstance
      have hVeq : (U.map H.subtype).map K.subtype = S.1 := by
        rw [hS, map_map]
        conv_rhs =>
          rw [← map_comap_eq_self_of_surjective he R.1, map_map]
        rfl
      have hKS : K ≤ normalizer (S : Set G) := by
        change K ≤ normalizer (S.1 : Set G)
        rw [← hVeq, ← normal_subgroupOf_iff_le_normalizer (map_subtype_le _)]
        simpa only [subgroupOf, comap_map_eq_self_of_injective K.subtype_injective] using hV
      obtain ⟨x, hxK, hxM⟩ := exists_mem_complement_outside_coatom P hM hK
      exact ⟨S, x, hxM, hKS hxK, H.map K.subtype, hH, (map_subtype_le H).trans hKS⟩
    have : Nontrivial P := not_subsingleton_iff_nontrivial.mp
      (fun hs => hPc (@isCyclic_of_subsingleton _ _ hs))
    obtain ⟨M, hM, _⟩ := (eq_top_or_exists_le_coatom (⊥ : Subgroup P)).resolve_left bot_ne_top
    obtain ⟨S, _, _, _, H, hH, hHS⟩ := hnormalizer M hM
    suffices hSn : S.Normal by
      let := S.unique_of_normal hSn
      exact Q.normal_of_subsingleton
    rw [← normalizer_eq_top_iff, eq_top_iff]
    -- All the largest Sylow subgroups are conjugate by the smallest Sylow subgroup.
    -- Its maximal subgroups are normal, so a proper normalizer would miss a required conjugate.
    have hPS : (normalizer (S : Set G)).subgroupOf P.1 = ⊤ := by
      by_contra hne
      obtain ⟨L, hL, hSL⟩ := (eq_top_or_exists_le_coatom _).resolve_left hne
      obtain ⟨S', x, hxL, hxS', _, _, _⟩ := hnormalizer L hL
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S S'
      obtain ⟨⟨a, b⟩, hab⟩ := hH.2 g
      change (a : G) * (b : G) = g at hab
      rw [← hab, mul_smul, Sylow.smul_eq_iff_mem_normalizer.mpr (hHS b.2)] at hg
      have hy : (a⁻¹ * x * a : P) ∈ (normalizer (S : Set G)).subgroupOf P.1 := by
        change ((a : G)⁻¹ * (x : G) * (a : G)) ∈ normalizer (S : Set G)
        rw [← Sylow.smul_eq_iff_mem_normalizer, mul_smul, mul_smul, hg,
          Sylow.smul_eq_iff_mem_normalizer.mpr hxS', ← hg, inv_smul_smul]
      have hLn := Group.normalizerCondition_of_isNilpotent (G := P) |>.normal_of_coatom L hL
      have heq : a * (a⁻¹ * x * a) * a⁻¹ = x := by group
      exact hxL (heq ▸ hLn.conj_mem _ (hSL hy) a)
    rw [← hH.sup_eq_top]
    exact sup_le (by
      intro x hx
      have : (⟨x, hx⟩ : P) ∈ (normalizer (S : Set G)).subgroupOf P.1 := by simp [hPS]
      exact this) hHS

private theorem normal_le_of_coprime {G : Type u} [Group G] [Finite G]
    (N K : Subgroup G) [N.Normal] (h : (Nat.card N).Coprime K.index) : N ≤ K := by
  have hNK : N.relIndex (K ⊔ N) = N.relIndex K := relIndex_sup_right K N
  have heq : K.relIndex (K ⊔ N) * Nat.card (N ⊓ K : Subgroup G) = Nat.card N := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < N.relIndex K from index_pos)
    calc
      N.relIndex K * (K.relIndex (K ⊔ N) * Nat.card (N ⊓ K : Subgroup G)) =
          K.relIndex (K ⊔ N) * (N.relIndex K * Nat.card (N ⊓ K : Subgroup G)) := by ac_rfl
      _ = Nat.card (K ⊔ N : Subgroup G) := by
        rw [relIndex_mul_card]
        simpa only [inf_eq_left.mpr (show K ≤ K ⊔ N from le_sup_left)] using
          relIndex_mul_card K (K ⊔ N)
      _ = N.relIndex K * Nat.card N := by
        rw [← hNK]
        simpa only [inf_eq_left.mpr (show N ≤ K ⊔ N from le_sup_right)] using
          (relIndex_mul_card N (K ⊔ N)).symm
  have hd : K.relIndex (K ⊔ N) ∣ Nat.card N := dvd_of_mul_right_eq _ heq
  have h1 := Nat.eq_one_of_dvd_coprimes h hd (relIndex_dvd_index_of_le le_sup_left)
  exact le_sup_right.trans (relIndex_eq_one.mp h1)

private theorem complemented_maximals_quotient {G : Type u} [Group G] [Finite G]
    (h : ComplementedMaximals G) (N : Subgroup G) [N.Normal] {q : ℕ}
    (hq : q.Prime) (hN : Nat.card N = q) : ComplementedMaximals (G ⧸ N) := by
  intro p hp Q hQc L hL
  let f := QuotientGroup.mk' N
  have hsurj : Function.Surjective f := QuotientGroup.mk'_surjective N
  obtain ⟨P, rfl⟩ := Sylow.mapSurjective_surjective hsurj p Q
  let e := f.subgroupMap P.1
  have he : Function.Surjective e := f.subgroupMap_surjective P.1
  let M := L.comap e
  have hM : IsCoatom M := isCoatom_comap_of_surjective he hL
  have hPc : ¬ IsCyclic P := fun hc => hQc (isCyclic_of_surjective e he)
  obtain ⟨K, hK⟩ := h p P hPc M hM
  have hMmap : (M.map P.1.subtype).map f = L.map (P.map f).subtype := by
    rw [← map_comap_eq_self_of_surjective he L, map_map, map_map]
    rfl
  use K.map f
  change (L.map (P.map f).subtype).IsComplement' (K.map f)
  rw [← hMmap]
  refine isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [disjoint_iff_inf_le]
    rintro _ ⟨⟨a, ha, rfl⟩, b, hb, heq⟩
    have hab : b * a⁻¹ ∈ N := by
      have hker : b * a⁻¹ ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, heq, mul_inv_cancel]
      simpa only [f, QuotientGroup.ker_mk'] using hker
    suffices a ∈ N from (QuotientGroup.eq_one_iff _).mpr this
    by_cases hpq : p = q
    · have hNp : IsPGroup p N := IsPGroup.of_card (n := 1) (by rw [hN, pow_one, hpq])
      have hNP := hNp.le_sylow_of_normal P
      have hNM : N ≤ M.map P.1.subtype := by
        intro x hx
        refine ⟨⟨x, hNP hx⟩, ?_, rfl⟩
        change e ⟨x, hNP hx⟩ ∈ L
        have hfx : e ⟨x, hNP hx⟩ = 1 :=
          Subtype.ext ((QuotientGroup.eq_one_iff _).mpr hx)
        rw [hfx]
        exact L.one_mem
      have hbM : b ∈ M.map P.1.subtype := by
        simpa only [inv_mul_cancel_right] using
          (M.map P.1.subtype).mul_mem (hNM hab) ha
      have hb1 := hK.disjoint.le_bot ⟨hbM, hb⟩
      rw [Subgroup.mem_bot] at hb1
      simpa [hb1] using N.inv_mem hab
    · have hNle : N ≤ K := by
        obtain ⟨k, hk⟩ := (P.isPGroup.to_subgroup M).exists_card_eq
        apply normal_le_of_coprime
        rw [hN, hK.index_eq_card, card_map_of_injective P.1.subtype_injective, hk]
        exact (hq.coprime_iff_not_dvd.mpr
          (fun h => hpq ((Nat.prime_dvd_prime_iff_eq hq hp.out).mp h).symm)).pow_right _
      have haK := K.mul_mem (K.inv_mem (hNle hab)) hb
      have ha1 : a = 1 := hK.disjoint.le_bot ⟨ha, by simpa using haK⟩
      rw [ha1]
      exact N.one_mem
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨g, rfl⟩ := hsurj x
    obtain ⟨⟨a, b⟩, hab⟩ := hK.2 g
    exact ⟨f a, ⟨a, a.2, rfl⟩, f b, ⟨b, b.2, rfl⟩,
      (map_mul f _ _).symm.trans (congrArg f hab)⟩

private theorem invariant_prime_subgroup {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) [P.Normal] (h : ComplementedMaximals G)
    (hPc : ¬ IsCyclic P) {H : Subgroup G} (hH : P.1.IsComplement' H)
    (M : Subgroup P) (hM : IsCoatom M) :
    ∃ A : Subgroup G, A ≤ P.1 ∧ Nat.card A = p ∧ H ≤ normalizer (A : Set G) ∧
      ¬ A.subgroupOf P.1 ≤ M := by
  obtain ⟨K, hK⟩ := h p P hPc M hM
  obtain ⟨T, hT, hc⟩ := complement_has_small_sylow P M hM K hK
  have hTn : T.Normal := hT.symm ▸ inferInstanceAs (P.1.subgroupOf K).Normal
  obtain ⟨W, hW⟩ := exists_right_complement'_of_coprime T.card_coprime_index
  have hPW := lift_complement P M hK hT hW.symm
  have := P.isPGroup.isNilpotent
  have := Group.IsNilpotent.to_isSolvable (G := P)
  obtain ⟨g, hg, hWH⟩ :=
    SchurZassenhausWanted.schur_zassenhaus_conjugate_complements P.1 P.card_coprime_index
      _ H hPW hH
  let A := T.1.map K.subtype
  have hAP : A ≤ P.1 := by
    change T.1.map K.subtype ≤ P.1
    rw [hT, subgroupOf_map_subtype]
    exact inf_le_left
  have hKA : K ≤ normalizer (A : Set G) := by
    rw [← normal_subgroupOf_iff_le_normalizer (show A ≤ K from map_subtype_le T.1)]
    simpa only [A, subgroupOf, comap_map_eq_self_of_injective K.subtype_injective] using hTn
  let c := (MulAut.conj g).toMonoidHom
  refine ⟨A.map c, ?_, ?_, ?_, ?_⟩
  · rw [map_le_iff_le_comap]
    exact fun x hx => (inferInstance : P.1.Normal).conj_mem x (hAP hx) g
  · rw [card_map_of_injective (MulAut.conj g).injective, card_map_of_injective K.subtype_injective]
    exact hc
  · rw [← hWH]
    exact (map_mono ((map_subtype_le W).trans hKA)).trans (le_normalizer_map c)
  · obtain ⟨x, hxK, hxM⟩ := exists_mem_complement_outside_coatom P hM hK
    have hxA : (x : G) ∈ A := by
      change (x : G) ∈ T.1.map K.subtype
      rw [hT, subgroupOf_map_subtype]
      exact ⟨x.2, hxK⟩
    let x' := (MulAut.conj ⟨g, hg⟩ : MulAut P) x
    have hx'A : x' ∈ (A.map c).subgroupOf P.1 := ⟨x, hxA, rfl⟩
    intro hle
    have hMn := Group.normalizerCondition_of_isNilpotent (G := P) |>.normal_of_coatom M hM
    apply hxM
    convert hMn.conj_mem x' (hle hx'A) (⟨g, hg⟩ : P)⁻¹ using 1
    dsimp [x', MulAut.conj_apply]
    group

private theorem cyclic_action {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) [P.Normal] (h : ComplementedMaximals G)
    (hPc : ¬ IsCyclic P) {H : Subgroup G} (hH : P.1.IsComplement' H) :
    let f := (MulAut.conjNormal (H := P.1)).comp H.subtype
    (∀ x y : H, Commute (f x) (f y)) ∧ ∀ x : H, f x ^ (p - 1) = 1 := by
  classical
  dsimp only
  let f := (MulAut.conjNormal (H := P.1)).comp H.subtype
  let S : Set P := {x | ∃ A : Subgroup G,
    A ≤ P.1 ∧ Nat.card A = p ∧ H ≤ normalizer (A : Set G) ∧ (x : G) ∈ A}
  -- Every maximal subgroup misses an invariant subgroup of order p, so these generate P.
  have hS : closure S = ⊤ := by
    by_contra hn
    obtain ⟨M, hM, hSM⟩ := (eq_top_or_exists_le_coatom _).resolve_left hn
    obtain ⟨A, hAP, hc, hHA, hAM⟩ := invariant_prime_subgroup P h hPc hH M hM
    exact hAM fun x hx => hSM (subset_closure ⟨A, hAP, hc, hHA, hx⟩)
  have h_eq (x y : H)
      (he : ∀ A : Subgroup G, A ≤ P.1 → Nat.card A = p →
        ∀ hHA : H ≤ normalizer (A : Set G),
        (A.normalizerMonoidHom.comp (inclusion hHA)) x =
          (A.normalizerMonoidHom.comp (inclusion hHA)) y) :
      f x = f y := by
    apply MulEquiv.toMonoidHom_injective
    apply MonoidHom.eq_of_eqOn_dense hS
    rintro a ⟨A, hAP, hc, hHA, ha⟩
    apply Subtype.ext
    exact congrArg (fun z : MulAut A => (z ⟨a, ha⟩ : G)) (he A hAP hc hHA)
  constructor
  · intro x y
    change f x * f y = f y * f x
    rw [← map_mul, ← map_mul]
    apply h_eq
    intro A _ hc hHA
    let g := A.normalizerMonoidHom.comp (inclusion hHA)
    have : IsCyclic A := isCyclic_of_prime_card hc
    apply (IsCyclic.mulAutMulEquiv A).injective
    change IsCyclic.mulAutMulEquiv A (g (x * y)) = IsCyclic.mulAutMulEquiv A (g (y * x))
    rw [map_mul, map_mul, map_mul, map_mul, mul_comm]
  · intro x
    change f x ^ (p - 1) = 1
    rw [← map_pow, ← map_one f]
    apply h_eq
    intro A _ hc hHA
    let g := A.normalizerMonoidHom.comp (inclusion hHA)
    have : IsCyclic A := isCyclic_of_prime_card hc
    have he : Nat.card (MulAut A) = p - 1 := by
      rw [IsCyclic.card_mulAut, hc, Nat.totient_prime Fact.out]
    change g (x ^ (p - 1)) = g 1
    rw [map_pow, map_one, ← he, pow_card_eq_one']

open Module Polynomial
open scoped Polynomial

private theorem eigenvalue_of_pow_eq {V : Type u} [AddCommGroup V] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (f : End (ZMod p) V) (hf : f ^ p = f) : ∃ a : ZMod p, f.HasEigenvalue a := by
  have hi : IsIntegral (ZMod p) f := Algebra.IsIntegral.isIntegral f
  have hpol : (minpoly (ZMod p) f) ∣ (X ^ p - X : (ZMod p)[X]) := by
    apply minpoly.dvd
    simp [hf]
  have hs := (Polynomial.splits_X_pow_char_sub_X (ZMod p) p).of_dvd
    (Polynomial.X_pow_sub_X_ne_zero (Fact.out : p.Prime).one_lt) hpol
  obtain ⟨a, ha⟩ := hs.exists_eval_eq_zero (ne_of_gt (minpoly.degree_pos hi))
  exact ⟨a, Module.End.hasEigenvalue_of_isRoot ha⟩

private theorem pow_eq_of_mapped_power {A B : Type*} [Monoid A] [Monoid B]
    (f : A →* B) (x : A) {n : ℕ} (hn : 0 < n)
    (h : f (x ^ (n - 1)) = f 1) : f x ^ n = f x := by
  rw [map_pow, map_one] at h
  have he : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [← he, pow_succ, h, one_mul]

private theorem normal_prime_of_action {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) [P.Normal] [Nontrivial P]
    {H : Subgroup G} (hH : P.1.IsComplement' H)
    (haction : IsCyclic P ∨
      let f := (MulAut.conjNormal (H := P.1)).comp H.subtype
      (∀ x y : H, Commute (f x) (f y)) ∧ ∀ x : H, f x ^ (p - 1) = 1) :
    ∃ N : Subgroup G, N.Normal ∧ Nat.card N = p := by
  classical
  let Z := (center P).map P.1.subtype
  have hZP : Z ≤ P.1 := map_subtype_le _
  have hZn : Z.Normal := inferInstance
  have hZne : Z ≠ ⊥ := by
    intro he
    have he' : center P = ⊥ := map_injective P.1.subtype_injective
      (he.trans (map_bot P.1.subtype).symm)
    exact (P.isPGroup.bot_lt_center.ne) he'.symm
  obtain ⟨N, hN⟩ := exists_minimal_of_wellFoundedLT
    (fun N : Subgroup G => N ≤ Z ∧ N.Normal ∧ N ≠ ⊥) ⟨Z, le_rfl, hZn, hZne⟩
  have hNnorm := hN.prop.2.1
  have hNP := hN.prop.1.trans hZP
  have hNnt : Nontrivial N := (nontrivial_iff_ne_bot N).mpr hN.prop.2.2
  have hcentral (x : N) (y : P) : Commute (x : G) (y : G) := by
    obtain ⟨z, hz, he⟩ := hN.prop.1 x.2
    have hh := mem_center_iff.mp hz y
    change (z : G) = (x : G) at he
    rw [← he]
    exact congrArg Subtype.val hh.symm
  have hcommN : ∀ x y : N, x * y = y * x :=
    fun x y => Subtype.ext (hcentral x ⟨y, hNP y.2⟩).eq
  have : IsMulCommutative N := ⟨⟨hcommN⟩⟩
  have hpcard : p ∣ Nat.card N := by
    have hNp : IsPGroup p N := P.isPGroup.of_injective (inclusion hNP) (inclusion_injective hNP)
    exact hNp.card_eq_or_dvd.resolve_left (by
      intro he
      let := (Nat.card_eq_one_iff_unique.mp he).1
      exact not_nontrivial N hNnt)
  let E := (powMonoidHom (α := N) p).ker
  have hEc : E.Characteristic := by
    rw [characteristic_iff_le_comap]
    intro e x hx
    change x ^ p = 1 at hx
    change e x ^ p = 1
    rw [← map_pow, hx, map_one]
  have hpow : ∀ x : N, x ^ p = 1 := by
    have hEM : E.map N.subtype = N := by
      have hEn : (E.map N.subtype).Normal := inferInstance
      have hEne : E.map N.subtype ≠ ⊥ := by
        obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpcard
        have hxE : x ∈ E := by
          change x ^ p = 1
          rw [← hx, pow_orderOf_eq_one]
        intro he
        have hx1 : x = 1 := Subtype.ext (show (x : G) ∈ (⊥ : Subgroup G) from
          he ▸ E.apply_coe_mem_map N.subtype ⟨x, hxE⟩)
        exact (Fact.out : p.Prime).ne_one (hx ▸ (hx1 ▸ orderOf_one))
      exact (map_subtype_le E).antisymm
        (hN.le_of_le ⟨(map_subtype_le E).trans hN.prop.1, hEn, hEne⟩ (map_subtype_le E))
    intro x
    have htop : E = ⊤ := map_injective N.subtype_injective
      (hEM.trans (by rw [Subgroup.map_top, range_subtype]))
    exact show x ∈ E by rw [htop]; trivial
  rcases haction with hcyc | ⟨hc, hp⟩
  · have : IsCyclic P := hcyc
    have hNc : IsCyclic N := isCyclic_of_le hNP
    obtain ⟨a, ha⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hNc
    have hcard := orderOf_eq_card_of_zpowers_eq_top ha
    exact ⟨N, hNnorm, Nat.dvd_antisymm (hcard ▸ orderOf_dvd_of_pow_eq_one (hpow a)) hpcard⟩
  let zmodModule : Module (ZMod p) (Additive N) := AddCommGroup.zmodModule hpow
  let : Module (ZMod p) (Additive N) := zmodModule
  have finiteModule : Module.Finite (ZMod p) (Additive N) := Module.Finite.of_finite
  let EndV := End (ZMod p) (Additive N)
  let endMonoid : Monoid EndV := Module.End.instMonoid
  let : Monoid EndV := endMonoid
  let linear (x : H) : End (ZMod p) (Additive N) :=
    ((MulAut.conjNormal (H := N) (x : G)).toMonoidHom.toAdditive).toZModLinearMap p
  let mulOneH := (Subgroup.toGroup H).toMonoid.toMulOneClass.toMulOne
  let mulOneEnd := endMonoid.toMulOneClass.toMulOne
  let action : @MonoidHom H EndV mulOneH mulOneEnd := by
    refine {
      toFun := linear
      map_one' := ?_
      map_mul' := ?_ }
    · apply LinearMap.ext
      intro a
      change Additive.ofMul (MulAut.conjNormal (H := N) 1 a.toMul) = a
      rw [map_one]
      rfl
    · intro x y
      apply LinearMap.ext
      intro a
      change Additive.ofMul (MulAut.conjNormal (H := N) ((x : G) * (y : G)) a.toMul) =
        Additive.ofMul (MulAut.conjNormal (H := N) (x : G)
          (MulAut.conjNormal (H := N) (y : G) a.toMul))
      rw [map_mul]
      rfl
  have transfer_eq (x y : H)
      (he : MulAut.conjNormal (H := P.1) (x : G) = MulAut.conjNormal (H := P.1) (y : G)) :
      action x = action y := by
    apply LinearMap.ext
    intro a
    change Additive.ofMul (MulAut.conjNormal (H := N) (x : G) a.toMul) =
      Additive.ofMul (MulAut.conjNormal (H := N) (y : G) a.toMul)
    congr 1
    apply Subtype.ext
    exact congrArg (fun v : MulAut P => (v ⟨a.toMul, hNP a.toMul.2⟩ : G)) he
  let f := (MulAut.conjNormal (H := P.1)).comp H.subtype
  have haction_comm (x y : H) : @Commute EndV endMonoid.toMul (action x) (action y) := by
    have hxy : f (x * y) = f (y * x) := by simpa only [map_mul] using (hc x y).eq
    exact (@MonoidHom.map_mul' _ _ mulOneH mulOneEnd action x y).symm.trans
      ((transfer_eq _ _ hxy).trans (@MonoidHom.map_mul' _ _ mulOneH mulOneEnd action y x))
  have haction_exp (x : H) : action (x ^ (p - 1)) = action (1 : H) := by
    apply transfer_eq
    change f (x ^ (p - 1)) = f 1
    rw [map_pow, map_one]
    exact hp x
  have invariant_normal (A : Subgroup N)
      (hA : ∀ (y : H) (a : N), a ∈ A → MulAut.conjNormal (y : G) a ∈ A) :
      (A.map N.subtype).Normal := by
    constructor
    rintro _ ⟨a, ha, rfl⟩ g
    obtain ⟨⟨x, y⟩, he⟩ := hH.2 g
    let b := MulAut.conjNormal (H := N) (y : G) a
    refine ⟨b, hA y a ha, ?_⟩
    change (x : G) * (y : G) = g at he
    change (b : G) = g * (a : G) * g⁻¹
    rw [← he, mul_inv_rev]
    have hx : (x : G) * (b : G) * (x : G)⁻¹ = (b : G) := by
      rw [(hcentral b x).symm.eq, mul_inv_cancel_right]
    simp only [b, MulAut.conjNormal_apply] at hx
    calc
      ((y : G) * (a : G) * (y : G)⁻¹) =
          (x : G) * ((y : G) * (a : G) * (y : G)⁻¹) * (x : G)⁻¹ := hx.symm
      _ = _ := by group
  -- Each eigenspace is invariant under the commuting action and hence normal in G.
  -- Minimality of N forces each operator to act as a scalar.
  have scalar (x : H) : ∃ k : ZMod p, ∀ a : Additive N, (linear x).toFun a = k • a := by
    have hpowx := @pow_eq_of_mapped_power H EndV inferInstance endMonoid action x p
      (Fact.out : p.Prime).pos (haction_exp x)
    obtain ⟨k, hk⟩ := @eigenvalue_of_pow_eq (Additive N) inferInstance inferInstance p
      inferInstance zmodModule finiteModule (linear x) hpowx
    let U := (action x).eigenspace k
    let A : Subgroup N := U.toAddSubgroup.toSubgroup'
    have hAnorm : (A.map N.subtype).Normal := invariant_normal A (by
      intro y a ha
      change action y (Additive.ofMul a) ∈ U
      exact Module.End.mapsTo_genEigenspace_of_comm (haction_comm x y) k 1 ha)
    have hAne : A.map N.subtype ≠ ⊥ := by
      intro he
      have hAb : A = ⊥ := map_injective N.subtype_injective
        (he.trans (map_bot N.subtype).symm)
      apply hk
      apply (U.eq_bot_iff).mpr
      intro a ha
      have hm : a.toMul ∈ A := ha
      rw [hAb, mem_bot] at hm
      exact hm
    have hAt : A = ⊤ := by
      apply map_injective N.subtype_injective
      rw [Subgroup.map_top, range_subtype]
      exact (map_subtype_le A).antisymm
        (hN.le_of_le ⟨(map_subtype_le A).trans hN.prop.1, hAnorm, hAne⟩ (map_subtype_le A))
    refine ⟨k, fun a => Module.End.mem_eigenspace_iff.mp ?_⟩
    exact show a.toMul ∈ A by rw [hAt]; trivial
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p hpcard
  let B := zpowers a
  have hBn : (B.map N.subtype).Normal := invariant_normal B (by
    intro y x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    rw [map_zpow]
    apply B.zpow_mem
    obtain ⟨c, hc⟩ := scalar y
    have he : (linear y).toFun (Additive.ofMul a) = c.val • Additive.ofMul a := by
      rw [hc, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
    refine mem_zpowers_iff.mpr ⟨c.val, ?_⟩
    rw [zpow_natCast]
    exact congrArg Additive.toMul he.symm)
  refine ⟨B.map N.subtype, hBn, ?_⟩
  rw [card_map_of_injective N.subtype_injective, Nat.card_zpowers, ha]

private theorem exists_normal_prime {G : Type u} [Group G] [Finite G]
    (h : ComplementedMaximals G) (hcard : Nat.card G ≠ 1) :
    ∃ (p : ℕ) (N : Subgroup G), p.Prime ∧ N.Normal ∧ Nat.card N = p := by
  classical
  let s := (Nat.card G).primeFactors
  have hs : s.Nonempty := ⟨(Nat.card G).minFac,
    Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime hcard, Nat.minFac_dvd _, Nat.card_pos.ne'⟩⟩
  let p := s.max' hs
  obtain ⟨hp, hpd, _⟩ := Nat.mem_primeFactors.mp (s.max'_mem hs)
  have : Fact p.Prime := ⟨hp⟩
  let P : Sylow p G := default
  have hPn : P.Normal := largest_sylow_normal h hpd
    (fun r hr hrd => s.le_max' r (Nat.mem_primeFactors.mpr ⟨hr, hrd, Nat.card_pos.ne'⟩)) P
  have : Nontrivial P := (nontrivial_iff_ne_bot P.1).mpr (P.ne_bot_of_dvd_card hpd)
  obtain ⟨H, hH⟩ := exists_right_complement'_of_coprime P.card_coprime_index
  have haction : IsCyclic P ∨
      let f := (MulAut.conjNormal (H := P.1)).comp H.subtype
      (∀ x y : H, Commute (f x) (f y)) ∧ ∀ x : H, f x ^ (p - 1) = 1 := by
    by_cases hPc : IsCyclic P
    · exact Or.inl hPc
    exact Or.inr (cyclic_action P h hPc hH)
  obtain ⟨N, hN, hNp⟩ := normal_prime_of_action P hH haction
  exact ⟨p, N, hp, hN, hNp⟩

private theorem lift_supersoluble {G : Type u} [Group G] (N : Subgroup G) [N.Normal] [IsCyclic N]
    (h : IsSupersoluble (G ⧸ N)) : IsSupersoluble G := by
  obtain ⟨n, H, h0, hn, hnormal, hstep⟩ := h
  let f := QuotientGroup.mk' N
  let L : Fin (n + 2) → Subgroup G := Fin.cases ⊥ fun i => (H i).comap f
  refine ⟨n + 1, L, rfl, ?_, ?_, ?_⟩
  · change (H (Fin.last n)).comap f = ⊤
    rw [hn, comap_top]
  · refine Fin.cases ?_ fun i => ?_
    · exact normal_bot
    · exact (hnormal i).comap f
  · refine Fin.cases ?_ fun i => ?_
    · change ⊥ ≤ (H 0).comap f ∧
        ∃ g ∈ (H 0).comap f, ∀ x ∈ (H 0).comap f, ∃ k : ℤ, x * (g ^ k)⁻¹ ∈ (⊥ : Subgroup G)
      rw [h0, MonoidHom.comap_bot, QuotientGroup.ker_mk']
      obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := N)
      refine ⟨bot_le, a, a.2, fun x hx => ?_⟩
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (ha ⟨x, hx⟩)
      refine ⟨k, ?_⟩
      rw [Subgroup.mem_bot, mul_inv_eq_one]
      exact congrArg Subtype.val hk.symm
    · change (H i.castSucc).comap f ≤ (H i.succ).comap f ∧
        ∃ g ∈ (H i.succ).comap f, ∀ x ∈ (H i.succ).comap f,
          ∃ k : ℤ, x * (g ^ k)⁻¹ ∈ (H i.castSucc).comap f
      obtain ⟨hle, g, hg, hs⟩ := hstep i
      obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective N g
      refine ⟨comap_mono hle, a, ?_, fun x hx => ?_⟩
      · change f a ∈ H i.succ
        exact ha.symm ▸ hg
      · obtain ⟨k, hk⟩ := hs (f x) hx
        refine ⟨k, ?_⟩
        change f (x * (a ^ k)⁻¹) ∈ H i.castSucc
        rw [map_mul, map_inv, map_zpow, ha]
        exact hk

private theorem supersoluble_of_complemented_maximals {G : Type u} [Group G] [Finite G]
    (h : ComplementedMaximals G) : IsSupersoluble G := by
  classical
  generalize hn : Nat.card G = n
  induction n using Nat.strong_induction_on generalizing G with
  | ind n ih =>
    subst n
    by_cases hcard : Nat.card G = 1
    · have := (Nat.card_eq_one_iff_unique.mp hcard).1
      exact ⟨0, fun _ => ⊥, rfl, Subsingleton.elim _ _, fun _ => normal_bot,
        fun i => i.elim0⟩
    obtain ⟨p, N, hprime, hN, hNp⟩ := exists_normal_prime h hcard
    have : Fact p.Prime := ⟨hprime⟩
    have : IsCyclic N := isCyclic_of_prime_card hNp
    have hlt : Nat.card (G ⧸ N) < Nat.card G := by
      rw [← N.card_mul_index, ← N.index_eq_card, hNp]
      simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right hprime.one_lt N.index_pos
    exact lift_supersoluble N (ih _ hlt (complemented_maximals_quotient h N hprime hNp) rfl)

/--
**Finite non-supersoluble groups have uncomplemented maximal subgroups of Sylow subgroups.** For
every finite group $G$ that is not supersoluble, there are a prime $p$ and a non-cyclic Sylow
$p$-subgroup $P$ of $G$ with a maximal subgroup $M$ of $P$ that has no proper complement in $G$:
there is no subgroup $K \ne G$ with $MK = G$ and $M \cap K = 1$. This answers Kourovka
Problem 15.81 in the affirmative.

The Kourovka Archive answers 15.81 "Yes, it is" (Wang and Wei).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.81 (A. N.
Skiba); resolution: Wang Yanming and Wei Huaquan, Sci. China Ser. A 47 (2004), no. 1, 96-103,
Kourovka Archive, Problem 15.81 (answer: Yes, it is).
-/
public theorem nonSupersolubleHasUncomplementedSylowMaximal_holds :
    nonSupersolubleHasUncomplementedSylowMaximal := by
  classical
  intro G _ _ hG
  by_contra hn
  apply hG
  apply supersoluble_of_complemented_maximals
  intro p hp P hPc M hM
  obtain ⟨hle, hmax⟩ := coatom_of_map hM
  by_contra hK
  exact hn ⟨p, hp.out, P, hPc, M.map P.1.subtype, hle, hmax, fun ⟨K, _, hmul, hdisj⟩ =>
    hK ⟨K, isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hdisj) hmul⟩⟩

end MathlibExt.GroupTheory.NonSupersolubleUncomplementedMaximalKourovka15Problem81Wanted
