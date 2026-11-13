/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Torsor.Defs
import Mathlib.Data.Nat.Squarefree
import Mathlib.GroupTheory.SpecificGroups.ZGroup

@[expose] public section

namespace MetaMathlibExt

/-! # Szele's criterion for cyclic numbers
-/

private theorem isCyclic_mul_comm_of_isCyclic (G : Type*) [Group G] [IsCyclic G] (x y : G) :
    x * y = y * x := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  simp only [Subgroup.mem_zpowers_iff] at hg
  obtain ⟨a, rfl⟩ := hg x
  obtain ⟨b, rfl⟩ := hg y
  rw [← zpow_add, ← zpow_add, add_comm]

private theorem natCard_multiplicative_zmod (m : ℕ) [NeZero m] :
    Nat.card (Multiplicative (ZMod m)) = m := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

private theorem not_isCyclic_semidirect_of_ne {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N}
    (a : N) (b : G) (h : ⇑(φ b) a ≠ a) : ¬ IsCyclic (N ⋊[φ] G) := by
  intro hc
  haveI := hc
  have hxy := isCyclic_mul_comm_of_isCyclic _ (⟨a, 1⟩ : N ⋊[φ] G) (⟨1, b⟩ : N ⋊[φ] G)
  have hleft : a * ⇑(φ 1) 1 = 1 * ⇑(φ b) a := congrArg SemidirectProduct.left hxy
  simp only [map_one, mul_one, one_mul] at hleft
  exact h hleft.symm

private theorem prime_dvd_sub_one_of_dvd_totient (t m : ℕ) (hm : Squarefree m) (ht : t.Prime)
    (hdiv : t ∣ m.totient) : ∃ s, s.Prime ∧ s ∣ m ∧ t ∣ s - 1 := by
  revert hm hdiv
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro hm hdiv
    by_cases hm1 : m = 1
    · subst hm1
      rw [Nat.totient_one] at hdiv
      exact absurd hdiv ht.not_dvd_one
    · obtain ⟨s, hsprime, hsdvd⟩ := Nat.exists_prime_and_dvd hm1
      have hmpos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · exfalso
          exact (Nat.squarefree_iff_prime_squarefree.mp hm) 2 Nat.prime_two ⟨0, rfl⟩
        · exact h
      have hsub_dvd : m / s ∣ m := ⟨s, (Nat.div_mul_cancel hsdvd).symm⟩
      have hSq_sub : Squarefree (m / s) := by
        intro y hy
        exact hm y (dvd_trans hy hsub_dvd)
      have hsk : s.Coprime (m / s) := by
        rw [hsprime.coprime_iff_not_dvd]
        intro hd
        have hme : s * (m / s) = m := Nat.mul_div_cancel' hsdvd
        have hmul := mul_dvd_mul_left s hd
        rw [hme] at hmul
        exact (Nat.squarefree_iff_prime_squarefree.mp hm) s hsprime hmul
      have hme : s * (m / s) = m := Nat.mul_div_cancel' hsdvd
      have hφm : m.totient = (s - 1) * (m / s).totient := by
        have h2 : (s * (m / s)).totient = (s - 1) * (m / s).totient := by
          rw [Nat.totient_mul hsk, Nat.totient_prime hsprime]
        rwa [hme] at h2
      rw [hφm] at hdiv
      rcases (ht.dvd_mul.mp hdiv) with h | h
      · exact ⟨s, hsprime, hsdvd, h⟩
      · obtain ⟨s', hs'prime, hsdvd', hts'⟩ :=
          ih (m / s) (Nat.div_lt_self hmpos hsprime.one_lt) hSq_sub h
        exact ⟨s', hs'prime, dvd_trans hsdvd' hsub_dvd, hts'⟩

private theorem squarefree_of_coprime_totient (n : ℕ) (hn : 0 < n)
    (h : Nat.gcd n (Nat.totient n) = 1) : Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro r hr hrr
  have hrn : r ∣ n := dvd_trans ⟨r, rfl⟩ hrr
  have hrt : r ∣ n.totient := by
    have hn0 : n ≠ 0 := by omega
    have hrr2 : r ^ 2 ∣ n := by simpa [pow_two] using hrr
    have hj : 2 ≤ n.factorization r :=
      (hr.pow_dvd_iff_le_factorization hn0).mp hrr2
    have hcop_pow : (r ^ n.factorization r).Coprime (n / r ^ n.factorization r) :=
      ((hr.coprime_iff_not_dvd).mpr (Nat.not_dvd_ordCompl hr hn0)).pow_left _
    have hkj : r ^ n.factorization r * (n / r ^ n.factorization r) = n :=
      Nat.ordProj_mul_ordCompl_eq_self n r
    have hφ : n.totient =
        (r ^ (n.factorization r - 1) * (r - 1)) * (n / r ^ n.factorization r).totient := by
      have h2 : (r ^ n.factorization r * (n / r ^ n.factorization r)).totient =
          (r ^ (n.factorization r - 1) * (r - 1)) * (n / r ^ n.factorization r).totient := by
        rw [Nat.totient_mul hcop_pow,
          Nat.totient_prime_pow hr (by omega : 0 < n.factorization r)]
      rwa [hkj] at h2
    have hr1 : r ∣ r ^ (n.factorization r - 1) * (r - 1) :=
      dvd_mul_of_dvd_left (dvd_pow_self r (by omega : n.factorization r - 1 ≠ 0)) _
    exact dvd_trans hr1 ⟨_, hφ⟩
  have hgcd : r ∣ Nat.gcd n n.totient := Nat.dvd_gcd hrn hrt
  rw [h] at hgcd
  exact hr.not_dvd_one hgcd

private theorem exists_nonisCyclic_of_sq_dvd (n r : ℕ) (hn : 0 < n) (hrprime : r.Prime)
    (hrrdvd : r * r ∣ n) :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G), Fintype.card G = n ∧ ¬ IsCyclic G := by
  have hrpos : 0 < r := hrprime.pos
  have hrn : r ∣ n := dvd_trans ⟨r, rfl⟩ hrrdvd
  have hrle : r ≤ n := Nat.le_of_dvd hn hrn
  have hnpos : 0 < n / r := Nat.div_pos hrle hrpos
  haveI : NeZero (n / r) := ⟨by omega⟩
  haveI : NeZero r := ⟨by omega⟩
  obtain ⟨k, hk⟩ := hrrdvd
  have hdiv_eq : n / r = r * k := by
    rw [hk, mul_assoc]
    exact Nat.mul_div_cancel_left _ hrpos
  have h1 : r ∣ n / r := ⟨k, hdiv_eq⟩
  have hcop : ¬ (n / r).Coprime r := by
    intro hc
    have hgcd := hc.gcd_eq_one
    have hdvd : r ∣ Nat.gcd (n / r) r := Nat.dvd_gcd h1 dvd_rfl
    rw [hgcd] at hdvd
    exact hrprime.not_dvd_one hdvd
  refine ⟨Multiplicative (ZMod (n / r)) × Multiplicative (ZMod r),
    inferInstance, inferInstance, ?_, ?_⟩
  · rw [Fintype.card_prod, Fintype.card_multiplicative, Fintype.card_multiplicative,
      ZMod.card, ZMod.card, Nat.div_mul_cancel hrn]
  · intro hG
    have hcc := (Group.isCyclic_prod_iff.mp hG).2.2
    rw [natCard_multiplicative_zmod, natCard_multiplicative_zmod] at hcc
    exact hcop hcc

private theorem exists_nonisCyclic_of_dvd_totient (n p : ℕ) (hn : 0 < n) (hpprime : p.Prime)
    (hpn : p ∣ n) (hpφ : p ∣ Nat.totient n) (hsq : ¬ ∃ r, r.Prime ∧ r * r ∣ n) :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G), Fintype.card G = n ∧ ¬ IsCyclic G := by
  have hp2 : 2 ≤ p := hpprime.two_le
  have hppos : 0 < p := by omega
  haveI : Fact p.Prime := Fact.mk hpprime
  have hpm : ¬ p ∣ n / p := by
    intro hd
    obtain ⟨t, ht⟩ := hd
    have hme : n / p * p = n := Nat.div_mul_cancel hpn
    rw [ht] at hme
    exact hsq ⟨p, hpprime, t, by rw [← hme]; ring⟩
  have hcop_pm : p.Coprime (n / p) := (hpprime.coprime_iff_not_dvd).mpr hpm
  have hple : p ≤ n := Nat.le_of_dvd hn hpn
  have hmpos : 0 < n / p := Nat.div_pos hple hppos
  haveI : NeZero (n / p) := ⟨by omega⟩
  have hn_eq : n = p * (n / p) := (Nat.mul_div_cancel' hpn).symm
  have hφn : (p * (n / p)).totient = (p - 1) * (n / p).totient := by
    rw [Nat.totient_mul hcop_pm, Nat.totient_prime hpprime]
  have hpφ' : p ∣ (p * (n / p)).totient := by
    rw [← hn_eq]
    exact hpφ
  rw [hφn] at hpφ'
  have hpφm : p ∣ (n / p).totient := by
    rcases (hpprime.dvd_mul.mp hpφ') with h | h
    · exfalso
      have hle : p ≤ p - 1 := Nat.le_of_dvd (by omega) h
      omega
    · exact h
  haveI hNcyc : IsCyclic (Multiplicative (ZMod (n / p))) :=
    isCyclic_multiplicative_iff.mpr inferInstance
  have hNcard : Nat.card (Multiplicative (ZMod (n / p))) = n / p :=
    natCard_multiplicative_zmod _
  have e := IsCyclic.mulAutMulEquiv (Multiplicative (ZMod (n / p)))
  rw [hNcard] at e
  obtain ⟨u, hu⟩ : ∃ _ : (ZMod (n / p))ˣ, orderOf _ = p :=
    exists_prime_orderOf_dvd_card p (by
      rw [ZMod.card_units_eq_totient]
      exact hpφm)
  have hσ : orderOf (e.symm u) = p := by
    have h := orderOf_injective (e.symm.toMonoidHom) (e.symm.injective) u
    exact h.trans hu
  haveI : Fintype ↥(Subgroup.zpowers (e.symm u)) := inferInstance
  haveI : Fintype (Multiplicative (ZMod (n / p)) ⋊[(Subgroup.zpowers (e.symm u)).subtype]
    ↥(Subgroup.zpowers (e.symm u))) :=
    Fintype.ofEquiv _ SemidirectProduct.equivProd.symm
  have hHcard : Fintype.card (Multiplicative (ZMod (n / p)) ⋊[(Subgroup.zpowers (e.symm u)).subtype]
      ↥(Subgroup.zpowers (e.symm u))) = n := by
    rw [← Nat.card_eq_fintype_card, SemidirectProduct.card, hNcard, Nat.card_zpowers, hσ]
    exact Nat.div_mul_cancel hpn
  have hσne : e.symm u ≠ 1 := by
    intro hcon
    have h1 : orderOf (e.symm u) = 1 := by
      rw [hcon]
      exact orderOf_one
    omega
  obtain ⟨a, ha⟩ : ∃ a, (e.symm u) a ≠ a := by
    by_contra hc
    push Not at hc
    apply hσne
    apply MulEquiv.ext
    intro a
    rw [MulAut.one_apply]
    exact hc a
  have h : ⇑(Subgroup.zpowers (e.symm u)).subtype ⟨e.symm u, Subgroup.mem_zpowers _⟩ a
      ≠ a := ha
  refine ⟨Multiplicative (ZMod (n / p)) ⋊[(Subgroup.zpowers (e.symm u)).subtype]
    ↥(Subgroup.zpowers (e.symm u)), inferInstance, inferInstance, hHcard, ?_⟩
  exact not_isCyclic_semidirect_of_ne a ⟨e.symm u, Subgroup.mem_zpowers _⟩ h

/--
**Szele's criterion for cyclic numbers.** Let $n$ be a positive integer. Every group of order $n$
is cyclic if and only if $n$ is relatively prime to $\varphi(n)$, that is,
$\gcd(n, \varphi(n)) = 1$, where $\varphi$ is Euler's totient function.

Source: Joel E. Cohen, "Conjectures about Primes and Cyclic Numbers,"
Journal of Integer Sequences 28 (2025), Article 25.4.7, Szele's criterion,
lines 107–114,
https://cs.uwaterloo.ca/journals/JIS/VOL28/Cohen/cohen41.tex
(citing T. Szele, "Über die endlichen Ordnungszahlen, zu denen nur eine
Gruppe gehört," Comment. Math. Helv. 20 (1947), 265–267).
Proves `Wanted` entry `szele_cyclic_number_criterion`.
-/
theorem szele_cyclic_number_criterion
    (n : ℕ) (hn : 0 < n) :
    (∀ (G : Type*) [Group G] [Fintype G], Fintype.card G = n → IsCyclic G) ↔
      Nat.gcd n (Nat.totient n) = 1 := by
  constructor
  · intro hAll
    by_contra hne
    obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have hpn : p ∣ n := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
    have hpφ : p ∣ n.totient := dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
    by_cases hsq : ∃ r, r.Prime ∧ r * r ∣ n
    · obtain ⟨r, hrprime, hrr⟩ := hsq
      obtain ⟨G₀, _, _, hcard, hncyc⟩ :=
        exists_nonisCyclic_of_sq_dvd n r hn hrprime hrr
      have hcard1 : Fintype.card (ULift.{u_1, 0} G₀) = n :=
        (Fintype.card_ulift G₀).trans hcard
      have hcyc : IsCyclic (ULift.{u_1, 0} G₀) := hAll _ hcard1
      have hcyc0 : IsCyclic G₀ := ((MulEquiv.ulift (α := G₀)).isCyclic).mp hcyc
      exact hncyc hcyc0
    · obtain ⟨G₀, _, _, hcard, hncyc⟩ :=
        exists_nonisCyclic_of_dvd_totient n p hn hpprime hpn hpφ hsq
      have hcard1 : Fintype.card (ULift.{u_1, 0} G₀) = n :=
        (Fintype.card_ulift G₀).trans hcard
      have hcyc : IsCyclic (ULift.{u_1, 0} G₀) := hAll _ hcard1
      have hcyc0 : IsCyclic G₀ := ((MulEquiv.ulift (α := G₀)).isCyclic).mp hcyc
      exact hncyc hcyc0
  · intro hgcd G _ _ hcard
    have hSq : Squarefree n := squarefree_of_coprime_totient n hn hgcd
    have hcardN : Nat.card G = n := by
      rw [Nat.card_eq_fintype_card]
      exact hcard
    have hZN : Squarefree (Nat.card G) := by
      rw [hcardN]
      exact hSq
    have hZ : IsZGroup G := IsZGroup.of_squarefree hZN
    obtain ⟨N, H, φ, eGH, hHcyc, hNcyc, hcop⟩ := isZGroup_iff_exists_mulEquiv.mp hZ
    have hH : Nat.card ↥H ∣ n := by
      have h := Subgroup.card_subgroup_dvd_card H
      rwa [hcardN] at h
    have hN : Nat.card ↥N ∣ n := by
      have h := Subgroup.card_subgroup_dvd_card N
      rwa [hcardN] at h
    have hNsq : Squarefree (Nat.card ↥N) := by
      intro y hy
      exact hSq y (dvd_trans hy hN)
    have hNpos : 0 < Nat.card ↥N := Nat.card_pos
    haveI : NeZero (Nat.card ↥N) := ⟨Nat.card_pos.ne'⟩
    haveI := hNcyc
    have hNt : Nat.card (MulAut ↥N) = (Nat.card ↥N).totient := by
      rw [Nat.card_congr (IsCyclic.mulAutMulEquiv ↥N).toEquiv, Nat.card_eq_fintype_card,
        ZMod.card_units_eq_totient]
    have hφtriv : φ = 1 := by
      apply MonoidHom.ext
      intro g
      have h1 : orderOf (φ g) ∣ Nat.card ↥H :=
        dvd_trans (orderOf_map_dvd φ g) (orderOf_dvd_natCard g)
      have h2 : orderOf (φ g) ∣ (Nat.card ↥N).totient := by
        rw [← hNt]
        exact orderOf_dvd_natCard (φ g)
      have hgcd1 : Nat.gcd (Nat.card ↥H) (Nat.card ↥N).totient = 1 := by
        by_contra hne
        obtain ⟨t, htprime, htdvd⟩ := Nat.exists_prime_and_dvd hne
        have htH : t ∣ Nat.card ↥H := dvd_trans htdvd (Nat.gcd_dvd_left _ _)
        have htT : t ∣ (Nat.card ↥N).totient := dvd_trans htdvd (Nat.gcd_dvd_right _ _)
        obtain ⟨s, hsprime, hsdvd, hts⟩ := prime_dvd_sub_one_of_dvd_totient _ _ hNsq htprime htT
        have hsn : s ∣ n := dvd_trans hsdvd hN
        have htn : t ∣ n := dvd_trans htH hH
        have hspn : ¬ s ∣ n / s := by
          intro hd
          have hme : s * (n / s) = n := Nat.mul_div_cancel' hsn
          have hmul := mul_dvd_mul_left s hd
          rw [hme] at hmul
          exact (Nat.squarefree_iff_prime_squarefree.mp hSq) s hsprime hmul
        have hcop_sn : s.Coprime (n / s) := (hsprime.coprime_iff_not_dvd).mpr hspn
        have hn_eq_s : n = s * (n / s) := (Nat.mul_div_cancel' hsn).symm
        have hs1dvd : s - 1 ∣ n.totient := by
          have hφs : (s * (n / s)).totient = (s - 1) * (n / s).totient := by
            rw [Nat.totient_mul hcop_sn, Nat.totient_prime hsprime]
          have hφs' : n.totient = (s - 1) * (n / s).totient := by
            rwa [← hn_eq_s] at hφs
          exact ⟨_, hφs'⟩
        have htφ : t ∣ n.totient := dvd_trans hts hs1dvd
        have htgcd : t ∣ Nat.gcd n n.totient := Nat.dvd_gcd htn htφ
        rw [hgcd] at htgcd
        exact htprime.not_dvd_one htgcd
      have hfin : orderOf (φ g) = 1 := by
        have h := Nat.dvd_gcd h1 h2
        rw [hgcd1] at h
        exact Nat.dvd_one.mp h
      have h01 : φ g = 1 := orderOf_eq_one_iff.mp hfin
      exact h01.trans (MonoidHom.one_apply g).symm
    subst hφtriv
    have hprod : IsCyclic (↥N × ↥H) := Group.isCyclic_prod_iff.mpr ⟨hNcyc, hHcyc, hcop⟩
    have hsemi : IsCyclic (↥N ⋊[1] ↥H) :=
      (MulEquiv.isCyclic SemidirectProduct.mulEquivProd).mpr hprod
    exact (MulEquiv.isCyclic eGH).mpr hsemi

end MetaMathlibExt
