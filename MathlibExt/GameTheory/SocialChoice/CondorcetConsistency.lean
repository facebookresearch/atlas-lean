/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module
public import MathlibExt.GameTheory.SocialChoice.VotingRules
set_option autoImplicit false
namespace MathlibExt.GameTheory.SocialChoice
open Classical
open MathlibExt.Order
open MathlibExt.GameTheory.SocialChoice.ArrowWanted
open scoped BigOperators
@[expose] public section
private theorem not_majorityPrefers_self {Alt Voter : Type*} [Fintype Alt]
    [Fintype Voter] (P : Profile Alt Voter) (a : Alt) :
    ¬ CondorcetCycle.MajorityPrefers P a a := by
  classical
  intro h
  rw [majorityPrefers_iff_netPreference_pos] at h
  rw [netPreference_self] at h
  exact lt_irrefl 0 h
private theorem not_majorityPrefers_of_majorityPrefers {Alt Voter : Type*}
    [Fintype Alt] [Fintype Voter] (P : Profile Alt Voter)
    {a b : Alt} (h : CondorcetCycle.MajorityPrefers P a b) :
    ¬ CondorcetCycle.MajorityPrefers P b a := by
  classical
  rw [majorityPrefers_iff_netPreference_pos] at h ⊢
  rw [netPreference_antisymm P b a] at ⊢
  intro hcon
  omega
private theorem winners_eq_singleton_of_forall_lt {Alt : Type*} [Fintype Alt]
    [DecidableEq Alt] (s : Alt → ℤ) (a : Alt)
    (h : ∀ b, b ≠ a → s b < s a) : winners s = {a} := by
  apply Finset.ext
  intro x
  simp only [winners, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro hx
    by_contra hne
    exact not_le_of_gt (h x hne) (hx a)
  · intro hx
    rw [hx]
    intro b
    by_cases hb : b = a
    · subst hb
      exact le_rfl
    · exact le_of_lt (h b hb)
private theorem copelandScore_lt_of_isCondorcetWinner {Alt Voter : Type*}
    [Fintype Alt] [Fintype Voter] (P : Profile Alt Voter)
    {a : Alt} (ha : IsCondorcetWinner P a) (x : Alt) (hx : x ≠ a) :
    copelandScore P x < copelandScore P a := by
  classical
  have hself : ∀ x, ¬ CondorcetCycle.MajorityPrefers P x x :=
    fun x => not_majorityPrefers_self P x
  have hLa : Finset.univ.filter (fun b => CondorcetCycle.MajorityPrefers P b a) = ∅ := by
    apply Finset.filter_false_of_mem
    intro c _
    show ¬ CondorcetCycle.MajorityPrefers P c a
    by_cases hca : c = a
    · rw [hca]
      exact hself a
    · exact not_majorityPrefers_of_majorityPrefers P (ha c hca)
  have hWa : Finset.univ.filter (fun b => CondorcetCycle.MajorityPrefers P a b) =
      Finset.univ.erase a := by
    apply Finset.ext
    intro c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    by_cases hca : c = a
    · rw [hca]
      exact iff_of_false (hself a) (not_not_intro rfl)
    · exact iff_of_true (ha c hca) hca
  have hmem : a ∈ Finset.univ.filter (fun b => CondorcetCycle.MajorityPrefers P b x) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ha x hx
  have hsub : Finset.univ.filter (fun b => CondorcetCycle.MajorityPrefers P x b) ⊆
      Finset.univ.erase x := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro hcon
    rw [hcon] at hc
    exact hself x hc
  have hcard_a : (Finset.univ.filter (fun b => CondorcetCycle.MajorityPrefers P a b)).card =
      (Finset.univ : Finset Alt).card - 1 := by
    rw [hWa, Finset.card_erase_of_mem (Finset.mem_univ a)]
  have hcard_La :
      (Finset.univ.filter (fun b => CondorcetCycle.MajorityPrefers P b a)).card = 0 := by
    rw [hLa, Finset.card_empty]
  have hcard_Wx : (Finset.univ.filter (fun b => CondorcetCycle.MajorityPrefers P x b)).card ≤
      (Finset.univ : Finset Alt).card - 1 := by
    calc (Finset.univ.filter (fun b => CondorcetCycle.MajorityPrefers P x b)).card
        ≤ (Finset.univ.erase x).card := Finset.card_le_card hsub
      _ = (Finset.univ : Finset Alt).card - 1 :=
          Finset.card_erase_of_mem (Finset.mem_univ x)
  have hcard_Lx : 1 ≤
      (Finset.univ.filter (fun b => CondorcetCycle.MajorityPrefers P b x)).card := by
    have hsing : ({a} : Finset Alt) ⊆
        Finset.univ.filter (fun b => CondorcetCycle.MajorityPrefers P b x) := by
      intro y hy
      simp only [Finset.mem_singleton] at hy
      rw [hy]
      exact hmem
    calc 1 = ({a} : Finset Alt).card := (Finset.card_singleton a).symm
      _ ≤ (Finset.univ.filter (fun b => CondorcetCycle.MajorityPrefers P b x)).card :=
          Finset.card_le_card hsing
  simp only [copelandScore]
  rw [hcard_a, hcard_La]
  simp only [Nat.cast_zero, sub_zero]
  have h1 : ((Finset.univ.filter (fun b => CondorcetCycle.MajorityPrefers P x b)).card : ℤ) ≤
      (((Finset.univ : Finset Alt).card - 1 : ℕ) : ℤ) := by
    exact_mod_cast hcard_Wx
  have h2 : (1 : ℤ) ≤
      ((Finset.univ.filter (fun b => CondorcetCycle.MajorityPrefers P b x)).card : ℤ) := by
    exact_mod_cast hcard_Lx
  omega
private theorem maximinScore_lt_of_isCondorcetWinner {Alt Voter : Type*}
    [Fintype Alt] [Fintype Voter] [DecidableEq Alt] [Nontrivial Alt]
    (P : Profile Alt Voter) {a : Alt} (ha : IsCondorcetWinner P a) (b : Alt)
    (hb : b ≠ a) :
    maximinScore P b < maximinScore P a := by
  have hpos : 0 < maximinScore P a := by
    have hmem : maximinScore P a ∈
        (Finset.univ.erase a).image (netPreference P a) :=
      Finset.min'_mem _ _
    obtain ⟨c, hc_mem, hc_eq⟩ := Finset.mem_image.mp hmem
    have hc_ne : c ≠ a := (Finset.mem_erase.mp hc_mem).1
    rw [← hc_eq]
    exact (majorityPrefers_iff_netPreference_pos _ _ _).mp (ha c hc_ne)
  have hneg : maximinScore P b < 0 := by
    have ha_mem : a ∈ Finset.univ.erase b :=
      Finset.mem_erase.mpr ⟨Ne.symm hb, Finset.mem_univ a⟩
    have hle : maximinScore P b ≤ netPreference P b a :=
      Finset.min'_le _ _ (Finset.mem_image.mpr ⟨a, ha_mem, rfl⟩)
    have hlt : netPreference P b a < 0 := by
      have h1 : (0 : ℤ) < netPreference P a b :=
        (majorityPrefers_iff_netPreference_pos _ _ _).mp (ha b hb)
      have h2 : netPreference P b a = -netPreference P a b :=
        netPreference_antisymm P b a
      omega
    omega
  omega
/-- Margin formulation of being a Condorcet winner. -/
theorem isCondorcetWinner_iff {Alt Voter : Type*} [Fintype Alt]
    [Fintype Voter] [DecidableEq Alt] (P : Profile Alt Voter) (a : Alt) :
    IsCondorcetWinner P a ↔ ∀ b ≠ a, 0 < netPreference P a b := by
  simp only [IsCondorcetWinner, majorityPrefers_iff_netPreference_pos]
/-- **Copeland is Condorcet-consistent**: the Condorcet winner is the
unique Copeland winner. -/
theorem winners_copelandScore_of_isCondorcetWinner {Alt Voter : Type*}
    [Fintype Alt] [Fintype Voter] [DecidableEq Alt]
    (P : Profile Alt Voter) {a : Alt} (ha : IsCondorcetWinner P a) :
    winners (copelandScore P) = {a} := by
  exact winners_eq_singleton_of_forall_lt _ _
    (fun b hb => copelandScore_lt_of_isCondorcetWinner P ha b hb)
/-- **Maximin is Condorcet-consistent**: the Condorcet winner is the
unique maximin winner. -/
theorem winners_maximinScore_of_isCondorcetWinner {Alt Voter : Type*}
    [Fintype Alt] [Fintype Voter] [DecidableEq Alt] [Nontrivial Alt]
    (P : Profile Alt Voter) {a : Alt} (ha : IsCondorcetWinner P a) :
    winners (maximinScore P) = {a} := by
  exact winners_eq_singleton_of_forall_lt _ _
    (fun b hb => maximinScore_lt_of_isCondorcetWinner P ha b hb)
/-- **Kemeny is Condorcet-consistent**: every Kemeny ranking puts the
Condorcet winner on top (strictly above every other alternative: `r.lt a b`
reads "`a` is ranked above `b`" in the provider's convention). -/
theorem isKemenyRanking_top_of_isCondorcetWinner {Alt Voter : Type*}
    [Fintype Alt] [Fintype Voter] (P : Profile Alt Voter) {a : Alt}
    (ha : IsCondorcetWinner P a) {r : MathlibExt.Order.StrictTotalOrder Alt}
    (hr : IsKemenyRanking P r) (b : Alt) (hb : b ≠ a) :
    r.lt a b := by
  classical
  by_contra hcon
  have hba : r.lt b a := by
    rcases r.total (Ne.symm hb) with h | h
    · exact absurd h hcon
    · exact h
  -- (K0) Alternatives ranked above `a`, and one maximizing `rankAbove`.
  let S := Finset.univ.filter (fun x => r.lt x a)
  have hbS : b ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ b, hba⟩
  obtain ⟨c, hcS, hcmax⟩ := Finset.exists_max_image S (rankAbove r) ⟨b, hbS⟩
  have hca_lt : r.lt c a := (Finset.mem_filter.mp hcS).2
  have hca : c ≠ a := by
    intro hcon2
    rw [hcon2] at hca_lt
    exact r.irrefl a hca_lt
  have hac : a ≠ c := Ne.symm hca
  have hnca : ¬ r.lt a c := fun h => r.irrefl a (r.trans h hca_lt)
  have hadj : ∀ x, r.lt c x → r.lt x a → False := by
    intro x hcx hxa
    have hxS : x ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxa⟩
    have hlt : rankAbove r c < rankAbove r x := by
      have hcB : c ∈ Finset.univ.filter (fun y => r.lt y x) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ c, hcx⟩
      have hsub : Finset.univ.filter (fun y => r.lt y c) ⊆
          (Finset.univ.filter (fun y => r.lt y x)).erase c := by
        intro y hy
        have hyC : r.lt y c := (Finset.mem_filter.mp hy).2
        have hyX : r.lt y x := r.trans hyC hcx
        have hyB : y ∈ Finset.univ.filter (fun y => r.lt y x) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ y, hyX⟩
        have hyne : y ≠ c := by
          intro hcon3
          rw [hcon3] at hyC
          exact r.irrefl c hyC
        exact Finset.mem_erase.mpr ⟨hyne, hyB⟩
      have hcard_le := Finset.card_le_card hsub
      have hcard_erase := Finset.card_erase_of_mem hcB
      have hcard_pos := Finset.card_pos.mpr ⟨c, hcB⟩
      change (Finset.univ.filter (fun y => r.lt y c)).card <
        (Finset.univ.filter (fun y => r.lt y x)).card
      omega
    have hle_rank : rankAbove r x ≤ rankAbove r c := hcmax x hxS
    omega
  have hpair : (a, c) ≠ (c, a) := fun h => hac (congrArg Prod.fst h)
  -- The order obtained by swapping `a` and `c`.
  let s : MathlibExt.Order.StrictTotalOrder Alt :=
    { lt := fun x y => r.lt (Equiv.swap a c x) (Equiv.swap a c y),
      irrefl := by
        intro x h
        exact r.irrefl _ h,
      trans := by
        intro x y z h1 h2
        exact r.trans h1 h2,
      total := by
        intro x y hxy
        have hinj := (Equiv.swap a c).injective
        have hne : Equiv.swap a c x ≠ Equiv.swap a c y := fun h => hxy (hinj h)
        exact r.total hne }
  have hs_red : ∀ x y, s.lt x y = r.lt (Equiv.swap a c x) (Equiv.swap a c y) :=
    fun x y => rfl
  have hswap_a : Equiv.swap a c a = c := by rw [Equiv.swap_apply_left]
  have hswap_c : Equiv.swap a c c = a := by rw [Equiv.swap_apply_right]
  have hswap_eq : ∀ z, z ≠ a → z ≠ c → Equiv.swap a c z = z :=
    fun z h1 h2 => Equiv.swap_apply_of_ne_of_ne h1 h2
  -- (K1) The swapped pair flips.
  have hsac : s.lt a c := by
    rw [hs_red, hswap_a, hswap_c]
    exact hca_lt
  have hnca_s : ¬ s.lt c a := by
    rw [hs_red, hswap_c, hswap_a]
    exact hnca
  -- (K2) Off the swapped pair, `s` agrees with `r`.
  have hK2 : ∀ x y, (x, y) ≠ (a, c) → (x, y) ≠ (c, a) →
      (s.lt x y ↔ r.lt x y) := by
    intro x y h1 h2
    by_cases hxy : x = y
    · rw [hxy]
      have nsy : ¬ s.lt y y := by
        rw [hs_red]
        exact r.irrefl _
      exact iff_of_false nsy (r.irrefl y)
    · by_cases hxa : x = a
      · by_cases hxc : x = c
        · exfalso
          exact hac (hxa.symm.trans hxc)
        · rw [hxa]
          have hya : y ≠ a := fun hy => hxy (hxa.trans hy.symm)
          have hyc : y ≠ c := fun hy => h1 (by rw [hxa, hy])
          rw [hs_red, hswap_a, hswap_eq y hya hyc]
          constructor
          · intro hcy
            by_contra hnay
            have hya' : r.lt y a := by
              rcases r.total (Ne.symm hya) with h | h
              · exact absurd h hnay
              · exact h
            exact hadj y hcy hya'
          · intro hay
            exact r.trans hca_lt hay
      · by_cases hxc : x = c
        · rw [hxc]
          have hyc : y ≠ c := fun hy => hxy (hxc.trans hy.symm)
          have hya : y ≠ a := fun hy => h2 (by rw [hxc, hy])
          rw [hs_red, hswap_c, hswap_eq y hya hyc]
          constructor
          · intro hay
            exact r.trans hca_lt hay
          · intro hcy
            by_contra hnay
            have hya' : r.lt y a := by
              rcases r.total (Ne.symm hya) with h | h
              · exact absurd h hnay
              · exact h
            exact hadj y hcy hya'
        · by_cases hya : y = a
          · rw [hya]
            rw [hs_red, hswap_eq x hxa hxc, hswap_a]
            constructor
            · intro hxc1
              exact r.trans hxc1 hca_lt
            · intro hxa1
              by_contra hnx
              have hcx : r.lt c x := by
                rcases r.total hxc with h | h
                · exact absurd h hnx
                · exact h
              exact hadj x hcx hxa1
          · by_cases hyc : y = c
            · rw [hyc]
              rw [hs_red, hswap_eq x hxa hxc, hswap_c]
              constructor
              · intro hxa1
                by_contra hnx
                have hcx : r.lt c x := by
                  rcases r.total hxc with h | h
                  · exact absurd h hnx
                  · exact h
                exact hadj x hcx hxa1
              · intro hxc1
                exact r.trans hxc1 hca_lt
            · rw [hs_red, hswap_eq x hxa hxc, hswap_eq y hya hyc]
  have hsub : ({(a, c), (c, a)} : Finset (Alt × Alt)) ⊆
      Finset.univ ×ˢ Finset.univ := by
    intro p _
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  have hnotin : (a, c) ∉ ({(c, a)} : Finset (Alt × Alt)) :=
    fun h => hpair (Finset.mem_singleton.mp h)
  -- (K3) Per-voter Kendall-tau difference.
  have hK3 : ∀ u : MathlibExt.Order.StrictTotalOrder Alt,
      (kendallTau u r : ℤ) - (kendallTau u s : ℤ) =
      (if u.lt a c then (1:ℤ) else 0) - (if u.lt c a then (1:ℤ) else 0) := by
    intro u
    have hcard_r : (kendallTau u r : ℤ) =
        ∑ p ∈ (Finset.univ ×ˢ Finset.univ),
          (if u.lt p.1 p.2 ∧ r.lt p.2 p.1 then (1:ℤ) else 0) := by
      unfold kendallTau
      rw [Finset.card_filter, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro p _
      by_cases h : u.lt p.1 p.2 ∧ r.lt p.2 p.1 <;> simp [h]
    have hcard_s : (kendallTau u s : ℤ) =
        ∑ p ∈ (Finset.univ ×ˢ Finset.univ),
          (if u.lt p.1 p.2 ∧ s.lt p.2 p.1 then (1:ℤ) else 0) := by
      unfold kendallTau
      rw [Finset.card_filter, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro p _
      by_cases h : u.lt p.1 p.2 ∧ s.lt p.2 p.1 <;> simp [h]
    have hvanish : ∀ p ∈ (Finset.univ ×ˢ Finset.univ),
        p ∉ ({(a, c), (c, a)} : Finset (Alt × Alt)) →
        ((if u.lt p.1 p.2 ∧ r.lt p.2 p.1 then (1:ℤ) else 0) -
          (if u.lt p.1 p.2 ∧ s.lt p.2 p.1 then (1:ℤ) else 0)) = 0 := by
      intro p _ hpe
      obtain ⟨p1, p2⟩ := p
      have h1 : (p1, p2) ≠ (a, c) := fun h => hpe (by simp [h])
      have h2 : (p1, p2) ≠ (c, a) := fun h => hpe (by simp [h])
      have h1' : (p2, p1) ≠ (a, c) := by
        intro hcon
        apply h2
        have e1 : p2 = a := congrArg Prod.fst hcon
        have e2 : p1 = c := congrArg Prod.snd hcon
        rw [e2, e1]
      have h2' : (p2, p1) ≠ (c, a) := by
        intro hcon
        apply h1
        have e1 : p2 = c := congrArg Prod.fst hcon
        have e2 : p1 = a := congrArg Prod.snd hcon
        rw [e2, e1]
      have hKs : s.lt p2 p1 ↔ r.lt p2 p1 := hK2 p2 p1 h1' h2'
      have hiff : (u.lt p1 p2 ∧ r.lt p2 p1) ↔ (u.lt p1 p2 ∧ s.lt p2 p1) := by
        constructor
        · intro h
          exact ⟨h.1, hKs.mpr h.2⟩
        · intro h
          exact ⟨h.1, hKs.mp h.2⟩
      change ((if u.lt p1 p2 ∧ r.lt p2 p1 then (1:ℤ) else 0) -
        (if u.lt p1 p2 ∧ s.lt p2 p1 then (1:ℤ) else 0)) = 0
      by_cases h : u.lt p1 p2 ∧ r.lt p2 p1
      · have hQ : u.lt p1 p2 ∧ s.lt p2 p1 := hiff.mp h
        simp [h, hQ]
      · have hnQ : ¬ (u.lt p1 p2 ∧ s.lt p2 p1) := fun hQ => h (hiff.mpr hQ)
        simp [h, hnQ]
    have hFac : ((if u.lt a c ∧ r.lt c a then (1:ℤ) else 0) -
        (if u.lt a c ∧ s.lt c a then (1:ℤ) else 0)) =
        (if u.lt a c then (1:ℤ) else 0) := by
      by_cases hU : u.lt a c <;> simp [hU, hca_lt, hnca_s]
    have hFca : ((if u.lt c a ∧ r.lt a c then (1:ℤ) else 0) -
        (if u.lt c a ∧ s.lt a c then (1:ℤ) else 0)) =
        (0 - (if u.lt c a then (1:ℤ) else 0)) := by
      by_cases hU : u.lt c a <;> simp [hU, hnca, hsac]
    have hsum_e : (∑ p ∈ ({(a, c), (c, a)} : Finset (Alt × Alt)),
        ((if u.lt p.1 p.2 ∧ r.lt p.2 p.1 then (1:ℤ) else 0) -
          (if u.lt p.1 p.2 ∧ s.lt p.2 p.1 then (1:ℤ) else 0))) =
        (if u.lt a c then (1:ℤ) else 0) - (if u.lt c a then (1:ℤ) else 0) := by
      rw [Finset.sum_insert hnotin, Finset.sum_singleton]
      change ((if u.lt a c ∧ r.lt c a then (1:ℤ) else 0) -
        (if u.lt a c ∧ s.lt c a then (1:ℤ) else 0)) +
        ((if u.lt c a ∧ r.lt a c then (1:ℤ) else 0) -
          (if u.lt c a ∧ s.lt a c then (1:ℤ) else 0)) =
        (if u.lt a c then (1:ℤ) else 0) - (if u.lt c a then (1:ℤ) else 0)
      rw [hFac, hFca]
      by_cases h1 : u.lt a c <;> by_cases h2 : u.lt c a <;> simp [h1, h2]
    rw [hcard_r, hcard_s, ← Finset.sum_sub_distrib]
    exact (Finset.sum_subset hsub hvanish).symm.trans hsum_e
  -- (K4) Summing over voters gives the net preference.
  have hK4 : (kemenyScore P r : ℤ) - (kemenyScore P s : ℤ) =
      netPreference P a c := by
    have hkr : (kemenyScore P r : ℤ) = ∑ i, ((kendallTau (P i) r : ℕ) : ℤ) := by
      unfold kemenyScore
      rw [Nat.cast_sum]
    have hks : (kemenyScore P s : ℤ) = ∑ i, ((kendallTau (P i) s : ℕ) : ℤ) := by
      unfold kemenyScore
      rw [Nat.cast_sum]
    have hdiff : (kemenyScore P r : ℤ) - (kemenyScore P s : ℤ) =
        ∑ i, ((((kendallTau (P i) r : ℕ) : ℤ) - ((kendallTau (P i) s : ℕ) : ℤ))) := by
      rw [hkr, hks, ← Finset.sum_sub_distrib]
    have hpoint : ∀ i ∈ (Finset.univ : Finset Voter),
        ((kendallTau (P i) r : ℕ) : ℤ) - ((kendallTau (P i) s : ℕ) : ℤ) =
        ((if (P i).lt a c then (1:ℤ) else 0) -
          (if (P i).lt c a then (1:ℤ) else 0)) := by
      intro i _
      exact hK3 (P i)
    have hUac : (∑ i ∈ (Finset.univ : Finset Voter),
        (if (P i).lt a c then (1:ℤ) else 0)) =
        ((Finset.univ.filter (fun i => (P i).lt a c)).card : ℤ) := by
      rw [Finset.card_filter, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : (P i).lt a c <;> simp [h]
    have hUca : (∑ i ∈ (Finset.univ : Finset Voter),
        (if (P i).lt c a then (1:ℤ) else 0)) =
        ((Finset.univ.filter (fun i => (P i).lt c a)).card : ℤ) := by
      rw [Finset.card_filter, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : (P i).lt c a <;> simp [h]
    have hnet : netPreference P a c =
        ((Finset.univ.filter (fun i => (P i).lt a c)).card : ℤ) -
        ((Finset.univ.filter (fun i => (P i).lt c a)).card : ℤ) := rfl
    rw [hdiff, Finset.sum_congr rfl hpoint, Finset.sum_sub_distrib, hUac, hUca, hnet]
  -- (K5) The Condorcet winner's positive margin contradicts minimality.
  have hpos : 0 < netPreference P a c :=
    (majorityPrefers_iff_netPreference_pos P a c).mp (ha c hca)
  have hle : kemenyScore P r ≤ kemenyScore P s := hr s
  omega
private theorem lt_of_kendallTau_eq_zero {Alt : Type*} [Fintype Alt]
    [DecidableEq Alt] {u v : MathlibExt.Order.StrictTotalOrder Alt}
    (h : kendallTau u v = 0) {x y : Alt} (huxy : u.lt x y) :
    v.lt x y := by
  by_contra hvxy
  have hne : x ≠ y := by rintro rfl; exact u.irrefl _ huxy
  rcases v.total hne with h1 | h2
  · exact hvxy h1
  · have hmem : (x, y) ∈ (Finset.univ ×ˢ Finset.univ).filter
        (fun p => u.lt p.1 p.2 ∧ v.lt p.2 p.1) := by
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        true_and]
      exact ⟨huxy, h2⟩
    have hpos : 0 < (((Finset.univ ×ˢ Finset.univ).filter
        (fun p => u.lt p.1 p.2 ∧ v.lt p.2 p.1))).card :=
      Finset.card_pos.mpr ⟨(x, y), hmem⟩
    have hzero : (((Finset.univ ×ˢ Finset.univ).filter
        (fun p => u.lt p.1 p.2 ∧ v.lt p.2 p.1))).card = 0 := h
    omega
private theorem lt_iff_of_kendallTau_eq_zero {Alt : Type*} [Fintype Alt]
    [DecidableEq Alt] {u v : MathlibExt.Order.StrictTotalOrder Alt}
    (h : kendallTau u v = 0) (x y : Alt) :
    u.lt x y ↔ v.lt x y := by
  have h' : kendallTau v u = 0 := (kendallTau_comm u v).symm.trans h
  exact ⟨lt_of_kendallTau_eq_zero h, lt_of_kendallTau_eq_zero h'⟩
/-- **Dodgson is Condorcet-consistent**: the Condorcet winner has Dodgson
score `0`, and every other alternative has positive Dodgson score. -/
theorem dodgsonScore_eq_zero_iff {Alt Voter : Type*} [Fintype Alt]
    [Fintype Voter] [DecidableEq Alt] [Nonempty Voter]
    (P : Profile Alt Voter) (a : Alt) :
    dodgsonScore P a = 0 ↔ IsCondorcetWinner P a := by
  constructor
  · intro h0
    obtain ⟨Q0, hQ0⟩ := exists_isCondorcetWinner (Voter := Voter) a
    have hne : (Set.range fun Q : {Q // IsCondorcetWinner Q a} =>
        profileDist P Q.1).Nonempty :=
      ⟨profileDist P Q0, ⟨Q0, hQ0⟩, rfl⟩
    have hmem : sInf (Set.range fun Q : {Q // IsCondorcetWinner Q a} =>
        profileDist P Q.1) ∈ Set.range fun Q : {Q // IsCondorcetWinner Q a} =>
        profileDist P Q.1 :=
      Nat.sInf_mem hne
    rw [sInf_range] at hmem
    obtain ⟨Q, hQeq⟩ := hmem
    have h0' : (⨅ Q : {Q // IsCondorcetWinner Q a},
        profileDist P Q.1) = 0 := h0
    have hdist : profileDist P Q.1 = 0 := hQeq.trans h0'
    have hzero : ∀ i, kendallTau (P i) (Q.1 i) = 0 := by
      have hsum : ∑ i, kendallTau (P i) (Q.1 i) = 0 := hdist
      intro i
      exact Finset.sum_eq_zero_iff.mp hsum i (Finset.mem_univ i)
    have hPt : ∀ i x y, (P i).lt x y ↔ (Q.1 i).lt x y :=
      fun i x y => lt_iff_of_kendallTau_eq_zero (hzero i) x y
    have hPQ : P = Q.1 := by
      funext i
      apply MathlibExt.Order.StrictTotalOrder.ext
      funext x y
      exact propext (hPt i x y)
    rw [hPQ]
    exact Q.2
  · intro ha
    have hbdd : BddBelow (Set.range fun Q : {Q // IsCondorcetWinner Q a} =>
        profileDist P Q.1) := by
      refine ⟨0, ?_⟩
      intro y hy
      obtain ⟨Q, rfl⟩ := hy
      exact Nat.zero_le _
    have hle : dodgsonScore P a ≤ profileDist P P := ciInf_le hbdd ⟨P, ha⟩
    have hPP : profileDist P P = 0 := by simp [profileDist, kendallTau_self]
    omega
/-- Rank key for the ballot `0` above `1` above `2`. -/
private def bordaRankA : Fin 3 → ℕ := fun x => x.val
/-- Rank key for the ballot `1` above `2` above `0`. -/
private def bordaRankB : Fin 3 → ℕ :=
  fun x => if x = 1 then 0 else if x = 2 then 1 else 2
/-- The ballot ranking `0` above `1` above `2`, best first. -/
private def bordaOrderA : MathlibExt.Order.StrictTotalOrder (Fin 3) where
  lt := fun x y => bordaRankA x < bordaRankA y
  irrefl := fun x => lt_irrefl _
  trans := fun {x y z} h1 h2 => lt_trans h1 h2
  total := fun {x y} h => by
    have hne : bordaRankA x ≠ bordaRankA y :=
      fun heq => h (Fin.ext heq)
    have htri := lt_or_gt_of_ne hne
    cases htri with
    | inl hlt => exact Or.inl hlt
    | inr hgt => exact Or.inr hgt
private theorem bordaOrderB_total : ∀ x y : Fin 3,
    x ≠ y → bordaRankB x < bordaRankB y ∨
      bordaRankB y < bordaRankB x := by
  decide
/-- The ballot ranking `1` above `2` above `0`, best first. -/
private def bordaOrderB : MathlibExt.Order.StrictTotalOrder (Fin 3) where
  lt := fun x y => bordaRankB x < bordaRankB y
  irrefl := fun _x => lt_irrefl _
  trans := fun {_x _y _z} h1 h2 => lt_trans h1 h2
  total := fun {x y} h => bordaOrderB_total x y h
/-- Five-voter, three-alternative witness profile: voters `0, 1, 2`
rank `0` above `1` above `2`; voters `3, 4` rank `1` above `2` above
`0`. Alternative `0` is the Condorcet winner (margins `3` to `2`), but
the Borda scores are `6, 7, 2`. -/
private def bordaWitness : Profile (Fin 3) (Fin 5) :=
  fun i => if i.val < 3 then bordaOrderA else bordaOrderB
private theorem bw_eq_orderA (i : Fin 5) (h : i.val < 3) :
    bordaWitness i = bordaOrderA := by
  unfold bordaWitness
  rw [ite_eq_left h]
private theorem bw_eq_orderB (i : Fin 5) (h : ¬ i.val < 3) :
    bordaWitness i = bordaOrderB := by
  unfold bordaWitness
  rw [ite_eq_right h]
private theorem bw_lt_01 (i : Fin 5) :
    (bordaWitness i).lt 0 1 ↔ i.val < 3 := by
  by_cases h : i.val < 3
  · rw [bw_eq_orderA i h]
    show (0 : Fin 3).val < (1 : Fin 3).val ↔ i.val < 3
    exact iff_of_true (by decide) h
  · rw [bw_eq_orderB i h]
    show bordaRankB 0 < bordaRankB 1 ↔ i.val < 3
    exact iff_of_false (by decide) h
private theorem bw_lt_10 (i : Fin 5) :
    (bordaWitness i).lt 1 0 ↔ ¬ i.val < 3 := by
  by_cases h : i.val < 3
  · rw [bw_eq_orderA i h]
    show (1 : Fin 3).val < (0 : Fin 3).val ↔ ¬ i.val < 3
    exact iff_of_false (by decide) (not_not_intro h)
  · rw [bw_eq_orderB i h]
    show bordaRankB 1 < bordaRankB 0 ↔ ¬ i.val < 3
    exact iff_of_true (by decide) h
private theorem bw_lt_02 (i : Fin 5) :
    (bordaWitness i).lt 0 2 ↔ i.val < 3 := by
  by_cases h : i.val < 3
  · rw [bw_eq_orderA i h]
    show (0 : Fin 3).val < (2 : Fin 3).val ↔ i.val < 3
    exact iff_of_true (by decide) h
  · rw [bw_eq_orderB i h]
    show bordaRankB 0 < bordaRankB 2 ↔ i.val < 3
    exact iff_of_false (by decide) h
private theorem bw_lt_20 (i : Fin 5) :
    (bordaWitness i).lt 2 0 ↔ ¬ i.val < 3 := by
  by_cases h : i.val < 3
  · rw [bw_eq_orderA i h]
    show (2 : Fin 3).val < (0 : Fin 3).val ↔ ¬ i.val < 3
    exact iff_of_false (by decide) (not_not_intro h)
  · rw [bw_eq_orderB i h]
    show bordaRankB 2 < bordaRankB 0 ↔ ¬ i.val < 3
    exact iff_of_true (by decide) h
private theorem bw_filter_lt_01 :
    Finset.univ.filter (fun i : Fin 5 => (bordaWitness i).lt 0 1)
      = {0, 1, 2} := by
  have hcongr : Finset.univ.filter
        (fun i : Fin 5 => (bordaWitness i).lt 0 1)
      = Finset.univ.filter (fun i : Fin 5 => i.val < 3) :=
    Finset.filter_congr (fun i _ => bw_lt_01 i)
  rw [hcongr]
  decide
private theorem bw_filter_lt_10 :
    Finset.univ.filter (fun i : Fin 5 => (bordaWitness i).lt 1 0)
      = {3, 4} := by
  have hcongr : Finset.univ.filter
        (fun i : Fin 5 => (bordaWitness i).lt 1 0)
      = Finset.univ.filter (fun i : Fin 5 => ¬ i.val < 3) :=
    Finset.filter_congr (fun i _ => bw_lt_10 i)
  rw [hcongr]
  decide
private theorem bw_filter_lt_02 :
    Finset.univ.filter (fun i : Fin 5 => (bordaWitness i).lt 0 2)
      = {0, 1, 2} := by
  have hcongr : Finset.univ.filter
        (fun i : Fin 5 => (bordaWitness i).lt 0 2)
      = Finset.univ.filter (fun i : Fin 5 => i.val < 3) :=
    Finset.filter_congr (fun i _ => bw_lt_02 i)
  rw [hcongr]
  decide
private theorem bw_filter_lt_20 :
    Finset.univ.filter (fun i : Fin 5 => (bordaWitness i).lt 2 0)
      = {3, 4} := by
  have hcongr : Finset.univ.filter
        (fun i : Fin 5 => (bordaWitness i).lt 2 0)
      = Finset.univ.filter (fun i : Fin 5 => ¬ i.val < 3) :=
    Finset.filter_congr (fun i _ => bw_lt_20 i)
  rw [hcongr]
  decide
private theorem bw_card_lt_01 :
    (Finset.univ.filter (fun i : Fin 5 => (bordaWitness i).lt 0 1)).card
      = 3 := by
  rw [bw_filter_lt_01]
  decide
private theorem bw_card_lt_10 :
    (Finset.univ.filter (fun i : Fin 5 => (bordaWitness i).lt 1 0)).card
      = 2 := by
  rw [bw_filter_lt_10]
  decide
private theorem bw_card_lt_02 :
    (Finset.univ.filter (fun i : Fin 5 => (bordaWitness i).lt 0 2)).card
      = 3 := by
  rw [bw_filter_lt_02]
  decide
private theorem bw_card_lt_20 :
    (Finset.univ.filter (fun i : Fin 5 => (bordaWitness i).lt 2 0)).card
      = 2 := by
  rw [bw_filter_lt_20]
  decide
private theorem bw_majority_01 :
    CondorcetCycle.MajorityPrefers bordaWitness 0 1 := by
  rw [majorityPrefers_iff_netPreference_pos]
  simp only [netPreference]
  rw [bw_card_lt_01, bw_card_lt_10]
  decide
private theorem bw_majority_02 :
    CondorcetCycle.MajorityPrefers bordaWitness 0 2 := by
  rw [majorityPrefers_iff_netPreference_pos]
  simp only [netPreference]
  rw [bw_card_lt_02, bw_card_lt_20]
  decide
private theorem bw_isCondorcetWinner :
    IsCondorcetWinner bordaWitness 0 := by
  intro b hb
  have hb0 : b.val ≠ 0 :=
    fun h => hb (Fin.ext (by show b.val = (0 : Fin 3).val; rw [h]; rfl))
  have hv2 : b.val = 1 ∨ b.val = 2 := by
    have h3 := b.isLt
    omega
  cases hv2 with
  | inl h1 =>
    have hb1 : b = 1 :=
      Fin.ext (by show b.val = (1 : Fin 3).val; rw [h1]; rfl)
    rw [hb1]
    exact bw_majority_01
  | inr h2 =>
    have hb2 : b = 2 :=
      Fin.ext (by show b.val = (2 : Fin 3).val; rw [h2]; rfl)
    rw [hb2]
    exact bw_majority_02
private theorem bw_innerA0 :
    Finset.univ.filter (fun b : Fin 3 => bordaOrderA.lt 0 b)
      = {1, 2} := by
  have hcongr : Finset.univ.filter (fun b : Fin 3 => bordaOrderA.lt 0 b)
      = Finset.univ.filter (fun b : Fin 3 => (0 : Fin 3).val < b.val) :=
    Finset.filter_congr (fun b _ => Iff.rfl)
  rw [hcongr]
  decide
private theorem bw_innerB0 :
    Finset.univ.filter (fun b : Fin 3 => bordaOrderB.lt 0 b) = ∅ := by
  have hcongr : Finset.univ.filter (fun b : Fin 3 => bordaOrderB.lt 0 b)
      = Finset.univ.filter
        (fun b : Fin 3 => bordaRankB 0 < bordaRankB b) :=
    Finset.filter_congr (fun b _ => Iff.rfl)
  rw [hcongr]
  decide
private theorem bw_innerA1 :
    Finset.univ.filter (fun b : Fin 3 => bordaOrderA.lt 1 b)
      = {2} := by
  have hcongr : Finset.univ.filter (fun b : Fin 3 => bordaOrderA.lt 1 b)
      = Finset.univ.filter (fun b : Fin 3 => (1 : Fin 3).val < b.val) :=
    Finset.filter_congr (fun b _ => Iff.rfl)
  rw [hcongr]
  decide
private theorem bw_innerB1 :
    Finset.univ.filter (fun b : Fin 3 => bordaOrderB.lt 1 b)
      = {2, 0} := by
  have hcongr : Finset.univ.filter (fun b : Fin 3 => bordaOrderB.lt 1 b)
      = Finset.univ.filter
        (fun b : Fin 3 => bordaRankB 1 < bordaRankB b) :=
    Finset.filter_congr (fun b _ => Iff.rfl)
  rw [hcongr]
  decide
private theorem bw_per0 : ∀ i ∈ Finset.univ,
    (Finset.univ.filter (fun b : Fin 3 => (bordaWitness i).lt 0 b)).card =
      (if i.val < 3 then 2 else 0) := by
  intro i _
  by_cases h : i.val < 3
  · rw [ite_eq_left h, bw_eq_orderA i h, bw_innerA0]
    decide
  · rw [ite_eq_right h, bw_eq_orderB i h, bw_innerB0]
    exact Finset.card_empty
private theorem bw_per1 : ∀ i ∈ Finset.univ,
    (Finset.univ.filter (fun b : Fin 3 => (bordaWitness i).lt 1 b)).card =
      (if i.val < 3 then 1 else 2) := by
  intro i _
  by_cases h : i.val < 3
  · rw [ite_eq_left h, bw_eq_orderA i h, bw_innerA1]
    exact Finset.card_singleton 2
  · rw [ite_eq_right h, bw_eq_orderB i h, bw_innerB1]
    decide
private theorem bw_score_zero :
    bordaScore bordaWitness 0 = 6 := by
  simp only [bordaScore]
  rw [Finset.sum_congr rfl bw_per0]
  decide
private theorem bw_score_one :
    bordaScore bordaWitness 1 = 7 := by
  simp only [bordaScore]
  rw [Finset.sum_congr rfl bw_per1]
  decide
private theorem bw_zero_not_mem_winners :
    (0 : Fin 3) ∉ winners (fun a => (bordaScore bordaWitness a : ℤ)) := by
  intro hmem
  simp only [winners, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  have hle := hmem 1
  rw [bw_score_zero, bw_score_one] at hle
  exact absurd hle (by decide)
/-- **Borda is not Condorcet-consistent**: unlike Copeland, maximin,
Kemeny and Dodgson above, Borda can fail to elect the Condorcet winner.
In the explicit five-voter, three-alternative witness, three voters rank
`0` above `1` above `2` and two voters rank `1` above `2` above `0`;
alternative `0` is the Condorcet winner (pairwise margins `3` to `2`),
but the Borda scores are `6` for `0` and `7` for `1`, so `0` is not
a Borda winner at all. (Handbook of Computational Social Choice,
Chapter 2: Borda fails the Condorcet criterion.) -/
theorem exists_isCondorcetWinner_notMem_winners_bordaScore :
    ∃ (P : Profile (Fin 3) (Fin 5)) (a : Fin 3),
      IsCondorcetWinner P a ∧ a ∉ winners (fun x => (bordaScore P x : ℤ)) := by
  exact ⟨bordaWitness, 0, bw_isCondorcetWinner, bw_zero_not_mem_winners⟩
/-- The Borda winner set in the witness above is not the Condorcet
winner alone (corollary of non-membership). -/
theorem exists_isCondorcetWinner_winners_bordaScore_ne :
    ∃ (P : Profile (Fin 3) (Fin 5)) (a : Fin 3),
      IsCondorcetWinner P a ∧
        winners (fun x => (bordaScore P x : ℤ)) ≠ {a} := by
  obtain ⟨P, a, hCW, hnot⟩ :=
    exists_isCondorcetWinner_notMem_winners_bordaScore
  exact ⟨P, a, hCW,
    fun h => hnot (by rw [h]; exact Finset.mem_singleton_self a)⟩
end
end MathlibExt.GameTheory.SocialChoice
