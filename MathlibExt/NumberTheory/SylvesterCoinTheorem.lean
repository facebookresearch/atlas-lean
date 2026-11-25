/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring.RingNF

@[expose] public section

namespace MetaMathlibExt

/--
**Sylvester's coin theorem.** Let $a$ and $b$ be coprime natural numbers. Then the number of
natural numbers $n$ that cannot be written as $n = ax + by$ with natural numbers $x, y$ is
$(a - 1)(b - 1)/2$.

Subtraction here is truncated at $0$: if $a = 0$ or $b = 0$, coprimality forces the other number
to be $1$, every natural number is representable, and both sides are $0$.

Source: J. J. Sylvester on the Frobenius coin problem (1882); the count of gaps is
`(a - 1) * (b - 1) / 2` for coprime `a b`.
-/
theorem sylvester_coin_theorem
    (a b : ℕ) (hab : Nat.Coprime a b) :
    {n : ℕ | ¬ ∃ x y : ℕ, n = a * x + b * y}.ncard =
      (a - 1) * (b - 1) / 2 := by
  rcases eq_or_ne a 0 with rfl | ha0
  · have hb1 : b = 1 := (Nat.coprime_zero_left b).mp hab
    subst hb1
    have hset : {n : ℕ | ¬ ∃ x y : ℕ, n = 0 * x + 1 * y} = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro n hn
      exact hn ⟨0, n, by simp⟩
    rw [hset, Set.ncard_empty]
  rcases eq_or_ne b 0 with rfl | hb0
  · have ha1 : a = 1 := (Nat.coprime_zero_right a).mp hab
    subst ha1
    have hset : {n : ℕ | ¬ ∃ x y : ℕ, n = 1 * x + 0 * y} = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro n hn
      exact hn ⟨n, 0, by simp⟩
    rw [hset, Set.ncard_empty]
  rcases eq_or_ne a 1 with rfl | ha1
  · have hset : {n : ℕ | ¬ ∃ x y : ℕ, n = 1 * x + b * y} = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro n hn
      exact hn ⟨n, 0, by simp⟩
    rw [hset, Set.ncard_empty]
    simp
  rcases eq_or_ne b 1 with rfl | hb1
  · have hset : {n : ℕ | ¬ ∃ x y : ℕ, n = a * x + 1 * y} = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro n hn
      exact hn ⟨0, n, by simp⟩
    rw [hset, Set.ncard_empty]
    simp
  have ha2 : 2 ≤ a := by omega
  have hb2 : 2 ≤ b := by omega
  have haPos : 0 < a := by omega
  have hbPos : 0 < b := by omega
  obtain ⟨binv, hbinv_lt, hbinv_eq⟩ :=
    Nat.exists_mul_mod_eq_one_of_coprime hab.symm (by omega : 1 < a)
  have hbinv_eq' : binv * b % a = 1 := by rw [Nat.mul_comm]; exact hbinv_eq
  set y : ℕ → ℕ := fun r => (r * binv) % a with hy_def
  have hy_lt : ∀ r, y r < a := fun r => by
    simp only [hy_def]; exact Nat.mod_lt _ haPos
  have hy_mod : ∀ r, b * y r % a = r % a := by
    intro r
    have h1 : b * y r % a = b * (r * binv) % a := by
      simp only [hy_def]; exact Nat.mul_mod_mod b (r * binv) a
    have h2 : b * (r * binv) = r * (b * binv) := by ring
    have h3 : r * (b * binv) % a = r % a := by
      rw [Nat.mul_mod, hbinv_eq]; simp
    rw [h1, h2, h3]
  have hy_eq : ∀ r, r < a → b * y r % a = r := by
    intro r hr; rw [hy_mod, Nat.mod_eq_of_lt hr]
  set yinv : ℕ → ℕ := fun s => (s * b) % a with hyinv_def
  have hyinv_lt : ∀ s, yinv s < a := fun s => by
    simp only [hyinv_def]; exact Nat.mod_lt _ haPos
  have hy_yinv : ∀ r, r < a → yinv (y r) = r := by
    intro r hr
    simp only [hyinv_def]
    rw [Nat.mul_comm (y r) b]
    exact hy_eq r hr
  have h_yinv_y : ∀ s, s < a → y (yinv s) = s := by
    intro s hs
    have e3 : (s * b) * binv = s * (b * binv) := by ring
    simp only [hy_def, hyinv_def]
    rw [Nat.mod_mul_mod, e3, Nat.mul_mod, hbinv_eq]
    simp [Nat.mod_eq_of_lt hs]
  have hsum_y : ∑ r ∈ Finset.range a, y r = ∑ r ∈ Finset.range a, r := by
    apply Finset.sum_bij (fun r _ => y r)
    · intro r hr
      exact Finset.mem_range.mpr (hy_lt r)
    · intro r1 hr1 r2 hr2 h
      have h1 : r1 < a := Finset.mem_range.mp hr1
      have h2 : r2 < a := Finset.mem_range.mp hr2
      have hcon : yinv (y r1) = yinv (y r2) := by rw [h]
      rw [hy_yinv r1 h1, hy_yinv r2 h2] at hcon
      exact hcon
    · intro s hs
      have hs_lt : s < a := Finset.mem_range.mp hs
      exact ⟨yinv s, Finset.mem_range.mpr (hyinv_lt s), h_yinv_y s hs_lt⟩
    · intro r hr; rfl
  have hle : ∀ r, r < a → r ≤ b * y r := by
    intro r hr
    calc r = b * y r % a := (hy_eq r hr).symm
      _ ≤ b * y r := Nat.mod_le _ _
  have hdvd : ∀ r, r < a → a ∣ (b * y r - r) := by
    intro r hr
    have hle_r := hle r hr
    have hmod : r ≡ b * y r [MOD a] := Eq.symm (hy_mod r)
    exact (Nat.modEq_iff_dvd' hle_r).mp hmod
  set c : ℕ → ℕ := fun r => (b * y r - r) / a with hc_def
  have hc_mul : ∀ r, r < a → c r * a = b * y r - r := by
    intro r hr
    simp only [hc_def]
    exact Nat.div_mul_cancel (hdvd r hr)
  have hc_add : ∀ r, r < a → c r * a + r = b * y r := by
    intro r hr
    have h1 := hc_mul r hr
    have h2 := hle r hr
    omega
  have hcancel : ∀ u, binv * (b * u) % a = u % a := by
    intro u
    have e1 : binv * (b * u) = u * (binv * b) := by ring
    rw [e1, Nat.mul_mod, hbinv_eq']
    simp
  have hrepr : ∀ n, (∃ x y0, n = a * x + b * y0) ↔ b * y (n % a) ≤ n := by
    intro n
    constructor
    · rintro ⟨x, y0, rfl⟩
      have hr_lt : (a * x + b * y0) % a < a := Nat.mod_lt _ haPos
      set r := (a * x + b * y0) % a with hr_def
      have h_nmod : (a * x + b * y0) % a = b * y0 % a := by
        have : a * x + b * y0 = b * y0 + a * x := by ring
        rw [this]
        exact Nat.add_mul_mod_self_left _ _ _
      have h_yr : b * y r % a = (a * x + b * y0) % a := by
        rw [hy_eq r hr_lt]
      have h_eq : b * y0 % a = b * y r % a := by
        rw [← h_nmod, ← h_yr]
      have h_congr : binv * (b * y0) % a = binv * (b * y r) % a := by
        have e1 : binv * (b * y0) % a = (binv % a * (b * y0 % a)) % a :=
          Nat.mul_mod _ _ _
        have e2 : binv * (b * y r) % a = (binv % a * (b * y r % a)) % a :=
          Nat.mul_mod _ _ _
        rw [e1, e2, h_eq]
      have h1 : binv * (b * y0) % a = y0 % a := hcancel y0
      have h2 : binv * (b * y r) % a = y r % a := hcancel (y r)
      have h_y0_eq : y0 % a = y r % a := by rw [← h1, ← h2, h_congr]
      have h_yr_eq : y r = y0 % a := by
        have : y r % a = y r := Nat.mod_eq_of_lt (hy_lt r)
        rw [← this, ← h_y0_eq]
      have h_le1 : y r ≤ y0 := by
        rw [h_yr_eq]
        exact Nat.mod_le _ _
      have h_le2 : b * y r ≤ b * y0 :=
        Nat.mul_le_mul_left b h_le1
      have h_le3 : b * y0 ≤ a * x + b * y0 := Nat.le_add_left _ _
      omega
    · intro h_le
      set r := n % a with hr_def
      have hr_lt : r < a := Nat.mod_lt _ haPos
      have hmod : b * y r % a = n % a := by
        rw [hy_eq r hr_lt]
      have hmod' : b * y r ≡ n [MOD a] := hmod
      have hdvd_n : a ∣ (n - b * y r) := (Nat.modEq_iff_dvd' h_le).mp hmod'
      have hdiv : (n - b * y r) / a * a = n - b * y r :=
        Nat.div_mul_cancel hdvd_n
      refine ⟨(n - b * y r) / a, y r, ?_⟩
      have hadd : n - b * y r + b * y r = n := Nat.sub_add_cancel h_le
      calc n = n - b * y r + b * y r := hadd.symm
        _ = (n - b * y r) / a * a + b * y r := by rw [hdiv]
        _ = a * ((n - b * y r) / a) + b * y r := by rw [Nat.mul_comm]
  -- fibers
  set F : ℕ → Finset ℕ := fun r => (Finset.range (c r)).image (fun t => r + a * t)
    with hF_def
  have hF_inj : ∀ r, Function.Injective (fun t => r + a * t) := by
    intro r t1 t2 h
    have h2 : a * t1 = a * t2 := Nat.add_left_cancel h
    exact mul_left_cancel₀ ha0 h2
  have hF_card : ∀ r, r < a → (F r).card = c r := by
    intro r hr
    simp only [hF_def]
    rw [Finset.card_image_of_injective _ (hF_inj r), Finset.card_range]
  have h_disj : Set.PairwiseDisjoint (↑(Finset.range a) : Set ℕ) F := by
    intro r1 hr1 r2 hr2 hne
    have hr1_lt : r1 < a := Finset.mem_range.mp (Finset.mem_coe.mp hr1)
    have hr2_lt : r2 < a := Finset.mem_range.mp (Finset.mem_coe.mp hr2)
    show Disjoint (F r1) (F r2)
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    obtain ⟨t1, _, ht1⟩ := Finset.mem_image.mp hn1
    obtain ⟨t2, _, ht2⟩ := Finset.mem_image.mp hn2
    have h1 : n % a = r1 := by
      rw [← ht1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr1_lt]
    have h2 : n % a = r2 := by
      rw [← ht2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr2_lt]
    exact hne (h1.symm.trans h2)
  set Gf : Finset ℕ := (Finset.range a).biUnion F with hGf_def
  have hSet_eq : (↑Gf : Set ℕ) = {n | ¬ ∃ x y0, n = a * x + b * y0} := by
    ext n
    simp only [hGf_def, Finset.mem_coe, Finset.mem_biUnion]
    constructor
    · rintro ⟨r, hr, hn⟩
      have hr_lt : r < a := Finset.mem_range.mp hr
      obtain ⟨t, ht, h_n⟩ := Finset.mem_image.mp hn
      have h_tlt : t < c r := Finset.mem_range.mp ht
      have h_nmod : n % a = r := by
        rw [← h_n, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr_lt]
      have h_alt : a * t < a * c r := (Nat.mul_lt_mul_left haPos).mpr h_tlt
      have h_r_ac : r + a * c r = b * y r := by
        have h_add := hc_add r hr_lt
        calc r + a * c r = a * c r + r := by ac_rfl
          _ = c r * a + r := by rw [Nat.mul_comm]
          _ = b * y r := h_add
      have h_nlt : n < b * y r := by
        calc n = r + a * t := h_n.symm
          _ < r + a * c r := Nat.add_lt_add_left h_alt r
          _ = b * y r := h_r_ac
      intro h_ex
      obtain ⟨x, y0, hn_eq⟩ := h_ex
      have h_le : b * y (n % a) ≤ n := (hrepr n).mp ⟨x, y0, hn_eq⟩
      rw [h_nmod] at h_le
      exact absurd h_le (Nat.not_le_of_gt h_nlt)
    · intro hn
      have h_le_not : ¬ (b * y (n % a) ≤ n) := fun h => hn ((hrepr n).mpr h)
      have h_lt : n < b * y (n % a) := not_le.mp h_le_not
      have hr_lt : n % a < a := Nat.mod_lt _ haPos
      have hr_mem : n % a ∈ Finset.range a := Finset.mem_range.mpr hr_lt
      have h_n_eq : n % a + a * (n / a) = n := Nat.mod_add_div n a
      have h_r_ac : b * y (n % a) = n % a + a * c (n % a) := by
        have h_add := hc_add (n % a) hr_lt
        calc b * y (n % a) = c (n % a) * a + n % a := h_add.symm
          _ = a * c (n % a) + n % a := by rw [Nat.mul_comm]
          _ = n % a + a * c (n % a) := by ac_rfl
      have h_alt2 : n % a + a * (n / a) < n % a + a * c (n % a) := by
        calc n % a + a * (n / a) = n := h_n_eq
          _ < b * y (n % a) := h_lt
          _ = n % a + a * c (n % a) := h_r_ac
      have h_at_lt : a * (n / a) < a * c (n % a) :=
        Nat.lt_of_add_lt_add_left h_alt2
      have h_tlt : n / a < c (n % a) := Nat.lt_of_mul_lt_mul_left h_at_lt
      exact ⟨n % a, hr_mem,
        Finset.mem_image.mpr ⟨n / a, Finset.mem_range.mpr h_tlt, h_n_eq⟩⟩
  have hcard_Gf : Gf.card = ∑ r ∈ Finset.range a, c r := by
    simp only [hGf_def]
    rw [Finset.card_biUnion h_disj]
    apply Finset.sum_congr rfl
    intro r hr
    exact hF_card r (Finset.mem_range.mp hr)
  have hncard : {n : ℕ | ¬ ∃ x y0, n = a * x + b * y0}.ncard
      = ∑ r ∈ Finset.range a, c r := by
    rw [← hSet_eq, Set.ncard_coe_finset, hcard_Gf]
  have hsum_eq : (∑ r ∈ Finset.range a, c r) * a + ∑ r ∈ Finset.range a, r
      = b * ∑ r ∈ Finset.range a, r := by
    have h1 : ∑ r ∈ Finset.range a, (c r * a + r)
        = ∑ r ∈ Finset.range a, (b * y r) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact hc_add r (Finset.mem_range.mp hr)
    rw [Finset.sum_add_distrib] at h1
    have h2 : ∑ r ∈ Finset.range a, c r * a
        = (∑ r ∈ Finset.range a, c r) * a := by
      rw [Finset.sum_mul]
    have h3 : ∑ r ∈ Finset.range a, b * y r
        = b * ∑ r ∈ Finset.range a, r := by
      rw [← Finset.mul_sum, hsum_y]
    rw [h2, h3] at h1
    exact h1
  have h_Sa : (∑ r ∈ Finset.range a, c r) * a
      = (b - 1) * ∑ r ∈ Finset.range a, r := by
    have hbT : b * ∑ r ∈ Finset.range a, r
        = (b - 1) * ∑ r ∈ Finset.range a, r + ∑ r ∈ Finset.range a, r := by
      have hb_eq : b = (b - 1) + 1 := by omega
      calc b * ∑ r ∈ Finset.range a, r
          = ((b - 1) + 1) * ∑ r ∈ Finset.range a, r := by rw [← hb_eq]
        _ = (b - 1) * ∑ r ∈ Finset.range a, r + ∑ r ∈ Finset.range a, r := by
            rw [Nat.add_mul, Nat.one_mul]
    have h1 : (∑ r ∈ Finset.range a, c r) * a + ∑ r ∈ Finset.range a, r
        = (b - 1) * ∑ r ∈ Finset.range a, r + ∑ r ∈ Finset.range a, r := by
      rw [← hbT]
      exact hsum_eq
    exact Nat.add_right_cancel h1
  have h2T : (∑ r ∈ Finset.range a, r) * 2 = a * (a - 1) :=
    Finset.sum_range_id_mul_two a
  have h3 : (2 * ∑ r ∈ Finset.range a, c r) * a
      = ((a - 1) * (b - 1)) * a := by
    calc (2 * ∑ r ∈ Finset.range a, c r) * a
        = 2 * ((∑ r ∈ Finset.range a, c r) * a) := by ac_rfl
      _ = 2 * ((b - 1) * ∑ r ∈ Finset.range a, r) := by rw [h_Sa]
      _ = (b - 1) * (2 * ∑ r ∈ Finset.range a, r) := by ac_rfl
      _ = (b - 1) * ((∑ r ∈ Finset.range a, r) * 2) := by
          rw [Nat.mul_comm 2 (∑ r ∈ Finset.range a, r)]
      _ = (b - 1) * (a * (a - 1)) := by rw [h2T]
      _ = ((a - 1) * (b - 1)) * a := by ac_rfl
  have h4 : 2 * ∑ r ∈ Finset.range a, c r = (a - 1) * (b - 1) :=
    Nat.eq_of_mul_eq_mul_right haPos h3
  rw [hncard]
  omega

end MetaMathlibExt
