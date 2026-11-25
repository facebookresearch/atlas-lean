/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Data.Finset.Slice
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.FieldSimp

/-!
# Kleitman's theorem on Dedekind numbers

The logarithm to base two of the number of antichains in the Boolean lattice is asymptotic
to the size of its middle layer. The upper bound counts antichains by branching on a set
with many strict subsets. A weighted maximal-chain count bounds the remaining family when
every set has few strict subsets.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.DedekindAntichainCountErdosProblem497Wanted

/-- **Dedekind numbers.** For a natural number $n$, the Dedekind number $M(n)$ is the number of
antichains with respect to inclusion among the subsets of the $n$-element set
$\{0, 1, \dots, n-1\}$, that is, of families of subsets in which no member is contained in a
different member; the empty family and the family $\{\emptyset\}$ are counted. -/
noncomputable def antichainCount (n : ℕ) : ℕ :=
  {F : Finset (Finset (Fin n)) | IsAntichain (· ⊆ ·) (F : Set (Finset (Fin n)))}.ncard

/-- **Erdős Problem 497: the asymptotic statement for Dedekind numbers.** Let $M(n)$ be the
number of antichains with respect to inclusion among the subsets of an $n$-element set (the
Dedekind number). The statement is that $\log_2 M(n) / \binom{n}{\lfloor n/2 \rfloor} \to 1$
as $n \to \infty$; equivalently, $M(n) = 2^{(1 + o(1)) \binom{n}{\lfloor n/2 \rfloor}}$. -/
def antichainCountLogAsymptotic : Prop :=
  Filter.Tendsto (fun n : ℕ => Real.logb 2 (antichainCount n) / (n.choose (n / 2) : ℝ))
    Filter.atTop (nhds 1)

open Finset

private abbrev Family (n : ℕ) := Finset (Finset (Fin n))

open Classical in
private noncomputable def antichains {n : ℕ} (F : Family n) : Finset (Family n) :=
  F.powerset.filter fun A => IsAntichain (· ⊆ ·) (A : Set (Finset (Fin n)))

private lemma count_eq (n : ℕ) : antichainCount n = (antichains (univ : Family n)).card := by
  unfold antichainCount
  rw [← Set.ncard_coe_finset]
  congr 1
  ext A
  simp [antichains]

private lemma count_lower (n : ℕ) : 2 ^ n.choose (n / 2) ≤ antichainCount n := by
  classical
  let L := (univ : Finset (Fin n)).powersetCard (n / 2)
  have h : L.powerset ⊆ antichains (univ : Family n) := by
    intro A hA
    exact mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _),
      (Set.sized_powersetCard _ _).isAntichain.subset (mem_powerset.mp hA)⟩
  simpa [count_eq, L, card_powersetCard] using card_le_card h

private abbrev middle (n : ℕ) := n.choose (n / 2)

private lemma le_interior_choose {n k : ℕ} (hk : 0 < k) (hkn : k < n) : n ≤ n.choose k := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    rcases k with _ | k
    · omega
    by_cases h : k = 0
    · simp [h]
    by_cases h' : k + 1 = n
    · rw [h', ← Nat.choose_symm (n := n + 1) (k := n) (by omega)]
      simp
    rw [Nat.choose_succ_succ']
    have := ih (k := k + 1) (by omega) (by omega)
    have := Nat.choose_pos (n := n) (k := k) (by omega)
    omega

/-- The weighted contribution from a proper sublevel to a chain starting at level `s`. -/
private lemma weight_le {n s t : ℕ} (hts : t < s) (hsn : s ≤ n) :
    (n.choose t : ℝ) / s.choose t ≤ 2 * (middle n : ℝ) / n := by
  have hn : 0 < n := by omega
  have hmid : n ≤ middle n := by simpa using Nat.choose_le_middle 1 n
  have hpos : (0 : ℝ) < s.choose t := Nat.cast_pos.mpr (Nat.choose_pos hts.le)
  rw [div_le_div_iff₀ hpos (Nat.cast_pos.mpr hn)]
  norm_cast
  by_cases ht : t = 0
  · simp [ht]; omega
  by_cases hs : s = n
  · subst s
    nlinarith [Nat.mul_le_mul_left (n.choose t) hmid]
  have h₁ := le_interior_choose (by omega : 0 < t) hts
  have h₂ := le_interior_choose (by omega : 0 < s - t) (by omega : s - t < n - t)
  have h₃ := Nat.choose_mul (n := n) (k := s) (s := t) hts.le
  have h₄ := Nat.choose_le_middle t n
  have h₅ := Nat.choose_le_middle s n
  change _ ≤ 2 * middle n * _
  calc
    n.choose t * n ≤ n.choose t * (s + (n - t)) := Nat.mul_le_mul_left _ (by omega)
    _ ≤ middle n * s.choose t + n.choose t * (n - t).choose (s - t) := by
      rw [Nat.mul_add]
      gcongr
    _ ≤ 2 * middle n * s.choose t := by rw [← h₃]; nlinarith [Nat.mul_le_mul_right (s.choose t) h₅]

/-- Weighted expected number of members of `F` on a descending maximal chain from `s`. -/
private noncomputable def mass {n : ℕ} (F : Family n) (s : Finset (Fin n)) : ℝ :=
  ∑ t ∈ F with t ⊆ s, (n.choose t.card : ℝ) / s.card.choose t.card

/-- Conditioning on the first element erased averages the masses of the immediate subsets. -/
private lemma mass_erase_sum {n : ℕ} (F : Family n) (s : Finset (Fin n)) (hs : s ∉ F) :
    ∑ x ∈ s, mass F (s.erase x) = s.card * mass F s := by
  classical
  simp only [mass, sum_filter, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro t ht
  by_cases h : t ⊆ s
  · have hlt := card_lt_card (ssubset_of_subset_of_ne h (fun he => hs (he ▸ ht)))
    have hpos : 0 < s.card := by omega
    rw [ite_eq_left h]
    simp_rw [subset_erase, and_iff_right h]
    have he : ∀ x ∈ s, (s.erase x).card = s.card - 1 := fun x hx => card_erase_of_mem hx
    rw [sum_congr rfl (fun x hx => by rw [he x hx])]
    rw [← sum_filter, sum_const, nsmul_eq_mul, ← sdiff_eq_filter, card_sdiff_of_subset h]
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    rw [hm] at hlt ⊢
    simp only [Nat.succ_sub_one]
    have hc := Nat.choose_mul_succ_eq m t.card
    have hp₁ := Nat.choose_pos (show t.card ≤ m by omega)
    have hp₂ := Nat.choose_pos hlt.le
    have hc' := congrArg (fun k : ℕ => (k : ℝ)) hc
    push_cast [Nat.cast_sub hlt.le] at *
    field_simp
    nlinarith [congrArg (fun a : ℝ => (n.choose t.card : ℝ) * a) hc']
  · simp [h, subset_erase]

/-- If each member contains at most `d` strict subsets in the family, its size is at most
`(1 + 2d/n)` times the size of the middle layer. -/
private lemma sparse_bound {n d : ℕ} (F : Family n)
    (hF : ∀ s ∈ F, (F.filter fun t => t ⊂ s).card ≤ d) :
    (F.card : ℝ) ≤ middle n + d * (2 * (middle n : ℝ) / n) := by
  classical
  let bound : ℝ := middle n + d * (2 * (middle n : ℝ) / n)
  have hbound : 0 ≤ bound := by dsimp [bound]; positivity
  have aux (s : Finset (Fin n)) : mass F s ≤ bound := by
    induction s using Finset.strongInductionOn with
    | _ s ih =>
      by_cases hs : s ∈ F
      · have hmem : s ∈ F.filter (· ⊆ s) := by simp [hs]
        have herase : (F.filter (· ⊆ s)).erase s = F.filter (· ⊂ s) := by
          ext t
          simp [ssubset_iff_subset_ne, and_assoc, and_comm]
        unfold mass
        rw [← add_sum_erase _ _ hmem, herase]
        simp only [Nat.choose_self, Nat.cast_one, div_one]
        refine add_le_add (by exact_mod_cast Nat.choose_le_middle s.card n) ?_
        calc
          _ ≤ ∑ _t ∈ F.filter (· ⊂ s), 2 * (middle n : ℝ) / n := by
            apply sum_le_sum
            intro t ht
            apply weight_le (card_lt_card (mem_filter.mp ht).2)
            simpa using s.card_le_univ
          _ ≤ _ := by rw [sum_const, nsmul_eq_mul]; gcongr; exact hF s hs
      · by_cases h0 : s = ∅
        · subst s
          have he : (F.filter (· ⊆ (∅ : Finset (Fin n)))) = ∅ :=
            filter_eq_empty_iff.mpr fun t ht h => hs ((subset_empty.mp h) ▸ ht)
          simpa only [mass, he, sum_empty] using hbound
        have hpos : 0 < (s.card : ℝ) :=
          Nat.cast_pos.mpr (card_pos.mpr (nonempty_iff_ne_empty.mpr h0))
        apply le_of_mul_le_mul_left _ hpos
        rw [← mass_erase_sum F s hs, ← nsmul_eq_mul, ← sum_const]
        exact sum_le_sum fun x hx => ih _ (erase_ssubset hx)
  have hp (t : Finset (Fin n)) : (n.choose t.card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by simpa using t.card_le_univ)).ne'
  simpa [mass, bound, hp] using aux univ

/-- Separate antichains according to whether they contain the selected set. -/
private lemma branch {n : ℕ} (F : Family n) (s : Finset (Fin n)) :
    (antichains F).card ≤ (antichains (F.erase s)).card +
      (antichains (F.filter fun t => ¬ t ⊆ s)).card := by
  classical
  let G := F.filter fun t => ¬ t ⊆ s
  have h : antichains F ⊆ antichains (F.erase s) ∪ (antichains G).image (insert s) := by
    intro A hA
    obtain ⟨hAF, ha⟩ := mem_filter.mp hA
    have hsub := mem_powerset.mp hAF
    apply mem_union.mpr
    by_cases hs : s ∈ A
    · right
      refine mem_image.mpr ⟨A.erase s, mem_filter.mpr ⟨mem_powerset.mpr ?_,
        ha.subset (erase_subset _ _)⟩, insert_erase hs⟩
      intro t ht
      obtain ⟨hne, ht⟩ := mem_erase.mp ht
      exact mem_filter.mpr ⟨hsub ht, ha ht hs hne⟩
    · exact Or.inl (mem_filter.mpr ⟨mem_powerset.mpr (subset_erase.mpr ⟨hsub, hs⟩), ha⟩)
  exact (card_le_card h).trans ((card_union_le _ _).trans (Nat.add_le_add_left card_image_le _))

/-- A sparse family contributes at most `2^L` possibilities. At each branching step the
weights `q^(k-1)` and `q^(k-d-1)` sum to at most the parent weight `q^k`. -/
private lemma count_upper {n d : ℕ} {q : ℝ} (hq : 1 ≤ q) (hd : 1 ≤ q ^ d * (q - 1))
    (F : Family n) :
    ((antichains F).card : ℝ) ≤
      (2 : ℝ) ^ ((middle n : ℝ) + d * (2 * (middle n : ℝ) / n)) * q ^ F.card := by
  classical
  let L : ℝ := middle n + d * (2 * (middle n : ℝ) / n)
  change _ ≤ (2 : ℝ) ^ L * _
  induction F using Finset.strongInductionOn with
  | _ F ih =>
    by_cases hF : ∀ s ∈ F, (F.filter fun t => t ⊂ s).card ≤ d
    · calc
        _ ≤ ((2 ^ F.card : ℕ) : ℝ) := by
          exact_mod_cast (card_le_card (filter_subset _ F.powerset)).trans_eq (card_powerset _)
        _ ≤ (2 : ℝ) ^ L := by
          push_cast
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (sparse_bound F hF)
        _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hq)
    · push Not at hF
      obtain ⟨s, hs, hdlt⟩ := hF
      let G := F.filter fun t => ¬ t ⊆ s
      have hGF : G ⊆ F := filter_subset _ _
      have hGs : s ∉ G := by simp [G]
      have hG := ih G (ssubset_of_subset_of_ne hGF (fun h => hGs (h ▸ hs)))
      have hE := ih _ (erase_ssubset hs)
      have hcards : G.card + d ≤ (F.erase s).card := by
        have hpart := F.card_filter_add_card_filter_not (fun t => t ⊆ s)
        have hle : (F.filter (· ⊂ s)).card ≤ (F.filter (· ⊆ s)).card :=
          card_le_card fun t ht => mem_filter.mpr ⟨(mem_filter.mp ht).1, (mem_filter.mp ht).2.le⟩
        dsimp [G]
        rw [card_erase_of_mem hs]
        omega
      have hpow : q ^ G.card ≤ q ^ (F.erase s).card * (q - 1) := calc
        _ ≤ q ^ G.card * (q ^ d * (q - 1)) :=
          le_mul_of_one_le_right (pow_nonneg (by linarith) _) hd
        _ = q ^ (G.card + d) * (q - 1) := by rw [pow_add, mul_assoc]
        _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hq hcards) (by linarith)
      have hsize : (F.erase s).card + 1 = F.card := by
        rw [card_erase_of_mem hs]
        have := card_pos.mpr ⟨s, hs⟩
        omega
      calc
        _ ≤ ((antichains (F.erase s)).card : ℝ) + (antichains G).card := by
          exact_mod_cast branch F s
        _ ≤ (2 : ℝ) ^ L * (q ^ (F.erase s).card + q ^ G.card) := by
          rw [mul_add]; exact add_le_add hE hG
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [← hsize, pow_succ]
          linarith

/-- An elementary lower estimate for the size of the middle layer in even dimension. -/
private lemma central_lower (k : ℕ) (hk : 1 ≤ k) :
    16 ^ k ≤ 4 * k * k.centralBinom ^ 2 := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have h := Nat.succ_mul_centralBinom_succ k
    apply Nat.le_of_mul_le_mul_left _ (show 0 < (k + 1) ^ 2 by positivity)
    calc
      (k + 1) ^ 2 * 16 ^ (k + 1) ≤ 16 * (k + 1) ^ 2 * (4 * k * k.centralBinom ^ 2) := by
        rw [pow_succ 16 k]; nlinarith [Nat.mul_le_mul_left (16 * (k + 1) ^ 2) ih]
      _ ≤ 4 * (k + 1) * (2 * (2 * k + 1) * k.centralBinom) ^ 2 := by
        nlinarith [Nat.zero_le ((k + 1) * k.centralBinom ^ 2)]
      _ = _ := by rw [← h]; ring

private lemma middle_lower (n : ℕ) :
    (2 ^ n) ^ 2 ≤ 16 * (n + 1) * middle n ^ 2 := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [show middle (2 * k) = k.centralBinom by simp [middle, Nat.centralBinom]]
    rw [pow_mul, ← pow_mul, Nat.mul_comm k 2, pow_mul]
    by_cases hk : k = 0
    · simp [hk]
    have := central_lower k (by omega)
    norm_num at *
    nlinarith [Nat.zero_le (k.centralBinom ^ 2)]
  · have h : k.centralBinom ≤ middle (2 * k + 1) := by
      rw [middle, show (2 * k + 1) / 2 = k by omega, Nat.centralBinom]
      exact Nat.choose_le_choose _ (by omega)
    by_cases hk : k = 0
    · subst k; decide
    have hpow : (2 ^ (2 * k + 1)) ^ 2 = 4 * 16 ^ k := by
      rw [pow_succ 2 (2 * k), mul_pow, pow_mul 2 2 k, ← pow_mul, Nat.mul_comm k 2, pow_mul]
      ring
    rw [hpow]
    calc
      _ ≤ 4 * (4 * k * k.centralBinom ^ 2) := Nat.mul_le_mul_left 4 (central_lower k (by omega))
      _ ≤ _ := by
        rw [← Nat.mul_assoc]
        exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left h _)

/-- For `m` of order `n^(1/8)`, deleting `m^7` subsets offsets the other branch. -/
private lemma branch_factor (m : ℕ) (hm : 5 ≤ m) :
    1 ≤ (1 + 1 / (m : ℝ) ^ 5) ^ (m ^ 7) * ((1 + 1 / (m : ℝ) ^ 5) - 1) := by
  let q : ℝ := 1 + 1 / (m : ℝ) ^ 5
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have h₂ : 2 ≤ q ^ (m ^ 5) := by
    have hnonneg : 0 ≤ 1 / (m : ℝ) ^ 5 := by positivity
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 / (m : ℝ) ^ 5 by linarith) (m ^ 5)
    norm_num [q, hm'.ne', one_div] at h ⊢
    exact h
  have hmpow : (m : ℝ) ≤ 2 ^ m := by
    exact_mod_cast (Nat.lt_two_pow_self (n := m)).le
  have hlarge : (m : ℝ) ^ 5 ≤ q ^ (m ^ 7) := calc
    _ ≤ ((2 : ℝ) ^ m) ^ 5 := pow_le_pow_left₀ (by positivity) hmpow _
    _ = (2 : ℝ) ^ (m * 5) := (pow_mul _ _ _).symm
    _ ≤ (2 : ℝ) ^ (m ^ 2) := by
      apply pow_le_pow_right₀ (by norm_num)
      simpa [sq] using Nat.mul_le_mul_left m hm
    _ ≤ (q ^ (m ^ 5)) ^ (m ^ 2) := pow_le_pow_left₀ (by norm_num) h₂ _
    _ = _ := by rw [← pow_mul, ← pow_add]
  change 1 ≤ q ^ (m ^ 7) * _
  rw [add_sub_cancel_left, ← div_eq_mul_one_div, le_div_iff₀ (by positivity)]
  simpa using hlarge

private lemma ratio_upper {n m : ℕ} (hm : 5 ≤ m) (hlo : m ^ 8 ≤ n)
    (hhi : n < (m + 1) ^ 8) :
    Real.logb 2 (antichainCount n) / middle n ≤ 1 + 130 / m := by
  let q : ℝ := 1 + 1 / (m : ℝ) ^ 5
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hn : 0 < n := lt_of_lt_of_le (pow_pos (by omega) _) hlo
  have hmpos : (0 : ℝ) < middle n := Nat.cast_pos.mpr (Nat.choose_pos (Nat.div_le_self _ _))
  have hq : 1 ≤ q := le_add_of_nonneg_right (by positivity)
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hcard : (antichainCount n : ℝ) ≤
      (2 : ℝ) ^ ((middle n : ℝ) + (m : ℝ) ^ 7 * (2 * (middle n : ℝ) / n)) *
        q ^ (2 ^ n) := by
    simpa [count_eq, Fintype.card_finset] using
      count_upper hq (branch_factor m hm) (univ : Family n)
  have hcnt : (0 : ℝ) < antichainCount n := by
    exact_mod_cast lt_of_lt_of_le (by positivity : 0 < 2 ^ middle n) (count_lower n)
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hcnt hcard
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_rpow (by norm_num) (by norm_num),
    Real.logb_pow] at hlog
  push_cast at hlog
  have hlq : Real.logb 2 q ≤ 2 / (m : ℝ) ^ 5 := by
    rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
    have hhalf := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hhalf
    have h := Real.log_le_sub_one_of_pos hqpos
    dsimp [q] at h
    calc
      _ ≤ 1 / (m : ℝ) ^ 5 := by linarith
      _ = 2 / (m : ℝ) ^ 5 * (1 / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hwin : n + 1 ≤ 256 * m ^ 8 := calc
    _ ≤ (m + 1) ^ 8 := hhi
    _ ≤ (2 * m) ^ 8 := Nat.pow_le_pow_left (by omega) _
    _ = _ := by rw [mul_pow]; norm_num
  have hN : (2 : ℝ) ^ n ≤ 64 * (m : ℝ) ^ 4 * middle n := by
    have hsq := middle_lower n
    have hbound : (2 ^ n) ^ 2 ≤ (64 * m ^ 4 * middle n) ^ 2 := calc
      _ ≤ _ := hsq
      _ ≤ 16 * (256 * m ^ 8) * middle n ^ 2 := by gcongr
      _ = _ := by ring
    exact_mod_cast (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hbound
  have hreal : (m : ℝ) ^ 8 ≤ n := by exact_mod_cast hlo
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsmall : (m : ℝ) ^ 7 * (2 * middle n / n) ≤ 2 * middle n / m := by
    rw [← mul_div_assoc, div_le_div_iff₀ hn' hm']
    calc
      _ = (2 * middle n : ℝ) * (m : ℝ) ^ 8 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hreal (by positivity)
  apply (div_le_iff₀ hmpos).mpr
  calc
    _ ≤ _ := hlog
    _ ≤ middle n + 2 * (middle n : ℝ) / m +
        (64 * (m : ℝ) ^ 4 * middle n) * (2 / (m : ℝ) ^ 5) := by
      gcongr
      exact Real.logb_nonneg (by norm_num) hq
    _ = _ := by field_simp; ring

/--
**Kleitman's theorem on Dedekind numbers.** Let $M(n)$ be the number of antichains with respect
to inclusion among the subsets of an $n$-element set. Then
$\log_2 M(n) / \binom{n}{\lfloor n/2 \rfloor} \to 1$ as $n \to \infty$; that is,
$M(n) = 2^{(1 + o(1)) \binom{n}{\lfloor n/2 \rfloor}}$.

Source: T. F. Bloom, Erdős Problems, Problem #497, https://www.erdosproblems.com/497
(status SOLVED (LEAN)); resolution: D. Kleitman, On Dedekind's problem: the number of monotone
Boolean functions, Proc. Amer. Math. Soc. (1969), 677-682, erdosproblems.com/497: resolved by
Kleitman, the number is 2^{(1 + o(1)) C(n, ⌊n/2⌋)}, https://www.erdosproblems.com/497.
-/
theorem antichainCountLogAsymptotic_holds : antichainCountLogAsymptotic := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (130 / ε)
  filter_upwards [Filter.eventually_ge_atTop ((max 5 k) ^ 8)] with n hn
  let m := Nat.nthRoot 8 n
  have hkm : max 5 k ≤ m := (Nat.le_nthRoot_iff (by decide)).mpr hn
  have hm : 5 ≤ m := (le_max_left _ _).trans hkm
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hu := ratio_upper hm (Nat.pow_nthRoot_le (.inl (by decide)))
    (Nat.lt_pow_nthRoot_add_one (by decide) n)
  have he : 130 / (m : ℝ) < ε := by
    rw [div_lt_iff₀ hm']
    have h := (div_lt_iff₀ hε).mp hk
    calc
      _ < (k : ℝ) * ε := h
      _ ≤ ε * m := by rw [mul_comm]; gcongr; exact (le_max_right _ _).trans hkm
  have hB : (0 : ℝ) < middle n := Nat.cast_pos.mpr (Nat.choose_pos (Nat.div_le_self _ _))
  have hl : 1 ≤ Real.logb 2 (antichainCount n) / middle n := by
    rw [le_div_iff₀ hB, one_mul]
    have h : (2 : ℝ) ^ middle n ≤ antichainCount n := by exact_mod_cast count_lower n
    simpa [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using
      Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) h
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hl)]
  linarith

end MathlibExt.Combinatorics.DedekindAntichainCountErdosProblem497Wanted
