/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

/-!
# Monochromatic sums of products in two-colourings of the integers (Erdős Problem 1198)

Erdős Problem 1198: if `ℕ` is `2`-coloured, must there be an infinite set `A = {a₁ < a₂ < ⋯}` such
that all expressions `∏_{i ∈ S₁} aᵢ + ⋯ + ∏_{i ∈ S_k} aᵢ` for disjoint `S₁, …, S_k` (excluding the
trivial expressions `aᵢ`) have the same colour?

We prove `monochromaticSumsOfProducts_refuted` by comparing the accuracy of high and
low binary approximations by powers of two.

Source: T. F. Bloom, Erdős Problems, Problem #1198, https://www.erdosproblems.com/1198 (status
DISPROVED). UnsolvedMath record UM-30007239 (`EP-1198`), dataset ulamai/UnsolvedMath v1.8.0.

The index sets are nonempty, finite and pairwise disjoint, `k ≥ 1`, and the excluded trivial
expressions are `k = 1` with `|S₁| = 1`; the elements `aᵢ` themselves need not have that colour (as
discussed on the problem page). The elements are positive integers. Compared with the
formal-conjectures statement `ErdosProblems/1198.lean` (equivalent; no code imported).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.MonochromaticSumsOfProductsErdosProblem1198Wanted

open Finset

/-- **Erdős Problem 1198: monochromatic sums of products.** This is the statement that for every
colouring $c : \mathbb{N} \to \{0, 1\}$ there are a strictly increasing sequence
$0 < a_0 < a_1 < \cdots$ of natural numbers and a colour $\gamma \in \{0, 1\}$ such that
$c\bigl(\sum_{j < k} \prod_{i \in S_j} a_i\bigr) = \gamma$ for every $k \ge 1$ and all pairwise
disjoint nonempty finite sets $S_0, \dots, S_{k-1} \subseteq \mathbb{N}$, except when $k = 1$ and
$S_0$ has exactly one element. -/
def monochromaticSumsOfProducts : Prop :=
  ∀ c : ℕ → Fin 2, ∃ a : ℕ → ℕ, StrictMono a ∧ 0 < a 0 ∧ ∃ col : Fin 2,
    ∀ (k : ℕ) (S : Fin k → Finset ℕ), 0 < k → (∀ j, (S j).Nonempty) →
      Pairwise (fun j j' => Disjoint (S j) (S j')) → ¬ (k = 1 ∧ ∀ j, (S j).card = 1) →
        c (∑ j, ∏ i ∈ S j, a i) = col

private abbrev v (n : ℕ) := n.factorization 2
private abbrev oddPart (n : ℕ) := ordCompl[2] n

-- The low-end error is the dyadic size of the odd part minus one.
private def lowError (n : ℕ) : ℚ :=
  if oddPart n = 1 then 0 else (2 ^ v (oddPart n - 1))⁻¹

private def NearPower (ε : ℚ) (n : ℕ) : Prop :=
  ∃ k : ℕ, (1 - ε) * (2 : ℚ) ^ k < n ∧ (n : ℚ) < (1 + ε) * 2 ^ k

private noncomputable def colour (n : ℕ) : Fin 2 := by
  classical
  exact if ¬ 2 ∣ n then 0 else if ¬ 4 ∣ n then 1 else
    if NearPower (lowError n) n then 0 else 1

private lemma twoPow_mono {i j : ℕ} (h : i ≤ j) : (2 : ℚ) ^ i ≤ 2 ^ j :=
  pow_le_pow_right₀ (by norm_num) h

private lemma v_add_of_dvd {x y : ℕ} (hx : x ≠ 0) (hy : 2 ^ (v x + 1) ∣ y) :
    v (x + y) = v x := by
  have hp := Nat.prime_two
  have hxy : x + y ≠ 0 := by omega
  have hd : 2 ^ v x ∣ x := Nat.ordProj_dvd x 2
  have hnd : ¬ 2 ^ (v x + 1) ∣ x := by
    rw [hp.pow_dvd_iff_le_factorization hx]
    exact Nat.not_succ_le_self _
  apply le_antisymm
  · by_contra! h
    exact hnd ((Nat.dvd_add_iff_left hy).mpr
      ((hp.pow_dvd_iff_le_factorization hxy).mpr h))
  · exact (hp.pow_dvd_iff_le_factorization hxy).mp
      (dvd_add hd (dvd_trans (pow_dvd_pow 2 (Nat.le_succ _)) hy))

private lemma oddPart_add_of_mul {x t : ℕ} (hx : x ≠ 0) (ht : 2 ∣ t) :
    oddPart (x + 2 ^ v x * t) = oddPart x + t := by
  have ht' : 2 ^ (v x + 1) ∣ 2 ^ v x * t := by
    rw [pow_succ]
    exact Nat.mul_dvd_mul_left _ ht
  change (x + 2 ^ v x * t) / 2 ^ v (x + 2 ^ v x * t) = _
  rw [v_add_of_dvd hx ht', Nat.add_mul_div_left _ _ (by positivity)]

private lemma lowError_add_eq {x y : ℕ} (hx : x ≠ 0) (hn : oddPart x ≠ 1)
    (hy : 2 ^ (v x + v (oddPart x - 1) + 1) ∣ y) :
    lowError (x + y) = lowError x := by
  let d := v (oddPart x - 1)
  obtain ⟨t, ht⟩ : ∃ t, y = 2 ^ v x * t ∧ 2 ^ (d + 1) ∣ t := by
    obtain ⟨q, hq⟩ := hy
    exact ⟨2 ^ (d + 1) * q, by rw [hq, ← mul_assoc, ← pow_add]; congr 2, dvd_mul_right ..⟩
  have hodd : 0 < oddPart x := Nat.ordCompl_pos 2 hx
  have hsub : oddPart x - 1 ≠ 0 := by omega
  have ht2 : 2 ∣ t := dvd_trans (pow_dvd_pow 2 (by omega : 1 ≤ d + 1)) ht.2
  have heq : oddPart x + t - 1 = oddPart x - 1 + t := by omega
  have hne : oddPart x + t ≠ 1 := by omega
  simp [lowError, ht.1, oddPart_add_of_mul hx ht2, hn, hne, heq, v_add_of_dvd hsub ht.2]

private lemma lowError_le_of_modEq {x d : ℕ} (hx : x ≠ 0)
    (h : oddPart x ≡ 1 [MOD 2 ^ d]) :
    lowError x ≤ ((2 : ℚ) ^ d)⁻¹ := by
  by_cases h1 : oddPart x = 1
  · simp [lowError, h1]
  have hsub : oddPart x - 1 ≠ 0 := by
    have hodd : 0 < oddPart x := Nat.ordCompl_pos 2 hx
    omega
  have hdvd : 2 ^ d ∣ oddPart x - 1 := Nat.modEq_iff_dvd' (Nat.ordCompl_pos 2 hx) |>.mp h.symm
  have hd := (Nat.prime_two.pow_dvd_iff_le_factorization hsub).mp hdvd
  rw [lowError, ite_eq_right h1]
  exact inv_anti₀ (by positivity) (twoPow_mono hd)

private lemma NearPower.mono {ε δ : ℚ} {n : ℕ} (h : NearPower ε n) (hε : ε ≤ δ) :
    NearPower δ n := by
  obtain ⟨k, hlo, hhi⟩ := h
  refine ⟨k, ?_, ?_⟩
  · exact lt_of_le_of_lt (by gcongr) hlo
  · exact hhi.trans_le (by gcongr)

private lemma not_nearPower_of_bounds {n k : ℕ} {ε : ℚ} (hε : ε ≤ 1)
    (hlo : (1 + ε) * (2 : ℚ) ^ k ≤ n) (hhi : (n : ℚ) ≤ (1 - ε) * 2 ^ (k + 1)) :
    ¬ NearPower ε n := by
  rintro ⟨j, hjlo, hjhi⟩
  by_cases hj : j ≤ k
  · have h := twoPow_mono hj
    have h' : 0 ≤ 1 + ε := by
      have hp : 0 < (2 : ℚ) ^ j := by positivity
      have hn : 0 ≤ (n : ℚ) := by positivity
      nlinarith
    exact (hjhi.trans_le ((mul_le_mul_of_nonneg_left h h').trans hlo)).false
  · have h := twoPow_mono (show k + 1 ≤ j by omega)
    exact (hjlo.trans_le (hhi.trans (mul_le_mul_of_nonneg_left h (by linarith)))).false


-- Compare two prefix products in the same mantissa interval and with the same odd residue.
private lemma exists_approximate_product {a : ℕ → ℕ} (ha : ∀ i, 0 < a i)
    (he : ∀ N, ∃ i ≥ N, 2 ∣ a i) (N D : ℕ) {ε : ℚ} (hε : 0 < ε) :
    ∃ s : Finset ℕ, s.Nonempty ∧ (∀ i ∈ s, N ≤ i) ∧
      2 ^ D ∣ (∏ i ∈ s, a i) ∧
      oddPart (∏ i ∈ s, a i) ≡ 1 [MOD 2 ^ D] ∧ NearPower ε (∏ i ∈ s, a i) := by
  classical
  let E : Set ℕ := {i | N ≤ i ∧ 2 ∣ a i}
  have hE : E.Infinite := Set.infinite_of_forall_exists_gt fun j ↦ by
    obtain ⟨i, hi, hd⟩ := he (max N (j + 1))
    exact ⟨i, ⟨(le_max_left ..).trans hi, hd⟩, (le_max_right ..).trans hi⟩
  let b : ℕ ↪ ℕ := (hE.natEmbedding E).trans (Function.Embedding.subtype _)
  have hb (i : ℕ) : N ≤ b i ∧ 2 ∣ a (b i) := (hE.natEmbedding E i).property
  let p (i : ℕ) := ∏ u ∈ range (i * (D + 1)), a (b u)
  have hp (i : ℕ) : 0 < p i := prod_pos fun _ _ ↦ ha _
  let e (i : ℕ) := Nat.log 2 (p i)
  let r (i : ℕ) : ℚ := (p i : ℚ) / 2 ^ e i
  have hr (i : ℕ) : 1 ≤ r i ∧ r i < 2 := by
    dsimp [r]
    have hpow : (0 : ℚ) < 2 ^ e i := by positivity
    constructor
    · rw [le_div_iff₀ hpow, one_mul]
      exact_mod_cast Nat.pow_log_le_self 2 (hp i).ne'
    · rw [div_lt_iff₀ hpow, ← pow_succ']
      exact_mod_cast Nat.lt_pow_succ_log_self Nat.one_lt_two (p i)
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / ε)
  have hM' : 1 < ε * (M : ℚ) := by
    rw [div_lt_iff₀ hε, mul_comm] at hM
    exact hM
  have hMpos : 0 < (M : ℚ) := (by positivity : 0 < 1 / ε).trans hM
  have hpos (u : ℕ) : 0 ≤ (M : ℚ) * r u := mul_nonneg hMpos.le (zero_le_one.trans (hr u).1)
  let f (i : ℕ) : Fin (2 * M) × Fin (2 ^ D) :=
    (⟨⌊(M : ℚ) * r i⌋₊, by
        apply (Nat.floor_lt (hpos i)).mpr
        push_cast
        simpa only [mul_comm (2 : ℚ)] using mul_lt_mul_of_pos_left (hr i).2 hMpos⟩,
      ⟨oddPart (p i) % 2 ^ D, Nat.mod_lt _ (by positivity)⟩)
  obtain ⟨i, j, hij, hf⟩ : ∃ i j, i < j ∧ f i = f j := by
    obtain ⟨i, j, hne, hj⟩ := Finite.exists_ne_map_eq_of_infinite f
    exact (lt_or_gt_of_ne hne).elim (fun h ↦ ⟨i, j, h, hj⟩) (fun h ↦ ⟨j, i, h, hj.symm⟩)
  let I := Ico (i * (D + 1)) (j * (D + 1))
  let w := ∏ u ∈ I, a (b u)
  have hij' : i * (D + 1) < j * (D + 1) :=
    Nat.mul_lt_mul_of_pos_right hij (by omega)
  have hpw : p i * w = p j := prod_range_mul_prod_Ico _ hij'.le
  have hpow : e i ≤ e j := Nat.log_mono_right (Nat.le_of_dvd (hp j) ⟨w, hpw.symm⟩)
  have hq : r i * (w : ℚ) = r j * 2 ^ (e j - e i) := by
    have h := congrArg (fun u : ℕ ↦ (u : ℚ)) hpw
    push_cast at h
    have hk : (2 : ℚ) ^ e j = 2 ^ (e j - e i) * 2 ^ e i := by
      rw [← pow_add, Nat.sub_add_cancel hpow]
    dsimp [r]
    rw [hk]
    field_simp
    linarith
  have hf₁ : ⌊(M : ℚ) * r i⌋₊ = ⌊(M : ℚ) * r j⌋₊ := congrArg (fun u ↦ u.1.val) hf
  have hr_close (l m : ℕ) (hlm : ⌊(M : ℚ) * r l⌋₊ = ⌊(M : ℚ) * r m⌋₊) :
      r l - r m < ε := by
    have hl := Nat.lt_floor_add_one ((M : ℚ) * r l)
    have hm := Nat.floor_le (hpos m)
    rw [hlm] at hl
    apply lt_of_mul_lt_mul_left (a := (M : ℚ)) _ hMpos.le
    linarith
  have hεr := mul_nonneg hε.le (sub_nonneg.mpr (hr i).1)
  have hlo : (1 - ε) * r i < r j := by nlinarith only [hr_close i j hf₁, hεr]
  have hhi : r j < (1 + ε) * r i := by nlinarith only [hr_close j i hf₁.symm, hεr]
  have hri : 0 < r i := zero_lt_one.trans_le (hr i).1
  have hn : NearPower ε w := by
    refine ⟨e j - e i, ?_, ?_⟩
    · apply lt_of_mul_lt_mul_left (a := r i) _ hri.le
      rw [hq, ← mul_assoc, mul_comm (r i)]
      exact mul_lt_mul_of_pos_right hlo (by positivity)
    · apply lt_of_mul_lt_mul_left (a := r i) _ hri.le
      rw [hq, ← mul_assoc, mul_comm (r i)]
      exact mul_lt_mul_of_pos_right hhi (by positivity)
  have hmod : oddPart w ≡ 1 [MOD 2 ^ D] := by
    have hf₂ : oddPart (p j) ≡ oddPart (p i) [MOD 2 ^ D] := by
      exact congrArg (fun u : Fin (2 * M) × Fin (2 ^ D) ↦ u.2.val) hf.symm
    have hh : oddPart (p i) * oddPart w ≡ oddPart (p i) * 1 [MOD 2 ^ D] := by
      simpa only [← Nat.ordCompl_mul, hpw, mul_one] using hf₂
    exact hh.cancel_left_of_coprime ((Nat.coprime_ordCompl Nat.prime_two (hp i).ne').pow_left D)
  have hD : D ≤ I.card := by
    have h := Nat.mul_le_mul_right (D + 1) (show i + 1 ≤ j by omega)
    rw [Nat.add_mul, one_mul] at h
    simp only [I, Nat.card_Ico]
    omega
  have hdvd : 2 ^ D ∣ w := by
    refine (pow_dvd_pow 2 hD).trans ?_
    rw [← prod_const]
    exact prod_dvd_prod_of_dvd _ _ fun u _ ↦ (hb u).2
  refine ⟨I.map b, (nonempty_Ico.mpr hij').map, ?_, ?_⟩
  · intro l hl
    obtain ⟨u, _, rfl⟩ := mem_map.mp hl
    exact (hb u).1
  · simpa only [prod_map] using And.intro hdvd (And.intro hmod hn)


private lemma exists_large_approximate_product {a : ℕ → ℕ} (ha : ∀ i, 0 < a i)
    (he : ∀ N, ∃ i ≥ N, 2 ∣ a i) (N D : ℕ) (B : ℚ) {ε : ℚ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ∃ (s : Finset ℕ) (k : ℕ), s.Nonempty ∧ (∀ i ∈ s, N ≤ i) ∧
      2 ^ D ∣ (∏ i ∈ s, a i) ∧ oddPart (∏ i ∈ s, a i) ≡ 1 [MOD 2 ^ D] ∧
      B < (2 : ℚ) ^ k ∧ (1 - ε) * (2 : ℚ) ^ k < (∏ i ∈ s, a i : ℕ) ∧
      ((∏ i ∈ s, a i : ℕ) : ℚ) < (1 + ε) * 2 ^ k := by
  obtain ⟨E, hE⟩ := pow_unbounded_of_one_lt (2 * B) (by norm_num : (1 : ℚ) < 2)
  obtain ⟨s, hs, hN, hdiv, hmod, k, hlo, hhi⟩ :=
    exists_approximate_product ha he N (max D E) hε
  have hD := pow_dvd_pow 2 (le_max_left D E)
  have hpow : (2 : ℚ) ^ E ≤ ((∏ i ∈ s, a i : ℕ) : ℚ) := by
    exact_mod_cast Nat.le_of_dvd (prod_pos fun i _ ↦ ha i)
      ((pow_dvd_pow 2 (le_max_right D E)).trans hdiv)
  refine ⟨s, k, hs, hN, hD.trans hdiv, hmod.of_dvd hD, ?_, hlo, hhi⟩
  have ht : (1 + ε) * (2 : ℚ) ^ k ≤ 2 * 2 ^ k := by gcongr; linarith
  linarith [hE.trans_le hpow, hhi.trans_le ht]

private lemma lowError_pos {n : ℕ} (h : oddPart n ≠ 1) : 0 < lowError n := by
  rw [lowError, ite_eq_right h]
  positivity

private lemma lowError_le_one (n : ℕ) : lowError n ≤ 1 := by
  unfold lowError
  split_ifs
  · norm_num
  · exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

private lemma colour_of_near {n : ℕ} (h4 : 4 ∣ n) (hn : NearPower (lowError n) n) :
    colour n = 0 := by
  have h2 : 2 ∣ n := dvd_trans (by decide : 2 ∣ 4) h4
  simp [colour, h2, h4, hn]

private lemma colour_of_far {n : ℕ} (h4 : 4 ∣ n) (hn : ¬ NearPower (lowError n) n) :
    colour n = 1 := by
  have h2 : 2 ∣ n := dvd_trans (by decide : 2 ∣ 4) h4
  simp [colour, h2, h4, hn]

private lemma disjoint_of_lt {s t : Finset ℕ} {N : ℕ} (hs : ∀ i ∈ s, i < N)
    (ht : ∀ i ∈ t, N ≤ i) : Disjoint s t :=
  Finset.disjoint_left.mpr fun i hi hj ↦ (hs i hi).not_ge (ht i hj)

-- A fixed non-power can contribute either the low digits or the high digits of a sum.
private lemma different_colours_of_nonpower {a : ℕ → ℕ} (ha : ∀ i, 0 < a i)
    (he : ∀ N, ∃ i ≥ N, 2 ∣ a i) {A : Finset ℕ} (hA : A.Nonempty)
    (hA4 : 4 ∣ ∏ i ∈ A, a i) (hAx : oddPart (∏ i ∈ A, a i) ≠ 1) {col : Fin 2}
    (hTwo : ∀ {s t : Finset ℕ}, s.Nonempty → t.Nonempty → Disjoint s t →
      colour ((∏ i ∈ s, a i) + ∏ i ∈ t, a i) = col) : False := by
  let x := ∏ i ∈ A, a i
  have hx : 0 < x := prod_pos fun i _ ↦ ha i
  let N := A.sup id + 1
  have hN : ∀ i ∈ A, i < N := fun i hi ↦ Nat.lt_succ_of_le (le_sup (f := id) hi)
  have hsmall : 0 < lowError x / 2 := half_pos (lowError_pos hAx)
  have hsmall₁ : lowError x / 2 ≤ 1 := by linarith [lowError_le_one x]
  let D := max 2 (v x + v (oddPart x - 1) + 1)
  obtain ⟨s, k, hs, hsN, hsD, _, hk, hlo, hhi⟩ :=
    exists_large_approximate_product ha he N D ((x : ℚ) / (lowError x / 2)) hsmall hsmall₁
  let z := ∏ i ∈ s, a i
  have hz4 : 4 ∣ z := (pow_dvd_pow 2 (le_max_left 2 _)).trans hsD
  have hl : lowError (x + z) = lowError x :=
    lowError_add_eq hx.ne' hAx ((pow_dvd_pow 2 (le_max_right 2 _)).trans hsD)
  have hnear : NearPower (lowError (x + z)) (x + z) := by
    rw [hl]
    refine ⟨k, ?_, ?_⟩ <;> push_cast
    · have h := mul_nonneg hsmall.le (show (0 : ℚ) ≤ 2 ^ k by positivity)
      have hxq : (0 : ℚ) ≤ x := by positivity
      linarith
    · have h := (div_lt_iff₀ hsmall).mp hk
      linarith
  have hcol0 : (0 : Fin 2) = col :=
    (colour_of_near (dvd_add hA4 hz4) hnear).symm.trans (hTwo hA hs (disjoint_of_lt hN hsN))
  let e := Nat.log 2 x
  have hex : 2 ^ e < x := by
    have hle := Nat.pow_log_le_self 2 hx.ne'
    refine hle.lt_of_ne fun h ↦ hAx ?_
    change oddPart x = 1
    rw [← h]
    exact Nat.ordCompl_self_pow Nat.prime_two
  have hehi : x < 2 ^ (e + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two x
  have hlow : (2 : ℚ) ^ e + 1 ≤ x := by
    exact_mod_cast (Nat.succ_le_of_lt hex)
  have hhigh : (x : ℚ) + 1 ≤ 2 ^ (e + 1) := by
    exact_mod_cast (Nat.succ_le_of_lt hehi)
  let δ : ℚ := 1 / (8 * 2 ^ e)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδP : δ * 2 ^ e = 1 / 8 := by dsimp [δ]; field_simp
  have hδ₁ : δ ≤ 1 := by
    have hP : (1 : ℚ) ≤ 2 ^ e := one_le_pow₀ (by norm_num)
    nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hP)]
  have hδx : δ * x ≤ 1 / 4 := by
    have h := mul_le_mul_of_nonneg_left (show (x : ℚ) ≤ 2 ^ (e + 1) by linarith) hδ.le
    rw [pow_succ] at h
    linarith only [h, hδP]
  obtain ⟨d, hd⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (2 : ℚ)⁻¹ < 1)
  obtain ⟨t, _, ht, htN, htD, htM, _, _, _⟩ :=
    exists_large_approximate_product ha he N (max 2 d) 0 (by norm_num : (0 : ℚ) < 1) le_rfl
  let y := ∏ i ∈ t, a i
  have hy : 0 < y := prod_pos fun i _ ↦ ha i
  have hy4 : 4 ∣ y := (pow_dvd_pow 2 (le_max_left 2 _)).trans htD
  have hyM : oddPart y ≡ 1 [MOD 2 ^ d] :=
    htM.of_dvd (pow_dvd_pow 2 (le_max_right 2 d))
  let M := t.sup id + N + 1
  have hNM : N ≤ M := by dsimp [M]; omega
  have hltM : ∀ i ∈ t, i < M := by
    intro i hi
    have h := le_sup (f := id) hi
    dsimp [M]
    exact Nat.lt_succ_of_le (h.trans (Nat.le_add_right ..))
  obtain ⟨u, j, _, huM, huD, _, hj, hjlo, hjhi⟩ :=
    exists_large_approximate_product ha he M (v y + max 1 d) (4 * (y : ℚ)) hδ hδ₁
  let w := ∏ i ∈ u, a i
  have hdiv : 2 ^ (v y + max 1 d) ∣ x * w := dvd_mul_of_dvd_right huD _
  obtain ⟨q, hq⟩ := hdiv
  let r := 2 ^ max 1 d * q
  have hxr : x * w = 2 ^ v y * r := by rw [hq, pow_add, mul_assoc]
  have hr2 : 2 ∣ r := (pow_dvd_pow 2 (le_max_left 1 d)).trans (dvd_mul_right ..)
  have hrd : 2 ^ d ∣ r := (pow_dvd_pow 2 (le_max_right 1 d)).trans (dvd_mul_right ..)
  have hym : oddPart (y + x * w) ≡ 1 [MOD 2 ^ d] := by
    rw [hxr, oddPart_add_of_mul hy.ne' hr2]
    simpa only [add_zero] using hyM.add (Nat.modEq_zero_iff_dvd.mpr hrd)
  have hyx : y + x * w ≠ 0 := by omega
  have hErr : lowError (y + x * w) ≤ δ :=
    (lowError_le_of_modEq hyx hym).trans (by simpa only [inv_pow] using hd.le)
  have hfar : ¬ NearPower (lowError (y + x * w)) (y + x * w) := by
    intro hn
    apply not_nearPower_of_bounds (k := e + j) hδ₁ _ _ (hn.mono hErr)
    · push_cast
      rw [pow_add]
      have h := mul_lt_mul_of_pos_left hjlo (show (0 : ℚ) < x by exact_mod_cast hx)
      have hyq : (0 : ℚ) ≤ y := by positivity
      have hlo' : (1 + δ) * (2 : ℚ) ^ e ≤ (x : ℚ) * (1 - δ) := by
        linarith only [hlow, hδP, hδx]
      calc
        (1 + δ) * ((2 : ℚ) ^ e * 2 ^ j) ≤ (x : ℚ) * (1 - δ) * 2 ^ j := by
          rw [← mul_assoc]
          gcongr
        _ ≤ (y : ℚ) + (x : ℚ) * w := by linarith only [h, hyq]
    · push_cast
      rw [show e + j + 1 = (e + 1) + j by omega, pow_add]
      have h := mul_lt_mul_of_pos_left hjhi (show (0 : ℚ) < x by exact_mod_cast hx)
      have htop : (x : ℚ) * (1 + δ) + 1 / 4 ≤ (1 - δ) * 2 ^ (e + 1) := by
        rw [pow_succ] at hhigh ⊢
        linarith only [hhigh, hδP, hδx]
      calc
        (y : ℚ) + (x : ℚ) * w ≤ ((x : ℚ) * (1 + δ) + 1 / 4) * 2 ^ j := by
          linarith only [h, hj]
        _ ≤ (1 - δ) * ((2 : ℚ) ^ (e + 1) * 2 ^ j) := by
          rw [← mul_assoc]
          gcongr
  have hAu : Disjoint A u := disjoint_of_lt hN fun i hi ↦ hNM.trans (huM i hi)
  have htu : Disjoint t u := disjoint_of_lt hltM huM
  have htAu : Disjoint t (A ∪ u) := disjoint_union_right.mpr
    ⟨(disjoint_of_lt hN htN).symm, htu⟩
  have hcol1 : (1 : Fin 2) = col := by
    have h := hTwo ht (hA.mono subset_union_left : (A ∪ u).Nonempty) htAu
    rw [prod_union hAu] at h
    exact (colour_of_far (dvd_add hy4 (dvd_mul_of_dvd_left hA4 _)) hfar).symm.trans h
  exact (by decide : (0 : Fin 2) ≠ 1) (hcol0.trans hcol1.symm)


private lemma lowError_pow_add_mul {p q t : ℕ} (hpq : p < q) (ht : ¬ 2 ∣ t) :
    lowError (2 ^ p + 2 ^ q * t) = ((2 : ℚ) ^ (q - p))⁻¹ := by
  let d := q - p
  have hd : 0 < d := Nat.sub_pos_of_lt hpq
  have he : 2 ^ q = 2 ^ p * 2 ^ d := by rw [← pow_add, Nat.add_sub_of_le hpq.le]
  have ht0 : t ≠ 0 := fun h ↦ ht (h ▸ dvd_zero 2)
  have ht' : 2 ∣ 2 ^ d * t :=
    (pow_dvd_pow 2 (show 1 ≤ d from hd)).trans (dvd_mul_right ..)
  have hdiv : ¬ 2 ∣ 1 + 2 ^ d * t := by
    rw [← Nat.dvd_add_iff_left ht']
    decide
  have hdv : v (2 ^ d * t) = d := by
    change (2 ^ d * t).factorization 2 = d
    simp [Nat.factorization_mul (by positivity : 2 ^ d ≠ 0) ht0,
      Nat.prime_two.factorization_pow, Nat.factorization_eq_zero_of_not_dvd ht]
  have hne : 1 + 2 ^ d * t ≠ 1 := by
    have : 0 < 2 ^ d * t := by positivity
    omega
  have hop : oddPart (2 ^ p + 2 ^ q * t) = 1 + 2 ^ d * t := by
    have h : 2 ^ p + 2 ^ q * t = 2 ^ p * (1 + 2 ^ d * t) := by
      rw [he, mul_add, mul_one, mul_assoc]
    rw [h]
    exact Nat.ordCompl_pow_mul_of_not_dvd p Nat.prime_two hdiv
  rw [lowError, hop, ite_eq_right hne, Nat.add_sub_cancel_left, hdv]

-- Two isolated bits have equal low- and high-end errors. A sufficiently distant third bit
-- makes the high-end error strictly smaller.
private lemma colours_of_powers {p q r : ℕ} (hp : 2 ≤ p) (hq : p + 2 ≤ q)
    (hr : q + (q - p) + 2 ≤ r) :
    colour (2 ^ p + 2 ^ q) = 1 ∧ colour (2 ^ p + 2 ^ q + 2 ^ r) = 0 := by
  let ε : ℚ := ((2 : ℚ) ^ (q - p))⁻¹
  have hpq : p < q := by omega
  have hqr : q < r := by omega
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεq : ε * (2 : ℚ) ^ q = 2 ^ p := by
    dsimp [ε]
    have h : (2 : ℚ) ^ q = 2 ^ p * 2 ^ (q - p) := by
      rw [← pow_add, Nat.add_sub_of_le hpq.le]
    rw [h]
    field_simp
  have h4 (x : ℕ) (hx : 2 ≤ x) : 4 ∣ 2 ^ x := pow_dvd_pow 2 hx
  have hpair : lowError (2 ^ p + 2 ^ q) = ε := by
    simpa only [mul_one] using lowError_pow_add_mul hpq (t := 1) (by decide)
  constructor
  · apply colour_of_far (dvd_add (h4 p hp) (h4 q (by omega)))
    rw [hpair]
    apply not_nearPower_of_bounds (k := q)
    · rw [← hpair]
      exact lowError_le_one _
    · push_cast
      linarith only [hεq]
    · push_cast
      rw [pow_succ]
      have h := twoPow_mono hq
      rw [pow_add] at h
      norm_num at h
      have hp' : (0 : ℚ) ≤ 2 ^ p := by positivity
      linarith only [h, hεq, hp']
  · have h4' : 4 ∣ 2 ^ p + 2 ^ q + 2 ^ r :=
      dvd_add (dvd_add (h4 p hp) (h4 q (by omega))) (h4 r (by omega))
    apply colour_of_near h4'
    have h := show 2 ^ r = 2 ^ q * 2 ^ (r - q) by rw [← pow_add, Nat.add_sub_of_le hqr.le]
    have hodd : ¬ 2 ∣ 1 + 2 ^ (r - q) := by
      have hev : 2 ∣ 2 ^ (r - q) := pow_dvd_pow 2 (by omega : 1 ≤ r - q)
      rw [← Nat.dvd_add_iff_left hev]
      decide
    have htriple : lowError (2 ^ p + 2 ^ q + 2 ^ r) = ε := by
      have heq : 2 ^ p + 2 ^ q + 2 ^ r = 2 ^ p + 2 ^ q * (1 + 2 ^ (r - q)) := by
        rw [h, mul_add, mul_one, add_assoc]
      rw [heq]
      exact lowError_pow_add_mul hpq hodd
    rw [htriple]
    refine ⟨r, ?_, ?_⟩ <;> push_cast
    · have : (0 : ℚ) < ε * 2 ^ r := by positivity
      have : (0 : ℚ) < 2 ^ p + 2 ^ q := by positivity
      linarith
    · have h₁ := twoPow_mono hpq.le
      have h₂ := twoPow_mono hr
      rw [pow_add, pow_add] at h₂
      norm_num at h₂
      have hpos : (0 : ℚ) < 2 ^ q * 2 ^ (q - p) := by positivity
      have hsum : ((2 : ℚ) ^ p + 2 ^ q) * 2 ^ (q - p) < 2 ^ r := by
        have h' := mul_le_mul_of_nonneg_right h₁
          (show (0 : ℚ) ≤ 2 ^ (q - p) by positivity)
        linarith only [h', h₂, hpos]
      have he : (2 : ℚ) ^ (q - p) * ε = 1 := by dsimp [ε]; field_simp
      have hh := mul_lt_mul_of_pos_right hsum hε
      rw [mul_assoc, he, mul_one] at hh
      linarith only [hh]

private lemma different_colours_of_eventually_odd {a : ℕ → ℕ} {col : Fin 2} {N : ℕ}
    (ho : ∀ i ≥ N, ¬ 2 ∣ a i)
    (hTwo : ∀ {i j : ℕ}, i ≠ j → colour (a i + a j) = col)
    (hThree : ∀ {i j k : ℕ}, i ≠ j → i ≠ k → j ≠ k → colour (a i + a j + a k) = col) :
    False := by
  have h₀ := ho N le_rfl
  have h₁ := ho (N + 1) (by omega)
  have h₂ := ho (N + 2) (by omega)
  have h3 : ¬ 2 ∣ a N + a (N + 1) + a (N + 2) := by omega
  have hc0 : (0 : Fin 2) = col := by
    simpa [colour, h3] using hThree (i := N) (j := N + 1) (k := N + 2) (by omega)
      (by omega) (by omega)
  have hpair : ∃ i j, N ≤ i ∧ N ≤ j ∧ i ≠ j ∧ a i % 4 = a j % 4 := by
    have h : a N % 4 = a (N + 1) % 4 ∨ a N % 4 = a (N + 2) % 4 ∨
        a (N + 1) % 4 = a (N + 2) % 4 := by omega
    rcases h with h | h | h
    · exact ⟨N, N + 1, by omega, by omega, by omega, h⟩
    · exact ⟨N, N + 2, by omega, by omega, by omega, h⟩
    · exact ⟨N + 1, N + 2, by omega, by omega, by omega, h⟩
  obtain ⟨i, j, hi, hj, hij, heq⟩ := hpair
  have hoi := ho i hi
  have hoj := ho j hj
  have hd2 : 2 ∣ a i + a j := by omega
  have hd4 : ¬ 4 ∣ a i + a j := by omega
  have hc1 : (1 : Fin 2) = col := by simpa [colour, hd2, hd4] using hTwo hij
  exact (by decide : (0 : Fin 2) ≠ 1) (hc0.trans hc1.symm)

/--
**Smith's counterexample to Erdős Problem 1198.** There is a colouring
$c : \mathbb{N} \to \{0, 1\}$ such that for every strictly increasing sequence
$0 < a_0 < a_1 < \cdots$ of natural numbers, the numbers $\sum_{j < k} \prod_{i \in S_j} a_i$,
taken over all $k \ge 1$ and all pairwise disjoint nonempty finite sets
$S_0, \dots, S_{k-1} \subseteq \mathbb{N}$ other than those with $k = 1$ and $|S_0| = 1$, do not
all have the same colour.

Smith (SIAM J. Discrete Math. 2001) constructed, for $m \ne n$, a two-cell partition of
$\mathbb{N}$ in which no cell contains $SP_n(x) \cup SP_m(y)$ for any sequences $x$ and $y$, where
$SP_m(x)$ is the set of sums $\prod_{t \in F_1} x_t + \cdots + \prod_{t \in F_m} x_t$ over nonempty
finite sets $F_1 < \cdots < F_m$ (here $F < F'$ means that every element of $F$ is less than every
element of $F'$). Taking $x = y = a$, $m = 2$ and $n = 3$, every such sum is one of the numbers
above, so they cannot all have one colour. Hindman's theorem is the case where every $S_j$ is a
singleton.

Source: T. F. Bloom, Erdős Problems, Problem
#1198, https://www.erdosproblems.com/1198 (status DISPROVED); resolution: G. L. Smith, Partitions
and (m and n) sums of products, J. Combin. Theory Ser. A 72 (1995), 77-94; G. L. Smith, Partitions
and (m and n) sums of products - two cell partition, SIAM J. Discrete Math. 14 (2001), 356-369,
erdosproblems.com/1198: a counterexample was provided by Smith [Sm95]; the two-colour counterexample
is the 2001 paper (abstract: for m ≠ n, a two cell partition of ℕ such that neither cell contains
SP_n(⟨x_t⟩) ∪ SP_m(⟨y_t⟩), SP_m the sums of m increasing products),
https://doi.org/10.1137/S0895480198349014.
-/
theorem monochromaticSumsOfProducts_refuted : ¬ monochromaticSumsOfProducts := by
  intro h
  obtain ⟨a, hmono, ha₀, col, hc⟩ := h colour
  have ha (i : ℕ) : 0 < a i := ha₀.trans_le (hmono.monotone (Nat.zero_le i))
  have hTwo {s t : Finset ℕ} (hs : s.Nonempty) (ht : t.Nonempty) (hd : Disjoint s t) :
      colour ((∏ i ∈ s, a i) + ∏ i ∈ t, a i) = col := by
    let S : Fin 2 → Finset ℕ := ![s, t]
    have hS (j : Fin 2) : (S j).Nonempty := by fin_cases j <;> assumption
    have hD : Pairwise (fun j j' ↦ Disjoint (S j) (S j')) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [S, hd.symm]
    simpa [Fin.sum_univ_two, S] using hc 2 S (by decide) hS hD (by simp)
  have hPair {i j : ℕ} (hij : i ≠ j) : colour (a i + a j) = col := by
    simpa using hTwo (s := {i}) (t := {j}) (by simp) (by simp) (by simpa)
  have hThree {i j k : ℕ} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      colour (a i + a j + a k) = col := by
    let S : Fin 3 → Finset ℕ := ![{i}, {j}, {k}]
    have hS (u : Fin 3) : (S u).Nonempty := by fin_cases u <;> simp [S]
    have hD : Pairwise (fun u v ↦ Disjoint (S u) (S v)) := by
      intro u v huv
      fin_cases u <;> fin_cases v <;> simp_all [S, Ne.symm hij, Ne.symm hik, Ne.symm hjk]
    simpa [Fin.sum_univ_three, S, add_assoc] using hc 3 S (by decide) hS hD (by simp)
  by_cases he : ∀ N, ∃ i ≥ N, 2 ∣ a i
  · by_cases hx : ∃ i, 2 ∣ a i ∧ oddPart (a i) ≠ 1
    · obtain ⟨i, hi, hxi⟩ := hx
      obtain ⟨j, hj, hjd⟩ := he (i + 1)
      have hij : i ≠ j := by omega
      have hp : 4 ∣ a i * a j := Nat.mul_dvd_mul hi hjd
      have ho : oddPart (a i * a j) ≠ 1 := by
        have heq : oddPart (a i * a j) = oddPart (a i) * oddPart (a j) :=
          Nat.ordCompl_mul (a i) (a j) 2
        rw [heq]
        intro h
        exact hxi (Nat.dvd_antisymm ⟨_, h.symm⟩ (one_dvd _))
      exact different_colours_of_nonpower ha he (A := {i, j}) (by simp)
        (by simpa [prod_pair hij]) (by simpa [prod_pair hij]) @hTwo
    · push Not at hx
      have hindex (i : ℕ) : i ≤ a i := by
        induction i with
        | zero => exact Nat.zero_le _
        | succ i ih => exact ih.trans_lt (hmono (Nat.lt_succ_self i))
      have hpowers (p : ℕ) (N : ℕ) : ∃ i ≥ N, ∃ q ≥ p, a i = 2 ^ q := by
        obtain ⟨i, hi, h2⟩ := he (max N (2 ^ p))
        have hpow : a i = 2 ^ v (a i) := by
          have h := Nat.ordProj_mul_ordCompl_eq_self (a i) 2
          change 2 ^ v (a i) * oddPart (a i) = a i at h
          rw [hx i h2, mul_one] at h
          exact h.symm
        have hle : 2 ^ p ≤ a i := (le_max_right N _).trans (hi.trans (hindex i))
        rw [hpow] at hle
        exact ⟨i, (le_max_left N _).trans hi, v (a i),
          (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp hle, hpow⟩
      obtain ⟨i, _, p, hp, hi⟩ := hpowers 2 0
      obtain ⟨j, hj, q, hq, hj'⟩ := hpowers (p + 2) (i + 1)
      obtain ⟨k, hk, r, hr, hk'⟩ := hpowers (q + (q - p) + 2) (j + 1)
      have h1 := hPair (i := i) (j := j) (by omega)
      have h0 := hThree (i := i) (j := j) (k := k) (by omega) (by omega) (by omega)
      rw [hi, hj', (colours_of_powers hp hq hr).1] at h1
      rw [hi, hj', hk', (colours_of_powers hp hq hr).2] at h0
      exact (by decide : (0 : Fin 2) ≠ 1) (h0.trans h1.symm)
  · push Not at he
    obtain ⟨N, hN⟩ := he
    exact different_colours_of_eventually_odd hN @hPair @hThree

end MathlibExt.Combinatorics.MonochromaticSumsOfProductsErdosProblem1198Wanted
