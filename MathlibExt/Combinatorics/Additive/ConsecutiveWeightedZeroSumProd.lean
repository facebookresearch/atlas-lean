/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Finset.Max

/-!
# Consecutive weighted zero sums in a product of modules

Repeat a zero-sum-free word in the first coordinate, putting the letters of a zero-sum-free word
in the second coordinate between copies. An interval meeting a separator is detected in the
second coordinate; an interval missing all separators lies in one copy of the first word.
-/

namespace MetaMathlibExt

set_option quotPrecheck false in
local notation "HasConsecutiveSum" A:max x:max =>
  ∃ s t, s ≤ t ∧ ∃ a : _ → _, (∀ i ∈ Finset.Icc s t, a i ∈ A) ∧
    ∑ i ∈ Finset.Icc s t, a i • x i = 0

set_option quotPrecheck false in
local notation "consecutiveSet(" R ", " M ", " A ")" => {k : ℕ | 0 < k ∧ ∀ x : Fin k → M,
  ∃ s t : Fin k, s ≤ t ∧
    ∃ a : Fin k → R, (∀ i ∈ Finset.Icc s t, a i ∈ A) ∧ ∑ i ∈ Finset.Icc s t, a i • x i = 0}

private theorem exists_consecutiveFree_pred {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {A : Set R} {d : ℕ} (hd : IsLeast (consecutiveSet(R, M, A)) d) :
    ∃ x : Fin (d - 1) → M, ¬ HasConsecutiveSum A x := by
  by_cases hp : 0 < d - 1
  · by_contra! hall
    have hle := hd.2 (show d - 1 ∈ consecutiveSet(R, M, A) from ⟨hp, hall⟩)
    omega
  · exact ⟨fun _ => 0, fun ⟨s, _⟩ => hp s.pos⟩

/-- Pull an interval back along an order embedding, discarding zero entries off its image. -/
private theorem hasConsecutiveSum_of_embedding {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] {A : Set R} {n k : ℕ} (e : Fin n ↪o Fin k) {x : Fin n → M}
    {y : Fin k → M} {s t : Fin k} {a : Fin k → R}
    (hxy : ∀ j, y (e j) = x j) (ha : ∀ i ∈ Finset.Icc s t, a i ∈ A)
    (hsum : ∑ i ∈ Finset.Icc s t, a i • y i = 0)
    (hzero : ∀ i ∈ Finset.Icc s t, i ∉ Set.range e → y i = 0)
    (hne : ∃ j, e j ∈ Finset.Icc s t) : HasConsecutiveSum A x := by
  let J : Finset (Fin n) := Finset.univ.filter fun j => e j ∈ Finset.Icc s t
  have mem_J (j : Fin n) : j ∈ J ↔ e j ∈ Finset.Icc s t := by simp [J]
  obtain ⟨j, hj⟩ := hne
  have hJ : J.Nonempty := ⟨j, (mem_J j).mpr hj⟩
  let u := J.min' hJ
  let v := J.max' hJ
  have hJuv : Finset.Icc u v = J := by
    ext i
    rw [Finset.mem_Icc]
    refine ⟨fun ⟨hui, hiv⟩ => (mem_J i).mpr (Finset.mem_Icc.mpr ⟨?_, ?_⟩),
      fun hi => ⟨J.min'_le _ hi, J.le_max' _ hi⟩⟩
    · exact ((Finset.mem_Icc.mp ((mem_J u).mp (J.min'_mem hJ))).1).trans (e.monotone hui)
    · exact (e.monotone hiv).trans (Finset.mem_Icc.mp ((mem_J v).mp (J.max'_mem hJ))).2
  refine ⟨u, v, J.min'_le _ (J.max'_mem hJ), a ∘ e, ?_, ?_⟩
  · rw [hJuv]
    exact fun i hi => ha _ ((mem_J i).mp hi)
  · rw [hJuv]
    calc
      ∑ j ∈ J, (a ∘ e) j • x j = ∑ j ∈ J.map e.toEmbedding, a j • y j := by
        rw [Finset.sum_map]
        apply Finset.sum_congr rfl
        intro j _
        change a (e j) • x j = a (e j) • y (e j)
        rw [hxy]
      _ = ∑ i ∈ Finset.Icc s t, a i • y i := by
        apply Finset.sum_subset
        · rintro _ hi
          obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
          exact (mem_J j).mp hj
        · intro i hi hnot
          rw [hzero i hi (fun ⟨j, hj⟩ => hnot (Finset.mem_map.mpr
            ⟨j, (mem_J j).mpr (hj ▸ hi), hj⟩)), smul_zero]
      _ = 0 := hsum

/-- **Consecutive weighted zero-sum constant of a product of modules.** Let $R$ be a ring and
$A \subseteq R$. For an $R$-module $P$, let $C_A(P)$ be the least positive integer $k$, if one
exists, such that every sequence $x_1, \dots, x_k$ in $P$ has indices $s \le t$ and weights
$a_s, \dots, a_t \in A$ with $a_s x_s + \dots + a_t x_t = 0$. If $M$ and $N$ are $R$-modules
for which $C_A(M)$, $C_A(N)$ and $C_A(M \times N)$ all exist, then
$C_A(M \times N) \ge C_A(M) \, C_A(N)$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 2.4 (`integers-2024-A38-thm-2-4`). -/
public theorem consecutive_prod_ge {R M N : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (A : Set R) {cM cN c : ℕ}
    (hM : IsLeast (consecutiveSet(R, M, A)) cM) (hN : IsLeast (consecutiveSet(R, N, A)) cN)
    (h : IsLeast (consecutiveSet(R, M × N, A)) c) :
    cM * cN ≤ c := by
  have hm : 0 < cM := hM.1.1
  obtain ⟨x, hx⟩ := exists_consecutiveFree_pred hM
  obtain ⟨y, hy⟩ := exists_consecutiveFree_pred hN
  by_contra! hlt
  let L := cN * cM - 1
  have hc : c ≤ L := by dsimp [L]; rw [Nat.mul_comm]; omega
  -- The separators are the last positions of all but the last block of width `cM`.
  let sep (j : Fin (cN - 1)) : Fin L := ⟨j.val * cM + (cM - 1), by
    have hj := Nat.mul_lt_mul_of_pos_right (show j.val + 1 < cN by omega) hm
    rw [Nat.add_mul, Nat.one_mul] at hj
    dsimp [L]
    omega⟩
  let eN : Fin (cN - 1) ↪o Fin L := OrderEmbedding.ofStrictMono sep fun i j hij => by
    exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right hij hm) _
  let zM (i : Fin L) : M :=
    if hi : i.val % cM < cM - 1 then x ⟨i.val % cM, hi⟩ else 0
  let zN : Fin L → N := Function.extend eN y (fun _ => 0)
  -- Restrict to the prefix of length `c`, then lift its interval back to the full word.
  obtain ⟨s₀, t₀, hst, a₀, ha₀, hsum₀⟩ := h.1.2
    (fun i => (zM (i.castLE hc), zN (i.castLE hc)))
  let s := s₀.castLE hc
  let t := t₀.castLE hc
  let a : Fin L → R := Function.extend (Fin.castLEEmb hc) a₀ (fun _ => 0)
  have ha : ∀ i ∈ Finset.Icc s t, a i ∈ A := by
    rw [← Fin.map_castLEEmb_Icc s₀ t₀ hc]
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    simpa only [a, (Fin.castLEEmb hc).injective.extend_apply] using ha₀ j hj
  have hsum : ∑ i ∈ Finset.Icc s t, a i • (zM i, zN i) = 0 := by
    rw [← Fin.map_castLEEmb_Icc s₀ t₀ hc, Finset.sum_map]
    simp only [a, (Fin.castLEEmb hc).injective.extend_apply]
    exact hsum₀
  by_cases hsep : ∃ j, eN j ∈ Finset.Icc s t
  · apply hy
    refine hasConsecutiveSum_of_embedding eN (y := zN) (eN.injective.extend_apply y _) ha
      ?_ ?_ hsep
    · simpa only [Prod.snd_sum, Prod.smul_snd, Prod.snd_zero] using congrArg Prod.snd hsum
    · exact fun i _ hi => Function.extend_apply' y (fun _ => 0) i hi
  · let b := s.val / cM
    have hlo : b * cM ≤ s.val := Nat.div_mul_le_self _ _
    have hst' : s.val ≤ t.val := hst
    have ht : t.val < L := t.isLt
    have hhi : t.val < b * cM + (cM - 1) := by
      by_contra! hb
      have hs := Nat.lt_mul_div_succ s.val hm
      rw [Nat.mul_comm cM, Nat.add_mul, Nat.one_mul] at hs
      change s.val < b * cM + cM at hs
      have hb' : b < cN - 1 := by
        by_contra! hle
        have hmul := Nat.mul_le_mul_right cM (show cN ≤ b + 1 from by omega)
        rw [Nat.add_mul, Nat.one_mul] at hmul
        dsimp [L] at ht
        omega
      apply hsep
      exact ⟨⟨b, hb'⟩, Finset.mem_Icc.mpr ⟨show s.val ≤ b * cM + (cM - 1) by omega, hb⟩⟩
    -- With no separator, the whole interval is in the block containing `s`.
    let block (j : Fin (cM - 1)) : Fin L := ⟨b * cM + j.val, by
      have hj := j.isLt
      have hb : b < cN := (Nat.div_lt_iff_lt_mul hm).mpr (by dsimp [L] at ht; omega)
      have hmul := Nat.mul_le_mul_right cM (show b + 1 ≤ cN by omega)
      rw [Nat.add_mul, Nat.one_mul] at hmul
      dsimp [L]
      omega⟩
    let eM : Fin (cM - 1) ↪o Fin L := OrderEmbedding.ofStrictMono block fun i j hij => by
      exact Nat.add_lt_add_left hij _
    have hrange (i : Fin L) (hi : i ∈ Finset.Icc s t) : i ∈ Set.range eM := by
      have hsi : s.val ≤ i.val := (Finset.mem_Icc.mp hi).1
      have hit : i.val ≤ t.val := (Finset.mem_Icc.mp hi).2
      refine ⟨⟨i.val - b * cM, by omega⟩, Fin.ext ?_⟩
      change b * cM + (i.val - b * cM) = i.val
      omega
    apply hx
    refine hasConsecutiveSum_of_embedding eM (y := zM) ?_ ha ?_
      (fun i hi hn => (hn (hrange i hi)).elim) ?_
    · intro i
      change zM (block i) = x i
      have hi : i.val < cM := lt_of_lt_of_le i.isLt (Nat.sub_le _ _)
      have hmod : (block i).val % cM = i.val := by
        change (b * cM + i.val) % cM = i.val
        rw [Nat.mul_comm b, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
      simp [zM, hmod, i.isLt]
    · simpa only [Prod.fst_sum, Prod.smul_fst, Prod.fst_zero] using congrArg Prod.fst hsum
    · have hs : s ∈ Finset.Icc s t := Finset.left_mem_Icc.mpr hst
      obtain ⟨j, hj⟩ := hrange s hs
      exact ⟨j, hj ▸ hs⟩

end MetaMathlibExt
