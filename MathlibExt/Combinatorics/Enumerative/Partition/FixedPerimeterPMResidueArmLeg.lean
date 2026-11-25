/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.FixedPerimeterAlder
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Sym.Card

/-!
# Counting partitions with parts in two residue classes

We characterize nonvanishing for partitions into parts congruent to $a$ or $-a$
with prescribed largest part and length, and give the two binomial counts.
-/

namespace MetaMathlibExt
namespace perimeterPMResidueArmLegCount_ne_zero_iff_and_eq_choose

private theorem modEq_neg_iff {a n x : ℕ} (han : a ≤ n) :
    (x : ℤ) ≡ -a [ZMOD n] ↔ x ≡ n - a [MOD n] := by
  rw [← Int.natCast_modEq_iff, Int.natCast_sub han]
  have h : (n : ℤ) - a ≡ -(a : ℤ) [ZMOD n] := by
    rw [sub_eq_add_neg, Int.modulus_add_modEq_iff]
  exact ⟨fun hx => hx.trans h.symm, fun hx => hx.trans h⟩

/-- The allowable parts at most `m`, using the two positive residue representatives. -/
private def allowedParts (n a m : ℕ) : Finset ℕ :=
  (Finset.range (m + 1)).filter fun x => x ≡ a [MOD n] ∨ x ≡ n - a [MOD n]

private theorem mem_allowedParts {n a m x : ℕ} (han : a ≤ n) :
    x ∈ allowedParts n a m ↔
      x ≤ m ∧ ((x : ℤ) ≡ a [ZMOD n] ∨ (x : ℤ) ≡ -a [ZMOD n]) := by
  simp only [allowedParts, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff,
    Int.natCast_modEq_iff, modEq_neg_iff han]

private theorem min_allowedPart {n a x : ℕ} (ha : 0 < a) (han : 2 * a < n)
    (hx : x ≡ a [MOD n] ∨ x ≡ n - a [MOD n]) : a ≤ x := by
  have hle := Nat.mod_le x n
  obtain hx | hx := hx
  · rw [Nat.ModEq, Nat.mod_eq_of_lt (show a < n by omega)] at hx
    omega
  · rw [Nat.ModEq, Nat.mod_eq_of_lt (show n - a < n by omega)] at hx
    omega

private theorem card_allowedParts {n a m : ℕ} (hn : 0 < n) (ha : 0 < a) (han : 2 * a < n)
    (hm : m ∈ allowedParts n a m) :
    (allowedParts n a m).card = 2 * (m / n) + (if a < m % n then 2 else 1) := by
  have hpos : a % n = a := Nat.mod_eq_of_lt (by omega)
  have hneg : (n - a) % n = n - a := Nat.mod_eq_of_lt (by omega)
  have hdisj : Disjoint ((Finset.range m).filter (· ≡ a [MOD n]))
      ((Finset.range m).filter (· ≡ n - a [MOD n])) := by
    refine Finset.disjoint_left.mpr fun x hx hy => ?_
    have heq := (Finset.mem_filter.mp hx).2.symm.trans (Finset.mem_filter.mp hy).2
    change a % n = (n - a) % n at heq
    omega
  have hres := (Finset.mem_filter.mp hm).2
  -- Count each residue below m, then include m itself.
  have hcount :
      (allowedParts n a m).card =
        m / n + (if a < m % n then 1 else 0) +
          (m / n + (if n - a < m % n then 1 else 0)) + 1 := by
    rw [allowedParts, Finset.range_add_one, Finset.filter_insert, ite_eq_left hres,
      Finset.card_insert_of_notMem (fun h => Finset.notMem_range_self (Finset.mem_filter.mp h).1),
      Finset.filter_or, Finset.card_union_of_disjoint hdisj, ← Nat.count_eq_card_filter_range,
      ← Nat.count_eq_card_filter_range, Nat.count_modEq_card m hn, Nat.count_modEq_card m hn,
      hpos, hneg]
  have hrem : m % n = a ∨ m % n = n - a := by
    simpa only [Nat.ModEq, hpos, hneg] using hres
  rw [hcount]
  obtain h | h := hrem
  · simp [h, show ¬ n - a < a by omega]
    omega
  · simp [h, show a < n - a by omega]
    omega

private theorem card_sym (s : Finset ℕ) (j : ℕ) :
    (s.sym j).card = (s.card + j - 1).choose j := by
  have hs : (Finset.univ : Finset s).map (Function.Embedding.subtype _) = s := by
    exact Finset.attach_map_val
  conv_lhs =>
    rw [← hs, Finset.sym_map, Finset.card_map, Finset.sym_univ, Finset.card_univ]
  rw [Sym.card_sym_eq_choose, Fintype.card_coe]

private theorem sup_mem_of_card_pos {s : Multiset ℕ} (hs : 0 < s.card) : s.sup ∈ s := by
  have h := s.toFinset.sup_mem_of_nonempty (f := id)
    (Multiset.toFinset_nonempty.mpr (Multiset.card_pos.mp hs))
  simpa [Finset.sup_def] using h

-- Erasing one copy of the largest part identifies the remaining multiset with a symmetric power.
private theorem count_eq_choose {d a m k : ℕ} (ha : 0 < a) (ham : 2 * a < d + 3)
    (hm : 0 < m) (hk : 0 < k) (hmem : m ∈ allowedParts (d + 3) a m) :
    perimeterPMResidueArmLegCount d a m k =
      ((allowedParts (d + 3) a m).card + (k - 1) - 1).choose (k - 1) := by
  have han : a ≤ d + 3 := by omega
  have hset :
      ((fixedPerimeterPartitions (m + k - 1)).filter fun s =>
        s.sup = m ∧ s.card = k ∧ ∀ x : ℕ, x ∈ s →
          (x : ℤ) ≡ a [ZMOD d + 3] ∨ (x : ℤ) ≡ -a [ZMOD d + 3]) =
      ((allowedParts (d + 3) a m).sym (k - 1)).map (symConsEmbedding m (k - 1)) := by
    ext s
    rw [Finset.mem_filter, mem_fixedPerimeterPartitions, Finset.mem_map]
    constructor
    · rintro ⟨-, hsup, hcard, hres⟩
      have hms : m ∈ s := hsup ▸ sup_mem_of_card_pos (hcard ▸ hk)
      refine ⟨Sym.mk (s.erase m) (by
        rw [Multiset.card_erase_of_mem hms, hcard, Nat.pred_eq_sub_one]), ?_, ?_⟩
      · rw [Finset.mem_sym_iff]
        intro x hx
        have hx' := Multiset.mem_of_mem_erase (show x ∈ s.erase m from hx)
        exact (mem_allowedParts han).2 ⟨hsup ▸ Multiset.le_sup hx', hres x hx'⟩
      · exact Multiset.cons_erase hms
    · rintro ⟨t, ht, rfl⟩
      let s := m ::ₘ (t : Multiset ℕ)
      change ((∀ x ∈ s, 0 < x) ∧ s.sup + s.card = m + k - 1 + 1) ∧
        s.sup = m ∧ s.card = k ∧ ∀ x : ℕ, x ∈ s →
          (x : ℤ) ≡ a [ZMOD d + 3] ∨ (x : ℤ) ≡ -a [ZMOD d + 3]
      have ht' := Finset.mem_sym_iff.mp ht
      have hs : s.sup = m := by
        rw [show s = m ::ₘ (t : Multiset ℕ) from rfl, Multiset.sup_cons, sup_eq_left]
        exact Multiset.sup_le.mpr fun x hx => ((mem_allowedParts han).mp (ht' x hx)).1
      have hc : s.card = k := by
        dsimp [s]
        rw [Multiset.card_cons, Sym.card_coe]
        omega
      refine ⟨⟨?_, by rw [hs, hc]; omega⟩, hs, hc, ?_⟩
      · intro x hx
        rcases Multiset.mem_cons.mp hx with rfl | hx
        · exact hm
        · exact ha.trans_le (min_allowedPart ha ham (Finset.mem_filter.mp (ht' x hx)).2)
      · intro x hx
        rcases Multiset.mem_cons.mp hx with rfl | hx
        · exact ((mem_allowedParts han).mp hmem).2
        · exact ((mem_allowedParts han).mp (ht' x hx)).2
  rw [perimeterPMResidueArmLegCount, hset, Finset.card_map, card_sym]

end perimeterPMResidueArmLegCount_ne_zero_iff_and_eq_choose

open perimeterPMResidueArmLegCount_ne_zero_iff_and_eq_choose in
/-- **Nonvanishing and binomial count for parts $\equiv \pm a \pmod{d+3}$.** Let $d$, $a$,
$\alpha$ and $\lambda$ be positive integers with $a < (d + 3)/2$, and let
$\ell_d^{(a)}(\alpha, \lambda)$ be the number of partitions into parts congruent to $a$ or $-a$
modulo $d + 3$ with largest part $\alpha$ and exactly $\lambda$ parts. Then
$\ell_d^{(a)}(\alpha, \lambda) \ne 0$ if and only if $\alpha \ge a$ and
$\alpha \equiv \pm a \pmod{d + 3}$. Moreover, if $\alpha \ge a$ and $\alpha \equiv a \pmod{d + 3}$,
then $\ell_d^{(a)}(\alpha, \lambda) = \binom{2(\alpha - a)/(d + 3) + \lambda - 1}{\lambda - 1}$,
and if $\alpha \ge a$ and $\alpha \equiv -a \pmod{d + 3}$, then
$\ell_d^{(a)}(\alpha, \lambda) = \binom{2(\alpha + a)/(d + 3) + \lambda - 2}{\lambda - 1}$.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Lemma 4. -/
public theorem perimeterPMResidueArmLegCount_ne_zero_iff_and_eq_choose {d a m k : ℕ}
    (hd : 0 < d) (ha : 0 < a) (hm : 0 < m) (hk : 0 < k) (had : 2 * a < d + 3) :
    (perimeterPMResidueArmLegCount d a m k ≠ 0 ↔
        a ≤ m ∧ ((m : ℤ) ≡ a [ZMOD d + 3] ∨ (m : ℤ) ≡ -a [ZMOD d + 3])) ∧
      (a ≤ m → (m : ℤ) ≡ a [ZMOD d + 3] →
        perimeterPMResidueArmLegCount d a m k =
          (2 * ((m - a) / (d + 3)) + k - 1).choose (k - 1)) ∧
      (a ≤ m → (m : ℤ) ≡ -a [ZMOD d + 3] →
        perimeterPMResidueArmLegCount d a m k =
          (2 * ((m + a) / (d + 3)) + k - 2).choose (k - 1)) := by
  have hn : 0 < d + 3 := hd.trans_le (Nat.le_add_right d 3)
  have han : a ≤ d + 3 := by omega
  have hpos : a % (d + 3) = a := Nat.mod_eq_of_lt (by omega)
  have hneg : (d + 3 - a) % (d + 3) = d + 3 - a := Nat.mod_eq_of_lt (by omega)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro h
    obtain ⟨s, hs⟩ := Finset.card_ne_zero.mp h
    obtain ⟨-, hsup, hcard, hres⟩ := Finset.mem_filter.mp hs
    have h := hres m (hsup ▸ sup_mem_of_card_pos (hcard ▸ hk))
    exact ⟨min_allowedPart ha had (h.imp Int.natCast_modEq_iff.mp (modEq_neg_iff han).mp), h⟩
  · rintro ⟨-, hr⟩
    have hmem := (mem_allowedParts han).2 ⟨le_rfl, hr⟩
    rw [count_eq_choose ha had hm hk hmem]
    have := Finset.card_pos.mpr ⟨m, hmem⟩
    exact (Nat.choose_pos (by omega)).ne'
  · intro _ hr
    have hmem := (mem_allowedParts han).2 ⟨le_rfl, Or.inl hr⟩
    have hr' : m % (d + 3) = a := Eq.trans (Int.natCast_modEq_iff.mp hr) hpos
    have hdiv : (m - a) / (d + 3) = m / (d + 3) := by
      have heq := Nat.div_add_mod m (d + 3)
      rw [hr'] at heq
      rw [show m - a = (d + 3) * (m / (d + 3)) by omega, Nat.mul_div_cancel_left _ hn]
    rw [count_eq_choose ha had hm hk hmem, card_allowedParts hn ha had hmem, hr', hdiv]
    simp only [lt_self_iff_false, ite_false]
    congr 1
    omega
  · intro _ hr
    have hmem := (mem_allowedParts han).2 ⟨le_rfl, Or.inr hr⟩
    have hr' : m % (d + 3) = d + 3 - a := Eq.trans ((modEq_neg_iff han).mp hr) hneg
    have hdiv : (m + a) / (d + 3) = m / (d + 3) + 1 := by
      have heq := Nat.div_add_mod m (d + 3)
      rw [hr'] at heq
      rw [show m + a = (d + 3) * (m / (d + 3) + 1) by rw [Nat.mul_add, mul_one]; omega,
        Nat.mul_div_cancel_left _ hn]
    rw [count_eq_choose ha had hm hk hmem, card_allowedParts hn ha had hmem, hr', hdiv,
      ite_eq_left (show a < d + 3 - a by omega)]
    congr 1
    omega

end MetaMathlibExt
