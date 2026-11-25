/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.FixedPerimeterAlder
import Mathlib.Data.Sym.Card

/-!
# Counting partitions with parts in one residue class

For a prescribed largest part and length, we characterize when the residue-class partition
count is nonzero and express it as a binomial coefficient.
-/

namespace MetaMathlibExt
namespace perimeterResidueArmLegCount_ne_zero_iff_and_eq_choose

private theorem sup_mem_of_card_pos {s : Multiset ℕ} (hs : 0 < s.card) : s.sup ∈ s := by
  have h := s.toFinset.sup_mem_of_nonempty (f := id)
    (Multiset.toFinset_nonempty.mpr (Multiset.card_pos.mp hs))
  simpa [Finset.sup_def] using h

-- Once the largest part is fixed, the other j parts form a multiset on q + 1 choices.
private theorem count_progression {d a m q : ℕ} (j : ℕ) (hn : 0 < d + 1)
    (ha : 0 < a) (had : a ≤ d + 1) (hmq : m = a + (d + 1) * q) :
    perimeterResidueArmLegCount d a m (j + 1) = (q + j).choose j := by
  let e : Fin (q + 1) ↪ ℕ :=
    ⟨fun i => a + (d + 1) * i, fun _ _ h =>
      Fin.ext (Nat.eq_of_mul_eq_mul_left hn (Nat.add_left_cancel h))⟩
  let parts := Finset.univ.map e
  have hparts {x : ℕ} : x ∈ parts ↔ 0 < x ∧ x ≤ m ∧ x ≡ a [MOD d + 1] := by
    constructor
    · intro hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
      change 0 < a + (d + 1) * i.val ∧ a + (d + 1) * i.val ≤ m ∧
        a + (d + 1) * i.val ≡ a [MOD d + 1]
      have hi : i.val ≤ q := Nat.le_of_lt_succ i.isLt
      exact ⟨by omega, hmq ▸ Nat.add_le_add_left (Nat.mul_le_mul_left _ hi) _, by simp⟩
    · rintro ⟨hx, hxm, hr⟩
      have hax := hr.symm.le_of_lt_add (show a < x + (d + 1) by omega)
      obtain ⟨i, rfl⟩ := (Nat.modEq_iff_exists_eq_add hax).mp hr.symm
      rw [hmq, Nat.add_le_add_iff_left, Nat.mul_le_mul_left_iff hn] at hxm
      exact Finset.mem_map.mpr ⟨⟨i, by omega⟩, Finset.mem_univ _, rfl⟩
  have hmax : m ∈ parts := Finset.mem_map.mpr ⟨Fin.last q, Finset.mem_univ _, hmq.symm⟩
  have hset :
      ((fixedPerimeterPartitions (m + (j + 1) - 1)).filter fun s =>
        s.sup = m ∧ s.card = j + 1 ∧ ∀ x ∈ s, x ≡ a [MOD d + 1]) =
      (parts.sym j).map (symConsEmbedding m j) := by
    ext s
    rw [Finset.mem_filter, mem_fixedPerimeterPartitions, Finset.mem_map]
    constructor
    · rintro ⟨⟨hpos, -⟩, hsup, hcard, hres⟩
      have hms : m ∈ s := hsup ▸ sup_mem_of_card_pos (hcard ▸ Nat.zero_lt_succ j)
      refine ⟨Sym.mk (s.erase m) (by rw [Multiset.card_erase_of_mem hms, hcard]; rfl), ?_,
        Multiset.cons_erase hms⟩
      apply Finset.mem_sym_iff.mpr
      intro x hx
      have hxs := Multiset.mem_of_mem_erase (show x ∈ s.erase m from hx)
      exact hparts.mpr ⟨hpos x hxs, hsup ▸ Multiset.le_sup hxs, hres x hxs⟩
    · rintro ⟨t, ht, rfl⟩
      let s := m ::ₘ (t : Multiset ℕ)
      have hallowed : ∀ x ∈ s, x ∈ parts := by
        intro x hx
        rcases Multiset.mem_cons.mp hx with rfl | hx
        · exact hmax
        · exact Finset.mem_sym_iff.mp ht x hx
      have hsup : s.sup = m := le_antisymm
        (Multiset.sup_le.mpr fun x hx => (hparts.mp (hallowed x hx)).2.1)
        (Multiset.le_sup (Multiset.mem_cons_self m _))
      have hcard : s.card = j + 1 := by simp [s]
      exact ⟨⟨fun x hx => (hparts.mp (hallowed x hx)).1, by change s.sup + s.card = _; omega⟩,
        hsup, hcard, fun x hx => (hparts.mp (hallowed x hx)).2.2⟩
  rw [perimeterResidueArmLegCount, hset, Finset.card_map]
  simp only [parts, Finset.sym_map, Finset.card_map, Finset.sym_univ, Finset.card_univ,
    Sym.card_sym_eq_choose, Fintype.card_fin]
  congr 1
  omega

end perimeterResidueArmLegCount_ne_zero_iff_and_eq_choose

open perimeterResidueArmLegCount_ne_zero_iff_and_eq_choose in
/-- **Nonvanishing and binomial count for parts $\equiv a \pmod{d+1}$.** Let $d$, $a$, $\alpha$
and $\lambda$ be positive integers with $a \le d + 1$, and let $f_d^{(a)}(\alpha, \lambda)$ be the
number of partitions into parts congruent to $a$ modulo $d + 1$ with largest part $\alpha$ and
exactly $\lambda$ parts. Then $f_d^{(a)}(\alpha, \lambda) \ne 0$ if and only if $\alpha \ge a$ and
$\alpha \equiv a \pmod{d + 1}$, and in that case
$f_d^{(a)}(\alpha, \lambda) = \binom{(\alpha - a)/(d + 1) + \lambda - 1}{\lambda - 1}$.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Lemma 2. -/
public theorem perimeterResidueArmLegCount_ne_zero_iff_and_eq_choose {d a m k : ℕ}
    (hd : 0 < d) (ha : 0 < a) (hm : 0 < m) (hk : 0 < k) (had : a ≤ d + 1) :
    (perimeterResidueArmLegCount d a m k ≠ 0 ↔ a ≤ m ∧ m ≡ a [MOD d + 1]) ∧
      (a ≤ m → m ≡ a [MOD d + 1] →
        perimeterResidueArmLegCount d a m k = ((m - a) / (d + 1) + k - 1).choose (k - 1)) := by
  have hcount (ham : a ≤ m) (hr : m ≡ a [MOD d + 1]) :
      perimeterResidueArmLegCount d a m k = ((m - a) / (d + 1) + k - 1).choose (k - 1) := by
    obtain ⟨q, hmq⟩ := (Nat.modEq_iff_exists_eq_add ham).mp hr.symm
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    have hn := hd.trans_le (Nat.le_succ d)
    have hdiv : (m - a) / (d + 1) = q := by simp [hmq, Nat.mul_div_cancel_left _ hn]
    rw [hdiv, ← Nat.add_assoc q j 1, Nat.add_sub_cancel, Nat.succ_sub_one]
    exact count_progression j hn ha had hmq
  refine ⟨⟨?_, ?_⟩, hcount⟩
  · intro h
    obtain ⟨s, hs⟩ := Finset.card_ne_zero.mp h
    obtain ⟨-, hsup, hcard, hres⟩ := Finset.mem_filter.mp hs
    have hr := hres m (hsup ▸ sup_mem_of_card_pos (hcard ▸ hk))
    exact ⟨hr.symm.le_of_lt_add (by omega), hr⟩
  · rintro ⟨ham, hr⟩
    rw [hcount ham hr]
    exact (Nat.choose_pos (Nat.sub_le_sub_right (Nat.le_add_left k _) 1)).ne'

end MetaMathlibExt
