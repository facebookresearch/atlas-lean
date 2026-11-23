/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Nat.Factorization.Basic
public import MathlibExt.NumberTheory.CoveringSystem

/-! # Swapping two residues modulo a prime in a covering system -/

namespace MetaMathlibExt

namespace isCoveringSystem_swap_residues_mod_prime

/-- If `p ∤ m` and `m ∣ L`, every prime power dividing `m` divides the shift. -/
private theorem shift_modEq_zero {L p m : ℕ} {t : ℤ} (hL : L ≠ 0) (hm : m ∣ L)
    (hpm : ¬ p ∣ m)
    (htq : ∀ q : ℕ, q.Prime → q ∣ L → q ≠ p → t ≡ 0 [ZMOD ((q ^ L.factorization q : ℕ) : ℤ)]) :
    t ≡ 0 [ZMOD m] := by
  rw [Int.modEq_zero_iff_dvd, Int.natCast_dvd, Nat.dvd_iff_prime_pow_dvd_dvd]
  intro q k hq hqk
  obtain rfl | hk := eq_or_ne k 0
  · simp
  have hqm := (dvd_pow_self q hk).trans hqk
  have hqt := htq q hq (hqm.trans hm) (fun heq => hpm (heq ▸ hqm))
  exact ((hq.pow_dvd_iff_dvd_ordProj hL).mp (hqk.trans hm)).trans
    (Int.natCast_dvd.mp (Int.modEq_zero_iff_dvd.mp hqt))

end isCoveringSystem_swap_residues_mod_prime

/-- **Swapping two residues modulo a prime in a covering system.** Let $C$ be a covering system
with positive moduli: a finite set of congruences $x \equiv a \pmod m$ with $a \in \mathbb{Z}$
and $m \ge 1$ such that every integer satisfies at least one of them. Let $L$ be the least
common multiple of its moduli, $p$ a prime dividing $L$, and $a_1 < a_2 \le p - 1$ natural
numbers. For a prime $\ell$ write $\nu_\ell(L)$ for the exponent of $\ell$ in $L$, and let
$C_p(\alpha)$ be the set of congruences $x \equiv a \pmod m$ in $C$ with $p \mid m$ and
$a \equiv \alpha \pmod p$. Let $t \in \mathbb{Z}$ satisfy $t \equiv a_2 - a_1 \pmod{p^{\nu_p(L)}}$
and $t \equiv 0 \pmod{q^{\nu_q(L)}}$ for every prime $q \ne p$ dividing $L$. Then the
congruences of $C$ outside $C_p(a_1) \cup C_p(a_2)$, together with $x \equiv a + t \pmod m$ for
each $x \equiv a \pmod m$ in $C_p(a_1)$ and $x \equiv a - t \pmod m$ for each
$x \equiv a \pmod m$ in $C_p(a_2)$, form a covering system.

Source: Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
INTEGERS 26 (2026), Article A38, Lemma 4 (`integers-2026-A38-lem-4`), from the author's thesis,
Lemma 2.13. -/
public theorem isCoveringSystem_swap_residues_mod_prime (classes : Finset (ℤ × ℕ))
    (hcov : Int.IsCoveringSystem classes) (hpos : ∀ c ∈ classes, 0 < c.2) {L p : ℕ}
    (hL : L = classes.lcm Prod.snd) (hp : p.Prime) (hpL : p ∣ L) {a₁ a₂ : ℕ} (h₁₂ : a₁ < a₂)
    (h₂ : a₂ ≤ p - 1) (t : ℤ)
    (htp : t ≡ (a₂ : ℤ) - a₁ [ZMOD ((p ^ L.factorization p : ℕ) : ℤ)])
    (htq : ∀ q : ℕ, q.Prime → q ∣ L → q ≠ p → t ≡ 0 [ZMOD ((q ^ L.factorization q : ℕ) : ℤ)]) :
    Int.IsCoveringSystem
      ((classes.filter fun c => ¬ (p ∣ c.2 ∧ (c.1 ≡ a₁ [ZMOD p] ∨ c.1 ≡ a₂ [ZMOD p]))) ∪
        (classes.filter fun c => p ∣ c.2 ∧ c.1 ≡ a₁ [ZMOD p]).image (fun c => (c.1 + t, c.2)) ∪
        (classes.filter fun c => p ∣ c.2 ∧ c.1 ≡ a₂ [ZMOD p]).image (fun c => (c.1 - t, c.2))) := by
  have hL₀ : L ≠ 0 := hL ▸ Finset.lcm_ne_zero_iff.mpr fun c hc => (hpos c hc).ne'
  have ht : t ≡ (a₂ : ℤ) - a₁ [ZMOD p] :=
    htp.of_dvd (Int.natCast_dvd_natCast.mpr
      (dvd_pow_self p (hp.factorization_pos_of_dvd hL₀ hpL).ne'))
  have ht₀ {c : ℤ × ℕ} (hc : c ∈ classes) (hpc : ¬ p ∣ c.2) : t ≡ 0 [ZMOD c.2] :=
    isCoveringSystem_swap_residues_mod_prime.shift_modEq_zero hL₀
      (hL ▸ Finset.dvd_lcm hc) hpc htq
  intro z
  have residue_eq (a : ℕ) (ha : a < p) : z ≡ a [ZMOD p] ↔ z % p = a := by
    simp only [Int.ModEq, Int.emod_eq_of_lt (Int.natCast_nonneg a) (Int.ofNat_lt.mpr ha)]
  have ha₂ : a₂ < p := by omega
  have ha₁ := h₁₂.trans ha₂
  -- Over the first residue, look up the integer shifted into the second residue.
  by_cases hz₁ : z % p = a₁
  · obtain ⟨c, hc, hzc⟩ := hcov (z + t)
    by_cases hpc : p ∣ c.2
    · have hz := (residue_eq a₁ ha₁).mpr hz₁
      have hca : c.1 ≡ a₂ [ZMOD p] := by
        simpa using (hzc.of_dvd (Int.natCast_dvd_natCast.mpr hpc)).symm.trans (hz.add ht)
      refine ⟨_, Finset.mem_union_right _ (Finset.mem_image_of_mem _
        (Finset.mem_filter.mpr ⟨hc, hpc, hca⟩)), ?_⟩
      simpa using hzc.sub_right t
    · refine ⟨c, Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hc, fun h => hpc h.1⟩)), ?_⟩
      simpa using hzc.sub (ht₀ hc hpc)
  -- Over the second residue, use the opposite shift.
  by_cases hz₂ : z % p = a₂
  · obtain ⟨c, hc, hzc⟩ := hcov (z - t)
    by_cases hpc : p ∣ c.2
    · have hz := (residue_eq a₂ ha₂).mpr hz₂
      have hca : c.1 ≡ a₁ [ZMOD p] := by
        simpa using (hzc.of_dvd (Int.natCast_dvd_natCast.mpr hpc)).symm.trans (hz.sub ht)
      refine ⟨_, Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _
        (Finset.mem_filter.mpr ⟨hc, hpc, hca⟩))), ?_⟩
      simpa using hzc.add_right t
    · refine ⟨c, Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hc, fun h => hpc h.1⟩)), ?_⟩
      simpa using hzc.add (ht₀ hc hpc)
  -- Every other residue keeps its original covering class.
  obtain ⟨c, hc, hzc⟩ := hcov z
  refine ⟨c, Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_filter.mpr ⟨hc, ?_⟩)), hzc⟩
  rintro ⟨hpc, ha | ha⟩
  · exact hz₁ ((residue_eq a₁ ha₁).mp ((hzc.of_dvd (by exact_mod_cast hpc)).trans ha))
  · exact hz₂ ((residue_eq a₂ ha₂).mp ((hzc.of_dvd (by exact_mod_cast hpc)).trans ha))

end MetaMathlibExt
