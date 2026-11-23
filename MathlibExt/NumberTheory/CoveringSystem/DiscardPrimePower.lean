/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
public import MathlibExt.NumberTheory.CoveringSystem
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Data.Nat.Prime.Int

/-!
# Discarding prime-power multiples in a distinct covering system

For prime `p` and positive `a`, if all moduli of a distinct covering system are less than
`p ^ a * (p + 1)`, the classes whose moduli are divisible by `p ^ a` can be discarded.
-/

namespace MetaMathlibExt

namespace isCoveringSystem_filter_not_dvd_of_lt

/-- A class of modulus zero is redundant because the positive moduli have a common period. -/
private theorem exists_nonzero_modulus {C : Finset (ℤ × ℕ)} (hcov : Int.IsCoveringSystem C)
    (hdist : Set.InjOn Prod.snd (C : Set (ℤ × ℕ))) (z : ℤ) :
    ∃ c ∈ C, c.2 ≠ 0 ∧ z ≡ c.1 [ZMOD c.2] := by
  obtain ⟨c, hc, hzc⟩ := hcov z
  by_cases hzero : c.2 = 0
  · let pos := C.filter fun d => d.2 ≠ 0
    let L := pos.lcm Prod.snd
    have hL : L ≠ 0 := Finset.lcm_ne_zero_iff.mpr fun d hd => (Finset.mem_filter.mp hd).2
    obtain ⟨d, hd, hzd⟩ := hcov (z + L)
    have hd₀ : d.2 ≠ 0 := by
      intro heq
      have hcd : c = d := hdist hc hd (hzero.trans heq.symm)
      subst d
      simp [hzero, Int.ModEq] at hzc hzd
      omega
    refine ⟨d, hd, hd₀, Int.ModEq.trans ?_ hzd⟩
    exact Int.left_modEq_add_iff.mpr (Int.natCast_dvd_natCast.mpr
      (Finset.dvd_lcm (Finset.mem_filter.mpr ⟨hd, hd₀⟩) : d.2 ∣ L))
  · exact ⟨c, hc, hzero, hzc⟩

/-- If every positive multiple of `p ^ a` occurring as a modulus has quotient less than
`p`, there are too few such classes to cover a progression missed by the other classes. -/
private theorem filter_of_small_quotients {C : Finset (ℤ × ℕ)} (hcov : Int.IsCoveringSystem C)
    (hdist : Set.InjOn Prod.snd (C : Set (ℤ × ℕ))) {p a : ℕ} (hp : p.Prime) (ha : 0 < a)
    (hsmall : ∀ c ∈ C, p ^ a ∣ c.2 → c.2 / p ^ a < p) :
    Int.IsCoveringSystem (C.filter fun c => ¬ p ^ a ∣ c.2) := by
  let keep := C.filter fun c => ¬ p ^ a ∣ c.2
  let L := keep.lcm Prod.snd
  have hnonzero (c) (hc : c ∈ keep) : c.2 ≠ 0 :=
    fun h => (Finset.mem_filter.mp hc).2 (h ▸ dvd_zero _)
  have hL : ¬ p ^ a ∣ L := by
    rw [hp.pow_dvd_iff_le_factorization (Finset.lcm_ne_zero_iff.mpr hnonzero), not_le,
      Finset.factorization_lcm hnonzero, Finset.sup_lt_iff ha]
    intro c hc
    exact lt_of_not_ge fun h => (Finset.mem_filter.mp hc).2
      ((hp.pow_dvd_iff_le_factorization (hnonzero c hc)).mpr h)
  intro z
  by_contra hmiss
  -- The classes covering the translates of z must all have discarded moduli.
  choose c hc hc₀ hmod using fun i : ℕ => exists_nonzero_modulus hcov hdist (z + ↑(i * L))
  have hdvd (i) : p ^ a ∣ (c i).2 := by
    by_contra h
    have hmem : c i ∈ keep := Finset.mem_filter.mpr ⟨hc i, h⟩
    apply hmiss
    refine ⟨c i, hmem, Int.ModEq.trans ?_ (hmod i)⟩
    exact Int.left_modEq_add_iff.mpr (Int.natCast_dvd_natCast.mpr
      ((Finset.dvd_lcm hmem : (c i).2 ∣ L).trans (dvd_mul_left _ _)))
  -- The first p translates need distinct quotients in the interval (0, p).
  let k (i : ℕ) := (c i).2 / p ^ a
  have hk (i : ℕ) : k i ∈ Finset.Ioo 0 p := Finset.mem_Ioo.mpr
    ⟨Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (hc₀ i)) (hdvd i)) (pow_pos hp.pos _),
      hsmall _ (hc i) (hdvd i)⟩
  have hinj (i : ℕ) (hi : i < p) (j : ℕ) (hj : j < p) (heq : k i = k j) : i = j := by
    have hmoduli : (c i).2 = (c j).2 := by
      simpa only [k, Nat.mul_div_cancel' (hdvd i), Nat.mul_div_cancel' (hdvd j)] using
        congrArg (p ^ a * ·) heq
    have hclasses : c i = c j := hdist (hc i) (hc j) hmoduli
    have hz := (hmod i).trans (hclasses ▸ (hmod j).symm)
    have h := (Int.ModEq.add_left_cancel' z (hz.of_dvd (Int.natCast_dvd_natCast.mpr
      (hdvd i)))).dvd
    push_cast at h
    rw [← sub_mul] at h
    apply Nat.ModEq.eq_of_lt_of_lt _ hi hj
    rw [Nat.modEq_iff_dvd]
    by_contra hnd
    exact hL (by exact_mod_cast (Nat.prime_iff_prime_int.mp hp).pow_dvd_of_dvd_mul_left a hnd h)
  have hcard := Finset.le_card_of_inj_on_range k (fun i _ => hk i) hinj
  rw [Nat.card_Ioo] at hcard
  have := hp.pos
  omega

end isCoveringSystem_filter_not_dvd_of_lt

open isCoveringSystem_filter_not_dvd_of_lt

/-- **Discarding the classes whose modulus is divisible by a large prime power.** Let $C$ be a
distinct covering system: a finite set of congruences $x \equiv r \pmod m$ with
$r \in \mathbb{Z}$ and $m \in \mathbb{N}$ (where $x \equiv r \pmod 0$ means $x = r$), no two
with the same modulus, such that every integer satisfies at least one of them. Let
$B \in \mathbb{N}$ be at least every modulus of $C$, let $p$ be a prime and $a \ge 1$. If
$B < p^a (p + 1)$, then the congruences of $C$ whose modulus is not divisible by $p^a$ still
cover every integer.

Source: Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
INTEGERS 26 (2026), Article A38, Lemma 1 (`integers-2026-A38-lem-1`), quoting Krukenberg,
Corollary 2.3, and Dalton–Trifonov, Corollary 8. -/
public theorem isCoveringSystem_filter_not_dvd_of_lt (classes : Finset (ℤ × ℕ))
    (hcov : Int.IsCoveringSystem classes) (hdist : Set.InjOn Prod.snd (classes : Set (ℤ × ℕ)))
    (B : ℕ) (hB : ∀ c ∈ classes, c.2 ≤ B) {p a : ℕ} (hp : p.Prime) (ha : 0 < a)
    (hpa : B < p ^ a * (p + 1)) :
    Int.IsCoveringSystem (classes.filter fun c => ¬ p ^ a ∣ c.2) := by
  -- First discard multiples of the next power, including the possible modulus p ^ (a + 1).
  let C := classes.filter fun c => ¬ p ^ (a + 1) ∣ c.2
  have hhigh : Int.IsCoveringSystem C :=
    filter_of_small_quotients hcov hdist hp (Nat.succ_pos a) (by
      intro c hc _
      apply Nat.div_lt_of_lt_mul
      refine (hB c hc).trans_lt (hpa.trans_le ?_)
      rw [pow_succ, Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ (lt_mul_self hp.one_lt))
  have hdist' : Set.InjOn Prod.snd (C : Set (ℤ × ℕ)) :=
    hdist.mono (Finset.filter_subset _ _)
  -- In C the quotient by p ^ a is at most p, and equality would give the excluded next power.
  have hlow := filter_of_small_quotients hhigh hdist' hp ha (by
    intro c hc hd
    obtain ⟨hc, hnext⟩ := Finset.mem_filter.mp hc
    have hlt := Nat.div_lt_of_lt_mul ((hB c hc).trans_lt hpa)
    have hne : c.2 / p ^ a ≠ p := by
      intro heq
      apply hnext
      rw [pow_succ, ← Nat.dvd_div_iff_mul_dvd hd, heq]
    omega)
  intro z
  obtain ⟨c, hc, hz⟩ := hlow z
  obtain ⟨hc, hd⟩ := Finset.mem_filter.mp hc
  exact ⟨c, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hc).1, hd⟩, hz⟩

end MetaMathlibExt
