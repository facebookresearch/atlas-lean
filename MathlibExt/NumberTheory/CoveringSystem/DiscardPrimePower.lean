/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.GCDMonoid.Finset
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

/-- **Merging the p classes whose modulus is divisible by a prime power.** Let $C$ be a
covering system with positive moduli: a finite set of congruences $x \equiv r \pmod m$ with
$r \in \mathbb{Z}$ and $m \ge 1$ such that every integer satisfies at least one of them. Let $p$
be a prime and $a \ge 1$, and suppose exactly $p$ congruences of $C$ have modulus divisible by
$p^a$, with moduli $p^a m_1, \dots, p^a m_p$. Then for some $r \in \mathbb{Z}$, replacing these
$p$ congruences by the single congruence $x \equiv r \pmod{p^{a-1} \operatorname{lcm}(m_1,
\dots, m_p)}$ still gives a covering system.

Source: Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
INTEGERS 26 (2026), Article A38, Lemma 2 (`integers-2026-A38-lem-2`), quoting Dalton–Trifonov,
Corollary 9. -/
public theorem exists_isCoveringSystem_merge_prime_power (classes : Finset (ℤ × ℕ))
    (hcov : Int.IsCoveringSystem classes) (hpos : ∀ c ∈ classes, 0 < c.2) {p a : ℕ}
    (hp : p.Prime) (ha : 0 < a) (hcard : (classes.filter fun c => p ^ a ∣ c.2).card = p) :
    ∃ r : ℤ, Int.IsCoveringSystem
      (insert (r, p ^ (a - 1) * (classes.filter fun c => p ^ a ∣ c.2).lcm fun c => c.2 / p ^ a)
        (classes.filter fun c => ¬ p ^ a ∣ c.2)) := by
  let keep := classes.filter fun c => ¬ p ^ a ∣ c.2
  let drop := classes.filter fun c => p ^ a ∣ c.2
  let K := (keep.lcm Prod.snd).lcm (p ^ (a - 1))
  let Miss (z : ℤ) := ¬ ∃ c ∈ keep, z ≡ c.1 [ZMOD c.2]
  have hkeep₀ (c) (hc : c ∈ keep) : c.2 ≠ 0 := (hpos c (Finset.mem_filter.mp hc).1).ne'
  have hlcm₀ : keep.lcm Prod.snd ≠ 0 := Finset.lcm_ne_zero_iff.mpr hkeep₀
  have hpow₀ : p ^ (a - 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
  -- Use a common period of the retained classes with p-adic valuation exactly a - 1.
  have hK : ¬ p ^ a ∣ K := by
    rw [hp.pow_dvd_iff_le_factorization (Nat.lcm_ne_zero hlcm₀ hpow₀), not_le,
      Nat.factorization_lcm hlcm₀ hpow₀, Finsupp.sup_apply, sup_lt_iff,
      Finset.factorization_lcm hkeep₀, Finset.sup_lt_iff ha, Nat.factorization_pow_self hp]
    exact ⟨fun c hc => lt_of_not_ge fun h => (Finset.mem_filter.mp hc).2
      ((hp.pow_dvd_iff_le_factorization (hkeep₀ c hc)).mpr h), by omega⟩
  have hpK : p ^ a ∣ p * K := by
    rw [← Nat.sub_add_cancel ha, pow_succ']
    exact Nat.mul_dvd_mul_left _ (Nat.dvd_lcm_right ..)
  have hmiss_shift {z : ℤ} (hz : Miss z) (i : ℕ) : Miss (z + (i : ℤ) * K) := by
    rintro ⟨c, hc, hzc⟩
    have hd : c.2 ∣ K := (Finset.dvd_lcm hc).trans (Nat.dvd_lcm_left ..)
    exact hz ⟨c, hc, (Int.left_modEq_add_iff.mpr
      ((Int.natCast_dvd_natCast.mpr hd).trans (dvd_mul_left _ _))).trans hzc⟩
  have hindex {z : ℤ} {i j : ℕ} (hi : i < p) (hj : j < p)
      (h : z + (i : ℤ) * K ≡ z + (j : ℤ) * K [ZMOD (p ^ a : ℕ)]) : i = j := by
    have h := (Int.ModEq.add_left_cancel' z h).dvd
    rw [← sub_mul] at h
    apply Nat.ModEq.eq_of_lt_of_lt _ hi hj
    rw [Nat.modEq_iff_dvd]
    by_contra hnd
    exact hK (by exact_mod_cast (Nat.prime_iff_prime_int.mp hp).pow_dvd_of_dvd_mul_left a hnd h)
  -- The first p translates of a missed integer must use all p discarded classes.
  have hhit {z : ℤ} (hz : Miss z) (c) (hc : c ∈ drop) :
      ∃ i < p, z + (i : ℤ) * K ≡ c.1 [ZMOD c.2] := by
    have hcover (i : ℕ) : ∃ d ∈ drop, z + (i : ℤ) * K ≡ d.1 [ZMOD d.2] := by
      obtain ⟨d, hd, hzd⟩ := hcov (z + (i : ℤ) * K)
      by_cases hdiv : p ^ a ∣ d.2
      · exact ⟨d, Finset.mem_filter.mpr ⟨hd, hdiv⟩, hzd⟩
      · exact (hmiss_shift hz i ⟨d, Finset.mem_filter.mpr ⟨hd, hdiv⟩, hzd⟩).elim
    choose f hf hmod using hcover
    have hinj : Set.InjOn f (Finset.range p : Set ℕ) := by
      intro i hi j hj hij
      exact hindex (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
        (((hmod i).trans (hij ▸ (hmod j).symm)).of_dvd
          (Int.natCast_dvd_natCast.mpr (Finset.mem_filter.mp (hf i)).2))
    obtain ⟨i, hi, rfl⟩ := Finset.surjOn_of_injOn_of_card_le f (fun i _ => hf i) hinj
      (by rw [Finset.card_range, hcard]) hc
    exact ⟨i, Finset.mem_range.mp hi, hmod i⟩
  -- Apply the same argument after shifting by pK. The same class must occur
  -- at the same index, so its full modulus divides pK and its reduced modulus divides K.
  have hreduce {z : ℤ} (hz : Miss z) (c) (hc : c ∈ drop) :
      z ≡ c.1 [ZMOD (p ^ (a - 1) * (c.2 / p ^ a) : ℕ)] := by
    obtain ⟨i, hi, hzi⟩ := hhit hz c hc
    obtain ⟨j, hj, hzj⟩ := hhit (hmiss_shift hz p) c hc
    have hshift : z + (j : ℤ) * K ≡ (z + (p : ℤ) * K) + (j : ℤ) * K [ZMOD (p ^ a : ℕ)] := by
      rw [add_right_comm z ((p : ℤ) * K)]
      exact Int.left_modEq_add_iff.mpr (by exact_mod_cast hpK)
    have hij := hindex hi hj (((hzi.trans hzj.symm).of_dvd
      (Int.natCast_dvd_natCast.mpr (Finset.mem_filter.mp hc).2)).trans hshift.symm)
    subst j
    rw [add_right_comm z ((p : ℤ) * K)] at hzj
    have hd : c.2 ∣ p * K := Int.natCast_dvd_natCast.mp
      (Int.left_modEq_add_iff.mp (hzi.trans hzj.symm))
    have hm : p * (p ^ (a - 1) * (c.2 / p ^ a)) = c.2 := by
      rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel ha,
        Nat.mul_div_cancel' (Finset.mem_filter.mp hc).2]
    have hdK : p ^ (a - 1) * (c.2 / p ^ a) ∣ K := by
      rw [← hm] at hd
      exact (mul_dvd_mul_iff_left hp.ne_zero).mp hd
    have hdmod : p ^ (a - 1) * (c.2 / p ^ a) ∣ c.2 :=
      dvd_of_mul_left_dvd (dvd_of_eq hm)
    exact (Int.left_modEq_add_iff.mpr
      ((Int.natCast_dvd_natCast.mpr hdK).trans (dvd_mul_left _ _))).trans
      (hzi.of_dvd (Int.natCast_dvd_natCast.mpr hdmod))
  by_cases hex : ∃ r, Miss r
  · obtain ⟨r, hr⟩ := hex
    refine ⟨r, fun z => ?_⟩
    by_cases hz : Miss z
    · refine ⟨_, Finset.mem_insert_self _ _, ?_⟩
      change z ≡ r [ZMOD (p ^ (a - 1) * drop.lcm (fun c => c.2 / p ^ a) : ℕ)]
      have hdiv (c) (hc : c ∈ drop) : p ^ (a - 1) * (c.2 / p ^ a) ∣ (r - z).natAbs :=
        Int.natCast_dvd.mp ((hreduce hz c hc).trans (hreduce hr c hc).symm).dvd
      have hne : drop.Nonempty := Finset.card_pos.mp (hcard.symm ▸ hp.pos)
      obtain ⟨c, hc⟩ := hne
      have hbase : p ^ (a - 1) ∣ (r - z).natAbs := (dvd_mul_right _ _).trans (hdiv c hc)
      rw [Int.modEq_iff_dvd, Int.natCast_dvd, ← Nat.dvd_div_iff_mul_dvd hbase]
      exact Finset.lcm_dvd fun d hd => (Nat.dvd_div_iff_mul_dvd hbase).mpr (hdiv d hd)
    · obtain ⟨c, hc, hzc⟩ := not_not.mp hz
      exact ⟨c, Finset.mem_insert_of_mem hc, hzc⟩
  · refine ⟨0, fun z => ?_⟩
    obtain ⟨c, hc, hzc⟩ := not_not.mp (fun hz : Miss z => hex ⟨z, hz⟩)
    exact ⟨c, Finset.mem_insert_of_mem hc, hzc⟩

end MetaMathlibExt
