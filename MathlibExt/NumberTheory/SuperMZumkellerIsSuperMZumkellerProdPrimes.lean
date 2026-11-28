/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SuperMZumkeller
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.Ring

/-!
# Super-m-Zumkeller numbers from distinct primes

For every finite set `S` of at least three primes, the product `∏ p ∈ S, p` is super-m-Zumkeller.
The divisor product of such a number is a product of prime powers whose exponents are divisible
by four; the divisors of each such prime power split into two complementary sets with equal
products, and splits of coprime factors combine.

The same construction applies to `2^k * (p * q)` when `k` is odd and `p` and `q` are
distinct odd primes: the divisor product again has all prime exponents divisible by four.

## References

- Harish Patodia, "Super-m-Zumkeller Numbers", *INTEGERS* 26 (2026), Article A79, pp. 1–9,
  Lemma 1, Corollary 1 and Corollary 2(i)
  (<https://math.colgate.edu/~integers/aa79/aa79.pdf>), DOI `10.5281/zenodo.20931172`.
- David M. Burton, *Elementary Number Theory*, McGraw Hill Education (India), 2012,
  cited by Patodia for the divisor-product formula in Lemma 1.
- H. Patodia and H. K. Saikia, "On m-Zumkeller numbers", *Bull. Calcutta Math. Soc.* 113 (1)
  (2021), 53–60, cited by Patodia for the definition of m-Zumkeller numbers.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.SuperMZumkellerWanted

private theorem prod_sq_of_split (D A : Finset ℕ) (hsub : A ⊆ D)
    (h : ∏ x ∈ A, x = ∏ x ∈ D \ A, x) : (∏ x ∈ A, x) ^ 2 = ∏ x ∈ D, x := by
  calc (∏ x ∈ A, x) ^ 2 = (∏ x ∈ A, x) * ∏ x ∈ D \ A, x := by rw [sq, h]
    _ = ∏ x ∈ D, x := by rw [mul_comm]; exact Finset.prod_sdiff hsub

private theorem split_of_prod_sq (D A : Finset ℕ) (hsub : A ⊆ D)
    (hpos : ∏ x ∈ A, x ≠ 0) (h : (∏ x ∈ A, x) ^ 2 = ∏ x ∈ D, x) :
    ∏ x ∈ A, x = ∏ x ∈ D \ A, x := by
  have hps : (∏ x ∈ D \ A, x) * ∏ x ∈ A, x = ∏ x ∈ D, x := Finset.prod_sdiff hsub
  rw [← h, sq] at hps
  exact (mul_right_cancel₀ hpos hps).symm

private theorem prod_mul_fst_snd (s t : Finset ℕ) :
    ∏ p ∈ s ×ˢ t, p.1 * p.2 = (∏ x ∈ s, x) ^ t.card * (∏ y ∈ t, y) ^ s.card := by
  rw [Finset.prod_product]
  change ∏ x ∈ s, ∏ y ∈ t, x * y = _
  have inner : ∀ x ∈ s, ∏ y ∈ t, x * y = x ^ t.card * ∏ y ∈ t, y := by
    intro x _
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  rw [Finset.prod_congr rfl inner, Finset.prod_mul_distrib]
  congr 1
  · exact Finset.prod_pow s t.card (fun x ↦ x)
  · exact Finset.prod_const _

private theorem exists_split_mul {u v : ℕ} (hcop : u.Coprime v)
    (Au : Finset ℕ) (hAu : Au ⊆ u.divisors)
    (eAu : ∏ x ∈ Au, x = ∏ x ∈ u.divisors \ Au, x)
    (Av : Finset ℕ) (hAv : Av ⊆ v.divisors)
    (eAv : ∏ x ∈ Av, x = ∏ x ∈ v.divisors \ Av, x) :
    ∃ A : Finset ℕ, A ⊆ (u * v).divisors ∧
      (∏ x ∈ A, x) = ∏ x ∈ (u * v).divisors \ A, x := by
  have sAu : (∏ x ∈ Au, x) ^ 2 = ∏ x ∈ u.divisors, x :=
    prod_sq_of_split _ _ hAu eAu
  have sAv : (∏ x ∈ Av, x) ^ 2 = ∏ x ∈ v.divisors, x :=
    prod_sq_of_split _ _ hAv eAv
  set S : Finset (ℕ × ℕ) := (Au ×ˢ Av) ∪ ((u.divisors \ Au) ×ˢ (v.divisors \ Av)) with hS
  have hSsub : S ⊆ u.divisors ×ˢ v.divisors := by
    rw [hS]
    exact Finset.union_subset (Finset.product_subset_product hAu hAv)
      (Finset.product_subset_product Finset.sdiff_subset Finset.sdiff_subset)
  have hdisj : Disjoint (Au ×ˢ Av) ((u.divisors \ Au) ×ˢ (v.divisors \ Av)) := by
    rw [Finset.disjoint_product]
    exact Or.inl Finset.disjoint_sdiff
  have hinj : Set.InjOn (fun p : ℕ × ℕ ↦ p.1 * p.2) ↑S :=
    (Nat.Coprime.mul_injOn_divisors hcop).mono (Finset.coe_subset.mpr hSsub)
  have hcap : Av ∩ v.divisors = Av := by
    ext x
    simp only [Finset.mem_inter]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hAv h⟩⟩
  have hc1 : (v.divisors \ Av).card = v.divisors.card - Av.card := by
    have hc := Finset.card_sdiff (s := Av) (t := v.divisors)
    rw [hcap] at hc
    exact hc
  have hle1 := Finset.card_le_card hAv
  have hcard1 : Av.card + (v.divisors \ Av).card = v.divisors.card := by omega
  have hcap2 : Au ∩ u.divisors = Au := by
    ext x
    simp only [Finset.mem_inter]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hAu h⟩⟩
  have hc2 : (u.divisors \ Au).card = u.divisors.card - Au.card := by
    have hc := Finset.card_sdiff (s := Au) (t := u.divisors)
    rw [hcap2] at hc
    exact hc
  have hle2 := Finset.card_le_card hAu
  have hcard2 : Au.card + (u.divisors \ Au).card = u.divisors.card := by omega
  have hSprod : ∏ p ∈ S, p.1 * p.2 =
      (∏ x ∈ Au, x) ^ v.divisors.card * (∏ x ∈ Av, x) ^ u.divisors.card := by
    rw [hS, Finset.prod_union hdisj, prod_mul_fst_snd, prod_mul_fst_snd, ← eAu, ← eAv,
      ← hcard1, ← hcard2, pow_add, pow_add]
    ac_rfl
  have hT : ∏ x ∈ (u * v).divisors, x =
      (∏ x ∈ u.divisors, x) ^ v.divisors.card * (∏ x ∈ v.divisors, x) ^ u.divisors.card := by
    rw [hcop.divisors_mul, Finset.prod_map]
    change ∏ x ∈ (u.divisors ×ˢ v.divisors).attach, x.val.1 * x.val.2 = _
    have hatt : ∏ x ∈ (u.divisors ×ˢ v.divisors).attach, x.val.1 * x.val.2 =
        ∏ x ∈ u.divisors ×ˢ v.divisors, x.1 * x.2 :=
      Finset.prod_attach _ (fun y : ℕ × ℕ ↦ y.1 * y.2)
    rw [hatt]
    exact prod_mul_fst_snd _ _
  have g1 : ((∏ x ∈ Au, x) ^ v.divisors.card) ^ 2 =
      (∏ x ∈ u.divisors, x) ^ v.divisors.card := by
    rw [← pow_mul, mul_comm (v.divisors.card) 2, pow_mul, sAu]
  have g2 : ((∏ x ∈ Av, x) ^ u.divisors.card) ^ 2 =
      (∏ x ∈ v.divisors, x) ^ u.divisors.card := by
    rw [← pow_mul, mul_comm (u.divisors.card) 2, pow_mul, sAv]
  have hAprod : ∏ x ∈ Finset.image (fun p : ℕ × ℕ ↦ p.1 * p.2) S, x =
      ∏ p ∈ S, p.1 * p.2 := Finset.prod_image hinj
  have hsq : (∏ x ∈ Finset.image (fun p : ℕ × ℕ ↦ p.1 * p.2) S, x) ^ 2 =
      ∏ x ∈ (u * v).divisors, x := by
    rw [hAprod, hSprod, mul_pow, g1, g2, ← hT]
  have hpos : ∏ x ∈ Finset.image (fun p : ℕ × ℕ ↦ p.1 * p.2) S, x ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro y hy
    obtain ⟨p, hpS, rfl⟩ := Finset.mem_image.mp hy
    have hp := hSsub hpS
    rw [Finset.mem_product] at hp
    obtain ⟨h1, h2⟩ := hp
    have q1 := Nat.pos_of_mem_divisors h1
    have q2 := Nat.pos_of_mem_divisors h2
    exact ne_of_gt (Nat.mul_pos q1 q2)
  have hAsub : Finset.image (fun p : ℕ × ℕ ↦ p.1 * p.2) S ⊆ (u * v).divisors := by
    intro y hy
    obtain ⟨p, hpS, rfl⟩ := Finset.mem_image.mp hy
    rw [hcop.divisors_mul]
    exact Finset.mem_map.mpr ⟨⟨p, hSsub hpS⟩, Finset.mem_attach _ _, rfl⟩
  exact ⟨Finset.image (fun p : ℕ × ℕ ↦ p.1 * p.2) S, hAsub,
    split_of_prod_sq _ _ hAsub hpos hsq⟩

private theorem exists_split_prime_pow {p e : ℕ} (hp : p.Prime) (hdiv : 4 ∣ e) :
    ∃ A : Finset ℕ, A ⊆ (p ^ e).divisors ∧
      (∏ x ∈ A, x) = ∏ x ∈ (p ^ e).divisors \ A, x := by
  obtain ⟨k, rfl⟩ := hdiv
  rcases Nat.eq_zero_or_pos k with rfl | _hkpos
  · simp only [mul_zero, pow_zero]
    refine ⟨∅, Finset.empty_subset _, ?_⟩
    rw [Finset.prod_empty, Finset.sdiff_empty, Nat.divisors_one, Finset.prod_singleton]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero _hkpos.ne'
    have hinj1 : Function.Injective (fun i : ℕ ↦ 3 * (k + 1) + 1 + i) := by
      intro a b h
      have h' : 3 * (k + 1) + 1 + a = 3 * (k + 1) + 1 + b := h
      omega
    have hinj2 : Function.Injective (fun j : ℕ ↦ p ^ j) := Nat.pow_right_injective hp.two_le
    set J : Finset ℕ := Finset.range ((k + 1) + 1) ∪
      Finset.map ⟨fun i ↦ 3 * (k + 1) + 1 + i, hinj1⟩ (Finset.range (k + 1)) with hJ
    have hJsub : J ⊆ Finset.range (4 * (k + 1) + 1) := by
      rw [hJ]
      refine Finset.union_subset ?_ ?_
      · exact Finset.range_subset.mpr (fun x hx ↦ Finset.mem_range.mpr (by omega))
      · intro x hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
        rw [Finset.mem_range] at ha
        change 3 * (k + 1) + 1 + a ∈ Finset.range (4 * (k + 1) + 1)
        rw [Finset.mem_range]
        omega
    have hdisjJ : Disjoint (Finset.range ((k + 1) + 1))
        (Finset.map ⟨fun i ↦ 3 * (k + 1) + 1 + i, hinj1⟩ (Finset.range (k + 1))) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      obtain ⟨a, ha, hax⟩ := Finset.mem_map.mp hx2
      have hax' : 3 * (k + 1) + 1 + a = x := hax
      rw [Finset.mem_range] at hx1 ha
      omega
    have hsumJ : ∑ x ∈ J, x = ∑ x ∈ Finset.range ((k + 1) + 1), x +
        ∑ x ∈ Finset.map ⟨fun i ↦ 3 * (k + 1) + 1 + i, hinj1⟩
          (Finset.range (k + 1)), x := by
      rw [hJ]
      exact Finset.sum_union hdisjJ
    have hsumMap : ∑ x ∈ Finset.map ⟨fun i ↦ 3 * (k + 1) + 1 + i, hinj1⟩
        (Finset.range (k + 1)), x =
        (k + 1) * (3 * (k + 1) + 1) + ∑ x ∈ Finset.range (k + 1), x := by
      rw [Finset.sum_map]
      change ∑ t ∈ Finset.range (k + 1), (3 * (k + 1) + 1 + t) = _
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id]
    have hR1 := Finset.sum_range_id_mul_two ((k + 1) + 1)
    have d1 : ((k + 1) + 1) - 1 = k + 1 := by omega
    rw [d1] at hR1
    have hR2 := Finset.sum_range_id_mul_two (k + 1)
    have d2 : (k + 1) - 1 = k := Nat.add_sub_cancel k 1
    rw [d2] at hR2
    have hR3 := Finset.sum_range_id_mul_two (4 * (k + 1) + 1)
    have d3 : (4 * (k + 1) + 1) - 1 = 4 * (k + 1) := by omega
    rw [d3] at hR3
    have r1 : 2 * ∑ x ∈ Finset.range ((k + 1) + 1), x = ((k + 1) + 1) * (k + 1) := by
      rw [mul_comm]; exact hR1
    have r2 : 2 * ∑ x ∈ Finset.range (k + 1), x = (k + 1) * k := by
      rw [mul_comm]; exact hR2
    have r3 : 2 * ∑ x ∈ Finset.range (4 * (k + 1) + 1), x =
        (4 * (k + 1) + 1) * (4 * (k + 1)) := by
      rw [mul_comm]; exact hR3
    have rearr : 2 * (∑ x ∈ J, x + ∑ x ∈ J, x) =
        2 * (2 * ∑ x ∈ Finset.range ((k + 1) + 1), x) +
        2 * (2 * ∑ x ∈ Finset.range (k + 1), x) +
        4 * ((k + 1) * (3 * (k + 1) + 1)) := by
      rw [hsumJ, hsumMap]; ring
    have key2 : 2 * (∑ x ∈ J, x + ∑ x ∈ J, x) =
        2 * ∑ x ∈ Finset.range (4 * (k + 1) + 1), x := by
      rw [rearr, r1, r2, r3]
      ring
    have key : ∑ x ∈ J, x + ∑ x ∈ J, x =
        ∑ x ∈ Finset.range (4 * (k + 1) + 1), x := by
      omega
    have hAprod : ∏ x ∈ Finset.map ⟨fun j ↦ p ^ j, hinj2⟩ J, x = p ^ ∑ x ∈ J, x := by
      rw [Finset.prod_map]
      change ∏ x ∈ J, p ^ x = _
      rw [Finset.prod_pow_eq_pow_sum]
    have hDprod : ∏ x ∈ (p ^ (4 * (k + 1))).divisors, x =
        p ^ ∑ x ∈ Finset.range (4 * (k + 1) + 1), x := by
      rw [Nat.divisors_prime_pow hp, Finset.prod_map]
      change ∏ x ∈ Finset.range (4 * (k + 1) + 1), p ^ x = _
      rw [Finset.prod_pow_eq_pow_sum]
    have hsqA : (∏ x ∈ Finset.map ⟨fun j ↦ p ^ j, hinj2⟩ J, x) ^ 2 =
        ∏ x ∈ (p ^ (4 * (k + 1))).divisors, x := by
      rw [hAprod, hDprod, ← pow_mul]
      congr 1
      omega
    have hposA : ∏ x ∈ Finset.map ⟨fun j ↦ p ^ j, hinj2⟩ J, x ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro y hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hy
      exact pow_ne_zero _ hp.ne_zero
    have hAsub : Finset.map ⟨fun j ↦ p ^ j, hinj2⟩ J ⊆
        (p ^ (4 * (k + 1))).divisors := by
      rw [Nat.divisors_prime_pow hp]
      exact Finset.map_subset_map.mpr hJsub
    exact ⟨Finset.map ⟨fun j ↦ p ^ j, hinj2⟩ J, hAsub,
      split_of_prod_sq _ _ hAsub hposA hsqA⟩

private theorem exists_split_prod_prime_pow (s : Finset ℕ) (e : ℕ)
    (hdiv : 4 ∣ e) :
    (∀ p ∈ s, p.Prime) →
    ∃ A : Finset ℕ, A ⊆ (∏ p ∈ s, p ^ e).divisors ∧
      (∏ x ∈ A, x) = ∏ x ∈ (∏ p ∈ s, p ^ e).divisors \ A, x := by
  induction s using Finset.induction with
  | empty =>
    intro hs
    rw [Finset.prod_empty]
    refine ⟨∅, Finset.empty_subset _, ?_⟩
    rw [Finset.prod_empty, Finset.sdiff_empty, Nat.divisors_one, Finset.prod_singleton]
  | @insert p0 s hnot ih =>
    intro hs
    have hp0 : p0.Prime := hs p0 (Finset.mem_insert_self p0 s)
    have hs' : ∀ p ∈ s, p.Prime := fun p hp ↦ hs p (Finset.mem_insert_of_mem hp)
    have hprod : (∏ p ∈ insert p0 s, p ^ e) = p0 ^ e * ∏ p ∈ s, p ^ e :=
      Finset.prod_insert hnot
    rw [hprod]
    have hnot : ¬ p0 ∣ ∏ p ∈ s, p ^ e := by
      intro hdvd
      obtain ⟨q, hqs, hqdvd⟩ :=
        ((Nat.prime_iff.mp hp0).dvd_finsetProd_iff (fun p ↦ p ^ e)).mp hdvd
      have hdvdq : p0 ∣ q := hp0.dvd_of_dvd_pow hqdvd
      rcases (Nat.dvd_prime (hs' q hqs)).mp hdvdq with h1 | h1
      · exact hp0.ne_one h1
      · subst h1
        exact hnot hqs
    have hcop : (p0 ^ e).Coprime (∏ p ∈ s, p ^ e) :=
      Nat.Coprime.pow_left e ((hp0.coprime_iff_not_dvd).mpr hnot)
    obtain ⟨Au, hAu, eAu⟩ := exists_split_prime_pow hp0 hdiv
    obtain ⟨Av, hAv, eAv⟩ := ih hs'
    exact exists_split_mul hcop Au hAu eAu Av hAv eAv

private theorem divisorProd_eq_prod_prime_pow (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (hr : 1 ≤ s.card) :
    divisorProd (∏ p ∈ s, p) = ∏ p ∈ s, p ^ (2 ^ (s.card - 1)) := by
  have hn0 : (∏ p ∈ s, p) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro q hq
    exact (hs q hq).ne_zero
  have hfact1 : ∀ x ∈ s, (∏ p ∈ s, p).factorization x = 1 := by
    intro x hx
    have hpos : ∀ y ∈ s, (fun p : ℕ ↦ p) y ≠ 0 := fun y hy ↦ (hs y hy).ne_zero
    have hfp := Nat.factorization_prod hpos
    have h2 : (∑ q ∈ s, (q).factorization) x = ∑ q ∈ s, (q).factorization x := by
      simpa only [Finsupp.applyAddHom_apply] using
        map_sum (Finsupp.applyAddHom (M := ℕ) x) (fun q ↦ (q).factorization) s
    have hval : (∏ p ∈ s, p).factorization x = ∑ q ∈ s, (q).factorization x := by
      calc (∏ p ∈ s, p).factorization x = (∑ q ∈ s, (q).factorization) x := by rw [hfp]
        _ = ∑ q ∈ s, (q).factorization x := h2
    have h1 : ∀ b ∈ s, b ≠ x → (b).factorization x = 0 := by
      intro b hb hne
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hdvd
      rcases (Nat.dvd_prime (hs b hb)).mp hdvd with h1 | h1
      · exact (hs x hx).ne_one h1
      · exact hne h1.symm
    have h2' : x ∉ s → (x).factorization x = 0 := fun hcon ↦ absurd hx hcon
    rw [hval, Finset.sum_eq_single x h1 h2']
    exact (hs x hx).factorization_self
  have hpf : (∏ p ∈ s, p).primeFactors = s := by
    ext q
    rw [Nat.mem_primeFactors]
    constructor
    · intro h
      obtain ⟨hqprime, hdvd, -⟩ := h
      obtain ⟨r, hrs, hrdvd⟩ :=
        ((Nat.prime_iff.mp hqprime).dvd_finsetProd_iff (fun p ↦ p)).mp hdvd
      have hdr : q ∣ r := hrdvd
      rcases (Nat.dvd_prime (hs r hrs)).mp hdr with h1 | h1
      · exact absurd h1 hqprime.ne_one
      · rw [h1]; exact hrs
    · intro hqs
      exact ⟨hs q hqs, Finset.dvd_prod_of_mem _ hqs, hn0⟩
  have hcard : (∏ p ∈ s, p).divisors.card = 2 ^ s.card := by
    rw [Nat.card_divisors hn0, hpf]
    have h2 : ∀ x ∈ s, (∏ p ∈ s, p).factorization x + 1 = 2 := by
      intro x hx
      rw [hfact1 x hx]
    rw [Finset.prod_congr rfl h2]
    exact Finset.prod_const 2
  have hn : 0 < ∏ p ∈ s, p := Nat.pos_of_ne_zero hn0
  have hT := divisorProd_sq _ hn
  rw [hcard] at hT
  have hr1 : s.card - 1 + 1 = s.card := Nat.sub_add_cancel hr
  have hexp : 2 ^ (s.card - 1) * 2 = 2 ^ s.card := by
    have h := pow_add (2 : ℕ) (s.card - 1) 1
    rw [pow_one] at h
    rw [hr1] at h
    exact h.symm
  have hT2 : ((∏ p ∈ s, p) ^ (2 ^ (s.card - 1))) ^ 2 = (∏ p ∈ s, p) ^ (2 ^ s.card) := by
    rw [← pow_mul, hexp]
  have hTeq : divisorProd (∏ p ∈ s, p) = (∏ p ∈ s, p) ^ (2 ^ (s.card - 1)) :=
    pow_left_injective (n := 2) (by omega) (by
      change (divisorProd (∏ p ∈ s, p)) ^ 2 = ((∏ p ∈ s, p) ^ (2 ^ (s.card - 1))) ^ 2
      rw [hT, hT2])
  rw [hTeq]
  exact (Finset.prod_pow s (2 ^ (s.card - 1)) (fun p ↦ p)).symm

private theorem four_dvd_two_pow (r : ℕ) (hr : 3 ≤ r) : 4 ∣ 2 ^ (r - 1) := by
  refine ⟨2 ^ (r - 1 - 2), by rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add]; congr 1; omega⟩

/-- **Products of at least three distinct primes are super-m-Zumkeller.** For every finite set
$S$ of at least three primes, the product $\prod_{p \in S} p$ is super-m-Zumkeller.

Source: Harish Patodia, "Super m-Zumkeller Numbers",
Corollary 1. -/
theorem isSuperMZumkeller_prod_primes (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) (hcard : 3 ≤ s.card) :
    IsSuperMZumkeller (∏ p ∈ s, p) := by
  have hT := divisorProd_eq_prod_prime_pow s hs (by omega)
  have h4 := four_dvd_two_pow s.card hcard
  change ∃ A : Finset ℕ, A ⊆ (divisorProd (∏ p ∈ s, p)).divisors ∧
    (∏ x ∈ A, x) = ∏ x ∈ (divisorProd (∏ p ∈ s, p)).divisors \ A, x
  rw [hT]
  exact exists_split_prod_prime_pow s (2 ^ (s.card - 1)) h4 hs

/-- **Odd powers of $2$ times two distinct odd primes are super-m-Zumkeller.** Let $k$ be an odd
natural number and let $p$ and $q$ be distinct odd primes. Then $2^k p q$ is super-m-Zumkeller.

The primes are required to be odd because the paper's proof uses that this number has
$(k+1) \cdot 2^2$ divisors.

Source: Harish Patodia, "Super m-Zumkeller Numbers",
Corollary 2. -/
theorem isSuperMZumkeller_two_pow_mul_two_primes (k : ℕ)
    (hk : Odd k) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) :
    IsSuperMZumkeller ((2 : ℕ) ^ k * (p * q)) := by
  have hcopP : (2 : ℕ).Coprime p := (Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm
  have hcopQ : (2 : ℕ).Coprime q := (Nat.coprime_primes Nat.prime_two hq).mpr hq2.symm
  have hcopPQ : p.Coprime q := (Nat.coprime_primes hp hq).mpr hpq
  have hcop : (2 : ℕ).Coprime (p * q) := hcopP.mul_right hcopQ
  have hcard : ((2 : ℕ) ^ k * (p * q)).divisors.card = (k + 1) * 4 := by
    rw [(hcop.pow_left k).divisors_mul, Finset.card_map, Finset.card_attach,
      Finset.card_product, hcopPQ.divisors_mul, Finset.card_map, Finset.card_attach,
      Finset.card_product, Nat.divisors_prime_pow Nat.prime_two, Finset.card_map,
      Finset.card_range, hp.divisors, hq.divisors]
    simp [hp.ne_one.symm, hq.ne_one.symm]
  let e := 2 * (k + 1)
  have hT : divisorProd ((2 : ℕ) ^ k * (p * q)) = 2 ^ (k * e) * (p ^ e * q ^ e) := by
    have hpos : 0 < (2 : ℕ) ^ k * (p * q) :=
      Nat.mul_pos (pow_pos (by decide) _) (Nat.mul_pos hp.pos hq.pos)
    apply pow_left_injective (n := 2) (by decide)
    change divisorProd (2 ^ k * (p * q)) ^ 2 = (2 ^ (k * e) * (p ^ e * q ^ e)) ^ 2
    rw [divisorProd_sq _ hpos, hcard]
    have he : (k + 1) * 4 = e * 2 := by dsimp [e]; omega
    rw [he, pow_mul, mul_pow, mul_pow (p : ℕ), ← pow_mul]
  obtain ⟨i, hi⟩ := hk
  have he : e = 4 * (i + 1) := by dsimp [e]; omega
  have h4 : 4 ∣ e := ⟨i + 1, he⟩
  have h4k : 4 ∣ k * e := ⟨k * (i + 1), by rw [he]; ac_rfl⟩
  obtain ⟨A, hA, hAsplit⟩ := exists_split_prime_pow Nat.prime_two h4k
  obtain ⟨B, hB, hBsplit⟩ := exists_split_prime_pow hp h4
  obtain ⟨C, hC, hCsplit⟩ := exists_split_prime_pow hq h4
  obtain ⟨D, hD, hDsplit⟩ := exists_split_mul ((hcopPQ.pow_left e).pow_right e)
    B hB hBsplit C hC hCsplit
  have hcop' : ((2 : ℕ) ^ (k * e)).Coprime (p ^ e * q ^ e) := by
    rw [← mul_pow]
    exact (hcop.pow_left (k * e)).pow_right e
  unfold IsSuperMZumkeller
  rw [hT]
  exact exists_split_mul hcop' A hA hAsplit D hD hDsplit

end MathlibExt.NumberTheory.SuperMZumkellerWanted
