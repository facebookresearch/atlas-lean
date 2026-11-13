/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ProdigiousNumber
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-- Valuation bound: for `n ∣ M` with `M > 0`, every prime factorization
exponent of `n` is at most `M`. -/
private lemma factor_bound_aux (n M p : ℕ) (hM : 0 < M) (hnM : n ∣ M)
    (hp : p.Prime) : n.factorization p ≤ M := by
  have h1 : p ^ n.factorization p ∣ M := (Nat.ordProj_dvd n p).trans hnM
  have h2 : p ^ n.factorization p ≤ M := Nat.le_of_dvd hM h1
  have h3 : 2 ^ n.factorization p ≤ p ^ n.factorization p :=
    Nat.pow_le_pow_left hp.two_le _
  have h4 : n.factorization p < 2 ^ n.factorization p := Nat.lt_two_pow_self
  omega

/-- Dividing out the full `b ^ K`-gcd kills every prime factor of `b`,
provided `K` exceeds all relevant valuations. -/
private lemma coprime_div_gcd_pow_aux (b K n : ℕ) (hn : 0 < n)
    (hb : b ≠ 0)
    (hK : ∀ p, p.Prime → p ∣ b → n.factorization p ≤ K) :
    (n / n.gcd (b ^ K)).Coprime b := by
  by_contra hnc
  have hgcd : (n / n.gcd (b ^ K)).gcd b ≠ 1 := fun h => hnc h
  obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd hgcd
  have hpt : p ∣ n / n.gcd (b ^ K) := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
  have hpb : p ∣ b := dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
  have hddvd : n.gcd (b ^ K) ∣ n := Nat.gcd_dvd_left _ _
  have hdpos : 0 < n.gcd (b ^ K) := Nat.pos_of_dvd_of_pos hddvd hn
  have htpos : 0 < n / n.gcd (b ^ K) :=
    Nat.div_pos (Nat.le_of_dvd hn hddvd) hdpos
  have hfacpos : 0 < (n / n.gcd (b ^ K)).factorization p :=
    hpprime.factorization_pos_of_dvd (ne_of_gt htpos) hpt
  have hbound := hK p hpprime hpb
  have hbf : 1 ≤ b.factorization p :=
    hpprime.factorization_pos_of_dvd hb hpb
  have hdiv := Nat.factorization_div hddvd
  have hgcd2 := Nat.factorization_gcd (ne_of_gt hn) (pow_ne_zero K hb)
  have e3 : ((b ^ K).factorization) p = K * b.factorization p := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have hfac : (n / n.gcd (b ^ K)).factorization p = 0 := by
    have e1 : (n / n.gcd (b ^ K)).factorization p =
        n.factorization p - (n.gcd (b ^ K)).factorization p := by
      rw [hdiv]
      exact Finsupp.tsub_apply n.factorization
        (n.gcd (b ^ K)).factorization p
    have e2 : (n.gcd (b ^ K)).factorization p =
        n.factorization p ⊓ (K * b.factorization p) := by
      rw [hgcd2, Finsupp.inf_apply, e3]
    have hKm : K * 1 ≤ K * b.factorization p := Nat.mul_le_mul (le_refl K) hbf
    rw [mul_one] at hKm
    have hle : n.factorization p ≤ K * b.factorization p :=
      le_trans hbound hKm
    rw [e1, e2, inf_eq_left.mpr hle, Nat.sub_self]
  omega

/-- A geometric sum with ratio `≡ 1` is `≡` its length. -/
private lemma geomSum_modEq_aux (B T N : ℕ) (hB : B ≡ 1 [MOD T]) :
    ∑ j ∈ Finset.range N, B ^ j ≡ N [MOD T] := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    exact Nat.ModEq.refl 0
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 : B ^ n ≡ 1 [MOD T] := by
      have h := hB.pow n
      simpa using h
    exact ih.add h1

/-- Recurrence for the geometric sum. -/
private lemma geomSum_succ_aux (B n : ℕ) :
    B * ∑ j ∈ Finset.range n, B ^ j + 1
      = ∑ j ∈ Finset.range (n + 1), B ^ j := by
  rw [Finset.sum_range_succ', pow_zero, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (pow_succ' B i).symm

/-- The flattened block list evaluates to the geometric sum. -/
private lemma ofDigits_blocks_aux (b B n e : ℕ) (hB : B = b ^ (e + 1)) :
    Nat.ofDigits b ((List.replicate n (1 :: List.replicate e 0)).flatten) =
      ∑ j ∈ Finset.range n, B ^ j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, Nat.ofDigits_append]
    have h1 : Nat.ofDigits b (1 :: List.replicate e 0) = 1 := by
      rw [Nat.ofDigits_cons, Nat.ofDigits_replicate_zero, mul_zero, add_zero]
    have hlen : (1 :: List.replicate e 0).length = e + 1 := by simp
    rw [h1, hlen, ih, ← hB]
    have hgs := geomSum_succ_aux B n
    omega

/-- The constructed number has only `0/1` digits, so its nonzero-digit
product is `1`. -/
private lemma digits_repunit_mul_aux (b B M N e : ℕ) (hb : 1 < b)
    (hB : B = b ^ (e + 1)) (c : ℕ)
    (hc : c = b ^ M * ∑ j ∈ Finset.range N, B ^ j) (hN : 0 < N) :
    nonzeroDigitProd b c = 1 := by
  obtain ⟨N', hN1⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hN)
  have hN2 : N = N' + 1 := by omega
  subst hN2
  set L : List ℕ := List.replicate M 0 ++
    (List.replicate N' (1 :: List.replicate e 0)).flatten ++ [1] with hL
  have h01 : ∀ y ∈ L, y = 0 ∨ y = 1 := by
    intro y hy
    rw [hL] at hy
    simp only [List.mem_append, List.mem_replicate, List.mem_flatten,
      List.mem_singleton] at hy
    rcases hy with ((⟨_, rfl⟩ | ⟨s, ⟨_, rfl⟩, hy2⟩) | rfl)
    · exact Or.inl rfl
    · rw [List.mem_cons, List.mem_replicate] at hy2
      rcases hy2 with rfl | ⟨_, rfl⟩
      · exact Or.inr rfl
      · exact Or.inl rfl
    · exact Or.inr rfl
  have hall : ∀ l ∈ L, l < b := by
    intro l hl
    rcases h01 l hl with rfl | rfl <;> omega
  have hlast : ∀ h : L ≠ [], L.getLast h ≠ 0 := by
    intro h
    simp only [hL, List.getLast_concat] at ⊢
    exact one_ne_zero
  have hblen : (1 :: List.replicate e 0).length = e + 1 := by simp
  have hlenflat : ((List.replicate N' (1 :: List.replicate e 0)).flatten).length
      = N' * (e + 1) := by
    rw [List.length_flatten, List.map_replicate, hblen, List.sum_replicate]
    simp
  have hA : Nat.ofDigits b (List.replicate M 0 ++
      (List.replicate N' (1 :: List.replicate e 0)).flatten) =
      b ^ M * ∑ j ∈ Finset.range N', B ^ j := by
    rw [Nat.ofDigits_append, Nat.ofDigits_replicate_zero, List.length_replicate,
      ofDigits_blocks_aux b B N' e hB, zero_add]
  have hlenA : (List.replicate M 0 ++
      (List.replicate N' (1 :: List.replicate e 0)).flatten).length
      = M + N' * (e + 1) := by
    rw [List.length_append, List.length_replicate, hlenflat]
  have ho1 : Nat.ofDigits b [1] = 1 := by
    rw [Nat.ofDigits_cons, Nat.ofDigits_nil, mul_zero, add_zero]
  have hexp : b ^ (M + N' * (e + 1)) = b ^ M * B ^ N' := by
    rw [pow_add, hB, ← pow_mul, mul_comm (e + 1) N']
  have hof : Nat.ofDigits b L = c := by
    rw [hL, hc, Nat.ofDigits_append, ho1, hA, hlenA, mul_one,
      Finset.sum_range_succ, hexp, mul_add]
  have hdig : Nat.digits b c = L := by
    rw [← hof]
    exact Nat.digits_ofDigits b hb L hall hlast
  unfold nonzeroDigitProd
  rw [hdig]
  apply List.prod_eq_one
  intro y hy
  rw [List.mem_filter] at hy
  obtain ⟨hmem, hne⟩ := hy
  rcases h01 y hmem with h0 | h1
  · rw [h0] at hne
    simp at hne
  · exact h1

/--
**Chinese remainder solutions with nonzero-digit product one.** Let $b \ge 3$ and $w \ge 1$
be integers, and for $v = 1, \dots, w$ let $m_v$ be a positive integer and $r_v$ an integer.
Suppose the system of congruences $x \equiv r_v \pmod{m_v}$, $v = 1, \dots, w$, has an integer
solution, and $r_v = 0$ whenever $\gcd(m_v, b) \ne 1$. Then the system has a positive integer
solution $c$ with $p_b(c) = 1$, where $p_b(c)$ is the product of the nonzero base-$b$ digits
of $c$.

Proves `Wanted` entry `exists_positive_crt_solution_nonzero_digit_product_one`.

Source: Michael Gohn, Joshua Harrington, Sophia Lebiere, Hani Samamah,
Kyla Shappell, and Tony W. H. Wong, "Arithmetic Progressions of
b-Prodigious Numbers," Journal of Integer Sequences 25 (2022),
Article 22.8.7, Lemma `lem:crt`, lines 178-180,
<https://cs.uwaterloo.ca/journals/JIS/VOL25/Wong/wong42.tex>.
-/
theorem exists_positive_crt_solution_nonzero_digit_product_one
    (w b : ℕ)
    (r : Fin w → ℤ)
    (m : Fin w → ℕ)
    (hw : 0 < w)
    (hb : 3 ≤ b)
    (hmpos : ∀ v, 0 < m v)
    (hconsistent : ∃ x : ℤ, ∀ v, Int.ModEq (m v : ℤ) x (r v))
    (hzero : ∀ v, Nat.gcd (m v) b ≠ 1 → r v = 0) :
    ∃ c : ℕ,
      0 < c ∧
        (∀ v, Int.ModEq (m v : ℤ) (c : ℤ) (r v)) ∧
          nonzeroDigitProd b c = 1 := by
  have hb1 : 1 < b := by omega
  have hb0 : 0 < b := by omega
  have hbne : b ≠ 0 := ne_of_gt hb0
  set M : ℕ := ∏ v, m v with hMdef
  have hMpos : 0 < M := Finset.prod_pos (fun v _ => hmpos v)
  have hmM : ∀ v, m v ∣ M := fun v => Finset.dvd_prod_of_mem _ (Finset.mem_univ v)
  set T : ℕ := M / M.gcd (b ^ M) with hTdef
  have hDdvdM : M.gcd (b ^ M) ∣ M := Nat.gcd_dvd_left _ _
  have hDdvdP : M.gcd (b ^ M) ∣ b ^ M := Nat.gcd_dvd_right _ _
  have hDpos : 0 < M.gcd (b ^ M) := Nat.pos_of_dvd_of_pos hDdvdM hMpos
  have hDT : M.gcd (b ^ M) * T = M := Nat.mul_div_cancel' hDdvdM
  have hTpos : 0 < T :=
    Nat.div_pos (Nat.le_of_dvd hMpos hDdvdM) hDpos
  have hTne : T ≠ 0 := ne_of_gt hTpos
  have hcopT : T.Coprime b :=
    coprime_div_gcd_pow_aux b M M hMpos hbne
      (fun p hp _ => factor_bound_aux M M p hMpos dvd_rfl hp)
  have hcopt : ∀ v, ((m v / (m v).gcd (b ^ M))).Coprime b :=
    fun v => coprime_div_gcd_pow_aux b M (m v) (hmpos v) hbne
      (fun p hp _ => factor_bound_aux (m v) M p hMpos (hmM v) hp)
  have hφpos : 0 < T.totient := Nat.totient_pos.mpr hTpos
  obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hφpos)
  have he1 : T.totient = e + 1 := by omega
  have hcopbT : b.Coprime T := Nat.coprime_comm.mp hcopT
  set B : ℕ := b ^ T.totient with hBdef
  have hB1 : B ≡ 1 [MOD T] := Nat.ModEq.pow_totient hcopbT
  have hBdef' : B = b ^ (e + 1) := by rw [hBdef, he1]
  have hE : (b ^ M) ^ T.totient ≡ 1 [MOD T] :=
    Nat.ModEq.pow_totient (hcopbT.pow_left M)
  rw [he1] at hE
  obtain ⟨x, hx⟩ := hconsistent
  set X : ℕ := (x % (T : ℤ)).toNat with hXdef
  have hXmod : (X : ℤ) ≡ x [ZMOD (T : ℤ)] := by
    have hTe : (T : ℤ) ≠ 0 := by exact_mod_cast hTne
    rw [hXdef, Int.toNat_of_nonneg (Int.emod_nonneg x hTe)]
    exact Int.mod_modEq x (T : ℤ)
  set N : ℕ := X * (b ^ M) ^ e + T with hNdef
  have hNpos : 0 < N := lt_of_lt_of_le hTpos (Nat.le_add_left T _)
  have hsumN : ∑ j ∈ Finset.range N, B ^ j ≡ N [MOD T] :=
    geomSum_modEq_aux B T N hB1
  have hNT : b ^ M * T ≡ 0 [MOD T] :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left T (b ^ M))
  have h2 : b ^ M * N ≡ X [MOD T] := by
    have e1 : b ^ M * N = X * (b ^ M) ^ (e + 1) + b ^ M * T := by
      rw [hNdef, mul_add, pow_succ]
      ring
    have e2 : X * (b ^ M) ^ (e + 1) + b ^ M * T ≡ X [MOD T] := by
      have g := ((Nat.ModEq.refl X).mul hE).add hNT
      rwa [mul_one, add_zero] at g
    rw [e1]; exact e2
  have hkey : b ^ M * ∑ j ∈ Finset.range N, B ^ j ≡ X [MOD T] :=
    Nat.ModEq.trans ((Nat.ModEq.refl _).mul hsumN) h2
  have hkeyZ : ((b ^ M * ∑ j ∈ Finset.range N, B ^ j : ℕ) : ℤ) ≡ (X : ℤ)
      [ZMOD (T : ℤ)] :=
    Int.modEq_iff_dvd.mpr (Nat.modEq_iff_dvd.mp hkey)
  have hTZ : ((b ^ M * ∑ j ∈ Finset.range N, B ^ j : ℕ) : ℤ) ≡ x
      [ZMOD (T : ℤ)] :=
    hkeyZ.trans hXmod
  have hBpos : 0 < B := pow_pos hb0 _
  have hspos : 0 < ∑ j ∈ Finset.range N, B ^ j := by
    have hle := Finset.single_le_sum (s := Finset.range N)
      (f := fun j => B ^ j) (fun i _ => Nat.zero_le (B ^ i))
      (Finset.mem_range.mpr hNpos)
    rw [pow_zero] at hle
    omega
  have hcpos : 0 < b ^ M * ∑ j ∈ Finset.range N, B ^ j :=
    mul_pos (pow_pos hb0 M) hspos
  have hcv : ∀ v, Int.ModEq (m v : ℤ)
      ((b ^ M * ∑ j ∈ Finset.range N, B ^ j : ℕ) : ℤ) (r v) := by
    intro v
    have hdvdm : (m v).gcd (b ^ M) ∣ m v := Nat.gcd_dvd_left _ _
    have hdvdp : (m v).gcd (b ^ M) ∣ b ^ M := Nat.gcd_dvd_right _ _
    have hmt : (m v).gcd (b ^ M) * (m v / (m v).gcd (b ^ M)) = m v :=
      Nat.mul_div_cancel' hdvdm
    have hcopdt : ((m v).gcd (b ^ M)).Coprime
        (m v / (m v).gcd (b ^ M)) := by
      have h1 : (m v / (m v).gcd (b ^ M)).Coprime (b ^ M) :=
        (hcopt v).pow_right M
      have h3 : (m v / (m v).gcd (b ^ M)).Coprime ((m v).gcd (b ^ M)) :=
        h1.coprime_dvd_right hdvdp
      exact h3.symm
    have hdvd : ((((m v).gcd (b ^ M)) : ℕ) : ℤ) ∣
        x - ((b ^ M * ∑ j ∈ Finset.range N, B ^ j : ℕ) : ℤ) := by
      by_cases hgc : (m v).gcd b = 1
      · have hd1 : (m v).gcd (b ^ M) = 1 := by
          have hcb : (m v).Coprime b := hgc
          have h1 : ((m v).gcd (b ^ M)).Coprime b :=
            hcb.coprime_dvd_left hdvdm
          have h2b : ((m v).gcd (b ^ M)).Coprime (b ^ M) := h1.pow_right M
          exact h2b.eq_one_of_dvd hdvdp
        rw [hd1, Nat.cast_one]
        exact one_dvd _
      · have hr0 : r v = 0 := hzero v hgc
        have hxv : x ≡ (0 : ℤ) [ZMOD (((m v) : ℕ) : ℤ)] := by
          have h := hx v
          rwa [hr0] at h
        have h1 : ((((m v) : ℕ)) : ℤ) ∣ x :=
          Int.modEq_zero_iff_dvd.mp hxv
        have hxd : ((((m v).gcd (b ^ M)) : ℕ) : ℤ) ∣ x :=
          dvd_trans (Int.natCast_dvd_natCast.mpr hdvdm) h1
        have hcc : (m v).gcd (b ^ M)
            ∣ b ^ M * ∑ j ∈ Finset.range N, B ^ j :=
          dvd_trans hdvdp (dvd_mul_right _ _)
        have hcd : ((((m v).gcd (b ^ M)) : ℕ) : ℤ) ∣
            ((b ^ M * ∑ j ∈ Finset.range N, B ^ j : ℕ) : ℤ) :=
          Int.natCast_dvd_natCast.mpr hcc
        exact dvd_sub hxd hcd
    have htT : m v / (m v).gcd (b ^ M) ∣ T := by
      have htm2 : m v / (m v).gcd (b ^ M) ∣ m v :=
        ⟨(m v).gcd (b ^ M), hmt.symm.trans (mul_comm _ _)⟩
      have htm : m v / (m v).gcd (b ^ M) ∣ M := htm2.trans (hmM v)
      have hcopTD : (m v / (m v).gcd (b ^ M)).Coprime (M.gcd (b ^ M)) := by
        have h1 : (m v / (m v).gcd (b ^ M)).Coprime (b ^ M) :=
          (hcopt v).pow_right M
        exact h1.coprime_dvd_right hDdvdP
      have htmT : m v / (m v).gcd (b ^ M) ∣ M.gcd (b ^ M) * T := by
        rw [hDT]
        exact htm
      exact hcopTD.dvd_of_dvd_mul_left htmT
    have hdvd2 : ((((m v / (m v).gcd (b ^ M)) : ℕ)) : ℤ) ∣
        x - ((b ^ M * ∑ j ∈ Finset.range N, B ^ j : ℕ) : ℤ) :=
      Int.modEq_iff_dvd.mp
        (Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr htT) hTZ)
    have hcomb : ((((m v) : ℕ)) : ℤ) ∣
        x - ((b ^ M * ∑ j ∈ Finset.range N, B ^ j : ℕ) : ℤ) := by
      have h1 : (m v).gcd (b ^ M)
          ∣ (x - ((b ^ M * ∑ j ∈ Finset.range N, B ^ j : ℕ) : ℤ)).natAbs :=
        Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdvd)
      have h2n : m v / (m v).gcd (b ^ M)
          ∣ (x - ((b ^ M * ∑ j ∈ Finset.range N, B ^ j : ℕ) : ℤ)).natAbs :=
        Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdvd2)
      have h3 : (m v).gcd (b ^ M) * (m v / (m v).gcd (b ^ M)) ∣
          (x - ((b ^ M * ∑ j ∈ Finset.range N, B ^ j : ℕ) : ℤ)).natAbs :=
        hcopdt.mul_dvd_of_dvd_of_dvd h1 h2n
      rw [hmt] at h3
      have h6 : ((((m v) : ℕ)) : ℤ).natAbs ∣
          (x - ((b ^ M * ∑ j ∈ Finset.range N, B ^ j : ℕ) : ℤ)).natAbs := by
        simpa using h3
      exact Int.natAbs_dvd_natAbs.mp h6
    exact (Int.modEq_iff_dvd.mpr hcomb).trans (hx v)
  have hprod : nonzeroDigitProd b (b ^ M * ∑ j ∈ Finset.range N, B ^ j) = 1 :=
    digits_repunit_mul_aux b B M N e hb1 hBdef' _ rfl hNpos
  exact ⟨_, hcpos, hcv, hprod⟩

end MetaMathlibExt
