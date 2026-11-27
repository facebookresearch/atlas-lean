/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

@[expose] public section

namespace MetaMathlibExt

/--
**Period of a generalized bi-periodic Fibonacci sequence modulo a prime, given the roots.** Let
$p$ be an odd prime and let $a, b, c, d \in \mathbb{Z}/p\mathbb{Z}$ with $a \ne 0$, $c \ne 0$,
$d \ne 0$, and $a \ne b$ or $c \ne d$. Let $F : \mathbb{N} \to \mathbb{Z}/p\mathbb{Z}$ satisfy
$F_0 = 0$, $F_1 = 1$ and, for every $n \ge 2$, $F_n = a F_{n-1} + c F_{n-2}$ if $n$ is even and
$F_n = b F_{n-1} + d F_{n-2}$ if $n$ is odd. Put $A = ab + c + d$ and $\Delta = A^2 - 4cd$, and
let $\alpha, \beta \in \mathbb{Z}/p\mathbb{Z}$ satisfy $\alpha + \beta = A$ and
$\alpha \beta = cd$. Let $k$ be the least positive period of $F$: $k > 0$, $F_{n+k} = F_n$ for
all $n$, and $k \le m$ for every $m > 0$ with $F_{n+m} = F_n$ for all $n$. If $\Delta \ne 0$,
then $k$ divides $2(p - 1)$, and if moreover $\alpha$ and $\beta$ are nonzero squares in
$\mathbb{Z}/p\mathbb{Z}$, then $k$ divides $p - 1$.

Since $\Delta = (\alpha - \beta)^2$, no hypothesis that $\Delta$ is a square is needed.
-/
theorem generalizedBiPeriodicFibonacci_period_dvd_general :
  ∀ (p : ℕ) (_hp : p.Prime) (_hpOdd : Odd p)
    (a b c d : ZMod p)
    (F : ℕ → ZMod p)
    (A Δ α β : ZMod p)
    (k : ℕ),
    F 0 = 0 →
    F 1 = 1 →
    (∀ n, 2 ≤ n → n % 2 = 0 →
      F n = a * F (n - 1) + c * F (n - 2)) →
    (∀ n, 2 ≤ n → n % 2 = 1 →
      F n = b * F (n - 1) + d * F (n - 2)) →
    a ≠ 0 →
    c ≠ 0 →
    d ≠ 0 →
    (a ≠ b ∨ c ≠ d) →
    A = a * b + c + d →
    Δ = A ^ 2 - 4 * c * d →
    α + β = A →
    α * β = c * d →
    0 < k →
    (∀ n, F (n + k) = F n) →
    (∀ m, 0 < m → (∀ n, F (n + m) = F n) → k ≤ m) →
    Δ ≠ 0 →
    k ∣ 2 * (p - 1) ∧
      ((α ≠ 0 ∧ IsSquare α ∧ β ≠ 0 ∧ IsSquare β) → k ∣ p - 1) := by
  intro p hp hpOdd a b c d F A Δ α β k h0 h1 heven hodd ha hc hd hne hA hΔ hsum hprod hkpos hper
      hmin hΔne
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have _hp2 : 2 ≤ p := hp.two_le
  obtain ⟨_k, _hk⟩ := hpOdd
  have hp1pos : 0 < p - 1 := by omega
  have hhalf_pos : 0 < (p - 1) / 2 := by omega
  have hhalf2 : 2 * ((p - 1) / 2) = p - 1 := by omega
  have hF2 : F 2 = a := by
    have h := heven 2 le_rfl (by decide)
    norm_num [h0, h1] at h
    simpa using h
  have hkeven : Even k := by
    rcases Nat.even_or_odd k with hev | hodd_k
    · exact hev
    · exfalso
      obtain ⟨r, hr⟩ := hodd_k
      have hk1 : F k = F 0 := by have h := hper 0; simpa using h
      have hk2 : F (1 + k) = F 1 := hper 1
      have hab : a = b := by
        have hmod : (2 + k) % 2 = 1 := by omega
        have hle : 2 ≤ 2 + k := by omega
        have h3 := hodd (2 + k) hle hmod
        have e1 : 2 + k - 1 = 1 + k := by omega
        have e2 : 2 + k - 2 = k := by omega
        rw [e1, e2] at h3
        have hper2 : F (2 + k) = F 2 := hper 2
        rw [hk1, hk2, h0, h1] at h3
        rw [hF2] at hper2
        simp only [mul_one, mul_zero, add_zero] at h3
        rw [h3] at hper2
        exact hper2.symm
      have hcd : c = d := by
        have hF3 : F 3 = b * F 2 + d * F 1 := by
          have h := hodd 3 (by norm_num) (by decide)
          norm_num at h
          simpa using h
        have hmod3 : (3 + k) % 2 = 0 := by omega
        have hle3 : 2 ≤ 3 + k := by omega
        have h4 := heven (3 + k) hle3 hmod3
        have e3 : 3 + k - 1 = 2 + k := by omega
        have e4 : 3 + k - 2 = 1 + k := by omega
        rw [e3, e4] at h4
        have hper3 : F (3 + k) = F 3 := hper 3
        have hk3 : F (2 + k) = F 2 := hper 2
        rw [hk3, hk2] at h4
        rw [hab] at h4
        rw [h4, hF3] at hper3
        simp only [add_left_cancel_iff] at hper3
        rw [h1] at hper3
        simpa using hper3
      rcases hne with h | h
      · exact h hab
      · exact h hcd
  obtain ⟨t, ht⟩ := hkeven
  have hk2t : k = 2 * t := by omega
  have htpos : 0 < t := by omega
  have hcd : c * d ≠ 0 := mul_ne_zero hc hd
  have hαne : α ≠ 0 := by
    intro hcon
    rw [hcon, zero_mul] at hprod
    exact hcd hprod.symm
  have hβne : β ≠ 0 := by
    intro hcon
    rw [hcon, mul_zero] at hprod
    exact hcd hprod.symm
  have hsub2 : (α - β) ^ 2 = Δ := by
    have h1 : (α - β) ^ 2 = (α + β) ^ 2 - 4 * (α * β) := by ring
    rw [h1, hsum, hprod]
    linear_combination hΔ.symm
  have hsubne : α - β ≠ 0 := by
    intro hcon
    rw [hcon] at hsub2
    simp at hsub2
    exact hΔne hsub2.symm
  set M : Matrix (Fin 2) (Fin 2) (ZMod p) := !![a * b + d, b * c; a, c] with hMdef
  have hM2 : M ^ 2 = (a * b + c + d) • M - (c * d) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
    rw [hMdef]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_two, Matrix.mul_apply] <;> ring
  have hα2 : α ^ 2 = (a * b + c + d) * α - c * d := by
    have hAs : α + β = a * b + c + d := by rw [← hA, hsum]
    have hmul : α * (α + β) = α * (a * b + c + d) := by rw [hAs]
    have hsq : α * α = (a * b + c + d) * α - c * d := by linear_combination hmul - hprod
    calc α ^ 2 = α * α := by rw [pow_two]
      _ = (a * b + c + d) * α - c * d := hsq
  have hβ2 : β ^ 2 = (a * b + c + d) * β - c * d := by
    have hAs : α + β = a * b + c + d := by rw [← hA, hsum]
    have hmul : β * (α + β) = β * (a * b + c + d) := by rw [hAs]
    have hsq : β * β = (a * b + c + d) * β - c * d := by linear_combination hmul - hprod
    calc β ^ 2 = β * β := by rw [pow_two]
      _ = (a * b + c + d) * β - c * d := hsq
  have key : ∀ n, ∃ e f : ZMod p, M ^ n = e • M + f • (1 : Matrix (Fin 2) (Fin 2) (ZMod p))
      ∧ α ^ n = e * α + f ∧ β ^ n = e * β + f := by
    intro n
    induction n with
    | zero => exact ⟨0, 1, by simp, by simp, by simp⟩
    | succ n ih =>
      obtain ⟨e, f, hM, hα, hβ⟩ := ih
      refine ⟨(a * b + c + d) * e + f, -(c * d) * e, ?_, ?_, ?_⟩
      · have hpow : M ^ (n + 1) = M ^ n * M := by rw [pow_succ]
        rw [hpow, hM]
        have hMM : M * M = M ^ 2 := by rw [pow_two]
        have step : (e • M + f • (1 : Matrix (Fin 2) (Fin 2) (ZMod p))) * M
            = e • (M ^ 2) + f • M := by
          rw [add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, hMM]
        rw [step, hM2, smul_sub]
        ext i j
        simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
        ring
      · rw [pow_succ, hα]
        have h2 : α * α = (a * b + c + d) * α - c * d := by rw [← pow_two]; exact hα2
        calc (e * α + f) * α = e * (α * α) + f * α := by ring
          _ = e * ((a * b + c + d) * α - c * d) + f * α := by rw [h2]
          _ = ((a * b + c + d) * e + f) * α + (-(c * d) * e) := by ring
      · rw [pow_succ, hβ]
        have h2 : β * β = (a * b + c + d) * β - c * d := by rw [← pow_two]; exact hβ2
        calc (e * β + f) * β = e * (β * β) + f * β := by ring
          _ = e * ((a * b + c + d) * β - c * d) + f * β := by rw [h2]
          _ = ((a * b + c + d) * e + f) * β + (-(c * d) * e) := by ring
  set Q : ℕ → Fin 2 → ZMod p := fun m => ![F (2 * m + 1), F (2 * m)] with hQdef
  have hQ0 : Q 0 = ![1, 0] := by
    have e1 : 2 * 0 + 1 = 1 := by omega
    have e0 : 2 * 0 = 0 := by omega
    simp [hQdef, e1, e0, h0, h1]
  have hF_even : ∀ m, F (2 * (m + 1)) = a * F (2 * m + 1) + c * F (2 * m) := by
    intro m
    have hmod : (2 * (m + 1)) % 2 = 0 := by omega
    have hle : 2 ≤ 2 * (m + 1) := by omega
    have h := heven (2 * (m + 1)) hle hmod
    have e1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    have e2 : 2 * (m + 1) - 2 = 2 * m := by omega
    rw [e1, e2] at h
    exact h
  have hF_odd : ∀ m, F (2 * (m + 1) + 1) = b * F (2 * (m + 1)) + d * F (2 * m + 1) := by
    intro m
    have hmod : (2 * (m + 1) + 1) % 2 = 1 := by omega
    have hle : 2 ≤ 2 * (m + 1) + 1 := by omega
    have h := hodd (2 * (m + 1) + 1) hle hmod
    have e1 : 2 * (m + 1) + 1 - 1 = 2 * (m + 1) := by omega
    have e2 : 2 * (m + 1) + 1 - 2 = 2 * m + 1 := by omega
    rw [e1, e2] at h
    exact h
  have hQstep : ∀ m, Q (m + 1) = Matrix.mulVec M (Q m) := by
    intro m
    ext i
    fin_cases i
    · simp only [hQdef, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Matrix.mulVec, hMdef,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.dotProduct_cons,
        Matrix.head_cons, Matrix.tail_cons, Matrix.dotProduct_of_isEmpty, add_zero]
      rw [hF_odd m, hF_even m]
      ring
    · simp only [hQdef, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.mulVec, hMdef, Matrix.of_apply, Matrix.cons_val', Matrix.dotProduct_cons,
        Matrix.head_cons, Matrix.tail_cons, Matrix.dotProduct_of_isEmpty, add_zero]
      rw [hF_even m]
  have hQpow : ∀ m, Q m = Matrix.mulVec (M ^ m) (Q 0) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [hQstep m, ih, pow_succ', Matrix.mulVec_mulVec]
  have hQper : ∀ m, Q (m + t) = Q m := by
    intro m
    ext i
    fin_cases i
    · simp only [hQdef, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      have heq : 2 * (m + t) + 1 = (2 * m + 1) + k := by omega
      rw [heq]
      exact hper (2 * m + 1)
    · simp only [hQdef, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      have heq : 2 * (m + t) = 2 * m + k := by omega
      rw [heq]
      exact hper (2 * m)
  have hQt0 : Q t = Q 0 := by
    have h := hQper 0
    simpa using h
  have hMt0 : Matrix.mulVec (M ^ t) (Q 0) = Q 0 := by
    rw [← hQpow t]
    exact hQt0
  have hF3val : F 3 = b * a + d := by
    have h := hodd 3 (by norm_num) (by decide)
    norm_num at h
    rw [hF2, h1] at h
    simpa using h
  have hQ1 : Q 1 = ![a * b + d, a] := by
    have e1 : 2 * 1 + 1 = 3 := by omega
    have e0 : 2 * 1 = 2 := by omega
    have hQ1e : Q 1 = ![F 3, F 2] := by simp [hQdef, e1, e0]
    rw [hQ1e, hF3val, hF2]
    ext i
    fin_cases i <;> simp
    ring
  have hMt1 : Matrix.mulVec (M ^ t) (Q 1) = Q 1 := by
    have h1t : Q (1 + t) = Q 1 := hQper 1
    have e10 : (1 : ℕ) + t = t + 1 := by omega
    rw [hQpow (1 + t), e10, pow_add, ← Matrix.mulVec_mulVec, ← hQpow 1] at h1t
    exact h1t
  have hMt : M ^ t = 1 := by
    have h0' : Matrix.mulVec (M ^ t) ![1, 0] = ![1, 0] := by rw [← hQ0]; exact hMt0
    have h1' : Matrix.mulVec (M ^ t) ![a * b + d, a] = ![a * b + d, a] := by rw [← hQ1]; exact hMt1
    have h00 := congrFun h0' 0
    have h10 := congrFun h0' 1
    have h20 := congrFun h1' 0
    have h21 := congrFun h1' 1
    simp only [Fin.isValue, Matrix.mulVec_fin_two, Nat.succ_eq_add_one, Nat.reduceAdd,
        Matrix.cons_val_zero, mul_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero,
        add_zero] at h00 h10 h20 h21
    have e00 : (M ^ t) 0 0 = 1 := by simpa using h00
    have e10 : (M ^ t) 1 0 = 0 := by simpa using h10
    have e01 : (M ^ t) 0 1 = 0 := by
      rw [e00] at h20
      have hza : (M ^ t) 0 1 * a = 0 := by linear_combination h20
      rcases mul_eq_zero.mp hza with hh | hh
      · exact hh
      · exact absurd hh ha
    have e11 : (M ^ t) 1 1 = 1 := by
      rw [e10] at h21
      simp only [zero_mul, Fin.isValue, zero_add] at h21
      have heq : (M ^ t) 1 1 * a = 1 * a := by linear_combination h21
      exact mul_right_cancel₀ ha heq
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using e00
    · simpa using e01
    · simpa using e10
    · simpa using e11
  have hminM : ∀ s, 0 < s → M ^ s = 1 → t ≤ s := by
    intro s hs hMs
    have hQs : ∀ m, Q (m + s) = Q m := by
      intro m
      rw [hQpow (m + s), pow_add, ← Matrix.mulVec_mulVec, hMs, Matrix.one_mulVec, ← hQpow m]
    have hFs : ∀ n, F (n + 2 * s) = F n := by
      intro n
      rcases Nat.even_or_odd n with hev | hod
      · obtain ⟨u, hu⟩ := hev
        have hn : n = 2 * u := by omega
        have c0 : Q (u + s) 1 = Q u 1 := by rw [hQs u]
        simp only [hQdef, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one] at c0
        have g1 : 2 * (u + s) = n + 2 * s := by omega
        have g2 : 2 * u = n := by omega
        rw [g1] at c0
        rw [g2] at c0
        exact c0
      · obtain ⟨u, hu⟩ := hod
        have hn : n = 2 * u + 1 := by omega
        have c0 : Q (u + s) 0 = Q u 0 := by rw [hQs u]
        simp only [hQdef, Fin.isValue, Matrix.cons_val_zero] at c0
        have g1 : 2 * (u + s) + 1 = n + 2 * s := by omega
        have g2 : 2 * u + 1 = n := by omega
        rw [g1] at c0
        rw [g2] at c0
        exact c0
    have h2s : 0 < 2 * s := by omega
    have hle := hmin (2 * s) h2s hFs
    omega
  have hdvd_of : ∀ N, 0 < N → M ^ N = 1 → t ∣ N := by
    intro N hNpos hMN
    have hmod1 : M ^ (N % t) = 1 := by
      have hdiv : t * (N / t) + N % t = N := Nat.div_add_mod N t
      have e : M ^ N = (M ^ t) ^ (N / t) * M ^ (N % t) := by
        conv_lhs => rw [← hdiv]
        rw [pow_add, pow_mul]
      rw [hMt, one_pow, one_mul] at e
      rw [hMN] at e
      exact e.symm
    have hr : N % t = 0 := by
      by_contra hne0
      have hpos : 0 < N % t := Nat.pos_of_ne_zero hne0
      have hle := hminM (N % t) hpos hmod1
      have hlt := Nat.mod_lt N htpos
      omega
    exact Nat.dvd_of_mod_eq_zero hr
  have hαpow : α ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hαne
  have hβpow : β ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hβne
  have hMpow1 : M ^ (p - 1) = 1 := by
    obtain ⟨e1, f1, hM1, hA1, hB1⟩ := key (p - 1)
    have hA1' : e1 * α + f1 = 1 := hA1.symm.trans hαpow
    have hB1' : e1 * β + f1 = 1 := hB1.symm.trans hβpow
    have he1 : e1 = 0 := by
      have hsub : e1 * (α - β) = 0 := by linear_combination hA1' - hB1'
      rcases mul_eq_zero.mp hsub with hh | hh
      · exact hh
      · exact absurd hh hsubne
    have hf1 : f1 = 1 := by
      rw [he1] at hA1'
      simpa using hA1'
    rw [hM1, he1, hf1]
    simp
  have htdvd : t ∣ p - 1 := hdvd_of (p - 1) hp1pos hMpow1
  have hk_dvd1 : k ∣ 2 * (p - 1) := by
    obtain ⟨q, hq⟩ := htdvd
    exact ⟨q, by rw [hk2t, hq]; ring⟩
  have hsecond : (α ≠ 0 ∧ IsSquare α ∧ β ≠ 0 ∧ IsSquare β) → k ∣ p - 1 := by
    intro hsq
    obtain ⟨hα0, hsα, hβ0, hsβ⟩ := hsq
    obtain ⟨rα, hrα⟩ := hsα
    obtain ⟨rβ, hrβ⟩ := hsβ
    have hrαne : rα ≠ 0 := by
      intro hcon
      rw [hcon, mul_zero] at hrα
      exact hα0 hrα
    have hrβne : rβ ≠ 0 := by
      intro hcon
      rw [hcon, mul_zero] at hrβ
      exact hβ0 hrβ
    have eα : α ^ ((p - 1) / 2) = 1 := by
      rw [hrα, mul_pow, ← pow_add]
      have he : (p - 1) / 2 + (p - 1) / 2 = p - 1 := by omega
      rw [he, ZMod.pow_card_sub_one_eq_one hrαne]
    have eβ : β ^ ((p - 1) / 2) = 1 := by
      rw [hrβ, mul_pow, ← pow_add]
      have he : (p - 1) / 2 + (p - 1) / 2 = p - 1 := by omega
      rw [he, ZMod.pow_card_sub_one_eq_one hrβne]
    have hMhalf : M ^ ((p - 1) / 2) = 1 := by
      obtain ⟨e1, f1, hM1, hA1, hB1⟩ := key ((p - 1) / 2)
      have hA1' : e1 * α + f1 = 1 := hA1.symm.trans eα
      have hB1' : e1 * β + f1 = 1 := hB1.symm.trans eβ
      have he1 : e1 = 0 := by
        have hsub : e1 * (α - β) = 0 := by linear_combination hA1' - hB1'
        rcases mul_eq_zero.mp hsub with hh | hh
        · exact hh
        · exact absurd hh hsubne
      have hf1 : f1 = 1 := by
        rw [he1] at hA1'
        simpa using hA1'
      rw [hM1, he1, hf1]
      simp
    have htdvd2 : t ∣ (p - 1) / 2 := hdvd_of ((p - 1) / 2) hhalf_pos hMhalf
    obtain ⟨q, hq⟩ := htdvd2
    exact ⟨q, by have h1 : p - 1 = 2 * ((p - 1) / 2) := hhalf2.symm; rw [h1, hq, hk2t]; ring⟩
  exact ⟨hk_dvd1, hsecond⟩

set_option linter.unusedVariables false in
/--
**Period of a generalized bi-periodic Fibonacci sequence modulo a prime.** Let $p$ be an odd
prime and let $a, b, c, d \in \mathbb{Z}/p\mathbb{Z}$ with $a \ne 0$, $c \ne 0$, $d \ne 0$, and
$a \ne b$ or $c \ne d$. Let $F : \mathbb{N} \to \mathbb{Z}/p\mathbb{Z}$ satisfy $F_0 = 0$,
$F_1 = 1$ and, for every $n \ge 2$, $F_n = a F_{n-1} + c F_{n-2}$ if $n$ is even and
$F_n = b F_{n-1} + d F_{n-2}$ if $n$ is odd. Put $A = ab + c + d$ and $\Delta = A^2 - 4cd$, and
let $\alpha, \beta \in \mathbb{Z}/p\mathbb{Z}$ satisfy $\alpha + \beta = A$ and
$\alpha \beta = cd$. Let $k$ be the least positive period of $F$: $k > 0$, $F_{n+k} = F_n$ for
all $n$, and $k \le m$ for every $m > 0$ with $F_{n+m} = F_n$ for all $n$. If $\Delta$ is a
nonzero square in $\mathbb{Z}/p\mathbb{Z}$, then $k$ divides $2(p - 1)$, and if moreover
$\alpha$ and $\beta$ are nonzero squares in $\mathbb{Z}/p\mathbb{Z}$, then $k$ divides $p - 1$.

Source: Hacène Belbachir and Celia Salhi, "The Generalized Bi-Periodic
Fibonacci Sequence Modulo m," Journal of Integer Sequences 24 (2021),
Article 21.9.4, Theorem (label th1), lines 225–226,
<https://cs.uwaterloo.ca/journals/JIS/VOL24/Salhi/salhi4.tex>.
It follows from `generalizedBiPeriodicFibonacci_period_dvd_general`, which drops the
unused `IsSquare Δ`.
Proves `Wanted` entry `generalizedBiPeriodicFibonacci_period_dvd`.
-/
theorem generalizedBiPeriodicFibonacci_period_dvd :
  ∀ (p : ℕ) (hp : p.Prime) (hpOdd : Odd p)
    (a b c d : ZMod p)
    (F : ℕ → ZMod p)
    (A Δ α β : ZMod p)
    (k : ℕ),
    F 0 = 0 →
    F 1 = 1 →
    (∀ n, 2 ≤ n → n % 2 = 0 →
      F n = a * F (n - 1) + c * F (n - 2)) →
    (∀ n, 2 ≤ n → n % 2 = 1 →
      F n = b * F (n - 1) + d * F (n - 2)) →
    a ≠ 0 →
    c ≠ 0 →
    d ≠ 0 →
    (a ≠ b ∨ c ≠ d) →
    A = a * b + c + d →
    Δ = A ^ 2 - 4 * c * d →
    α + β = A →
    α * β = c * d →
    0 < k →
    (∀ n, F (n + k) = F n) →
    (∀ m, 0 < m → (∀ n, F (n + m) = F n) → k ≤ m) →
    Δ ≠ 0 →
    IsSquare Δ →
    k ∣ 2 * (p - 1) ∧
      ((α ≠ 0 ∧ IsSquare α ∧ β ≠ 0 ∧ IsSquare β) → k ∣ p - 1) :=
  fun p hp hpOdd a b c d F A Δ α β k h0 h1 heven hodd ha hc hd hne hA hΔ hsum hprod hkpos hper
      hmin hΔne _ =>
    generalizedBiPeriodicFibonacci_period_dvd_general p hp hpOdd a b c d F A Δ α β k h0 h1 heven
      hodd ha hc hd hne hA hΔ hsum hprod hkpos hper hmin hΔne

end MetaMathlibExt
