/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Data.Set.Density
public import MathlibExt.NumberTheory.LaurentCartierCongruence
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Density-one zeros of constant terms modulo a prime

If a prime divides the constant term of some power of a Laurent polynomial `P`, the zeros of
the constant terms of `P ^ n * Q` modulo that prime have density one for every `Q`. The
residue sequence has arbitrarily long zero runs and is uniformly recurrent only if it is zero.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Occurrence of a sequence factor at a position.** Let $s = (s_n)_{n \ge 0}$ be a sequence and
let $i$, $\ell$ and $i'$ be natural numbers. The factor of $s$ of length $\ell$ starting at
position $i$ occurs at position $i'$ when $s_{i'+t} = s_{i+t}$ for every natural number $t < \ell$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Definition 1. -/
public def SeqFactorOccursAt {α : Type*} (s : ℕ → α) (i ℓ i' : ℕ) : Prop :=
  ∀ t < ℓ, s (i' + t) = s (i + t)

/-- **Uniformly recurrent sequence.** A sequence $s : \mathbb{N} \to \alpha$ is uniformly
recurrent if for every factor $w$ there is a constant $C_w$ such that every occurrence of $w$ is
followed by another occurrence at distance at most $C_w$: for all $i, \ell \in \mathbb{N}$ there
is $C \in \mathbb{N}$ such that for every $i'$ with $s(i' + t) = s(i + t)$ for all $t < \ell$,
there is $j$ with $0 < j \le C$ and $s(i' + j + t) = s(i + t)$ for all $t < \ell$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Definition 1. -/
public def IsUniformlyRecurrentSeq {α : Type*} (s : ℕ → α) : Prop :=
  ∀ i ℓ : ℕ, ∃ C, ∀ i', SeqFactorOccursAt s i ℓ i' →
    ∃ j, 0 < j ∧ j ≤ C ∧ SeqFactorOccursAt s i ℓ (i' + j)

namespace constantTerm_zero_density_mod_prime

open AddMonoidAlgebra

-- A gap of zero digits separates the constant terms of the two factors.
private theorem split_constantTerm {r p : ℕ} (hp : p.Prime)
    (P R : AddMonoidAlgebra ℤ (Fin r → ℤ)) (s n : ℕ) (hR : laurentDeg R < p ^ s) :
    (P ^ (p ^ s * n) * R).coeff 0 ≡ (P ^ n).coeff 0 * R.coeff 0 [ZMOD p] := by
  classical
  induction s generalizing R with
  | zero =>
    have hsingle : R = single 0 (R.coeff 0) := by
      ext j
      by_cases hj : j = 0
      · simp [hj]
      · have hzero : R.coeff j = 0 := by
          by_contra h
          apply hj
          funext i
          have hi := (laurentDeg_le_iff R _).1 le_rfl j (Finsupp.mem_support_iff.mpr h) i
          have : (j i).natAbs = 0 := by simpa using (show (j i).natAbs < 1 from hi.trans_lt hR)
          simpa using this
        simp [hj, hzero]
    rw [pow_zero, one_mul, hsingle, coeff_mul_single_zero, coeff_single, Finsupp.single_eq_same]
  | succ s ih =>
    have hdeg : laurentDeg (laurentCartier p R) < p ^ s := by
      have hpos := pow_pos hp.pos s
      suffices laurentDeg (laurentCartier p R) ≤ p ^ s - 1 by omega
      apply (laurentDeg_le_iff _ _).2
      intro j hj i
      rw [Finsupp.mem_support_iff, coeff_laurentCartier hp.ne_zero,
        ← Finsupp.mem_support_iff] at hj
      have hi := (laurentDeg_le_iff R _).1 le_rfl _ hj i
      simp only [Pi.smul_apply, nsmul_eq_mul, Int.natAbs_mul, Int.natAbs_natCast] at hi
      have : (j i).natAbs < p ^ s := by
        apply Nat.lt_of_mul_lt_mul_left (a := p)
        rw [← pow_succ']
        omega
      omega
    have hstep := constantTerm_pow_mul_modEq_laurentCartier hp P R (p ^ s * n) 0
    simp only [Nat.add_zero, pow_zero, one_mul] at hstep
    rw [pow_succ', Nat.mul_assoc]
    exact hstep.trans (by simpa [coeff_laurentCartier hp.ne_zero] using ih _ hdeg)

-- Read the low digits first. The bound on the Laurent degree is independent of their number.
private theorem read_suffix {r p : ℕ} (hp : p.Prime) (P : AddMonoidAlgebra ℤ (Fin r → ℤ))
    {m : ℕ} (hP : laurentDeg P - 1 ≤ m) (k t : ℕ) (ht : t < p ^ k)
    (R : AddMonoidAlgebra ℤ (Fin r → ℤ)) (hR : laurentDeg R ≤ m) :
    ∃ S : AddMonoidAlgebra ℤ (Fin r → ℤ), laurentDeg S ≤ m ∧
      ∀ n, (P ^ (p ^ k * n + t) * R).coeff 0 ≡ (P ^ n * S).coeff 0 [ZMOD p] := by
  induction k generalizing R t with
  | zero =>
    have : t = 0 := by simpa using ht
    exact ⟨R, hR, fun n => by simp [this]⟩
  | succ k ih =>
    let d := t % p
    have hd : d < p := Nat.mod_lt _ hp.pos
    let S := laurentCartier p (P ^ d * R)
    have hS : laurentDeg S ≤ m :=
      (laurentDeg_foldl_laurentCartier_le hp P R [d] (by simpa using hd)).trans
        (max_le hP hR)
    obtain ⟨T, hT, hseq⟩ := ih (t / p) ((Nat.div_lt_iff_lt_mul hp.pos).2
      (by simpa [pow_succ] using ht)) S hS
    refine ⟨T, hT, fun n => ?_⟩
    have he : p ^ (k + 1) * n + t = p * (p ^ k * n + t / p) + d := by
      rw [pow_succ', Nat.mul_assoc, Nat.mul_add, Nat.add_assoc, Nat.mul_comm p (t / p)]
      exact congrArg (_ + ·) (Nat.div_add_mod' t p).symm
    rw [he]
    exact (constantTerm_pow_mul_modEq_laurentCartier hp P R _ d).trans (hseq n)

-- In base B, one digit forces the residue to vanish for every prefix and suffix.
private theorem exists_zero_digit {r p : ℕ} (hp : p.Prime)
    (P Q : AddMonoidAlgebra ℤ (Fin r → ℤ)) {w : ℕ} (hw : (p : ℤ) ∣ (P ^ w).coeff 0) :
    ∃ B d : ℕ, 1 < B ∧ d < B ∧ ∀ k h t : ℕ, t < B ^ k →
      (p : ℤ) ∣ (P ^ ((B * h + d) * B ^ k + t) * Q).coeff 0 := by
  let m := max (laurentDeg P - 1) (laurentDeg Q)
  let s := max (max m (laurentDeg (P ^ w))) (max w 1)
  let a := p ^ s
  have hs : s < a := Nat.lt_pow_self hp.one_lt
  have hm : m < a := lt_of_le_of_lt (by dsimp [s]; omega) hs
  have hdeg : laurentDeg (P ^ w) < a := lt_of_le_of_lt (by dsimp [s]; omega) hs
  have hw' : w < a := lt_of_le_of_lt (by dsimp [s]; omega) hs
  have ha : 1 < a := lt_of_le_of_lt (by dsimp [s]; omega) hs
  refine ⟨a * a, a * w, by nlinarith, Nat.mul_lt_mul_of_pos_left hw' (by omega), ?_⟩
  intro k h t ht
  have hpow : (a * a) ^ k = p ^ ((s + s) * k) := by rw [pow_mul, pow_add]
  rw [hpow] at ht ⊢
  obtain ⟨R, hR, hread⟩ := read_suffix hp P (m := m) (le_max_left _ _) _ t ht Q
    (le_max_right _ _)
  rw [Nat.mul_comm (a * a * h + a * w)]
  apply (hread _).dvd_iff.mpr
  rw [show a * a * h + a * w = a * (a * h + w) by ring]
  apply (split_constantTerm hp P R s _ (hR.trans_lt hm)).dvd_iff.mpr
  apply dvd_mul_of_dvd_left
  rw [pow_add]
  apply (split_constantTerm hp P (P ^ w) s h hdeg).dvd_iff.mpr
  exact dvd_mul_of_dvd_right hw _

open Finset Filter
open scoped Topology

private theorem count_blocks (f : ℕ → Prop) [DecidablePred f] (a b : ℕ) :
    Nat.count f (a * b) = ∑ j ∈ range a, Nat.count (fun t => f (j * b + t)) b := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.succ_mul, Nat.count_add, ih, sum_range_succ]

-- In each aligned interval the distinguished digit eliminates one of the B subintervals.
private theorem count_without_digit {B d : ℕ} (hd : d < B) (S : Set ℕ)
    (hz : ∀ k h t, t < B ^ k → (B * h + d) * B ^ k + t ∈ S) (k : ℕ) :
    open scoped Classical in Nat.count (fun n => n ∉ S) (B ^ k) ≤ (B - 1) ^ k := by
  classical
  let C (k h : ℕ) := Nat.count (fun t => h * B ^ k + t ∉ S) (B ^ k)
  suffices ∀ h, C k h ≤ (B - 1) ^ k by simpa [C] using this 0
  induction k with
  | zero => exact fun h => (Nat.count_le _).trans_eq (by simp)
  | succ k ih =>
    intro h
    have expand : C (k + 1) h = ∑ j ∈ range B, C k (h * B + j) := by
      dsimp only [C]
      rw [pow_succ', count_blocks]
      simp only [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
    have hzero : C k (h * B + d) = 0 := Nat.count_of_forall_not fun t ht =>
      not_not.mpr (by simpa [Nat.mul_comm B h] using hz k h t ht)
    rw [expand, ← sum_erase_add _ _ (mem_range.mpr hd), hzero, add_zero]
    calc
      _ ≤ ∑ _j ∈ (range B).erase d, (B - 1) ^ k := sum_le_sum fun _ _ => ih _
      _ = (B - 1) ^ (k + 1) := by
        simp [card_erase_of_mem (mem_range.mpr hd), pow_succ']

private theorem density_of_zero_digit {B d : ℕ} (hB : 1 < B) (hd : d < B) (S : Set ℕ)
    (hz : ∀ k h t, t < B ^ k → (B * h + d) * B ^ k + t ∈ S) : S.HasDensity 1 := by
  classical
  let c (N : ℕ) := Nat.count (fun n => n ∉ S) N
  let q := ((B - 1 : ℕ) : ℝ) / B
  have hlog : Tendsto (Nat.log B) atTop atTop :=
    tendsto_atTop_atTop.mpr fun k => ⟨B ^ k, fun _ => Nat.le_log_of_pow_le hB⟩
  have hq : q < 1 := by
    apply (div_lt_one (by positivity : 0 < (B : ℝ))).mpr
    exact_mod_cast (show B - 1 < B by omega)
  have hlim : Tendsto (fun N => ((B - 1 : ℕ) : ℝ) * q ^ Nat.log B N) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by dsimp [q]; positivity) hq
      |>.comp hlog).const_mul ((B - 1 : ℕ) : ℝ)
  have hc : Tendsto (fun N => (c N : ℝ) / N) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    · exact .of_forall fun N => by positivity
    filter_upwards [eventually_ge_atTop 1] with N hN
    let k := Nat.log B N
    have hcount : c N ≤ (B - 1) ^ (k + 1) :=
      (Nat.count_monotone _ (Nat.lt_pow_of_log_lt hB (Nat.lt_succ_self k)).le).trans
        (count_without_digit hd S hz _)
    have hden : B ^ k ≤ N := Nat.pow_log_le_self _ (by omega)
    calc
      (c N : ℝ) / N ≤ (((B - 1 : ℕ) : ℝ) ^ (k + 1)) / (B : ℝ) ^ k :=
        div_le_div₀ (by positivity) (by exact_mod_cast hcount)
          (by positivity) (by exact_mod_cast hden)
      _ = _ := by rw [pow_succ', mul_div_assoc, ← div_pow]
  have hpart (N : ℕ) : (S ∩ Set.Iio N).ncard + c N = N := by
    have heq : S ∩ Set.Iio N = ↑((range N).filter (· ∈ S)) := by ext; simp [and_comm]
    rw [heq, Set.ncard_coe_finset]
    simpa [c, Nat.count_eq_card_filter_range] using
      ((range N).card_filter_add_card_filter_not (· ∈ S))
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hc
  apply (show Tendsto _ _ (𝓝 (1 : ℝ)) by simpa using h).congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Set.ncard_Iio_nat]
  have hsum : ((S ∩ Set.Iio N).ncard : ℝ) + c N = N := by exact_mod_cast hpart N
  change 1 - (c N : ℝ) / N = _
  field_simp
  linarith

-- A symbol in a uniformly recurrent sequence must recur with bounded gaps.
private theorem eq_zero_of_zero_runs {α : Type*} [Zero α] (s : ℕ → α)
    (hrec : IsUniformlyRecurrentSeq s) (hruns : ∀ L : ℕ, ∃ i, ∀ t < L, s (i + t) = 0)
    (n : ℕ) : s n = 0 := by
  obtain ⟨C, hC⟩ := hrec n 1
  have cover (k : ℕ) : ∃ j, n + k ≤ j ∧ j ≤ n + k + C ∧ s j = s n := by
    induction k with
    | zero => exact ⟨n, by omega, by omega, rfl⟩
    | succ k ih =>
      obtain ⟨j, hj, hj', heq⟩ := ih
      by_cases h : n + (k + 1) ≤ j
      · exact ⟨j, h, by omega, heq⟩
      · obtain ⟨u, hu, hu', hnext⟩ := hC j (by
          intro t ht
          have : t = 0 := by omega
          simpa [this] using heq)
        exact ⟨j + u, by omega, by omega, by simpa using hnext 0 (by decide)⟩
  obtain ⟨i, hi⟩ := hruns (n + C + 1)
  obtain ⟨j, hj, hj', heq⟩ := cover i
  have hzero := hi (j - i) (by omega)
  rwa [show i + (j - i) = j by omega, heq] at hzero

end constantTerm_zero_density_mod_prime

open constantTerm_zero_density_mod_prime in
/-- **Density-one zeros of constant terms modulo $p$.** Let $p$ be a prime, let $P$ be a Laurent
polynomial in $r$ variables with integer coefficients, write $\operatorname{ct}[F]$ for the
constant term of a Laurent polynomial $F$, and suppose that $p$ divides $\operatorname{ct}[P^n]$
for some natural number $n$. Then for every Laurent polynomial $Q$ in $r$ variables with integer
coefficients, the set of natural numbers $n$ with $p \mid \operatorname{ct}[P^n Q]$ has natural
density $1$; for every natural number $L$ there is a natural number $i$ such that
$p \mid \operatorname{ct}[P^{i+t} Q]$ for all $t < L$; and either
$p \mid \operatorname{ct}[P^n Q]$ for every $n$, or the sequence of residues
$\operatorname{ct}[P^n Q] \bmod p$ in $\mathbb{Z}/p\mathbb{Z}$ is not uniformly recurrent.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Theorem 14 (`jis-2026-26.4.2-thm-14`). -/
public theorem constantTerm_zero_density_mod_prime {r p : ℕ} (hp : p.Prime)
    (P : AddMonoidAlgebra ℤ (Fin r → ℤ)) (hP : ∃ n, (p : ℤ) ∣ (P ^ n).coeff 0)
    (Q : AddMonoidAlgebra ℤ (Fin r → ℤ)) :
    ({n : ℕ | (p : ℤ) ∣ (P ^ n * Q).coeff 0} : Set ℕ).HasDensity 1 ∧
      (∀ L : ℕ, ∃ i, ∀ t < L, (p : ℤ) ∣ (P ^ (i + t) * Q).coeff 0) ∧
      ((∀ n, (p : ℤ) ∣ (P ^ n * Q).coeff 0) ∨
        ¬ IsUniformlyRecurrentSeq fun n => ((P ^ n * Q).coeff 0 : ZMod p)) := by
  obtain ⟨w, hw⟩ := hP
  obtain ⟨B, d, hB, hd, hz⟩ := exists_zero_digit hp P Q hw
  have hruns (L : ℕ) : ∃ i, ∀ t < L, (p : ℤ) ∣ (P ^ (i + t) * Q).coeff 0 := by
    refine ⟨d * B ^ L, fun t ht => ?_⟩
    simpa using hz L 0 t (ht.trans (Nat.lt_pow_self hB))
  refine ⟨density_of_zero_digit hB hd _ hz, hruns, or_iff_not_imp_right.mpr ?_⟩
  simp only [not_not]
  intro hrec n
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  apply eq_zero_of_zero_runs _ hrec _ n
  intro L
  obtain ⟨i, hi⟩ := hruns L
  exact ⟨i, fun t ht => (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hi t ht)⟩

end

end MetaMathlibExt
