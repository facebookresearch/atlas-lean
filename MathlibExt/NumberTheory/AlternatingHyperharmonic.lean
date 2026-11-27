/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Choose.Basic
import MathlibExt.Analysis.Series.StolzCesaro
import MathlibExt.Analysis.SpecialFunctions.Log.AlternatingHarmonic
import MathlibExt.NumberTheory.Harmonic.ShiftedChoose

/-!
# Type II alternating hyperharmonic numbers

The type II numbers of order `r` are asymptotic to the alternating zeta value
times `n ^ (r - 1) / (r - 1)!`.
-/

namespace MetaMathlibExt

open Asymptotics Filter Finset
open scoped Topology

@[expose] public section

/-- **Alternating generalized harmonic numbers.** For a real number $s$ and a natural number $n$,
the alternating generalized harmonic number is
$\overline{H}_n^{(s)} = \sum_{j=1}^{n} (-1)^{j-1} / j^s$, which is $0$ for $n = 0$.

For $s = -p$ with $p$ a natural number this is $\sum_{j=1}^{n} (-1)^{j-1} j^p$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Section 1 (definition of `H̄_n^{(p)}` and `H̄_n^{(-p)}`). -/
public noncomputable def alternatingGeneralizedHarmonic (s : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 n, (-1 : ℝ) ^ (j - 1) * ((j : ℝ) ^ s)⁻¹

/-- **Alternating generalized harmonic numbers of index zero.** For every real number $s$, the
alternating generalized harmonic number $\overline{H}_0^{(s)}$ is $0$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Section 1 (definition of `H̄_n^{(p)}`). -/
@[simp]
public theorem alternatingGeneralizedHarmonic_zero (s : ℝ) :
    alternatingGeneralizedHarmonic s 0 = 0 := by
  simp [alternatingGeneralizedHarmonic]

/-- **Signed iterated partial sums.** Let $(b_n)_{n \ge 0}$ be a real sequence and fix a choice of
signs, either alternating, $\varepsilon_k = (-1)^{k-1}$, or constant, $\varepsilon_k = 1$. The
signed iterated partial sums $S^{(r)}_n$ of $b$, for orders $r \in \mathbb{N}$ and
$n \in \mathbb{N}$, are defined by $S^{(0)}_n = 0$, $S^{(1)}_n = b_n$ and, for $r \ge 1$,
$$S^{(r+1)}_n = \sum_{k=1}^{n} \varepsilon_k \, S^{(r)}_k.$$
The value $0$ at order $0$ is a convention and is not used.

With $b_n = H_n^{(p)} = \sum_{j=1}^{n} j^{-p}$, constant signs give the generalized hyperharmonic
numbers $H_n^{(p,r)}$ and alternating signs give the type I alternating ones $H_n^{(p,r,1)}$; with
$b_n = \bar H_n^{(p)} = \sum_{j=1}^{n} (-1)^{j-1} j^{-p}$, constant signs give type II,
$H_n^{(p,r,2)}$, and alternating signs give type III, $H_n^{(p,r,3)}$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Section 1 (definitions of `H_n^{(p,r)}` and `H_n^{(p,r,i)}`, `i = 1, 2, 3`). -/
public noncomputable def signedIteratedPartialSum (alt : Bool) (b : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | 1, n => b n
  | r + 2, n => ∑ k ∈ Icc 1 n, (if alt then (-1 : ℝ) ^ (k - 1) else 1) *
      signedIteratedPartialSum alt b (r + 1) k

/-- **Order one of the signed iterated partial sums.** For every real sequence
$(b_n)_{n \ge 0}$, either choice of signs and every $n \in \mathbb{N}$, the signed iterated partial
sum of $b$ of order $1$ at $n$ equals $b_n$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Section 1 (`H_n^{(p,1)} = H_n^{(p)}`, `H_n^{(p,1,1)} = H_n^{(p)}`,
`H_n^{(p,1,2)} = H_n^{(p,1,3)} = H̄_n^{(p)}`). -/
public theorem signedIteratedPartialSum_one (alt : Bool) (b : ℕ → ℝ) (n : ℕ) :
    signedIteratedPartialSum alt b 1 n = b n := rfl

/-- **Recursion for the signed iterated partial sums.** Let $(b_n)_{n \ge 0}$ be a real sequence,
fix a choice of signs, either $\varepsilon_k = (-1)^{k-1}$ for all $k$ or $\varepsilon_k = 1$ for
all $k$, and let $S^{(r)}_n$ denote the signed iterated partial sum of $b$ of order $r$ at $n$ for
this choice. Then for every $r \ge 1$ and every $n \in \mathbb{N}$,
$$S^{(r+1)}_n = \sum_{k=1}^{n} \varepsilon_k \, S^{(r)}_k.$$

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Section 1 (definitions of `H_n^{(p,r)}` and `H_n^{(p,r,i)}`). -/
public theorem signedIteratedPartialSum_succ (alt : Bool) (b : ℕ → ℝ) (r n : ℕ) :
    signedIteratedPartialSum alt b (r + 2) n = ∑ k ∈ Icc 1 n,
      (if alt then (-1 : ℝ) ^ (k - 1) else 1) * signedIteratedPartialSum alt b (r + 1) k := rfl

/-- **Alternating zeta values.** For a natural number $p$, the alternating zeta value
$\bar\zeta(p)$ is defined by $\bar\zeta(1) = \log 2$, by $\bar\zeta(p) = (1 - 2^{1-p})\,\zeta(p)$
for $p \ge 2$, where $\zeta(p) = \sum_{n \ge 1} 1/n^p$, and by $\bar\zeta(0) = 0$.

For every $p \ge 1$ this is the alternating series $\bar\zeta(p) = \sum_{n \ge 1} (-1)^{n-1}/n^p$;
the value at $p = 0$ is not used.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 10 (definition of `ζ̄(s)`). -/
public noncomputable def alternatingZeta (p : ℕ) : ℝ :=
  if p = 1 then Real.log 2 else (1 - 2 ^ (1 - (p : ℝ))) * ∑' n : ℕ, 1 / (n : ℝ) ^ p

/-- **Alternating zeta value at one.** The alternating zeta value at $1$ is $\bar\zeta(1) = \log 2$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 10 (definition of `ζ̄(s)`). -/
@[simp]
public theorem alternatingZeta_one : alternatingZeta 1 = Real.log 2 := by
  simp [alternatingZeta]

end

namespace alternatingHyperharmonic_typeII_isEquivalent

private theorem harmonic_limit {p : ℕ} (hp : 1 ≤ p) :
    Tendsto (alternatingGeneralizedHarmonic p) atTop (𝓝 (alternatingZeta p)) := by
  have reindex (n : ℕ) : alternatingGeneralizedHarmonic p n =
      ∑ k ∈ range n, (-1 : ℝ) ^ k / ((k + 1 : ℕ) : ℝ) ^ p := by
    rw [alternatingGeneralizedHarmonic, ← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
    simp [Nat.add_comm 1, div_eq_mul_inv]
  rw [funext reindex]
  rcases eq_or_lt_of_le hp with h | h
  · subst p
    simpa using Real.tendsto_sum_alternating_harmonic
  -- The even denominators contribute a fraction 2⁻ᵖ of the whole p-series.
  let f (n : ℕ) : ℝ := 1 / (n : ℝ) ^ p
  let Z := ∑' n, f n
  let c := ((2 : ℝ) ^ p)⁻¹
  have hf : Summable f := Real.summable_one_div_nat_pow.mpr h
  have heven : HasSum (fun k => f (2 * k)) (c * Z) := by
    simpa [Z, f, c, mul_pow, one_div, mul_comm] using hf.hasSum.mul_left c
  have ho := (hf.comp_injective (show Function.Injective (fun k : ℕ => 2 * k + 1) by
    intro a b hab
    dsimp at hab
    omega)).hasSum
  have hsplit := (heven.even_add_odd (f := f) ho).tsum_eq
  have hfshift : HasSum (fun k => f (k + 1)) Z := by
    apply (hasSum_nat_add_iff 1).2
    simpa [Z, f, ne_of_gt (show 0 < p by omega)] using hf.hasSum
  let g (k : ℕ) := (-1 : ℝ) ^ k / ((k + 1 : ℕ) : ℝ) ^ p
  have hge : HasSum (fun k => g (2 * k)) (∑' k, f (2 * k + 1)) := by
    simpa [g, pow_mul, f, Function.comp_def] using ho
  have hgo : HasSum (fun k => g (2 * k + 1)) (-(c * Z)) := by
    refine ((hfshift.mul_left c).neg).congr_fun ?_
    intro k
    suffices ((2 * (k : ℝ) + 1 + 1) ^ p)⁻¹ = (2 ^ p)⁻¹ * ((k + 1 : ℝ) ^ p)⁻¹ by
      simpa [g, f, c, pow_succ (-1 : ℝ), pow_mul, div_eq_mul_inv] using this
    rw [show 2 * (k : ℝ) + 1 + 1 = 2 * (k + 1) by ring, mul_pow, mul_inv_rev, mul_comm]
  have hvalue : (∑' k, f (2 * k + 1)) + -(c * Z) = alternatingZeta p := by
    simp only [alternatingZeta, h.ne', ↓reduceIte]
    rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_natCast]
    change _ = (1 - 2 / (2 : ℝ) ^ p) * Z
    change Z = c * Z + ∑' k, f (2 * k + 1) at hsplit
    rw [div_eq_mul_inv]
    change _ = (1 - 2 * c) * Z
    linear_combination -hsplit
  rw [← hvalue]
  exact (hge.even_add_odd (f := g) hgo).tendsto_sum_nat

private theorem zeta_pos {p : ℕ} (hp : 1 ≤ p) : 0 < alternatingZeta p := by
  rcases eq_or_lt_of_le hp with h | h
  · subst p
    exact Real.log_pos (by norm_num : (1 : ℝ) < 2)
  simp only [alternatingZeta, h.ne', ↓reduceIte]
  apply mul_pos
  · apply sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ?_)
    exact sub_neg.mpr (by exact_mod_cast h)
  · exact (Real.summable_one_div_nat_pow.mpr h).tsum_pos (fun n => by positivity) 1 (by simp)

-- Pascal's identity makes the first difference of the binomial denominator
-- exactly the denominator of the preceding order at the next index.
private theorem iterated_limit {b : ℕ → ℝ} {L : ℝ} (hb : Tendsto b atTop (𝓝 L)) (d : ℕ) :
    Tendsto (fun n => signedIteratedPartialSum false b (d + 1) n / (n + d).choose d)
      atTop (𝓝 L) := by
  induction d with
  | zero => simpa [signedIteratedPartialSum_one] using hb
  | succ d ih =>
    let B (n : ℕ) := (n + (d + 1)).choose (d + 1)
    have step (n : ℕ) : B (n + 1) = (n + 1 + d).choose d + B n := by
      dsimp [B]
      rw [show n + 1 + (d + 1) = (n + (d + 1)) + 1 by omega, Nat.choose_succ_succ]
      rw [show n + 1 + d = n + (d + 1) by omega]
    have hB : StrictMono B := by
      apply strictMono_nat_of_lt_succ
      intro n
      rw [step]
      have := Nat.choose_pos (show d ≤ n + 1 + d by omega)
      omega
    apply stolz_cesaro (b := fun n => (B n : ℝ)) (fun _ _ h => Nat.cast_lt.mpr (hB h))
      (tendsto_natCast_atTop_atTop.comp hB.tendsto_atTop)
    convert ih.comp (tendsto_add_atTop_nat 1) using 1
    ext n
    simp [signedIteratedPartialSum_succ, sum_Icc_succ_top, step]

end alternatingHyperharmonic_typeII_isEquivalent

open alternatingHyperharmonic_typeII_isEquivalent in
/-- **Asymptotic of type II alternating hyperharmonic numbers.** For a natural number $p$ let
$\overline{H}_n^{(p)} = \sum_{i=1}^{n} (-1)^{i-1}/i^p$ be the alternating generalized harmonic
numbers, and let the type II generalized alternating hyperharmonic numbers be
$H_n^{(p,1,2)} = \overline{H}_n^{(p)}$ and $H_n^{(p,r+1,2)} = \sum_{k=1}^{n} H_k^{(p,r,2)}$. Let
$\bar\zeta(p)$ be the alternating zeta value at $p$, so that $\bar\zeta(1) = \log 2$. Then for all
natural numbers $r, p \ge 1$, $H_n^{(p,r,2)} \sim n^{r-1} \bar\zeta(p) / (r-1)!$ as $n \to \infty$.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 13 (`jis-2024-24.4.1-lem-13`). -/
public theorem alternatingHyperharmonic_typeII_isEquivalent {r p : ℕ} (hr : 1 ≤ r)
    (hp : 1 ≤ p) :
    (fun n : ℕ => signedIteratedPartialSum false (alternatingGeneralizedHarmonic p) r n) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ (r - 1) * alternatingZeta p / (r - 1).factorial := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  simp only [Nat.add_one_sub_one]
  have h := (isEquivalent_const_iff_tendsto (zeta_pos hp).ne').2
    (iterated_limit (harmonic_limit hp) d)
  have hprod := h.mul (isEquivalent_add_choose d)
  refine (hprod.congr_left (.of_forall fun n => ?_)).congr_right (.of_forall fun n => ?_)
  · exact div_mul_cancel₀ _ (by exact_mod_cast (Nat.choose_pos (Nat.le_add_left d n)).ne')
  · dsimp [Function.const]
    ring

end MetaMathlibExt
