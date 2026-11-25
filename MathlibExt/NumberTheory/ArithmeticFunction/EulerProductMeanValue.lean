/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Interval.Finset.Basic
import MathlibExt.NumberTheory.ArithmeticFunction.WintnerMeanValue
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

namespace MetaMathlibExt

/-- Coordinate restriction of `f` to the `i`-th coordinate, as an arithmetic
function: `emvF f i m = f (Function.update 1 i m)` for `m ≠ 0`. -/
private noncomputable def emvF {k : ℕ} (f : (Fin k → ℕ) → ℂ) (i : Fin k) :
    ArithmeticFunction ℂ :=
  ⟨fun m => if m = 0 then 0 else f (Function.update 1 i m), rfl⟩

/-- Moebius convolution factor `μ * emvF f i`, with the same coercion as in
`wintner_mean_value`. -/
private noncomputable def emvG {k : ℕ} (f : (Fin k → ℕ) → ℂ) (i : Fin k) :
    ArithmeticFunction ℂ :=
  (↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * emvF f i

private lemma emvF_apply {k : ℕ} (f : (Fin k → ℕ) → ℂ) (i : Fin k) {m : ℕ}
    (hm : m ≠ 0) :
    emvF f i m = f (Function.update 1 i m) := by
  change (if m = 0 then (0 : ℂ) else f (Function.update 1 i m)) = _
  rw [ite_eq_right hm]

private lemma emvF_one {k : ℕ} (f : (Fin k → ℕ) → ℂ) (i : Fin k) :
    emvF f i 1 = f 1 := by
  rw [emvF_apply f i one_ne_zero]
  have hupd : Function.update (1 : Fin k → ℕ) i 1 = 1 := by
    funext j
    by_cases hji : j = i
    · subst hji
      rw [Function.update_apply, ite_eq_left rfl, Pi.one_apply]
    · rw [Function.update_apply, ite_eq_right hji]
  rw [hupd]

/-- `f 1` is `0` or `1`. -/
private lemma emv_f_one {k : ℕ} (f : (Fin k → ℕ) → ℂ)
    (hmult : ∀ a b : Fin k → ℕ, (∀ i, Nat.Coprime (a i) (b i)) →
      f (fun i => a i * b i) = f a * f b) :
    f 1 = 0 ∨ f 1 = 1 := by
  have h11 : (fun i => (1 : Fin k → ℕ) i * (1 : Fin k → ℕ) i) = 1 := by
    funext i
    simp
  have h := hmult 1 1 (fun _ => Nat.coprime_one_left 1)
  rw [h11] at h
  have hfac : f 1 * (f 1 - 1) = 0 := by linear_combination -h
  rcases mul_eq_zero.mp hfac with hz | hz
  · exact Or.inl hz
  · exact Or.inr (sub_eq_zero.mp hz)

/-- If `f 1 = 0` then `f` is identically `0`. -/
private lemma emv_f_zero_of_one_zero {k : ℕ} (f : (Fin k → ℕ) → ℂ)
    (hmult : ∀ a b : Fin k → ℕ, (∀ i, Nat.Coprime (a i) (b i)) →
      f (fun i => a i * b i) = f a * f b)
    (h1 : f 1 = 0) (n : Fin k → ℕ) :
    f n = 0 := by
  have h := hmult n 1 (fun i => Nat.coprime_one_right (n i))
  have hn : (fun i => n i * (1 : Fin k → ℕ) i) = n := by
    funext i
    simp
  rw [hn, h1, mul_zero] at h
  exact h

/-- Auxiliary product decomposition over a finset of coordinates. -/
private lemma emv_prod_decomp_aux {k : ℕ} (f : (Fin k → ℕ) → ℂ)
    (hmult : ∀ a b : Fin k → ℕ, (∀ i, Nat.Coprime (a i) (b i)) →
      f (fun i => a i * b i) = f a * f b)
    (h1 : f 1 = 1) {n : Fin k → ℕ} (s : Finset (Fin k)) :
    f (fun j => if j ∈ s then n j else 1) =
      ∏ i ∈ s, f (Function.update 1 i (n i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hempty : (fun j => if j ∈ (∅ : Finset (Fin k)) then n j else 1) = 1 := by
      funext j
      simp
    rw [hempty, h1, Finset.prod_empty]
  | insert a s has ih =>
    have hfactor : (fun j => if j ∈ insert a s then n j else 1)
        = (fun j => (if j ∈ s then n j else 1) *
          Function.update (1 : Fin k → ℕ) a (n a) j) := by
      funext j
      by_cases hja : j = a
      · subst hja
        rw [ite_eq_left (Finset.mem_insert_self j s), ite_eq_right has,
          Function.update_apply, ite_eq_left rfl, one_mul]
      · by_cases hjs : j ∈ s
        · rw [ite_eq_left (Finset.mem_insert_of_mem hjs), ite_eq_left hjs,
            Function.update_apply, ite_eq_right hja, Pi.one_apply, mul_one]
        · rw [ite_eq_right (by simpa [hja] using hjs), ite_eq_right hjs,
            Function.update_apply, ite_eq_right hja, one_mul, Pi.one_apply]
    have hcop : ∀ j, Nat.Coprime ((if j ∈ s then n j else 1))
        (Function.update (1 : Fin k → ℕ) a (n a) j) := by
      intro j
      by_cases hja : j = a
      · subst hja
        rw [ite_eq_right has, Function.update_apply, ite_eq_left rfl]
        exact Nat.coprime_one_left _
      · rw [Function.update_apply, ite_eq_right hja]
        exact Nat.coprime_one_right _
    rw [hfactor, hmult _ _ hcop, ih, Finset.prod_insert has]
    exact mul_comm _ _

/-- Under `hmult` and `f 1 = 1`, `f` splits as a product over coordinates. -/
private lemma emv_prod_decomp {k : ℕ} (f : (Fin k → ℕ) → ℂ)
    (hmult : ∀ a b : Fin k → ℕ, (∀ i, Nat.Coprime (a i) (b i)) →
      f (fun i => a i * b i) = f a * f b)
    (h1 : f 1 = 1) (n : Fin k → ℕ) :
    f n = ∏ i, f (Function.update 1 i (n i)) := by
  have h := emv_prod_decomp_aux f hmult h1 Finset.univ (n := n)
  have huniv : (fun j => if j ∈ (Finset.univ : Finset (Fin k)) then n j else 1)
      = n := by
    funext j
    simp
  rw [huniv] at h
  simpa using h

/-- Product decomposition through the coordinate restrictions. -/
private lemma emv_prod_decomp_apply {k : ℕ} (f : (Fin k → ℕ) → ℂ)
    (hmult : ∀ a b : Fin k → ℕ, (∀ i, Nat.Coprime (a i) (b i)) →
      f (fun i => a i * b i) = f a * f b)
    (h1 : f 1 = 1) {n : Fin k → ℕ} (hn : ∀ i, n i ≠ 0) :
    f n = ∏ i, emvF f i (n i) := by
  rw [emv_prod_decomp f hmult h1 n]
  apply Finset.prod_congr rfl
  intro i _
  exact (emvF_apply f i (hn i)).symm

/-- The coordinate restriction is multiplicative. -/
private lemma emvF_isMultiplicative {k : ℕ} (f : (Fin k → ℕ) → ℂ) (i : Fin k)
    (hmult : ∀ a b : Fin k → ℕ, (∀ i, Nat.Coprime (a i) (b i)) →
      f (fun i => a i * b i) = f a * f b)
    (h1 : f 1 = 1) :
    (emvF f i).IsMultiplicative := by
  constructor
  · rw [emvF_one f i, h1]
  · intro m n hcop
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    have hmn : m * n ≠ 0 := mul_ne_zero hm hn
    rw [emvF_apply _ _ hmn, emvF_apply _ _ hm, emvF_apply _ _ hn]
    have hupd : Function.update (1 : Fin k → ℕ) i (m * n)
        = (fun j => Function.update (1 : Fin k → ℕ) i m j *
          Function.update (1 : Fin k → ℕ) i n j) := by
      funext j
      by_cases hji : j = i
      · subst hji
        rw [Function.update_apply, Function.update_apply, Function.update_apply,
          ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl]
      · rw [Function.update_apply, Function.update_apply, Function.update_apply,
          ite_eq_right hji, ite_eq_right hji, ite_eq_right hji, Pi.one_apply,
          mul_one]
    have hcop' : ∀ j, Nat.Coprime (Function.update (1 : Fin k → ℕ) i m j)
        (Function.update (1 : Fin k → ℕ) i n j) := by
      intro j
      by_cases hji : j = i
      · subst hji
        rw [Function.update_apply, Function.update_apply, ite_eq_left rfl,
          ite_eq_left rfl]
        exact hcop
      · rw [Function.update_apply, Function.update_apply, ite_eq_right hji,
          ite_eq_right hji]
        exact Nat.coprime_one_left _
    rw [hupd]
    exact hmult _ _ hcop'

/-- The Moebius convolution factor is multiplicative. -/
private lemma emvG_isMultiplicative {k : ℕ} (f : (Fin k → ℕ) → ℂ) (i : Fin k)
    (hmult : ∀ a b : Fin k → ℕ, (∀ i, Nat.Coprime (a i) (b i)) →
      f (fun i => a i * b i) = f a * f b)
    (h1 : f 1 = 1) :
    (emvG f i).IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.mul
    ArithmeticFunction.isMultiplicative_moebius.intCast
    (emvF_isMultiplicative f i hmult h1)

/-- Unfolding of `emvG` as a divisor sum. -/
private lemma emvG_apply {k : ℕ} (f : (Fin k → ℕ) → ℂ) (i : Fin k) (m : ℕ) :
    emvG f i m = ∑ x ∈ m.divisorsAntidiagonal,
      (((ArithmeticFunction.moebius x.1 : ℤ)) : ℂ) * emvF f i x.2 := by
  change ((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * emvF f i) m
    = _
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [ArithmeticFunction.intCoe_apply]

/-- The Wanted divisor sum at a prime power equals the product of the local
Moebius factors. -/
private lemma emv_G_eq_prod {k : ℕ} (f : (Fin k → ℕ) → ℂ)
    (hmult : ∀ a b : Fin k → ℕ, (∀ i, Nat.Coprime (a i) (b i)) →
      f (fun i => a i * b i) = f a * f b)
    (h1 : f 1 = 1) (p : ℕ) (hp : Nat.Prime p) (ν : Fin k → ℕ) :
    (∑ d ∈ Fintype.piFinset (fun i => Nat.divisors (p ^ (ν i))),
        (∏ i, ((ArithmeticFunction.moebius (d i) : ℤ) : ℂ)) *
        f (fun i => p ^ (ν i) / d i))
    = ∏ i, emvG f i (p ^ (ν i)) := by
  have hmem : ∀ d ∈ Fintype.piFinset (fun i => Nat.divisors (p ^ (ν i))),
      ∀ i, 1 ≤ p ^ (ν i) / d i := by
    intro d hd i
    have hi := Fintype.mem_piFinset.mp hd i
    rw [Nat.mem_divisors] at hi
    have hpos : 0 < p ^ (ν i) := pow_pos hp.pos _
    exact Nat.div_pos (Nat.le_of_dvd hpos hi.1)
      (Nat.pos_of_dvd_of_pos hi.1 hpos)
  have hsummand : ∀ d ∈ Fintype.piFinset (fun i => Nat.divisors (p ^ (ν i))),
      (∏ i, ((ArithmeticFunction.moebius (d i) : ℤ) : ℂ)) *
        f (fun i => p ^ (ν i) / d i)
      = ∏ i, (((ArithmeticFunction.moebius (d i) : ℤ) : ℂ) *
        emvF f i (p ^ (ν i) / d i)) := by
    intro d hd
    have hdecomp := emv_prod_decomp_apply f hmult h1
      (n := fun i => p ^ (ν i) / d i) (fun i => ne_of_gt (hmem d hd i))
    rw [hdecomp, Finset.prod_mul_distrib]
  calc (∑ d ∈ Fintype.piFinset (fun i => Nat.divisors (p ^ (ν i))),
          (∏ i, ((ArithmeticFunction.moebius (d i) : ℤ) : ℂ)) *
          f (fun i => p ^ (ν i) / d i))
        = ∑ d ∈ Fintype.piFinset (fun i => Nat.divisors (p ^ (ν i))),
          ∏ i, (((ArithmeticFunction.moebius (d i) : ℤ) : ℂ) *
            emvF f i (p ^ (ν i) / d i)) :=
          Finset.sum_congr rfl (fun d hd => hsummand d hd)
      _ = ∏ i, ∑ u ∈ Nat.divisors (p ^ (ν i)),
          (((ArithmeticFunction.moebius u : ℤ)) : ℂ) *
            emvF f i (p ^ (ν i) / u) :=
          (Finset.prod_univ_sum (fun i => Nat.divisors (p ^ (ν i)))
            (fun i u => (((ArithmeticFunction.moebius u : ℤ)) : ℂ) *
              emvF f i (p ^ (ν i) / u))).symm
      _ = ∏ i, emvG f i (p ^ (ν i)) := by
          apply Finset.prod_congr rfl
          intro i _
          rw [emvG_apply f i]
          exact (Nat.sum_divisorsAntidiagonal
            (fun a b => (((ArithmeticFunction.moebius a : ℤ)) : ℂ) *
              emvF f i b)).symm

/-- Restriction of the summability hypothesis to a single coordinate. -/
private lemma emv_primePow_summable {k : ℕ} (f : (Fin k → ℕ) → ℂ)
    (hmult : ∀ a b : Fin k → ℕ, (∀ i, Nat.Coprime (a i) (b i)) →
      f (fun i => a i * b i) = f a * f b)
    (h1 : f 1 = 1)
    (hsumm : Summable (fun q : { q : { p : ℕ // p.Prime } × (Fin k → ℕ) //
        q.2 ≠ 0 } =>
      ‖(∑ d ∈ Fintype.piFinset (fun i => Nat.divisors ((q.1.1 : ℕ) ^
          (q.1.2 i))),
          (∏ i, ((ArithmeticFunction.moebius (d i) : ℤ) : ℂ)) *
          f (fun i => (q.1.1 : ℕ) ^ (q.1.2 i) / d i)) /
        (((q.1.1 : ℕ) : ℂ) ^ (∑ i, q.1.2 i))‖))
    (i : Fin k) :
    Summable (fun q : Nat.Primes × ℕ =>
      ‖emvG f i (((q.1 : ℕ)) ^ (q.2 + 1))‖ /
        ((((q.1 : ℕ))) : ℝ) ^ (q.2 + 1)) := by
  have hne : ∀ q : Nat.Primes × ℕ,
      Pi.single i (q.2 + 1) ≠ (0 : Fin k → ℕ) := by
    intro q
    exact Pi.single_ne_zero_iff.mpr (Nat.succ_ne_zero _)
  let φ : Nat.Primes × ℕ →
      { q : { p : ℕ // p.Prime } × (Fin k → ℕ) // q.2 ≠ 0 } :=
    fun q => ⟨((⟨((q.1 : ℕ)), q.1.property⟩ : { p : ℕ // p.Prime }),
      Pi.single i (q.2 + 1)), hne q⟩
  have hφinj : Function.Injective φ := by
    intro a b hab
    have hval : (φ a).val = (φ b).val := congrArg Subtype.val hab
    have hfst : (φ a).val.1 = (φ b).val.1 := congrArg Prod.fst hval
    have hsnd : (φ a).val.2 = (φ b).val.2 := congrArg Prod.snd hval
    have ha1 : a.1 = b.1 :=
      Subtype.ext (congrArg Subtype.val hfst)
    have ha2 : a.2 = b.2 := by
      have h : Pi.single i (a.2 + 1) i = Pi.single i (b.2 + 1) i :=
        congrArg (fun ν : Fin k → ℕ => ν i) hsnd
      rw [Pi.single_apply, Pi.single_apply, ite_eq_left rfl,
        ite_eq_left rfl] at h
      omega
    exact Prod.ext ha1 ha2
  have hcomp := hsumm.comp_injective hφinj
  apply hcomp.congr
  intro q
  obtain ⟨p, e⟩ := q
  simp only [Function.comp_apply]
  have hφpe : φ (p, e) = ⟨((⟨((p : ℕ)), p.property⟩ : { p : ℕ // p.Prime }),
      Pi.single i (e + 1)), hne (p, e)⟩ := rfl
  rw [hφpe]
  dsimp only []
  have hsingle0 : ∀ j : Fin k, j ≠ i →
      emvG f j ((p : ℕ) ^ (Pi.single i (e + 1) j)) = 1 := by
    intro j hji
    have hsj : (Pi.single i (e + 1) : Fin k → ℕ) j = 0 := by
      rw [Pi.single_apply, ite_eq_right hji]
    rw [hsj, pow_zero]
    exact (emvG_isMultiplicative f j hmult h1).map_one
  have h0' : ∀ j ∈ (Finset.univ : Finset (Fin k)), j ≠ i →
      emvG f j ((p : ℕ) ^ (Pi.single i (e + 1) j)) = 1 :=
    fun j _ hji => hsingle0 j hji
  have h1' : i ∉ (Finset.univ : Finset (Fin k)) →
      emvG f i ((p : ℕ) ^ ((Pi.single i (e + 1) : Fin k → ℕ) i)) = 1 :=
    fun hcon => absurd (Finset.mem_univ i) hcon
  have hsinglei : (Pi.single i (e + 1) : Fin k → ℕ) i = e + 1 := by
    rw [Pi.single_apply, ite_eq_left rfl]
  have h0exp : ∀ j ∈ (Finset.univ : Finset (Fin k)), j ≠ i →
      (Pi.single i (e + 1) : Fin k → ℕ) j = 0 := by
    intro j _ hji
    rw [Pi.single_apply, ite_eq_right hji]
  have h1exp : i ∉ (Finset.univ : Finset (Fin k)) →
      (Pi.single i (e + 1) : Fin k → ℕ) i = 0 :=
    fun hcon => absurd (Finset.mem_univ i) hcon
  have hsumexp : ∑ j : Fin k, (Pi.single i (e + 1) : Fin k → ℕ) j = e + 1 := by
    rw [Finset.sum_eq_single i h0exp h1exp, Pi.single_apply, ite_eq_left rfl]
  rw [emv_G_eq_prod f hmult h1 ((p : ℕ)) p.property (Pi.single i (e + 1)),
    Finset.prod_eq_single i h0' h1', hsinglei, hsumexp, norm_div, norm_pow,
    Complex.norm_natCast]

/-- Summability of `‖g n‖ / n` from summability over prime powers. -/
private lemma emv_summable_norm_div (g : ArithmeticFunction ℂ)
    (hg : g.IsMultiplicative)
    (hprime : Summable (fun q : Nat.Primes × ℕ =>
      ‖g (((q.1 : ℕ)) ^ (q.2 + 1))‖ / ((((q.1 : ℕ))) : ℝ) ^ (q.2 + 1))) :
    Summable (fun n : ℕ => ‖g n‖ / (n : ℝ)) := by
  set h : ℕ → ℝ := fun n => ‖g n‖ / (n : ℝ) with hhdef
  have h0 : h 0 = 0 := by
    change ‖g 0‖ / (((0 : ℕ)) : ℝ) = 0
    rw [ArithmeticFunction.map_zero, norm_zero, Nat.cast_zero, zero_div]
  have h1 : h 1 = 1 := by
    change ‖g 1‖ / (((1 : ℕ)) : ℝ) = 1
    rw [hg.1, norm_one, Nat.cast_one, div_one]
  have hnn : ∀ n, 0 ≤ h n := by
    intro n
    change 0 ≤ ‖g n‖ / ((n : ℝ))
    positivity
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → h (m * n) = h m * h n := by
    intro m n hcop
    change ‖g (m * n)‖ / ((((m * n : ℕ))) : ℝ)
      = (‖g m‖ / ((m : ℝ))) * (‖g n‖ / ((n : ℝ)))
    rw [hg.2 hcop, norm_mul, Nat.cast_mul, div_mul_div_comm]
  set F : Nat.Primes × ℕ → ℝ := fun q => h (((q.1 : ℕ)) ^ (q.2 + 1)) with hFdef
  have hF : Summable F := by
    apply hprime.congr
    intro q
    simp only [hFdef, hhdef, Nat.cast_pow]
  have hper : ∀ (p : ℕ) (hp : Nat.Prime p),
      Summable (fun e : ℕ => h (p ^ e)) := by
    intro p hp
    have hslice : Summable (fun e : ℕ => F ((⟨p, hp⟩ : Nat.Primes), e)) :=
      hF.comp_injective (fun a b hab => congrArg Prod.snd hab)
    have hshift : Summable (fun e : ℕ => h (p ^ (e + 1))) :=
      hslice.congr (fun e => rfl)
    exact (summable_nat_add_iff 1).mp hshift
  have hpernorm : ∀ (p : ℕ) (hp : Nat.Prime p),
      Summable (fun n : ℕ => ‖h (p ^ n)‖) := by
    intro p hp
    apply (hper p hp).congr
    intro e
    exact ((Real.norm_eq_abs _).trans (abs_of_nonneg (hnn _))).symm
  have hper' : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ ↦ ‖h (p ^ n)‖) := by
    intro p hp
    exact hpernorm p hp
  have hfactor : ∀ (p : ℕ) (hp : Nat.Prime p),
      (∑' n : ℕ, h (p ^ n)) = 1 + ∑' e : ℕ, F ((⟨p, hp⟩ : Nat.Primes), e) := by
    intro p hp
    have hsum_pe : Summable (fun n : ℕ => h (p ^ n)) := hper p hp
    have hdecomp := hsum_pe.sum_add_tsum_nat_add 1
    rw [Finset.sum_range_one] at hdecomp
    have hp0 : h (p ^ 0) = 1 := by
      rw [pow_zero]
      exact h1
    rw [hp0] at hdecomp
    have hspe : (∑' n : ℕ, h (p ^ (n + 1)))
        = ∑' e : ℕ, F ((⟨p, hp⟩ : Nat.Primes), e) := rfl
    rw [← hdecomp, hspe]
  have hS'sum : Summable (fun q : Nat.Primes => ∑' e : ℕ, F (q, e)) := hF.prod
  have hST : (∑' q : Nat.Primes, ∑' e : ℕ, F (q, e))
      = ∑' q : Nat.Primes × ℕ, F q := hF.tsum_prod.symm
  -- bound for partial sums over `range (N+1)`
  have hbound : ∀ N : ℕ, ∑ n ∈ Finset.range (N + 1), h n ≤
      Real.exp (∑' q : Nat.Primes × ℕ, F q) := by
    intro N
    obtain ⟨-, hHas⟩ :=
      EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
        h1 hmul hper' (Finset.range (N + 1))
    have hmemfact : ∀ n ∈ Finset.range (N + 1), n ≠ 0 →
        n ∈ Nat.factoredNumbers (Finset.range (N + 1)) := by
      intro n hn hne
      rw [Nat.mem_factoredNumbers]
      refine ⟨hne, fun p hp => ?_⟩
      have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactorsList hp
      have hple : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hpdvd
      have hnN : n < N + 1 := Finset.mem_range.mp hn
      exact Finset.mem_range.mpr
        (Nat.lt_succ_of_le (le_trans hple (Nat.lt_succ_iff.mp hnN)))
    set t : Finset ↥(Nat.factoredNumbers (Finset.range (N + 1))) :=
      Finset.subtype (· ∈ Nat.factoredNumbers (Finset.range (N + 1)))
        (Finset.range (N + 1)) with htdef
    have htsum_eq : ∑ n ∈ (Finset.range (N + 1)).filter
        (· ∈ Nat.factoredNumbers (Finset.range (N + 1))), h n
        = ∑ i ∈ t, h (i.val) := by
      refine Finset.sum_bij
        (fun n hn => (⟨n, (Finset.mem_filter.mp hn).2⟩ :
          ↥(Nat.factoredNumbers (Finset.range (N + 1))))) ?_ ?_ ?_ ?_
      · intro n hn
        rw [htdef]
        exact Finset.mem_subtype.mpr (Finset.mem_filter.mp hn).1
      · intro n1 hn1 n2 hn2 heq
        exact congrArg Subtype.val heq
      · intro i hi
        have hi' : (i.val) ∈ (Finset.range (N + 1)).filter
            (· ∈ Nat.factoredNumbers (Finset.range (N + 1))) := by
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_subtype.mp hi, i.property⟩
        refine ⟨i.val, hi', ?_⟩
        exact Subtype.ext rfl
      · intro n hn
        rfl
    have hfilter_eq : ∑ n ∈ (Finset.range (N + 1)).filter
        (· ∈ Nat.factoredNumbers (Finset.range (N + 1))), h n
        = ∑ n ∈ Finset.range (N + 1), h n := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro n hn hnim
      have hn0 : n = 0 := by
        by_contra hne
        exact hnim (Finset.mem_filter.mpr ⟨hn, hmemfact n hn hne⟩)
      rw [hn0]
      exact h0
    have hle_range : ∑ n ∈ Finset.range (N + 1), h n ≤
        (∏ p ∈ Finset.range (N + 1) with p.Prime, ∑' n : ℕ, h (p ^ n)) := by
      rw [← hfilter_eq, htsum_eq]
      have hsumt := hHas.summable.sum_le_tsum t (fun i _ => hnn _)
      rw [hHas.tsum_eq] at hsumt
      exact hsumt
    set u : Finset Nat.Primes :=
      ((Finset.range (N + 1)).filter Nat.Prime).attach.image
        (fun x => (⟨x.val, (Finset.mem_filter.mp x.property).2⟩ :
          Nat.Primes)) with hudef
    have hVtoU : (∏ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
          ∑' n : ℕ, h (p ^ n))
        = ∏ q ∈ u, (∑' n : ℕ, h (((q : ℕ)) ^ n)) := by
      refine Finset.prod_bij
        (fun p hp => (⟨p, (Finset.mem_filter.mp hp).2⟩ : Nat.Primes)) ?_ ?_ ?_ ?_
      · intro p hp
        exact Finset.mem_image.mpr
          ⟨⟨p, hp⟩, Finset.mem_attach _ _, rfl⟩
      · intro p1 hp1 p2 hp2 heq
        exact congrArg Subtype.val heq
      · intro q hq
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
        exact ⟨x.val, x.property, rfl⟩
      · intro p hp
        rfl
    have h0u : ∀ q ∈ u, (0 : ℝ) ≤ ∑' n : ℕ, h (((q : ℕ)) ^ n) :=
      fun q _ => tsum_nonneg (fun n => hnn _)
    have h1u : ∀ q ∈ u, (∑' n : ℕ, h (((q : ℕ)) ^ n))
        ≤ Real.exp (∑' e : ℕ, F (q, e)) := by
      intro q _
      obtain ⟨p, hp⟩ := q
      change (∑' n : ℕ, h (p ^ n))
        ≤ Real.exp (∑' e : ℕ, F ((⟨p, hp⟩ : Nat.Primes), e))
      rw [hfactor p hp]
      have hbase := Real.add_one_le_exp
        (∑' e : ℕ, F ((⟨p, hp⟩ : Nat.Primes), e))
      linarith
    have hsum_le : (∑ q ∈ u, ∑' e : ℕ, F (q, e))
        ≤ ∑' q : Nat.Primes × ℕ, F q := by
      have hfin := hS'sum.sum_le_tsum u
        (fun q _ => tsum_nonneg (fun e => hnn _))
      rw [hST] at hfin
      exact hfin
    have hVle : (∏ p ∈ Finset.range (N + 1) with p.Prime, ∑' n : ℕ, h (p ^ n))
        ≤ Real.exp (∑' q : Nat.Primes × ℕ, F q) := by
      calc (∏ p ∈ Finset.range (N + 1) with p.Prime, ∑' n : ℕ, h (p ^ n))
          = ∏ q ∈ u, (∑' n : ℕ, h (((q : ℕ)) ^ n)) := hVtoU
        _ ≤ ∏ q ∈ u, Real.exp (∑' e : ℕ, F (q, e)) :=
            Finset.prod_le_prod₀ h0u h1u
        _ = Real.exp (∑ q ∈ u, ∑' e : ℕ, F (q, e)) :=
            (Real.exp_sum _ _).symm
        _ ≤ Real.exp (∑' q : Nat.Primes × ℕ, F q) :=
            Real.exp_le_exp.mpr hsum_le
    exact hle_range.trans hVle
  refine summable_of_sum_range_le (c := Real.exp (∑' q : Nat.Primes × ℕ, F q)) hnn
    (fun n => ?_)
  rcases n with _ | n
  · rw [Finset.sum_range_zero]
    exact (Real.exp_pos _).le
  · exact hbound n

/-- Local factor identity at a prime: Moebius inversion against the geometric
series. -/
private lemma emv_local_factor (F : ArithmeticFunction ℂ) (p : ℕ)
    (hp : Nat.Prime p)
    (hs : Summable (fun e : ℕ =>
      ‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * F) (p ^ e)‖ /
        ((p : ℝ) ^ e))) :
    Summable (fun e : ℕ => ‖F (p ^ e) / ((p : ℂ) ^ e)‖) ∧
    (∑' e : ℕ, ((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * F)
        (p ^ e) / ((p : ℂ) ^ e))
      = (1 - 1 / ((p : ℂ))) * (∑' e : ℕ, F (p ^ e) / ((p : ℂ) ^ e)) := by
  set g : ArithmeticFunction ℂ :=
    (↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * F with hgdef
  have hident : g * (↑ArithmeticFunction.zeta : ArithmeticFunction ℂ) = F := by
    have e1 : g * (↑ArithmeticFunction.zeta : ArithmeticFunction ℂ)
        = (↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) *
          (F * (↑ArithmeticFunction.zeta : ArithmeticFunction ℂ)) := by
      rw [hgdef, mul_assoc]
    have e2 : F * (↑ArithmeticFunction.zeta : ArithmeticFunction ℂ)
        = (↑ArithmeticFunction.zeta : ArithmeticFunction ℂ) * F :=
      mul_comm _ _
    have e3 : (↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) *
          ((↑ArithmeticFunction.zeta : ArithmeticFunction ℂ) * F)
        = ((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) *
          (↑ArithmeticFunction.zeta : ArithmeticFunction ℂ)) * F :=
      (mul_assoc _ _ _).symm
    rw [e1, e2, e3, ArithmeticFunction.coe_moebius_mul_coe_zeta, one_mul]
  have hdiv : ∀ e : ℕ, F (p ^ e)
      = ∑ j ∈ Finset.range (e + 1), g (p ^ j) := by
    intro e
    have h1 : (g * (↑ArithmeticFunction.zeta : ArithmeticFunction ℂ)) (p ^ e)
        = F (p ^ e) := by rw [hident]
    rw [ArithmeticFunction.coe_mul_zeta_apply] at h1
    rw [← h1, Nat.divisors_prime_pow hp, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro j _
    rfl
  set x : ℂ := 1 / ((p : ℂ)) with hxdef
  have hnormx : ‖x‖ < 1 := by
    rw [hxdef, norm_div, norm_one, Complex.norm_natCast]
    have hp2 : (2 : ℝ) ≤ ((p : ℕ)) := by exact_mod_cast hp.two_le
    have hpos : (0 : ℝ) < ((p : ℕ)) := by linarith
    rw [div_lt_one hpos]
    linarith
  have hxxnorm : ∀ j : ℕ, ‖x ^ j‖ = 1 / ((p : ℝ) ^ j) := by
    intro j
    rw [norm_pow, hxdef, norm_div, norm_one, Complex.norm_natCast, div_pow,
      one_pow]
  have hpt : ∀ j : ℕ, ‖g (p ^ j) * x ^ j‖
      = ‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * F) (p ^ j)‖ /
        ((p : ℝ) ^ j) := by
    intro j
    rw [norm_mul, hxxnorm j, hgdef]
    exact (div_eq_mul_one_div _ _).symm
  have hgx : Summable (fun j : ℕ => ‖g (p ^ j) * x ^ j‖) :=
    hs.congr (fun j => (hpt j).symm)
  have hxx : Summable (fun m : ℕ => ‖x ^ m‖) :=
    (summable_geometric_of_lt_one (norm_nonneg _) hnormx).congr
      (fun m => (norm_pow _ _).symm)
  have hinner : ∀ e : ℕ,
      (∑ k ∈ Finset.range (e + 1), g (p ^ k) * x ^ k * x ^ (e - k))
      = F (p ^ e) * x ^ e := by
    intro e
    rw [hdiv e, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range, Nat.lt_succ_iff] at hj
    have hpow : x ^ j * x ^ (e - j) = x ^ e := by
      rw [← pow_add, Nat.add_sub_cancel' hj]
    rw [mul_assoc, hpow]
  have htsum : (∑' j : ℕ, g (p ^ j) * x ^ j) * (∑' m : ℕ, x ^ m)
      = ∑' e : ℕ, F (p ^ e) * x ^ e := by
    rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hgx hxx]
    apply tsum_congr
    intro e
    exact hinner e
  have hgeo : (∑' m : ℕ, x ^ m) = (1 - x)⁻¹ :=
    tsum_geometric_of_norm_lt_one hnormx
  have hx1 : (1 : ℂ) - x ≠ 0 := by
    intro hcon
    have hx1' : (1 : ℂ) = x := sub_eq_zero.mp hcon
    rw [← hx1', norm_one] at hnormx
    exact lt_irrefl _ hnormx
  have hconv : ∀ (a : ℂ) (e : ℕ), a / ((p : ℂ) ^ e) = a * x ^ e := by
    intro a e
    rw [hxdef, div_pow, one_pow, div_eq_mul_one_div]
  have hmain : (∑' e : ℕ, g (p ^ e) * x ^ e)
      = (1 - x) * (∑' e : ℕ, F (p ^ e) * x ^ e) := by
    have h2 := congrArg ((1 - x) * ·) (hgeo ▸ htsum)
    rw [mul_left_comm, mul_inv_cancel₀ hx1, mul_one] at h2
    exact h2
  have hnormF : Summable (fun e : ℕ => ‖F (p ^ e) * x ^ e‖) := by
    apply (summable_norm_sum_mul_range_of_summable_norm hgx hxx).congr
    intro e
    rw [hinner e]
  have hnormF2 : Summable (fun e : ℕ => ‖F (p ^ e) / ((p : ℂ) ^ e)‖) := by
    apply hnormF.congr
    intro e
    rw [hconv]
  refine ⟨hnormF2, ?_⟩
  have hF2 : (∑' e : ℕ, F (p ^ e) / ((p : ℂ) ^ e))
      = ∑' e : ℕ, F (p ^ e) * x ^ e :=
    tsum_congr (fun e => hconv _ _)
  have hG2 : (∑' e : ℕ, g (p ^ e) / ((p : ℂ) ^ e))
      = ∑' e : ℕ, g (p ^ e) * x ^ e :=
    tsum_congr (fun e => hconv _ _)
  have hxeq : (1 : ℂ) - 1 / ((p : ℂ)) = 1 - x := by rw [hxdef]
  have hG2' : (∑' e : ℕ,
      ((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * F) (p ^ e) /
        ((p : ℂ) ^ e))
      = ∑' e : ℕ, g (p ^ e) * x ^ e := by
    rw [← hG2]
  rw [hG2', hF2, hxeq]
  exact hmain

/-- Product formula for absolutely summable families over `Fin k → ℕ`. -/
private lemma emv_tsum_pi_prod {k : ℕ} (b : Fin k → ℕ → ℂ)
    (hb : ∀ i, Summable (fun e => ‖b i e‖)) :
    Summable (fun ν : Fin k → ℕ => ‖∏ i, b i (ν i)‖) ∧
    (∑' ν : Fin k → ℕ, ∏ i, b i (ν i)) = ∏ i, ∑' e, b i e := by
  induction k with
  | zero =>
    refine ⟨Summable.of_finite, ?_⟩
    have hL : (∑' ν : Fin 0 → ℕ, ∏ i, b i (ν i)) = 1 := by
      rw [tsum_fintype]
      simp
    have hR : (∏ i, ∑' e, b i e) = 1 := Fin.prod_univ_zero _
    rw [hL, hR]
  | succ k ih =>
    obtain ⟨hsumT, htsumT⟩ :=
      ih (fun i e => b (Fin.succ i) e) (fun i => hb (Fin.succ i))
    have htsumT' : (∑' ν : Fin k → ℕ, ∏ i, b (Fin.succ i) (ν i))
        = ∏ i, ∑' e, b (Fin.succ i) e := by
      have h1 : (∑' ν : Fin k → ℕ, ∏ i, b (Fin.succ i) (ν i))
          = ∑' ν : Fin k → ℕ, ∏ i, (fun i e => b (Fin.succ i) e) i (ν i) := by
        apply tsum_congr
        intro ν
        exact Finset.prod_congr rfl (fun i _ => rfl)
      have h2 : (∏ i, ∑' e, b (Fin.succ i) e)
          = ∏ i, ∑' e, (fun i e => b (Fin.succ i) e) i e :=
        Finset.prod_congr rfl (fun i _ => tsum_congr (fun e => rfl))
      rw [h1, h2]
      exact htsumT
    have h0 : ∀ q : ℕ × (Fin k → ℕ),
        (Fin.consEquiv (fun _ : Fin (k + 1) => ℕ)) q 0 = q.1 := by
      intro q
      rw [Fin.consEquiv_apply, Fin.cons_zero]
    have hs : ∀ (q : ℕ × (Fin k → ℕ)) (i : Fin k),
        (Fin.consEquiv (fun _ : Fin (k + 1) => ℕ)) q (Fin.succ i) = q.2 i := by
      intro q i
      rw [Fin.consEquiv_apply, Fin.cons_succ]
    have hprod : ∀ q : ℕ × (Fin k → ℕ),
        (∏ i, b i ((Fin.consEquiv (fun _ : Fin (k + 1) => ℕ)) q i))
          = b 0 q.1 * ∏ i, b (Fin.succ i) (q.2 i) := by
      intro q
      have hY : (∏ i, b (Fin.succ i)
            ((Fin.consEquiv (fun _ : Fin (k + 1) => ℕ)) q (Fin.succ i)))
          = ∏ i, b (Fin.succ i) (q.2 i) :=
        Finset.prod_congr rfl (fun i _ => by rw [hs q i])
      rw [Fin.prod_univ_succ, h0 q, hY]
    have hbase := Summable.mul_norm (hb 0) hsumT
    have hnormprod : Summable (fun q : ℕ × (Fin k → ℕ) =>
        ‖b 0 q.1 * ∏ i, b (Fin.succ i) (q.2 i)‖) := by
      apply hbase.congr
      intro q
      have hqq : (∏ i, (fun i e => b (Fin.succ i) e) i (q.2 i))
          = ∏ i, b (Fin.succ i) (q.2 i) :=
        Finset.prod_congr rfl (fun i _ => rfl)
      rw [hqq]
    have hcomp : Summable ((fun ν : Fin (k + 1) → ℕ => ‖∏ i, b i (ν i)‖) ∘
        (Fin.consEquiv (fun _ : Fin (k + 1) => ℕ))) := by
      apply hnormprod.congr
      intro q
      simp only [Function.comp_apply]
      rw [hprod q]
    have hsum : Summable (fun ν : Fin (k + 1) → ℕ => ‖∏ i, b i (ν i)‖) :=
      (Fin.consEquiv (fun _ : Fin (k + 1) => ℕ)).summable_iff.mp hcomp
    have hmul0 := tsum_mul_tsum_of_summable_norm (hb 0) hsumT
    have hmul : (∑' e0 : ℕ, b 0 e0)
          * (∑' ν : Fin k → ℕ, ∏ i, b (Fin.succ i) (ν i))
        = ∑' q : ℕ × (Fin k → ℕ), b 0 q.1 * ∏ i, b (Fin.succ i) (q.2 i) := by
      have e1 : (∑' ν : Fin k → ℕ, ∏ i, b (Fin.succ i) (ν i))
          = ∑' ν : Fin k → ℕ, ∏ i, (fun i e => b (Fin.succ i) e) i (ν i) := by
        apply tsum_congr
        intro ν
        exact Finset.prod_congr rfl (fun i _ => rfl)
      have e2 : (∑' q : ℕ × (Fin k → ℕ), b 0 q.1 * ∏ i, b (Fin.succ i) (q.2 i))
          = ∑' q : ℕ × (Fin k → ℕ),
            b 0 q.1 * ∏ i, (fun i e => b (Fin.succ i) e) i (q.2 i) := by
        apply tsum_congr
        intro q
        have hqq : (∏ i, b (Fin.succ i) (q.2 i))
            = ∏ i, (fun i e => b (Fin.succ i) e) i (q.2 i) :=
          Finset.prod_congr rfl (fun i _ => rfl)
        rw [hqq]
      rw [e1, e2]
      exact hmul0
    have hback : (∑' q : ℕ × (Fin k → ℕ),
          b 0 q.1 * ∏ i, b (Fin.succ i) (q.2 i))
        = ∑' ν : Fin (k + 1) → ℕ, ∏ i, b i (ν i) := by
      rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => ℕ)).tsum_eq
        (fun ν : Fin (k + 1) → ℕ => ∏ i, b i (ν i))]
      apply tsum_congr
      intro q
      exact (hprod q).symm
    refine ⟨hsum, ?_⟩
    have hR : (∏ i, ∑' e, b i e)
        = (∑' e0 : ℕ, b 0 e0) * ∏ i, ∑' e, b (Fin.succ i) e := by
      rw [Fin.prod_univ_succ]
    rw [hR, ← htsumT', ← hback]
    exact hmul.symm

/-- One-coordinate mean value from `wintner_mean_value`. -/
private lemma emv_mean_tendsto {k : ℕ} (f : (Fin k → ℕ) → ℂ)
    (hmult : ∀ a b : Fin k → ℕ, (∀ i, Nat.Coprime (a i) (b i)) →
      f (fun i => a i * b i) = f a * f b)
    (h1 : f 1 = 1)
    (hsumm : Summable (fun q : { q : { p : ℕ // p.Prime } × (Fin k → ℕ) //
        q.2 ≠ 0 } =>
      ‖(∑ d ∈ Fintype.piFinset (fun i => Nat.divisors ((q.1.1 : ℕ) ^
          (q.1.2 i))),
          (∏ i, ((ArithmeticFunction.moebius (d i) : ℤ) : ℂ)) *
          f (fun i => (q.1.1 : ℕ) ^ (q.1.2 i) / d i)) /
        (((q.1.1 : ℕ) : ℂ) ^ (∑ i, q.1.2 i))‖))
    (i : Fin k) :
    Filter.Tendsto (fun N : ℕ => ((N : ℂ)⁻¹) *
        ∑ m ∈ Finset.Icc 1 N, emvF f i m)
      Filter.atTop (nhds (∑' n : ℕ, emvG f i n / (n : ℂ))) := by
  have hsum := emv_summable_norm_div (emvG f i)
    (emvG_isMultiplicative f i hmult h1)
    (emv_primePow_summable f hmult h1 hsumm i)
  exact MetaMathlibExt.wintner_mean_value (emvF f i) hsum

/-- Slice of the prime-power summability at a fixed prime, in Moebius form. -/
private lemma emv_slice_summable {k : ℕ} (f : (Fin k → ℕ) → ℂ)
    (hmult : ∀ a b : Fin k → ℕ, (∀ i, Nat.Coprime (a i) (b i)) →
      f (fun i => a i * b i) = f a * f b)
    (h1 : f 1 = 1)
    (hsumm : Summable (fun q : { q : { p : ℕ // p.Prime } × (Fin k → ℕ) //
        q.2 ≠ 0 } =>
      ‖(∑ d ∈ Fintype.piFinset (fun i => Nat.divisors ((q.1.1 : ℕ) ^
          (q.1.2 i))),
          (∏ i, ((ArithmeticFunction.moebius (d i) : ℤ) : ℂ)) *
          f (fun i => (q.1.1 : ℕ) ^ (q.1.2 i) / d i)) /
        (((q.1.1 : ℕ) : ℂ) ^ (∑ i, q.1.2 i))‖))
    (i : Fin k) (p : Nat.Primes) : Summable (fun e : ℕ =>
      ‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * emvF f i)
        ((((p : ℕ))) ^ e)‖ / (((((p : ℕ))) : ℝ) ^ e)) := by
  have hprime := emv_primePow_summable f hmult h1 hsumm i
  set Fp : Nat.Primes × ℕ → ℝ := fun q =>
    ‖emvG f i ((((q.1 : ℕ))) ^ (q.2 + 1))‖ / (((((q.1 : ℕ))) : ℝ) ^ (q.2 + 1)) with hFpdef
  have hinj : Function.Injective (fun e : ℕ => (p, e)) := by
    intro a b hab
    exact congrArg Prod.snd hab
  have hs0 : Summable (fun e : ℕ => Fp (p, e)) :=
    hprime.comp_injective hinj
  have hs0e : Summable (fun e : ℕ => ‖emvG f i ((((p : ℕ))) ^ (e + 1))‖ /
      (((((p : ℕ))) : ℝ) ^ (e + 1))) := by
    apply hs0.congr
    intro e
    rfl
  have hs1 : Summable (fun e : ℕ => ‖emvG f i ((((p : ℕ))) ^ e)‖ /
      (((((p : ℕ))) : ℝ) ^ e)) :=
    (summable_nat_add_iff (f := fun e => ‖emvG f i ((((p : ℕ))) ^ e)‖ /
      (((((p : ℕ))) : ℝ) ^ e)) 1).mp hs0e
  exact hs1

/-- Euler product for one coordinate, with the local factor from
`emv_local_factor`. -/
private lemma emv_euler_hasProd {k : ℕ} (f : (Fin k → ℕ) → ℂ)
    (hmult : ∀ a b : Fin k → ℕ, (∀ i, Nat.Coprime (a i) (b i)) →
      f (fun i => a i * b i) = f a * f b)
    (h1 : f 1 = 1)
    (hsumm : Summable (fun q : { q : { p : ℕ // p.Prime } × (Fin k → ℕ) //
        q.2 ≠ 0 } =>
      ‖(∑ d ∈ Fintype.piFinset (fun i => Nat.divisors ((q.1.1 : ℕ) ^
          (q.1.2 i))),
          (∏ i, ((ArithmeticFunction.moebius (d i) : ℤ) : ℂ)) *
          f (fun i => (q.1.1 : ℕ) ^ (q.1.2 i) / d i)) /
        (((q.1.1 : ℕ) : ℂ) ^ (∑ i, q.1.2 i))‖))
    (i : Fin k) :
    HasProd (fun p : Nat.Primes =>
        (1 - 1 / ((((p : ℕ))) : ℂ)) *
          ∑' e : ℕ, emvF f i ((((p : ℕ))) ^ e) / ((((p : ℕ))) : ℂ) ^ e)
      (∑' n : ℕ, emvG f i n / ((n : ℕ) : ℂ)) := by
  have hprime := emv_primePow_summable f hmult h1 hsumm i
  have hmulG := emvG_isMultiplicative f i hmult h1
  have ha1 : (fun n => emvG f i n / ((n : ℕ) : ℂ)) 1 = 1 := by
    change emvG f i 1 / (((1 : ℕ)) : ℂ) = 1
    rw [hmulG.1, Nat.cast_one, div_one]
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n →
      (fun n => emvG f i n / ((n : ℕ) : ℂ)) (m * n)
        = (fun n => emvG f i n / ((n : ℕ) : ℂ)) m *
          (fun n => emvG f i n / ((n : ℕ) : ℂ)) n := by
    intro m n hcop
    change emvG f i (m * n) / ((((m * n : ℕ))) : ℂ)
      = (emvG f i m / ((m : ℕ) : ℂ)) * (emvG f i n / ((n : ℕ) : ℂ))
    rw [hmulG.2 hcop, Nat.cast_mul, ← div_mul_div_comm]
  have hnorm := emv_summable_norm_div (emvG f i) hmulG hprime
  have hsum : Summable (fun n => ‖(fun n => emvG f i n / ((n : ℕ) : ℂ)) n‖) := by
    apply hnorm.congr
    intro n
    show ‖emvG f i n‖ / ((n : ℕ) : ℝ)
      = ‖(fun n => emvG f i n / ((n : ℕ) : ℂ)) n‖
    rw [norm_div, Complex.norm_natCast]
  have ha0 : (fun n => emvG f i n / ((n : ℕ) : ℂ)) 0 = 0 := by
    change emvG f i 0 / (((0 : ℕ)) : ℂ) = 0
    rw [ArithmeticFunction.map_zero, Nat.cast_zero, div_zero]
  have hEP := EulerProduct.eulerProduct_hasProd
    (f := fun n => emvG f i n / ((n : ℕ) : ℂ)) ha1 hmul hsum ha0
  have hslice : ∀ p : Nat.Primes, Summable (fun e : ℕ =>
      ‖((↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * emvF f i)
        ((((p : ℕ))) ^ e)‖ / (((((p : ℕ))) : ℝ) ^ e)) :=
    fun p => emv_slice_summable f hmult h1 hsumm i p
  have hfactor : ∀ p : Nat.Primes,
      (∑' e : ℕ, (fun n => emvG f i n / ((n : ℕ) : ℂ)) ((((p : ℕ))) ^ e))
        = (1 - 1 / ((((p : ℕ))) : ℂ)) *
          ∑' e : ℕ, emvF f i ((((p : ℕ))) ^ e) / ((((p : ℕ))) : ℂ) ^ e := by
    intro p
    have hN82 := (emv_local_factor (emvF f i) (((p : ℕ))) p.property
      (hslice p)).2
    have he : (∑' e : ℕ,
          (fun n => emvG f i n / ((n : ℕ) : ℂ)) ((((p : ℕ))) ^ e))
        = ∑' e : ℕ, emvG f i ((((p : ℕ))) ^ e) / ((((p : ℕ))) : ℂ) ^ e := by
      apply tsum_congr
      intro e
      change emvG f i ((((p : ℕ))) ^ e) / ((((((p : ℕ))) ^ e : ℕ)) : ℂ)
        = emvG f i ((((p : ℕ))) ^ e) / ((((p : ℕ))) : ℂ) ^ e
      rw [Nat.cast_pow]
    rw [he]
    exact hN82
  have hval : (∑' n : ℕ, (fun n => emvG f i n / ((n : ℕ) : ℂ)) n)
      = ∑' n : ℕ, emvG f i n / ((n : ℕ) : ℂ) :=
    tsum_congr (fun n => rfl)
  rw [hval] at hEP
  exact hEP.congr_fun (fun p => (hfactor p).symm)

/-- The cube average factors as a product of one-coordinate averages. -/
private lemma emv_cube_mean_eq {k : ℕ} (f : (Fin k → ℕ) → ℂ)
    (hmult : ∀ a b : Fin k → ℕ, (∀ i, Nat.Coprime (a i) (b i)) →
      f (fun i => a i * b i) = f a * f b)
    (h1 : f 1 = 1) (N : ℕ) :
    (∑ n ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 N), f n) /
        ((N : ℂ) ^ k)
      = ∏ i, ((N : ℂ)⁻¹ * ∑ m ∈ Finset.Icc 1 N, emvF f i m) := by
  have hfn : ∀ n ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 N),
      f n = ∏ i, emvF f i (n i) := by
    intro n hn
    apply emv_prod_decomp_apply f hmult h1
    intro j
    have hj := Fintype.mem_piFinset.mp hn j
    simp only [Finset.mem_Icc] at hj
    obtain ⟨hlo, -⟩ := hj
    omega
  have hNk : ((N : ℂ) ^ k) = ∏ _i : Fin k, (N : ℂ) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.sum_congr rfl (fun n hn => hfn n hn), ← Finset.prod_univ_sum, hNk]
  simp only [← div_eq_inv_mul, Finset.prod_div_distrib]

/--
**Euler product for mean values of coordinatewise multiplicative functions.** Let $k$ be a natural
number, write $\mathbb{N} = \{0, 1, 2, \dots\}$, and let $f \colon \mathbb{N}^k \to \mathbb{C}$
satisfy $f(a_1 b_1, \dots, a_k b_k) = f(a) f(b)$ for all $a, b \in \mathbb{N}^k$ with
$\gcd(a_i, b_i) = 1$ for every $i$. For a prime $p$ and $\nu = (\nu_1, \dots, \nu_k) \in
\mathbb{N}^k$ write $p^\nu = (p^{\nu_1}, \dots, p^{\nu_k})$, $|\nu| = \nu_1 + \dots + \nu_k$ and
$$
(\mu * f)(p^\nu) = \sum_{d_1 \mid p^{\nu_1}, \dots, d_k \mid p^{\nu_k}}
\mu(d_1) \cdots \mu(d_k) \, f(p^{\nu_1} / d_1, \dots, p^{\nu_k} / d_k),
$$
where $\mu$ is the Möbius function and each $d_i$ runs over the positive divisors of $p^{\nu_i}$.
Suppose that the family $|(\mu * f)(p^\nu)| / p^{|\nu|}$, indexed by the pairs $(p, \nu)$ of a
prime $p$ and a nonzero $\nu \in \mathbb{N}^k$, is summable. Then there is a complex number $M$
such that
$$
\frac{1}{N^k} \sum_{n \in \{1, \dots, N\}^k} f(n) \to M \quad (N \to \infty)
$$
and
$$
M = \prod_p \Bigl(1 - \frac{1}{p}\Bigr)^k \sum_{\nu \in \mathbb{N}^k} \frac{f(p^\nu)}{p^{|\nu|}},
$$
where the product runs over all primes and the product and the inner sums are unconditional (an
unconditional sum that does not converge is read as $0$, a product as $1$).

This is the Wintner–Ushiroya theorem (Ushiroya, Theorem 4; Tóth, Proposition 19) under a
stronger multiplicativity hypothesis: the source asks for $f(a_1 b_1, \dots, a_k b_k) = f(a) f(b)$
only when $\gcd(a_1 \cdots a_k, b_1 \cdots b_k) = 1$. The hypothesis used here forces $f$ to be a
product of one-variable multiplicative functions of the coordinates, and the proof reduces to the
one-variable Wintner theorem in each coordinate. The averages over the cubes $\{1, \dots, N\}^k$
are the diagonal of the source's multi-parameter limit, so they converge to the same value.

Source: László Tóth,
"On the Asymptotic Density of k-tuples of Positive Integers with Pairwise
Non-Coprime Components,"
Journal of Integer Sequences 27 (2024), Article 24.8.5,
Theorem (unlabeled; multiplicative-function form following label
Th_Wintner_gen), equation (label Euler_product), lines 314–326,
https://cs.uwaterloo.ca/journals/JIS/VOL27/Toth/toth27.tex
-/
public theorem euler_product_mean_value
    {k : ℕ} (f : (Fin k → ℕ) → ℂ)
    (hmult : ∀ a b : Fin k → ℕ, (∀ i, Nat.Coprime (a i) (b i)) →
      f (fun i => a i * b i) = f a * f b)
    (hsumm : Summable (fun q : { q : { p : ℕ // p.Prime } × (Fin k → ℕ) // q.2 ≠ 0 } =>
      ‖(∑ d ∈ Fintype.piFinset (fun i => Nat.divisors ((q.1.1 : ℕ) ^ (q.1.2 i))),
          (∏ i, ((ArithmeticFunction.moebius (d i) : ℤ) : ℂ)) *
          f (fun i => (q.1.1 : ℕ) ^ (q.1.2 i) / d i)) /
        (((q.1.1 : ℕ) : ℂ) ^ (∑ i, q.1.2 i))‖)) :
    ∃ M : ℂ, Filter.Tendsto (fun N : ℕ =>
      (∑ n ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 N), f n) / ((N : ℂ) ^ k))
      Filter.atTop (nhds M) ∧
      M = ∏' (p : { p : ℕ // p.Prime }),
        ((1 - 1 / ((p : ℕ) : ℂ)) ^ k *
        (∑' (ν : Fin k → ℕ),
          f (fun i => (p : ℕ) ^ (ν i)) / (((p : ℕ) : ℂ) ^ (∑ i, ν i)))) := by
  rcases emv_f_one f hmult with h10 | h11
  · refine ⟨0, ?_, ?_⟩
    · have havg : (fun N : ℕ =>
          (∑ n ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 N), f n) /
            ((N : ℂ) ^ k)) = fun _ => (0 : ℂ) := by
        funext N
        rw [Finset.sum_congr rfl
          (fun n _ => emv_f_zero_of_one_zero f hmult h10 n)]
        simp
      rw [havg]
      exact tendsto_const_nhds
    · have hfac : ∀ p : { p : ℕ // p.Prime },
          ((1 - 1 / ((p : ℕ) : ℂ)) ^ k *
            (∑' (ν : Fin k → ℕ),
              f (fun i => (p : ℕ) ^ (ν i)) / (((p : ℕ) : ℂ) ^ (∑ i, ν i)))) = 0 := by
        intro p
        have hz : (fun ν : Fin k → ℕ => f (fun i => (p : ℕ) ^ (ν i)) /
            (((p : ℕ) : ℂ) ^ (∑ i, ν i))) = fun _ => 0 :=
          funext (fun ν => by
            rw [emv_f_zero_of_one_zero f hmult h10, zero_div])
        rw [hz, tsum_zero, mul_zero]
      exact (tprod_of_exists_eq_zero ⟨⟨2, Nat.prime_two⟩, hfac _⟩).symm
  · refine ⟨∏ i, ∑' n : ℕ, emvG f i n / ((n : ℕ) : ℂ), ?_, ?_⟩
    · have hlim : ∀ i : Fin k, Filter.Tendsto
          (fun N : ℕ => ((N : ℂ)⁻¹) * ∑ m ∈ Finset.Icc 1 N, emvF f i m)
          Filter.atTop (nhds (∑' n : ℕ, emvG f i n / ((n : ℕ) : ℂ))) :=
        fun i => emv_mean_tendsto f hmult h11 hsumm i
      have hprod := tendsto_finsetProd Finset.univ (fun i _ => hlim i)
      exact hprod.congr' (Filter.Eventually.of_forall
        (fun N => (emv_cube_mean_eq f hmult h11 N).symm))
    · have hHP : ∀ i ∈ (Finset.univ : Finset (Fin k)), HasProd
          (fun p : Nat.Primes => (1 - 1 / ((((p : ℕ))) : ℂ)) *
            ∑' e : ℕ, emvF f i ((((p : ℕ))) ^ e) / ((((p : ℕ))) : ℂ) ^ e)
          (∑' n : ℕ, emvG f i n / ((n : ℕ) : ℂ)) :=
        fun i _ => emv_euler_hasProd f hmult h11 hsumm i
      have hBIG := hasProd_prod hHP
      have hlocal : ∀ p : Nat.Primes,
          (∏ i ∈ (Finset.univ : Finset (Fin k)),
            ((1 - 1 / ((((p : ℕ))) : ℂ)) *
              ∑' e : ℕ, emvF f i ((((p : ℕ))) ^ e) / ((((p : ℕ))) : ℂ) ^ e))
          = ((1 - 1 / (((p : ℕ)) : ℂ)) ^ k *
            (∑' (ν : Fin k → ℕ),
              f (fun i => ((p : ℕ)) ^ (ν i)) / ((((p : ℕ)) : ℂ) ^ (∑ i, ν i)))) := by
        intro p
        have h1p : (∏ i ∈ (Finset.univ : Finset (Fin k)),
              ((1 - 1 / ((((p : ℕ))) : ℂ)) *
                ∑' e : ℕ, emvF f i ((((p : ℕ))) ^ e) / ((((p : ℕ))) : ℂ) ^ e))
            = (1 - 1 / ((((p : ℕ))) : ℂ)) ^ k *
              ∏ i ∈ (Finset.univ : Finset (Fin k)),
                (∑' e : ℕ, emvF f i ((((p : ℕ))) ^ e) / ((((p : ℕ))) : ℂ) ^ e) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin]
        have hnorm1 : ∀ i : Fin k, Summable (fun e : ℕ =>
            ‖emvF f i ((((p : ℕ))) ^ e) / ((((p : ℕ))) : ℂ) ^ e‖) :=
          fun i => (emv_local_factor (emvF f i) (((p : ℕ))) p.property
            (emv_slice_summable f hmult h11 hsumm i p)).1
        have hN9 := (emv_tsum_pi_prod (fun i e => emvF f i ((((p : ℕ))) ^ e) /
            ((((p : ℕ))) : ℂ) ^ e) hnorm1).2
        have hX : (∏ i ∈ (Finset.univ : Finset (Fin k)),
              (∑' e : ℕ, emvF f i ((((p : ℕ))) ^ e) / ((((p : ℕ))) : ℂ) ^ e))
            = ∑' (ν : Fin k → ℕ),
              f (fun i => ((p : ℕ)) ^ (ν i)) / ((((p : ℕ)) : ℂ) ^ (∑ i, ν i)) := by
          have hstep : (∏ i ∈ (Finset.univ : Finset (Fin k)),
                (∑' e : ℕ, emvF f i ((((p : ℕ))) ^ e) / ((((p : ℕ))) : ℂ) ^ e))
              = ∑' (ν : Fin k → ℕ), ∏ i,
                (emvF f i ((((p : ℕ))) ^ (ν i)) / ((((p : ℕ))) : ℂ) ^ (ν i)) :=
            hN9.symm
          rw [hstep]
          apply tsum_congr
          intro ν
          have hne : ∀ i : Fin k, ((((p : ℕ))) ^ (ν i)) ≠ 0 :=
            fun i => pow_ne_zero _ (ne_of_gt p.property.pos)
          have hdecomp : f (fun i => ((((p : ℕ))) ^ (ν i)))
              = ∏ i, emvF f i ((((p : ℕ))) ^ (ν i)) :=
            emv_prod_decomp_apply f hmult h11 hne
          rw [hdecomp, Finset.prod_div_distrib]
          congr 1
          exact Finset.prod_pow_eq_pow_sum _ _ _
        rw [h1p, hX]
      have hBIG2 : HasProd (fun p : Nat.Primes =>
          ((1 - 1 / (((p : ℕ)) : ℂ)) ^ k *
            (∑' (ν : Fin k → ℕ),
              f (fun i => ((p : ℕ)) ^ (ν i)) / ((((p : ℕ)) : ℂ) ^ (∑ i, ν i)))))
          (∏ i ∈ (Finset.univ : Finset (Fin k)),
            (∑' n : ℕ, emvG f i n / ((n : ℕ) : ℂ))) :=
        hBIG.congr_fun (fun p => (hlocal p).symm)
      exact (HasProd.tprod_eq hBIG2).symm

end MetaMathlibExt
