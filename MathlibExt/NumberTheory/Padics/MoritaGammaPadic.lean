/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.MoritaGamma
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.ContinuousMap.Basic
import MathlibExt.NumberTheory.WilsonPrimePow
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Morita's p-adic gamma function on `ℤ_[p]`

For every prime `p`, the finite values `moritaGammaNat p n = (-1) ^ n ∏_{k < n, p ∤ k} k` extend
to a unique continuous function `moritaGamma p : ℤ_[p] → ℤ_[p]`. For odd `p` the needed
congruences come from Gauss's generalisation of Wilson's theorem modulo `p ^ s`; for `p = 2` they
come from its analogue modulo `2 ^ s`, `s ≥ 3`.

## Main definitions

* `MetaMathlibExt.moritaGamma`: Morita's `p`-adic gamma function, as a continuous map
  `ℤ_[p] → ℤ_[p]`.

## Main statements

* `PadicInt.existsUnique_continuous_natCast_eq`: a sequence `ℕ → ℤ_[p]` that is uniformly
  continuous for the `p`-adic topology on `ℕ` extends uniquely to a continuous function on
  `ℤ_[p]`.
* `MetaMathlibExt.norm_moritaGammaNat_sub_le`: `n ≡ m (mod p ^ s)` implies
  `Γ_p(n) ≡ Γ_p(m) (mod p ^ s)`, for `p` odd or `s ≥ 3`.
* `MetaMathlibExt.isMoritaPadicGamma_moritaGamma` and
  `MetaMathlibExt.IsMoritaPadicGamma.eq_moritaGamma`: `moritaGamma p` is the unique continuous,
  unit-valued extension of the finite values, for every prime `p` (including `p = 2`);
  `MetaMathlibExt.existsUnique_isMoritaPadicGamma` packages this as `∃!`.
* `MetaMathlibExt.moritaGamma_add_one`: the functional equation
  `Γ_p(x + 1) = h_p(x) Γ_p(x)`, where `h_p(x) = -x` if `x` is a unit and `-1` otherwise.
* `MetaMathlibExt.moritaGamma_neg_natCast_mul_moritaGamma_natCast_add_one`:
  `Γ_p(-n) Γ_p(n + 1) = (-1) ^ (⌊n / p⌋ + n + 1)`.
* `MetaMathlibExt.moritaGamma_mul_moritaGamma_one_sub`: the reflection formula
  `Γ_p(x) Γ_p(1 - x) = (-1) ^ ℓ(x)` for odd `p`, where `ℓ(x) ∈ {1, …, p}` is congruent to `x`
  modulo `p`.
* `MetaMathlibExt.moritaGamma_sq_of_two_mul_eq_one`: `Γ_p(1/2) ^ 2` is `1` if `p ≡ 3 (mod 4)`
  and `-1` if `p ≡ 1 (mod 4)`.
-/

@[expose] public section

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- Naturals that are `p`-adically closer than `p ^ (1 - N)` are congruent modulo `p ^ N`. -/
private lemma natCast_modEq_of_norm_sub_lt {k k' N : ℕ}
    (h : ‖(k : ℤ_[p]) - k'‖ < (p : ℝ) ^ (-(N : ℤ) + 1)) : k ≡ k' [MOD p ^ N] := by
  rw [← PadicInt.norm_le_pow_iff_norm_lt_pow_add_one] at h
  have hcast : (k : ℤ_[p]) - k' = (((k : ℤ) - k' : ℤ) : ℤ_[p]) := by push_cast; ring
  rw [hcast, PadicInt.norm_int_le_pow_iff_dvd] at h
  rw [Nat.modEq_iff_dvd]
  have := h.neg_right
  push_cast at this ⊢
  simpa using this

/-- **Interpolation criterion.** If `a : ℕ → ℤ_[p]` satisfies: for every `m` there is `N` such
that `k ≡ k' (mod p ^ N)` implies `a k ≡ a k' (mod p ^ m)`, then there is a unique continuous
`f : ℤ_[p] → ℤ_[p]` with `f k = a k` for every natural number `k`. -/
theorem existsUnique_continuous_natCast_eq (a : ℕ → ℤ_[p])
    (ha : ∀ m : ℕ, ∃ N : ℕ, ∀ k k' : ℕ, k ≡ k' [MOD p ^ N] →
      ‖a k - a k'‖ ≤ (p : ℝ) ^ (-(m : ℤ))) :
    ∃! f : C(ℤ_[p], ℤ_[p]), ∀ k : ℕ, f k = a k := by
  set S : Set ℤ_[p] := Set.range (Nat.cast : ℕ → ℤ_[p])
  have hS : Dense S := PadicInt.denseRange_natCast
  let g : S → ℤ_[p] := fun s => a (Classical.choose s.2)
  have hg : ∀ k : ℕ, g ⟨k, k, rfl⟩ = a k := fun k => by
    have := Classical.choose_spec (⟨k, rfl⟩ : (k : ℤ_[p]) ∈ S)
    simp only [g]
    congr 1
    exact Nat.cast_injective this
  have hgS : ∀ s : S, ∃ k : ℕ, s = ⟨k, k, rfl⟩ := fun ⟨_, k, rfl⟩ => ⟨k, rfl⟩
  have hgu : UniformContinuous g := by
    rw [Metric.uniformContinuous_iff]
    intro ε hε
    obtain ⟨m, hm⟩ := PadicInt.exists_pow_neg_lt p hε
    obtain ⟨N, hN⟩ := ha m
    refine ⟨(p : ℝ) ^ (-(N : ℤ) + 1),
      zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _, fun {s t} hst => ?_⟩
    obtain ⟨k, rfl⟩ := hgS s
    obtain ⟨k', rfl⟩ := hgS t
    rw [hg, hg, dist_eq_norm]
    rw [Subtype.dist_eq, dist_eq_norm] at hst
    exact (hN k k' (natCast_modEq_of_norm_sub_lt hst)).trans_lt hm
  have hui : IsUniformInducing (Subtype.val : S → ℤ_[p]) := isUniformInducing_val S
  have hext := uniformContinuous_uniformly_extend hui hS.denseRange_val hgu
  refine ⟨⟨hS.extend g, hext.continuous⟩, fun k => ?_, ?_⟩
  · rw [← hg k]
    exact hS.extend_eq hgu.continuous ⟨k, k, rfl⟩
  · rintro f hfk
    refine ContinuousMap.ext fun x => ?_
    refine congrFun (Continuous.ext_on hS f.continuous hext.continuous ?_) x
    rintro _ ⟨k, rfl⟩
    rw [hfk k, ← hg k]
    exact (hS.extend_eq hgu.continuous ⟨k, k, rfl⟩).symm

end PadicInt

namespace MetaMathlibExt

open PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- The finite gamma values reduced modulo `p ^ s`. -/
theorem toZModPow_moritaGammaNat (s n : ℕ) :
    toZModPow s (moritaGammaNat p n) =
      (-1) ^ n * ∏ k ∈ (Finset.range n).filter (fun k => ¬ p ∣ k), (k : ZMod (p ^ s)) := by
  simp [moritaGammaNat, map_prod]

/-- The integers prime to `p` in a block of `p ^ s` consecutive integers, together with the sign
`(-1) ^ (p ^ s)`, multiply to `1` modulo `p ^ s`, for `p` odd and `s ≥ 1` or `p = 2` and
`s ≥ 3`. -/
private lemma neg_one_pow_mul_prod_block (s n : ℕ) (hps : (p ≠ 2 ∧ 0 < s) ∨ (p = 2 ∧ 3 ≤ s)) :
    (-1 : ZMod (p ^ s)) ^ (p ^ s) *
      ∏ j ∈ Finset.range (p ^ s), (if ¬ p ∣ n + j then ((n + j : ℕ) : ZMod (p ^ s)) else 1) =
        1 := by
  have hs : 0 < s := by omega
  rw [← Finset.prod_filter, ZMod.prod_range_filter_not_dvd_add_eq_prod_units p n s hs]
  rcases hps with ⟨hp2, -⟩ | ⟨rfl, hs3⟩
  · obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    rw [ZMod.prod_units_prime_pow_eq_neg_one p t hp2,
      ((Nat.Prime.odd_of_ne_two Fact.out hp2).pow).neg_one_pow]
    ring
  · obtain ⟨t, rfl⟩ : ∃ t, s = t + 3 := ⟨s - 3, by omega⟩
    rw [← Units.coe_prod, ZMod.prod_units_two_pow_eq_one t, Units.val_one,
      (even_two.pow_of_ne_zero (by omega)).neg_one_pow, one_mul]

/-- `Γ_p(n + p ^ s) ≡ Γ_p(n) (mod p ^ s)`, for `p` odd or `s ≥ 3`. -/
theorem toZModPow_moritaGammaNat_add_prime_pow {s : ℕ} (hps : p ≠ 2 ∨ 3 ≤ s) (n : ℕ) :
    toZModPow s (moritaGammaNat p (n + p ^ s)) = toZModPow s (moritaGammaNat p n) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · have : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  have hblock := neg_one_pow_mul_prod_block s n (by
    rcases hps with h | h
    · exact Or.inl ⟨h, hs⟩
    · by_cases hp : p = 2
      · exact Or.inr ⟨hp, h⟩
      · exact Or.inl ⟨hp, hs⟩)
  rw [toZModPow_moritaGammaNat, toZModPow_moritaGammaNat, Finset.prod_filter, Finset.prod_filter,
    Finset.prod_range_add, pow_add]
  linear_combination ((-1 : ZMod (p ^ s)) ^ n * ∏ x ∈ Finset.range n,
    if ¬ p ∣ x then (x : ZMod (p ^ s)) else 1) * hblock

/-- `Γ_p(n + t p ^ s) ≡ Γ_p(n) (mod p ^ s)`, for `p` odd or `s ≥ 3`. -/
theorem toZModPow_moritaGammaNat_add_mul_prime_pow {s : ℕ} (hps : p ≠ 2 ∨ 3 ≤ s) (n t : ℕ) :
    toZModPow s (moritaGammaNat p (n + t * p ^ s)) = toZModPow s (moritaGammaNat p n) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show n + (t + 1) * p ^ s = n + t * p ^ s + p ^ s by ring,
      toZModPow_moritaGammaNat_add_prime_pow hps, ih]

/-- Morita's finite gamma values are `p`-adically continuous: `m ≡ n (mod p ^ s)` implies
`Γ_p(m) ≡ Γ_p(n) (mod p ^ s)`, for `p` odd or `s ≥ 3`. -/
theorem norm_moritaGammaNat_sub_le {s : ℕ} (hps : p ≠ 2 ∨ 3 ≤ s) {m n : ℕ}
    (h : m ≡ n [MOD p ^ s]) :
    ‖moritaGammaNat p m - moritaGammaNat p n‖ ≤ (p : ℝ) ^ (-(s : ℤ)) := by
  wlog hmn : m ≤ n generalizing m n
  · rw [norm_sub_rev]
    exact this h.symm (by omega)
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hmn).mp h
  have hn : n = m + t * p ^ s := by rw [mul_comm]; omega
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    sub_eq_zero, hn, toZModPow_moritaGammaNat_add_mul_prime_pow hps]

/-- The finite gamma values extend uniquely to a continuous function on `ℤ_[p]`, for every
prime `p`. -/
theorem existsUnique_continuous_moritaGammaNat (p : ℕ) [Fact p.Prime] :
    ∃! f : C(ℤ_[p], ℤ_[p]), ∀ n : ℕ, f n = moritaGammaNat p n := by
  refine PadicInt.existsUnique_continuous_natCast_eq _ fun m => ⟨m + 3, fun k k' h => ?_⟩
  refine (norm_moritaGammaNat_sub_le (Or.inr (by omega)) h).trans ?_
  exact zpow_le_zpow_right₀ (by exact_mod_cast (Fact.out : p.Prime).one_le) (by omega)

/-- **Morita's `p`-adic gamma function** `Γ_p : ℤ_[p] → ℤ_[p]`: the unique continuous function
with `Γ_p(n) = (-1) ^ n ∏_{k < n, p ∤ k} k` for every natural number `n`. -/
noncomputable def moritaGamma (p : ℕ) [Fact p.Prime] : C(ℤ_[p], ℤ_[p]) :=
  (existsUnique_continuous_moritaGammaNat p).exists.choose

@[simp]
theorem moritaGamma_natCast (n : ℕ) : moritaGamma p n = moritaGammaNat p n :=
  (existsUnique_continuous_moritaGammaNat p).exists.choose_spec n

@[simp]
theorem moritaGamma_ofNat (n : ℕ) [n.AtLeastTwo] :
    moritaGamma p ofNat(n) = moritaGammaNat p ofNat(n) :=
  moritaGamma_natCast n

@[simp]
theorem moritaGamma_zero : moritaGamma p 0 = 1 := by
  simpa using moritaGamma_natCast (p := p) 0

@[simp]
theorem moritaGamma_one : moritaGamma p 1 = -1 := by
  have := moritaGamma_natCast (p := p) 1
  rw [Nat.cast_one] at this
  rw [this]
  simp [moritaGammaNat, Finset.filter_singleton]

/-- Every finite Morita gamma value is a `p`-adic unit. -/
theorem norm_moritaGammaNat (n : ℕ) : ‖moritaGammaNat p n‖ = 1 := by
  rw [moritaGammaNat, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_prod]
  refine Finset.prod_eq_one fun k hk => ?_
  rw [PadicInt.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr (Finset.mem_filter.mp hk).2

/-- `Γ_p` takes values in the `p`-adic units. -/
theorem norm_moritaGamma (x : ℤ_[p]) : ‖moritaGamma p x‖ = 1 := by
  have heq : (fun x : ℤ_[p] => ‖moritaGamma p x‖) = fun _ => 1 := by
    refine Continuous.ext_on PadicInt.denseRange_natCast (moritaGamma p).continuous.norm
      continuous_const ?_
    rintro _ ⟨n, rfl⟩
    simp [norm_moritaGammaNat]
  exact congrFun heq x

theorem isUnit_moritaGamma (x : ℤ_[p]) : IsUnit (moritaGamma p x) :=
  PadicInt.isUnit_iff.mpr (norm_moritaGamma x)

/-- `moritaGamma p` is a continuous, unit-valued extension of Morita's finite gamma values, for
every prime `p`. -/
theorem isMoritaPadicGamma_moritaGamma (p : ℕ) [Fact p.Prime] :
    IsMoritaPadicGamma p (moritaGamma p) :=
  ⟨moritaGamma_zero, fun n _ => moritaGamma_natCast n, isUnit_moritaGamma⟩

/-- Any continuous extension of Morita's finite gamma values is `moritaGamma p`. -/
theorem IsMoritaPadicGamma.eq_moritaGamma {Γ : C(ℤ_[p], ℤ_[p])}
    (hΓ : IsMoritaPadicGamma p Γ) : Γ = moritaGamma p := by
  refine (existsUnique_continuous_moritaGammaNat p).unique (fun n => ?_) moritaGamma_natCast
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using hΓ.zero_eq
  · exact hΓ.natCast_eq hn

/-- For every prime `p` (including `p = 2`), Morita's finite gamma values have a unique
continuous, unit-valued extension to `ℤ_[p]`.

Source: Y. Morita, "A p-adic analogue of the Γ-function", J. Fac. Sci. Univ. Tokyo Sect. IA
Math. 22 (1975), 255–266. The definition and extension theorem are reproduced in
arXiv:2307.08940, arXiv:2307.10000, arXiv:2307.11982, arXiv:2310.15207, and arXiv:2311.03259.

Proves `Wanted` entry `existsUnique_moritaPadicGamma` (stated there for odd primes). -/
theorem existsUnique_isMoritaPadicGamma (p : ℕ) [Fact p.Prime] :
    ∃! Γ : C(ℤ_[p], ℤ_[p]), IsMoritaPadicGamma p Γ :=
  ⟨moritaGamma p, isMoritaPadicGamma_moritaGamma p, fun _ hΓ => hΓ.eq_moritaGamma⟩

/-- The odd-prime case of `existsUnique_isMoritaPadicGamma`. -/
@[deprecated existsUnique_isMoritaPadicGamma +typeChanged (since := "2026-10-29")]
theorem existsUnique_moritaPadicGamma (p : ℕ) [Fact p.Prime] (_hp : p ≠ 2) :
    ∃! Γ : C(ℤ_[p], ℤ_[p]), IsMoritaPadicGamma p Γ :=
  existsUnique_isMoritaPadicGamma p

/-- The recursion for the finite values: `Γ_p(n + 1) = -n Γ_p(n)` if `p ∤ n`, and
`Γ_p(n + 1) = -Γ_p(n)` if `p ∣ n`. -/
theorem moritaGammaNat_succ (n : ℕ) :
    moritaGammaNat p (n + 1) =
      (if p ∣ n then -1 else -(n : ℤ_[p])) * moritaGammaNat p n := by
  unfold moritaGammaNat
  rw [Finset.range_add_one, Finset.filter_insert]
  have hn : n ∉ (Finset.range n).filter (fun j => ¬ p ∣ j) := by simp
  by_cases h : p ∣ n
  · rw [ite_eq_right (not_not.mpr h), ite_eq_left h]
    ring
  · rw [ite_eq_left h, ite_eq_right h, Finset.prod_insert hn]
    ring

/-- The factor `h_p(x)` in the functional equation is continuous. -/
private lemma continuous_moritaGamma_factor :
    Continuous fun x : ℤ_[p] => if ‖x‖ = 1 then -x else -1 := by
  have hs : IsClopen {x : ℤ_[p] | ‖x‖ = 1} := by
    have := IsUltrametricDist.isClopen_sphere (0 : ℤ_[p]) (r := 1) one_ne_zero
    simpa [Metric.sphere] using this
  have : (fun x : ℤ_[p] => if ‖x‖ = 1 then -x else -1) =
      fun x => if x ∈ {x : ℤ_[p] | ‖x‖ = 1} then -x else -1 := rfl
  rw [this]
  apply Continuous.if
  · intro a ha; simp [hs.frontier_eq] at ha
  · fun_prop
  · fun_prop

/-- **Functional equation of `Γ_p`**: `Γ_p(x + 1) = h_p(x) Γ_p(x)`, where `h_p(x) = -x` if
`‖x‖ = 1` and `h_p(x) = -1` if `‖x‖ < 1`. -/
theorem moritaGamma_add_one (x : ℤ_[p]) :
    moritaGamma p (x + 1) = (if ‖x‖ = 1 then -x else -1) * moritaGamma p x := by
  have key : (fun x : ℤ_[p] => moritaGamma p (x + 1)) =
      fun x => (if ‖x‖ = 1 then -x else -1) * moritaGamma p x := by
    refine Continuous.ext_on PadicInt.denseRange_natCast ?_ ?_ ?_
    · exact (moritaGamma p).continuous.comp (continuous_id.add continuous_const)
    · exact continuous_moritaGamma_factor.mul (moritaGamma p).continuous
    · rintro _ ⟨n, rfl⟩
      have h1 : ((n : ℤ_[p]) + 1) = ((n + 1 : ℕ) : ℤ_[p]) := by push_cast; rfl
      simp only
      rw [h1, moritaGamma_natCast, moritaGamma_natCast, moritaGammaNat_succ]
      simp only [PadicInt.norm_natCast_eq_one_iff, Nat.Prime.coprime_iff_not_dvd Fact.out]
      split_ifs <;> rfl
  exact congrFun key x

/-- `Γ_p(-n) Γ_p(n + 1) = (-1) ^ (⌊n / p⌋ + n + 1)` for every natural number `n`. -/
theorem moritaGamma_neg_natCast_mul_moritaGamma_natCast_add_one (n : ℕ) :
    moritaGamma p (-(n : ℤ_[p])) * moritaGamma p ((n : ℤ_[p]) + 1) =
      (-1) ^ (n / p + n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hfe := moritaGamma_add_one (p := p) (-((n + 1 : ℕ) : ℤ_[p]))
    have e1 : -((n + 1 : ℕ) : ℤ_[p]) + 1 = -(n : ℤ_[p]) := by push_cast; ring
    rw [e1, norm_neg, neg_neg] at hfe
    have e2 : ((n + 1 : ℕ) : ℤ_[p]) + 1 = ((n + 1 + 1 : ℕ) : ℤ_[p]) := by push_cast; ring
    have e3 : (n : ℤ_[p]) + 1 = ((n + 1 : ℕ) : ℤ_[p]) := by push_cast; ring
    rw [Nat.cast_succ, ← Nat.cast_succ, e2, moritaGamma_natCast, moritaGammaNat_succ,
      ← moritaGamma_natCast]
    rw [e3, hfe] at ih
    simp only [PadicInt.norm_natCast_eq_one_iff, Nat.Prime.coprime_iff_not_dvd Fact.out] at ih
    by_cases hc : p ∣ n + 1
    · rw [ite_eq_right (not_not.mpr hc)] at ih
      rw [ite_eq_left hc]
      have hd : (n + 1) / p = n / p + 1 := by
        rw [Nat.succ_div, ite_eq_left hc]
      rw [hd, show n / p + 1 + (n + 1) + 1 = (n / p + n + 1) + 1 + 1 by ring, pow_succ,
        pow_succ, ← ih]
      ring
    · rw [ite_eq_left hc] at ih
      rw [ite_eq_right hc]
      have hd : (n + 1) / p = n / p := by
        rw [Nat.succ_div, ite_eq_right hc, add_zero]
      rw [hd, show n / p + (n + 1) + 1 = (n / p + n + 1) + 1 by ring, pow_succ, ← ih]
      ring

/-- Reduction modulo `p` is constant on balls of radius `1`. -/
private lemma toZMod_eq_of_norm_sub_lt_one {x y : ℤ_[p]} (h : ‖y - x‖ < 1) :
    PadicInt.toZMod y = PadicInt.toZMod x := by
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZMod,
    IsLocalRing.mem_maximalIdeal]
  exact PadicInt.mem_nonunits.2 h

/-- A function of `x ∈ ℤ_[p]` that only depends on `x` modulo `p` is continuous. -/
private lemma continuous_comp_toZMod {X : Type*} [TopologicalSpace X] (g : ZMod p → X) :
    Continuous fun x : ℤ_[p] => g (PadicInt.toZMod x) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  refine (continuousAt_const (y := g (PadicInt.toZMod x))).congr ?_
  filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
  rw [toZMod_eq_of_norm_sub_lt_one (x := x) (y := y) (by simpa [dist_eq_norm] using hy)]

/-- The parity identity behind the reflection formula at a positive integer `m + 1`. -/
private lemma neg_one_pow_div_add_eq (hp : p ≠ 2) (m : ℕ) :
    ((-1 : ℤ_[p]) ^ (m / p + m + 1)) =
      (-1) ^ (if ((m + 1 : ℕ) : ZMod p) = 0 then p else ((m + 1 : ℕ) : ZMod p).val) := by
  obtain ⟨j, hj⟩ := (Fact.out : p.Prime).odd_of_ne_two hp
  have hsd := Nat.succ_div (a := m) (b := p)
  have hdm := Nat.div_add_mod (m + 1) p
  have hpQ : p * ((m + 1) / p) = 2 * (j * ((m + 1) / p)) + (m + 1) / p := by rw [hj]; ring
  rw [neg_one_pow_eq_pow_mod_two (R := ℤ_[p]),
    neg_one_pow_eq_pow_mod_two (R := ℤ_[p]) (n := ite _ _ _)]
  congr 1
  simp only [ZMod.natCast_eq_zero_iff, ZMod.val_natCast]
  split_ifs at hsd ⊢ with h
  · rw [Nat.dvd_iff_mod_eq_zero] at h
    omega
  · rw [Nat.dvd_iff_mod_eq_zero] at h
    omega

/-- **Reflection formula for `Γ_p`.** For an odd prime `p` and `x ∈ ℤ_[p]`,
`Γ_p(x) Γ_p(1 - x) = (-1) ^ ℓ(x)`, where `ℓ(x) ∈ {1, …, p}` is congruent to `x` modulo `p`: it is
`p` if `x ≡ 0 (mod p)` and the least positive residue of `x` otherwise. -/
theorem moritaGamma_mul_moritaGamma_one_sub (hp : p ≠ 2) (x : ℤ_[p]) :
    moritaGamma p x * moritaGamma p (1 - x) =
      (-1) ^ (if PadicInt.toZMod x = 0 then p else (PadicInt.toZMod x).val) := by
  have hc := (moritaGamma p).continuous
  have hsurj : Function.Surjective fun y : ℤ_[p] => y + 1 := fun y => ⟨y - 1, by simp⟩
  have hdense : DenseRange ((fun y : ℤ_[p] => y + 1) ∘ (fun n : ℕ => (n : ℤ_[p]))) :=
    DenseRange.comp hsurj.denseRange PadicInt.denseRange_natCast
      (continuous_id.add continuous_const)
  have key : (fun x : ℤ_[p] => moritaGamma p x * moritaGamma p (1 - x)) =
      fun x => (-1) ^ (if PadicInt.toZMod x = 0 then p else (PadicInt.toZMod x).val) := by
    refine Continuous.ext_on hdense ?_
      (continuous_comp_toZMod fun a : ZMod p => ((-1 : ℤ_[p]) ^ (if a = 0 then p else a.val)))
      ?_
    · exact hc.mul (hc.comp (continuous_const.sub continuous_id))
    · rintro _ ⟨m, rfl⟩
      simp only [Function.comp_apply]
      have e1 : (1 : ℤ_[p]) - ((m : ℤ_[p]) + 1) = -(m : ℤ_[p]) := by ring
      have e2 : (m : ℤ_[p]) + 1 = ((m + 1 : ℕ) : ℤ_[p]) := by push_cast; ring
      rw [e1, mul_comm, moritaGamma_neg_natCast_mul_moritaGamma_natCast_add_one,
        neg_one_pow_div_add_eq hp, e2, map_natCast]
  exact congrFun key x

/-- For an odd prime `p` and `x = 1/2 ∈ ℤ_[p]` (that is, `2 * x = 1`), `Γ_p(x) ^ 2 = 1` if
`p ≡ 3 (mod 4)` and `Γ_p(x) ^ 2 = -1` if `p ≡ 1 (mod 4)`. -/
theorem moritaGamma_sq_of_two_mul_eq_one (hp : p ≠ 2) {x : ℤ_[p]} (hx : 2 * x = 1) :
    moritaGamma p x ^ 2 = if p % 4 = 3 then 1 else -1 := by
  have hpp := (Fact.out : p.Prime)
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hpp.odd_of_ne_two hp)
  have h1x : 1 - x = x := by linear_combination -hx
  have href := moritaGamma_mul_moritaGamma_one_sub hp x
  rw [h1x] at href
  set k := (p + 1) / 2 with hk
  have h2k : 2 * k = p + 1 := by omega
  have hkp : k < p := by have := hpp.two_le; omega
  have hk1 : 1 ≤ k := by omega
  have h20 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hz : PadicInt.toZMod x = (k : ZMod p) := by
    have h1 : (2 : ZMod p) * PadicInt.toZMod x = 1 := by
      have := congrArg (PadicInt.toZMod (p := p)) hx
      rwa [map_mul, map_ofNat, map_one] at this
    have h2 : (2 : ZMod p) * (k : ZMod p) = 1 := by
      have : ((2 * k : ℕ) : ZMod p) = ((p + 1 : ℕ) : ZMod p) := by rw [h2k]
      push_cast at this
      simpa using this
    have : (2 : ZMod p) * (PadicInt.toZMod x - k) = 0 := by linear_combination h1 - h2
    have := (mul_eq_zero.mp this).resolve_left h20
    linear_combination this
  have hk0 : (k : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  have hval : (k : ZMod p).val = k := ZMod.val_natCast_of_lt hkp
  rw [hz, ite_eq_right hk0, hval] at href
  rw [sq, href]
  split_ifs with h4
  · exact Even.neg_one_pow ⟨k / 2, by omega⟩
  · exact Odd.neg_one_pow ⟨k / 2, by omega⟩

end MetaMathlibExt
