/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

open scoped NumberField

namespace NumberField
namespace Ideal

variable (K : Type*) [Field K] [NumberField K]

/-!
# Counting ideals of bounded norm

This file proves an explicit upper bound on the number of nonzero ideals of the
ring of integers of a number field with absolute norm at most `M`.

## Source and statement map

The exact source is ATLAS corpus record `NumberTheoryI:295`, *Number Theory I*,
Section 14.5, Lemma 14.21. At ATLAS revision
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, its
[corpus entry](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/targets.yaml#L2072-L2077)
and the corresponding
[Lean wrapper](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/Chapter14/ClassGroupFinite.lean#L29-L32)
are immutable references. The wrapper declaration is
`ClassGroupFinite.ideals_bounded_absNorm_card_le`.

The source statement is: “Let `K` be a number field of degree `n` and let
`M ∈ ℝ_{>0}`. The number of `𝓞_K`-ideals of norm `N(I) ≤ M` is bounded by
`(nM)^(log₂ M)` (and in particular, finite).”

The exact clause-by-clause formalization is
`card_nonzero_absNorm_le_real_rpow`:

* “number field `K` of degree `n`” is `[Field K] [NumberField K]` with
  `n = Module.finrank ℚ K`;
* “`M ∈ ℝ_{>0}`” is `M : ℝ` together with `hM : 0 < M`, with no additional
  endpoint restriction;
* “ideals with `N(I) ≤ M`” is the subtype of `I : Ideal (𝓞 K)` satisfying
  `I ≠ ⊥` and `(Ideal.absNorm I : ℝ) ≤ M`;
* “the number” is `Nat.card` of that subtype, cast to `ℝ`;
* the source bound is represented literally as
  `((Module.finrank ℚ K : ℝ) * M) ^ Real.logb 2 M`, where the real exponent
  notation is Mathlib's `Real.rpow`.

The integer theorem `card_nonzero_absNorm_le` and floor theorem
`card_nonzero_absNorm_le_real` are derived discrete strengthenings used to
prove the source endpoint; they are not claimed as literal source statements.

## Main results

* `NumberField.Ideal.card_nonzero_absNorm_le`: the number of nonzero ideals `I`
  of `𝓞 K` with `Ideal.absNorm I ≤ M` is at most
  `(Module.finrank ℚ K * M) ^ Nat.log 2 M`, for every `M : ℕ`.
* `NumberField.Ideal.card_nonzero_absNorm_le_real`: the same bound with a real
  threshold `M`, stated in terms of `⌊M⌋₊` (the stronger discrete bridge).
* `NumberField.Ideal.card_nonzero_absNorm_le_real_rpow`: the textbook's exact
  positive-real endpoint, with bound `((finrank : ℝ) * M) ^ Real.logb 2 M`
  via real `rpow`, derived from the floor bridge.

## Proof sketch

Every nonzero ideal factors uniquely into prime ideals, each of norm at least
`2`, so an ideal of norm at most `M` has at most `Nat.log 2 M` prime factors
counted with multiplicity. A prime ideal above a rational prime `p` satisfies
`absNorm P = p ^ inertiaDeg`, so every prime factor lies above a rational
prime `p ≤ M`; at most `finrank ℚ K` primes lie above each `p` since
ramification indices and inertia degrees are positive and sum to the degree
(`Ideal.sum_ramification_inertia_eq_finrank`). Padding the factor list with
`none` injects the bounded ideals into `Fin (Nat.log 2 M) → Option fibers`,
which gives the power bound.

## Derivation of the source endpoint

The textbook states this lemma with a positive real threshold `M` and bound
`(n * M) ^ log₂ M`. The integer-threshold theorem above is the strongest
discrete form: it is computable and holds for all `M : ℕ` including `0` and
`1` (where both sides degenerate correctly). The real-`⌊M⌋₊` corollary is the
bridge: for `M < 1` the subtype is empty, and for `1 ≤ M` the real and integer
subtypes coincide. The real-`rpow` theorem is the exact source endpoint,
stating the textbook bound literally with real `rpow`; it follows from the
floor bridge by monotonicity of `rpow` in both base and exponent.
-/

/-- The subtype of nonzero ideals of bounded absolute norm is finite. -/
noncomputable instance instFiniteIdealsBoundedAbsNorm (M : ℕ) :
    Finite {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ M} :=
  ((Ideal.finite_setOfPred_absNorm_le M).subset fun _ hI => hI.2).to_subtype

/-- Prime ideals of `𝓞 K` lying above rational primes `p ≤ M`, bundled by `p`. -/
private abbrev primeFibers (M : ℕ) :=
  (p : {p : ℕ // p.Prime ∧ p ≤ M}) ×
    ↥((Ideal.span ({(p.1 : ℤ)} : Set ℤ)).primesOver (𝓞 K))

/-- Per-fiber `Fintype`: a nonzero prime of `ℤ` is maximal, so each
`primesOver` set is finite. -/
private noncomputable instance fiberFintype (M : ℕ)
    (p : {p : ℕ // p.Prime ∧ p ≤ M}) :
    Fintype ↥((Ideal.span ({(p.1 : ℤ)} : Set ℤ)).primesOver (𝓞 K)) := by
  have hcast : ((p.1 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast p.2.1.ne_zero
  have hprime : (Ideal.span ({(p.1 : ℤ)} : Set ℤ)).IsPrime :=
    (Ideal.span_singleton_prime hcast).mpr (Nat.prime_iff_prime_int.mp p.2.1)
  have hP0 : Ideal.span ({(p.1 : ℤ)} : Set ℤ) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hcast
  have hmax : (Ideal.span ({(p.1 : ℤ)} : Set ℤ)).IsMaximal :=
    hprime.isMaximal hP0
  infer_instance

/-- `Fintype` for the rational primes bounded by `M`. -/
private noncomputable instance instFintypePrimeBounds (M : ℕ) :
    Fintype {p : ℕ // p.Prime ∧ p ≤ M} := by
  have hfin : {p : ℕ | p.Prime ∧ p ≤ M}.Finite :=
    (Finset.range (M + 1)).finite_toSet.subset fun p hp =>
      Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.lt_succ_of_le hp.2))
  exact hfin.fintype

private noncomputable instance instFintypePrimeFibers (M : ℕ) :
    Fintype (primeFibers K M) := by
  infer_instance

/-- A nonzero prime ideal has norm at least `2`. -/
private theorem two_le_absNorm_of_prime {P : Ideal (𝓞 K)}
    (hprime : P.IsPrime) (hbot : P ≠ ⊥) : 2 ≤ Ideal.absNorm P := by
  have h0 : Ideal.absNorm P ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hbot
  have h1 : Ideal.absNorm P ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr hprime.ne_top
  omega

/-- An ideal of norm at most `M` has at most `Nat.log 2 M` prime factors. -/
private theorem card_normalizedFactors_le_log (M : ℕ) {I : Ideal (𝓞 K)}
    (hI : I ≠ ⊥) (hle : Ideal.absNorm I ≤ M) :
    (UniqueFactorizationMonoid.normalizedFactors I).card ≤ Nat.log 2 M := by
  have hmem : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
      2 ≤ Ideal.absNorm P := by
    intro P hP
    obtain ⟨hprime, hleIP⟩ := (Ideal.mem_normalizedFactors_iff hI).mp hP
    have hPbot : P ≠ ⊥ := by
      rintro rfl
      exact hI (le_bot_iff.mp hleIP)
    exact two_le_absNorm_of_prime K hprime hPbot
  have hmap : ((UniqueFactorizationMonoid.normalizedFactors I).map
      ⇑Ideal.absNorm).prod = Ideal.absNorm I := by
    rw [← map_multiset_prod, Ideal.prod_normalizedFactors_eq_self hI]
  have htwo : (2 : ℕ) ^ (UniqueFactorizationMonoid.normalizedFactors I).card ≤
      Ideal.absNorm I := by
    have h := Multiset.pow_card_le_prod (s :=
      (UniqueFactorizationMonoid.normalizedFactors I).map ⇑Ideal.absNorm)
      (a := 2) (fun x hx => by
        obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hx
        exact hmem P hP)
    rwa [Multiset.card_map, hmap] at h
  exact Nat.le_log_of_pow_le (by norm_num) (htwo.trans hle)

/-- At most `finrank ℚ K` prime ideals lie above a given rational prime. -/
private theorem card_primesOver_le_finrank {p : ℕ} (hp : p.Prime) :
    Nat.card ↥((Ideal.span ({(p : ℤ)} : Set ℤ)).primesOver (𝓞 K)) ≤
      Module.finrank ℚ K := by
  have hcast : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  haveI hprime : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsPrime :=
    (Ideal.span_singleton_prime hcast).mpr (Nat.prime_iff_prime_int.mp hp)
  have hP0 : Ideal.span ({(p : ℤ)} : Set ℤ) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hcast
  have hmax : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsMaximal :=
    hprime.isMaximal hP0
  rw [Nat.card_eq_fintype_card, ← NumberField.RingOfIntegers.rank,
    ← Ideal.sum_ramification_inertia_eq_finrank
      (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 K),
    ← Finset.card_univ, Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum fun q _ => ?_
  have hq : q.1.IsPrime := q.2.1
  have he : 0 < q.1.ramificationIdx ℤ := Ideal.ramificationIdx_pos ℤ q.1
  have hf : 0 < q.1.inertiaDeg ℤ := Ideal.inertiaDeg_pos q.1 ℤ
  exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero he.ne' hf.ne')

/-- Every bounded nonzero prime ideal lies above a small rational prime. -/
private theorem exists_prime_liesOver {P : Ideal (𝓞 K)} (M : ℕ)
    (hprime : P.IsPrime) (hbot : P ≠ ⊥) (hle : Ideal.absNorm P ≤ M) :
    ∃ p : ℕ, p.Prime ∧ p ≤ M ∧
      P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
  have hPprime : P.IsPrime := hprime
  haveI := hprime
  obtain ⟨q, hq⟩ := IsPrincipalIdealRing.principal (P.under ℤ)
  have hqspan : Ideal.span ({q} : Set ℤ) = P.under ℤ := hq.symm
  have hq0 : q ≠ 0 := by
    rintro rfl
    apply hbot
    have hunder : P.under ℤ = ⊥ := by
      rw [← hqspan]
      exact Ideal.span_singleton_eq_bot.mpr rfl
    exact Ideal.eq_bot_of_under_eq_bot hunder
  have hgen_prime : (Ideal.span ({q} : Set ℤ)).IsPrime := by
    rw [hqspan]
    infer_instance
  have hqprime : Prime q := (Ideal.span_singleton_prime hq0).mp hgen_prime
  have hspan : Ideal.span ({((q.natAbs : ℕ) : ℤ)} : Set ℤ) =
      Ideal.span ({q} : Set ℤ) := by
    rcases abs_choice q with h | h <;> simp [h]
  have hlie : P.LiesOver (Ideal.span ({q} : Set ℤ)) := by
    rcases abs_choice q with h | h <;>
      simpa [h, Ideal.span_singleton_neg q, ← Ideal.submodule_span_eq, ← hq]
        using Ideal.over_under P
  have hlieN : P.LiesOver (Ideal.span ({((q.natAbs : ℕ) : ℤ)} : Set ℤ)) := by
    rw [hspan]
    exact hlie
  have hlieI : P.LiesOver (Ideal.span ({((q.natAbs : ℕ) : ℤ)} : Set ℤ)) := hlieN
  haveI := hlieN
  have hpow := Ideal.pow_inertiaDeg q.natAbs P
  have hpos : 0 < P.inertiaDeg ℤ := Ideal.inertiaDeg_pos P ℤ
  have h1 : 1 ≤ q.natAbs := Int.natAbs_pos.mpr hq0
  refine ⟨q.natAbs, Int.prime_iff_natAbs_prime.mp hqprime, ?_, hlieN⟩
  calc q.natAbs ≤ q.natAbs ^ P.inertiaDeg ℤ := le_self_pow₀ h1 hpos.ne'
    _ = Ideal.absNorm P := hpow
    _ ≤ M := hle

/-- Prime factors of a bounded ideal are prime, nonzero, and bounded. -/
private theorem factor_props {M : ℕ} {I : Ideal (𝓞 K)}
    (hI : I ≠ ⊥) (hle : Ideal.absNorm I ≤ M)
    {P : Ideal (𝓞 K)}
    (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors I) :
    P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P ≤ M := by
  obtain ⟨hprime, hleIP⟩ := (Ideal.mem_normalizedFactors_iff hI).mp hP
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    exact hI (le_bot_iff.mp hleIP)
  have hdvd : P ∣ I :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
  have hnorm : Ideal.absNorm P ∣ Ideal.absNorm I :=
    Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hdvd)
  have hne : Ideal.absNorm I ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hI
  have hPle : Ideal.absNorm P ≤ M :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hnorm).trans hle
  exact ⟨hprime, hPbot, hPle⟩

/-- The fiber element over a prime factor; a pure term so projections hold
by `rfl`. -/
private noncomputable def fiberMkAux {M : ℕ} (p : ℕ) (hprimep : p.Prime)
    (hpleM : p ≤ M) {P : Ideal (𝓞 K)} (hprime : P.IsPrime)
    (hlies : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))) :
    primeFibers K M :=
  ⟨⟨p, hprimep, hpleM⟩, P, hprime, hlies⟩

omit [NumberField K] in
private theorem fiberMkAux_val {M : ℕ} (p : ℕ) (hprimep : p.Prime)
    (hpleM : p ≤ M) {P : Ideal (𝓞 K)} (hprime : P.IsPrime)
    (hlies : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))) :
    (fiberMkAux K p hprimep hpleM hprime hlies).2.1 = P := rfl

/-- Injection data: the padded factor list of a bounded ideal. -/
private noncomputable def encode (M : ℕ)
    (x : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ M}) :
    Fin (Nat.log 2 M) → Option (primeFibers K M) := fun i =>
  if h : i.val < (UniqueFactorizationMonoid.normalizedFactors x.1).toList.length
  then
    have hPmem : (UniqueFactorizationMonoid.normalizedFactors x.1).toList[i.val]'h ∈
        UniqueFactorizationMonoid.normalizedFactors x.1 :=
      Multiset.mem_toList.mp (List.mem_of_getElem rfl)
    have hprops := factor_props K x.2.1 x.2.2 hPmem
    have hex := exists_prime_liesOver K M hprops.1 hprops.2.1 hprops.2.2
    some (fiberMkAux K hex.choose hex.choose_spec.1 hex.choose_spec.2.1
      hprops.1 hex.choose_spec.2.2)
  else none

private theorem length_toList_le_log (M : ℕ)
    (x : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ M}) :
    (UniqueFactorizationMonoid.normalizedFactors x.1).toList.length ≤
      Nat.log 2 M := by
  rw [Multiset.length_toList]
  exact card_normalizedFactors_le_log K M x.2.1 x.2.2

/-- Forgetting proofs recovers the factor list entry. -/
private theorem map_encode_eq (M : ℕ)
    (x : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ M})
    (i : Fin (Nat.log 2 M)) :
    (encode K M x i).map (fun F : primeFibers K M => F.2.1) =
      (UniqueFactorizationMonoid.normalizedFactors x.1).toList[i.val]? := by
  by_cases h : i.val <
    (UniqueFactorizationMonoid.normalizedFactors x.1).toList.length
  · unfold encode
    rw [dite_eq_left h]
    simp only [Option.map_some, fiberMkAux_val, List.getElem?_eq_getElem h]
  · have e0 : encode K M x i = none := by
      unfold encode
      exact dite_eq_right h
    rw [e0, Option.map_none]
    exact (List.getElem?_eq_none (le_of_not_gt h)).symm

/-- The padded-factor-list encoding is injective. -/
private theorem encode_injective (M : ℕ) :
    Function.Injective (encode K M) := by
  intro x y hxy
  have hlist : (UniqueFactorizationMonoid.normalizedFactors x.1).toList =
      (UniqueFactorizationMonoid.normalizedFactors y.1).toList := by
    apply List.ext_getElem?
    intro n
    by_cases hn : n < Nat.log 2 M
    · have h1 := map_encode_eq K M x ⟨n, hn⟩
      have h2 := map_encode_eq K M y ⟨n, hn⟩
      have h3 := congrFun hxy ⟨n, hn⟩
      rw [h3] at h1
      exact h1.symm.trans h2
    · rw [List.getElem?_eq_none_iff.mpr
          (le_trans (length_toList_le_log K M x) (le_of_not_gt hn)),
        List.getElem?_eq_none_iff.mpr
          (le_trans (length_toList_le_log K M y) (le_of_not_gt hn))]
  have hnf : UniqueFactorizationMonoid.normalizedFactors x.1 =
      UniqueFactorizationMonoid.normalizedFactors y.1 := by
    have hcoe := congrArg (fun l : List (Ideal (𝓞 K)) => (l : Multiset (Ideal (𝓞 K))))
      hlist
    rwa [Multiset.coe_toList, Multiset.coe_toList] at hcoe
  have hI : x.1 = y.1 := by
    conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self x.2.1]
    conv_rhs => rw [← Ideal.prod_normalizedFactors_eq_self y.2.1]
    rw [hnf]
  exact Subtype.ext hI

/-- There are at most `M - 1` rational primes `p ≤ M`. -/
private theorem card_primeBounds_le (M : ℕ) :
    Fintype.card {p : ℕ // p.Prime ∧ p ≤ M} ≤ M - 1 := by
  rw [← Fintype.card_fin (M - 1)]
  refine Fintype.card_le_of_injective
    (fun p : {p : ℕ // p.Prime ∧ p ≤ M} => ⟨p.1 - 2, by
      obtain ⟨hprime, hle⟩ := p.2
      have h2 := hprime.two_le
      omega⟩) ?_
  intro a b hab
  have h2a := a.2.1.two_le
  have h2b := b.2.1.two_le
  have heq : a.1 - 2 = b.1 - 2 := Fin.ext_iff.mp hab
  have hval : a.1 = b.1 := by omega
  exact Subtype.ext hval

/-- The bundled fiber type has at most `finrank ℚ K * (M - 1)` elements. -/
private theorem card_primeFibers_le (M : ℕ) :
    Fintype.card (primeFibers K M) ≤ Module.finrank ℚ K * (M - 1) := by
  classical
  have h1 : ∀ p : {p : ℕ // p.Prime ∧ p ≤ M},
      Fintype.card ↥((Ideal.span ({(p.1 : ℤ)} : Set ℤ)).primesOver (𝓞 K)) ≤
        Module.finrank ℚ K := by
    intro p
    rw [← Nat.card_eq_fintype_card]
    exact card_primesOver_le_finrank K p.2.1
  have hsum : Fintype.card (primeFibers K M)
      = ∑ p : {p : ℕ // p.Prime ∧ p ≤ M},
        Fintype.card ↥((Ideal.span ({(p.1 : ℤ)} : Set ℤ)).primesOver (𝓞 K)) :=
    Fintype.card_sigma
  rw [hsum]
  calc (∑ p : {p : ℕ // p.Prime ∧ p ≤ M},
          Fintype.card ↥((Ideal.span ({(p.1 : ℤ)} : Set ℤ)).primesOver (𝓞 K)))
        ≤ (∑ _p : {p : ℕ // p.Prime ∧ p ≤ M}, Module.finrank ℚ K) :=
          Finset.sum_le_sum fun p _ => h1 p
    _ = Fintype.card {p : ℕ // p.Prime ∧ p ≤ M} • Module.finrank ℚ K := by
          rw [Finset.sum_const, Finset.card_univ]
    _ ≤ (M - 1) • Module.finrank ℚ K := by
          simp only [smul_eq_mul]
          exact mul_le_mul (card_primeBounds_le M) le_rfl (Nat.zero_le _)
            (Nat.zero_le _)
    _ = Module.finrank ℚ K * (M - 1) := by rw [smul_eq_mul, mul_comm]

/-- **Bound on the number of ideals of bounded norm, integer threshold.** Let $K$ be a number
field of degree $n = [K : \mathbb{Q}]$ with ring of integers $\mathcal{O}_K$, let $M$ be a natural
number, and let $k$ be the largest natural number with $2^k \le M$, with $k = 0$ if $M = 0$.
Then the number of nonzero ideals $I$ of $\mathcal{O}_K$ whose absolute norm
$N(I) = |\mathcal{O}_K / I|$ satisfies $N(I) \le M$ is at most $(nM)^k$.

Source: ATLAS `NumberTheoryI:295`, *Number Theory I*, Section 14.5, Lemma 14.21; this is a
discrete strengthening with an integer threshold, valid also at $M = 0$ and $M = 1$, not the
source's literal positive-real statement. -/
theorem card_nonzero_absNorm_le (M : ℕ) :
    Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ M} ≤
      (Module.finrank ℚ K * M) ^ Nat.log 2 M := by
  rcases eq_zero_or_pos M with rfl | hMpos
  · have hempty : IsEmpty
      {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ 0} := by
      constructor
      rintro ⟨I, hbot, hle⟩
      exact (Ideal.absNorm_eq_zero_iff.not.mpr hbot) (Nat.le_zero.mp hle)
    have hfin : Fintype
      {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ 0} := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero]
    exact Nat.zero_le _
  · have hM1 : 1 ≤ M := hMpos
    have hfin : Fintype
      {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ M} := Fintype.ofFinite _
    have hinj : Function.Injective (encode K M) := encode_injective K M
    have hfib := card_primeFibers_le K M
    have hfr : 1 ≤ Module.finrank ℚ K := Module.finrank_pos
    calc Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ M}
        = Fintype.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ M} :=
          Nat.card_eq_fintype_card
      _ ≤ Fintype.card (Fin (Nat.log 2 M) → Option (primeFibers K M)) :=
          Fintype.card_le_of_injective _ hinj
      _ = Nat.card (Fin (Nat.log 2 M) → Option (primeFibers K M)) :=
          Nat.card_eq_fintype_card.symm
      _ = (Nat.card (Option (primeFibers K M))) ^ Nat.card (Fin (Nat.log 2 M)) :=
          Nat.card_fun
      _ = (Fintype.card (primeFibers K M) + 1) ^ Nat.log 2 M := by
          rw [Finite.card_option, Nat.card_eq_fintype_card, Nat.card_fin]
      _ ≤ (Module.finrank ℚ K * M) ^ Nat.log 2 M := by
          apply Nat.pow_le_pow_left _ _
          calc Fintype.card (primeFibers K M) + 1
              ≤ Module.finrank ℚ K * (M - 1) + 1 := Nat.add_le_add_right hfib 1
            _ ≤ Module.finrank ℚ K * (M - 1) + Module.finrank ℚ K :=
                Nat.add_le_add_left hfr _
            _ = Module.finrank ℚ K * ((M - 1) + 1) := by
                rw [Nat.mul_add, Nat.mul_one]
            _ = Module.finrank ℚ K * M := by rw [Nat.sub_add_cancel hM1]

/-- **Bound on the number of ideals of bounded norm, floor form.** Let $K$ be a number field of
degree $n = [K : \mathbb{Q}]$ with ring of integers $\mathcal{O}_K$, let $M$ be any real number,
and let $m = \max(0, \lfloor M \rfloor)$. Let $k$ be the largest natural number with
$2^k \le m$, and $k = 0$ if $m = 0$. Then the number of nonzero ideals $I$ of $\mathcal{O}_K$
whose absolute norm $N(I) = |\mathcal{O}_K / I|$ satisfies $N(I) \le M$ is at most $(nm)^k$.

For $M < 1$ there are no such ideals, since every nonzero ideal has norm at least $1$; for
$M \ge 1$ the condition $N(I) \le M$ is equivalent to $N(I) \le m$. -/
theorem card_nonzero_absNorm_le_real (M : ℝ) :
    Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M} ≤
      (Module.finrank ℚ K * ⌊M⌋₊) ^ Nat.log 2 ⌊M⌋₊ := by
  by_cases hM : 1 ≤ M
  · have hM0 : (0 : ℝ) ≤ M := zero_le_one.trans hM
    have hequiv : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M} ≃
        {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ ⌊M⌋₊} :=
      Equiv.subtypeEquivRight fun I => by
        constructor
        · rintro ⟨hbot, hle⟩
          exact ⟨hbot, (Nat.le_floor_iff hM0).mpr hle⟩
        · rintro ⟨hbot, hle⟩
          exact ⟨hbot, (Nat.le_floor_iff hM0).mp hle⟩
    rw [Nat.card_congr hequiv]
    exact card_nonzero_absNorm_le K ⌊M⌋₊
  · have hM' : M < 1 := lt_of_not_ge hM
    have hempty : IsEmpty
      {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M} := by
      constructor
      rintro ⟨I, hbot, hle⟩
      have hne : Ideal.absNorm I ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hbot
      have h1 : (1 : ℝ) ≤ Ideal.absNorm I := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
      linarith
    have hfin : Fintype
      {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M} :=
      Fintype.ofIsEmpty
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero]
    exact Nat.zero_le _

/-- **Bound on the number of ideals of bounded norm.** Let $K$ be a number field of degree
$n = [K : \mathbb{Q}]$ with ring of integers $\mathcal{O}_K$, and let $M > 0$ be a real number.
The number of nonzero ideals $I$ of $\mathcal{O}_K$ whose absolute norm
$N(I) = |\mathcal{O}_K / I|$ satisfies $N(I) \le M$ is at most $(nM)^{\log_2 M}$, where the
exponent $\log_2 M$ is a real number.

Source: ATLAS `NumberTheoryI:295`, *Number Theory I*, Section 14.5, Lemma 14.21. The proof
derives this bound from the integer-threshold and floor variants. -/
theorem card_nonzero_absNorm_le_real_rpow (M : ℝ) (hM : 0 < M) :
    (Nat.card {I : Ideal (𝓞 K) //
      I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M} : ℝ) ≤
      ((Module.finrank ℚ K : ℝ) * M) ^ (Real.logb 2 M) := by
  by_cases h1M : 1 ≤ M
  · have hNM : (⌊M⌋₊ : ℝ) ≤ M := Nat.floor_le hM.le
    have hN1 : 1 ≤ ⌊M⌋₊ := Nat.le_floor (by exact_mod_cast h1M)
    have hNpos : 0 < ⌊M⌋₊ := by omega
    have hlog : (Nat.log 2 ⌊M⌋₊ : ℝ) ≤ Real.logb 2 M := by
      rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hM]
      rw [Real.rpow_natCast]
      calc
        (2 : ℝ) ^ Nat.log 2 ⌊M⌋₊ = ((2 ^ Nat.log 2 ⌊M⌋₊ : ℕ) : ℝ) := by
          norm_num
        _ ≤ (⌊M⌋₊ : ℝ) := by
          exact_mod_cast Nat.pow_log_le_self 2 (Nat.ne_of_gt hNpos)
        _ ≤ M := hNM
    have hfinR : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
      exact_mod_cast Module.finrank_pos
    have hfinN : (0 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := Nat.cast_nonneg _
    have hbaseNM : (Module.finrank ℚ K : ℝ) * ⌊M⌋₊ ≤
        (Module.finrank ℚ K : ℝ) * M :=
      mul_le_mul_of_nonneg_left hNM hfinN
    have hbase1 : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) * M :=
      one_le_mul_of_one_le_of_one_le hfinR h1M
    have hexpN : (0 : ℝ) ≤ (Nat.log 2 ⌊M⌋₊ : ℝ) := Nat.cast_nonneg _
    have hbaseN : (0 : ℝ) ≤ (Module.finrank ℚ K : ℝ) * ⌊M⌋₊ :=
      mul_nonneg hfinN (Nat.cast_nonneg _)
    have hcast : (Nat.card {I : Ideal (𝓞 K) //
        I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M} : ℝ) ≤
        ((Module.finrank ℚ K : ℝ) * ⌊M⌋₊) ^ (Nat.log 2 ⌊M⌋₊ : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast card_nonzero_absNorm_le_real K M
    calc
      (Nat.card {I : Ideal (𝓞 K) //
            I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M} : ℝ) ≤
          ((Module.finrank ℚ K : ℝ) * ⌊M⌋₊) ^ (Nat.log 2 ⌊M⌋₊ : ℝ) := hcast
      _ ≤ ((Module.finrank ℚ K : ℝ) * M) ^ (Nat.log 2 ⌊M⌋₊ : ℝ) :=
        Real.rpow_le_rpow hbaseN hbaseNM hexpN
      _ ≤ ((Module.finrank ℚ K : ℝ) * M) ^ (Real.logb 2 M) :=
        Real.rpow_le_rpow_of_exponent_le hbase1 hlog
  · have hM' : M < 1 := lt_of_not_ge h1M
    have hempty : IsEmpty
        {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M} := by
      constructor
      rintro ⟨I, hbot, hle⟩
      have hne : Ideal.absNorm I ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hbot
      have h1 : (1 : ℝ) ≤ Ideal.absNorm I := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
      linarith
    have hfin : Fintype
        {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M} :=
      Fintype.ofIsEmpty
    have hcard0 : Nat.card
        {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M} = 0 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero]
    have hbase : (0 : ℝ) ≤ (Module.finrank ℚ K : ℝ) * M :=
      mul_nonneg (Nat.cast_nonneg _) hM.le
    have hrhs : (0 : ℝ) ≤
        ((Module.finrank ℚ K : ℝ) * M) ^ (Real.logb 2 M) :=
      Real.rpow_nonneg hbase _
    rw [hcard0, Nat.cast_zero]
    exact hrhs

end Ideal
end NumberField
