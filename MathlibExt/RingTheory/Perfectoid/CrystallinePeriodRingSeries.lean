/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from `ZInQKernel/Contrib/OneProof/AcrisImagePhi.lean` and
`ZInQKernel/Contrib/OneProof/AcrisImageSep.lean` (https://github.com/Deicyde/diophantine-z-q),
compared with the source files at commit `e9956cda4174c060ff85f5a6ddc7e4003e63fdd3`.
Copyright 2026 the contributors to Deicyde/diophantine-z-q.
Licensed under the Apache License, Version 2.0.
-/

module

public import MathlibExt.RingTheory.Perfectoid.CrystallinePeriodRingBasic
import Mathlib.RingTheory.WittVector.Complete

/-!
# Fontaine's crystalline period ring: restricted series and separatedness

Let `w ∈ A_inf = W(𝓞_ℂ_[p]♭)` and let `D = A_inf[w^n/n! : n ≥ 1]`
(`PadicComplexInt.finiteDividedPowers`). A restricted power series `f = Σ aₙ Xⁿ` (with `aₙ → 0`
`p`-adically) gives an element `PadicComplexInt.ofRestricted w hf` of the `p`-adic completion of
`D`: the limit of the partial sums `Σ_{n<N} aₙ w^n/n! ∈ D`. Every element of the completion
arises this way (`PadicComplexInt.exists_ofRestricted_eq`). For a generator `w` of `ker θ`, this
is the description of `A_cris` in Fontaine, *Le corps des périodes p-adiques*, Astérisque 223
(1994), Exposé II, §4.1.2 p. 83.

For a generator `w` of `ker θ`, the ring `D` is `p`-adically separated modulo the powers of the
kernel of `θ` with `p` inverted: if `y ∈ D` lies in `p^k D + (ker θ)^m` for every `k`, then
`y ∈ (ker θ)^m` (`PadicComplexInt.mem_ker_pow_of_forall`). Multiplying by `m!` moves `D` into
`A_inf` modulo `(ker θ)^m`, where this is `⋂ₖ (p^k A_inf + w^m A_inf) = w^m A_inf`. This is the
separatedness behind the well-definedness of the map `A_cris → B_dR^+` (Fontaine, *op. cit.*,
§§4.1.1–4.1.2, p. 83).
-/

@[expose] public noncomputable section

open Ideal PowerSeries
open WittVector (fontaineTheta)

namespace PadicComplexInt

variable (p : ℕ) [hp : Fact p.Prime]

local notation "𝔸" => WittVector p (PreTilt 𝓞_ℂ_[p] p)
local notation "𝔸ₚ" => Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))
local notation "𝕀" => RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)

variable {p}

/-! ### The completion as limits of restricted series -/

section Limits

variable (w : WittVector p (PreTilt 𝓞_ℂ_[p] p))

/-- The ideal `(p)` of `W(𝓞_ℂ_[p]♭)[w^n/n!]`, along which `CrystallineCompletion p w` is the
completion. -/
abbrev pIdeal : Ideal (finiteDividedPowers p w) :=
  Ideal.span ({(p : finiteDividedPowers p w)} : Set (finiteDividedPowers p w))

/-- An element `d` of `D = W(𝓞_ℂ_[p]♭)[w^n/n!]` lies in `(p) ^ k` if and only if `d = p ^ k e`
for some `e ∈ D`. -/
theorem mem_pIdeal_pow_iff (k : ℕ) (d : finiteDividedPowers p w) :
    d ∈ pIdeal w ^ k ↔ ∃ e ∈ finiteDividedPowers p w, (d : 𝔸ₚ) = (p : 𝔸ₚ) ^ k * e := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a, a.2, ?_⟩
    push_cast
    ring
  · rintro ⟨e, he, hde⟩
    refine ⟨⟨e, he⟩, Subtype.ext ?_⟩
    push_cast
    rw [hde]
    ring

/-- In a commutative ring, `I ^ k • ⊤ = I ^ k`. -/
private theorem mem_pow_smul_top_iff {R : Type*} [CommRing R] (I : Ideal R) (k : ℕ) (r : R) :
    r ∈ (I ^ k • ⊤ : Submodule R R) ↔ r ∈ I ^ k := by
  rw [smul_eq_mul, Ideal.mul_top]

/-- The partial sum `Σ_{n<N} aₙ w^n/n!` of the divided-power series of `f` at `w`, as an element
of `W(𝓞_ℂ_[p]♭)[w^n/n!]`. -/
def dividedPowerSumD (f : 𝔸⟦X⟧) (N : ℕ) : finiteDividedPowers p w :=
  ⟨dividedPowerSum w f N, dividedPowerSum_mem w f N⟩

/-- A finite sum `Σ_{n ∈ s} aₙ w^n/n!` whose coefficients are all divisible by `p^k` lies
in `p^k D`. -/
private theorem exists_sum_eq_pow_mul_mem {f : 𝔸⟦X⟧} {k : ℕ} (s : Finset ℕ)
    (h : ∀ n ∈ s, (p : 𝔸) ^ k ∣ PowerSeries.coeff n f) :
    ∃ e ∈ finiteDividedPowers p w,
      ∑ n ∈ s, algebraMap 𝔸 𝔸ₚ (PowerSeries.coeff n f) * dividedPower w n =
        (p : 𝔸ₚ) ^ k * e := by
  obtain ⟨g, hg⟩ := exists_sum_eq_pow_mul_sum w s h
  exact ⟨_, sum_mul_dividedPower_mem w s fun n => PowerSeries.coeff n g, hg⟩

/-- If the coefficients `aₙ` with `N ≤ n < M` are divisible by `p^k`, the partial sums at `N`
and at `M` agree modulo `p^k D`. -/
private theorem dividedPowerSumD_sub_mem {f : 𝔸⟦X⟧} {k N M : ℕ} (hNM : N ≤ M)
    (h : ∀ n, N ≤ n → n < M → (p : 𝔸) ^ k ∣ PowerSeries.coeff n f) :
    dividedPowerSumD w f M - dividedPowerSumD w f N ∈ pIdeal w ^ k := by
  rw [mem_pIdeal_pow_iff]
  obtain ⟨e, he, hse⟩ := exists_sum_eq_pow_mul_mem w (Finset.Ico N M) (f := f) (k := k)
    fun n hn => h n (Finset.mem_Ico.mp hn).1 (Finset.mem_Ico.mp hn).2
  refine ⟨e, he, ?_⟩
  change dividedPowerSum w f M - dividedPowerSum w f N = _
  rw [dividedPowerSum_sub_dividedPowerSum w f hNM, hse]

variable {w}

/-- A modulus of `p`-adic decay of a restricted series `f = Σ aₙ Xⁿ`: `p^k ∣ aₙ` for
`n ≥ decayBound hf k` (`decayBound_spec`). -/
def decayBound {f : 𝔸⟦X⟧} (hf : f ∈ restrictedPowerSeries p) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (k + 1), Classical.choose (hf j)

/-- For a restricted series `f = Σ aₙ Xⁿ`, `p^k` divides `aₙ` for every `n ≥ decayBound hf k`. -/
theorem decayBound_spec {f : 𝔸⟦X⟧} (hf : f ∈ restrictedPowerSeries p) (k : ℕ) :
    ∀ n, decayBound hf k ≤ n → (p : 𝔸) ^ k ∣ PowerSeries.coeff n f := by
  intro n hn
  have h1 : Classical.choose (hf k) ≤ decayBound hf k :=
    Finset.single_le_sum (f := fun j => Classical.choose (hf j)) (fun _ _ => Nat.zero_le _)
      (Finset.self_mem_range_succ k)
  exact Classical.choose_spec (hf k) n (h1.trans hn)

/-- The modulus of decay `decayBound hf` is monotone. -/
theorem decayBound_mono {f : 𝔸⟦X⟧} (hf : f ∈ restrictedPowerSeries p) :
    Monotone (decayBound hf) := by
  intro a b hab
  exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))

variable (w)

/-- Beyond `decayBound hf k`, the partial sums of a restricted series are constant modulo
`p^k D`. -/
private theorem dividedPowerSumD_sub_mem_of_le {f : 𝔸⟦X⟧} (hf : f ∈ restrictedPowerSeries p)
    {k N M : ℕ} (hN : decayBound hf k ≤ N) (hNM : N ≤ M) :
    dividedPowerSumD w f M - dividedPowerSumD w f N ∈ pIdeal w ^ k :=
  dividedPowerSumD_sub_mem w hNM fun n hn _ => decayBound_spec hf k n (hN.trans hn)

/-- The partial sums of a restricted series at the moduli `decayBound hf k` form a `p`-adic
Cauchy sequence in `W(𝓞_ℂ_[p]♭)[w^n/n!]`. -/
theorem dividedPowerSumD_decayBound_smodEq {f : 𝔸⟦X⟧} (hf : f ∈ restrictedPowerSeries p)
    (k : ℕ) :
    dividedPowerSumD w f (decayBound hf k) ≡ dividedPowerSumD w f (decayBound hf (k + 1))
      [SMOD (pIdeal w ^ k • ⊤ :
        Submodule (finiteDividedPowers p w) (finiteDividedPowers p w))] := by
  rw [SModEq.sub_mem, mem_pow_smul_top_iff, ← neg_mem_iff, neg_sub]
  exact dividedPowerSumD_sub_mem_of_le w hf le_rfl (decayBound_mono hf (Nat.le_succ k))

/-- The element of the `p`-adic completion of `W(𝓞_ℂ_[p]♭)[w^n/n!]` defined by a restricted
series `f = Σ aₙ Xⁿ`: the limit of the partial sums `Σ_{n<N} aₙ w^n/n!`. -/
def ofRestricted {f : 𝔸⟦X⟧} (hf : f ∈ restrictedPowerSeries p) : CrystallineCompletion p w :=
  AdicCompletion.mk (pIdeal w) (finiteDividedPowers p w)
    (AdicCompletion.AdicCauchySequence.mk (pIdeal w) (finiteDividedPowers p w)
      (fun k => dividedPowerSumD w f (decayBound hf k))
      (dividedPowerSumD_decayBound_smodEq w hf))

/-- Modulo `p^k`, the element defined by a restricted series is the class of its partial sum
`Σ_{n<N} aₙ w^n/n!`, for every `N ≥ decayBound hf k`. -/
theorem evalₐ_ofRestricted {f : 𝔸⟦X⟧} (hf : f ∈ restrictedPowerSeries p) (k N : ℕ)
    (hN : decayBound hf k ≤ N) :
    AdicCompletion.evalₐ (pIdeal w) k (ofRestricted w hf) =
      Ideal.Quotient.mk _ (dividedPowerSumD w f N) := by
  unfold ofRestricted
  rw [AdicCompletion.evalₐ_mk]
  change Ideal.Quotient.mk _ (dividedPowerSumD w f (decayBound hf k)) = _
  rw [eq_comm, Ideal.Quotient.eq]
  exact dividedPowerSumD_sub_mem_of_le w hf le_rfl hN

/-- Two restricted series define the same element if, for every `k`, their partial sums agree
modulo `p^k D` from some point on. -/
theorem ofRestricted_eq_of_forall {f g : 𝔸⟦X⟧} (hf : f ∈ restrictedPowerSeries p)
    (hg : g ∈ restrictedPowerSeries p)
    (h : ∀ k, ∃ N₀, ∀ N, N₀ ≤ N → ∃ e ∈ finiteDividedPowers p w,
      dividedPowerSum w f N - dividedPowerSum w g N = (p : 𝔸ₚ) ^ k * e) :
    ofRestricted w hf = ofRestricted w hg := by
  refine AdicCompletion.ext_evalₐ fun k => ?_
  have hk := h k
  obtain ⟨N₀, hN₀⟩ := hk
  have hN : N₀ ≤ N₀ + decayBound hf k + decayBound hg k := by omega
  have h1 : decayBound hf k ≤ N₀ + decayBound hf k + decayBound hg k := by omega
  have h2 : decayBound hg k ≤ N₀ + decayBound hf k + decayBound hg k := by omega
  refine (evalₐ_ofRestricted w hf k _ h1).trans
    (Eq.trans ?_ (evalₐ_ofRestricted w hg k _ h2).symm)
  rw [Ideal.Quotient.eq, mem_pIdeal_pow_iff]
  exact hN₀ _ hN

/-- The zero series defines the zero element. -/
theorem ofRestricted_zero : ofRestricted w (Subring.zero_mem (restrictedPowerSeries p)) = 0 := by
  refine AdicCompletion.ext_evalₐ fun k => ?_
  refine (evalₐ_ofRestricted w (Subring.zero_mem (restrictedPowerSeries p)) k _ le_rfl).trans ?_
  rw [map_zero (AdicCompletion.evalₐ (pIdeal w) k), Ideal.Quotient.eq_zero_iff_mem]
  have h0 : dividedPowerSumD w 0 (decayBound (Subring.zero_mem (restrictedPowerSeries p)) k) = 0 :=
    Subtype.ext (dividedPowerSum_zero_left w _)
  rw [h0]
  exact zero_mem _

/-- Every element of the `p`-adic completion of `W(𝓞_ℂ_[p]♭)[w^n/n!]` is defined by a
restricted series. -/
theorem exists_ofRestricted_eq (x : CrystallineCompletion p w) :
    ∃ (f : 𝔸⟦X⟧) (hf : f ∈ restrictedPowerSeries p), ofRestricted w hf = x := by
  classical
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective (pIdeal w) (finiteDividedPowers p w) x
  -- the consecutive differences `s (j+1) - s j = p^j e_j`
  have hdiff : ∀ j, ∃ e ∈ finiteDividedPowers p w,
      ((s.val (j + 1) : finiteDividedPowers p w) : 𝔸ₚ) - (s.val j : 𝔸ₚ) =
        (p : 𝔸ₚ) ^ j * e := by
    intro j
    have h1 := SModEq.sub_mem.mp (s.property (Nat.le_succ j))
    rw [mem_pow_smul_top_iff, ← neg_mem_iff, neg_sub] at h1
    exact (mem_pIdeal_pow_iff w j _).mp h1
  choose e he hse using hdiff
  -- finite expansions of `s 0` and of the `e_j`
  have hs0 := exists_dividedPowerSum_of_mem w (s.val 0).2
  obtain ⟨F₀, N₀, hF₀, hs₀⟩ := hs0
  choose G M hG hGe using fun j => exists_dividedPowerSum_of_mem w (he j)
  -- the coefficients of the approximations `s K`
  let c : ℕ → ℕ → 𝔸 := fun n K =>
    PowerSeries.coeff n F₀ + ∑ j ∈ Finset.range K, (p : 𝔸) ^ j * PowerSeries.coeff n (G j)
  have hc_succ : ∀ n K, c n (K + 1) = c n K + (p : 𝔸) ^ K * PowerSeries.coeff n (G K) := by
    intro n K
    simp only [c, Finset.sum_range_succ, add_assoc]
  have hcauchy : ∀ n, AdicCompletion.IsAdicCauchy (Ideal.span {(p : 𝔸)}) 𝔸
      (fun K => c n K) := by
    intro n
    refine (AdicCompletion.isAdicCauchy_iff _ _ _).mpr fun K => ?_
    rw [SModEq.sub_mem, mem_pow_smul_top_iff, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, hc_succ]
    exact ⟨-PowerSeries.coeff n (G K), by ring⟩
  choose a ha using fun n =>
    IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {(p : 𝔸)}) 𝔸) (hcauchy n)
  have ha' : ∀ n K, (p : 𝔸) ^ K ∣ c n K - a n := by
    intro n K
    have h1 := SModEq.sub_mem.mp (ha n K)
    rwa [mem_pow_smul_top_iff, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
  -- a common bound for the supports of `s 0, e_0, …, e_{K-1}`
  let B : ℕ → ℕ := fun K => N₀ + ∑ j ∈ Finset.range K, M j
  have hN₀B : ∀ K, N₀ ≤ B K := fun K => Nat.le_add_right _ _
  have hMB : ∀ K j, j < K → M j ≤ B K := by
    intro K j hj
    have h1 : M j ≤ ∑ i ∈ Finset.range K, M i :=
      Finset.single_le_sum (f := M) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj)
    simp only [B]
    omega
  have hcB : ∀ K n, B K ≤ n → c n K = 0 := by
    intro K n hn
    simp only [c]
    rw [hF₀ n ((hN₀B K).trans hn), zero_add]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [hG j n ((hMB K j (Finset.mem_range.mp hj)).trans hn), mul_zero]
  -- `s K = s 0 + Σ_{j<K} p^j e_j`
  have hTel : ∀ K, (s.val K : 𝔸ₚ) =
      s.val 0 + ∑ j ∈ Finset.range K, (p : 𝔸ₚ) ^ j * e j := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ← ih, ← hse K]
      ring
  have hA : ∀ K L, dividedPowerSum w (PowerSeries.mk fun n => c n K) L =
      dividedPowerSum w F₀ L + ∑ j ∈ Finset.range K, (p : 𝔸ₚ) ^ j * dividedPowerSum w (G j) L := by
    intro K L
    simp only [dividedPowerSum, c, PowerSeries.coeff_mk, map_add, map_sum, map_mul, map_pow,
      map_natCast, add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  have hBpsum : ∀ K L, B K ≤ L →
      dividedPowerSum w (PowerSeries.mk fun n => c n K) L = s.val K := by
    intro K L hL
    rw [hA, hTel K, dividedPowerSum_eq_of_le w ((hN₀B K).trans hL) hF₀, ← hs₀]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [dividedPowerSum_eq_of_le w ((hMB K j (Finset.mem_range.mp hj)).trans hL) (hG j), ← hGe j]
  -- the limit series is restricted
  have hf : PowerSeries.mk a ∈ restrictedPowerSeries p := by
    intro k
    refine ⟨B k, fun n hn => ?_⟩
    have h1 := ha' n k
    rw [hcB k n hn, zero_sub, dvd_neg] at h1
    simpa only [PowerSeries.coeff_mk] using h1
  refine ⟨PowerSeries.mk a, hf, AdicCompletion.ext_evalₐ fun k => ?_⟩
  refine (evalₐ_ofRestricted w hf k (max (decayBound hf k) (B k)) (le_max_left _ _)).trans ?_
  conv_rhs => rw [AdicCompletion.evalₐ_mk]
  rw [Ideal.Quotient.eq, mem_pIdeal_pow_iff]
  have h1 : ((dividedPowerSumD w (PowerSeries.mk a) (max (decayBound hf k) (B k)) - s.val k :
      finiteDividedPowers p w) : 𝔸ₚ) =
      dividedPowerSum w (PowerSeries.mk a - PowerSeries.mk fun n => c n k)
        (max (decayBound hf k) (B k)) := by
    rw [dividedPowerSum_sub, hBpsum k _ (le_max_right _ _)]
    rfl
  rw [h1]
  refine exists_sum_eq_pow_mul_mem w _ fun n _ => ?_
  rw [map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_mk, ← dvd_neg, neg_sub]
  exact ha' n k

end Limits

/-! ### Separatedness modulo the powers of `ker θ` -/

section Separated

variable {w : WittVector p (PreTilt 𝓞_ℂ_[p] p)}

/-- `m! · (w^n/n!) = (m!/n!) · w^n` for `n ≤ m`. -/
theorem factorial_mul_dividedPower_of_le (w : 𝔸) {m n : ℕ} (h : n ≤ m) :
    ((m.factorial : ℕ) : 𝔸ₚ) * dividedPower w n =
      algebraMap 𝔸 𝔸ₚ (((m.factorial / n.factorial : ℕ) : 𝔸) * w ^ n) := by
  have hd : m.factorial / n.factorial * n.factorial = m.factorial :=
    Nat.div_mul_cancel (Nat.factorial_dvd_factorial h)
  rw [map_mul, map_pow, map_natCast, ← factorial_mul_dividedPower w n, ← mul_assoc,
    ← Nat.cast_mul, hd]

/-- If `θ(w) = 0`, then for `y ∈ W(𝓞_ℂ_[p]♭)[w^n/n!]` and every `m`, `m! y` is congruent to an
element of `W(𝓞_ℂ_[p]♭)` modulo the `m`-th power of the kernel of `θ` with `p` inverted. -/
theorem exists_factorial_mul_sub_mem (hw : fontaineTheta 𝓞_ℂ_[p] p w = 0) {y : 𝔸ₚ}
    (hy : y ∈ finiteDividedPowers p w) (m : ℕ) :
    ∃ a : 𝔸, ((m.factorial : ℕ) : 𝔸ₚ) * y - algebraMap 𝔸 𝔸ₚ a ∈ 𝕀 ^ m := by
  obtain ⟨f, N, hf, rfl⟩ := exists_dividedPowerSum_of_mem w hy
  have htail : dividedPowerSum w f N - dividedPowerSum w f m ∈ 𝕀 ^ m := by
    rcases le_total m N with h | h
    · exact dividedPowerSum_sub_mem_ker_pow w hw f h
    · rw [dividedPowerSum_eq_of_le w h hf, sub_self]
      exact Ideal.zero_mem _
  refine ⟨∑ n ∈ Finset.range m,
      PowerSeries.coeff n f * (((m.factorial / n.factorial : ℕ) : 𝔸) * w ^ n), ?_⟩
  have hsum : ((m.factorial : ℕ) : 𝔸ₚ) * dividedPowerSum w f m =
      algebraMap 𝔸 𝔸ₚ (∑ n ∈ Finset.range m,
        PowerSeries.coeff n f * (((m.factorial / n.factorial : ℕ) : 𝔸) * w ^ n)) := by
    rw [dividedPowerSum, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [map_mul, ← factorial_mul_dividedPower_of_le w (Finset.mem_range.mp hn).le]
    ring
  have h1 : ((m.factorial : ℕ) : 𝔸ₚ) * dividedPowerSum w f N -
      algebraMap 𝔸 𝔸ₚ (∑ n ∈ Finset.range m,
        PowerSeries.coeff n f * (((m.factorial / n.factorial : ℕ) : 𝔸) * w ^ n)) =
      ((m.factorial : ℕ) : 𝔸ₚ) * (dividedPowerSum w f N - dividedPowerSum w f m) := by
    rw [← hsum]
    ring
  rw [h1]
  exact Ideal.mul_mem_left _ _ htail

/-- For a generator `w` of the kernel of `θ`, the ring `D = W(𝓞_ℂ_[p]♭)[w^n/n!]` is `p`-adically
separated modulo the powers of the kernel of `θ` with `p` inverted: if `y ∈ D` lies in
`p^k D + (ker θ)^m` for every `k`, then `y ∈ (ker θ)^m`. -/
theorem mem_ker_pow_of_forall
    (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w}) {y : 𝔸ₚ}
    (hy : y ∈ finiteDividedPowers p w) (m : ℕ)
    (h : ∀ k, ∃ e ∈ finiteDividedPowers p w, y - (p : 𝔸ₚ) ^ k * e ∈ 𝕀 ^ m) :
    y ∈ 𝕀 ^ m := by
  have hw : fontaineTheta 𝓞_ℂ_[p] p w = 0 := by
    change w ∈ RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p)
    rw [hgen]
    exact mem_span_singleton_self w
  obtain ⟨a, ha⟩ := exists_factorial_mul_sub_mem hw hy m
  have hmem : a ∈ span {w ^ m} := by
    refine mem_span_pow_of_forall hgen m fun k => ?_
    obtain ⟨e, he, hek⟩ := h k
    obtain ⟨b, hb⟩ := exists_factorial_mul_sub_mem hw he m
    have h2 : algebraMap 𝔸 𝔸ₚ (a - (p : 𝔸) ^ k * b) ∈ 𝕀 ^ m := by
      have h3 : algebraMap 𝔸 𝔸ₚ (a - (p : 𝔸) ^ k * b) =
          -(((m.factorial : ℕ) : 𝔸ₚ) * y - algebraMap 𝔸 𝔸ₚ a) +
            ((m.factorial : ℕ) : 𝔸ₚ) * (y - (p : 𝔸ₚ) ^ k * e) +
            (p : 𝔸ₚ) ^ k * (((m.factorial : ℕ) : 𝔸ₚ) * e - algebraMap 𝔸 𝔸ₚ b) := by
        rw [map_sub, map_mul, map_pow, map_natCast]
        ring
      rw [h3]
      exact Ideal.add_mem _ (Ideal.add_mem _ (neg_mem ha)
        (Ideal.mul_mem_left _ _ hek)) (Ideal.mul_mem_left _ _ hb)
    obtain ⟨c, hc⟩ := mem_span_singleton'.mp (mem_span_pow_of_algebraMap_mem hgen m h2)
    exact ⟨b, c, by linear_combination -hc⟩
  have hia : algebraMap 𝔸 𝔸ₚ a ∈ 𝕀 ^ m := by
    obtain ⟨c, rfl⟩ := mem_span_singleton'.mp hmem
    rw [ker_fontaineThetaInvertP_pow_eq_span_pow hgen, map_mul, map_pow]
    exact Ideal.mul_mem_left _ _ (mem_span_singleton_self _)
  have hmy : ((m.factorial : ℕ) : 𝔸ₚ) * y ∈ 𝕀 ^ m := by
    have := Ideal.add_mem _ ha hia
    rwa [sub_add_cancel] at this
  obtain ⟨u, hu⟩ := isUnit_natCast_factorial (p := p) m
  have hyu : y = ↑u⁻¹ * (((m.factorial : ℕ) : 𝔸ₚ) * y) := by
    rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
  rw [hyu]
  exact Ideal.mul_mem_left _ _ hmy

end Separated

end PadicComplexInt
