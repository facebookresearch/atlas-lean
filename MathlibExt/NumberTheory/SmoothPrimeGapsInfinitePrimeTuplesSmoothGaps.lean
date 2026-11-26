/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SmoothPrimeGaps
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.ZMod.Basic

/-!
# Prime m-tuples with smooth gaps

Given the Maynard–Tao hypothesis for `m` and `k` (every admissible set of at least `k`
integers yields `m` primes infinitely often), there are infinitely many prime `m`-tuples
whose gaps are `k`-smooth. The proof applies the hypothesis to the admissible,
difference-`k`-smooth set `{0, k!, …, (k-1) * k!}` and extracts a fixed `m`-subset
occurring infinitely often.

Source: Carol Wu, *On Smooth Gaps between Primes Using the Maynard-Tao Sieve*,
INTEGERS 25 (2025), Article A44 (arXiv:2403.19696).
-/

namespace MetaMathlibExt

@[expose] public section

/-- The set `{0, k!, …, (k-1) * k!}` as a `Finset ℤ`. -/
private def smoothAdmissibleSet (k : ℕ) : Finset ℤ :=
  (Finset.range k).image (fun i => ((i * k.factorial : ℕ) : ℤ))

/-- The set `smoothAdmissibleSet k` has `k` elements. -/
private theorem card_smoothAdmissibleSet (k : ℕ) :
    (smoothAdmissibleSet k).card = k := by
  unfold smoothAdmissibleSet
  rw [Finset.card_image_of_injective]
  · exact Finset.card_range k
  · intro a b hab
    simp only at hab
    have hcast : a * k.factorial = b * k.factorial := by exact_mod_cast hab
    exact Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos k) hcast

/-- For prime `p ≤ k`, the factorial `k!` vanishes in `ZMod p`. -/
private theorem zmod_factorial_eq_zero {p k : ℕ} (hp : p.Prime) (hpk : p ≤ k) :
    ((k.factorial : ℕ) : ZMod p) = 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hdvd : p ∣ k.factorial := (hp.dvd_factorial).mpr hpk
  obtain ⟨t, ht⟩ := hdvd
  rw [ht, Nat.cast_mul, ZMod.natCast_self, zero_mul]

/-- The set `smoothAdmissibleSet k` is admissible. -/
private theorem isAdmissible_smoothAdmissibleSet (k : ℕ) :
    IsAdmissibleFinset (smoothAdmissibleSet k) := by
  intro p hp
  have := Fact.mk hp
  by_cases hpk : p ≤ k
  · have hK : ((k.factorial : ℕ) : ZMod p) = 0 := zmod_factorial_eq_zero hp hpk
    refine ⟨1, fun h hh heq => ?_⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hh
    have h0 : (((i * k.factorial : ℕ) : ℤ) : ZMod p) = 0 := by
      rw [Int.cast_natCast, Nat.cast_mul, hK, mul_zero]
    exact zero_ne_one (h0.symm.trans heq)
  · push Not at hpk
    have himg : ((smoothAdmissibleSet k).image fun h : ℤ => (h : ZMod p)).card <
        Fintype.card (ZMod p) := by
      rw [ZMod.card]
      have hle : ((smoothAdmissibleSet k).image fun h : ℤ => (h : ZMod p)).card ≤ k := by
        calc _ ≤ (smoothAdmissibleSet k).card := Finset.card_image_le
             _ = k := card_smoothAdmissibleSet k
      exact hle.trans_lt hpk
    obtain ⟨r, -, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := (smoothAdmissibleSet k).image fun h : ℤ => (h : ZMod p)) (t := Finset.univ)
      (by simpa using himg)
    exact ⟨r, fun h hh hEq => hr (Finset.mem_image.mpr ⟨h, hh, hEq⟩)⟩

/-- The factorial `k!` is `(k+1)`-smooth. -/
private theorem factorial_mem_smoothNumbers (k : ℕ) :
    k.factorial ∈ Nat.smoothNumbers (k + 1) := by
  rw [Nat.mem_smoothNumbers']
  intro p hp hdvd
  have hle : p ≤ k := (hp.dvd_factorial).mp hdvd
  exact Nat.lt_succ_of_le hle

/-- The set `smoothAdmissibleSet k` is difference-`k`-smooth. -/
private theorem isDifferenceSmooth_smoothAdmissibleSet (k : ℕ) :
    IsDifferenceSmooth k (smoothAdmissibleSet k) := by
  intro a ha b hb hab
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
  simp only [Finset.mem_range] at hi hj
  rcases le_total i j with hle | hle
  · have hne : i ≠ j := by
      intro heq
      apply hab
      rw [heq]
    have hlt : i < j := lt_of_le_of_ne hle hne
    have hmul_le : i * k.factorial ≤ j * k.factorial :=
      Nat.mul_le_mul_right _ hle
    have hnat : ((↑(i * k.factorial) : ℤ) - (↑(j * k.factorial) : ℤ)).natAbs =
        (j - i) * k.factorial := by
      rw [Int.natAbs_natCast_sub_natCast_of_le hmul_le]
      rw [← Nat.mul_sub_right_distrib]
    rw [hnat]
    have hd_pos : 0 < j - i := Nat.sub_pos_of_lt hlt
    have hd_lt : j - i < k + 1 := lt_of_le_of_lt (Nat.sub_le j i) (Nat.lt_succ_of_le (le_of_lt hj))
    have hd_smooth : (j - i) ∈ Nat.smoothNumbers (k + 1) :=
      Nat.mem_smoothNumbers_of_lt hd_pos hd_lt
    exact Nat.mul_mem_smoothNumbers hd_smooth (factorial_mem_smoothNumbers k)
  · have hne : j ≠ i := by
      intro heq
      apply hab
      rw [heq]
    have hlt : j < i := lt_of_le_of_ne hle hne
    have hmul_le : j * k.factorial ≤ i * k.factorial :=
      Nat.mul_le_mul_right _ hle
    have hnat : ((↑(i * k.factorial) : ℤ) - (↑(j * k.factorial) : ℤ)).natAbs =
        (i - j) * k.factorial := by
      rw [Int.natAbs_natCast_sub_natCast_of_ge hmul_le]
      rw [← Nat.mul_sub_right_distrib]
    rw [hnat]
    have hd_pos : 0 < i - j := Nat.sub_pos_of_lt hlt
    have hd_lt : i - j < k + 1 := lt_of_le_of_lt (Nat.sub_le i j) (Nat.lt_succ_of_le (le_of_lt hi))
    have hd_smooth : (i - j) ∈ Nat.smoothNumbers (k + 1) :=
      Nat.mem_smoothNumbers_of_lt hd_pos hd_lt
    exact Nat.mul_mem_smoothNumbers hd_smooth (factorial_mem_smoothNumbers k)

/-- If an infinite set is covered by finitely many sets, some intersection is infinite. -/
private theorem exists_infinite_inter_of_infinite_cover {α : Type*} {S : Set α}
    (hS : S.Infinite) {ι : Type*} (F : Finset ι) (U : ι → Set α)
    (hcover : S ⊆ ⋃ T ∈ (↑F : Set ι), U T) :
    ∃ T ∈ F, (S ∩ U T).Infinite := by
  by_contra hcon
  push Not at hcon
  have hfin : ∀ T ∈ (↑F : Set ι), (S ∩ U T).Finite := by
    intro T hT
    exact hcon T (Finset.mem_coe.mp hT)
  have hunion_fin : (⋃ T ∈ (↑F : Set ι), (S ∩ U T)).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet F) hfin
  have hsub : S ⊆ ⋃ T ∈ (↑F : Set ι), (S ∩ U T) := by
    intro x hx
    have hxU := hcover hx
    simp only [Set.mem_iUnion, Finset.mem_coe] at hxU ⊢
    obtain ⟨T, hTF, hxT⟩ := hxU
    exact ⟨T, hTF, hx, hxT⟩
  exact hS.not_finite (hunion_fin.subset hsub)

/-- If `x.toNat` is prime then `0 < x`. -/
private theorem pos_of_toNat_prime {x : ℤ} (hp : x.toNat.Prime) : 0 < x := by
  have hne : x.toNat ≠ 0 := hp.ne_zero
  have hnot : ¬ x ≤ 0 := fun hle => hne (Int.toNat_eq_zero.mpr hle)
  exact not_le.mp hnot

/-- For `0 ≤ A ≤ B`, the difference of `toNat`s is the `toNat` of the difference. -/
private theorem toNat_sub_eq_toNat_sub {A B : ℤ} (h0 : 0 ≤ A) (hle : A ≤ B) :
    B.toNat - A.toNat = (B - A).toNat := by
  have hBA : 0 ≤ B - A := by omega
  have hB0 : 0 ≤ B := by omega
  have hcast1 : ((B.toNat : ℕ) : ℤ) = B := Int.toNat_of_nonneg hB0
  have hcast2 : ((A.toNat : ℕ) : ℤ) = A := Int.toNat_of_nonneg h0
  have hcast3 : (((B - A).toNat : ℕ) : ℤ) = B - A := Int.toNat_of_nonneg hBA
  have hle_nat : A.toNat ≤ B.toNat := Int.toNat_le_toNat hle
  have hcast_sub : (((B.toNat - A.toNat : ℕ)) : ℤ) = B - A := by
    rw [Nat.cast_sub hle_nat, hcast1, hcast2]
  have h_eq : (((B.toNat - A.toNat : ℕ)) : ℤ) = (((B - A).toNat : ℕ) : ℤ) :=
    hcast_sub.trans hcast3.symm
  exact_mod_cast h_eq

/-- For `0 ≤ x`, `toNat` equals `natAbs`. -/
private theorem toNat_eq_natAbs_of_nonneg {x : ℤ} (hx : 0 ≤ x) : x.toNat = x.natAbs := by
  have h1 : ((x.toNat : ℕ) : ℤ) = x := Int.toNat_of_nonneg hx
  have h2 : ((x.natAbs : ℕ) : ℤ) = x := Int.natAbs_of_nonneg hx
  have h3 : ((x.toNat : ℕ) : ℤ) = ((x.natAbs : ℕ) : ℤ) := h1.trans h2.symm
  exact_mod_cast h3

/-- **Prime $m$-tuples with smooth gaps.** Let $m \ge 2$ and $k$ be natural numbers such that
every admissible finite set $H$ of at least $k$ integers has infinitely many integers $n$ for
which $n + h$ is a (positive) prime for at least $m$ elements $h \in H$. Then there are
infinitely many $m$-tuples of primes $p_1 < p_2 < \dots < p_m$ such that for all $j < i$ every
prime factor of $p_i - p_j$ is at most $k$.

Equivalently, every gap is $y$-smooth for $y$ the largest prime at most $k$; the paper applies
this with the admissible values $k_m$ of the Maynard–Tao theorem listed in its Table 1.

Source: Carol Wu, *On Smooth Gaps between Primes Using the Maynard-Tao Sieve*,
INTEGERS 25 (2025), Article A44, Theorem 3 (`integers-2025-A44-thm-3`). -/
public theorem infinite_prime_tuples_smooth_gaps (m k : ℕ) (hm : 2 ≤ m)
    (hk : ∀ H : Finset ℤ, IsAdmissibleFinset H → k ≤ H.card →
      {n : ℤ | m ≤ (H.filter (fun h => (n + h).toNat.Prime)).card}.Infinite) :
    {P : Fin m → ℕ | (∀ i, (P i).Prime) ∧
      ∀ i j, j < i → P j < P i ∧ P i - P j ∈ Nat.smoothNumbers (k + 1)}.Infinite := by
  have hHcard : (smoothAdmissibleSet k).card = k := card_smoothAdmissibleSet k
  have hHadm : IsAdmissibleFinset (smoothAdmissibleSet k) :=
    isAdmissible_smoothAdmissibleSet k
  have hHsmooth : IsDifferenceSmooth k (smoothAdmissibleSet k) :=
    isDifferenceSmooth_smoothAdmissibleSet k
  have hHle : k ≤ (smoothAdmissibleSet k).card := by rw [hHcard]
  have hS_inf := hk (smoothAdmissibleSet k) hHadm hHle
  by_cases hmk : m ≤ k
  · -- Cover S by the sets where a fixed m-subset is prime
    have hcover : {n : ℤ | m ≤ ((smoothAdmissibleSet k).filter
        (fun h => (n + h).toNat.Prime)).card} ⊆
        ⋃ T ∈ (↑((smoothAdmissibleSet k).powersetCard m) : Set (Finset ℤ)),
          {n : ℤ | T ⊆ (smoothAdmissibleSet k).filter
            (fun h => (n + h).toNat.Prime)} := by
      intro n hn
      have hn_le : m ≤ ((smoothAdmissibleSet k).filter
        (fun h => (n + h).toNat.Prime)).card := hn
      obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hn_le
      have hTH : T ⊆ smoothAdmissibleSet k := hTsub.trans (Finset.filter_subset _ _)
      have hTmem : T ∈ (smoothAdmissibleSet k).powersetCard m :=
        Finset.mem_powersetCard.mpr ⟨hTH, hTcard⟩
      exact Set.mem_biUnion (Finset.mem_coe.mpr hTmem) hTsub
    obtain ⟨T0, hT0mem, hN0inf⟩ := exists_infinite_inter_of_infinite_cover hS_inf
      ((smoothAdmissibleSet k).powersetCard m)
      (fun T => {n : ℤ | T ⊆ (smoothAdmissibleSet k).filter
        (fun h => (n + h).toNat.Prime)})
      hcover
    have hT0subcard : T0 ⊆ smoothAdmissibleSet k ∧ T0.card = m :=
      Finset.mem_powersetCard.mp hT0mem
    have hT0sub : T0 ⊆ smoothAdmissibleSet k := hT0subcard.1
    have hT0card : T0.card = m := hT0subcard.2
    let e := T0.orderEmbOfFin hT0card
    let f : ℤ → (Fin m → ℕ) := fun n i => (n + e i).toNat
    have hprime : ∀ n ∈ ({n : ℤ | m ≤ ((smoothAdmissibleSet k).filter
        (fun h => (n + h).toNat.Prime)).card} ∩
        {n : ℤ | T0 ⊆ (smoothAdmissibleSet k).filter
          (fun h => (n + h).toNat.Prime)}),
        ∀ i : Fin m, (n + e i).toNat.Prime := by
      intro n hn i
      have hnU : T0 ⊆ (smoothAdmissibleSet k).filter
        (fun h => (n + h).toNat.Prime) := hn.2
      have hei : e i ∈ T0 := Finset.orderEmbOfFin_mem T0 hT0card i
      have hmem := hnU hei
      exact (Finset.mem_filter.mp hmem).2
    have hgood : ∀ n ∈ ({n : ℤ | m ≤ ((smoothAdmissibleSet k).filter
        (fun h => (n + h).toNat.Prime)).card} ∩
        {n : ℤ | T0 ⊆ (smoothAdmissibleSet k).filter
          (fun h => (n + h).toNat.Prime)}),
        f n ∈ {P : Fin m → ℕ | (∀ i, (P i).Prime) ∧
          ∀ i j, j < i → P j < P i ∧ P i - P j ∈ Nat.smoothNumbers (k + 1)} := by
      intro n hn
      have hpr : ∀ i : Fin m, (n + e i).toNat.Prime := hprime n hn
      constructor
      · intro i
        exact hpr i
      · intro i j hji
        have he_lt : e j < e i := (OrderEmbedding.lt_iff_lt e).mpr hji
        have hlt : n + e j < n + e i := by omega
        have hpos_i : 0 < n + e i := pos_of_toNat_prime (hpr i)
        have hto_lt : (n + e j).toNat < (n + e i).toNat :=
          (Int.toNat_lt_toNat hpos_i).mpr hlt
        have h0j : 0 ≤ n + e j := le_of_lt (pos_of_toNat_prime (hpr j))
        have hle : n + e j ≤ n + e i := le_of_lt hlt
        have hsub : (n + e i).toNat - (n + e j).toNat =
            ((n + e i) - (n + e j)).toNat :=
          toNat_sub_eq_toNat_sub h0j hle
        have heq : (n + e i) - (n + e j) = e i - e j := by omega
        rw [heq] at hsub
        have hnonneg : 0 ≤ e i - e j := by omega
        have htat : (e i - e j).toNat = (e i - e j).natAbs :=
          toNat_eq_natAbs_of_nonneg hnonneg
        rw [htat] at hsub
        have hmem_i : e i ∈ smoothAdmissibleSet k :=
          hT0sub (Finset.orderEmbOfFin_mem T0 hT0card i)
        have hmem_j : e j ∈ smoothAdmissibleSet k :=
          hT0sub (Finset.orderEmbOfFin_mem T0 hT0card j)
        have hne : e i ≠ e j := ne_of_gt he_lt
        have hsmooth : (e i - e j).natAbs ∈ Nat.smoothNumbers (k + 1) :=
          hHsmooth _ hmem_i _ hmem_j hne
        have hsmooth' : (n + e i).toNat - (n + e j).toNat ∈ Nat.smoothNumbers (k + 1) := by
          rw [hsub]
          exact hsmooth
        exact ⟨hto_lt, hsmooth'⟩
    have hinj : Set.InjOn f ({n : ℤ | m ≤ ((smoothAdmissibleSet k).filter
        (fun h => (n + h).toNat.Prime)).card} ∩
        {n : ℤ | T0 ⊆ (smoothAdmissibleSet k).filter
          (fun h => (n + h).toNat.Prime)}) := by
      intro n1 hn1 n2 hn2 heq
      have h0m : 0 < m := by omega
      let i0 : Fin m := ⟨0, h0m⟩
      have hto_eq : (n1 + e i0).toNat = (n2 + e i0).toNat := congrFun heq i0
      have hpr1 : (n1 + e i0).toNat.Prime := hprime n1 hn1 i0
      have hpr2 : (n2 + e i0).toNat.Prime := hprime n2 hn2 i0
      have hpos1 : 0 ≤ n1 + e i0 := le_of_lt (pos_of_toNat_prime hpr1)
      have hpos2 : 0 ≤ n2 + e i0 := le_of_lt (pos_of_toNat_prime hpr2)
      have hcast1 : (((n1 + e i0).toNat : ℕ) : ℤ) = n1 + e i0 :=
        Int.toNat_of_nonneg hpos1
      have hcast2 : (((n2 + e i0).toNat : ℕ) : ℤ) = n2 + e i0 :=
        Int.toNat_of_nonneg hpos2
      have hEq : n1 + e i0 = n2 + e i0 := by
        have hcast_eq : (((n1 + e i0).toNat : ℕ) : ℤ) =
            (((n2 + e i0).toNat : ℕ) : ℤ) := by rw [hto_eq]
        rw [hcast1, hcast2] at hcast_eq
        exact hcast_eq
      omega
    have himg_inf : (f '' ({n : ℤ | m ≤ ((smoothAdmissibleSet k).filter
        (fun h => (n + h).toNat.Prime)).card} ∩
        {n : ℤ | T0 ⊆ (smoothAdmissibleSet k).filter
          (fun h => (n + h).toNat.Prime)})).Infinite :=
      Set.Infinite.image hinj hN0inf
    have hsub : f '' ({n : ℤ | m ≤ ((smoothAdmissibleSet k).filter
        (fun h => (n + h).toNat.Prime)).card} ∩
        {n : ℤ | T0 ⊆ (smoothAdmissibleSet k).filter
          (fun h => (n + h).toNat.Prime)}) ⊆
        {P : Fin m → ℕ | (∀ i, (P i).Prime) ∧
          ∀ i j, j < i → P j < P i ∧ P i - P j ∈ Nat.smoothNumbers (k + 1)} := by
      intro P hP
      obtain ⟨n, hn, rfl⟩ := hP
      exact hgood n hn
    exact Set.Infinite.mono hsub himg_inf
  · push Not at hmk
    have hS_empty : {n : ℤ | m ≤ ((smoothAdmissibleSet k).filter
        (fun h => (n + h).toNat.Prime)).card} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro n hn
      have hn_le : m ≤ (((smoothAdmissibleSet k).filter
          (fun h => (n + h).toNat.Prime)).card) := hn
      have hle : (((smoothAdmissibleSet k).filter
          (fun h => (n + h).toNat.Prime)).card) ≤ k := by
        calc _ ≤ (smoothAdmissibleSet k).card := Finset.card_filter_le _ _
             _ = k := hHcard
      omega
    rw [hS_empty] at hS_inf
    exact False.elim (hS_inf.not_finite Set.finite_empty)

end

end MetaMathlibExt
