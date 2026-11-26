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
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice

/-!
# Prime m-tuples with smooth gaps

Given the Maynard–Tao hypothesis for `m` and `k` (every admissible set of at least `k`
integers yields `m` primes infinitely often), there are infinitely many prime `m`-tuples
whose gaps are `k`-smooth. The proof applies the hypothesis to an admissible,
difference-`k`-smooth set of `k` integers (`exists_admissible_differenceSmooth`) and extracts
a fixed `m`-subset occurring infinitely often.

Source: Carol Wu, *On Smooth Gaps between Primes Using the Maynard-Tao Sieve*,
INTEGERS 25 (2025), Article A44 (arXiv:2403.19696).
-/

namespace MetaMathlibExt

@[expose] public section

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
  obtain ⟨H, hHcard, hHadm, hHsmooth⟩ := exists_admissible_differenceSmooth k
  have hHle : k ≤ H.card := by rw [hHcard]
  have hS_inf := hk H hHadm hHle
  by_cases hmk : m ≤ k
  · -- Cover S by the sets where a fixed m-subset is prime
    have hcover : {n : ℤ | m ≤ (H.filter
        (fun h => (n + h).toNat.Prime)).card} ⊆
        ⋃ T ∈ (↑(H.powersetCard m) : Set (Finset ℤ)),
          {n : ℤ | T ⊆ H.filter
            (fun h => (n + h).toNat.Prime)} := by
      intro n hn
      have hn_le : m ≤ (H.filter
        (fun h => (n + h).toNat.Prime)).card := hn
      obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hn_le
      have hTH : T ⊆ H := hTsub.trans (Finset.filter_subset _ _)
      have hTmem : T ∈ H.powersetCard m :=
        Finset.mem_powersetCard.mpr ⟨hTH, hTcard⟩
      exact Set.mem_biUnion (Finset.mem_coe.mpr hTmem) hTsub
    obtain ⟨T0, hT0mem, hN0inf⟩ := exists_infinite_inter_of_infinite_cover hS_inf
      (H.powersetCard m)
      (fun T => {n : ℤ | T ⊆ H.filter
        (fun h => (n + h).toNat.Prime)})
      hcover
    have hT0subcard : T0 ⊆ H ∧ T0.card = m :=
      Finset.mem_powersetCard.mp hT0mem
    have hT0sub : T0 ⊆ H := hT0subcard.1
    have hT0card : T0.card = m := hT0subcard.2
    let e := T0.orderEmbOfFin hT0card
    let f : ℤ → (Fin m → ℕ) := fun n i => (n + e i).toNat
    have hprime : ∀ n ∈ ({n : ℤ | m ≤ (H.filter
        (fun h => (n + h).toNat.Prime)).card} ∩
        {n : ℤ | T0 ⊆ H.filter
          (fun h => (n + h).toNat.Prime)}),
        ∀ i : Fin m, (n + e i).toNat.Prime := by
      intro n hn i
      have hnU : T0 ⊆ H.filter
        (fun h => (n + h).toNat.Prime) := hn.2
      have hei : e i ∈ T0 := Finset.orderEmbOfFin_mem T0 hT0card i
      have hmem := hnU hei
      exact (Finset.mem_filter.mp hmem).2
    have hgood : ∀ n ∈ ({n : ℤ | m ≤ (H.filter
        (fun h => (n + h).toNat.Prime)).card} ∩
        {n : ℤ | T0 ⊆ H.filter
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
          (Int.toNat_sub'' (h0j.trans hle) h0j).symm
        have heq : (n + e i) - (n + e j) = e i - e j := by omega
        rw [heq] at hsub
        have hnonneg : 0 ≤ e i - e j := by omega
        have htat : (e i - e j).toNat = (e i - e j).natAbs :=
          toNat_eq_natAbs_of_nonneg hnonneg
        rw [htat] at hsub
        have hmem_i : e i ∈ H :=
          hT0sub (Finset.orderEmbOfFin_mem T0 hT0card i)
        have hmem_j : e j ∈ H :=
          hT0sub (Finset.orderEmbOfFin_mem T0 hT0card j)
        have hne : e i ≠ e j := ne_of_gt he_lt
        have hsmooth : (e i - e j).natAbs ∈ Nat.smoothNumbers (k + 1) :=
          hHsmooth _ hmem_i _ hmem_j hne
        have hsmooth' : (n + e i).toNat - (n + e j).toNat ∈ Nat.smoothNumbers (k + 1) := by
          rw [hsub]
          exact hsmooth
        exact ⟨hto_lt, hsmooth'⟩
    have hinj : Set.InjOn f ({n : ℤ | m ≤ (H.filter
        (fun h => (n + h).toNat.Prime)).card} ∩
        {n : ℤ | T0 ⊆ H.filter
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
    have himg_inf : (f '' ({n : ℤ | m ≤ (H.filter
        (fun h => (n + h).toNat.Prime)).card} ∩
        {n : ℤ | T0 ⊆ H.filter
          (fun h => (n + h).toNat.Prime)})).Infinite :=
      Set.Infinite.image hinj hN0inf
    have hsub : f '' ({n : ℤ | m ≤ (H.filter
        (fun h => (n + h).toNat.Prime)).card} ∩
        {n : ℤ | T0 ⊆ H.filter
          (fun h => (n + h).toNat.Prime)}) ⊆
        {P : Fin m → ℕ | (∀ i, (P i).Prime) ∧
          ∀ i j, j < i → P j < P i ∧ P i - P j ∈ Nat.smoothNumbers (k + 1)} := by
      intro P hP
      obtain ⟨n, hn, rfl⟩ := hP
      exact hgood n hn
    exact Set.Infinite.mono hsub himg_inf
  · push Not at hmk
    have hS_empty : {n : ℤ | m ≤ (H.filter
        (fun h => (n + h).toNat.Prime)).card} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro n hn
      have hn_le : m ≤ ((H.filter
          (fun h => (n + h).toNat.Prime)).card) := hn
      have hle : ((H.filter
          (fun h => (n + h).toNat.Prime)).card) ≤ k := by
        calc _ ≤ H.card := Finset.card_filter_le _ _
             _ = k := hHcard
      omega
    rw [hS_empty] at hS_inf
    exact False.elim (hS_inf.not_finite Set.finite_empty)

end

end MetaMathlibExt
