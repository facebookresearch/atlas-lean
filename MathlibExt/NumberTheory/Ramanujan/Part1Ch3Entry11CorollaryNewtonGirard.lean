/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Corollary to Entry 11

Newton's identity relates elementary symmetric and power sums.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry11CorollaryNewtonGirard

/-- A `HasSum` limit can be computed along any monotone cover of the index type
by finite sets. -/
private theorem tendsto_sum_exhaust {α : Type*} {f : α → ℂ} {s : ℂ} (hs : HasSum f s)
    (G : ℕ → Finset α) (hsub : ∀ N M : ℕ, N ≤ M → G N ⊆ G M)
    (hcover : ∀ x, ∃ N, x ∈ G N) :
    Filter.Tendsto (fun N => ∑ x ∈ G N, f x) Filter.atTop (nhds s) := by
  have hG : Filter.Tendsto G Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro F₀
    rw [Filter.eventually_atTop]
    have hwit : ∀ x, x ∈ F₀ → ∃ N, x ∈ G N := fun x _ => hcover x
    choose N hN using hwit
    refine ⟨F₀.attach.sup (fun x => N x x.2), fun M hM => ?_⟩
    show F₀ ⊆ G M
    intro x hx
    have hle : N x hx ≤ F₀.attach.sup (fun x => N x x.2) :=
      Finset.le_sup (f := fun (x : {x // x ∈ F₀}) => N x x.2)
        (Finset.mem_attach _ ⟨x, hx⟩)
    exact hsub _ _ (le_trans hle hM) (hN x hx)
  exact hs.comp hG

/-- Truncated elementary symmetric sums converge to `e m`. -/
private theorem tendsto_powersetCard_prods (a : ℕ → ℂ) (e : ℕ → ℂ)
    (he : ∀ n : ℕ,
      HasSum (fun s : { s : Finset ℕ // s.card = n } => ∏ j ∈ (s : Finset ℕ), a j)
        (e n))
    (m : ℕ) :
    Filter.Tendsto (fun N => ∑ t ∈ (Finset.range N).powersetCard m, ∏ j ∈ t, a j)
      Filter.atTop (nhds (e m)) := by
  let G : ℕ → Finset { s : Finset ℕ // s.card = m } := fun N =>
    ((Finset.range N).powersetCard m).attach.image
      (fun t => (⟨t.1, (Finset.mem_powersetCard.mp t.2).2⟩ :
        { s : Finset ℕ // s.card = m }))
  have hsum : ∀ N, (∑ x ∈ G N, ∏ j ∈ (x : Finset ℕ), a j)
      = ∑ t ∈ (Finset.range N).powersetCard m, ∏ j ∈ t, a j := by
    intro N
    have hinj : Set.InjOn (fun t : { t : Finset ℕ // t ∈ (Finset.range N).powersetCard m } =>
        (⟨t.1, (Finset.mem_powersetCard.mp t.2).2⟩ : { s : Finset ℕ // s.card = m }))
        ↑(((Finset.range N).powersetCard m).attach) := by
      intro x _ y _ hxy
      apply Subtype.ext
      simpa using hxy
    calc (∑ x ∈ G N, ∏ j ∈ (x : Finset ℕ), a j)
        = ∑ t ∈ ((Finset.range N).powersetCard m).attach, ∏ j ∈ (t : Finset ℕ), a j :=
          Finset.sum_image hinj
      _ = ∑ t ∈ (Finset.range N).powersetCard m, ∏ j ∈ t, a j :=
          Finset.sum_attach _ (fun s => ∏ j ∈ s, a j)
  have hsub : ∀ N M : ℕ, N ≤ M → G N ⊆ G M := by
    intro N M hNM y hy
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hy
    have hmem : t.1 ∈ (Finset.range M).powersetCard m := by
      have ht := Finset.mem_powersetCard.mp t.2
      refine Finset.mem_powersetCard.mpr ⟨fun x hx => ?_, ht.2⟩
      have hxN : x ∈ Finset.range N := ht.1 hx
      rw [Finset.mem_range] at hxN ⊢
      omega
    exact Finset.mem_image.mpr ⟨⟨t.1, hmem⟩, Finset.mem_attach _ _, rfl⟩
  have hcover : ∀ x : { s : Finset ℕ // s.card = m }, ∃ N, x ∈ G N := by
    rintro ⟨s, hs⟩
    obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range s
    have hmemN : s ∈ (Finset.range N).powersetCard m :=
      Finset.mem_powersetCard.mpr ⟨hN, hs⟩
    exact ⟨N, Finset.mem_image.mpr ⟨⟨s, hmemN⟩, Finset.mem_attach _ _, rfl⟩⟩
  have hlim := tendsto_sum_exhaust (he m) G hsub hcover
  exact hlim.congr fun N => hsum N

/-- Truncated power sums converge to `p k`. -/
private theorem tendsto_range_pow (a : ℕ → ℂ) (p : ℕ → ℂ)
    (hp : ∀ k : ℕ, 1 ≤ k → HasSum (fun j : ℕ => (a j) ^ k) (p k))
    (k : ℕ) (hk : 1 ≤ k) :
    Filter.Tendsto (fun N => ∑ i ∈ Finset.range N, (a i) ^ k) Filter.atTop (nhds (p k)) :=
  (hp k hk).tendsto_sum_nat

/-- **Newton's identities for summable families.** Let $(a_j)_{j \ge 0}$ be a sequence of complex
numbers, and let $(e_n)_{n \ge 0}$ and $(p_k)_{k \ge 1}$ be complex numbers such that for every
$n$ the family $\prod_{j \in s} a_j$, indexed by the $n$-element finite sets $s$ of natural
numbers, is summable with sum $e_n$, and for every $k \ge 1$ the series $\sum_{j \ge 0} a_j^k$
is summable with sum $p_k$. Then for every natural number $n$,
$$n e_n = \sum_{k=1}^{n} (-1)^{k-1} p_k e_{n-k}.$$

No absolute summability of $(a_j)$ is assumed, and the case $n = 0$, where both sides vanish,
is included. -/
theorem ramanujan_part1_ch3_entry11_corollary_newton_girard_general
    (a : ℕ → ℂ) (e : ℕ → ℂ) (p : ℕ → ℂ)
    (he : ∀ n : ℕ,
        HasSum (fun s : { s : Finset ℕ // s.card = n } => ∏ j ∈ (s : Finset ℕ), a j) (e n))
    (hp : ∀ k : ℕ, 1 ≤ k → HasSum (fun j : ℕ => (a j) ^ k) (p k)) :
    ∀ n : ℕ, (n : ℂ) * e n = ∑ k ∈ Finset.Icc 1 n, (-1 : ℂ) ^ (k - 1) * p k * e (n - k) := by
  -- `ha` is redundant: `he` and `hp` already supply all the convergence used below.
  intro n
  have hE : ∀ m : ℕ, Filter.Tendsto
      (fun N => ∑ t ∈ (Finset.range N).powersetCard m, ∏ j ∈ t, a j)
      Filter.atTop (nhds (e m)) :=
    fun m => tendsto_powersetCard_prods a e he m
  have hP : ∀ k : ℕ, 1 ≤ k → Filter.Tendsto
      (fun N => ∑ i ∈ Finset.range N, (a i) ^ k) Filter.atTop (nhds (p k)) :=
    fun k hk => tendsto_range_pow a p hp k hk
  have key : ∀ N : ℕ, (n : ℂ) * (∑ t ∈ (Finset.range N).powersetCard n, ∏ j ∈ t, a j)
      = (-1 : ℂ) ^ (n + 1) * ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal n).filter
          (fun x => x.1 < n),
          (-1 : ℂ) ^ x.1 * (∑ t ∈ (Finset.range N).powersetCard x.1, ∏ j ∈ t, a j)
            * (∑ i ∈ Finset.range N, (a i) ^ x.2) := by
    intro N
    have hE_eval : ∀ m : ℕ, MvPolynomial.aeval (fun i : Fin N => a (i : ℕ))
          (MvPolynomial.esymm (Fin N) ℂ m)
        = ∑ t ∈ (Finset.range N).powersetCard m, ∏ j ∈ t, a j := by
      intro m
      have hbridge : (∑ t ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)),
            ∏ i ∈ t, a (i : ℕ))
          = ∑ t ∈ (Finset.range N).powersetCard m, ∏ j ∈ t, a j := by
        have hmap : Finset.map (⟨Fin.val, Fin.val_injective⟩ : Fin N ↪ ℕ) Finset.univ
            = Finset.range N := by
          ext i
          simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_range]
          constructor
          · rintro ⟨j, rfl⟩
            exact j.isLt
          · intro h
            exact ⟨⟨i, h⟩, rfl⟩
        have hpc := Finset.powersetCard_map (⟨Fin.val, Fin.val_injective⟩ : Fin N ↪ ℕ) m
          (Finset.univ : Finset (Fin N))
        rw [hmap] at hpc
        rw [hpc, Finset.sum_map]
        refine Finset.sum_congr rfl (fun t _ => ?_)
        show (∏ i ∈ t, a (i : ℕ)) = ∏ j ∈ (Finset.mapEmbedding
          (⟨Fin.val, Fin.val_injective⟩ : Fin N ↪ ℕ)).toEmbedding t, a j
        show (∏ i ∈ t, a (i : ℕ)) = ∏ j ∈ t.map
          (⟨Fin.val, Fin.val_injective⟩ : Fin N ↪ ℕ), a j
        exact (Finset.prod_map t (⟨Fin.val, Fin.val_injective⟩ : Fin N ↪ ℕ) a).symm
      show MvPolynomial.aeval _
        (∑ t ∈ Finset.powersetCard m Finset.univ, ∏ i ∈ t, MvPolynomial.X i) = _
      rw [map_sum]
      simp only [map_prod, MvPolynomial.aeval_X]
      exact hbridge
    have hP_eval : ∀ k : ℕ, MvPolynomial.aeval (fun i : Fin N => a (i : ℕ))
          (MvPolynomial.psum (Fin N) ℂ k)
        = ∑ i ∈ Finset.range N, (a i) ^ k := by
      intro k
      show MvPolynomial.aeval _ (∑ i, MvPolynomial.X i ^ k) = _
      rw [map_sum]
      simp only [map_pow, MvPolynomial.aeval_X]
      exact Fin.sum_univ_eq_sum_range (fun i => (a i) ^ k) N
    have hpoly := MvPolynomial.mul_esymm_eq_sum (Fin N) ℂ n
    have heval := congrArg (MvPolynomial.aeval (fun i : Fin N => a (i : ℕ))) hpoly
    simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum,
      hE_eval, hP_eval] at heval
    exact heval
  have hLHS : Filter.Tendsto
      (fun N => (n : ℂ) * (∑ t ∈ (Finset.range N).powersetCard n, ∏ j ∈ t, a j))
      Filter.atTop (nhds ((n : ℂ) * e n)) :=
    Filter.Tendsto.const_mul _ (hE n)
  have hterm : ∀ x ∈ (Finset.HasAntidiagonal.antidiagonal n).filter (fun x => x.1 < n),
      Filter.Tendsto (fun N => (-1 : ℂ) ^ x.1 *
          (∑ t ∈ (Finset.range N).powersetCard x.1, ∏ j ∈ t, a j) *
          (∑ i ∈ Finset.range N, (a i) ^ x.2))
        Filter.atTop (nhds ((-1 : ℂ) ^ x.1 * e x.1 * p x.2)) := by
    intro x hx
    have hx2 : 1 ≤ x.2 := by
      rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hx
      omega
    exact (tendsto_const_nhds.mul (hE x.1)).mul (hP x.2 hx2)
  have hRHS : Filter.Tendsto (fun N => (-1 : ℂ) ^ (n + 1) * ∑ x ∈
        (Finset.HasAntidiagonal.antidiagonal n).filter (fun x => x.1 < n),
        (-1 : ℂ) ^ x.1 * (∑ t ∈ (Finset.range N).powersetCard x.1, ∏ j ∈ t, a j) *
          (∑ i ∈ Finset.range N, (a i) ^ x.2))
      Filter.atTop (nhds ((-1 : ℂ) ^ (n + 1) * ∑ x ∈
        (Finset.HasAntidiagonal.antidiagonal n).filter (fun x => x.1 < n),
        (-1 : ℂ) ^ x.1 * e x.1 * p x.2)) :=
    Filter.Tendsto.const_mul _
      (tendsto_finsetSum _ (fun x hx => hterm x hx))
  have heq : (n : ℂ) * e n = (-1 : ℂ) ^ (n + 1) * ∑ x ∈
      (Finset.HasAntidiagonal.antidiagonal n).filter (fun x => x.1 < n),
      (-1 : ℂ) ^ x.1 * e x.1 * p x.2 :=
    tendsto_nhds_unique (hLHS.congr fun N => key N) hRHS
  have hrearr : (-1 : ℂ) ^ (n + 1) * ∑ x ∈
      (Finset.HasAntidiagonal.antidiagonal n).filter (fun x => x.1 < n),
      (-1 : ℂ) ^ x.1 * e x.1 * p x.2
      = ∑ k ∈ Finset.Icc 1 n, (-1 : ℂ) ^ (k - 1) * p k * e (n - k) := by
    rw [Finset.mul_sum]
    refine (Finset.sum_bij (fun k _ => (n - k, k)) ?_ ?_ ?_ ?_).symm
    · intro k hk
      rw [Finset.mem_Icc] at hk
      rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal]
      show (n - k) + k = n ∧ (n - k) < n
      exact ⟨Nat.sub_add_cancel hk.2, Nat.sub_lt (by omega) hk.1⟩
    · intro k1 _ k2 _ h
      exact congrArg Prod.snd h
    · intro x hx
      rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hx
      refine ⟨x.2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      have h1 : n - x.2 = x.1 := by omega
      have h2 : (n - x.2, x.2) = x := by simp only [h1, Prod.mk.eta]
      exact h2
    · intro k hk
      rw [Finset.mem_Icc] at hk
      have hexp : (n + 1) + (n - k) = 2 * (n - k + 1) + (k - 1) := by omega
      have hsign : (-1 : ℂ) ^ ((n + 1) + (n - k)) = (-1 : ℂ) ^ (k - 1) := by
        rw [hexp, pow_add, Even.neg_one_pow (even_iff_two_dvd.mpr ⟨n - k + 1, rfl⟩),
          one_mul]
      calc (-1 : ℂ) ^ (k - 1) * p k * e (n - k)
          = (-1 : ℂ) ^ (k - 1) * (p k * e (n - k)) := by ring
        _ = (-1 : ℂ) ^ ((n + 1) + (n - k)) * (e (n - k) * p k) := by
            rw [hsign]; ring
        _ = (-1 : ℂ) ^ (n + 1) * ((-1 : ℂ) ^ (n - k) * e (n - k) * p k) := by
            rw [pow_add]; ring
  exact heq.trans hrearr

set_option linter.unusedVariables false in
/-- **Newton's identities for absolutely summable sequences.** Let $(a_j)_{j \ge 0}$ be a sequence
of complex numbers with $\sum_j |a_j| < \infty$. Let $(e_n)_{n \ge 0}$ and $(p_k)_{k \ge 1}$ be
complex numbers such that for every $n$ the family $\prod_{j \in s} a_j$, indexed by the
$n$-element finite sets $s$ of natural numbers, is summable with sum $e_n$, and for every
$k \ge 1$ the series $\sum_{j \ge 0} a_j^k$ is summable with sum $p_k$. Then for every $n \ge 1$,
$$n e_n = \sum_{k=1}^{n} (-1)^{k-1} p_k e_{n-k}.$$

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Corollary to Entry 11, printed p.
    66 / PDF p. 76.
Proves `Wanted` entry `ramanujan_part1_ch3_entry11_corollary_newton_girard`.
-/
theorem ramanujan_part1_ch3_entry11_corollary_newton_girard
    (a : ℕ → ℂ) (e : ℕ → ℂ) (p : ℕ → ℂ)
    (ha : Summable (fun j : ℕ => ‖a j‖))
    (he : ∀ n : ℕ,
        HasSum (fun s : { s : Finset ℕ // s.card = n } => ∏ j ∈ (s : Finset ℕ), a j) (e n))
    (hp : ∀ k : ℕ, 1 ≤ k → HasSum (fun j : ℕ => (a j) ^ k) (p k)) :
    ∀ n : ℕ, 1 ≤ n → (n : ℂ) * e n = ∑ k ∈ Finset.Icc 1 n, (-1 : ℂ) ^ (k - 1) * p k * e (n - k) :=
  fun n _ => ramanujan_part1_ch3_entry11_corollary_newton_girard_general a e p he hp n

end Entry11CorollaryNewtonGirard

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
