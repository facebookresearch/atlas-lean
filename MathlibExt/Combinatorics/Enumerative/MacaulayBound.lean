/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.lean`
and
`P2M/Sol/S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.Combinatorics.Enumerative.MacaulayPow
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finsupp.Weight
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Push

/-!
# Macaulay's bound for monomial shadows

Let `B` be a set of monomials of degree `d ≥ 1` in `n + 1` variables and let `C` be a set of
monomials of degree `d + 1` all of whose divisors of degree `d` lie in `B`. Then
`#C ≤ Nat.macaulayPow d #B`. This is the combinatorial core of Macaulay's bound on the growth of
Hilbert functions. The lower-shadow form for families of multisets, with Macaulay's lower function,
is `MetaMathlibExt.macaulay_multiset_shadow_minimal`.

The proof proceeds by induction on the number of variables in use, compressing the set towards
the last variable used and splitting the result by the exponent of that variable.

## Main declarations

* `Finsupp.card_le_macaulayPow_card_of_forall_sub_single_mem`: Macaulay's bound.

## References

* F. S. Macaulay, *Some properties of enumeration in the theory of modular systems*,
  Proc. London Math. Soc. 26 (1927), 531–555.
-/

namespace Finsupp

namespace MacaulayBoundAux

private theorem tower_bound : ∀ (e : ℕ) (b : ℕ → ℕ) (c : ℕ), b (e + 1) ≤ 1 →
    (1 ≤ b e → b (e + 1) = 1) →
    (∀ k, k + 2 ≤ e + 1 → b k ≤ Nat.macaulayPow (e - k) (b (k + 1))) →
    c ≤ Nat.macaulayPow (e + 1) (b 0) →
    c + ∑ k ∈ Finset.range (e + 2), b k ≤ Nat.macaulayPow (e + 1) (∑ k ∈ Finset.range (e + 2), b k)
  | 0, b, c, h1, h2, _, h4 => by
      have h1' : b 1 ≤ 1 := h1
      have h2' : 1 ≤ b 0 → b 1 = 1 := h2
      have h4' : c ≤ (b 0 + 1).choose 2 := by rw [Nat.macaulayPow_one] at h4; exact h4
      change c + ∑ k ∈ Finset.range 2, b k ≤ Nat.macaulayPow 1 (∑ k ∈ Finset.range 2, b k)
      rw [Finset.sum_range_succ, Finset.sum_range_one, Nat.macaulayPow_one]
      rcases Nat.eq_zero_or_pos (b 0) with h0 | h0
      · have hc : c = 0 := by rw [h0] at h4'; simpa using h4'
        rw [hc, h0, zero_add, zero_add]
        rcases (show b 1 = 0 ∨ b 1 = 1 by omega) with h | h <;> rw [h] <;> simp
      · have hb1 := h2' h0
        have hp : (b 0 + 1 + 1).choose 2 = (b 0 + 1) + (b 0 + 1).choose 2 := by
          have := Nat.choose_succ_succ' (b 0 + 1) 1; rw [Nat.choose_one_right] at this; exact this
        rw [hb1]; omega
  | e + 1, b, c, h1, h2, h3, h4 => by
      have ih := tower_bound e (fun k => b (k + 1)) (b 0) h1 h2
        (fun k hk => by
          have := h3 (k + 1) (by omega)
          rwa [show e + 1 - (k + 1) = e - k by omega] at this)
        (by have := h3 0 (by omega); rwa [Nat.sub_zero] at this)
      rw [Finset.sum_range_succ' b (e + 2)]
      have key :=
        Nat.macaulayPow_succ_add_le (e + 1) (b 0) (∑ k ∈ Finset.range (e + 2), b (k + 1)) ih
      rw [add_comm (b 0)] at key
      omega

variable (n : ℕ)

private noncomputable def Mon (e : ℕ) : Finset (Fin (n + 1) →₀ ℕ) :=
  ((Finsupp.finite_of_degree_le (σ := Fin (n + 1)) e).subset
    (fun m (hm : m ∈ {m : Fin (n + 1) →₀ ℕ | m.degree = e}) => le_of_eq hm)).toFinset

@[local simp] private theorem mem_Mon (e : ℕ) (m : Fin (n + 1) →₀ ℕ) :
    m ∈ Mon n e ↔ m.degree = e := by
  simp [Mon]

private noncomputable def MonW (w e : ℕ) : Finset (Fin (n + 1) →₀ ℕ) :=
  (Mon n e).filter (fun m => ∀ i : Fin (n + 1), w ≤ (i : ℕ) → m i = 0)

private theorem mem_MonW (w e : ℕ) (m : Fin (n + 1) →₀ ℕ) :
    m ∈ MonW n w e ↔ m.degree = e ∧ ∀ i : Fin (n + 1), w ≤ (i : ℕ) → m i = 0 := by
  simp [MonW]

private theorem MonW_zero_succ (e : ℕ) : MonW n 0 (e + 1) = ∅ := by
  ext u
  simp only [mem_MonW, Finset.notMem_empty, iff_false, not_and]
  intro hdeg hsupp
  have : u = 0 := by
    ext i; exact hsupp i (Nat.zero_le _)
  rw [this, map_zero] at hdeg
  omega

private theorem MonW_zero_right (w : ℕ) : MonW n w 0 = {0} := by
  ext u
  simp only [mem_MonW, Finset.mem_singleton, Finsupp.degree_eq_zero_iff]
  constructor
  · exact fun h => h.1
  · rintro rfl; simp

private noncomputable def Bplus (w e : ℕ) (B : Finset (Fin (n + 1) →₀ ℕ)) :
    Finset (Fin (n + 1) →₀ ℕ) :=
  (MonW n w (e + 1)).filter (fun u => ∀ i : Fin (n + 1), 1 ≤ u i → u - Finsupp.single i 1 ∈ B)

private theorem mem_Bplus (w e : ℕ) (B : Finset (Fin (n + 1) →₀ ℕ)) (u : Fin (n + 1) →₀ ℕ) :
    u ∈ Bplus n w e B ↔
      u ∈ MonW n w (e + 1) ∧ ∀ i : Fin (n + 1), 1 ≤ u i → u - Finsupp.single i 1 ∈ B := by
  simp [Bplus]

private theorem Bplus_subset_MonW (w e : ℕ) (B : Finset (Fin (n + 1) →₀ ℕ)) :
    Bplus n w e B ⊆ MonW n w (e + 1) :=
  Finset.filter_subset _ _

variable {n}

private theorem degree_sub_single (u : Fin (n + 1) →₀ ℕ) (i : Fin (n + 1)) (hu : 1 ≤ u i) :
    (u - Finsupp.single i 1).degree + 1 = u.degree := by
  conv_rhs => rw [← Finsupp.sub_add_single_one_cancel (u := u) (i := i) (by omega)]
  rw [map_add, Finsupp.degree_single]

private theorem exists_one_le_of_degree_ne_zero (u : Fin (n + 1) →₀ ℕ) (hu : u.degree ≠ 0) :
    ∃ i, 1 ≤ u i := by
  rw [Finsupp.degree_eq_sum] at hu
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu
  exact ⟨i, by omega⟩

section Compression

variable (i c : Fin (n + 1))

private noncomputable def mv (u : Fin (n + 1) →₀ ℕ) (j : ℕ) : Fin (n + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun l => if l = i then j else if l = c then u i + u c - j else u l

private noncomputable def key (u : Fin (n + 1) →₀ ℕ) : Fin (n + 1) →₀ ℕ := mv i c u 0

private noncomputable def J (A : Finset (Fin (n + 1) →₀ ℕ)) (m : Fin (n + 1) →₀ ℕ) : Finset ℕ :=
  (Finset.range (m c + 1)).filter fun j => mv i c m j ∈ A

private noncomputable def comp (A : Finset (Fin (n + 1) →₀ ℕ)) : Finset (Fin (n + 1) →₀ ℕ) :=
  (A.image (key i c)).biUnion fun m => (Finset.range (J i c A m).card).image (mv i c m)

private def wt (u : Fin (n + 1) →₀ ℕ) : ℕ := ∑ l ∈ Finset.univ.erase c, u l

private def pot (A : Finset (Fin (n + 1) →₀ ℕ)) : ℕ := ∑ u ∈ A, wt c u

private theorem mv_apply (u : Fin (n + 1) →₀ ℕ) (j : ℕ) (l : Fin (n + 1)) :
    mv i c u j l = if l = i then j else if l = c then u i + u c - j else u l := rfl

@[local simp] private theorem mv_apply_i (u : Fin (n + 1) →₀ ℕ) (j : ℕ) : mv i c u j i = j := by
  simp [mv_apply]

private theorem mem_J {A : Finset (Fin (n + 1) →₀ ℕ)} {m : Fin (n + 1) →₀ ℕ} {j : ℕ} :
    j ∈ J i c A m ↔ j ≤ m c ∧ mv i c m j ∈ A := by
  simp [J, Nat.lt_add_one_iff]

private theorem card_J_le (A : Finset (Fin (n + 1) →₀ ℕ)) (m : Fin (n + 1) →₀ ℕ) :
    (J i c A m).card ≤ m c + 1 :=
  (Finset.card_filter_le _ _).trans (by simp)

private theorem J_mono {A A' : Finset (Fin (n + 1) →₀ ℕ)} (h : A ⊆ A') (m : Fin (n + 1) →₀ ℕ) :
    J i c A m ⊆ J i c A' m := fun j hj => by
  rw [mem_J] at hj ⊢; exact ⟨hj.1, h hj.2⟩

private theorem mv_injective (u : Fin (n + 1) →₀ ℕ) : Function.Injective (mv i c u) :=
    fun j j' h => by
  have := congrArg (fun f => f i) h
  simpa using this

variable {i c} (hic : i ≠ c)
include hic

private theorem mv_apply_c (u : Fin (n + 1) →₀ ℕ) (j : ℕ) : mv i c u j c = u i + u c - j := by
  simp [mv_apply, Ne.symm hic]

omit hic in
private theorem mv_apply_ne {l : Fin (n + 1)} (hli : l ≠ i) (hlc : l ≠ c) (u : Fin (n + 1) →₀ ℕ)
    (j : ℕ) :
    mv i c u j l = u l := by
  simp [mv_apply, hli, hlc]

omit hic in
@[local simp] private theorem key_apply_i (u : Fin (n + 1) →₀ ℕ) : key i c u i = 0 := by simp [key]

private theorem key_apply_c (u : Fin (n + 1) →₀ ℕ) : key i c u c = u i + u c := by
  simp [key, mv_apply_c hic]

omit hic in
private theorem key_apply_ne {l : Fin (n + 1)} (hli : l ≠ i) (hlc : l ≠ c) (u : Fin (n + 1) →₀ ℕ) :
    key i c u l = u l := mv_apply_ne hli hlc u 0

omit hic in
private theorem ext3 {f g : Fin (n + 1) →₀ ℕ} (hi : f i = g i) (hc : f c = g c)
    (h : ∀ l, l ≠ i → l ≠ c → f l = g l) : f = g := by
  ext l
  by_cases hli : l = i
  · rw [hli]; exact hi
  by_cases hlc : l = c
  · rw [hlc]; exact hc
  exact h l hli hlc

private theorem mv_key (u : Fin (n + 1) →₀ ℕ) (j : ℕ) : mv i c (key i c u) j = mv i c u j :=
  ext3 (i := i) (c := c) (by simp)
    (by rw [mv_apply_c hic, mv_apply_c hic, key_apply_i, key_apply_c hic]; omega)
    fun l hli hlc => by rw [mv_apply_ne hli hlc, mv_apply_ne hli hlc, key_apply_ne hli hlc]

private theorem key_mv (u : Fin (n + 1) →₀ ℕ) (j : ℕ) (hj : j ≤ u i + u c) :
    key i c (mv i c u j) = key i c u :=
  ext3 (i := i) (c := c) (by simp)
    (by rw [key_apply_c hic, key_apply_c hic, mv_apply_i, mv_apply_c hic]; omega)
    fun l hli hlc => by rw [key_apply_ne hli hlc, key_apply_ne hli hlc, mv_apply_ne hli hlc]

private theorem key_key (u : Fin (n + 1) →₀ ℕ) : key i c (key i c u) = key i c u :=
  key_mv hic u 0 (Nat.zero_le _)

private theorem mv_self (u : Fin (n + 1) →₀ ℕ) : mv i c u (u i) = u :=
  ext3 (i := i) (c := c) (by simp) (by rw [mv_apply_c hic]; omega)
    fun l hli hlc => mv_apply_ne hli hlc u _

private theorem sub_add_eq_mv (u : Fin (n + 1) →₀ ℕ) (hu : 1 ≤ u i) :
    u - Finsupp.single i 1 + Finsupp.single c 1 = mv i c (key i c u) (u i - 1) :=
  ext3 (i := i) (c := c) (by simp [hic])
    (by rw [mv_apply_c hic, key_apply_i, key_apply_c hic]
        simp [Ne.symm hic]; omega)
    fun l hli hlc => by
      rw [mv_apply_ne hli hlc, key_apply_ne hli hlc]
      simp [Ne.symm hli, Ne.symm hlc]

private theorem mv_sub_single_i (u : Fin (n + 1) →₀ ℕ) (x : ℕ) (hx : 1 ≤ x) (hu : 1 ≤ u i) :
    mv i c u x - Finsupp.single i 1 = mv i c (u - Finsupp.single i 1) (x - 1) :=
  ext3 (i := i) (c := c) (by simp)
    (by rw [Finsupp.tsub_apply, mv_apply_c hic, mv_apply_c hic]; simp [Ne.symm hic]; omega)
    fun l hli hlc => by
      rw [Finsupp.tsub_apply, mv_apply_ne hli hlc, mv_apply_ne hli hlc, Finsupp.tsub_apply]

private theorem mv_sub_single_i' (u : Fin (n + 1) →₀ ℕ) (x : ℕ) (hx : 1 ≤ x) (hu : 1 ≤ u c) :
    mv i c u x - Finsupp.single i 1 = mv i c (u - Finsupp.single c 1) (x - 1) :=
  ext3 (i := i) (c := c) (by simp)
    (by
      rw [Finsupp.tsub_apply, mv_apply_c hic, mv_apply_c hic]
      simp [hic, Ne.symm hic]; omega)
    fun l hli hlc => by
      rw [Finsupp.tsub_apply, mv_apply_ne hli hlc, mv_apply_ne hli hlc, Finsupp.tsub_apply]
      simp [Ne.symm hli, Ne.symm hlc]

private theorem mv_sub_single_c (u : Fin (n + 1) →₀ ℕ) (x : ℕ) (hu : 1 ≤ u c) :
    mv i c u x - Finsupp.single c 1 = mv i c (u - Finsupp.single c 1) x :=
  ext3 (i := i) (c := c) (by simp [Ne.symm hic])
    (by rw [Finsupp.tsub_apply, mv_apply_c hic, mv_apply_c hic]; simp [hic]; omega)
    fun l hli hlc => by
      rw [Finsupp.tsub_apply, mv_apply_ne hli hlc, mv_apply_ne hli hlc, Finsupp.tsub_apply]

private theorem mv_sub_single_ne {l : Fin (n + 1)} (hli : l ≠ i) (hlc : l ≠ c)
    (u : Fin (n + 1) →₀ ℕ) (x : ℕ) :
    mv i c u x - Finsupp.single l 1 = mv i c (u - Finsupp.single l 1) x :=
  ext3 (i := i) (c := c) (by simp [hli])
    (by rw [Finsupp.tsub_apply, mv_apply_c hic, mv_apply_c hic]; simp [hli, hlc])
    fun l' hl'i hl'c => by
      rw [Finsupp.tsub_apply, mv_apply_ne hl'i hl'c, mv_apply_ne hl'i hl'c, Finsupp.tsub_apply]

private theorem mem_comp_iff (A : Finset (Fin (n + 1) →₀ ℕ)) (u : Fin (n + 1) →₀ ℕ) :
    u ∈ comp i c A ↔ u i < (J i c A (key i c u)).card := by
  constructor
  · intro hu
    simp only [comp, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range] at hu
    obtain ⟨m, ⟨a, -, rfl⟩, j, hj, rfl⟩ := hu
    have hjle : j ≤ a i + a c := by
      have := card_J_le i c A (key i c a); rw [key_apply_c hic] at this; omega
    rw [mv_apply_i, mv_key hic, key_mv hic a j hjle]
    exact hj
  · intro hu
    simp only [comp, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
    obtain ⟨j', hj'⟩ := Finset.card_pos.1 (show 0 < (J i c A (key i c u)).card by omega)
    rw [mem_J, key_apply_c hic, mv_key hic] at hj'
    refine ⟨key i c u, ⟨mv i c u j', hj'.2, key_mv hic u j' hj'.1⟩, u i, hu, ?_⟩
    rw [mv_key hic, mv_self hic]

private theorem comp_mono {A A' : Finset (Fin (n + 1) →₀ ℕ)} (h : A ⊆ A') :
    comp i c A ⊆ comp i c A' :=
  fun u hu => by
    rw [mem_comp_iff hic] at hu ⊢
    exact hu.trans_le (Finset.card_le_card (J_mono i c h _))

private theorem comp_step_mem {A : Finset (Fin (n + 1) →₀ ℕ)} {u : Fin (n + 1) →₀ ℕ}
    (hu : u ∈ comp i c A)
    (h1 : 1 ≤ u i) : u - Finsupp.single i 1 + Finsupp.single c 1 ∈ comp i c A := by
  rw [mem_comp_iff hic] at hu
  rw [sub_add_eq_mv hic u h1, mem_comp_iff hic, mv_apply_i, mv_key hic, key_mv hic u _ (by omega)]
  omega

private theorem sum_biUnion_mv (K : Finset (Fin (n + 1) →₀ ℕ)) (hK : ∀ m ∈ K, key i c m = m)
    (S : (Fin (n + 1) →₀ ℕ) → Finset ℕ) (hS : ∀ m ∈ K, ∀ j ∈ S m, j ≤ m i + m c)
    (f : (Fin (n + 1) →₀ ℕ) → ℕ) :
    ∑ u ∈ K.biUnion (fun m => (S m).image (mv i c m)), f u =
      ∑ m ∈ K, ∑ j ∈ S m, f (mv i c m j) := by
  rw [Finset.sum_biUnion]
  · exact Finset.sum_congr rfl fun m _ => Finset.sum_image fun j _ j' _ h => mv_injective i c m h
  · intro m hm m' hm' hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro u hu hu'
    rw [Finset.mem_image] at hu hu'
    obtain ⟨j, hj, rfl⟩ := hu
    obtain ⟨j', hj', h⟩ := hu'
    apply hne
    have h1 := key_mv hic m j (hS m hm j hj)
    have h2 := key_mv hic m' j' (hS m' hm' j' hj')
    rw [h, h1, hK m hm] at h2
    rw [hK m' hm'] at h2
    exact h2

private theorem key_of_mem_image {A : Finset (Fin (n + 1) →₀ ℕ)} {m : Fin (n + 1) →₀ ℕ}
    (hm : m ∈ A.image (key i c)) : key i c m = m := by
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hm; exact key_key hic a

private theorem sum_eq_sum_key (A : Finset (Fin (n + 1) →₀ ℕ)) (f : (Fin (n + 1) →₀ ℕ) → ℕ) :
    ∑ u ∈ A, f u = ∑ m ∈ A.image (key i c), ∑ j ∈ J i c A m, f (mv i c m j) := by
  have hA : A = (A.image (key i c)).biUnion (fun m => (J i c A m).image (mv i c m)) := by
    ext u
    simp only [Finset.mem_biUnion, Finset.mem_image]
    constructor
    · intro hu
      refine ⟨key i c u, ⟨u, hu, rfl⟩, u i, ?_, by rw [mv_key hic, mv_self hic]⟩
      rw [mem_J, key_apply_c hic, mv_key hic, mv_self hic]; exact ⟨by omega, hu⟩
    · rintro ⟨m, -, j, hj, rfl⟩
      exact ((mem_J i c).1 hj).2
  conv_lhs => rw [hA]
  refine sum_biUnion_mv hic _ (fun m hm => key_of_mem_image hic hm) _ (fun m hm j hj => ?_) f
  have := ((mem_J i c).1 hj).1; omega

private theorem sum_comp (A : Finset (Fin (n + 1) →₀ ℕ)) (f : (Fin (n + 1) →₀ ℕ) → ℕ) :
    ∑ u ∈ comp i c A, f u =
      ∑ m ∈ A.image (key i c), ∑ j ∈ Finset.range (J i c A m).card, f (mv i c m j) := by
  refine sum_biUnion_mv hic _ (fun m hm => key_of_mem_image hic hm) _ (fun m hm j hj => ?_) f
  rw [Finset.mem_range] at hj
  have := card_J_le i c A m; omega

private theorem card_comp (A : Finset (Fin (n + 1) →₀ ℕ)) : (comp i c A).card = A.card := by
  rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, sum_comp hic, sum_eq_sum_key hic A]
  simp

private theorem degree_mv (u : Fin (n + 1) →₀ ℕ) (j : ℕ) (hj : j ≤ u i + u c) :
    (mv i c u j).degree = u.degree := by
  have hi := Finset.mem_univ i
  have hc' : c ∈ Finset.univ.erase i := Finset.mem_erase.2 ⟨Ne.symm hic, Finset.mem_univ c⟩
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum,
    ← Finset.add_sum_erase Finset.univ (fun l => mv i c u j l) hi,
    ← Finset.add_sum_erase Finset.univ (fun l => u l) hi,
    ← Finset.add_sum_erase _ (fun l => mv i c u j l) hc',
    ← Finset.add_sum_erase _ (fun l => u l) hc', mv_apply_i, mv_apply_c hic]
  have : ∑ x ∈ (Finset.univ.erase i).erase c, mv i c u j x =
      ∑ x ∈ (Finset.univ.erase i).erase c, u x :=
    Finset.sum_congr rfl fun l hl => by
      simp only [Finset.mem_erase] at hl
      exact mv_apply_ne hl.2.1 hl.1 u j
  rw [this]; omega

private theorem mv_mem_MonW {u : Fin (n + 1) →₀ ℕ} {W e : ℕ} (hu : u ∈ MonW n W e)
    (hiW : (i : ℕ) < W)
    (hcW : (c : ℕ) < W) {j : ℕ} (hj : j ≤ u i + u c) : mv i c u j ∈ MonW n W e := by
  rw [mem_MonW] at hu ⊢
  refine ⟨by rw [degree_mv hic u j hj]; exact hu.1, fun l hl => ?_⟩
  have hli : l ≠ i := fun h => by rw [h] at hl; omega
  have hlc : l ≠ c := fun h => by rw [h] at hl; omega
  rw [mv_apply_ne hli hlc]; exact hu.2 l hl

private theorem comp_subset_MonW {A : Finset (Fin (n + 1) →₀ ℕ)} {W e : ℕ} (hA : A ⊆ MonW n W e)
    (hiW : (i : ℕ) < W) (hcW : (c : ℕ) < W) : comp i c A ⊆ MonW n W e := by
  intro u hu
  simp only [comp, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range] at hu
  obtain ⟨m, ⟨a, ha, rfl⟩, j, hj, rfl⟩ := hu
  rw [mv_key hic]
  have hjle : j ≤ a i + a c := by
    have := card_J_le i c A (key i c a); rw [key_apply_c hic] at this; omega
  exact mv_mem_MonW hic (hA ha) hiW hcW hjle

omit hic in
private theorem sum_range_card_le (S : Finset ℕ) :
    ∑ j ∈ Finset.range S.card, j ≤ ∑ j ∈ S, j ∧
      (∑ j ∈ Finset.range S.card, j = ∑ j ∈ S, j → S = Finset.range S.card) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s has ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (has a h)
    have hcard : s.card ≤ a := by
      have : s ⊆ Finset.range a := fun x hx => Finset.mem_range.2 (has x hx)
      simpa using Finset.card_le_card this
    rw [Finset.card_insert_of_notMem ha, Finset.sum_range_succ, Finset.sum_insert ha]
    refine ⟨by omega, fun h => ?_⟩
    have h1 : ∑ j ∈ Finset.range s.card, j = ∑ j ∈ s, j := by omega
    have h2 : s.card = a := by omega
    have h3 := ih.2 h1
    rw [Finset.range_add_one, ← h3, h2]

omit hic in
private theorem min_card_le (S S' : Finset ℕ) (t : ℕ) (h1 : ∀ x ∈ S, x < t → x ∈ S')
    (h2 : ∀ x ∈ S, 1 ≤ x → x - 1 ∈ S') : min S.card t ≤ S'.card := by
  by_cases hfull : ∀ g, g ≤ t → g ∈ S
  · have : Finset.range t ⊆ S' := fun x hx => by
      rw [Finset.mem_range] at hx; exact h1 x (hfull x hx.le) hx
    have := Finset.card_le_card this
    rw [Finset.card_range] at this
    omega
  · push Not at hfull
    obtain ⟨g, hgt, hgS⟩ := hfull
    have : S.card ≤ S'.card := by
      refine Finset.card_le_card_of_injOn (fun x => if x < g then x else x - 1) (fun x hx => ?_) ?_
      · rw [Finset.mem_coe] at hx
        have hxg : x ≠ g := fun h => hgS (h ▸ hx)
        change (if x < g then x else x - 1) ∈ (S' : Set ℕ)
        rw [Finset.mem_coe]
        split_ifs with h
        · exact h1 x hx (by omega)
        · exact h2 x hx (by omega)
      · intro x hx y hy hxy
        rw [Finset.mem_coe] at hx hy
        have hxg : x ≠ g := fun h => hgS (h ▸ hx)
        have hyg : y ≠ g := fun h => hgS (h ▸ hy)
        simp only at hxy
        split_ifs at hxy <;> omega
    omega

private theorem sub_single_mem_comp {A D : Finset (Fin (n + 1) →₀ ℕ)}
    (hAD : ∀ a ∈ A, ∀ l : Fin (n + 1), 1 ≤ a l → a - Finsupp.single l 1 ∈ D)
    {u : Fin (n + 1) →₀ ℕ} (hu : u ∈ comp i c A) (l : Fin (n + 1)) (hl : 1 ≤ u l) :
    u - Finsupp.single l 1 ∈ comp i c D := by
  rw [mem_comp_iff hic] at hu ⊢
  have hmem : ∀ x ∈ J i c A (key i c u), x ≤ u i + u c ∧ mv i c u x ∈ A := fun x hx => by
    have := (mem_J i c).1 hx; rw [key_apply_c hic, mv_key hic] at this; exact this
  by_cases hli : l = i
  · subst hli
    have e1 : (u - Finsupp.single l 1 : Fin (n + 1) →₀ ℕ) l = u l - 1 := by simp
    rw [e1]
    have hinj : ((J l c A (key l c u)).erase 0).card ≤
        (J l c D (key l c (u - Finsupp.single l 1))).card := by
      refine Finset.card_le_card_of_injOn (fun x => x - 1) (fun x hx => ?_) ?_
      · rw [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff] at hx
        obtain ⟨hx, hx0⟩ := hx
        obtain ⟨hxle, hxA⟩ := hmem x hx
        rw [Finset.mem_coe, mem_J, key_apply_c hic, mv_key hic]
        refine ⟨by rw [Finsupp.tsub_apply, Finsupp.tsub_apply]; simp [hic]; omega, ?_⟩
        have := hAD _ hxA l (by rw [mv_apply_i]; omega)
        rwa [mv_sub_single_i hic u x (by omega) hl] at this
      · intro x hx y hy hxy
        rw [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff] at hx hy
        simp only at hxy
        omega
    have := Finset.pred_card_le_card_erase (s := J l c A (key l c u)) (a := 0)
    omega
  by_cases hlc : l = c
  · subst hlc
    have e1 : (u - Finsupp.single l 1 : Fin (n + 1) →₀ ℕ) i = u i := by simp [hic]
    rw [e1]
    have key_le : min (J i l A (key i l u)).card (u i + u l) ≤
        (J i l D (key i l (u - Finsupp.single l 1))).card := by
      refine min_card_le _ _ (u i + u l) (fun x hx hxt => ?_) (fun x hx hx1 => ?_)
      · obtain ⟨-, hxA⟩ := hmem x hx
        rw [mem_J, key_apply_c hic, mv_key hic]
        refine ⟨by rw [Finsupp.tsub_apply, Finsupp.tsub_apply]; simp [Ne.symm hic]; omega, ?_⟩
        have := hAD _ hxA l (by rw [mv_apply_c hic]; omega)
        rwa [mv_sub_single_c hic u x hl] at this
      · obtain ⟨hxle, hxA⟩ := hmem x hx
        rw [mem_J, key_apply_c hic, mv_key hic]
        refine ⟨by rw [Finsupp.tsub_apply, Finsupp.tsub_apply]; simp [Ne.symm hic]; omega, ?_⟩
        have := hAD _ hxA i (by rw [mv_apply_i]; omega)
        rwa [mv_sub_single_i' hic u x hx1 hl] at this
    have : u i < u i + u l := by omega
    omega
  · have e1 : (u - Finsupp.single l 1 : Fin (n + 1) →₀ ℕ) i = u i := by simp [hli]
    rw [e1]
    have : (J i c A (key i c u)).card ≤ (J i c D (key i c (u - Finsupp.single l 1))).card := by
      refine Finset.card_le_card fun x hx => ?_
      obtain ⟨hxle, hxA⟩ := hmem x hx
      rw [mem_J, key_apply_c hic, mv_key hic]
      refine ⟨by rw [Finsupp.tsub_apply, Finsupp.tsub_apply]; simp [hli, hlc]; omega, ?_⟩
      have := hAD _ hxA l (by rw [mv_apply_ne hli hlc]; exact hl)
      rwa [mv_sub_single_ne hic hli hlc u x] at this
    omega

private theorem card_Bplus_le_comp (W e : ℕ) (X : Finset (Fin (n + 1) →₀ ℕ)) (hiW : (i : ℕ) < W)
    (hcW : (c : ℕ) < W) : (Bplus n W e X).card ≤ (Bplus n W e (comp i c X)).card := by
  rw [← card_comp hic (Bplus n W e X)]
  refine Finset.card_le_card fun u hu => ?_
  rw [mem_Bplus]
  refine ⟨comp_subset_MonW hic (Bplus_subset_MonW n W e X) hiW hcW hu, fun l hl => ?_⟩
  exact sub_single_mem_comp hic (fun a ha l hl => ((mem_Bplus n W e X a).1 ha).2 l hl) hu l hl

private theorem wt_mv (m : Fin (n + 1) →₀ ℕ) (j : ℕ) (hm : m i = 0) :
    wt c (mv i c m j) = wt c m + j := by
  unfold wt
  have hi : i ∈ Finset.univ.erase c := Finset.mem_erase.2 ⟨hic, Finset.mem_univ _⟩
  rw [← Finset.add_sum_erase _ (fun l => mv i c m j l) hi,
    ← Finset.add_sum_erase _ (fun l => m l) hi,
    mv_apply_i, hm, zero_add, add_comm]
  congr 1
  exact Finset.sum_congr rfl fun l hl => by
    simp only [Finset.mem_erase] at hl
    exact mv_apply_ne hl.1 hl.2.1 _ _

private theorem pot_comp_lt (A : Finset (Fin (n + 1) →₀ ℕ)) {u : Fin (n + 1) →₀ ℕ} (hu : u ∈ A)
    (h1 : 1 ≤ u i)
    (hnot : u - Finsupp.single i 1 + Finsupp.single c 1 ∉ A) : pot c (comp i c A) < pot c A := by
  unfold pot
  rw [sum_comp hic, sum_eq_sum_key hic A]
  have hrw : ∀ m ∈ A.image (key i c), ∀ (S : Finset ℕ),
      ∑ j ∈ S, wt c (mv i c m j) = S.card * wt c m + ∑ j ∈ S, j := fun m hm S => by
    have hm0 : m i = 0 := by
      have := key_apply_i (i := i) (c := c) m; rwa [key_of_mem_image hic hm] at this
    rw [Finset.sum_congr rfl fun j _ => wt_mv hic m j hm0, Finset.sum_add_distrib, Finset.sum_const,
      smul_eq_mul]
  apply Finset.sum_lt_sum
  · intro m hm
    rw [hrw m hm, hrw m hm, Finset.card_range]
    have := (sum_range_card_le (J i c A m)).1
    omega
  · refine ⟨key i c u, Finset.mem_image_of_mem _ hu, ?_⟩
    have hm := Finset.mem_image_of_mem (key i c) hu
    rw [hrw _ hm, hrw _ hm, Finset.card_range]
    have hle := (sum_range_card_le (J i c A (key i c u))).1
    have hne : J i c A (key i c u) ≠ Finset.range (J i c A (key i c u)).card := by
      intro heq
      have hin : u i ∈ J i c A (key i c u) :=
        (mem_J i c).2 ⟨by rw [key_apply_c hic]; omega, by rw [mv_key hic, mv_self hic]; exact hu⟩
      have hout : u i - 1 ∉ J i c A (key i c u) := fun h =>
        hnot (by rw [sub_add_eq_mv hic u h1]; exact ((mem_J i c).1 h).2)
      rw [heq, Finset.mem_range] at hin hout
      omega
    have hlt : ∑ j ∈ Finset.range (J i c A (key i c u)).card, j < ∑ j ∈ J i c A (key i c u), j :=
      lt_of_le_of_ne hle fun h => hne ((sum_range_card_le _).2 h)
    omega

end Compression

private theorem exists_stable (w : ℕ) (c : Fin (n + 1)) (hcw : (c : ℕ) = w) (e : ℕ) :
    ∀ (P : ℕ) (X : Finset (Fin (n + 1) →₀ ℕ)), pot c X = P → X ⊆ MonW n (w + 1) e →
    ∃ Y : Finset (Fin (n + 1) →₀ ℕ), Y ⊆ MonW n (w + 1) e ∧ Y.card = X.card ∧
      (Bplus n (w + 1) e X).card ≤ (Bplus n (w + 1) e Y).card ∧
      ∀ u ∈ Y, ∀ l : Fin (n + 1), (l : ℕ) < w → 1 ≤ u l →
        u - Finsupp.single l 1 + Finsupp.single c 1 ∈ Y := by
  intro P
  induction P using Nat.strong_induction_on with
  | _ P IH =>
  intro X hP hX
  by_cases hst : ∀ u ∈ X, ∀ l : Fin (n + 1), (l : ℕ) < w → 1 ≤ u l →
      u - Finsupp.single l 1 + Finsupp.single c 1 ∈ X
  · exact ⟨X, hX, rfl, le_rfl, hst⟩
  · push Not at hst
    obtain ⟨u, hu, l, hlw, hul, hnot⟩ := hst
    have hlc : l ≠ c := fun h => by rw [h, hcw] at hlw; omega
    have hlt : pot c (comp l c X) < P := hP ▸ pot_comp_lt hlc X hu hul hnot
    obtain ⟨Y, hY, hYc, hYB, hYs⟩ :=
      IH _ hlt (comp l c X) rfl (comp_subset_MonW hlc hX (by omega) (by omega))
    exact ⟨Y, hY, hYc.trans (card_comp hlc X),
      (card_Bplus_le_comp hlc _ e X (by omega) (by omega)).trans hYB, hYs⟩

variable (n)

private noncomputable def T (w : ℕ) (c : Fin (n + 1)) (X : Finset (Fin (n + 1) →₀ ℕ)) (e k : ℕ) :
    Finset (Fin (n + 1) →₀ ℕ) :=
  (MonW n w (e - k)).filter fun v => v + Finsupp.single c k ∈ X

private theorem T_subset (w : ℕ) (c : Fin (n + 1)) (X : Finset (Fin (n + 1) →₀ ℕ)) (e k : ℕ) :
    T n w c X e k ⊆ MonW n w (e - k) := Finset.filter_subset _ _

variable {n}

section Tower

variable {w : ℕ} {c : Fin (n + 1)} (hcw : (c : ℕ) = w) {X : Finset (Fin (n + 1) →₀ ℕ)} {e : ℕ}
  (hX : X ⊆ MonW n (w + 1) e)
include hcw hX

private theorem mem_T_iff {k : ℕ} (hk : k ≤ e) (v : Fin (n + 1) →₀ ℕ) :
    v ∈ T n w c X e k ↔ v c = 0 ∧ v + Finsupp.single c k ∈ X := by
  rw [T, Finset.mem_filter, mem_MonW]
  constructor
  · rintro ⟨⟨-, hsupp⟩, hmem⟩; exact ⟨hsupp c (by omega), hmem⟩
  · rintro ⟨hc0, hmem⟩
    have hu := (mem_MonW n _ _ _).1 (hX hmem)
    refine ⟨⟨?_, fun l hl => ?_⟩, hmem⟩
    · have := hu.1; rw [map_add, Finsupp.degree_single] at this; omega
    · by_cases hlc : l = c
      · rw [hlc]; exact hc0
      · have hl' : w + 1 ≤ (l : ℕ) := by
          have : (l : ℕ) ≠ w := fun h => hlc (Fin.ext (h.trans hcw.symm)); omega
        have := hu.2 l hl'
        rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hlc] at this; omega

private theorem card_T {k : ℕ} (hk : k ≤ e) :
    (T n w c X e k).card = (X.filter fun u => u c = k).card := by
  refine Finset.card_bij' (fun v _ => v + Finsupp.single c k) (fun u _ => u - Finsupp.single c k)
    ?_ ?_ ?_ ?_
  · intro v hv
    rw [mem_T_iff hcw hX hk] at hv
    rw [Finset.mem_filter]
    exact ⟨hv.2, by rw [Finsupp.add_apply, Finsupp.single_eq_same, hv.1, zero_add]⟩
  · intro u hu
    rw [Finset.mem_filter] at hu
    rw [mem_T_iff hcw hX hk]
    refine ⟨by rw [Finsupp.tsub_apply, Finsupp.single_eq_same, hu.2, Nat.sub_self], ?_⟩
    rw [tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (by rw [hu.2]))]
    exact hu.1
  · intro v _; exact add_tsub_cancel_right _ _
  · intro u hu
    rw [Finset.mem_filter] at hu
    exact tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (by rw [hu.2]))

private theorem sum_card_T : ∑ k ∈ Finset.range (e + 1), (T n w c X e k).card = X.card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun u => u c) (s := X) (t := Finset.range (e + 1))
    (fun u hu => by
      rw [Finset.mem_coe] at hu
      rw [Finset.mem_coe, Finset.mem_range, Nat.lt_succ_iff, ← ((mem_MonW n _ _ _).1 (hX hu)).1]
      exact Finsupp.le_degree c u)]
  exact Finset.sum_congr rfl fun k hk => card_T hcw hX (by rw [Finset.mem_range] at hk; omega)

private theorem card_Bplus_succ_le :
    (Bplus n (w + 1) e X).card ≤ (Bplus n w e (T n w c X e 0)).card + X.card := by
  classical
  have hsub : Bplus n (w + 1) e X ⊆
      Bplus n w e (T n w c X e 0) ∪ X.image (· + Finsupp.single c 1) := by
    intro u hu
    rw [mem_Bplus, mem_MonW] at hu
    obtain ⟨⟨hdeg, hsupp⟩, hdiv⟩ := hu
    rw [Finset.mem_union]
    by_cases h0 : u c = 0
    · left
      rw [mem_Bplus, mem_MonW]
      refine ⟨⟨hdeg, fun l hl => ?_⟩, fun l hl => ?_⟩
      · by_cases hlc : l = c
        · rw [hlc]; exact h0
        · exact hsupp l (by have : (l : ℕ) ≠ w := fun h => hlc (Fin.ext (h.trans hcw.symm)); omega)
      · rw [mem_T_iff hcw hX (Nat.zero_le e), Finsupp.single_zero, add_zero]
        exact ⟨by rw [Finsupp.tsub_apply, h0, Nat.zero_sub], hdiv l hl⟩
    · right
      rw [Finset.mem_image]
      exact ⟨u - Finsupp.single c 1, hdiv c (by omega), Finsupp.sub_add_single_one_cancel h0⟩
  calc (Bplus n (w + 1) e X).card ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left Finset.card_image_le _

omit hcw hX in
private theorem sub_add_single_comm (v : Fin (n + 1) →₀ ℕ) {l c' : Fin (n + 1)} (hlc : l ≠ c')
    (k : ℕ) :
    v - Finsupp.single l 1 + Finsupp.single c' (k + 1) =
      v + Finsupp.single c' k - Finsupp.single l 1 + Finsupp.single c' 1 := by
  ext x
  simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
  rcases eq_or_ne l x with rfl | h1
  · simp [Ne.symm hlc]
  · rcases eq_or_ne c' x with rfl | h2
    · simp [h1, add_assoc]
    · simp [h1, h2]

private theorem T_subset_Bplus
    (hstab : ∀ u ∈ X, ∀ l : Fin (n + 1), (l : ℕ) < w → 1 ≤ u l →
      u - Finsupp.single l 1 + Finsupp.single c 1 ∈ X)
    (k : ℕ) (hk : k + 1 ≤ e) : T n w c X e k ⊆ Bplus n w (e - (k + 1)) (T n w c X e (k + 1)) := by
  intro v hv
  have hv' := (mem_T_iff hcw hX (by omega) v).1 hv
  have hvM := (mem_MonW n _ _ _).1 (T_subset n w c X e k hv)
  rw [mem_Bplus, show e - (k + 1) + 1 = e - k by omega, mem_MonW]
  refine ⟨hvM, fun l hl => ?_⟩
  have hlw : (l : ℕ) < w := by
    by_contra h
    push Not at h
    have := hvM.2 l h; omega
  have hlc : l ≠ c := fun h => by rw [h, hcw] at hlw; omega
  rw [mem_T_iff hcw hX hk]
  refine ⟨by rw [Finsupp.tsub_apply, hv'.1, Nat.zero_sub], ?_⟩
  have := hstab _ hv'.2 l hlw
    (by rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hlc]; omega)
  rwa [← sub_add_single_comm v hlc k] at this

omit hcw hX in
private theorem card_T_last_le : (T n w c X e e).card ≤ 1 := by
  refine (Finset.card_le_card (T_subset n w c X e e)).trans ?_
  rw [Nat.sub_self, MonW_zero_right, Finset.card_singleton]

private theorem card_T_last_eq
    (hstab : ∀ u ∈ X, ∀ l : Fin (n + 1), (l : ℕ) < w → 1 ≤ u l →
      u - Finsupp.single l 1 + Finsupp.single c 1 ∈ X)
    (he : 1 ≤ e) (hne : 1 ≤ (T n w c X e (e - 1)).card) : (T n w c X e e).card = 1 := by
  refine le_antisymm card_T_last_le ?_
  obtain ⟨v, hv⟩ := Finset.card_pos.1 (show 0 < (T n w c X e (e - 1)).card by omega)
  have hsub := T_subset_Bplus hcw hX hstab (e - 1) (by omega) hv
  rw [show e - 1 + 1 = e by omega, mem_Bplus] at hsub
  have hdeg := ((mem_MonW n _ _ _).1 (T_subset n w c X e (e - 1) hv)).1
  obtain ⟨l, hl⟩ := exists_one_le_of_degree_ne_zero v (by rw [hdeg]; omega)
  exact Finset.card_pos.2 ⟨_, hsub.2 l hl⟩

end Tower

private theorem stable_bound (w : ℕ) (c : Fin (n + 1)) (hcw : (c : ℕ) = w)
    (ih : ∀ e, 1 ≤ e → ∀ Z : Finset (Fin (n + 1) →₀ ℕ), Z ⊆ MonW n w e →
      (Bplus n w e Z).card ≤ Nat.macaulayPow e Z.card)
    {e : ℕ} (he : 1 ≤ e) {X : Finset (Fin (n + 1) →₀ ℕ)} (hX : X ⊆ MonW n (w + 1) e)
    (hstab : ∀ u ∈ X, ∀ l : Fin (n + 1), (l : ℕ) < w → 1 ≤ u l →
      u - Finsupp.single l 1 + Finsupp.single c 1 ∈ X) :
    (Bplus n (w + 1) e X).card ≤ Nat.macaulayPow e X.card := by
  obtain ⟨e, rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  have hsum : ∑ k ∈ Finset.range (e + 2), (T n w c X (e + 1) k).card = X.card := sum_card_T hcw hX
  have h := tower_bound e (fun k => (T n w c X (e + 1) k).card)
    (Bplus n w (e + 1) (T n w c X (e + 1) 0)).card
    card_T_last_le ?_ ?_ ?_
  · rw [hsum] at h
    exact (card_Bplus_succ_le hcw hX).trans h
  · intro h1
    exact card_T_last_eq hcw hX hstab (by omega) (by simpa using h1)
  · intro k hk
    have hsub := T_subset_Bplus hcw hX hstab k (by omega)
    rw [show e + 1 - (k + 1) = e - k by omega] at hsub
    refine (Finset.card_le_card hsub).trans (ih (e - k) (by omega) _ ?_)
    have := T_subset n w c X (e + 1) (k + 1)
    rwa [show e + 1 - (k + 1) = e - k by omega] at this
  · exact ih (e + 1) (by omega) _ (T_subset n w c X (e + 1) 0)

private theorem main : ∀ w : ℕ, w ≤ n + 1 → ∀ e : ℕ, 1 ≤ e → ∀ X : Finset (Fin (n + 1) →₀ ℕ),
    X ⊆ MonW n w e → (Bplus n w e X).card ≤ Nat.macaulayPow e X.card
  | 0, _, e, he, X, hX => by
      obtain ⟨e, rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
      have h1 : X = ∅ := Finset.subset_empty.1 (by rw [MonW_zero_succ] at hX; exact hX)
      subst h1
      have h2 : Bplus n 0 (e + 1) ∅ = ∅ := Finset.subset_empty.1 (by
        have := Bplus_subset_MonW n 0 (e + 1) ∅; rw [MonW_zero_succ] at this; exact this)
      rw [h2, Finset.card_empty]; exact Nat.zero_le _
  | w + 1, hw, e, he, X, hX => by
      obtain ⟨Y, hY, hYc, hYB, hYs⟩ := exists_stable w ⟨w, by omega⟩ rfl e _ X rfl hX
      refine hYB.trans ?_
      rw [← hYc]
      exact stable_bound w ⟨w, by omega⟩ rfl (main w (by omega)) he hY hYs

end MacaulayBoundAux

end Finsupp

@[expose] public section

namespace Finsupp

open MacaulayBoundAux in
/-- **Macaulay's bound for monomial shadows.** Let `d ≥ 1`. If every degree-`d` divisor of every
monomial in a set `C` of degree-`(d + 1)` monomials in `n + 1` variables lies in a set `B` of
degree-`d` monomials, then `#C ≤ #B^⟨d⟩`. -/
public theorem card_le_macaulayPow_card_of_forall_sub_single_mem
    (n d : ℕ) (hd : 1 ≤ d) (B : Finset (Fin (n + 1) →₀ ℕ)) (hB : ∀ m ∈ B, m.degree = d)
    (C : Finset (Fin (n + 1) →₀ ℕ)) (hC : ∀ u ∈ C, u.degree = d + 1)
    (hCB : ∀ u ∈ C, ∀ i : Fin (n + 1), 1 ≤ u i → u - Finsupp.single i 1 ∈ B) :
    C.card ≤ Nat.macaulayPow d B.card := by
  have hBW : B ⊆ MonW n (n + 1) d := fun m hm =>
    (mem_MonW n _ _ m).2 ⟨hB m hm, fun i hi => absurd i.2 (by omega)⟩
  have hCsub : C ⊆ Bplus n (n + 1) d B := fun u hu =>
    (mem_Bplus n _ _ B u).2
      ⟨(mem_MonW n _ _ u).2 ⟨hC u hu, fun i hi => absurd i.2 (by omega)⟩, hCB u hu⟩
  exact (Finset.card_le_card hCsub).trans (main (n + 1) le_rfl d hd B hBW)

end Finsupp
