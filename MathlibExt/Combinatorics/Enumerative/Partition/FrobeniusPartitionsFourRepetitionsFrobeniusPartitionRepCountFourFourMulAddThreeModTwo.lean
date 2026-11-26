/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Topology.Instances.ZMod
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Int.ModEq
import MathlibExt.Combinatorics.Enumerative.Partition.LevelFiveEulerDissection
import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanProduct

/-!
# Parity of Frobenius partitions with four repetitions

This module defines `frobeniusPartitionRepCount` and proves that the number of generalized
Frobenius partitions of `4n + 3` with at most four repetitions in each row is even.

Source: Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4
Repetitions*, INTEGERS 25 (2025), Article A17, Theorem 2.
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

local notation "𝔣" => qEulerProduct

/-- **Frobenius partitions with at most $k$ repetitions.** For natural numbers $k$ and $n$,
$\varphi_k(n)$ is the number of generalized Frobenius partitions of $n$ in which each integer
appears at most $k$ times in each row. Concretely, $\varphi_k(n)$ is the number of pairs of
functions $m_1, m_2 \colon \{0, 1, \dots, n\} \to \{0, 1, \dots, k\}$ with
$\sum_i m_1(i) = \sum_i m_2(i)$ and $\sum_i (i + 1)\, m_1(i) + \sum_i i\, m_2(i) = n$.

Here a generalized Frobenius partition of $n$ is a two-rowed array of nonnegative integers with
$r$ columns, both rows nonincreasing, whose entries sum to $n - r$; its entries are at most $n$,
and $m_1(i)$, $m_2(i)$ count how often $i$ appears in the top and bottom rows.

Source: Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4
Repetitions*, INTEGERS 25 (2025), Article A17, Section 1 (definition of `φ_k(n)`, after
Andrews). -/
public def frobeniusPartitionRepCount (k n : ℕ) : ℕ :=
  ((Finset.univ : Finset ((Fin (n + 1) → Fin (k + 1)) × (Fin (n + 1) → Fin (k + 1)))).filter
    fun p => ∑ i : Fin (n + 1), (p.1 i : ℕ) = ∑ i : Fin (n + 1), (p.2 i : ℕ) ∧
      ∑ i : Fin (n + 1), (p.1 i : ℕ) * ((i : ℕ) + 1) +
        ∑ i : Fin (n + 1), (p.2 i : ℕ) * (i : ℕ) = n).card

private abbrev Pair (k N : ℕ) :=
  (Fin (N + 1) → Fin (k + 1)) × (Fin (N + 1) → Fin (k + 1))

private def frobSet (k N : ℕ) : Finset (Pair k N) :=
  Finset.univ.filter fun p =>
    ∑ i : Fin (N + 1), (p.1 i : ℕ) = ∑ i : Fin (N + 1), (p.2 i : ℕ) ∧
      ∑ i : Fin (N + 1), (p.1 i : ℕ) * ((i : ℕ) + 1) +
        ∑ i : Fin (N + 1), (p.2 i : ℕ) * (i : ℕ) = N

private lemma swap_mem {k N : ℕ} {p : Pair k N} (hp : p ∈ frobSet k N) :
    p.swap ∈ frobSet k N := by
  simp only [frobSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  obtain ⟨h1, h2⟩ := hp
  refine ⟨h1.symm, ?_⟩
  simp only [Prod.fst_swap, Prod.snd_swap, mul_add, mul_one, Finset.sum_add_distrib] at h2 ⊢
  omega

private lemma even_card_of_swap {α : Type*} (σ : α → α)
    (T : Finset α) (hmem : ∀ x ∈ T, σ x ∈ T) (hinv : ∀ x ∈ T, σ (σ x) = x)
    (hfree : ∀ x ∈ T, σ x ≠ x) : Even T.card := by
  apply ZMod.natCast_eq_zero_iff_even.mp
  have h := Finset.sum_involution (s := T) (f := fun _ => (1 : ZMod 2))
    (fun x _ => σ x) (fun _ _ => by decide) (fun x hx _ => hfree x hx) hmem hinv
  simpa using h

private def diagSet (k N : ℕ) : Finset (Fin (N + 1) → Fin (k + 1)) :=
  Finset.univ.filter fun m =>
    ∑ i : Fin (N + 1), (m i : ℕ) * ((i : ℕ) + 1) +
      ∑ i : Fin (N + 1), (m i : ℕ) * (i : ℕ) = N

private lemma card_filter_swap_eq_diag (k N : ℕ) :
    ((frobSet k N).filter (fun p => p.swap = p)).card = (diagSet k N).card := by
  have hset : (frobSet k N).filter (fun p => p.swap = p)
      = (diagSet k N).image (fun m => (m, m)) := by
    ext ⟨a, b⟩
    simp only [frobSet, diagSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, Prod.swap_prod_mk, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨_, hwt⟩, hba, hab⟩
      refine ⟨b, ?_, hba, rfl⟩
      simpa only [hab] using hwt
    · rintro ⟨m, hWm, hma, hmb⟩
      subst a b
      exact ⟨⟨rfl, hWm⟩, rfl, rfl⟩
  rw [hset]
  exact Finset.card_image_of_injective _ fun _ _ h => congrArg Prod.fst h

private noncomputable def diagonalSeries : (ZMod 2)⟦X⟧ :=
  PowerSeries.mk fun N => ((diagSet 4 N).card : ZMod 2)

private noncomputable def boundedFactor (i : ℕ) : (ZMod 2)⟦X⟧ :=
  ∑ j : Fin 5, X ^ ((j : ℕ) * (2 * i + 1))

private lemma diag_weight (N : ℕ) (m : Fin (N + 1) → Fin 5) :
    ∑ i : Fin (N + 1), (m i : ℕ) * ((i : ℕ) + 1) +
        ∑ i : Fin (N + 1), (m i : ℕ) * (i : ℕ) =
      ∑ i : Fin (N + 1), (m i : ℕ) * (2 * (i : ℕ) + 1) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma coeff_bounded_product (N : ℕ) :
    (∏ i ∈ Finset.range (N + 1), boundedFactor i).coeff N = ((diagSet 4 N).card : ZMod 2) := by
  rw [← Fin.prod_univ_eq_prod_range]
  simp only [boundedFactor]
  rw [Fintype.prod_sum]
  simp_rw [Finset.prod_pow_eq_pow_sum]
  simp only [map_sum, coeff_X_pow]
  simp only [diagSet, diag_weight, Finset.sum_boole]
  simp only [eq_comm]

private lemma boundedFactor_tail (i : ℕ) :
    boundedFactor i = 1 - (-∑ j : Fin 4, (X : (ZMod 2)⟦X⟧) ^
      (((j : ℕ) + 1) * (2 * i + 1))) := by
  simp [boundedFactor, Fin.sum_univ_succ]
  ring

private lemma boundedFactor_order (i : ℕ) :
    (2 * i + 1 : ℕ∞) ≤ (-∑ j : Fin 4, (X : (ZMod 2)⟦X⟧) ^
      (((j : ℕ) + 1) * (2 * i + 1))).order := by
  apply nat_le_order
  intro d hd
  simp only [map_neg, map_sum]
  rw [Finset.sum_eq_zero]
  · simp
  · intro j _
    rw [coeff_X_pow]
    have h : d ≠ ((j : ℕ) + 1) * (2 * i + 1) := by nlinarith
    simp [h]

open scoped PowerSeries.WithPiTopology in
private lemma hasProd_diagonalSeries : HasProd boundedFactor diagonalSeries := by
  rw [HasProd, WithPiTopology.tendsto_iff_coeff_tendsto]
  intro N
  apply tendsto_atTop_of_eventually_const
  intro s (hs : Finset.range (N + 1) ⊆ s)
  rw [← Finset.prod_sdiff hs]
  rw [Finset.prod_congr rfl (fun i _ => boundedFactor_tail i)]
  rw [mul_comm]
  rw [coeff_mul_prod_one_sub_of_lt_order]
  · simpa only [diagonalSeries, coeff_mk] using coeff_bounded_product N
  · intro i hi
    have hi' := (Finset.mem_sdiff.mp hi).2
    simp only [Finset.mem_range, not_lt] at hi'
    have hlt : (N : ℕ∞) < (2 * i + 1 : ℕ) := by
      exact_mod_cast (show N < 2 * i + 1 by omega)
    exact hlt.trans_le (boundedFactor_order i)

private noncomputable abbrev reduceSeries : ℤ⟦X⟧ →+* (ZMod 2)⟦X⟧ :=
  PowerSeries.map (Int.castRingHom (ZMod 2))

private noncomputable def eulerModTwo (k : ℕ) : (ZMod 2)⟦X⟧ :=
  reduceSeries (qEulerProduct k)

open scoped PowerSeries.WithPiTopology in
private lemma continuous_reduceSeries : Continuous reduceSeries := by
  apply continuous_pi
  intro d
  exact (continuous_of_discreteTopology : Continuous (Int.castRingHom (ZMod 2))).comp
    (continuous_pi_iff.mp (continuous_id : Continuous (id : ℤ⟦X⟧ → ℤ⟦X⟧)) d)

open scoped PowerSeries.WithPiTopology in
private lemma multipliable_minus (a b : ℕ) (ha : a ≠ 0) :
    Multipliable fun i : ℕ => (1 : (ZMod 2)⟦X⟧) - X ^ (a * i + b) := by
  simp_rw [sub_eq_add_neg]
  apply WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
  apply ENat.tendsto_nhds_top_iff_natCast_lt.mpr
  intro n
  apply Filter.eventually_atTop.mpr
  refine ⟨n + 1, fun i hi => ?_⟩
  rw [order_neg, order_X_pow]
  have h : n < a * i + b := by nlinarith [Nat.one_le_iff_ne_zero.mpr ha]
  exact_mod_cast h

open scoped PowerSeries.WithPiTopology in
private lemma hasProd_eulerModTwo (k : ℕ) (hk : k ≠ 0) :
    HasProd (fun i : ℕ => (1 : (ZMod 2)⟦X⟧) - X ^ (k * (i + 1))) (eulerModTwo k) := by
  have hm : Multipliable fun i : ℕ => (1 : ℤ⟦X⟧) - X ^ (k * (i + 1)) := by
    simp_rw [sub_eq_add_neg]
    apply WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
    apply ENat.tendsto_nhds_top_iff_natCast_lt.mpr
    intro n
    apply Filter.eventually_atTop.mpr
    refine ⟨n, fun i hi => ?_⟩
    rw [order_neg, order_X_pow]
    have h : n < k * (i + 1) := by nlinarith [Nat.one_le_iff_ne_zero.mpr hk]
    exact_mod_cast h
  have hp := hm.hasProd.map reduceSeries continuous_reduceSeries
  simpa only [eulerModTwo, qEulerProduct, Function.comp_def, reduceSeries,
    map_sub, map_one, map_pow, PowerSeries.map_X] using hp

open scoped PowerSeries.WithPiTopology in
private noncomputable def oddEulerModTwo (k : ℕ) : (ZMod 2)⟦X⟧ :=
  ∏' i : ℕ, (1 - X ^ (k * (2 * i + 1)))

open scoped PowerSeries.WithPiTopology in
private lemma hasProd_oddEulerModTwo (k : ℕ) (hk : k ≠ 0) :
    HasProd (fun i : ℕ => (1 : (ZMod 2)⟦X⟧) - X ^ (k * (2 * i + 1)))
      (oddEulerModTwo k) := by
  have hp := (multipliable_minus (2 * k) k (Nat.mul_ne_zero (by decide) hk)).hasProd
  have he : (fun i : ℕ => (1 : (ZMod 2)⟦X⟧) - X ^ ((2 * k) * i + k)) =
      (fun i : ℕ => (1 : (ZMod 2)⟦X⟧) - X ^ (k * (2 * i + 1))) := by
    funext i
    congr 2
    ring
  rw [he] at hp
  exact hp

open scoped PowerSeries.WithPiTopology in
private lemma oddEulerModTwo_mul (k : ℕ) (hk : k ≠ 0) :
    oddEulerModTwo k * eulerModTwo (2 * k) = eulerModTwo k := by
  have hp := HasProd.even_mul_odd (f := fun i : ℕ =>
      (1 : (ZMod 2)⟦X⟧) - X ^ (k * (i + 1)))
    ((hasProd_oddEulerModTwo k hk).congr_fun fun i => by simp [Nat.mul_add])
    ((hasProd_eulerModTwo (2 * k) (Nat.mul_ne_zero (by decide) hk)).congr_fun
      fun i => by congr 2; ring)
  exact hp.unique (hasProd_eulerModTwo k hk)

private lemma two_eq_zero : (2 : (ZMod 2)⟦X⟧) = 0 := by
  change C (2 : ZMod 2) = 0
  rw [show (2 : ZMod 2) = 0 by decide, map_zero]

private lemma neg_eq_self_modTwo (f : (ZMod 2)⟦X⟧) : -f = f := by
  apply neg_eq_iff_add_eq_zero.mpr
  rw [← two_mul, two_eq_zero, zero_mul]

open scoped PowerSeries.WithPiTopology in
private lemma eulerModTwo_double (k : ℕ) (hk : k ≠ 0) :
    eulerModTwo (2 * k) = eulerModTwo k ^ 2 := by
  have hlocal (i : ℕ) : ((1 : (ZMod 2)⟦X⟧) - X ^ (k * (i + 1))) ^ 2 =
      1 - X ^ ((2 * k) * (i + 1)) := by
    rw [sub_sq, two_eq_zero]
    simp only [zero_mul, sub_zero, one_pow]
    rw [← pow_mul]
    have hexp : k * (i + 1) * 2 = 2 * k * (i + 1) := by ring
    rw [hexp, sub_eq_add_neg, neg_eq_self_modTwo]
  have hp := ((hasProd_eulerModTwo k hk).pow 2).congr_fun
    (g := fun i => (1 : (ZMod 2)⟦X⟧) - X ^ ((2 * k) * (i + 1)))
    (fun i => (hlocal i).symm)
  exact (hp.unique (hasProd_eulerModTwo (2 * k) (Nat.mul_ne_zero (by decide) hk))).symm

private lemma boundedFactor_mul (i : ℕ) :
    boundedFactor i * (1 - X ^ (2 * i + 1)) =
      (1 : (ZMod 2)⟦X⟧) - X ^ (5 * (2 * i + 1)) := by
  simp only [boundedFactor, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
    zero_mul, pow_zero]
  simp only [Fin.sum_univ_zero, Nat.reduceAdd, zero_add,
    one_mul, add_zero]
  simp only [mul_comm 2 (2 * i + 1), mul_comm 3 (2 * i + 1),
    mul_comm 4 (2 * i + 1), mul_comm 5 (2 * i + 1), pow_mul]
  ring

open scoped PowerSeries.WithPiTopology in
private lemma diagonalSeries_mul_odd :
    diagonalSeries * oddEulerModTwo 1 = oddEulerModTwo 5 := by
  have hp := hasProd_diagonalSeries.mul (hasProd_oddEulerModTwo 1 (by decide))
  apply hp.unique
  exact (hasProd_oddEulerModTwo 5 (by decide)).congr_fun fun i => by
    simpa only [one_mul] using boundedFactor_mul i

private lemma eulerModTwo_ne (k : ℕ) (hk : k ≠ 0) : eulerModTwo k ≠ 0 := by
  intro h
  have hh := congrArg constantCoeff h
  change (constantCoeff (reduceSeries (qEulerProduct k))) = 0 at hh
  rw [← coeff_zero_eq_constantCoeff, reduceSeries, coeff_map,
    coeff_zero_eq_constantCoeff, constantCoeff_qEulerProduct (by omega)] at hh
  norm_num at hh

private lemma oddEulerModTwo_inverse (k : ℕ) (hk : k ≠ 0) :
    oddEulerModTwo k * eulerModTwo k = 1 := by
  apply mul_right_cancel₀ (eulerModTwo_ne k hk)
  calc
    oddEulerModTwo k * eulerModTwo k * eulerModTwo k =
        oddEulerModTwo k * eulerModTwo k ^ 2 := by ring
    _ = eulerModTwo k := by rw [← eulerModTwo_double k hk, oddEulerModTwo_mul k hk]
    _ = 1 * eulerModTwo k := (one_mul _).symm

private lemma diagonalSeries_mul_euler :
    diagonalSeries * eulerModTwo 5 = eulerModTwo 1 := by
  calc
    diagonalSeries * eulerModTwo 5 =
        diagonalSeries * (oddEulerModTwo 1 * eulerModTwo 1) * eulerModTwo 5 := by
      rw [oddEulerModTwo_inverse 1 (by decide), mul_one]
    _ = (diagonalSeries * oddEulerModTwo 1) * eulerModTwo 5 * eulerModTwo 1 := by ring
    _ = eulerModTwo 1 := by
      rw [diagonalSeries_mul_odd, oddEulerModTwo_inverse 5 (by decide), one_mul]

private lemma eulerModTwo_level_five :
    eulerModTwo 1 * eulerModTwo 5 =
      eulerModTwo 1 ^ 6 + X * eulerModTwo 5 ^ 6 := by
  have h := congrArg reduceSeries one_div_f1_cube_f5_two_dissection
  simp only [map_mul, map_pow, map_sub, map_add, map_ofNat] at h
  have h5 : (5 : (ZMod 2)⟦X⟧) = 1 := by
    change C (5 : ZMod 2) = 1
    rw [show (5 : ZMod 2) = 1 by decide, map_one]
  rw [PowerSeries.map_X, two_eq_zero, h5] at h
  simp only [zero_mul, sub_zero, add_zero, one_mul] at h
  change eulerModTwo 2 ^ 10 * eulerModTwo 8 ^ 2 * eulerModTwo 10 ^ 3 * eulerModTwo 20 =
      eulerModTwo 1 ^ 3 * eulerModTwo 2 ^ 3 * eulerModTwo 4 ^ 4 * eulerModTwo 5 *
        eulerModTwo 8 ^ 2 * eulerModTwo 10 ^ 2 * eulerModTwo 20 +
        X * eulerModTwo 1 ^ 3 * eulerModTwo 2 ^ 2 * eulerModTwo 4 ^ 3 * eulerModTwo 5 *
          eulerModTwo 8 ^ 2 * eulerModTwo 10 ^ 3 * eulerModTwo 20 ^ 2 at h
  have h2 := eulerModTwo_double 1 (by decide)
  have h4 := eulerModTwo_double 2 (by decide)
  have h8 := eulerModTwo_double 4 (by decide)
  have h10 := eulerModTwo_double 5 (by decide)
  have h20 := eulerModTwo_double 10 (by decide)
  norm_num only [Nat.reduceMul] at h2 h4 h8 h10 h20
  rw [h20, h10, h8, h4, h2] at h
  apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 35 (eulerModTwo_ne 1 (by decide)))
    (pow_ne_zero 9 (eulerModTwo_ne 5 (by decide))))
  linear_combination h

private lemma diagonalSeries_dissection :
    diagonalSeries = (eulerModTwo 1 ^ 3 * oddEulerModTwo 5) ^ 2 + X * eulerModTwo 5 ^ 4 := by
  apply mul_right_cancel₀ (pow_ne_zero 2 (eulerModTwo_ne 5 (by decide)))
  have hc : (eulerModTwo 1 ^ 3 * oddEulerModTwo 5) ^ 2 * eulerModTwo 5 ^ 2 =
      eulerModTwo 1 ^ 6 := by
    rw [← mul_pow, mul_assoc, oddEulerModTwo_inverse 5 (by decide), mul_one, ← pow_mul]
  calc
    diagonalSeries * eulerModTwo 5 ^ 2 = eulerModTwo 1 * eulerModTwo 5 := by
      rw [pow_two, ← mul_assoc, diagonalSeries_mul_euler]
    _ = eulerModTwo 1 ^ 6 + X * eulerModTwo 5 ^ 6 := eulerModTwo_level_five
    _ = ((eulerModTwo 1 ^ 3 * oddEulerModTwo 5) ^ 2 + X * eulerModTwo 5 ^ 4) *
        eulerModTwo 5 ^ 2 := by rw [add_mul, hc]; ring

private lemma expand_two (f : (ZMod 2)⟦X⟧) : expand 2 (by decide) f = f ^ 2 := by
  simpa only [ZMod.card] using FiniteField.PowerSeries.expand_card f

private lemma coeff_square_odd (f : (ZMod 2)⟦X⟧) (n : ℕ) : (f ^ 2).coeff (2 * n + 1) = 0 := by
  rw [← expand_two f, coeff_expand_of_not_dvd]
  omega

private lemma coeff_fourth_two (f : (ZMod 2)⟦X⟧) (n : ℕ) : (f ^ 4).coeff (4 * n + 2) = 0 := by
  have h : expand 4 (by decide) f = f ^ 4 := by
    change expand (2 * 2) (by decide) f = f ^ 4
    rw [expand_mul 2 (by decide) 2 (by decide), expand_two, expand_two, ← pow_mul]
  rw [← h, coeff_expand_of_not_dvd]
  omega

private lemma even_diag_card (n : ℕ) : Even ((diagSet 4 (4 * n + 3)).card) := by
  apply ZMod.natCast_eq_zero_iff_even.mp
  rw [← coeff_mk (4 * n + 3) (fun N => ((diagSet 4 N).card : ZMod 2))]
  change diagonalSeries.coeff (4 * n + 3) = 0
  rw [diagonalSeries_dissection, map_add]
  have hsq := coeff_square_odd (eulerModTwo 1 ^ 3 * oddEulerModTwo 5) (2 * n + 1)
  have hfour := coeff_fourth_two (eulerModTwo 5) n
  have he : 4 * n + 3 = 2 * (2 * n + 1) + 1 := by omega
  rw [he, hsq]
  have hX : (X * eulerModTwo 5 ^ 4).coeff (2 * (2 * n + 1) + 1) =
      (eulerModTwo 5 ^ 4).coeff (4 * n + 2) := by
    simpa only [pow_one, show (4 * n + 2) + 1 = 2 * (2 * n + 1) + 1 by omega]
      using coeff_X_pow_mul (eulerModTwo 5 ^ 4) 1 (4 * n + 2)
  rw [zero_add, hX]
  exact hfour

/-- **$\varphi_4(4n+3)$ is even.** Let $\varphi_4(n)$ be the number of generalized Frobenius
partitions of $n$ in which each integer appears at most $4$ times in each row. For every natural
number $n$, $\varphi_4(4n + 3) \equiv 0 \pmod 2$.

Source: Bipul Kumar Sarmah and Satyajit Gayan, *Congruences for F-partitions with 4
Repetitions*, INTEGERS 25 (2025), Article A17, Theorem 2 (`integers-2025-A17-thm-2`). -/
public theorem frobeniusPartitionRepCount_four_four_mul_add_three_mod_two (n : ℕ) :
    frobeniusPartitionRepCount 4 (4 * n + 3) ≡ 0 [MOD 2] := by
  change (frobSet 4 (4 * n + 3)).card % 2 = 0 % 2
  have hsplit := Finset.card_filter_add_card_filter_not (s := frobSet 4 (4 * n + 3))
    (fun p => p.swap = p)
  have hfree : Even (((frobSet 4 (4 * n + 3)).filter (fun p => ¬ p.swap = p))).card := by
    apply even_card_of_swap Prod.swap
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨swap_mem hx.1, ?_⟩
      simpa only [Prod.swap_swap, ne_eq, eq_comm] using hx.2
    · intro x _
      exact Prod.swap_swap x
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
  rw [card_filter_swap_eq_diag] at hsplit
  obtain ⟨a, ha⟩ := even_diag_card n
  obtain ⟨b, hb⟩ := hfree
  omega

end

end MetaMathlibExt
