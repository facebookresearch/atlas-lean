/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# Hadamard products of rational power series

`MetaMathlibExt.hadamardProduct_rational` gives a split denominator for the coefficientwise
product and proves that the product of two proper rational series is proper.
-/

namespace MetaMathlibExt

open PowerSeries

namespace hadamardProduct_rational

variable {K : Type*} [Field K]

private def shift (u : ℕ → K) : ℕ → K := fun k ↦ u (k + 1)

private def difference (a : K) : (ℕ → K) →ₗ[K] (ℕ → K) where
  toFun u := shift u - a • u
  map_add' u v := by ext k; simp [shift]; abel
  map_smul' c u := by ext k; simp [shift, mul_sub]; ring

-- The list records the factors of a recurrence polynomial in the forward shift.
private def solutions : List K → Submodule K (ℕ → K)
  | [] => ⊥
  | a :: l => (solutions l).comap (difference a)

private theorem shift_mem (l : List K) {u : ℕ → K} (hu : u ∈ solutions l) :
    shift u ∈ solutions l := by
  induction l generalizing u with
  | nil =>
    obtain rfl : u = 0 := (Submodule.mem_bot K).mp hu
    exact (solutions []).zero_mem
  | cons a l ih => exact ih (u := difference a u) hu

private theorem mem_cons (a : K) {l : List K} {u : ℕ → K} (hu : u ∈ solutions l) :
    u ∈ solutions (a :: l) :=
  (solutions l).sub_mem (shift_mem l hu) ((solutions l).smul_mem a hu)

private theorem mem_append (p : List K) {l : List K} {u : ℕ → K} (hu : u ∈ solutions l) :
    u ∈ solutions (p ++ l) := by
  induction p with
  | nil => exact hu
  | cons a p ih => exact mem_cons a ih

-- The discrete product rule peels off one factor from a row of pairwise products.
private theorem row_mem (a : K) (bs rest : List K) (u v : ℕ → K) (hv : v ∈ solutions bs)
    (hrest : ∀ w ∈ solutions bs, difference a u * w ∈ solutions rest) :
    u * v ∈ solutions (bs.map (a * ·) ++ rest) := by
  induction bs generalizing v with
  | nil =>
    obtain rfl : v = 0 := (Submodule.mem_bot K).mp hv
    rw [mul_zero]
    exact (solutions _).zero_mem
  | cons b bs ih =>
    change difference (a * b) (u * v) ∈ solutions (bs.map (a * ·) ++ rest)
    have hprod : difference (a * b) (u * v) =
        difference a u * shift v + a • (u * difference b v) := by
      ext k
      change u (k + 1) * v (k + 1) - (a * b) * (u k * v k) =
        (u (k + 1) - a * u k) * v (k + 1) + a * (u k * (v (k + 1) - b * v k))
      ring
    rw [hprod]
    exact (solutions _).add_mem (mem_append _ (hrest _ (shift_mem _ hv)))
      ((solutions _).smul_mem _ (ih (difference b v) hv (fun w hw ↦ hrest w (mem_cons b hw))))

private def pairwiseProducts (as bs : List K) : List K := as.flatMap fun a ↦ bs.map (a * ·)

private theorem mul_mem (as bs : List K) {u v : ℕ → K} (hu : u ∈ solutions as)
    (hv : v ∈ solutions bs) : u * v ∈ solutions (pairwiseProducts as bs) := by
  induction as generalizing u v with
  | nil =>
    obtain rfl : u = 0 := (Submodule.mem_bot K).mp hu
    rw [zero_mul]
    exact (solutions _).zero_mem
  | cons a as ih => exact row_mem a bs _ u v hv (fun _ hw ↦ ih hu hw)

private noncomputable def denominator (l : List K) : Polynomial K :=
  (l.map fun a ↦ 1 - Polynomial.C a * Polynomial.X).prod

private theorem denominator_cons (a : K) (l : List K) :
    denominator (a :: l) = (1 - Polynomial.C a * Polynomial.X) * denominator l := rfl

private noncomputable def tailCoeffs (f : PowerSeries K) (N : ℕ) : ℕ → K := fun k ↦ coeff (k + N) f

private theorem difference_tail (a : K) (f : PowerSeries K) (N : ℕ) :
    difference a (tailCoeffs f N) = tailCoeffs (f * (1 - C a * X)) (N + 1) := by
  funext k
  change coeff (k + 1 + N) f - a * coeff (k + N) f = coeff (k + (N + 1)) _
  rw [mul_sub, mul_one, ← mul_assoc, map_sub, ← Nat.add_assoc, coeff_succ_mul_X, coeff_mul_C]
  rw [Nat.add_right_comm k 1 N, mul_comm a]

-- Clearing one denominator factor acts on the coefficient tail by one forward difference.
private theorem tail_mem_iff (l : List K) (f : PowerSeries K) (N : ℕ) :
    tailCoeffs f N ∈ solutions l ↔
      ∀ k, coeff (k + (N + l.length)) (f * (denominator l : PowerSeries K)) = 0 := by
  induction l generalizing f N with
  | nil =>
    change tailCoeffs f N ∈ (⊥ : Submodule K (ℕ → K)) ↔ _
    simp only [Submodule.mem_bot, funext_iff, tailCoeffs, Pi.zero_apply, List.length_nil,
      Nat.add_zero, denominator, List.map_nil, List.prod_nil, Polynomial.coe_one, mul_one]
  | cons a l ih =>
    change difference a (tailCoeffs f N) ∈ solutions l ↔ _
    rw [difference_tail, ih]
    simp only [denominator_cons, Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_one,
      Polynomial.coe_C, Polynomial.coe_X, List.length_cons, mul_assoc]
    rw [Nat.add_right_comm N 1 l.length, Nat.add_assoc]

private theorem numerator_of_bounds (as bs : List K) (A B : PowerSeries K) (R S : Polynomial K)
    (hA : A * (denominator as : PowerSeries K) = R)
    (hB : B * (denominator bs : PowerSeries K) = S) (N : ℕ)
    (hR : R.degree < ↑(N + as.length)) (hS : S.degree < ↑(N + bs.length)) :
    ∃ T : Polynomial K, T.degree < ↑(N + (pairwiseProducts as bs).length) ∧
      mk (fun k ↦ coeff k A * coeff k B) * (denominator (pairwiseProducts as bs) : PowerSeries K)
        = T := by
  let H := mk (fun k ↦ coeff k A * coeff k B)
  let l := pairwiseProducts as bs
  have htail (p : List K) (f : PowerSeries K) (r : Polynomial K)
      (hr : f * (denominator p : PowerSeries K) = r) (hd : r.degree < ↑(N + p.length)) :
      tailCoeffs f N ∈ solutions p := by
    apply (tail_mem_iff p f N).2
    intro k
    rw [hr, Polynomial.coeff_coe]
    exact (Polynomial.degree_lt_iff_coeff_zero _ _).mp hd _ (by omega)
  have hH : tailCoeffs H N ∈ solutions l := by
    have h := mul_mem as bs (htail as A R hA hR) (htail bs B S hB hS)
    have heq : tailCoeffs H N = tailCoeffs A N * tailCoeffs B N := by
      ext k
      simp [tailCoeffs, H]
    rwa [heq]
  let F := H * (denominator l : PowerSeries K)
  refine ⟨trunc (N + l.length) F, degree_trunc_lt _ _, ?_⟩
  change F = ↑(trunc (N + l.length) F)
  ext k
  rw [Polynomial.coeff_coe, coeff_trunc]
  split_ifs with hk
  · rfl
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.le_of_not_gt hk)
    exact (tail_mem_iff l H N).mp hH j

private theorem coe_denominator (l : List K) :
    (denominator l : PowerSeries K) = (l.map fun a ↦ 1 - C a * X).prod := by
  induction l with
  | nil => exact Polynomial.coe_one
  | cons a l ih => simp [denominator_cons, ih]

private theorem coe_denominator_ofFn {m : ℕ} (α : Fin m → K) :
    (denominator (List.ofFn α) : PowerSeries K) = ∏ i, (1 - C (α i) * X) := by
  simp [coe_denominator, List.map_ofFn, List.prod_ofFn, Function.comp_def]

private theorem coe_denominator_pairs {m n : ℕ} (α : Fin m → K) (β : Fin n → K) :
    (denominator (pairwiseProducts (List.ofFn α) (List.ofFn β)) : PowerSeries K) =
      ∏ i, ∏ j, (1 - C (α i * β j) * X) := by
  simp [coe_denominator, pairwiseProducts, List.flatMap_def, List.prod_flatten, List.map_ofFn,
    List.prod_ofFn, Function.comp_def]

private theorem denominator_filter (l : List K) [DecidableEq K] :
    denominator (l.filter (· != 0)) = denominator l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : a = 0 <;> simp [ha, ih, denominator_cons]

private theorem denominator_coeff_zero (l : List K) : (denominator l).coeff 0 = 1 := by
  induction l with
  | nil => simp [denominator]
  | cons a l ih => simp [denominator_cons, Polynomial.mul_coeff_zero, ih]

private theorem denominator_degree {l : List K} (hl : ∀ a ∈ l, a ≠ 0) :
    (denominator l).degree = ↑l.length := by
  induction l with
  | nil => exact Polynomial.degree_one
  | cons a l ih =>
    have ha := Polynomial.degree_C_mul_X (hl a List.mem_cons_self)
    rw [denominator_cons, Polynomial.degree_mul, Polynomial.degree_sub_eq_right_of_degree_lt
      (by rw [Polynomial.degree_one, ha]; exact zero_lt_one), ha,
      ih (fun b hb ↦ hl b (by simp [hb]))]
    simp [add_comm]

-- A proper representation forces the same strict degree inequality for any other denominator.
private theorem proper_bound {f : PowerSeries K} {r : Polynomial K} {l : List K}
    (hl : ∀ a ∈ l, a ≠ 0) (hr : f * (denominator l : PowerSeries K) = r)
    (hp : ∃ P Q : Polynomial K, Q.coeff 0 ≠ 0 ∧ P.degree < Q.degree ∧
      f * (Q : PowerSeries K) = (P : PowerSeries K)) : r.degree < ↑l.length := by
  obtain ⟨P, Q, hQ, hPQ, hf⟩ := hp
  have hcross : r * Q = P * denominator l := by
    apply Polynomial.coe_injective K
    rw [Polynomial.coe_mul, Polynomial.coe_mul, ← hr, ← hf, mul_right_comm]
  have hdeg := congrArg Polynomial.degree hcross
  rw [Polynomial.degree_mul, Polynomial.degree_mul] at hdeg
  have hQ' : Q.degree ≠ ⊥ := Polynomial.degree_ne_bot.mpr (fun h ↦ hQ (by simp [h]))
  rw [← denominator_degree hl]
  apply (WithBot.add_lt_add_iff_right hQ').mp
  rw [hdeg, add_comm (denominator l).degree]
  exact WithBot.add_lt_add_right (denominator_degree hl ▸ WithBot.coe_ne_bot) hPQ

end hadamardProduct_rational

open hadamardProduct_rational

/-- **Hadamard products of rational series.** Let $K$ be a field of characteristic $0$, let
$\alpha_1, \dots, \alpha_m, \beta_1, \dots, \beta_n \in K$, and let $A = \sum_k a_k x^k$ and
$B = \sum_k b_k x^k$ be power series over $K$ such that $A(x) \prod_{i=1}^m (1 - \alpha_i x)$ and
$B(x) \prod_{j=1}^n (1 - \beta_j x)$ are polynomials. Then their Hadamard product
$A * B = \sum_k a_k b_k x^k$ has the property that
$(A * B)(x) \prod_{i=1}^m \prod_{j=1}^n (1 - \alpha_i \beta_j x)$ is a polynomial. Moreover, call a
power series $f$ over $K$ proper if $f Q = P$ for some polynomials $P$, $Q$ over $K$ with
$Q(0) \ne 0$ and $\deg P < \deg Q$. If $A$ and $B$ are proper, then so is $A * B$.

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, Theorem 13 (`jis-2024-24.1.3-thm-13`). -/
public theorem hadamardProduct_rational {K : Type*} [Field K] [CharZero K] (m n : ℕ)
    (α : Fin m → K) (β : Fin n → K) (R S : Polynomial K) (A B : PowerSeries K)
    (hA : A * ∏ i, (1 - C (α i) * X) = (R : PowerSeries K))
    (hB : B * ∏ j, (1 - C (β j) * X) = (S : PowerSeries K)) :
    (∃ T : Polynomial K, PowerSeries.mk (fun k => PowerSeries.coeff k A * PowerSeries.coeff k B) *
        ∏ i, ∏ j, (1 - C (α i * β j) * X) = (T : PowerSeries K)) ∧
      ((∃ P Q : Polynomial K, Q.coeff 0 ≠ 0 ∧ P.degree < Q.degree ∧
          A * (Q : PowerSeries K) = (P : PowerSeries K)) →
        (∃ P Q : Polynomial K, Q.coeff 0 ≠ 0 ∧ P.degree < Q.degree ∧
          B * (Q : PowerSeries K) = (P : PowerSeries K)) →
        ∃ P Q : Polynomial K, Q.coeff 0 ≠ 0 ∧ P.degree < Q.degree ∧
          PowerSeries.mk (fun k => PowerSeries.coeff k A * PowerSeries.coeff k B) *
            (Q : PowerSeries K) = (P : PowerSeries K)) := by
  classical
  let as := List.ofFn α
  let bs := List.ofFn β
  have hA' : A * (denominator as : PowerSeries K) = R := by rwa [coe_denominator_ofFn]
  have hB' : B * (denominator bs : PowerSeries K) = S := by rwa [coe_denominator_ofFn]
  constructor
  · let N := max R.natDegree S.natDegree + 1
    have bound (p : Polynomial K) (hp : p.natDegree < N) (d : ℕ) : p.degree < ↑(N + d) :=
      Polynomial.degree_le_natDegree.trans_lt
        (WithBot.coe_lt_coe.mpr (hp.trans_le (Nat.le_add_right N d)))
    obtain ⟨T, _, hT⟩ := numerator_of_bounds as bs A B R S hA' hB' N
      (bound R (by dsimp [N]; omega) _) (bound S (by dsimp [N]; omega) _)
    exact ⟨T, by rwa [coe_denominator_pairs] at hT⟩
  · intro hproperA hproperB
    let as' := as.filter (· != 0)
    let bs' := bs.filter (· != 0)
    have hne (l : List K) : ∀ a ∈ l.filter (· != 0), a ≠ 0 := by simp
    have hAf : A * (denominator as' : PowerSeries K) = R := by rwa [denominator_filter]
    have hBf : B * (denominator bs' : PowerSeries K) = S := by rwa [denominator_filter]
    obtain ⟨T, hdeg, hT⟩ := numerator_of_bounds as' bs' A B R S hAf hBf 0
      (by simpa using proper_bound (hne as) hAf hproperA)
      (by simpa using proper_bound (hne bs) hBf hproperB)
    have hpair : ∀ c ∈ pairwiseProducts as' bs', c ≠ 0 := by
      intro c hc
      obtain ⟨a, ha, hc⟩ := List.mem_flatMap.mp hc
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
      exact mul_ne_zero (hne as a ha) (hne bs b hb)
    refine ⟨T, denominator (pairwiseProducts as' bs'), ?_, ?_, hT⟩
    · simp [denominator_coeff_zero]
    · simpa [denominator_degree hpair] using hdeg

end MetaMathlibExt
