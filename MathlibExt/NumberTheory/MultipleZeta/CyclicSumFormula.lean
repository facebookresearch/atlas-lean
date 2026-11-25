/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.List.Rotate
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import MathlibExt.NumberTheory.MultipleZeta.Series
import MathlibExt.NumberTheory.MultipleZeta.Convergence
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

open scoped ENNReal

open Topology

section
open scoped BigOperators

namespace MetaMathlibExt

noncomputable def multipleZetaValue (k : List ℕ) : ℝ :=
  ∑' n : Fin k.length → ℕ,
    if (∀ a b : Fin k.length, a < b → n b < n a) ∧
        (∀ a : Fin k.length, 0 < n a) then
      ∏ a : Fin k.length, ((n a : ℝ) ^ k.get a)⁻¹
    else 0

namespace CyclicSumFormula

/-- **The index of a list of positive integers.** A list $(l_1, \dots, l_r)$ of positive
integers determines the multiple-zeta index whose entries are $l_1, \dots, l_r$ in this order;
its weight is $l_1 + \cdots + l_r$. -/
noncomputable def toIndex (l : List ℕ) (hpos : ∀ x ∈ l, 0 < x) :
    MultipleZeta.Index :=
  ⟨l.sum, ⟨l, fun {x} hx => hpos x hx, rfl⟩⟩

-- Admissibility transfers along `toIndex`.
private theorem toIndex_isAdmissible (l : List ℕ) (hpos : ∀ x ∈ l, 0 < x)
    (hadm : MultipleZeta.IsAdmissible l) : (toIndex l hpos).IsAdmissible := by
  rw [MultipleZeta.Index.isAdmissible_iff]
  exact hadm

-- Positivity of the lists occurring on the left-hand side.
private theorem leftList_pos (k : List ℕ) (hk_pos : ∀ n ∈ k, 1 ≤ n)
    (j : Fin k.length) (i : ℕ) (hi : i ∈ Finset.Icc 1 (k.get j - 1)) :
    ∀ x ∈ ((k.get j - i + 1) :: ((k.rotate j.1).tail ++ [i])), 0 < x := by
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  intro x hx
  rw [List.mem_cons] at hx
  rcases hx with rfl | hx
  · omega
  · rw [List.mem_append] at hx
    rcases hx with hx | hx
    · have hxR : x ∈ k.rotate j.1 := List.mem_of_mem_tail hx
      rw [List.mem_rotate] at hxR
      have h1 := hk_pos x hxR
      omega
    · rw [List.mem_singleton] at hx
      omega

-- Admissibility of the lists occurring on the left-hand side.
private theorem leftList_adm (k : List ℕ) (hk_pos : ∀ n ∈ k, 1 ≤ n)
    (j : Fin k.length) (i : ℕ) (hi : i ∈ Finset.Icc 1 (k.get j - 1)) :
    MultipleZeta.IsAdmissible
      ((k.get j - i + 1) :: ((k.rotate j.1).tail ++ [i])) := by
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hi2 : i ≤ k.get j - 1 := (Finset.mem_Icc.mp hi).2
  rw [MultipleZeta.isAdmissible_cons_iff]
  refine ⟨?_, ?_⟩
  · omega
  · intro x hx
    exact leftList_pos k hk_pos j i hi x (List.mem_cons_of_mem _ hx)

-- Positivity of the lists occurring on the right-hand side.
private theorem rightList_pos (k : List ℕ) (hk_pos : ∀ n ∈ k, 1 ≤ n)
    (j : Fin k.length) :
    ∀ x ∈ ((k.get j + 1) :: (k.rotate j.1).tail), 0 < x := by
  intro x hx
  rw [List.mem_cons] at hx
  rcases hx with rfl | hx
  · omega
  · have hxR : x ∈ k.rotate j.1 := List.mem_of_mem_tail hx
    rw [List.mem_rotate] at hxR
    have h1 := hk_pos x hxR
    omega

-- Admissibility of the lists occurring on the right-hand side.
private theorem rightList_adm (k : List ℕ) (hk_pos : ∀ n ∈ k, 1 ≤ n)
    (j : Fin k.length) :
    MultipleZeta.IsAdmissible ((k.get j + 1) :: (k.rotate j.1).tail) := by
  rw [MultipleZeta.isAdmissible_cons_iff]
  refine ⟨?_, ?_⟩
  · have h1 := hk_pos _ (List.get_mem k j)
    omega
  · intro x hx
    exact rightList_pos k hk_pos j x (List.mem_cons_of_mem _ hx)

/-- **Left-hand indices of the cyclic sum formula.** Let $k = (k_1, \dots, k_l)$ be a list of
positive integers, with subscripts read modulo $l$. For $1 \le j \le l$ and a natural number
$i$, the left-hand index of $k$ at $(j, i)$ is the index
$(k_j - i + 1, k_{j+1}, \dots, k_{j+l-1}, i)$ when $1 \le i \le k_j - 1$, and the index $(2)$
otherwise. The run $k_{j+1}, \dots, k_{j+l-1}$ is empty when $l = 1$. -/
noncomputable def leftIndex (k : List ℕ) (hk_pos : ∀ n ∈ k, 1 ≤ n)
    (j : Fin k.length) (i : ℕ) : MultipleZeta.Index :=
  if hmem : i ∈ Finset.Icc 1 (k.get j - 1) then
    toIndex ((k.get j - i + 1) :: ((k.rotate j.1).tail ++ [i])) (by
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hmem).1
      intro x hx
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · omega
      · rw [List.mem_append] at hx
        rcases hx with hx | hx
        · have hxR : x ∈ k.rotate j.1 := List.mem_of_mem_tail hx
          rw [List.mem_rotate] at hxR
          have h1 := hk_pos x hxR
          omega
        · rw [List.mem_singleton] at hx
          omega)
  else
    toIndex [2] (fun x hx => by rw [List.mem_singleton] at hx; omega)

/-- **Right-hand indices of the cyclic sum formula.** Let $k = (k_1, \dots, k_l)$ be a list of
positive integers, with subscripts read modulo $l$. For $1 \le j \le l$, the right-hand index of
$k$ at $j$ is the index $(k_j + 1, k_{j+1}, \dots, k_{j+l-1})$, where the run
$k_{j+1}, \dots, k_{j+l-1}$ is empty when $l = 1$. -/
noncomputable def rightIndex (k : List ℕ) (hk_pos : ∀ n ∈ k, 1 ≤ n)
    (j : Fin k.length) : MultipleZeta.Index :=
  toIndex ((k.get j + 1) :: (k.rotate j.1).tail) (by
    intro x hx
    rw [List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · have hxR : x ∈ k.rotate j.1 := List.mem_of_mem_tail hx
      rw [List.mem_rotate] at hxR
      have h1 := hk_pos x hxR
      omega)

/-- **Left-hand indices of the cyclic sum formula are admissible or empty.** For every list
$k = (k_1, \dots, k_l)$ of positive integers, every $1 \le j \le l$ and every natural number $i$,
the left-hand index of the cyclic sum formula of $k$ at $(j, i)$ is admissible or empty. -/
theorem leftIndex_isAdmissibleOrEmpty (k : List ℕ) (hk_pos : ∀ n ∈ k, 1 ≤ n)
    (j : Fin k.length) (i : ℕ) :
    (leftIndex k hk_pos j i).IsAdmissibleOrEmpty := by
  unfold leftIndex
  by_cases hmem : i ∈ Finset.Icc 1 (k.get j - 1)
  · rw [dite_eq_left hmem]
    exact Or.inl
      (toIndex_isAdmissible _ _ (leftList_adm k hk_pos j i hmem))
  · rw [dite_eq_right hmem]
    refine Or.inl (toIndex_isAdmissible _ _ ?_)
    rw [MultipleZeta.isAdmissible_cons_iff]
    refine ⟨le_rfl, ?_⟩
    intro x hx
    simp at hx

/-- **Right-hand indices of the cyclic sum formula are admissible or empty.** For every list
$k = (k_1, \dots, k_l)$ of positive integers and every $1 \le j \le l$, the right-hand index of
the cyclic sum formula of $k$ at $j$ is admissible or empty. -/
theorem rightIndex_isAdmissibleOrEmpty (k : List ℕ) (hk_pos : ∀ n ∈ k, 1 ≤ n)
    (j : Fin k.length) :
    (rightIndex k hk_pos j).IsAdmissibleOrEmpty := by
  exact Or.inl (toIndex_isAdmissible _ _ (rightList_adm k hk_pos j))

private lemma rotate_eq_get_cons_tail (k : List ℕ) (j : Fin k.length) :
    k.rotate j.1 = k.get j :: (k.rotate j.1).tail := by
  have hhead : (k.rotate j.1).head? = some (k.get j) := by
    rw [List.head?_rotate j.2, List.getElem?_eq_getElem j.2, List.get_eq_getElem]
  have hne : k.rotate j.1 ≠ [] := by
    intro h
    rw [h] at hhead
    simp at hhead
  obtain ⟨b, l', hcons⟩ := List.exists_cons_of_ne_nil hne
  have hb : b = k.get j := by
    have h1 : (b :: l').head? = some b := rfl
    rw [hcons] at hhead
    rw [h1] at hhead
    exact Option.some_inj.mp hhead
  rw [hcons, List.tail_cons, hb]

private lemma rotate_tail_append_get (k : List ℕ) (j : Fin k.length) :
    (k.rotate j.1).tail ++ [k.get j] = k.rotate (j.1 + 1) := by
  have h := rotate_eq_get_cons_tail k j
  have hrr : k.rotate (j.1 + 1) = (k.rotate j.1).tail ++ [k.get j] := by
    conv_lhs => rw [← List.rotate_rotate]
    conv_lhs => rw [h]
    rw [show (1 : ℕ) = 0 + 1 from rfl, List.rotate_cons_succ, List.rotate_zero]
  exact hrr.symm

private lemma sum_rotate_succ (k : List ℕ) (f : List ℕ → ℝ≥0∞) :
    ∑ j : Fin k.length, f (k.rotate (j.1 + 1)) = ∑ j : Fin k.length, f (k.rotate j.1) := by
  rcases eq_or_ne k [] with rfl | hne
  · simp
  · have hne0 : k.length ≠ 0 := fun h => hne (List.length_eq_zero_iff.mp h)
    have hpos : 0 < k.length := Nat.pos_of_ne_zero hne0
    have hlen : ∃ m, k.length = m + 1 := ⟨k.length - 1, by omega⟩
    obtain ⟨m, hm⟩ := hlen
    rw [Fin.sum_univ_eq_sum_range (fun n => f (k.rotate (n + 1))) k.length,
      Fin.sum_univ_eq_sum_range (fun n => f (k.rotate n)) k.length,
      hm, Finset.sum_range_succ, Finset.sum_range_succ']
    congr 1
    rw [← hm, List.rotate_length, List.rotate_zero]

-- N5 (real version). Note: the blueprint's ENNReal statement carries a `-` before the
-- finite sum, which is a typo (false already at L=2, x=5, c=2: 1/75 - 1/50 ≠ 1/30,
-- while 1/75 + 1/50 = 1/30). The correct identity, used in N7 and in (*), has `+`.
private lemma partial_fraction_real (x c : ℝ) (n : ℕ) (hx : 0 < x) (hc : 0 < c) (hcx : c < x) :
    1 / (x ^ (n + 1) * (x - c)) + ∑ i ∈ Finset.Icc 1 n, 1 / (x ^ (n + 1 - i + 1) * c ^ i)
      = 1 / (x * c ^ n * (x - c)) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hxc : x - c ≠ 0 := sub_ne_zero.mpr (ne_of_gt hcx)
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    rw [Finset.sum_Icc_succ_top h1 (fun i => 1 / (x ^ (n + 1 + 1 - i + 1) * c ^ i))]
    have hS : (∑ i ∈ Finset.Icc 1 n, 1 / (x ^ (n + 1 + 1 - i + 1) * c ^ i))
        = (1 / x) * (∑ i ∈ Finset.Icc 1 n, 1 / (x ^ (n + 1 - i + 1) * c ^ i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have him : i ≤ n := (Finset.mem_Icc.mp hi).2
      have hexp : n + 1 + 1 - i + 1 = (n + 1 - i + 1) + 1 := by omega
      rw [hexp, pow_succ]
      field_simp
    have hT : (1 : ℝ) / (x ^ (n + 1 + 1 - (n + 1) + 1) * c ^ (n + 1))
        = 1 / (x ^ 2 * c ^ (n + 1)) := by
      have hexp2 : n + 1 + 1 - (n + 1) + 1 = 2 := by omega
      rw [hexp2]
    have hA : (1 : ℝ) / (x ^ (n + 1 + 1) * (x - c))
        = (1 / x) * (1 / (x ^ (n + 1) * (x - c))) := by
      rw [pow_succ]
      field_simp
    have hB : (1 : ℝ) / (x * c ^ (n + 1) * (x - c))
        = (1 / x) * (1 / (x * c ^ n * (x - c))) + 1 / (x ^ 2 * c ^ (n + 1)) := by
      field_simp
      ring
    rw [hS, hT, hA, hB]
    linear_combination (1 / x) * ih

-- D1: nested finite sums over decreasing chains; bottom weight `w` at the chain bottom
-- (or at `A` itself when the list is empty).
private noncomputable def tailW : List ℕ → (ℕ → ℝ≥0∞) → ℕ → ℝ≥0∞
  | [], w, A => w A
  | e :: t, w, A => ∑ y ∈ Finset.Ioo 0 A, ((y : ℝ≥0∞) ^ e)⁻¹ * tailW t w y

-- D2: top-level sum over the largest variable.
private noncomputable def topSum (e : ℕ) (t : List ℕ) (w : ℕ → ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' x : ℕ, if 0 < x then ((x : ℝ≥0∞) ^ e)⁻¹ * tailW t (w x) x else 0

-- D3: ENNReal multiple zeta value in recursive form.
private noncomputable def zetaR : List ℕ → ℝ≥0∞
  | [] => 1
  | e :: t => topSum e t (fun _ _ => 1)

-- D4: harmonic tail weight.
private noncomputable def harmTail (x y : ℕ) : ℝ≥0∞ :=
  ∑ c ∈ Finset.range y, (((x - c : ℕ) : ℝ≥0∞))⁻¹

-- D5: auxiliary series T.
private noncomputable def cycT : List ℕ → ℝ≥0∞
  | [] => 0
  | e :: t => topSum e t harmTail

-- D6: remainder weight after splitting off the top variable.
private noncomputable def wWeight (L x y : ℕ) : ℝ≥0∞ :=
  ∑ c ∈ Finset.Ioo 0 y, (x : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) ^ (L - 1))⁻¹ * (((x - c : ℕ) : ℝ≥0∞))⁻¹

-- D7: ENNReal multiple zeta value in tuple form (Wanted summand with ℝ≥0∞).
private noncomputable def zetaE (l : List ℕ) : ℝ≥0∞ :=
  ∑' n : Fin l.length → ℕ,
    if (∀ a b : Fin l.length, a < b → n b < n a) ∧ (∀ a, 0 < n a) then
      ∏ a, ((n a : ℝ≥0∞) ^ l.get a)⁻¹
    else 0

-- N1(a): `tailW` distributes over finite sums of weights.
private lemma tailW_sum (t : List ℕ) {ι : Type*} (s : Finset ι) (v : ι → ℕ → ℝ≥0∞) (A : ℕ) :
    tailW t (fun y => ∑ i ∈ s, v i y) A = ∑ i ∈ s, tailW t (v i) A := by
  induction t generalizing A with
  | nil => rfl
  | cons e t ih =>
    unfold tailW
    trans ∑ y ∈ Finset.Ioo 0 A, ∑ i ∈ s, ((y : ℝ≥0∞) ^ e)⁻¹ * tailW t (v i) y
    · apply Finset.sum_congr rfl
      intro y _
      rw [ih, Finset.mul_sum]
    · exact Finset.sum_comm

-- N1(a) binary version.
private lemma tailW_add (t : List ℕ) (w w' : ℕ → ℝ≥0∞) (A : ℕ) :
    tailW t (fun y => w y + w' y) A = tailW t w A + tailW t w' A := by
  induction t generalizing A with
  | nil => rfl
  | cons e t ih =>
    unfold tailW
    trans ∑ y ∈ Finset.Ioo 0 A, (((y : ℝ≥0∞) ^ e)⁻¹ * tailW t w y
      + ((y : ℝ≥0∞) ^ e)⁻¹ * tailW t w' y)
    · apply Finset.sum_congr rfl
      intro y _
      rw [ih, mul_add]
    · exact Finset.sum_add_distrib

-- N1(b): scalar weights pull out.
private lemma tailW_const_mul (t : List ℕ) (r : ℝ≥0∞) (w : ℕ → ℝ≥0∞) (A : ℕ) :
    tailW t (fun y => r * w y) A = r * tailW t w A := by
  induction t generalizing A with
  | nil => rfl
  | cons e t ih =>
    unfold tailW
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [ih, mul_left_comm]

-- N1(c): congruence under the chain constraint.
private lemma tailW_congr (t : List ℕ) (w w' : ℕ → ℝ≥0∞) (A : ℕ) (hA : 0 < A)
    (h : ∀ y, 0 < y → y ≤ A → w y = w' y) : tailW t w A = tailW t w' A := by
  induction t generalizing A with
  | nil => exact h A hA (le_refl A)
  | cons e t ih =>
    unfold tailW
    apply Finset.sum_congr rfl
    intro y hy
    have hy0 : 0 < y := (Finset.mem_Ioo.mp hy).1
    have hyA : y ≤ A := le_of_lt (Finset.mem_Ioo.mp hy).2
    congr 1
    exact ih y hy0 (fun z hz0 hz => h z hz0 (le_trans hz hyA))

-- N1(d): monotonicity under the chain constraint.
private lemma tailW_mono (t : List ℕ) (w w' : ℕ → ℝ≥0∞) (A : ℕ) (hA : 0 < A)
    (h : ∀ y, 0 < y → y ≤ A → w y ≤ w' y) : tailW t w A ≤ tailW t w' A := by
  induction t generalizing A with
  | nil => exact h A hA (le_refl A)
  | cons e t ih =>
    unfold tailW
    apply Finset.sum_le_sum
    intro y hy
    have hy0 : 0 < y := (Finset.mem_Ioo.mp hy).1
    have hyA : y ≤ A := le_of_lt (Finset.mem_Ioo.mp hy).2
    exact mul_le_mul_right (ih y hy0 (fun z hz0 hz => h z hz0 (le_trans hz hyA))) _

-- N1(e): appending an exponent is a change of the bottom weight.
private lemma tailW_append (t : List ℕ) (e : ℕ) (w : ℕ → ℝ≥0∞) (A : ℕ) :
    tailW (t ++ [e]) w A
      = tailW t (fun y => ∑ c ∈ Finset.Ioo 0 y, ((c : ℝ≥0∞) ^ e)⁻¹ * w c) A := by
  induction t generalizing A with
  | nil => rfl
  | cons e' t ih =>
    rw [List.cons_append]
    unfold tailW
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    exact ih y

-- N2(a): `tailW` commutes with `tsum`.
private lemma tailW_tsum (t : List ℕ) {ι : Type*} (v : ι → ℕ → ℝ≥0∞) (A : ℕ) :
    (∑' i, tailW t (v i) A) = tailW t (fun y => ∑' i, v i y) A := by
  induction t generalizing A with
  | nil => rfl
  | cons e t ih =>
    unfold tailW
    rw [Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
    apply Finset.sum_congr rfl
    intro y _
    rw [ENNReal.tsum_mul_left, ih]

-- N2(b): swapping a triangular sum.
private lemma tsum_Ioo_swap (F : ℕ → ℕ → ℝ≥0∞) :
    (∑' x : ℕ, (if 0 < x then ∑ y ∈ Finset.Ioo 0 x, F x y else 0))
      = ∑' y : ℕ, (if 0 < y then ∑' x : ℕ, (if y < x then F x y else 0) else 0) := by
  have h1 : ∀ x : ℕ, (∑ y ∈ Finset.Ioo 0 x, F x y)
      = ∑' y : ℕ, (if y ∈ Finset.Ioo 0 x then F x y else 0) := by
    intro x
    have hsupp : Function.support (fun y => if y ∈ Finset.Ioo 0 x then F x y else 0)
        ⊆ ↑(Finset.Ioo 0 x) := by
      intro y hy
      rw [Finset.mem_coe]
      simp only [Function.mem_support, ne_eq] at hy
      by_contra hm
      exact hy (ite_eq_right hm)
    have h2 : (∑' y : ℕ, (if y ∈ Finset.Ioo 0 x then F x y else 0))
        = ∑ y ∈ Finset.Ioo 0 x, (if y ∈ Finset.Ioo 0 x then F x y else 0) :=
      tsum_eq_sum' hsupp
    rw [h2]
    apply Finset.sum_congr rfl
    intro y hy
    rw [ite_eq_left hy]
  have hJ : ∀ x : ℕ, (if 0 < x then ∑ y ∈ Finset.Ioo 0 x, F x y else 0)
      = ∑' y : ℕ, (if 0 < x ∧ 0 < y ∧ y < x then F x y else 0) := by
    intro x
    by_cases hx : 0 < x
    · rw [ite_eq_left hx, h1 x]
      apply tsum_congr
      intro y
      by_cases hy : y ∈ Finset.Ioo 0 x
      · obtain ⟨hy0, hyx⟩ := Finset.mem_Ioo.mp hy
        rw [ite_eq_left hy, ite_eq_left ⟨hx, hy0, hyx⟩]
      · rw [ite_eq_right hy, ite_eq_right (fun h => hy (Finset.mem_Ioo.mpr ⟨h.2.1, h.2.2⟩))]
    · rw [ite_eq_right hx]
      rw [tsum_congr (fun y => ite_eq_right (fun h : 0 < x ∧ 0 < y ∧ y < x => hx h.1)),
        tsum_zero]
  rw [tsum_congr hJ, ENNReal.tsum_comm]
  apply tsum_congr
  intro y
  by_cases hy : 0 < y
  · rw [ite_eq_left hy]
    apply tsum_congr
    intro x
    by_cases hxy : y < x
    · have hx : 0 < x := lt_trans hy hxy
      rw [ite_eq_left ⟨hx, hy, hxy⟩, ite_eq_left hxy]
    · rw [ite_eq_right (fun h => hxy h.2.2), ite_eq_right hxy]
  · rw [ite_eq_right hy]
    rw [tsum_congr (fun x => ite_eq_right (fun h : 0 < x ∧ 0 < y ∧ y < x => hy h.2.1)),
      tsum_zero]

-- N5 transfer to ℝ≥0∞ via `toReal` injectivity from `partial_fraction_real`.
-- Note: sign corrected from `-` to `+` (see `partial_fraction_real` comment above).
private lemma partial_fraction_cyclic (x c L : ℕ) (hc : 1 ≤ c) (hcx : c < x) (hL : 1 ≤ L) :
    ((x : ℝ≥0∞) ^ L)⁻¹ * (((x - c : ℕ) : ℝ≥0∞))⁻¹
      + ∑ i ∈ Finset.Icc 1 (L - 1),
        ((x : ℝ≥0∞) ^ (L - i + 1))⁻¹ * ((c : ℝ≥0∞) ^ i)⁻¹
      = (x : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) ^ (L - 1))⁻¹ * (((x - c : ℕ) : ℝ≥0∞))⁻¹ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
  simp only [Nat.succ_eq_add_one] at *
  rw [Nat.add_sub_cancel]
  have hx0 : x ≠ 0 := by omega
  have hc0' : c ≠ 0 := by omega
  have hsub0 : x - c ≠ 0 := by omega
  have hxE0 : (x : ℝ≥0∞) ≠ 0 := by exact_mod_cast hx0
  have hcE0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc0'
  have hsubE0 : ((x - c : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hsub0
  have hxET : (x : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top x
  have hcET : (c : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top c
  have hsubET : ((x - c : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hpowE_ne_zero : ∀ (a : ℝ≥0∞) (k : ℕ), a ≠ 0 → a ^ k ≠ 0 :=
    fun a k ha => ENNReal.pow_ne_zero ha k
  have hA_ne : ((x : ℝ≥0∞) ^ (n + 1))⁻¹ * (((x - c : ℕ) : ℝ≥0∞))⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (hpowE_ne_zero _ _ hxE0))
      (ENNReal.inv_ne_top.mpr hsubE0)
  have hS_ne : ∀ i ∈ Finset.Icc 1 n,
      ((x : ℝ≥0∞) ^ (n + 1 - i + 1))⁻¹ * ((c : ℝ≥0∞) ^ i)⁻¹ ≠ ⊤ := by
    intro i _
    exact ENNReal.mul_ne_top
      (ENNReal.inv_ne_top.mpr (hpowE_ne_zero _ _ hxE0))
      (ENNReal.inv_ne_top.mpr (hpowE_ne_zero _ _ hcE0))
  have hLHS_ne : ((x : ℝ≥0∞) ^ (n + 1))⁻¹ * (((x - c : ℕ) : ℝ≥0∞))⁻¹
      + ∑ i ∈ Finset.Icc 1 n,
        ((x : ℝ≥0∞) ^ (n + 1 - i + 1))⁻¹ * ((c : ℝ≥0∞) ^ i)⁻¹ ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hA_ne, ENNReal.sum_ne_top.mpr hS_ne⟩
  have hRHS_ne : (x : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) ^ n)⁻¹ * (((x - c : ℕ) : ℝ≥0∞))⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hxE0)
        (ENNReal.inv_ne_top.mpr (hpowE_ne_zero _ _ hcE0)))
      (ENNReal.inv_ne_top.mpr hsubE0)
  rw [← ENNReal.toReal_eq_toReal_iff' hLHS_ne hRHS_ne]
  rw [ENNReal.toReal_add hA_ne (ENNReal.sum_ne_top.mpr hS_ne)]
  rw [ENNReal.toReal_sum hS_ne]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_natCast]
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
  have hcxR : (c : ℝ) < (x : ℝ) := by exact_mod_cast hcx
  have hsub : ((((x - c : ℕ))) : ℝ) = (x : ℝ) - (c : ℝ) :=
    Nat.cast_sub (le_of_lt hcx)
  have hreal := partial_fraction_real (x : ℝ) (c : ℝ) n hxR hcR hcxR
  simp only [one_div, mul_inv] at hreal
  rw [hsub]
  exact hreal

-- Chain condition on `Fin.cons` splits into the tail chain plus the below-top bound.
private lemma chain_cons_iff (n y : ℕ) (n' : Fin n → ℕ) :
    (∀ a b : Fin (n + 1), a < b →
      Fin.cons (α := fun _ => ℕ) y n' b < Fin.cons (α := fun _ => ℕ) y n' a)
    ↔ (∀ a b : Fin n, a < b → n' b < n' a) ∧ (∀ i, n' i < y) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro a b hab
      have hss : a.succ < b.succ := Fin.succ_lt_succ_iff.mpr hab
      have h2 := h a.succ b.succ hss
      simp only [Fin.cons_succ] at h2
      exact h2
    · intro i
      have h0s : (0 : Fin (n + 1)) < i.succ :=
        Fin.pos_iff_ne_zero.mpr (Fin.succ_ne_zero i)
      have h2 := h 0 i.succ h0s
      simp only [Fin.cons_succ, Fin.cons_zero] at h2
      exact h2
  · intro h a b hab
    obtain ⟨hc', hb'⟩ := h
    rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨i, rfl⟩
    · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨j, rfl⟩
      · exact absurd hab (lt_irrefl 0)
      · simp only [Fin.cons_succ, Fin.cons_zero]
        exact hb' j
    · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨j, rfl⟩
      · exact absurd hab (not_lt_of_ge (Fin.zero_le _))
      · have hij : i < j := Fin.succ_lt_succ_iff.mp hab
        simp only [Fin.cons_succ]
        exact hc' i j hij

-- Positivity on `Fin.cons` splits into head and tail positivity.
private lemma pos_cons_iff (n y : ℕ) (n' : Fin n → ℕ) :
    (∀ a : Fin (n + 1), 0 < Fin.cons (α := fun _ => ℕ) y n' a) ↔ (0 < y ∧ ∀ a, 0 < n' a) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h2 := h 0
      rwa [Fin.cons_zero] at h2
    · intro a
      have h2 := h a.succ
      rwa [Fin.cons_succ] at h2
  · intro h a
    obtain ⟨hy0, hp'⟩ := h
    rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨i, rfl⟩
    · rw [Fin.cons_zero]
      exact hy0
    · rw [Fin.cons_succ]
      exact hp' i

-- Upper bound on `Fin.cons` splits into head and tail bounds.
private lemma bnd_cons_iff (n y A : ℕ) (n' : Fin n → ℕ) :
    (∀ a : Fin (n + 1), Fin.cons (α := fun _ => ℕ) y n' a < A) ↔ (y < A ∧ ∀ a, n' a < A) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h2 := h 0
      rwa [Fin.cons_zero] at h2
    · intro a
      have h2 := h a.succ
      rwa [Fin.cons_succ] at h2
  · intro h a
    obtain ⟨hyA, hb'⟩ := h
    rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨i, rfl⟩
    · rw [Fin.cons_zero]
      exact hyA
    · rw [Fin.cons_succ]
      exact hb' i

-- The reciprocal product on `Fin.cons` splits off the head factor.
private lemma prod_cons_split (h : ℕ) (tl : List ℕ) (y : ℕ) (n' : Fin tl.length → ℕ) :
    (∏ a : Fin (tl.length + 1), ((Fin.cons (α := fun _ => ℕ) y n' a : ℝ≥0∞) ^ (h :: tl).get a)⁻¹)
    = ((y : ℝ≥0∞) ^ h)⁻¹ * ∏ a', ((n' a' : ℝ≥0∞) ^ tl.get a')⁻¹ := by
  have hget0 : (h :: tl).get (0 : Fin (tl.length + 1)) = h := rfl
  have hgetS : ∀ i : Fin tl.length, (h :: tl).get i.succ = tl.get i := fun i => rfl
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, hget0, hgetS]

-- Bounded version: tuple sum with an upper bound equals the nested finite sum.
private lemma zetaE_bounded_eq_tailW (t : List ℕ) (A : ℕ) :
    (∑' n : Fin t.length → ℕ,
      if (∀ a b : Fin t.length, a < b → n b < n a) ∧ (∀ a, 0 < n a) ∧ (∀ a, n a < A)
      then ∏ a, ((n a : ℝ≥0∞) ^ t.get a)⁻¹ else 0)
    = tailW t (fun _ => 1) A := by
  induction t generalizing A with
  | nil =>
    rw [tsum_eq_single default]
    · rw [ite_eq_left ⟨fun a => Fin.elim0 a, fun a => Fin.elim0 a, fun a => Fin.elim0 a⟩]
      rfl
    · intro b hb
      exfalso
      apply hb
      funext i
      exact Fin.elim0 i
  | cons h tl ih =>
    refine (Equiv.tsum_eq (Fin.consEquiv (n := tl.length) (fun _ => ℕ)) _).symm.trans ?_
    rw [ENNReal.tsum_prod']
    simp only [Fin.consEquiv_apply]
    have hcond : ∀ (y : ℕ) (n' : Fin tl.length → ℕ),
        ((∀ a b : Fin (tl.length + 1), a < b →
            Fin.cons (α := fun _ => ℕ) y n' b < Fin.cons (α := fun _ => ℕ) y n' a)
          ∧ (∀ a, 0 < Fin.cons (α := fun _ => ℕ) y n' a)
          ∧ (∀ a, Fin.cons (α := fun _ => ℕ) y n' a < A))
        ↔ (0 < y ∧ y < A) ∧
          ((∀ a b : Fin tl.length, a < b → n' b < n' a) ∧ (∀ a, 0 < n' a) ∧ (∀ a, n' a < y)) := by
      intro y n'
      rw [chain_cons_iff, pos_cons_iff, bnd_cons_iff]
      constructor
      · intro h
        obtain ⟨⟨hc', hb'⟩, ⟨hy0, hp'⟩, ⟨hyA, _⟩⟩ := h
        exact ⟨⟨hy0, hyA⟩, hc', hp', hb'⟩
      · intro h
        obtain ⟨⟨hy0, hyA⟩, hc', hp', hb'⟩ := h
        refine ⟨⟨hc', hb'⟩, ⟨hy0, hp'⟩, hyA, ?_⟩
        intro i
        exact lt_trans (hb' i) hyA
    have hpoint : ∀ y : ℕ, (∑' n' : Fin tl.length → ℕ,
        (if (∀ a b : Fin (tl.length + 1), a < b →
              Fin.cons (α := fun _ => ℕ) y n' b < Fin.cons (α := fun _ => ℕ) y n' a)
            ∧ (∀ a, 0 < Fin.cons (α := fun _ => ℕ) y n' a)
            ∧ (∀ a, Fin.cons (α := fun _ => ℕ) y n' a < A)
          then ∏ a : Fin (tl.length + 1),
            ((Fin.cons (α := fun _ => ℕ) y n' a : ℝ≥0∞) ^ (h :: tl).get a)⁻¹ else 0))
        = (if 0 < y ∧ y < A then ((y : ℝ≥0∞) ^ h)⁻¹ * tailW tl (fun _ => 1) y else 0) := by
      intro y
      by_cases hQ : 0 < y ∧ y < A
      · rw [ite_eq_left hQ]
        trans ((y : ℝ≥0∞) ^ h)⁻¹ * ∑' n' : Fin tl.length → ℕ,
          (if (∀ a b : Fin tl.length, a < b → n' b < n' a) ∧ (∀ a, 0 < n' a) ∧ (∀ a, n' a < y)
           then ∏ a', ((n' a' : ℝ≥0∞) ^ tl.get a')⁻¹ else 0)
        · rw [← ENNReal.tsum_mul_left]
          apply tsum_congr
          intro n'
          simp only [hcond y n', and_iff_right hQ, prod_cons_split h tl y n']
          split_ifs with hP
          · rfl
          · exact (mul_zero _).symm
        · rw [ih y]
      · rw [ite_eq_right hQ]
        trans (∑' _ : Fin tl.length → ℕ, (0 : ℝ≥0∞))
        · apply tsum_congr
          intro n'
          simp only [hcond y n']
          exact ite_eq_right (fun h => hQ h.1)
        · exact tsum_zero
    trans ∑' y : ℕ, (if 0 < y ∧ y < A then ((y : ℝ≥0∞) ^ h)⁻¹ * tailW tl (fun _ => 1) y else 0)
    · exact tsum_congr hpoint
    · have hsupp : Function.support
          (fun y : ℕ => if 0 < y ∧ y < A then ((y : ℝ≥0∞) ^ h)⁻¹ * tailW tl (fun _ => 1) y else 0)
          ⊆ ↑(Finset.Ioo 0 A) := by
        intro y hy
        simp only [Function.mem_support, ne_eq] at hy
        rw [Finset.mem_coe, Finset.mem_Ioo]
        by_contra hcon
        exact hy (ite_eq_right hcon)
      rw [tsum_eq_sum' hsupp]
      have hRHS : tailW (h :: tl) (fun _ => 1) A
          = ∑ y ∈ Finset.Ioo 0 A, ((y : ℝ≥0∞) ^ h)⁻¹ * tailW tl (fun _ => 1) y := rfl
      rw [hRHS]
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.mem_Ioo] at hy
      rw [ite_eq_left hy]

-- N3: tuple sum = recursive sum.
private lemma zetaE_cons_eq_zetaR (e : ℕ) (t : List ℕ) : zetaE (e :: t) = zetaR (e :: t) := by
  unfold zetaE zetaR topSum
  refine (Equiv.tsum_eq (Fin.consEquiv (n := t.length) (fun _ => ℕ)) _).symm.trans ?_
  rw [ENNReal.tsum_prod']
  simp only [Fin.consEquiv_apply]
  have hcond : ∀ (x : ℕ) (n' : Fin t.length → ℕ),
      ((∀ a b : Fin (t.length + 1), a < b →
          Fin.cons (α := fun _ => ℕ) x n' b < Fin.cons (α := fun _ => ℕ) x n' a)
        ∧ (∀ a, 0 < Fin.cons (α := fun _ => ℕ) x n' a))
      ↔ (0 < x) ∧
        ((∀ a b : Fin t.length, a < b → n' b < n' a) ∧ (∀ a, 0 < n' a) ∧ (∀ a, n' a < x)) := by
    intro x n'
    rw [chain_cons_iff, pos_cons_iff]
    constructor
    · intro h
      obtain ⟨⟨hc', hb'⟩, ⟨hx0, hp'⟩⟩ := h
      exact ⟨hx0, hc', hp', hb'⟩
    · intro h
      obtain ⟨hx0, hc', hp', hb'⟩ := h
      exact ⟨⟨hc', hb'⟩, hx0, hp'⟩
  have hpoint : ∀ x : ℕ, (∑' n' : Fin t.length → ℕ,
      (if (∀ a b : Fin (t.length + 1), a < b →
            Fin.cons (α := fun _ => ℕ) x n' b < Fin.cons (α := fun _ => ℕ) x n' a)
          ∧ (∀ a, 0 < Fin.cons (α := fun _ => ℕ) x n' a)
        then ∏ a : Fin (t.length + 1),
          ((Fin.cons (α := fun _ => ℕ) x n' a : ℝ≥0∞) ^ (e :: t).get a)⁻¹ else 0))
      = (if 0 < x then ((x : ℝ≥0∞) ^ e)⁻¹ * tailW t (fun _ => 1) x else 0) := by
    intro x
    by_cases hQ : 0 < x
    · rw [ite_eq_left hQ]
      trans ((x : ℝ≥0∞) ^ e)⁻¹ * ∑' n' : Fin t.length → ℕ,
        (if (∀ a b : Fin t.length, a < b → n' b < n' a) ∧ (∀ a, 0 < n' a) ∧ (∀ a, n' a < x)
         then ∏ a', ((n' a' : ℝ≥0∞) ^ t.get a')⁻¹ else 0)
      · rw [← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro n'
        simp only [hcond x n', and_iff_right hQ, prod_cons_split e t x n']
        split_ifs with hP
        · rfl
        · exact (mul_zero _).symm
      · rw [zetaE_bounded_eq_tailW t x]
    · rw [ite_eq_right hQ]
      trans (∑' _ : Fin t.length → ℕ, (0 : ℝ≥0∞))
      · apply tsum_congr
        intro n'
        simp only [hcond x n']
        exact ite_eq_right (fun h => hQ h.1)
      · exact tsum_zero
  exact tsum_congr hpoint

-- N4(i): real bridge.
private lemma multipleZetaValue_eq_toReal_zetaE (l : List ℕ) :
    multipleZetaValue l = (zetaE l).toReal := by
  unfold multipleZetaValue zetaE
  have hne : ∀ n : Fin l.length → ℕ,
      (if (∀ a b : Fin l.length, a < b → n b < n a) ∧ (∀ a, 0 < n a) then
        ∏ a, ((n a : ℝ≥0∞) ^ l.get a)⁻¹ else 0) ≠ ⊤ := by
    intro n
    split_ifs with h
    · obtain ⟨-, hpos⟩ := h
      apply ENNReal.prod_ne_top
      intro a _
      apply ENNReal.inv_ne_top.mpr
      apply ENNReal.pow_ne_zero _ _
      have hpos' : 0 < n a := hpos a
      exact_mod_cast (ne_of_gt hpos')
    · exact bot_ne_top
  rw [ENNReal.tsum_toReal_eq hne]
  apply tsum_congr
  intro n
  split_ifs with h
  · rw [ENNReal.toReal_prod]
    apply Finset.prod_congr rfl
    intro a _
    rw [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  · exact ENNReal.toReal_zero

-- Bridge: the list-based real multiple-zeta value agrees with the canonical
-- strict value on every positive list (no admissibility needed for the
-- reindexing itself).
private theorem multipleZetaValue_eq_strictValue (l : List ℕ)
    (hpos : ∀ x ∈ l, 0 < x) (hAdm : (toIndex l hpos).IsAdmissibleOrEmpty) :
    multipleZetaValue l = MultipleZeta.strictValue (toIndex l hpos) hAdm := by
  unfold multipleZetaValue MultipleZeta.strictValue
  set index : MultipleZeta.Index := toIndex l hpos with hindex
  have hdepth : index.depth = l.length := rfl
  set f : (Fin l.length → ℕ) → ℝ := fun n =>
    if (∀ a b : Fin l.length, a < b → n b < n a) ∧ (∀ a, 0 < n a) then
      ∏ a, ((((n a : ℕ)) : ℝ) ^ l.get a)⁻¹
    else 0 with hf
  set g : MultipleZeta.StrictDecreasingTuple index.depth → (Fin l.length → ℕ) :=
    fun m a => (m.1 (Fin.cast hdepth.symm a) : ℕ) with hg
  have hg_inj : Function.Injective g := by
    intro m1 m2 h
    apply Subtype.ext
    funext i
    apply PNat.eq
    have hai := congrFun h (Fin.cast hdepth i)
    simp only [hg] at hai
    have hcast : Fin.cast hdepth.symm (Fin.cast hdepth i) = i :=
      Fin.leftInverse_cast hdepth i
    rw [hcast] at hai
    exact hai
  have hf_out : ∀ n ∉ Set.range g, f n = 0 := by
    intro n hn
    have hnot : ¬ ((∀ a b : Fin l.length, a < b → n b < n a)
        ∧ (∀ a, 0 < n a)) := by
      intro hP
      apply hn
      refine ⟨⟨fun i => ⟨n (Fin.cast hdepth i), hP.2 _⟩, ?_⟩, ?_⟩
      · intro a b hab
        change n (Fin.cast hdepth b) < n (Fin.cast hdepth a)
        exact hP.1 _ _ hab
      · funext a
        change n (Fin.cast hdepth (Fin.cast hdepth.symm a)) = n a
        rw [Fin.rightInverse_cast hdepth a]
    simp only [hf, ite_eq_right hnot]
  have hfg : f ∘ g = MultipleZeta.strictSummand index := by
    funext m
    simp only [Function.comp_apply]
    have hP : (∀ a b : Fin l.length, a < b → g m b < g m a)
        ∧ (∀ a, 0 < g m a) := by
      constructor
      · intro a b hab
        exact m.2 hab
      · intro a
        exact PNat.pos _
    simp only [hf, ite_eq_left hP]
    unfold MultipleZeta.strictSummand
    rw [← Finset.prod_inv_distrib]
    refine Fintype.prod_equiv (Fin.castOrderIso hdepth.symm).toEquiv _ _ (fun a => ?_)
    rfl
  have hsupp : Function.support f ⊆ Set.range g := by
    intro n hn
    rw [Function.mem_support] at hn
    by_contra hcon
    exact hn (hf_out n hcon)
  have htsum := Function.Injective.tsum_eq hg_inj hsupp
  rw [← htsum]
  apply tsum_congr
  intro m
  exact congrFun hfg m

-- On the summation range, `leftIndex` is the bundled list.
private theorem leftIndex_exists_toIndex (k : List ℕ)
    (hk_pos : ∀ n ∈ k, 1 ≤ n) (j : Fin k.length) (i : ℕ)
    (hi : i ∈ Finset.Icc 1 (k.get j - 1)) :
    ∃ hpos, leftIndex k hk_pos j i =
      toIndex ((k.get j - i + 1) :: ((k.rotate j.1).tail ++ [i])) hpos := by
  unfold leftIndex
  by_cases hmem : i ∈ Finset.Icc 1 (k.get j - 1)
  · rw [dite_eq_left hmem]
    exact ⟨_, rfl⟩
  · exact absurd hi hmem

-- `rightIndex` is the bundled list.
private theorem rightIndex_exists_toIndex (k : List ℕ)
    (hk_pos : ∀ n ∈ k, 1 ≤ n) (j : Fin k.length) :
    ∃ hpos, rightIndex k hk_pos j =
      toIndex ((k.get j + 1) :: (k.rotate j.1).tail) hpos :=
  ⟨_, rfl⟩

-- Each left-hand summand agrees with the canonical strict value.
private theorem mzV_eq_strictValue_left (k : List ℕ)
    (hk_pos : ∀ n ∈ k, 1 ≤ n) (j : Fin k.length) (i : ℕ)
    (hi : i ∈ Finset.Icc 1 (k.get j - 1)) :
    multipleZetaValue ((k.get j - i + 1) :: ((k.rotate j.1).tail ++ [i])) =
      MultipleZeta.strictValue (leftIndex k hk_pos j i)
        (leftIndex_isAdmissibleOrEmpty k hk_pos j i) := by
  obtain ⟨hpos, hunfold⟩ := leftIndex_exists_toIndex k hk_pos j i hi
  have hadmT : (toIndex ((k.get j - i + 1) :: ((k.rotate j.1).tail ++ [i]))
      hpos).IsAdmissibleOrEmpty := by
    rw [← hunfold]
    exact leftIndex_isAdmissibleOrEmpty k hk_pos j i
  have hgen : ∀ (idx : MultipleZeta.Index) (h : idx.IsAdmissibleOrEmpty),
      idx = toIndex ((k.get j - i + 1) :: ((k.rotate j.1).tail ++ [i])) hpos →
        multipleZetaValue ((k.get j - i + 1) :: ((k.rotate j.1).tail ++ [i])) =
          MultipleZeta.strictValue idx h := by
    intro idx h heq
    subst heq
    exact multipleZetaValue_eq_strictValue _ hpos h
  exact hgen _ _ hunfold

-- Each right-hand summand agrees with the canonical strict value.
private theorem mzV_eq_strictValue_right (k : List ℕ)
    (hk_pos : ∀ n ∈ k, 1 ≤ n) (j : Fin k.length) :
    multipleZetaValue ((k.get j + 1) :: (k.rotate j.1).tail) =
      MultipleZeta.strictValue (rightIndex k hk_pos j)
        (rightIndex_isAdmissibleOrEmpty k hk_pos j) := by
  obtain ⟨hpos, hunfold⟩ := rightIndex_exists_toIndex k hk_pos j
  have hadmT : (toIndex ((k.get j + 1) :: (k.rotate j.1).tail)
      hpos).IsAdmissibleOrEmpty := by
    rw [← hunfold]
    exact rightIndex_isAdmissibleOrEmpty k hk_pos j
  have hgen : ∀ (idx : MultipleZeta.Index) (h : idx.IsAdmissibleOrEmpty),
      idx = toIndex ((k.get j + 1) :: (k.rotate j.1).tail) hpos →
        multipleZetaValue ((k.get j + 1) :: (k.rotate j.1).tail) =
          MultipleZeta.strictValue idx h := by
    intro idx h heq
    subst heq
    exact multipleZetaValue_eq_strictValue _ hpos h
  exact hgen _ _ hunfold

-- N4(ii): admissible finiteness via `summable_strictSummand`.
private lemma zetaE_ne_top (e : ℕ) (t : List ℕ) (he : 2 ≤ e) (ht : ∀ x ∈ t, 1 ≤ x) :
    zetaE (e :: t) ≠ ⊤ := by
  set l : List ℕ := e :: t with hl
  have hpos : ∀ {i}, i ∈ l → 0 < i := by
    intro i hi
    rw [hl] at hi
    rcases List.mem_cons.mp hi with rfl | hi
    · omega
    · have h1 := ht _ hi
      omega
  set comp : Composition l.sum := ⟨l, hpos, rfl⟩ with hcomp
  set index : MultipleZeta.Index := ⟨l.sum, comp⟩ with hindex
  have hdepth : index.depth = l.length := rfl
  have hAdm : index.IsAdmissible := he
  have hsumm : Summable (MultipleZeta.strictSummand index) :=
    MultipleZeta.summable_strictSummand index hAdm
  set f : (Fin l.length → ℕ) → ℝ := fun n =>
    if (∀ a b : Fin l.length, a < b → n b < n a) ∧ (∀ a, 0 < n a) then
      ∏ a, ((((n a : ℕ)) : ℝ) ^ l.get a)⁻¹
    else 0 with hf
  set g : MultipleZeta.StrictDecreasingTuple index.depth → (Fin l.length → ℕ) :=
    fun m a => (m.1 (Fin.cast hdepth.symm a) : ℕ) with hg
  have hg_inj : Function.Injective g := by
    intro m1 m2 h
    apply Subtype.ext
    funext i
    apply PNat.eq
    have hai := congrFun h (Fin.cast hdepth i)
    simp only [hg] at hai
    have hcast : Fin.cast hdepth.symm (Fin.cast hdepth i) = i :=
      Fin.leftInverse_cast hdepth i
    rw [hcast] at hai
    exact hai
  have hf_out : ∀ n ∉ Set.range g, f n = 0 := by
    intro n hn
    have hnot : ¬ ((∀ a b : Fin l.length, a < b → n b < n a) ∧ (∀ a, 0 < n a)) := by
      intro hP
      apply hn
      refine ⟨⟨fun i => ⟨n (Fin.cast hdepth i), hP.2 _⟩, ?_⟩, ?_⟩
      · intro a b hab
        change n (Fin.cast hdepth b) < n (Fin.cast hdepth a)
        exact hP.1 _ _ hab
      · funext a
        change n (Fin.cast hdepth (Fin.cast hdepth.symm a)) = n a
        rw [Fin.rightInverse_cast hdepth a]
    simp only [hf, ite_eq_right hnot]
  have hfg : f ∘ g = MultipleZeta.strictSummand index := by
    funext m
    simp only [Function.comp_apply]
    have hP : (∀ a b : Fin l.length, a < b → g m b < g m a) ∧ (∀ a, 0 < g m a) := by
      constructor
      · intro a b hab
        exact m.2 hab
      · intro a
        exact PNat.pos _
    simp only [hf, ite_eq_left hP]
    unfold MultipleZeta.strictSummand
    rw [← Finset.prod_inv_distrib]
    refine Fintype.prod_equiv (Fin.castOrderIso hdepth.symm).toEquiv _ _ (fun a => ?_)
    rfl
  have hcomp : Summable (f ∘ g) := by
    rw [hfg]
    exact hsumm
  have hsum_f : Summable f := (Function.Injective.summable_iff hg_inj hf_out).mp hcomp
  have hnn : ∀ n, 0 ≤ f n := by
    intro n
    simp only [hf]
    split_ifs with h
    · apply Finset.prod_nonneg
      intro a _
      apply inv_nonneg.mpr
      apply pow_nonneg (Nat.cast_nonneg _)
    · exact le_rfl
  have hzeta_eq : zetaE l = ∑' n, ENNReal.ofReal (f n) := by
    unfold zetaE
    apply tsum_congr
    intro n
    simp only [hf]
    split_ifs with h
    · rw [ENNReal.ofReal_prod_of_nonneg
        (fun a _ => inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _))]
      apply Finset.prod_congr rfl
      intro a _
      have hpos_a : (0 : ℝ) < (((n a : ℕ)) : ℝ) := by exact_mod_cast h.2 a
      rw [ENNReal.ofReal_inv_of_pos (pow_pos hpos_a _)]
      rw [ENNReal.ofReal_pow (le_of_lt hpos_a)]
      rw [ENNReal.ofReal_natCast]
    · exact ENNReal.ofReal_zero.symm
  rw [hzeta_eq, ← ENNReal.ofReal_tsum_of_nonneg hnn hsum_f]
  exact ENNReal.ofReal_ne_top

private lemma zetaR_ne_top (e : ℕ) (t : List ℕ) (he : 2 ≤ e) (ht : ∀ x ∈ t, 1 ≤ x) :
    zetaR (e :: t) ≠ ⊤ := by
  rw [← zetaE_cons_eq_zetaR]
  exact zetaE_ne_top e t he ht

-- N6: telescoping series.
-- pure-real telescoping in the bottom variable
private lemma tele_inv_sub (y : ℝ) (c : ℕ) :
    ∑ d ∈ Finset.range c, (((y - d : ℝ))⁻¹ - ((y + 1 - d : ℝ))⁻¹)
      = ((y + 1 - c : ℝ))⁻¹ - ((y + 1 : ℝ))⁻¹ := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Finset.sum_range_succ, ih]
    have harg : (y : ℝ) - (c : ℝ) = y + 1 - ((c : ℝ) + 1) := by ring
    have hcc : ((((c + 1 : ℕ))) : ℝ) = (c : ℝ) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
    rw [hcc, harg]
    ring

-- closed form for the partial sums
private lemma N6_partial (c A : ℕ) (hc : 1 ≤ c) (hca : c ≤ A) (N : ℕ) :
    ∑ m ∈ Finset.range N, ((A + 1 + m : ℝ))⁻¹ * ((((A + 1 + m - c : ℕ)) : ℝ))⁻¹
      = (c : ℝ)⁻¹ * ((∑ d ∈ Finset.range c, ((((A - d : ℕ)) : ℝ))⁻¹)
        - ∑ d ∈ Finset.range c, ((((A + N - d : ℕ)) : ℝ))⁻¹) := by
  have hcast : ∀ u v : ℕ, v ≤ u → ((((u - v : ℕ)) : ℝ)) = (u : ℝ) - (v : ℝ) := by
    intro u v h
    rw [Nat.cast_sub h]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have htele : (∑ d ∈ Finset.range c, ((((A + N - d : ℕ)) : ℝ))⁻¹)
          - ∑ d ∈ Finset.range c, ((((A + N + 1 - d : ℕ)) : ℝ))⁻¹
        = ((((A + N + 1 - c : ℕ)) : ℝ))⁻¹ - ((((A + N + 1 : ℕ)) : ℝ))⁻¹ := by
      have e : ∀ d ∈ Finset.range c,
            ((((A + N - d : ℕ)) : ℝ))⁻¹ - ((((A + N + 1 - d : ℕ)) : ℝ))⁻¹
            = (((A:ℝ) + N - d))⁻¹ - (((A:ℝ) + N + 1 - d))⁻¹ := by
        intro d hd
        have hdc : d < c := Finset.mem_range.mp hd
        have h1 : d ≤ A + N := by omega
        have h2 : d ≤ A + N + 1 := by omega
        have hAN : ((((A + N : ℕ))) : ℝ) = (A : ℝ) + (N : ℝ) := by
          rw [Nat.cast_add]
        have hAN1 : ((((A + N + 1 : ℕ))) : ℝ) = (A : ℝ) + (N : ℝ) + 1 := by
          rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]
        rw [hcast _ _ h1, hcast _ _ h2, hAN, hAN1]
      rw [← Finset.sum_sub_distrib]
      trans ∑ d ∈ Finset.range c, ((((A:ℝ) + N - d))⁻¹ - (((A:ℝ) + N + 1 - d))⁻¹)
      · exact Finset.sum_congr rfl (fun d hd => e d hd)
      · have eT1 : ((((A + N + 1 - c : ℕ)) : ℝ)) = (A:ℝ) + N + 1 - (c : ℝ) := by
          have hle : c ≤ A + N + 1 := by omega
          have hAN1 : ((((A + N + 1 : ℕ))) : ℝ) = (A : ℝ) + (N : ℝ) + 1 := by
            rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]
          rw [hcast _ _ hle, hAN1]
        have eT2 : ((((A + N + 1 : ℕ)) : ℝ)) = (A:ℝ) + N + 1 := by
          rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]
        rw [eT1, eT2]
        exact tele_inv_sub _ _
    have hterm : ((A + 1 + N : ℝ))⁻¹ * ((((A + 1 + N - c : ℕ)) : ℝ))⁻¹
        = (c : ℝ)⁻¹ * ((((A + N + 1 - c : ℕ)) : ℝ))⁻¹
          - (c : ℝ)⁻¹ * ((((A + N + 1 : ℕ)) : ℝ))⁻¹ := by
      have hle : c ≤ A + 1 + N := by omega
      have hle2 : c ≤ A + N + 1 := by omega
      have hAN1 : ((((A + 1 + N : ℕ))) : ℝ) = (A : ℝ) + 1 + (N : ℝ) := by
        rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]
      have hAN1' : ((((A + N + 1 : ℕ))) : ℝ) = (A : ℝ) + (N : ℝ) + 1 := by
        rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]
      have hnorm : (A : ℝ) + (N : ℝ) + 1 = (A : ℝ) + 1 + (N : ℝ) := by ring
      have hc0 : (c : ℝ) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
      have hx0 : (A : ℝ) + 1 + (N : ℝ) ≠ 0 := by positivity
      have hxc0 : (A : ℝ) + 1 + (N : ℝ) - (c : ℝ) ≠ 0 := by
        have hcA : (c : ℝ) ≤ (A : ℝ) := by exact_mod_cast hca
        have hN : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
        have hpos : (0:ℝ) < (A:ℝ) + 1 + (N:ℝ) - (c:ℝ) := by linarith
        exact ne_of_gt hpos
      rw [hcast _ _ hle, hAN1, hcast _ _ hle2, hAN1', hnorm]
      field_simp
      ring
    rw [hterm]
    linear_combination (c : ℝ)⁻¹ * htele.symm

open Topology

-- reindex x = A + 1 + m
private lemma N6_reindex (c A : ℕ) :
    (∑' x : ℕ, (if A < x then ((x : ℝ))⁻¹ * ((((x - c : ℕ)) : ℝ))⁻¹ else 0))
      = ∑' m : ℕ, ((A + 1 + m : ℝ))⁻¹ * ((((A + 1 + m - c : ℕ)) : ℝ))⁻¹ := by
  have hinj : Function.Injective (fun m : ℕ => A + 1 + m) := by
    intro a b h
    simp only [] at h
    omega
  have hsupp : Function.support
        (fun x : ℕ => (if A < x then ((x : ℝ))⁻¹ * ((((x - c : ℕ)) : ℝ))⁻¹ else 0))
        ⊆ Set.range (fun m : ℕ => A + 1 + m) := by
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx
    have hAx : A < x := by
      by_contra hcon
      apply hx
      exact ite_eq_right hcon
    refine ⟨x - (A + 1), ?_⟩
    change A + 1 + (x - (A + 1)) = x
    omega
  have h := Function.Injective.tsum_eq hinj hsupp
  rw [← h]
  apply tsum_congr
  intro m
  rw [ite_eq_left (by omega : A < A + 1 + m)]
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]

-- the remainder tends to 0
private lemma N6_tendsto (c A : ℕ) (hca : c ≤ A) :
    Filter.Tendsto (fun N : ℕ => ∑ d ∈ Finset.range c, ((((A + N - d : ℕ)) : ℝ))⁻¹)
      Filter.atTop (nhds 0) := by
  have hcast : ∀ u v : ℕ, v ≤ u → ((((u - v : ℕ)) : ℝ)) = (u : ℝ) - (v : ℝ) := by
    intro u v h
    rw [Nat.cast_sub h]
  have hshift : Filter.Tendsto (fun N : ℕ => N + 1) Filter.atTop Filter.atTop :=
    StrictMono.tendsto_atTop (fun _ b h => Nat.succ_lt_succ h)
  have hglim : Filter.Tendsto (fun N : ℕ => (c : ℝ) / ((N : ℝ) + 1)) Filter.atTop (nhds 0) := by
    have hcomp := (tendsto_const_div_atTop_nhds_zero_nat (c : ℝ)).comp hshift
    apply Filter.Tendsto.congr _ hcomp
    intro N
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  have hbound : ∀ N : ℕ,
      (∑ d ∈ Finset.range c, ((((A + N - d : ℕ)) : ℝ))⁻¹) ≤ (c : ℝ) / ((N : ℝ) + 1) := by
    intro N
    have hNN : ∀ d ∈ Finset.range c,
        ((((A + N - d : ℕ)) : ℝ))⁻¹ ≤ (1 : ℝ) / ((N : ℝ) + 1) := by
      intro d hd
      have hdc : d < c := Finset.mem_range.mp hd
      have hle : d ≤ A + N := by omega
      have hdA1 : (d : ℝ) + 1 ≤ (A : ℝ) := by exact_mod_cast (by omega : d + 1 ≤ A)
      have hAN : ((((A + N : ℕ))) : ℝ) = (A : ℝ) + (N : ℝ) := by
        rw [Nat.cast_add]
      have hle2 : (N : ℝ) + 1 ≤ (A : ℝ) + (N : ℝ) - (d : ℝ) := by
        have hNp : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
        linarith
      have hNp1 : (0:ℝ) < (N : ℝ) + 1 := by
        have hNp : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
        linarith
      rw [hcast _ _ hle, hAN, inv_eq_one_div]
      exact one_div_le_one_div_of_le hNp1 hle2
    calc ∑ d ∈ Finset.range c, ((((A + N - d : ℕ)) : ℝ))⁻¹
        ≤ ∑ _d ∈ Finset.range c, (1 : ℝ) / ((N : ℝ) + 1) := Finset.sum_le_sum hNN
      _ = (c : ℝ) / ((N : ℝ) + 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hnn : ∀ N : ℕ,
      0 ≤ ∑ d ∈ Finset.range c, ((((A + N - d : ℕ)) : ℝ))⁻¹ := by
    intro N
    exact Finset.sum_nonneg (fun d _ => by positivity)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hglim hnn hbound

-- HasSum for the reindexed series
private lemma N6_hasSum (c A : ℕ) (hc : 1 ≤ c) (hca : c ≤ A) :
    HasSum (fun m : ℕ => ((A + 1 + m : ℝ))⁻¹ * ((((A + 1 + m - c : ℕ)) : ℝ))⁻¹)
      ((c : ℝ)⁻¹ * ∑ d ∈ Finset.range c, ((((A - d : ℕ)) : ℝ))⁻¹) := by
  have hnonneg : ∀ m : ℕ,
      0 ≤ ((A + 1 + m : ℝ))⁻¹ * ((((A + 1 + m - c : ℕ)) : ℝ))⁻¹ := by
    intro m
    positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg hnonneg]
  have hpart := N6_partial c A hc hca
  have hfun : (fun N : ℕ => ∑ m ∈ Finset.range N,
        ((A + 1 + m : ℝ))⁻¹ * ((((A + 1 + m - c : ℕ)) : ℝ))⁻¹)
      = (fun N : ℕ => (c : ℝ)⁻¹ * ((∑ d ∈ Finset.range c, ((((A - d : ℕ)) : ℝ))⁻¹)
        - ∑ d ∈ Finset.range c, ((((A + N - d : ℕ)) : ℝ))⁻¹)) :=
    funext hpart
  rw [hfun]
  have hR := N6_tendsto c A hca
  have hlim : Filter.Tendsto
      (fun N : ℕ => (c : ℝ)⁻¹ * ((∑ d ∈ Finset.range c, ((((A - d : ℕ)) : ℝ))⁻¹)
        - ∑ d ∈ Finset.range c, ((((A + N - d : ℕ)) : ℝ))⁻¹))
      Filter.atTop
      (nhds ((c : ℝ)⁻¹ * ((∑ d ∈ Finset.range c, ((((A - d : ℕ)) : ℝ))⁻¹) - 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub hR)
  simpa using hlim

private lemma N6_real_tsum (c A : ℕ) (hc : 1 ≤ c) (hca : c ≤ A) :
    (∑' m : ℕ, ((A + 1 + m : ℝ))⁻¹ * ((((A + 1 + m - c : ℕ)) : ℝ))⁻¹)
      = (c : ℝ)⁻¹ * ∑ d ∈ Finset.range c, ((((A - d : ℕ)) : ℝ))⁻¹ :=
  HasSum.tsum_eq (N6_hasSum c A hc hca)

-- N6: transfer to ℝ≥0∞
private lemma tsum_inv_mul_inv_sub_eq (c A : ℕ) (hc : 1 ≤ c) (hca : c ≤ A) :
    (∑' x : ℕ, (if A < x then (x : ℝ≥0∞)⁻¹ * (((x - c : ℕ) : ℝ≥0∞))⁻¹ else 0))
      = (c : ℝ≥0∞)⁻¹ * harmTail A c := by
  have hne : ∀ x : ℕ,
      (if A < x then (x : ℝ≥0∞)⁻¹ * (((x - c : ℕ) : ℝ≥0∞))⁻¹ else 0) ≠ ⊤ := by
    intro x
    split_ifs with hx
    · apply ENNReal.mul_ne_top
      · rw [ENNReal.inv_ne_top]
        have : x ≠ 0 := by omega
        exact_mod_cast this
      · rw [ENNReal.inv_ne_top]
        have : x - c ≠ 0 := by omega
        exact_mod_cast this
    · exact bot_ne_top
  have hmain : (∑' x : ℕ,
        (if A < x then (x : ℝ≥0∞)⁻¹ * (((x - c : ℕ) : ℝ≥0∞))⁻¹ else 0)).toReal
      = (c : ℝ)⁻¹ * ∑ d ∈ Finset.range c, ((((A - d : ℕ)) : ℝ))⁻¹ := by
    rw [ENNReal.tsum_toReal_eq hne]
    have hterm : ∀ x : ℕ,
        ((if A < x then (x : ℝ≥0∞)⁻¹ * (((x - c : ℕ) : ℝ≥0∞))⁻¹ else 0)).toReal
        = (if A < x then ((x : ℝ))⁻¹ * ((((x - c : ℕ)) : ℝ))⁻¹ else 0) := by
      intro x
      split_ifs with hx
      · rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_inv,
          ENNReal.toReal_natCast, ENNReal.toReal_natCast]
      · exact ENNReal.toReal_zero
    rw [tsum_congr hterm, N6_reindex c A, N6_real_tsum c A hc hca]
  have hval0 : (c : ℝ)⁻¹ * ∑ d ∈ Finset.range c, ((((A - d : ℕ)) : ℝ))⁻¹ ≠ 0 := by
    apply mul_ne_zero
    · have hcR : (0:ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
      exact inv_ne_zero (ne_of_gt hcR)
    · apply ne_of_gt
      apply Finset.sum_pos
      · intro d hd
        have hdc : d < c := Finset.mem_range.mp hd
        have hpos : (0:ℝ) < ((((A - d : ℕ)) : ℝ)) := by
          have h1 : 0 < A - d := by omega
          exact_mod_cast h1
        exact inv_pos.mpr hpos
      · exact Finset.nonempty_range_iff.mpr (by omega : c ≠ 0)
  have hfin : (∑' x : ℕ,
      (if A < x then (x : ℝ≥0∞)⁻¹ * (((x - c : ℕ) : ℝ≥0∞))⁻¹ else 0)) ≠ ⊤ := by
    intro hcon
    apply hval0
    have h0 : (∑' x : ℕ,
      (if A < x then (x : ℝ≥0∞)⁻¹ * (((x - c : ℕ) : ℝ≥0∞))⁻¹ else 0)).toReal = 0 := by
      rw [hcon]
      exact ENNReal.toReal_top
    rw [hmain] at h0
    exact h0
  have hof := congrArg ENNReal.ofReal hmain
  rw [ENNReal.ofReal_toReal hfin] at hof
  have hfin_eq : ∀ d ∈ Finset.range c,
      ENNReal.ofReal ((((A - d : ℕ)) : ℝ))⁻¹ = ((((A - d : ℕ)) : ℝ≥0∞))⁻¹ := by
    intro d hd
    have hdc : d < c := Finset.mem_range.mp hd
    have hpos : (0:ℝ) < ((((A - d : ℕ)) : ℝ)) := by
      have h1 : 0 < A - d := by omega
      exact_mod_cast h1
    rw [ENNReal.ofReal_inv_of_pos hpos, ENNReal.ofReal_natCast]
  have hcR : (0:ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
  rw [hof]
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg c))]
  rw [ENNReal.ofReal_inv_of_pos hcR]
  rw [ENNReal.ofReal_natCast]
  unfold harmTail
  have hnn2 : ∀ d ∈ Finset.range c, (0:ℝ) ≤ ((((A - d : ℕ)) : ℝ))⁻¹ := by
    intro d hd
    positivity
  rw [ENNReal.ofReal_sum_of_nonneg hnn2]
  congr 1
  exact Finset.sum_congr rfl (fun d hd => hfin_eq d hd)

-- N7: split identity, steps A+B.
private lemma cycT_add_sum_zetaR_eq (L : ℕ) (hL : 1 ≤ L) (rest : List ℕ) :
    cycT (L :: rest)
        + ∑ i ∈ Finset.Icc 1 (L - 1), zetaR ((L - i + 1) :: (rest ++ [i]))
      = zetaR ((L + 1) :: rest) + topSum 0 rest (wWeight L) := by
  have htailW : ∀ x : ℕ, 0 < x →
      ((x : ℝ≥0∞) ^ L)⁻¹ * tailW rest (harmTail x) x
        + ∑ i ∈ Finset.Icc 1 (L - 1),
          ((x : ℝ≥0∞) ^ (L - i + 1))⁻¹ * tailW (rest ++ [i]) (fun _ => 1) x
      = ((x : ℝ≥0∞) ^ (L + 1))⁻¹ * tailW rest (fun _ => 1) x
        + tailW rest (wWeight L x) x := by
    intro x hx
    simp only [tailW_append]
    simp only [← tailW_const_mul]
    simp only [← tailW_sum]
    simp only [← tailW_add]
    refine tailW_congr _ _ _ _ hx (fun y hy0 hyx => ?_)
    simp only [mul_one]
    have hsplit : harmTail x y
        = ((x : ℝ≥0∞))⁻¹
          + ∑ c ∈ Finset.Ioo 0 y, ((((x - c : ℕ)) : ℝ≥0∞))⁻¹ := by
      unfold harmTail
      have hsplit' : Finset.range y = insert 0 (Finset.Ioo 0 y) := by
        ext c
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
        omega
      rw [hsplit', Finset.sum_insert (by simp), Nat.sub_zero]
    have hx0 : (x : ℝ≥0∞) ≠ 0 := by
      have hx0' : x ≠ 0 := by omega
      exact_mod_cast hx0'
    have hxT : (x : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top x
    have hhead : ((x : ℝ≥0∞) ^ L)⁻¹ * (x : ℝ≥0∞)⁻¹
        = ((x : ℝ≥0∞) ^ (L + 1))⁻¹ := by
      have ha : ((x : ℝ≥0∞) ^ L) ≠ 0 ∨ (x : ℝ≥0∞) ≠ ⊤ := Or.inr hxT
      have hb : ((x : ℝ≥0∞) ^ L) ≠ ⊤ ∨ (x : ℝ≥0∞) ≠ 0 := Or.inr hx0
      rw [← ENNReal.mul_inv ha hb, ← pow_succ]
    have hswap : (∑ i ∈ Finset.Icc 1 (L - 1),
          ((x : ℝ≥0∞) ^ (L - i + 1))⁻¹
            * ∑ c ∈ Finset.Ioo 0 y, ((c : ℝ≥0∞) ^ i)⁻¹)
        = ∑ c ∈ Finset.Ioo 0 y, ∑ i ∈ Finset.Icc 1 (L - 1),
          ((x : ℝ≥0∞) ^ (L - i + 1))⁻¹ * ((c : ℝ≥0∞) ^ i)⁻¹ := by
      simp only [Finset.mul_sum]
      exact Finset.sum_comm
    rw [hsplit, mul_add, Finset.mul_sum, hhead, hswap, add_assoc]
    congr 1
    rw [← Finset.sum_add_distrib]
    unfold wWeight
    apply Finset.sum_congr rfl
    intro c hc
    have hc1 : 1 ≤ c := (Finset.mem_Ioo.mp hc).1
    have hcy : c < y := (Finset.mem_Ioo.mp hc).2
    have hcx : c < x := lt_of_lt_of_le hcy hyx
    exact partial_fraction_cyclic x c L hc1 hcx hL
  unfold cycT zetaR topSum
  simp only [pow_zero, inv_one, one_mul]
  rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
  apply tsum_congr
  intro x
  split_ifs with hx
  · exact htailW x hx
  · simp

-- Power identity for reassembling the rotated exponent.
private lemma cpow_succ_inv (L c : ℕ) (hL : 1 ≤ L) (hc : 1 ≤ c) :
    ((c : ℝ≥0∞) ^ (L - 1))⁻¹ * (c : ℝ≥0∞)⁻¹ = ((c : ℝ≥0∞) ^ L)⁻¹ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hL
  rw [Nat.add_sub_cancel]
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by
    have hc0' : c ≠ 0 := by omega
    exact_mod_cast hc0'
  have hcT : (c : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top c
  have ha : ((c : ℝ≥0∞) ^ k) ≠ 0 ∨ (c : ℝ≥0∞) ≠ ⊤ := Or.inr hcT
  have hb : ((c : ℝ≥0∞) ^ k) ≠ ⊤ ∨ (c : ℝ≥0∞) ≠ 0 := Or.inr hc0
  rw [pow_succ, ENNReal.mul_inv ha hb]

-- `tailW` of the zero weight is zero.
private lemma tailW_zero (t : List ℕ) (A : ℕ) : tailW t (fun _ => 0) A = 0 := by
  induction t generalizing A with
  | nil => rfl
  | cons e t' ih =>
    unfold tailW
    simp only [ih, mul_zero, Finset.sum_const_zero]

-- Single-`c` inner tsum: telescoping evaluation plus exponent reassembly.
private lemma inner_single (L c y : ℕ) (hL : 1 ≤ L) (hc : 1 ≤ c) (hcy : c ≤ y) :
    (∑' x : ℕ, (if y < x then (x : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) ^ (L - 1))⁻¹
      * ((((x - c : ℕ))) : ℝ≥0∞)⁻¹ else 0))
    = ((c : ℝ≥0∞) ^ L)⁻¹ * harmTail y c := by
  have hfactor : ∀ x : ℕ,
      (if y < x then (x : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) ^ (L - 1))⁻¹
        * ((((x - c : ℕ))) : ℝ≥0∞)⁻¹ else 0)
      = ((c : ℝ≥0∞) ^ (L - 1))⁻¹
        * (if y < x then (x : ℝ≥0∞)⁻¹ * ((((x - c : ℕ))) : ℝ≥0∞)⁻¹ else 0) := by
    intro x
    split_ifs with h
    · ring
    · exact (mul_zero _).symm
  simp only [hfactor]
  rw [ENNReal.tsum_mul_left, tsum_inv_mul_inv_sub_eq c y hc hcy, ← mul_assoc,
    cpow_succ_inv L c hL hc]

-- Summed inner tsum over the bottom variable.
private lemma inner_tsum_wWeight (L : ℕ) (hL : 1 ≤ L) (y z : ℕ) (hzy : z ≤ y) :
    (∑' x : ℕ, (if y < x then wWeight L x z else 0))
    = ∑ c ∈ Finset.Ioo 0 z, ((c : ℝ≥0∞) ^ L)⁻¹ * harmTail y c := by
  have hpush : ∀ x : ℕ, (if y < x then wWeight L x z else 0)
      = ∑ c ∈ Finset.Ioo 0 z,
        (if y < x then (x : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) ^ (L - 1))⁻¹
          * ((((x - c : ℕ))) : ℝ≥0∞)⁻¹ else 0) := by
    intro x
    unfold wWeight
    split_ifs with h
    · rfl
    · exact Finset.sum_const_zero.symm
  simp only [hpush]
  rw [Summable.tsum_finsetSum (fun c _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro c hc
  have hc1 : 1 ≤ c := (Finset.mem_Ioo.mp hc).1
  have hcz : c < z := (Finset.mem_Ioo.mp hc).2
  have hcy : c ≤ y := le_trans (le_of_lt hcz) hzy
  exact inner_single L c y hL hc1 hcy

-- N8: remainder = rotated T, step C.
private lemma topSum_wWeight_eq_cycT (L : ℕ) (hL : 1 ≤ L) (rest : List ℕ) :
    topSum 0 rest (wWeight L) = cycT (rest ++ [L]) := by
  cases rest with
  | nil =>
    simp only [List.nil_append]
    unfold cycT topSum
    simp only [pow_zero, inv_one, one_mul]
    have hnil : ∀ (w : ℕ → ℝ≥0∞) (A : ℕ), tailW [] w A = w A := fun w A => rfl
    simp only [hnil]
    unfold wWeight
    rw [tsum_Ioo_swap]
    apply tsum_congr
    intro c
    split_ifs with hc0
    · exact inner_single L c c hL hc0 le_rfl
    · rfl
  | cons e r =>
    have htail : ∀ x : ℕ, tailW (e :: r) (wWeight L x) x
        = ∑ y ∈ Finset.Ioo 0 x,
          ((y : ℝ≥0∞) ^ e)⁻¹ * tailW r (wWeight L x) y :=
      fun x => rfl
    unfold topSum
    simp only [pow_zero, inv_one, one_mul, htail]
    rw [tsum_Ioo_swap]
    simp only [List.cons_append]
    unfold cycT topSum
    simp only [tailW_append]
    apply tsum_congr
    intro y
    split_ifs with hy0
    · have hf : ∀ x : ℕ,
          (if y < x then ((y : ℝ≥0∞) ^ e)⁻¹ * tailW r (wWeight L x) y else 0)
          = ((y : ℝ≥0∞) ^ e)⁻¹
            * (if y < x then tailW r (wWeight L x) y else 0) := by
        intro x
        split_ifs with h
        · rfl
        · exact (mul_zero _).symm
      have hmove : ∀ x : ℕ, (if y < x then tailW r (wWeight L x) y else 0)
          = tailW r (fun z => if y < x then wWeight L x z else 0) y := by
        intro x
        split_ifs with h
        · rfl
        · rw [tailW_zero]
      simp only [hf, hmove]
      rw [ENNReal.tsum_mul_left, tailW_tsum]
      congr 1
      refine tailW_congr _ _ _ _ hy0 (fun z _ hzy => ?_)
      exact inner_tsum_wWeight L hL y z hzy
    · rfl

-- N9: rotation step (*) (two lines from N7 + N8; proof deferred with the rest).
private lemma cycT_rotation_step (L : ℕ) (hL : 1 ≤ L) (rest : List ℕ) :
    cycT (L :: rest)
        + ∑ i ∈ Finset.Icc 1 (L - 1), zetaR ((L - i + 1) :: (rest ++ [i]))
      = zetaR ((L + 1) :: rest) + cycT (rest ++ [L]) := by
  have h := cycT_add_sum_zetaR_eq L hL rest
  rw [topSum_wWeight_eq_cycT L hL rest] at h
  exact h

-- Pointwise bound for `harmTail` by a constant plus an inverse sum.
private lemma harmTail_le_one_add (x y : ℕ) (hy0 : 0 < y) (hyx : y ≤ x) :
    harmTail x y ≤ 1 + ∑ d ∈ Finset.Ioo 0 y, ((d : ℝ≥0∞) ^ 1)⁻¹ * 1 := by
  simp only [pow_one, mul_one]
  have hterm : ∀ c ∈ Finset.range y,
      ((((x - c : ℕ)) : ℝ≥0∞))⁻¹ ≤ ((((y - c : ℕ)) : ℝ≥0∞))⁻¹ := by
    intro c hc
    apply ENNReal.inv_le_inv.mpr
    exact_mod_cast Nat.sub_le_sub_right hyx c
  have hsum1 : harmTail x y
      ≤ ∑ c ∈ Finset.range y, ((((y - c : ℕ)) : ℝ≥0∞))⁻¹ := by
    unfold harmTail
    exact Finset.sum_le_sum hterm
  have hreflect : (∑ c ∈ Finset.range y, ((((y - c : ℕ)) : ℝ≥0∞))⁻¹)
      = ∑ c ∈ Finset.range y, ((((c + 1 : ℕ)) : ℝ≥0∞))⁻¹ := by
    have h1 : ∀ c ∈ Finset.range y,
        ((((y - c : ℕ)) : ℝ≥0∞))⁻¹
          = ((((y - 1 - c + 1 : ℕ)) : ℝ≥0∞))⁻¹ := by
      intro c hc
      have hcy : c < y := Finset.mem_range.mp hc
      have heq : y - c = y - 1 - c + 1 := by omega
      rw [heq]
    trans ∑ c ∈ Finset.range y, ((((y - 1 - c + 1 : ℕ)) : ℝ≥0∞))⁻¹
    · exact Finset.sum_congr rfl h1
    · exact Finset.sum_range_reflect (fun k => ((((k + 1 : ℕ)) : ℝ≥0∞))⁻¹) y
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ y by omega)
  have hstep3 : (∑ c ∈ Finset.range (m + 1), ((((c + 1 : ℕ)) : ℝ≥0∞))⁻¹)
      ≤ 1 + ∑ d ∈ Finset.Ioo 0 (m + 1), ((d : ℝ≥0∞))⁻¹ := by
    rw [Finset.sum_range_succ]
    have hIoo : (∑ d ∈ Finset.Ioo 0 (m + 1), ((d : ℝ≥0∞))⁻¹)
        = ∑ c ∈ Finset.range m, ((((c + 1 : ℕ)) : ℝ≥0∞))⁻¹ := by
      have hIoo_eq : Finset.Ioo 0 (m + 1) = Finset.Ico 1 (m + 1) := by
        ext d
        simp only [Finset.mem_Ioo, Finset.mem_Ico]
        omega
      rw [hIoo_eq, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
      apply Finset.sum_congr rfl
      intro c _
      have hac : (1 : ℕ) + c = c + 1 := add_comm 1 c
      rw [hac]
    rw [hIoo]
    have hle : ((((m + 1 : ℕ)) : ℝ≥0∞))⁻¹ ≤ 1 := by
      have h1y : (1 : ℝ≥0∞) ≤ ((m + 1 : ℕ) : ℝ≥0∞) := by
        exact_mod_cast (by omega : (1 : ℕ) ≤ m + 1)
      have h2 := ENNReal.inv_le_inv.mpr h1y
      rwa [inv_one] at h2
    calc (∑ c ∈ Finset.range m, ((((c + 1 : ℕ)) : ℝ≥0∞))⁻¹)
            + ((((m + 1 : ℕ)) : ℝ≥0∞))⁻¹
        ≤ (∑ c ∈ Finset.range m, ((((c + 1 : ℕ)) : ℝ≥0∞))⁻¹) + 1 :=
          add_le_add_right hle _
      _ = 1 + (∑ c ∈ Finset.range m, ((((c + 1 : ℕ)) : ℝ≥0∞))⁻¹) :=
          add_comm _ _
  calc harmTail x (m + 1)
      ≤ ∑ c ∈ Finset.range (m + 1), ((((m + 1 - c : ℕ)) : ℝ≥0∞))⁻¹ := hsum1
    _ = ∑ c ∈ Finset.range (m + 1), ((((c + 1 : ℕ)) : ℝ≥0∞))⁻¹ := hreflect
    _ ≤ 1 + ∑ d ∈ Finset.Ioo 0 (m + 1), ((d : ℝ≥0∞))⁻¹ := hstep3

-- N10: T bound for the finiteness base case.
private lemma cycT_cons_le (L : ℕ) (t : List ℕ) :
    cycT (L :: t) ≤ zetaR (L :: t) + zetaR (L :: (t ++ [1])) := by
  unfold cycT zetaR topSum
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro x
  split_ifs with hx
  · rw [← mul_add]
    have htail : tailW t (harmTail x) x
        ≤ tailW t (fun _ => 1) x + tailW (t ++ [1]) (fun _ => 1) x := by
      rw [tailW_append, ← tailW_add]
      refine tailW_mono _ _ _ _ hx ?_
      intro y hy0 hyx
      exact harmTail_le_one_add x y hy0 hyx
    exact mul_le_mul_right htail _
  · simp

-- Split off leading 1's: a positive list with some entry ≠ 1 is
-- `replicate p 1 ++ L :: s` with `2 ≤ L`.
private lemma decomp_leading_ones (l : List ℕ) :
    (∀ x ∈ l, 1 ≤ x) → (∃ x ∈ l, x ≠ 1) →
    ∃ p L s, l = List.replicate p 1 ++ L :: s ∧ 2 ≤ L ∧ (∀ x ∈ s, 1 ≤ x) := by
  induction l with
  | nil =>
    intro hpos hne
    obtain ⟨x, hx, _⟩ := hne
    simp at hx
  | cons h t ih =>
    intro hpos hne
    by_cases hh : h = 1
    · subst hh
      have hpos_t : ∀ x ∈ t, 1 ≤ x :=
        fun x hx => hpos x (List.mem_cons_of_mem _ hx)
      obtain ⟨x, hx, hx1⟩ := hne
      rw [List.mem_cons] at hx
      have hne_t : ∃ x ∈ t, x ≠ 1 := by
        rcases hx with rfl | hx
        · exact absurd rfl hx1
        · exact ⟨x, hx, hx1⟩
      obtain ⟨p, L, s, hl, hL, hs⟩ := ih hpos_t hne_t
      refine ⟨p + 1, L, s, ?_, hL, hs⟩
      rw [hl, List.replicate_succ, List.cons_append]
    · have h2 : 2 ≤ h := by
        have h1 := hpos h List.mem_cons_self
        omega
      exact ⟨0, h, t, rfl, h2,
        fun x hx => hpos x (List.mem_cons_of_mem _ hx)⟩

-- N11: T finite on every rotation.
private lemma cycT_ne_top (l : List ℕ) (hpos : ∀ x ∈ l, 1 ≤ x)
    (hne1 : ∃ x ∈ l, x ≠ 1) : cycT l ≠ ⊤ := by
  obtain ⟨p, L, s, hl, hL, hs⟩ := decomp_leading_ones l hpos hne1
  subst hl
  clear hpos hne1
  induction p generalizing s with
  | zero =>
    simp only [List.replicate_zero, List.nil_append]
    have h1 : zetaR (L :: s) ≠ ⊤ := zetaR_ne_top L s hL hs
    have hs1 : ∀ x ∈ s ++ [1], 1 ≤ x := by
      intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact hs x hx
      · rw [List.mem_singleton] at hx
        subst hx
        exact le_rfl
    have h2 : zetaR (L :: (s ++ [1])) ≠ ⊤ := zetaR_ne_top L (s ++ [1]) hL hs1
    have hne_add : zetaR (L :: s) + zetaR (L :: (s ++ [1])) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨h1, h2⟩
    exact ne_top_of_le_ne_top hne_add (cycT_cons_le L s)
  | succ p ih =>
    have hrep : List.replicate (p + 1) 1 ++ L :: s
        = 1 :: (List.replicate p 1 ++ L :: s) := by
      rw [List.replicate_succ, List.cons_append]
    rw [hrep]
    set R : List ℕ := List.replicate p 1 ++ L :: s with hR
    have hstep := cycT_rotation_step 1 (by omega : 1 ≤ 1) R
    have hIcc : Finset.Icc 1 (1 - 1) = ∅ := by decide
    have h11 : (1 : ℕ) + 1 = 2 := rfl
    rw [hIcc, Finset.sum_empty, add_zero, h11] at hstep
    rw [hstep]
    apply ENNReal.add_ne_top.mpr
    constructor
    · refine zetaR_ne_top 2 R le_rfl ?_
      intro x hx
      rw [hR, List.mem_append] at hx
      rcases hx with hx | hx
      · rw [List.mem_replicate] at hx
        obtain ⟨-, rfl⟩ := hx
        exact le_rfl
      · rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · omega
        · exact hs x hx
    · have hR1 : R ++ [1]
          = List.replicate p 1 ++ L :: (s ++ [1]) := by
        rw [hR, List.append_assoc, List.cons_append]
      rw [hR1]
      apply ih
      intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact hs x hx
      · rw [List.mem_singleton] at hx
        subst hx
        exact le_rfl

end CyclicSumFormula

/--
**Cyclic sum formula for strict multiple zeta values of indices.** Let $k = (k_1, \dots, k_l)$
be a nonempty list of positive integers, not all equal to $1$, with subscripts read modulo $l$,
and write $\zeta$ for the strict multiple zeta value. For $1 \le j \le l$ and
$1 \le i \le k_j - 1$ the left-hand index of the cyclic sum formula of $k$ at $(j, i)$ is
$(k_j - i + 1, k_{j+1}, \dots, k_{j+l-1}, i)$, and its right-hand index at $j$ is
$(k_j + 1, k_{j+1}, \dots, k_{j+l-1})$; the run $k_{j+1}, \dots, k_{j+l-1}$ is empty when
$l = 1$. Then
$$
\sum_{j=1}^{l} \sum_{i=1}^{k_j - 1} \zeta(k_j - i + 1, k_{j+1}, \dots, k_{j+l-1}, i)
= \sum_{j=1}^{l} \zeta(k_j + 1, k_{j+1}, \dots, k_{j+l-1}),
$$
where the inner sum is empty when $k_j = 1$.
-/
theorem hoffman_ohno_cyclic_sum_formula_strict
    (k : List ℕ)
    (hk_nonempty : k ≠ [])
    (hk_pos : ∀ n ∈ k, 1 ≤ n)
    (hk_not_all_one : ∃ n ∈ k, n ≠ 1) :
    ∑ j : Fin k.length,
        ∑ i ∈ Finset.Icc 1 (k.get j - 1),
          MultipleZeta.strictValue (CyclicSumFormula.leftIndex k hk_pos j i)
            (CyclicSumFormula.leftIndex_isAdmissibleOrEmpty k hk_pos j i) =
      ∑ j : Fin k.length,
        MultipleZeta.strictValue (CyclicSumFormula.rightIndex k hk_pos j)
          (CyclicSumFormula.rightIndex_isAdmissibleOrEmpty k hk_pos j) := by
  have _ : k.length ≠ 0 := fun h => hk_nonempty (List.length_eq_zero_iff.mp h)
  have hstep : ∀ j : Fin k.length,
      CyclicSumFormula.cycT (k.rotate j.1)
        + ∑ i ∈ Finset.Icc 1 (k.get j - 1),
          CyclicSumFormula.zetaR
            ((k.get j - i + 1) :: ((k.rotate j.1).tail ++ [i]))
      = CyclicSumFormula.zetaR ((k.get j + 1) :: (k.rotate j.1).tail)
        + CyclicSumFormula.cycT (k.rotate (j.1 + 1)) := by
    intro j
    have hLa : k.rotate j.1 = k.get j :: (k.rotate j.1).tail :=
      CyclicSumFormula.rotate_eq_get_cons_tail k j
    have hLb : (k.rotate j.1).tail ++ [k.get j] = k.rotate (j.1 + 1) :=
      CyclicSumFormula.rotate_tail_append_get k j
    have hLpos : 1 ≤ k.get j := hk_pos _ (List.get_mem k j)
    have h9 := CyclicSumFormula.cycT_rotation_step (k.get j) hLpos
      (k.rotate j.1).tail
    rw [← hLa, hLb] at h9
    exact h9
  have hsum : (∑ j : Fin k.length, CyclicSumFormula.cycT (k.rotate j.1))
        + ∑ j : Fin k.length, ∑ i ∈ Finset.Icc 1 (k.get j - 1),
          CyclicSumFormula.zetaR
            ((k.get j - i + 1) :: ((k.rotate j.1).tail ++ [i]))
      = (∑ j : Fin k.length,
          CyclicSumFormula.zetaR ((k.get j + 1) :: (k.rotate j.1).tail))
        + ∑ j : Fin k.length, CyclicSumFormula.cycT (k.rotate (j.1 + 1)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => hstep j)
  have hreidx : (∑ j : Fin k.length,
        CyclicSumFormula.cycT (k.rotate (j.1 + 1)))
      = ∑ j : Fin k.length, CyclicSumFormula.cycT (k.rotate j.1) :=
    CyclicSumFormula.sum_rotate_succ k (fun l => CyclicSumFormula.cycT l)
  have hSne : (∑ j : Fin k.length, CyclicSumFormula.cycT (k.rotate j.1)) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro j _
    apply CyclicSumFormula.cycT_ne_top
    · intro x hx
      rw [List.mem_rotate] at hx
      exact hk_pos x hx
    · obtain ⟨x, hx, hx1⟩ := hk_not_all_one
      exact ⟨x, List.mem_rotate.mpr hx, hx1⟩
  have hcancel : (∑ j : Fin k.length, ∑ i ∈ Finset.Icc 1 (k.get j - 1),
        CyclicSumFormula.zetaR
          ((k.get j - i + 1) :: ((k.rotate j.1).tail ++ [i])))
      = ∑ j : Fin k.length,
        CyclicSumFormula.zetaR ((k.get j + 1) :: (k.rotate j.1).tail) := by
    rw [hreidx] at hsum
    rw [add_comm (∑ j : Fin k.length, CyclicSumFormula.cycT (k.rotate j.1)) _]
      at hsum
    exact (ENNReal.add_left_inj hSne).mp hsum
  have hE : (∑ j : Fin k.length, ∑ i ∈ Finset.Icc 1 (k.get j - 1),
        CyclicSumFormula.zetaE
          ((k.get j - i + 1) :: ((k.rotate j.1).tail ++ [i])))
      = ∑ j : Fin k.length,
        CyclicSumFormula.zetaE ((k.get j + 1) :: (k.rotate j.1).tail) := by
    have h1 : (∑ j : Fin k.length, ∑ i ∈ Finset.Icc 1 (k.get j - 1),
          CyclicSumFormula.zetaR
            ((k.get j - i + 1) :: ((k.rotate j.1).tail ++ [i])))
        = ∑ j : Fin k.length, ∑ i ∈ Finset.Icc 1 (k.get j - 1),
          CyclicSumFormula.zetaE
            ((k.get j - i + 1) :: ((k.rotate j.1).tail ++ [i])) :=
      Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ =>
        (CyclicSumFormula.zetaE_cons_eq_zetaR _ _).symm))
    have h2 : (∑ j : Fin k.length,
          CyclicSumFormula.zetaR ((k.get j + 1) :: (k.rotate j.1).tail))
        = ∑ j : Fin k.length,
          CyclicSumFormula.zetaE ((k.get j + 1) :: (k.rotate j.1).tail) :=
      Finset.sum_congr rfl
        (fun j _ => (CyclicSumFormula.zetaE_cons_eq_zetaR _ _).symm)
    rw [← h1, ← h2]
    exact hcancel
  have hfinA : ∀ j : Fin k.length, ∀ i ∈ Finset.Icc 1 (k.get j - 1),
      CyclicSumFormula.zetaE
        ((k.get j - i + 1) :: ((k.rotate j.1).tail ++ [i])) ≠ ⊤ := by
    intro j i hi
    apply CyclicSumFormula.zetaE_ne_top
    · have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hi2 : i ≤ k.get j - 1 := (Finset.mem_Icc.mp hi).2
      omega
    · intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · have hxR : x ∈ k.rotate j.1 := List.mem_of_mem_tail hx
        rw [List.mem_rotate] at hxR
        exact hk_pos x hxR
      · rw [List.mem_singleton] at hx
        subst hx
        exact (Finset.mem_Icc.mp hi).1
  have hfinB : ∀ j : Fin k.length,
      CyclicSumFormula.zetaE ((k.get j + 1) :: (k.rotate j.1).tail) ≠ ⊤ := by
    intro j
    apply CyclicSumFormula.zetaE_ne_top
    · have hg := hk_pos _ (List.get_mem k j)
      omega
    · intro x hx
      have hxR : x ∈ k.rotate j.1 := List.mem_of_mem_tail hx
      rw [List.mem_rotate] at hxR
      exact hk_pos x hxR
  have hneA : ∀ j ∈ (Finset.univ : Finset (Fin k.length)),
      (∑ i ∈ Finset.Icc 1 (k.get j - 1), CyclicSumFormula.zetaE
        ((k.get j - i + 1) :: ((k.rotate j.1).tail ++ [i]))) ≠ ⊤ :=
    fun j _ => ENNReal.sum_ne_top.mpr (fun i hi => hfinA j i hi)
  have hneB : ∀ j ∈ (Finset.univ : Finset (Fin k.length)),
      CyclicSumFormula.zetaE ((k.get j + 1) :: (k.rotate j.1).tail) ≠ ⊤ :=
    fun j _ => hfinB j
  have hcongr := congrArg ENNReal.toReal hE
  rw [ENNReal.toReal_sum hneA, ENNReal.toReal_sum hneB] at hcongr
  have hinner : ∀ j : Fin k.length,
      (∑ i ∈ Finset.Icc 1 (k.get j - 1), CyclicSumFormula.zetaE
        ((k.get j - i + 1) :: ((k.rotate j.1).tail ++ [i]))).toReal
      = ∑ i ∈ Finset.Icc 1 (k.get j - 1), (CyclicSumFormula.zetaE
        ((k.get j - i + 1) :: ((k.rotate j.1).tail ++ [i]))).toReal :=
    fun j => ENNReal.toReal_sum (fun i hi => hfinA j i hi)
  simp only [hinner] at hcongr
  have hzL : ∀ (j : Fin k.length) (i : ℕ),
      i ∈ Finset.Icc 1 (k.get j - 1) →
        (CyclicSumFormula.zetaE
            ((k.get j - i + 1) :: ((k.rotate j.1).tail ++ [i]))).toReal =
          MultipleZeta.strictValue (CyclicSumFormula.leftIndex k hk_pos j i)
            (CyclicSumFormula.leftIndex_isAdmissibleOrEmpty k hk_pos j i) := by
    intro j i hi
    rw [← CyclicSumFormula.multipleZetaValue_eq_toReal_zetaE]
    exact CyclicSumFormula.mzV_eq_strictValue_left k hk_pos j i hi
  have hzR : ∀ j : Fin k.length,
      (CyclicSumFormula.zetaE
          ((k.get j + 1) :: (k.rotate j.1).tail)).toReal =
        MultipleZeta.strictValue (CyclicSumFormula.rightIndex k hk_pos j)
          (CyclicSumFormula.rightIndex_isAdmissibleOrEmpty k hk_pos j) := by
    intro j
    rw [← CyclicSumFormula.multipleZetaValue_eq_toReal_zetaE]
    exact CyclicSumFormula.mzV_eq_strictValue_right k hk_pos j
  have hL : (∑ j : Fin k.length, ∑ i ∈ Finset.Icc 1 (k.get j - 1),
        (CyclicSumFormula.zetaE
          ((k.get j - i + 1) :: ((k.rotate j.1).tail ++ [i]))).toReal)
      = ∑ j : Fin k.length, ∑ i ∈ Finset.Icc 1 (k.get j - 1),
        MultipleZeta.strictValue (CyclicSumFormula.leftIndex k hk_pos j i)
          (CyclicSumFormula.leftIndex_isAdmissibleOrEmpty k hk_pos j i) :=
    Finset.sum_congr rfl
      (fun j _ => Finset.sum_congr rfl (fun i hi => hzL j i hi))
  have hR : (∑ j : Fin k.length, (CyclicSumFormula.zetaE
        ((k.get j + 1) :: (k.rotate j.1).tail)).toReal)
      = ∑ j : Fin k.length, MultipleZeta.strictValue
        (CyclicSumFormula.rightIndex k hk_pos j)
        (CyclicSumFormula.rightIndex_isAdmissibleOrEmpty k hk_pos j) :=
    Finset.sum_congr rfl (fun j _ => hzR j)
  exact hL.symm.trans (hcongr.trans hR)

/--
**Cyclic sum formula (Hoffman–Ohno).** For a finite list $(n_1, \dots, n_r)$ of natural numbers
let $\zeta(n_1, \dots, n_r)$ be the sum of $(m_1^{n_1} \cdots m_r^{n_r})^{-1}$ over all integers
$m_1 > m_2 > \cdots > m_r > 0$, taken to be $0$ when this family is not summable. Let
$k = (k_1, \dots, k_l)$ be a nonempty list of positive integers, not all equal to $1$, with
subscripts read modulo $l$. Then
$$
\sum_{j=1}^{l} \sum_{i=1}^{k_j - 1} \zeta(k_j - i + 1, k_{j+1}, \dots, k_{j+l-1}, i)
= \sum_{j=1}^{l} \zeta(k_j + 1, k_{j+1}, \dots, k_{j+l-1}),
$$
where the inner sum is empty when $k_j = 1$ and the run $k_{j+1}, \dots, k_{j+l-1}$ is empty
when $l = 1$.

Proves `Wanted` entry `hoffman_ohno_cyclic_sum_formula`.

Source: Shingo Saito, Tatsushi Tanaka, and Noriko Wakabayashi,
"Combinatorial Remarks on the Cyclic Sum Formula for Multiple Zeta Values,"
Journal of Integer Sequences 14 (2011), Article 11.2.4,
Theorem `thm:CSF` ("Cyclic sum formula," first proved by Hoffman-Ohno), lines 242–248;
index set `check{I}^1` at lines 150–166,
<https://cs.uwaterloo.ca/journals/JIS/VOL14/Saito/saito22.tex>.
-/
theorem hoffman_ohno_cyclic_sum_formula
    (k : List ℕ)
    (hk_nonempty : k ≠ [])
    (hk_pos : ∀ n ∈ k, 1 ≤ n)
    (hk_not_all_one : ∃ n ∈ k, n ≠ 1) :
    ∑ j : Fin k.length,
        ∑ i ∈ Finset.Icc 1 (k.get j - 1),
          multipleZetaValue
            ((k.get j - i + 1) :: ((k.rotate j.1).tail ++ [i])) =
      ∑ j : Fin k.length,
        multipleZetaValue ((k.get j + 1) :: (k.rotate j.1).tail) := by
  have hL : ∀ (j : Fin k.length) (i : ℕ),
      i ∈ Finset.Icc 1 (k.get j - 1) →
        multipleZetaValue
            ((k.get j - i + 1) :: ((k.rotate j.1).tail ++ [i])) =
          MultipleZeta.strictValue (CyclicSumFormula.leftIndex k hk_pos j i)
            (CyclicSumFormula.leftIndex_isAdmissibleOrEmpty k hk_pos j i) :=
    fun j i hi => CyclicSumFormula.mzV_eq_strictValue_left k hk_pos j i hi
  have hR : ∀ j : Fin k.length,
      multipleZetaValue ((k.get j + 1) :: (k.rotate j.1).tail) =
        MultipleZeta.strictValue (CyclicSumFormula.rightIndex k hk_pos j)
          (CyclicSumFormula.rightIndex_isAdmissibleOrEmpty k hk_pos j) :=
    fun j => CyclicSumFormula.mzV_eq_strictValue_right k hk_pos j
  calc ∑ j : Fin k.length, ∑ i ∈ Finset.Icc 1 (k.get j - 1),
          multipleZetaValue
            ((k.get j - i + 1) :: ((k.rotate j.1).tail ++ [i]))
      = ∑ j : Fin k.length, ∑ i ∈ Finset.Icc 1 (k.get j - 1),
          MultipleZeta.strictValue (CyclicSumFormula.leftIndex k hk_pos j i)
            (CyclicSumFormula.leftIndex_isAdmissibleOrEmpty k hk_pos j i) :=
        Finset.sum_congr rfl
          (fun j _ => Finset.sum_congr rfl (fun i hi => hL j i hi))
    _ = ∑ j : Fin k.length, MultipleZeta.strictValue
          (CyclicSumFormula.rightIndex k hk_pos j)
          (CyclicSumFormula.rightIndex_isAdmissibleOrEmpty k hk_pos j) :=
        hoffman_ohno_cyclic_sum_formula_strict k hk_nonempty hk_pos
          hk_not_all_one
    _ = ∑ j : Fin k.length,
          multipleZetaValue ((k.get j + 1) :: (k.rotate j.1).tail) :=
        Finset.sum_congr rfl (fun j _ => (hR j).symm)

end MetaMathlibExt
end
