/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Round
public import MathlibExt.NumberTheory.FloorCeilingSums
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum

/-!
# Relations and periodicity of inclusion-exclusion-like sums

Appending a half-coordinate relates the two nearest-integer sums to floor and ceiling sums.
All four sums are periodic in each coordinate when there are at least two coordinates.
-/

namespace MetaMathlibExt
namespace inclExclLikeSum_relations_and_periodic

open Finset

-- Include the empty subset so that inserting an index gives an ordinary finite difference.
private def alternating {α : Type*} (s : Finset α) (x : α → ℝ) (F : ℝ → ℤ) : ℤ :=
  ∑ T ∈ s.powerset, (-1) ^ T.card * F (∑ j ∈ T, x j)

private theorem inclExclLikeSum_eq {n : ℕ} (F : ℝ → ℤ) (x : Fin n → ℝ) :
    inclExclLikeSum F x = F 0 - alternating univ x F := by
  rw [inclExclLikeSum, alternating, powerset_univ, sum_filter]
  rw [show F 0 = ∑ T : Finset (Fin n), (if T = ∅ then F 0 else 0) by simp, ← sum_sub_distrib]
  refine sum_congr rfl fun T _ => ?_
  rcases T.eq_empty_or_nonempty with rfl | hT
  · simp
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (card_pos.mpr hT).ne'
    simp [hT, hT.ne_empty, hk, pow_succ]

private theorem alternating_insert {α : Type*} [DecidableEq α] {i : α} {s : Finset α}
    (hi : i ∉ s) (x : α → ℝ) (F : ℝ → ℤ) :
    alternating (insert i s) x F = alternating s x (fun t => F t - F (t + x i)) := by
  simp only [alternating, sum_powerset_insert hi, mul_sub, sum_sub_distrib]
  rw [← sub_neg_eq_add, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun T hT => ?_
  have hiT := notMem_mono (mem_powerset.mp hT) hi
  simp [hiT, pow_succ, add_comm]

private theorem alternating_snoc {n : ℕ} (x : Fin n → ℝ) (c : ℝ) (F : ℝ → ℤ) :
    alternating univ (Fin.snoc x c) F =
      alternating univ x (fun t => F t - F (t + c)) := by
  rw [Fin.univ_castSuccEmb n, cons_eq_insert, alternating_insert (by simp [map_eq_image])]
  have hinj := (@Fin.castSuccEmb n).injective
  simp only [alternating, map_eq_image, powerset_image, Fin.snoc_last]
  rw [sum_image (image_injOn_powerset_of_injOn hinj.injOn)]
  simp only [card_image_of_injective _ hinj, sum_image hinj.injOn, Fin.castSuccEmb_apply,
    Fin.snoc_castSucc]

private theorem shift_eq_sub_snoc {n : ℕ} (x : Fin n → ℝ) (c : ℝ) (F : ℝ → ℤ) (hc : F c = 0) :
    inclExclLikeSum (fun t => F (t + c)) x =
      inclExclLikeSum F x - inclExclLikeSum F (Fin.snoc x c) := by
  simp only [inclExclLikeSum_eq, zero_add, hc, alternating_snoc]
  simp [alternating, mul_sub, sum_sub_distrib]

private theorem periodic {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (F : ℝ → ℤ) (i : Fin n)
    (q : ℤ) (hF : ∀ t, F (t + q) = F t + q) :
    inclExclLikeSum F (Function.update x i (x i + q)) = inclExclLikeSum F x := by
  let s := univ.erase i
  have hs : s.Nonempty := card_pos.mp (by simp [s, card_erase_of_mem]; omega)
  have hi : i ∉ s := notMem_erase _ _
  have hu : (univ : Finset (Fin n)) = insert i s := (insert_erase (mem_univ i)).symm
  simp only [inclExclLikeSum_eq, hu, alternating_insert hi, Function.update_self, sub_right_inj]
  unfold alternating
  have hterm (T : Finset (Fin n)) (hT : T ∈ s.powerset) :
      (∑ j ∈ T, Function.update x i (x i + q) j) = ∑ j ∈ T, x j :=
    sum_update_of_notMem (notMem_mono (mem_powerset.mp hT) hi) _ _
  calc
    _ = ∑ T ∈ s.powerset, ((-1 : ℤ) ^ T.card *
          (F (∑ j ∈ T, x j) - F ((∑ j ∈ T, x j) + x i)) - (-1) ^ T.card * q) := by
      refine sum_congr rfl fun T hT => ?_
      simp only [hterm T hT, ← add_assoc, hF]
      ring
    _ = _ := by
      rw [sum_sub_distrib, ← sum_mul, sum_powerset_neg_one_pow_card_of_nonempty hs, zero_mul,
        sub_zero]

end inclExclLikeSum_relations_and_periodic

open inclExclLikeSum_relations_and_periodic in
/-- **Relations and periodicity of the inclusion-exclusion-like sums.** Let $n \ge 2$ and write
$g_1$, $g_2$, $g_3$, $g_4$ for the inclusion-exclusion-like sums $g^{(F)}$ with $F$ the floor
function $\lfloor y \rfloor$, the ceiling function $\lceil y \rceil$, the nearest-integer function
$\lfloor y + 1/2 \rfloor$ (ties rounded up) and $\lceil y - 1/2 \rceil$ (ties rounded down),
respectively. For every $x = (x_1, \dots, x_n) \in \mathbb{R}^n$:
(i) $g_3(x) = g_1(x) - g_1(x_1, \dots, x_n, 1/2)$;
(ii) $g_4(x) = g_2(x) - g_2(x_1, \dots, x_n, -1/2)$;
(iii) for each $j \in \{1, 2, 3, 4\}$, each index $i$ and each integer $q$, adding $q$ to $x_i$
does not change $g_j(x)$.

Parts (i) and (ii) also hold for $n < 2$; part (iii) fails for $n = 1$, where
$g_1(x) = \lfloor x \rfloor$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Lemma 1. -/
public theorem inclExclLikeSum_relations_and_periodic {n : ℕ} (hn : 2 ≤ n)
    (x : Fin n → ℝ) :
    inclExclLikeSum round x =
        inclExclLikeSum Int.floor x - inclExclLikeSum Int.floor (Fin.snoc x (1 / 2 : ℝ)) ∧
      inclExclLikeSum (fun y : ℝ => ⌈y - 1 / 2⌉) x =
        inclExclLikeSum Int.ceil x - inclExclLikeSum Int.ceil (Fin.snoc x (-1 / 2 : ℝ)) ∧
      ∀ F ∈ ({Int.floor, Int.ceil, round, fun y : ℝ => ⌈y - 1 / 2⌉} : Set (ℝ → ℤ)),
        ∀ (i : Fin n) (q : ℤ),
        inclExclLikeSum F (Function.update x i (x i + q)) = inclExclLikeSum F x := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [← round_eq] using shift_eq_sub_snoc x (1 / 2) Int.floor (by norm_num)
  · simpa only [neg_div, ← sub_eq_add_neg] using
      shift_eq_sub_snoc x (-1 / 2) Int.ceil (by norm_num)
  · intro F hF i q
    apply periodic hn x F i q
    intro t
    rcases hF with rfl | rfl | rfl | h
    · exact Int.floor_add_intCast _ _
    · exact Int.ceil_add_intCast _ _
    · exact round_add_intCast _ _
    · obtain rfl := Set.mem_singleton_iff.mp h
      simpa only [add_sub_right_comm] using Int.ceil_add_intCast (t - 1 / 2) q

end MetaMathlibExt
