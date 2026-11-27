/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Coding.CycleCode
import Mathlib.Data.List.Pairwise

/-!
# The Polak–Schrijver lower bound for the capacity of the 7-cycle

The 367 words in the appendix of Polak and Schrijver (arXiv:1808.07438) give a
length-five code. Its fifth-root rate bounds the Shannon capacity from below.
-/

namespace MathlibExt.Combinatorics.Coding.CycleShannonBoundsWanted

open MathlibExt.Combinatorics.Coding.CycleGraphCode

/-- Each decimal position records one letter of a word in the appendix, including leading zeros. -/
private def appendix : List ℕ :=
  [
    02020, 02112, 02204, 02306, 02461, 02553, 03645, 03040, 03032, 03124, 03226, 03311,
    03403, 14144, 14231, 14323, 14415, 14510, 15602, 15064, 15166, 15251, 15343, 15430,
    15522, 16614, 16016, 16101, 16263, 16355, 16450, 16542, 10636, 10021, 10113, 10205,
    10300, 10462, 10554, 11656, 11041, 11033, 11125, 11220, 11312, 11404, 11506, 12661,
    12053, 12145, 12240, 12232, 12324, 12426, 12511, 13603, 13065, 13160, 13252, 13344,
    13446, 13431, 24010, 24102, 24264, 24366, 24451, 24543, 25630, 25022, 25114, 25216,
    25301, 25463, 25555, 26650, 26042, 26034, 26136, 26221, 26313, 26405, 26500, 20662,
    20054, 20156, 20241, 20233, 20325, 20420, 20512, 21604, 21006, 21161, 21253, 21345,
    21440, 21432, 22626, 22011, 22103, 22265, 22360, 22452, 22544, 23631, 23023, 23115,
    23210, 23302, 23464, 23566, 34130, 34222, 34314, 34416, 34501, 35663, 35055, 35150,
    35242, 35234, 35336, 35421, 35513, 36605, 36000, 36162, 36254, 36356, 36441, 36433,
    30620, 30012, 30104, 30206, 30361, 30453, 30545, 31632, 31024, 31126, 31211, 31303,
    31465, 31560, 32652, 32044, 32131, 32223, 32315, 32410, 32502, 33664, 33066, 33151,
    33243, 33235, 33330, 33422, 44616, 44001, 44163, 44255, 44350, 44442, 44434, 44536,
    45621, 45013, 45105, 45200, 45362, 45454, 45556, 46633, 46025, 46120, 46212, 46304,
    46406, 46561, 40653, 40045, 40132, 40224, 40326, 40411, 40503, 41665, 41060, 41152,
    41244, 41331, 41423, 41515, 42610, 42002, 42164, 42266, 42351, 42443, 42435, 43622,
    43014, 43116, 43201, 43363, 43455, 43550, 54634, 54036, 54121, 54213, 54305, 54400,
    54562, 55654, 55056, 55141, 55133, 55225, 55320, 55412, 55504, 56606, 56061, 56153,
    56245, 56332, 56424, 56526, 50611, 50003, 50165, 50260, 50352, 50444, 51623, 51015,
    51110, 51202, 51364, 51551, 52643, 52635, 52030, 52122, 52214, 53655, 53134, 64332,
    64424, 64526, 65611, 65003, 65260, 65352, 65444, 65546, 66623, 66110, 66202, 66364,
    66466, 66551, 60643, 60645, 60030, 60122, 60214, 60316, 60401, 60563, 61050, 61142,
    61134, 61236, 61321, 61413, 62600, 62062, 62154, 62256, 62341, 62333, 62520, 63612,
    63004, 63106, 63261, 63353, 63445, 63540, 64532, 04026, 04111, 04203, 04460, 04552,
    05644, 05031, 05123, 05310, 05402, 05564, 06666, 06051, 06143, 06230, 06322, 06414,
    06516, 00601, 00063, 00155, 00250, 00342, 00334, 00436, 01613, 01100, 01262, 01354,
    01456, 01541, 02625, 00521, 01005, 02533, 03565, 04052, 04365, 04624, 04660, 05046,
    05225, 10534, 14246, 15435, 22524, 24615, 24651, 32046, 34035, 34043, 36525, 40040,
    41246, 42530, 43514, 45641, 50531, 51456, 52400, 52563, 53050, 53142, 53320, 53412,
    56340, 61505, 62425, 64154, 64340, 65105, 66025]

private def decode (n : ℕ) (i : Fin 5) : Fin 7 :=
  Fin.ofNat 7 (n / 10 ^ (4 - i.val) % 10)

private abbrev Near (a b : Fin 7) : Prop := a - b = -1 ∨ a - b = 0 ∨ a - b = 1

private abbrev OnEdge (v a : Fin 7) : Prop := a = v ∨ a = v + 1

private theorem common_edge : ∀ a b : Fin 7, Near a b → ∃ v : Fin 7, OnEdge v a ∧ OnEdge v b := by
  decide +kernel

/-- Check that each product of cycle edges contains at most one row. Two confusable words
lie in such a product since their letters share an edge in every coordinate. -/
private def checkBoxes : List (Fin 5) → List ℕ → Bool
  | [], xs => decide (xs.length ≤ 1)
  | i :: is, xs => (List.finRange 7).all fun v ↦
      checkBoxes is (xs.filter fun n ↦ decide (OnEdge v (decode n i)))

private theorem checkBoxes_sound {x y : ℕ} (coords : List (Fin 5)) (rows : List ℕ)
    (ok : checkBoxes coords rows) (hxy : [x, y].Sublist rows)
    (h : ∀ i ∈ coords, Near (decode x i) (decode y i)) : False := by
  induction coords generalizing rows with
  | nil =>
    have hlen : rows.length ≤ 1 := of_decide_eq_true ok
    exact (by decide : ¬2 ≤ 1) (hxy.length_le.trans hlen)
  | cons i is ih =>
    obtain ⟨v, hx, hy⟩ := common_edge _ _ (h i (by simp))
    apply ih _ (List.all_eq_true.mp ok v (List.mem_finRange v)) _ (fun j hj ↦ h j (by simp [hj]))
    simpa [hx, hy] using hxy.filter (fun n ↦ decide (OnEdge v (decode n i)))

set_option maxRecDepth 2048 in
private theorem checked_boxes : checkBoxes (List.finRange 5) appendix := by decide +kernel

private def words := appendix.map decode

private abbrev Separated (x y : Fin 5 → Fin 7) : Prop :=
  ¬∀ i, Near (x i) (y i)

private theorem near_symm : ∀ a b : Fin 7, Near a b → Near b a := by decide +kernel

private instance separatedSymm : Std.Symm Separated where
  symm _ _ sep h := sep fun i ↦ near_symm _ _ (h i)

private theorem words_separated : words.Pairwise Separated := by
  apply List.pairwise_map.mpr
  apply List.pairwise_iff_forall_sublist.mpr
  exact fun hsub h ↦ checkBoxes_sound _ _ checked_boxes hsub fun i _ ↦ h i

/-- **Polak–Schrijver code of size 367 for the 7-cycle.** There is a finite set $A$ of words of
length $5$ over $\mathbb{Z}/7\mathbb{Z}$ that is an independent code for the $7$-cycle and has
exactly $367$ elements.

Source: Polak--Schrijver, arXiv:1808.07438, the fifth-power 367-word construction. -/
public theorem polakSchrijverLowerBound :
    ∃ A : Finset (Fin 5 → ZMod 7), IsCycleCode 7 A ∧ A.card = 367 := by
  have nodup : words.Nodup := words_separated.imp fun h he ↦ h (by simp [he, Near])
  have hcard : words.toFinset.card = 367 := by
    rw [List.toFinset_card_of_nodup nodup, words, List.length_map]
    decide +kernel
  refine ⟨words.toFinset, ?_, hcard⟩
  rintro _ ⟨x, hx, y, hy, rfl⟩ h
  by_cases he : x = y
  · simp [he]
  exact (words_separated.forall (List.mem_toFinset.mp hx) (List.mem_toFinset.mp hy) he h).elim

/-- **Polak–Schrijver lower bound for the capacity of the 7-cycle.** The Shannon capacity of the
$7$-cycle is at least $367^{1/5}$, as an inequality in $[0, \infty]$.

Source: Polak--Schrijver, arXiv:1808.07438, exact fifth-root rate. -/
public theorem polakSchrijverRateLowerBound :
    ENNReal.rpow 367 ((5 : ℝ)⁻¹) ≤ shannonCapacityCycle 7 :=
  cycleConstruction_implies_lowerBound 7 5 367 (by decide) polakSchrijverLowerBound

end MathlibExt.Combinatorics.Coding.CycleShannonBoundsWanted
