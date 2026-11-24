/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/24.lean` (Formal Conjectures):
Copyright The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors.
Adapted portions: the definition of `conjecture` and the statement of `conjecture_holds`.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Pentagons in triangle-free graphs

`conjecture_holds` bounds the number of pentagons on `5 * n` vertices by `n ^ 5`.
We use the three flag matrices of A. Grzesik, *On the maximum number of five-cycles
in a triangle-free graph*, https://arxiv.org/abs/1102.0962v3. We sample five vertices
with replacement, so the quadratic forms in the flag counts give exact finite sums.
-/

@[expose] public section

namespace MathlibExt.GraphTheory.ErdosProblem24Wanted

/-- **Pentagons in triangle-free graphs (Erdős Problem 24).** For every natural number $n$, every
graph on $5n$ vertices with no three pairwise adjacent vertices has at most $n^5$ subgraphs
isomorphic to the $5$-cycle $C_5$. -/
def conjecture : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin (5 * n))), G.CliqueFree 3 →
    G.copyCount (SimpleGraph.cycleGraph 5) ≤ n ^ 5

open Finset SimpleGraph

-- The bits record adjacency to the first, second and third root, respectively.
private def bits (a b c : Bool) : Fin 8 :=
  (if a then 1 else 0) + (if b then 2 else 0) + (if c then 4 else 0)

-- Grzesik's matrices, scaled by 2500. Rows and columns for inadmissible flags are zero.
private def emptyFlags : Fin 8 → Fin 8 → ℤ :=
  ![![96, -144, -144, 96, -144, 96, 96, -144],
    ![-144, 1108, 388, -316, 388, -316, -1036, 216],
    ![-144, 388, 1108, -316, 388, -1036, -316, 216],
    ![96, -316, -316, 988, -1036, 268, 268, -144],
    ![-144, 388, 388, -1036, 1108, -316, -316, 216],
    ![96, -316, -1036, 268, -316, 988, 268, -144],
    ![96, -1036, -316, 268, -316, 268, 988, -144],
    ![-144, 216, 216, -144, 216, -144, -144, 216]]

private def edgeFlags : Fin 8 → Fin 8 → ℤ :=
  ![![1728, -1551, -1551, 0, -1308, 687, 687, 0],
    ![-1551, 2336, 742, 0, 908, 2557, -4084, 0],
    ![-1551, 742, 2336, 0, 908, -4084, 2557, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![-1308, 908, 908, 0, 1728, -254, -254, 0],
    ![687, 2557, -4084, 0, -254, 15264, -14424, 0],
    ![687, -4084, 2557, 0, -254, -14424, 15264, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0]]

private def pathFlags : Fin 8 → Fin 8 → ℤ :=
  ![![6048, 2272, -1520, 0, 2272, -1504, 0, 0],
    ![2272, 1900, -764, 0, 0, -372, 0, 0],
    ![-1520, -764, 768, 0, -764, -8, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![2272, 0, -764, 0, 1900, -372, 0, 0],
    ![-1504, -372, -8, 0, -372, 760, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0]]

private def flagMatrix (t : Fin 8) : Fin 8 → Fin 8 → ℤ :=
  if t = 0 then emptyFlags else if t = 1 then edgeFlags else if t = 5 then pathFlags
  else fun _ _ => 0

-- The ten edges in the graph pulled back along an ordered five-tuple.
private structure Pattern where
  ab : Bool
  ac : Bool
  ad : Bool
  ae : Bool
  bc : Bool
  bd : Bool
  be : Bool
  cd : Bool
  ce : Bool
  de : Bool

private def Pattern.flag (p : Pattern) : ℤ :=
  flagMatrix (bits p.ab p.ac p.bc) (bits p.ad p.bd p.cd) (bits p.ae p.be p.ce)

private def Pattern.cycle (p : Pattern) : Bool :=
  p.ab && p.bc && p.cd && p.de && p.ae

-- A pentagon has ten cyclic orders among its 120 orders, hence the coefficient 12 × 2500.
private def Pattern.score (p : Pattern) : ℤ :=
  p.flag + 30000 * (if p.cycle then 1 else 0)

private def Pattern.triangle (p : Pattern) : Bool :=
  (p.ab && p.ac && p.bc) || (p.ab && p.ad && p.bd) || (p.ab && p.ae && p.be) ||
  (p.ac && p.ad && p.cd) || (p.ac && p.ae && p.ce) || (p.ad && p.ae && p.de) ||
  (p.bc && p.bd && p.cd) || (p.bc && p.be && p.ce) || (p.bd && p.be && p.de) ||
  (p.cd && p.ce && p.de)

private def swap01 (p : Pattern) : Pattern :=
  ⟨p.ab, p.bc, p.bd, p.be, p.ac, p.ad, p.ae, p.cd, p.ce, p.de⟩

private def swap12 (p : Pattern) : Pattern :=
  ⟨p.ac, p.ab, p.ad, p.ae, p.bc, p.cd, p.ce, p.bd, p.be, p.de⟩

private def swap23 (p : Pattern) : Pattern :=
  ⟨p.ab, p.ad, p.ac, p.ae, p.bd, p.bc, p.be, p.cd, p.de, p.ce⟩

private def swap34 (p : Pattern) : Pattern :=
  ⟨p.ab, p.ac, p.ae, p.ad, p.bc, p.be, p.bd, p.ce, p.cd, p.de⟩

-- Insert one position into a permutation of the earlier positions by adjacent swaps.
private def insertSum (f : Pattern → ℤ) : List (Pattern → Pattern) → Pattern → ℤ
  | [], p => f p
  | s :: ss, p => f p + insertSum (f ∘ s) ss p

private def symScore : Pattern → ℤ :=
  let f₂ := insertSum Pattern.score [swap01]
  let f₃ := insertSum f₂ [swap12, swap01]
  let f₄ := insertSum f₃ [swap23, swap12, swap01]
  insertSum f₄ [swap34, swap23, swap12, swap01]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
-- Check the ten edge bits and sum over all 120 orders for each triangle-free pattern.
private theorem score_bound (p : Pattern) (h : p.triangle = false) :
    symScore p ≤ 120 * 96 := by
  obtain ⟨a, b, c, d, e, f, g, i, j, k⟩ := p
  revert a b c d e f g i j k
  decide +kernel

-- Clearing denominators in a Gram factorization reduces each flag sum to a sum of squares.
private theorem gram_nonneg {V : Type*} [Fintype V] {r : ℕ}
    (M : Fin 8 → Fin 8 → ℤ) (d : ℤ) (hd : 0 < d)
    (w : Fin r → ℕ) (L : Fin r → Fin 8 → ℤ)
    (h : ∀ i j, d * M i j = ∑ k, (w k : ℤ) * L k i * L k j) (f : V → Fin 8) :
    0 ≤ ∑ x, ∑ y, M (f x) (f y) := by
  apply nonneg_of_mul_nonneg_right (a := d) _ hd
  calc
    0 ≤ ∑ k, (w k : ℤ) * (∑ x, L k (f x)) ^ 2 :=
      sum_nonneg fun _ _ => mul_nonneg (by positivity) (sq_nonneg _)
    _ = d * ∑ x, ∑ y, M (f x) (f y) := by
      simp_rw [pow_two, ← mul_assoc, mul_sum, sum_mul, h]
      rw [sum_comm]
      apply sum_congr rfl
      intro x _
      rw [sum_comm]
      apply sum_congr rfl
      intro y _
      apply sum_congr rfl
      intro k _
      ring

private theorem flags_nonneg {V : Type*} [Fintype V] (t : Fin 8) (f : V → Fin 8) :
    0 ≤ ∑ x, ∑ y, flagMatrix t (f x) (f y) := by
  unfold flagMatrix
  split
  · apply gram_nonneg emptyFlags 223 (by decide)
      (r := 4) ![5352, 4, 111240, 80280]
      ![![2, -3, -3, 2, -3, 2, 2, -3],
        ![0, -43, -43, 223, -223, 43, 43, 0],
        ![0, 1, 1, 0, 0, -1, -1, 0],
        ![0, 1, -1, 0, 0, 1, -1, 0]]
    decide
  split
  · apply gram_nonneg edgeFlags 1355027520 (by decide)
      (r := 5) ![7057435, 797, 69063862848, 425040, 1368539966640]
      ![![576, -517, -517, 0, -436, 229, 229, 0],
        ![0, -12769, -12769, 0, 35420, 12769, 12769, 0],
        ![0, 1, 1, 0, 0, -1, -1, 0],
        ![0, 1594, -1594, 0, 0, 6641, -6641, 0],
        ![0, 0, 0, 0, 0, 1, -1, 0]]
    decide
  split
  · apply gram_nonneg pathFlags 95 (by decide)
      (r := 3) ![2, 72952, 90250]
      ![![-376, -93, -2, 0, -93, 190, 0, 0],
        ![2, 1, -1, 0, 1, 0, 0, 0],
        ![0, 1, 0, 0, -1, 0, 0, 0]]
    decide
  simp

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

private def pattern (x : Fin 5 → V) : Pattern :=
  let e i j := decide (G.Adj (x i) (x j))
  ⟨e 0 1, e 0 2, e 0 3, e 0 4, e 1 2, e 1 3, e 1 4, e 2 3, e 2 4, e 3 4⟩

private theorem pattern_triangle (h : G.CliqueFree 3) (x : Fin 5 → V) :
    (pattern G x).triangle = false := by
  classical
  have h₃ (a b c : V) : G.Adj a b → G.Adj a c → ¬G.Adj b c :=
    fun hab hac hbc => h {a, b, c} (is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)
  simp only [Pattern.triangle, pattern, Bool.and_assoc, Bool.or_eq_false_iff,
    Bool.and_eq_false_imp, decide_eq_true_eq, decide_eq_false_iff_not]
  repeat' constructor
  all_goals exact h₃ _ _ _

variable [Fintype V]

private def total (f : Pattern → ℤ) : ℤ := ∑ x : Fin 5 → V, f (pattern G x)

private theorem total_swap (s : Pattern → Pattern) (i j : Fin 5)
    (hs : ∀ x, s (pattern G x) = pattern G (x ∘ Equiv.swap i j)) (f : Pattern → ℤ) :
    total G (f ∘ s) = total G f := by
  unfold total
  simp only [Function.comp_apply, hs]
  exact ((Equiv.swap i j).symm.arrowCongr (Equiv.refl V)).sum_comp
    (fun x => f (pattern G x))

private theorem total_insertSum (ss : List (Pattern → Pattern))
    (h : ∀ s ∈ ss, ∀ f, total G (f ∘ s) = total G f) (f : Pattern → ℤ) :
    total G (insertSum f ss) = (ss.length + 1 : ℕ) * total G f := by
  induction ss generalizing f with
  | nil => simp [insertSum]
  | cons s ss ih =>
    change (∑ x, (f (pattern G x) + insertSum (f ∘ s) ss (pattern G x))) = _
    rw [sum_add_distrib]
    change total G f + total G (insertSum (f ∘ s) ss) = _
    rw [ih (fun t ht => h t (by simp [ht])), h s (by simp)]
    push_cast
    simp [add_mul]
    ring

private theorem total_symScore : total G symScore = 120 * total G Pattern.score := by
  have h : ∀ s ∈ [swap34, swap23, swap12, swap01], ∀ f, total G (f ∘ s) = total G f := by
    intro s hs f
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · apply total_swap G _ 3 4 _ f
      intro x
      simp [swap34, pattern, Equiv.swap_apply_def, G.adj_comm]
    · apply total_swap G _ 2 3 _ f
      intro x
      simp [swap23, pattern, Equiv.swap_apply_def, G.adj_comm]
    · apply total_swap G _ 1 2 _ f
      intro x
      simp [swap12, pattern, Equiv.swap_apply_def, G.adj_comm]
    · apply total_swap G _ 0 1 _ f
      intro x
      simp [swap01, pattern, Equiv.swap_apply_def, G.adj_comm]
  unfold symScore
  repeat rw [total_insertSum G _ (fun s hs => h s (by simp_all))]
  norm_num [← mul_assoc]

private def tupleEquiv (V : Type*) : (V × V × V × V × V) ≃ (Fin 5 → V) where
  toFun
    | (a, b, c, d, e) => ![a, b, c, d, e]
  invFun x := (x 0, x 1, x 2, x 3, x 4)
  left_inv _ := rfl
  right_inv x := by ext i; fin_cases i <;> rfl

private theorem total_flag_nonneg : 0 ≤ total G Pattern.flag := by
  unfold total
  rw [← (tupleEquiv V).sum_comp (fun x => (pattern G x).flag)]
  simp only [Fintype.sum_prod_type]
  refine sum_nonneg fun a _ => sum_nonneg fun b _ => sum_nonneg fun c _ => ?_
  exact flags_nonneg (bits (decide (G.Adj a b)) (decide (G.Adj a c)) (decide (G.Adj b c)))
    (fun x => bits (decide (G.Adj a x)) (decide (G.Adj b x)) (decide (G.Adj c x)))

private abbrev Pentagon := cycleGraph 5

-- The five choices of a starting vertex and two choices of direction.
private def traversal (u : Fin 5 × Bool) (i : Fin 5) : Fin 5 :=
  if u.2 then u.1 + i else u.1 - i

private theorem traversal_injective : Function.Injective traversal := by
  have h : ∀ u v : Fin 5 × Bool,
      traversal u 0 = traversal v 0 → traversal u 1 = traversal v 1 → u = v := by decide
  exact fun u v huv => h u v (congrFun huv 0) (congrFun huv 1)

private def traversalIso (u : Fin 5 × Bool) : Pentagon ≃g Pentagon where
  toFun := traversal u
  invFun i := if u.2 then i - u.1 else u.1 - i
  left_inv := by revert u; decide
  right_inv := by revert u; decide
  map_rel_iff' := by revert u; decide

private abbrev PentagonSubgraph (G : SimpleGraph V) :=
  {S : G.Subgraph // Nonempty (Pentagon ≃g S.coe)}

private noncomputable def orderedCopy (S : PentagonSubgraph G) (u : Fin 5 × Bool) :
    Pentagon.Copy G :=
  S.val.coeCopy.comp ((S.property.some.comp (traversalIso u)).toCopy)

omit [Fintype V] [DecidableRel G.Adj] in
private theorem orderedCopy_image (S : PentagonSubgraph G) (u : Fin 5 × Bool) :
    (orderedCopy G S u).toSubgraph = S.val := by
  change (⊤ : Pentagon.Subgraph).map
    (S.val.hom.comp (S.property.some.comp (traversalIso u)).toHom) = S.val
  simp [Subgraph.map_comp]

omit [Fintype V] [DecidableRel G.Adj] in
private theorem orderedCopy_injective :
    Function.Injective (fun su : PentagonSubgraph G × (Fin 5 × Bool) =>
      (orderedCopy G su.1 su.2 : Fin 5 → V)) := by
  rintro ⟨S, u⟩ ⟨T, v⟩ h
  have hc := DFunLike.coe_injective h
  have he : S = T := Subtype.ext <| (orderedCopy_image G S u).symm.trans <|
    (congrArg Copy.toSubgraph hc).trans (orderedCopy_image G T v)
  subst T
  congr 1
  apply traversal_injective
  funext i
  apply S.property.some.injective
  apply Subtype.ext
  exact congrFun h i

omit [Fintype V] in
private theorem copy_cycle (f : Pentagon.Copy G) : (pattern G f).cycle = true := by
  have h (i j : Fin 5) (hij : Pentagon.Adj i j) : G.Adj (f i) (f j) := f.toHom.map_rel hij
  simp only [pattern, Pattern.cycle, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨h 0 1 (by decide), h 1 2 (by decide)⟩, h 2 3 (by decide)⟩,
    h 3 4 (by decide)⟩, h 0 4 (by decide)⟩

omit [DecidableRel G.Adj] in
private theorem card_pentagonSubgraph [Fintype (PentagonSubgraph G)] :
    Fintype.card (PentagonSubgraph G) = G.copyCount Pentagon := by
  classical
  unfold copyCount
  apply Fintype.card_of_subtype
  simp

private theorem copy_count_le :
    G.copyCount Pentagon * 10 ≤ #{x : Fin 5 → V | (pattern G x).cycle} := by
  classical
  let f (su : PentagonSubgraph G × (Fin 5 × Bool)) :
      {x : Fin 5 → V // (pattern G x).cycle} :=
    ⟨orderedCopy G su.1 su.2, copy_cycle G (orderedCopy G su.1 su.2)⟩
  have hf : Function.Injective f := by
    intro a b he
    apply orderedCopy_injective G (a₁ := a) (a₂ := b)
    exact congrArg Subtype.val he
  calc
    _ = Fintype.card (PentagonSubgraph G × (Fin 5 × Bool)) := by
      rw [Fintype.card_prod, Fintype.card_prod, card_pentagonSubgraph]
      rfl
    _ ≤ Fintype.card {x : Fin 5 → V // (pattern G x).cycle} :=
      Fintype.card_le_of_injective f hf
    _ = _ := Fintype.card_of_subtype _ (by simp)

/-- **Pentagon bound for triangle-free graphs (five-cycle case of Erdős Problem 24).** For every
natural number $n$, every graph on $5n$ vertices with no three pairwise adjacent vertices has at
most $n^5$ subgraphs isomorphic to the $5$-cycle $C_5$.

Source: Erdős Problems, Problem 24 (records the Grzesik and
Hatami–Hladký–Králʼ–Norine–Razborov resolution), https://www.erdosproblems.com/24; Andrzej
Grzesik, On the maximum number of five-cycles in a triangle-free graph, arXiv:1102.0962v3,
https://arxiv.org/abs/1102.0962v3; Hamed Hatami, Jan Hladky, Daniel Kral, Serguei Norine, and
Alexander Razborov, On the number of pentagons in triangle-free graphs, arXiv:1102.1634v4,
https://arxiv.org/abs/1102.1634v4. Moved from `OpenConjectures/GraphTheory/ErdosProblem24`.
-/
public theorem conjecture_holds : conjecture := by
  intro n G hG
  classical
  have htotal : 120 * total G Pattern.score ≤ 120 * 96 * (5 * (n : ℤ)) ^ 5 := by
    rw [← total_symScore]
    calc
      _ ≤ ∑ _ : Fin 5 → Fin (5 * n), (120 * 96 : ℤ) :=
        sum_le_sum fun x _ => score_bound _ (pattern_triangle G hG x)
      _ = _ := by simp; ring
  have hflag := total_flag_nonneg G
  have hcopies := copy_count_le G
  have hscore : total G Pattern.score = total G Pattern.flag +
      30000 * (#{x : Fin 5 → Fin (5 * n) | (pattern G x).cycle} : ℤ) := by
    simp only [total, Pattern.score, sum_add_distrib, ← mul_sum, sum_boole]
  rw [hscore] at htotal
  exact_mod_cast (show (G.copyCount Pentagon : ℤ) ≤ (n : ℤ) ^ 5 by
    have hc : (G.copyCount Pentagon : ℤ) * 10 ≤
        (#{x : Fin 5 → Fin (5 * n) | (pattern G x).cycle} : ℤ) := by exact_mod_cast hcopies
    linarith)

end MathlibExt.GraphTheory.ErdosProblem24Wanted
