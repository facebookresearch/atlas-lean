/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/800.lean` (Formal Conjectures), for the conjecture statement.
Copyright The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Ramsey
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Lattice.Nat
import MathlibExt.Combinatorics.Ramsey
import MathlibExt.Combinatorics.SimpleGraph.GoodmanTriangleBound
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 800

Alon's theorem gives a linear Ramsey bound when the vertices of degree at least three
form an independent set.

Source record `FC-ErdosProblem800`, ported from FormalConjectures
`ErdosProblems/800.lean` and checked against erdosproblems.com/800.
The statement reuses MathlibExt's arbitrary-graph Ramsey API; FC's unused edge-colouring
helper is not ported. The upstream `answer(True)` is dropped. Status:
resolved true (Alon [Al94]).

The proof adapts the nested dependent random choice argument in Fox and Sudakov,
*Dependent Random Choice*, Section 8.2 (https://arxiv.org/abs/0909.3271).
Extend the high-degree vertices to a maximal independent set. The remaining vertices form
singletons and edges, each with at most two neighbors in the independent set. Nested selection
places the independent set so that each singleton or edge can then use an ordered edge in
a common neighborhood.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosProblem800Wanted

open Finset

/-- **Erdős Problem 800 on linear Ramsey numbers.** The proposition asserts that there is a real
number $C > 0$ such that for every natural number $n$ and every simple graph $G$ on $n$ vertices
in which no two adjacent vertices both have degree at least $3$, the diagonal Ramsey number
$R(G, G)$ is at most $Cn$. -/
def conjecture : Prop :=
  ∃ C > (0 : ℝ), ∀ (n : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V = n →
    (∀ u v, G.Adj u v → ¬(3 ≤ G.degree u ∧ 3 ≤ G.degree v)) →
    (SimpleGraph.diagonalGraphRamsey G : ℝ) ≤ C * n

section CommonWitnesses

variable {U W : Type*} [Fintype W] [DecidableEq W]
variable (N : U → Finset W) (threshold : ℕ)

private def bad (A : Finset U) (x : U) : Finset U :=
  A.filter fun y => #(N x ∩ N y) < threshold

private lemma sum_bad_neighbors (A : Finset U) :
    ∑ w : W, ∑ x ∈ A.filter (fun x => w ∈ N x),
      (#(bad N threshold (A.filter (fun x => w ∈ N x)) x) : ℝ) =
    ∑ x ∈ A, ∑ y ∈ bad N threshold A x, (#(N x ∩ N y) : ℝ) := by
  classical
  have h (w : W) (x : U) :
      bad N threshold (A.filter (fun y => w ∈ N y)) x =
        (bad N threshold A x).filter (fun y => w ∈ N y) := by
    ext y
    simp only [bad, mem_filter, and_assoc]
    exact and_congr_right (fun _ => and_comm)
  simp_rw [h, ← sum_boole, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  simp_rw [ite_sum_zero]
  rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  simp_rw [← ite_and, ← mem_inter]
  rw [← sum_filter, filter_mem_eq_inter, univ_inter, sum_const, nsmul_eq_mul, mul_one]

-- Averaging over one common witness gives a large subset with few bad pairs.
-- Discard vertices incident with too many of those pairs to get a uniform bound.
private lemma thin {r c : ℝ} (hr : 0 < r) (hc : 0 < c) [Nonempty W]
    (A : Finset U) (hdegree : ∀ x ∈ A, 4 * r * Fintype.card W ≤ (#(N x) : ℝ))
    (hthreshold : (threshold : ℝ) ≤ 2 * r ^ 3 * Fintype.card W)
    (hbad : ∀ x ∈ A, (#(bad N threshold A x) : ℝ) ≤ c * #A) :
    ∃ B ⊆ A, r * #A ≤ (#B : ℝ) ∧
      ∀ x ∈ B, (#(bad N threshold B x) : ℝ) ≤ (r * c) * #B := by
  classical
  let A' (w : W) := A.filter (fun x => w ∈ N x)
  let X (w : W) : ℝ := #(A' w)
  let Y (w : W) : ℝ := ∑ x ∈ A' w, #(bad N threshold (A' w) x)
  let M : ℝ := Fintype.card W
  have hM : 0 < M := by dsimp [M]; positivity
  have hsumX : M * (4 * r * #A) ≤ ∑ w, X w := by
    have hswap : ∑ w, X w = ∑ x ∈ A, (#(N x) : ℝ) := by
      simp only [X, A', ← sum_boole]
      rw [sum_comm]
      refine sum_congr rfl fun x _ => ?_
      simp only [sum_boole, filter_mem_eq_inter, univ_inter]
    rw [hswap]
    calc
      _ = ∑ _x ∈ A, 4 * r * M := by simp; ring
      _ ≤ _ := sum_le_sum hdegree
  have hsumXsq : M * (4 * r * #A) ^ 2 ≤ ∑ w, X w ^ 2 := by
    have hCS := sq_sum_le_card_mul_sum_sq (s := (univ : Finset W)) (f := X)
    have hsq : (M * (4 * r * #A)) ^ 2 ≤ (∑ w, X w) ^ 2 := by
      gcongr
    apply le_of_mul_le_mul_left _ hM
    simp only [card_univ] at hCS
    nlinarith only [hCS, hsq]
  have hsumY : ∑ w, Y w ≤ M * (2 * r ^ 3 * c * (#A : ℝ) ^ 2) := by
    change (∑ w : W, ∑ x ∈ A' w, (#(bad N threshold (A' w) x) : ℝ)) ≤ _
    rw [sum_bad_neighbors]
    calc
      _ ≤ ∑ x ∈ A, ∑ _y ∈ bad N threshold A x, (threshold : ℝ) := by
        refine sum_le_sum fun x _ => sum_le_sum fun y hy => ?_
        exact_mod_cast (mem_filter.mp hy).2.le
      _ ≤ ∑ _x ∈ A, (c * #A) * (threshold : ℝ) := by
        refine sum_le_sum fun x hx => ?_
        simp only [sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (hbad x hx) (Nat.cast_nonneg _)
      _ ≤ _ := by
        simp only [sum_const, nsmul_eq_mul]
        have hp := mul_le_mul_of_nonneg_left hthreshold
          (show 0 ≤ (#A : ℝ) * (c * #A) by positivity)
        change (threshold : ℝ) ≤ 2 * r ^ 3 * M at hthreshold
        change (#A : ℝ) * (c * #A) * (threshold : ℝ) ≤
          (#A : ℝ) * (c * #A) * (2 * r ^ 3 * M) at hp
        linarith only [hp]
  have hex : ∃ w, 8 * r ^ 3 * c * (#A : ℝ) ^ 2 ≤ r * c * X w ^ 2 - 4 * Y w := by
    by_contra! h
    have hlt := sum_lt_sum_of_nonempty (univ_nonempty (α := W)) (fun w _ => h w)
    simp only [sum_const, nsmul_eq_mul, card_univ, sum_sub_distrib, ← mul_sum] at hlt
    change r * c * (∑ w, X w ^ 2) - 4 * ∑ w, Y w <
      M * (8 * r ^ 3 * c * (#A : ℝ) ^ 2) at hlt
    linarith only [hlt, mul_le_mul_of_nonneg_left hsumXsq (show 0 ≤ r * c by positivity),
      mul_le_mul_of_nonneg_left hsumY (show (0 : ℝ) ≤ 4 by norm_num)]
  obtain ⟨w, hw⟩ := hex
  have hy : 0 ≤ Y w := sum_nonneg fun _ _ => by positivity
  have hx : 0 ≤ X w := by dsimp [X]; positivity
  have hsize : 2 * r * #A ≤ X w := by
    have hsq : (2 * r * #A) ^ 2 ≤ X w ^ 2 := by
      apply le_of_mul_le_mul_left _ (show 0 < r * c by positivity)
      have hnonneg : 0 ≤ 4 * r ^ 3 * c * (#A : ℝ) ^ 2 := by positivity
      linarith only [hnonneg, hw, hy]
    exact (pow_le_pow_iff_left₀ (by positivity) hx (by decide : (2 : ℕ) ≠ 0)).mp hsq
  have hcount : 4 * Y w ≤ r * c * X w ^ 2 := by
    have hnonneg : 0 ≤ 8 * r ^ 3 * c * (#A : ℝ) ^ 2 := by positivity
    linarith only [hw, hnonneg]
  let B := (A' w).filter fun x =>
    (#(bad N threshold (A' w) x) : ℝ) ≤ (r * c / 2) * X w
  have hsub : B ⊆ A' w := filter_subset _ _
  have hhalf : X w ≤ 2 * (#B : ℝ) := by
    by_cases hx0 : X w = 0
    · rw [hx0]; positivity
    let E := A' w \ B
    have he (x : U) (hxE : x ∈ E) :
        (r * c / 2) * X w ≤ (#(bad N threshold (A' w) x) : ℝ) := by
      have h := mem_sdiff.mp hxE
      exact le_of_lt (lt_of_not_ge fun hp => h.2 (mem_filter.mpr ⟨h.1, hp⟩))
    have hE : (#E : ℝ) * ((r * c / 2) * X w) ≤ Y w := by
      calc
        _ = ∑ _x ∈ E, (r * c / 2) * X w := by simp
        _ ≤ ∑ x ∈ E, (#(bad N threshold (A' w) x) : ℝ) := sum_le_sum he
        _ ≤ Y w := sum_le_sum_of_subset_of_nonneg sdiff_subset (fun _ _ _ => by positivity)
    have hcE : 2 * (#E : ℝ) ≤ X w := by
      apply le_of_mul_le_mul_right _ (show 0 < (r * c / 2) * X w by positivity)
      linarith only [hE, hcount]
    have hcard : (#E : ℝ) + #B = X w := by
      dsimp only [E, X]
      exact_mod_cast card_sdiff_add_card_eq_card hsub
    linarith only [hcE, hcard]
  refine ⟨B, hsub.trans (filter_subset _ _), by linarith only [hsize, hhalf], ?_⟩
  intro x hxB
  have hle : (#(bad N threshold B x) : ℝ) ≤ #(bad N threshold (A' w) x) := by
    exact_mod_cast card_le_card (filter_subset_filter _ hsub)
  calc
    _ ≤ (r * c / 2) * X w := hle.trans (mem_filter.mp hxB).2
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ r * c / 2 by positivity)
      linarith only [h]

end CommonWitnesses

section Triangles

open MathlibExt.Combinatorics.SimpleGraph.GoodmanTriangleBound

variable {U : Type*} [Fintype U] [DecidableEq U]

private lemma mono_triangle {k : ℕ}
    (hk : ∀ φ : Finset (Fin k) → Fin 2, ∃ S : Finset (Fin k), S.card = 3 ∧
      ∃ c : Fin 2, ∀ T ∈ S.powersetCard 2, φ T = c)
    (H : SimpleGraph U) [DecidableRel H.Adj] [DecidableRel Hᶜ.Adj]
    (s : Finset U) (hs : #s = k) :
    ∃ t ⊆ s, t ∈ H.cliqueFinset 3 ∪ Hᶜ.cliqueFinset 3 := by
  classical
  let e : Fin k ↪ U := (s.equivFinOfCardEq hs).symm.toEmbedding.trans (Function.Embedding.subtype _)
  let φ (T : Finset (Fin k)) : Fin 2 :=
    if H.IsClique (↑(T.map e) : Set U) then 0 else 1
  obtain ⟨S, hS, c, hc⟩ := hk φ
  refine ⟨S.map e, ?_, ?_⟩
  · intro u hu
    obtain ⟨i, _, rfl⟩ := mem_map.mp hu
    exact ((s.equivFinOfCardEq hs).symm i).2
  have hpair {a b : U} (ha : a ∈ S.map e) (hb : b ∈ S.map e) (hab : a ≠ b) :
      φ (({(mem_map.mp ha).choose, (mem_map.mp hb).choose} : Finset (Fin k))) = c := by
    let i := (mem_map.mp ha).choose
    let j := (mem_map.mp hb).choose
    have hi := (mem_map.mp ha).choose_spec
    have hj := (mem_map.mp hb).choose_spec
    have hij : i ≠ j := fun h => hab (hi.2.symm.trans (congrArg e h |>.trans hj.2))
    exact hc {i, j} (mem_powersetCard.mpr ⟨insert_subset hi.1 (singleton_subset_iff.mpr hj.1),
      by simp [hij]⟩)
  have hcolor {a b : U} (ha : a ∈ S.map e) (hb : b ∈ S.map e) (hab : a ≠ b) :
      (if H.Adj a b then (0 : Fin 2) else 1) = c := by
    have h := hpair ha hb hab
    have hi := (mem_map.mp ha).choose_spec.2
    have hj := (mem_map.mp hb).choose_spec.2
    simpa [φ, map_insert, map_singleton, hi, hj, SimpleGraph.isClique_pair, hab] using h
  rw [mem_union]
  rcases Fin.eq_zero_or_eq_succ c with hc₀ | ⟨i, rfl⟩
  · left
    refine SimpleGraph.mem_cliqueFinset_iff.mpr ⟨?_, by simpa using hS⟩
    intro a ha b hb hab
    have h := hcolor ha hb hab
    simp_all
  · right
    refine SimpleGraph.mem_cliqueFinset_iff.mpr ⟨?_, by simpa using hS⟩
    intro a ha b hb hab
    have h := hcolor ha hb hab
    have hi : i = 0 := Subsingleton.elim _ _
    rw [hi] at h
    rw [SimpleGraph.compl_adj]
    refine ⟨hab, ?_⟩
    intro hadj
    simp [hadj] at h

omit [DecidableEq U] in
private lemma mono_triangle_density {k : ℕ} (hk3 : 3 ≤ k)
    (hk : ∀ φ : Finset (Fin k) → Fin 2, ∃ S : Finset (Fin k), S.card = 3 ∧
      ∃ c : Fin 2, ∀ T ∈ S.powersetCard 2, φ T = c)
    (H : SimpleGraph U) [DecidableRel H.Adj] [DecidableRel Hᶜ.Adj]
    (hU : max 4 k ≤ Fintype.card U) :
    Fintype.card U ^ 3 ≤ (8 * k.choose 3) *
      max #(orderedTriangles H) #(orderedTriangles Hᶜ) := by
  classical
  let m := Fintype.card U
  let tris := H.cliqueFinset 3 ∪ Hᶜ.cliqueFinset 3
  let family (t : Finset U) := ((univ : Finset U).powersetCard k).filter (t ⊆ ·)
  have hcover : (univ : Finset U).powersetCard k ⊆ tris.biUnion family := by
    intro s hs
    obtain ⟨t, ht, ht'⟩ := mono_triangle hk H s (mem_powersetCard.mp hs).2
    exact mem_biUnion.mpr ⟨t, ht', mem_filter.mpr ⟨hs, ht⟩⟩
  have hf (t : Finset U) (ht : t ∈ tris) : #(family t) = (m - 3).choose (k - 3) := by
    have htc : #t = 3 := by
      rcases mem_union.mp ht with h | h <;> exact (SimpleGraph.mem_cliqueFinset_iff.mp h).2
    simpa only [family, htc, card_univ] using
      card_filter_powersetCard_subset t univ k (subset_univ _) (htc ▸ hk3)
  have hcount : m.choose k ≤ #tris * (m - 3).choose (k - 3) := by
    calc
      _ = #((univ : Finset U).powersetCard k) := by simp [m]
      _ ≤ #(tris.biUnion family) := card_le_card hcover
      _ ≤ ∑ t ∈ tris, #(family t) := card_biUnion_le
      _ = _ := by rw [sum_congr rfl hf]; simp
  have hchoose : m.choose 3 ≤ #tris * k.choose 3 := by
    have hm : k ≤ m := (le_max_right _ _).trans hU
    apply Nat.le_of_mul_le_mul_right (c := (m - 3).choose (k - 3)) _
      (Nat.choose_pos (by omega))
    have h := Nat.mul_le_mul_right (k.choose 3) hcount
    rw [Nat.choose_mul hk3] at h
    simpa only [Nat.mul_assoc, Nat.mul_comm ((m - 3).choose (k - 3)) (k.choose 3)] using h
  have hsize : m ^ 3 ≤ 24 * m.choose 3 := by
    have h4 : 4 ≤ m := (le_max_left _ _).trans hU
    have h2 := Nat.choose_succ_right_eq m 1
    have h3 := Nat.choose_succ_right_eq m 2
    simp only [Nat.choose_one_right] at h2
    have heq : 6 * m.choose 3 = m * (m - 1) * (m - 2) := by
      calc
        _ = (m.choose 3 * 3) * 2 := by ring
        _ = (m.choose 2 * 2) * (m - 2) := by rw [h3]; ring
        _ = _ := by rw [h2]
    have hsmall : m ≤ 2 * (m - 1) := by omega
    have hlarge : m ≤ 2 * (m - 2) := by omega
    calc
      _ ≤ m * (2 * (m - 1)) * (2 * (m - 2)) := by
        simpa [pow_succ] using Nat.mul_le_mul (Nat.mul_le_mul_left m hsmall) hlarge
      _ = 4 * (6 * m.choose 3) := by rw [heq]; ring
      _ = _ := by ring
  let q := max #(H.cliqueFinset 3) #(Hᶜ.cliqueFinset 3)
  have htris : #tris ≤ 2 * q := by
    have h₁ : #(H.cliqueFinset 3) ≤ q := le_max_left _ _
    have h₂ : #(Hᶜ.cliqueFinset 3) ≤ q := le_max_right _ _
    have hh := card_union_le (H.cliqueFinset 3) (Hᶜ.cliqueFinset 3)
    change #tris ≤ _
    change #tris ≤ _ at hh
    omega
  calc
    _ = m ^ 3 := rfl
    _ ≤ 24 * m.choose 3 := hsize
    _ ≤ 24 * ((2 * q) * k.choose 3) :=
      Nat.mul_le_mul_left _ (hchoose.trans (Nat.mul_le_mul_right _ htris))
    _ = _ := by
      rw [card_orderedTriangles_eq_six_mul, card_orderedTriangles_eq_six_mul, ← mul_max]
      change _ = _ * (6 * q)
      ring

end Triangles

section Embedding

variable {U W : Type*} [DecidableEq W] [Fintype W] [Nonempty W]

private lemma nested (N : U → Finset W) (threshold D : ℕ) (hD : 1 < D)
    (A₀ : Finset U)
    (hdegree : ∀ x ∈ A₀, 4 * (D : ℝ)⁻¹ * Fintype.card W ≤ (#(N x) : ℝ))
    (hthreshold : (threshold : ℝ) ≤ 2 * ((D : ℝ)⁻¹) ^ 3 * Fintype.card W) :
    ∃ A : ℕ → Finset U, A 0 = A₀ ∧ Antitone A ∧
      (∀ j, #A₀ ≤ D ^ j * #(A j)) ∧
      ∀ j x, x ∈ A j → D ^ j * #(bad N threshold (A j) x) ≤ #(A j) := by
  classical
  let r := (D : ℝ)⁻¹
  have hr : 0 < r := by dsimp [r]; positivity
  let State (j : ℕ) := {A : Finset U // A ⊆ A₀ ∧ r ^ j * #A₀ ≤ (#A : ℝ) ∧
    ∀ x ∈ A, (#(bad N threshold A x) : ℝ) ≤ r ^ j * #A}
  let initial : State 0 := ⟨A₀, Subset.rfl, by simp, fun x _ => by
    simp only [pow_zero, one_mul]
    exact_mod_cast card_filter_le _ _⟩
  have hstep (j : ℕ) (s : State j) : ∃ t : State (j + 1), t.val ⊆ s.val := by
    obtain ⟨B, hBs, hB, hb⟩ := thin N threshold hr (pow_pos hr j) s.val
      (fun x hx => hdegree x (s.property.1 hx)) hthreshold s.property.2.2
    refine ⟨⟨B, hBs.trans s.property.1, ?_, ?_⟩, hBs⟩
    · rw [pow_succ, mul_comm (r ^ j), mul_assoc]
      exact (mul_le_mul_of_nonneg_left s.property.2.1 hr.le).trans hB
    · simpa only [pow_succ, mul_comm (r ^ j) r] using hb
  let S : (j : ℕ) → State j := Nat.rec initial (fun j s => (hstep j s).choose)
  let A (j : ℕ) := (S j).val
  have hform (j : ℕ) : r ^ j = ((D ^ j : ℕ) : ℝ)⁻¹ := by simp [r, inv_pow]
  have hdpos (j : ℕ) : (0 : ℝ) < ((D ^ j : ℕ) : ℝ) := by positivity
  refine ⟨A, rfl, antitone_nat_of_succ_le (fun j => (hstep j (S j)).choose_spec), ?_, ?_⟩
  · intro j
    have h : r ^ j * #A₀ ≤ (#(A j) : ℝ) := (S j).property.2.1
    rw [hform, inv_mul_eq_div] at h
    exact_mod_cast (div_le_iff₀' (hdpos j)).mp h
  · intro j x hx
    have h : (#(bad N threshold (A j) x) : ℝ) ≤ r ^ j * #(A j) :=
      (S j).property.2.2 x hx
    rw [hform, inv_mul_eq_div] at h
    exact_mod_cast (le_div_iff₀' (hdpos j)).mp h

-- Embed in decreasing order of weight. The logarithmic level balances the size
-- of the candidate set against the number of exclusions for each requirement.
private lemma embed_requirements {α : Type*} [Fintype α] [Nonempty U]
    (N : U → Finset W) (threshold D L : ℕ) (hD : 1 < D)
    (A₀ : Finset U) (hA₀ : 4 * D * L ≤ #A₀)
    (hdegree : ∀ x ∈ A₀, 4 * (D : ℝ)⁻¹ * Fintype.card W ≤ (#(N x) : ℝ))
    (hthreshold : (threshold : ℝ) ≤ 2 * ((D : ℝ)⁻¹) ^ 3 * Fintype.card W)
    (R : α → α → Prop) [DecidableRel R] (hR : ∀ ⦃x y⦄, R x y → R y x)
    (weight : α → ℕ) (hpos : ∀ x, 0 < weight x) (hweight : ∑ x, weight x ≤ L)
    (hrows : ∀ x, #(univ.filter (R x)) ≤ weight x) :
    ∃ f : α → U, Function.Injective f ∧ (∀ x, f x ∈ A₀) ∧
      ∀ x y, R x y → threshold ≤ #(N (f x) ∩ N (f y)) := by
  classical
  obtain ⟨A, hzero, hnest, hsize, hbad⟩ := nested N threshold D hD A₀ hdegree hthreshold
  let tier (x : α) := Nat.clog D (2 * weight x)
  have hdiag (x : U) (hx : x ∈ A₀) : threshold ≤ #(N x ∩ N x) := by
    have hinv : (D : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hD.le)
    have hn : 0 ≤ (D : ℝ)⁻¹ := by positivity
    have hsq : ((D : ℝ)⁻¹) ^ 2 ≤ 1 := by simpa using
      (pow_le_pow_left₀ hn hinv 2)
    have hcast := hdegree x hx
    rw [inter_self]
    apply (Nat.cast_le (α := ℝ)).mp
    refine hthreshold.trans (le_trans ?_ hcast)
    have hz := mul_le_mul_of_nonneg_right hsq
      (show 0 ≤ 2 * (D : ℝ)⁻¹ * Fintype.card W by positivity)
    linarith only [hz, show 0 ≤ (D : ℝ)⁻¹ * Fintype.card W by positivity]
  suffices h : ∀ s : Finset α, ∃ f : α → U, Set.InjOn f (s : Set α) ∧
      (∀ x ∈ s, f x ∈ A (tier x)) ∧
      ∀ x ∈ s, ∀ y ∈ s, R x y → threshold ≤ #(N (f x) ∩ N (f y)) by
    obtain ⟨f, hi, hf, hreq⟩ := h univ
    refine ⟨f, fun a b => hi (mem_univ a) (mem_univ b),
      fun x => hzero ▸ hnest (Nat.zero_le _) (hf x (mem_univ x)), ?_⟩
    exact fun x y => hreq x (mem_univ x) y (mem_univ y)
  intro s
  induction s using Finset.strongInduction with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨fun _ => Classical.arbitrary U, by simp, by simp, by simp⟩
    obtain ⟨x, hx, hmin⟩ := exists_min_image s weight hs
    let t := s.erase x
    have hts : t ⊂ s := erase_ssubset hx
    obtain ⟨f, hfi, hfA, hfR⟩ := ih t hts
    let j := tier x
    have hjlo : 2 * weight x ≤ D ^ j := Nat.le_pow_clog hD _
    have hjhi : D ^ j ≤ 2 * D * weight x := by
      have hpos' : 1 < 2 * weight x := by have := hpos x; omega
      have hj : 0 < j := Nat.clog_pos hD hpos'
      have hp := Nat.pow_pred_clog_lt_self D hpos'
      change D ^ (j - 1) < 2 * weight x at hp
      have heq : j = (j - 1) + 1 := by omega
      calc
        _ = D ^ (j - 1) * D := by nth_rw 1 [heq]; rw [pow_succ]
        _ ≤ (2 * weight x) * D := Nat.mul_le_mul_right _ hp.le
        _ = _ := by ring
    have hbudget : #s * weight x ≤ L := by
      calc
        _ = ∑ _y ∈ s, weight x := by simp
        _ ≤ ∑ y ∈ s, weight y := sum_le_sum hmin
        _ ≤ _ := (sum_le_sum_of_subset (subset_univ _)).trans hweight
    have hspace : 2 * #s ≤ #(A j) := by
      have h₁ := hsize j
      apply Nat.le_of_mul_le_mul_right (c := 2 * D * weight x) _ (Nat.mul_pos (by omega) (hpos x))
      calc
        _ = (4 * D) * (#s * weight x) := by ring
        _ ≤ (4 * D) * L := Nat.mul_le_mul_left _ hbudget
        _ ≤ #A₀ := hA₀
        _ ≤ D ^ j * #(A j) := h₁
        _ ≤ _ := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hjhi
    let Q := t.filter (R x)
    let F := Q.biUnion (fun y => bad N threshold (A j) (f y))
    have hQ : #Q ≤ weight x :=
      (card_le_card (filter_subset_filter _ (subset_univ _))).trans (hrows x)
    have hF : 2 * #F ≤ #(A j) := by
      have hsum : D ^ j * #F ≤ #Q * #(A j) := by
        calc
          _ ≤ D ^ j * ∑ y ∈ Q, #(bad N threshold (A j) (f y)) :=
            Nat.mul_le_mul_left _ card_biUnion_le
          _ = ∑ y ∈ Q, D ^ j * #(bad N threshold (A j) (f y)) := by rw [mul_sum]
          _ ≤ ∑ _y ∈ Q, #(A j) := by
            apply sum_le_sum
            intro y hy
            have hyt := (mem_filter.mp hy).1
            have hxy : j ≤ tier y := Nat.clog_mono_right _ (by
              exact Nat.mul_le_mul_left _ (hmin y (hts.le hyt)))
            exact hbad j (f y) (hnest hxy (hfA y hyt))
          _ = _ := by simp
      have hp := Nat.mul_le_mul_right (#(A j)) ((Nat.mul_le_mul_left 2 hQ).trans hjlo)
      apply Nat.le_of_mul_le_mul_left (c := D ^ j) _ (Nat.pow_pos (by omega))
      calc
        _ = 2 * (D ^ j * #F) := by ring
        _ ≤ 2 * (#Q * #(A j)) := Nat.mul_le_mul_left _ hsum
        _ = (2 * #Q) * #(A j) := by ring
        _ ≤ _ := hp
    have himage : #(t.image f) < #s := lt_of_le_of_lt card_image_le (card_lt_card hts)
    have hforbidden : #(t.image f ∪ F) < #(A j) := by
      have h := card_union_le (t.image f) F
      omega
    obtain ⟨v, hvJ, hv⟩ : ∃ v ∈ A j, v ∉ t.image f ∪ F := by
      by_contra! h
      exact (not_le_of_gt hforbidden) (card_le_card h)
    have hvold : v ∉ t.image f := fun h => hv (mem_union_left _ h)
    have hvnew : v ∉ F := fun h => hv (mem_union_right _ h)
    have hedge (y : α) (hy : y ∈ t) (hxy : R x y) :
        threshold ≤ #(N v ∩ N (f y)) := by
      rw [inter_comm]
      exact le_of_not_gt (fun h => hvnew
        (mem_biUnion.mpr ⟨y, mem_filter.mpr ⟨hy, hxy⟩, mem_filter.mpr ⟨hvJ, h⟩⟩))
    have hothers {y : α} (hy : y ∈ s) (hyx : y ≠ x) : y ∈ t := mem_erase.mpr ⟨hyx, hy⟩
    refine ⟨Function.update f x v, ?_, ?_, ?_⟩
    · intro a ha b hb hab
      by_cases hax : a = x <;> by_cases hbx : b = x
      · exact hax.trans hbx.symm
      · subst a
        rw [Function.update_self, Function.update_of_ne hbx] at hab
        exact (hvold (mem_image.mpr ⟨b, hothers hb hbx, hab.symm⟩)).elim
      · subst b
        rw [Function.update_of_ne hax, Function.update_self] at hab
        exact (hvold (mem_image.mpr ⟨a, hothers ha hax, hab⟩)).elim
      · rw [Function.update_of_ne hax, Function.update_of_ne hbx] at hab
        exact hfi (hothers ha hax) (hothers hb hbx) hab
    · intro y hy
      by_cases hyx : y = x
      · subst y; simpa using hvJ
      · rw [Function.update_of_ne hyx]
        exact hfA y (hothers hy hyx)
    · intro a ha b hb hab
      by_cases hax : a = x <;> by_cases hbx : b = x
      · subst a; subst b
        simp only [Function.update_self]
        exact hdiag v (hzero ▸ hnest (Nat.zero_le _) hvJ)
      · subst a
        simpa [Function.update_of_ne hbx] using hedge b (hothers hb hbx) hab
      · subst b
        simpa [Function.update_of_ne hax, inter_comm] using hedge a (hothers ha hax) (hR hab)
      · rw [Function.update_of_ne hax, Function.update_of_ne hbx]
        exact hfR a (hothers ha hax) b (hothers hb hbx) hab

end Embedding

section Blocks

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
private lemma independent_cover
    (hG : ∀ x y, G.Adj x y → ¬(3 ≤ G.degree x ∧ 3 ≤ G.degree y)) :
    ∃ I : Finset V, (∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y) ∧
      (∀ x ∉ I, G.degree x ≤ 2) ∧ ∀ x ∉ I, ∃ i ∈ I, G.Adj x i := by
  classical
  let S := (univ : Finset V).filter fun x => 3 ≤ G.degree x
  let P (I : Finset V) := S ⊆ I ∧ ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y
  let F := (univ : Finset V).powerset.filter P
  have hS : S ∈ F := by
    refine mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), Subset.rfl, ?_⟩
    intro x hx y hy hxy
    exact hG x y hxy ⟨(mem_filter.mp hx).2, (mem_filter.mp hy).2⟩
  obtain ⟨I, hIF, hmax⟩ := exists_max_image F card ⟨S, hS⟩
  have hI := (mem_filter.mp hIF).2
  refine ⟨I, hI.2, ?_, ?_⟩
  · intro x hx
    exact Nat.lt_succ_iff.mp (lt_of_not_ge fun h => hx (hI.1 (mem_filter.mpr ⟨mem_univ _, h⟩)))
  · intro x hx
    by_contra! h
    have hI' : insert x I ∈ F := by
      refine mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), ?_, ?_⟩
      · exact hI.1.trans (subset_insert _ _)
      · intro y hy z hz
        by_cases hyx : y = x <;> by_cases hzx : z = x
        · subst y; subst z; exact G.irrefl
        · subst y; exact h z ((mem_insert.mp hz).resolve_left hzx)
        · subst z
          exact fun he => h y ((mem_insert.mp hy).resolve_left hyx) he.symm
        · exact hI.2 y ((mem_insert.mp hy).resolve_left hyx) z ((mem_insert.mp hz).resolve_left hzx)
    have hh := hmax _ hI'
    simp [hx] at hh

private def lowNeighbors (I : Finset V) (x : V) : Finset V := G.neighborFinset x \ I

private def highNeighbors (I : Finset V) (x : V) : Finset V := G.neighborFinset x ∩ I

private lemma neighbor_sizes (I : Finset V) (x : V) :
    #(highNeighbors G I x) + #(lowNeighbors G I x) = G.degree x := by
  rw [← G.card_neighborFinset_eq_degree]
  exact Finset.card_inter_add_card_sdiff _ _

private lemma low_neighbor_count (I : Finset V)
    (hdeg : ∀ x ∉ I, G.degree x ≤ 2) (hdom : ∀ x ∉ I, ∃ i ∈ I, G.Adj x i)
    {x : V} (hx : x ∉ I) : #(lowNeighbors G I x) ≤ 1 := by
  obtain ⟨i, hi, hai⟩ := hdom x hx
  have hpos : 0 < #(highNeighbors G I x) :=
    card_pos.mpr ⟨i, mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hai, hi⟩⟩
  have hd := hdeg x hx
  have hh := neighbor_sizes G I x
  omega

private def block (I : Finset V) (x : V) : Finset V := insert x (lowNeighbors G I x)

private lemma mem_block (I : Finset V) {x y : V} :
    y ∈ block G I x ↔ y = x ∨ G.Adj x y ∧ y ∉ I := by
  simp [block, lowNeighbors]

private lemma block_eq_of_mem (I : Finset V)
    (hdeg : ∀ x ∉ I, G.degree x ≤ 2) (hdom : ∀ x ∉ I, ∃ i ∈ I, G.Adj x i)
    {x y : V} (hx : x ∉ I) (hy : y ∈ block G I x) : block G I y = block G I x := by
  rcases (mem_block G I).mp hy with rfl | ⟨hxy, hy⟩
  · rfl
  have hsingle (x y : V) (hx : x ∉ I) (hy : y ∉ I) (hxy : G.Adj x y) :
      lowNeighbors G I x = {y} := by
    have hyN : y ∈ lowNeighbors G I x := mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr hxy, hy⟩
    symm
    refine eq_of_subset_of_card_le (singleton_subset_iff.mpr hyN) ?_
    simpa using low_neighbor_count G I hdeg hdom hx
  simp only [block, hsingle x y hx hy hxy, hsingle y x hy hx hxy.symm, pair_comm]

private lemma block_size (I : Finset V)
    (hdeg : ∀ x ∉ I, G.degree x ≤ 2) (hdom : ∀ x ∉ I, ∃ i ∈ I, G.Adj x i)
    {x : V} (hx : x ∉ I) : #(block G I x) ≤ 2 := by
  exact (card_insert_le _ _).trans (Nat.succ_le_succ (low_neighbor_count G I hdeg hdom hx))

private lemma block_requirements_size (I : Finset V)
    (hdeg : ∀ x ∉ I, G.degree x ≤ 2) (hdom : ∀ x ∉ I, ∃ i ∈ I, G.Adj x i)
    {x : V} (hx : x ∉ I) : #((block G I x).biUnion (highNeighbors G I)) ≤ 2 := by
  classical
  by_cases h : #(block G I x) ≤ 1
  · have hxB : x ∈ block G I x := mem_insert_self _ _
    have heq : block G I x = {x} := by
      symm
      refine eq_of_subset_of_card_le (singleton_subset_iff.mpr hxB) ?_
      simpa using h
    rw [heq, singleton_biUnion]
    have ha := neighbor_sizes G I x
    have hb := hdeg x hx
    omega
  · refine card_biUnion_le.trans ?_
    have hh : ∀ y ∈ block G I x, #(highNeighbors G I y) ≤ 1 := by
      intro y hy
      have hyI : y ∉ I := ((mem_block G I).mp hy).elim (fun h => h.symm ▸ hx) And.right
      have heq := block_eq_of_mem G I hdeg hdom hx hy
      have hsmall : 1 < #(block G I y) := by rw [heq]; omega
      have hcard := card_insert_le y (lowNeighbors G I y)
      have hsum := neighbor_sizes G I y
      have hdy := hdeg y hyI
      change #(block G I y) ≤ _ at hcard
      omega
    calc
      _ ≤ ∑ _y ∈ block G I x, 1 := sum_le_sum hh
      _ ≤ 2 := by simpa using block_size G I hdeg hdom hx

end Blocks

section EdgeReservoirs

variable {U B : Type*} [Fintype U] [Fintype B] [Nonempty U] [DecidableEq U]

private def endpoints (e : U × U) : Finset U := {e.1, e.2}

private lemma choose_edges (n : ℕ) (occupied : Finset U) (hoccupied : #occupied ≤ n)
    (hB : Fintype.card B ≤ n) (C : B → Finset (U × U))
    (hC : ∀ b, 6 * n * Fintype.card U < #(C b)) :
    ∃ g : B → U × U, (∀ b, g b ∈ C b) ∧
      (∀ b, Disjoint (endpoints (g b)) occupied) ∧
      ∀ b b', b ≠ b' → Disjoint (endpoints (g b)) (endpoints (g b')) := by
  classical
  suffices h : ∀ s : Finset B, ∃ g : B → U × U, (∀ b ∈ s, g b ∈ C b) ∧
      (∀ b ∈ s, Disjoint (endpoints (g b)) occupied) ∧
      ∀ b ∈ s, ∀ b' ∈ s, b ≠ b' → Disjoint (endpoints (g b)) (endpoints (g b')) by
    obtain ⟨g, hg, hd, hpair⟩ := h univ
    exact ⟨g, fun b => hg b (mem_univ _), fun b => hd b (mem_univ _),
      fun b b' => hpair b (mem_univ _) b' (mem_univ _)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => Classical.arbitrary _, by simp, by simp, by simp⟩
  | @insert b s hb ih =>
    obtain ⟨g, hg, hd, hpair⟩ := ih
    let used := occupied ∪ s.biUnion (fun b => endpoints (g b))
    have hsize : #used ≤ 3 * n := by
      have hs : #s ≤ n := (card_le_univ _).trans hB
      have hsum : #(s.biUnion (fun b => endpoints (g b))) ≤ #s * 2 := by
        refine card_biUnion_le.trans ?_
        calc
          _ ≤ ∑ _b ∈ s, 2 := sum_le_sum fun b _ => by exact card_le_two
          _ = _ := by simp
      have hu := card_union_le occupied (s.biUnion (fun b => endpoints (g b)))
      change #used ≤ _ at hu
      omega
    let bad := (used ×ˢ (univ : Finset U)) ∪ ((univ : Finset U) ×ˢ used)
    have hbad : #bad ≤ 6 * n * Fintype.card U := by
      refine (card_union_le _ _).trans ?_
      simp only [card_product, card_univ]
      rw [mul_comm (Fintype.card U), ← two_mul]
      calc
        _ = (2 * #used) * Fintype.card U := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    obtain ⟨e, he, he'⟩ : ∃ e ∈ C b, e ∉ bad := by
      by_contra! h
      exact (not_le_of_gt ((hbad.trans_lt (hC b)))) (card_le_card h)
    have hdis : Disjoint (endpoints e) used := by
      rw [Finset.disjoint_left]
      intro v hv hv'
      rcases (show v = e.1 ∨ v = e.2 by simpa [endpoints] using hv) with rfl | rfl
      · exact he' (mem_union_left _ (mem_product.mpr ⟨hv', mem_univ _⟩))
      · exact he' (mem_union_right _ (mem_product.mpr ⟨mem_univ _, hv'⟩))
    have hdisPart (b' : B) (hb' : b' ∈ s) : Disjoint (endpoints e) (endpoints (g b')) :=
      hdis.mono_right fun v hv => mem_union_right _ (mem_biUnion.mpr ⟨b', hb', hv⟩)
    have hne_s {a : B} (ha : a ∈ s) : a ≠ b := fun h => hb (h ▸ ha)
    refine ⟨Function.update g b e, ?_, ?_, ?_⟩
    · intro a ha
      rcases mem_insert.mp ha with rfl | ha
      · simpa using he
      · simpa [Function.update_of_ne (hne_s ha)] using hg a ha
    · intro a ha
      rcases mem_insert.mp ha with rfl | ha
      · simpa using hdis.mono_right (subset_union_left (s₂ := s.biUnion fun b => endpoints (g b)))
      · simpa [Function.update_of_ne (hne_s ha)] using hd a ha
    · intro a ha a' ha' hne
      by_cases ha₀ : a = b <;> by_cases ha₁ : a' = b
      · exact (hne (ha₀.trans ha₁.symm)).elim
      · subst a
        simpa [Function.update_of_ne ha₁] using hdisPart a' ((mem_insert.mp ha').resolve_left ha₁)
      · subst a'
        simpa [Function.update_of_ne ha₀] using
          (hdisPart a ((mem_insert.mp ha).resolve_left ha₀)).symm
      · simpa [Function.update_of_ne ha₀, Function.update_of_ne ha₁] using
          hpair a ((mem_insert.mp ha).resolve_left ha₀)
            a' ((mem_insert.mp ha').resolve_left ha₁) hne

end EdgeReservoirs

section DenseHost

open MathlibExt.Combinatorics.SimpleGraph.GoodmanTriangleBound

variable {U : Type*} [Fintype U]
variable (H : SimpleGraph U) [DecidableRel H.Adj]

private def witnesses (x : U) : Finset (U × U) :=
  univ.filter (fun (y, z) => H.Adj x y ∧ H.Adj y z ∧ H.Adj x z)

private lemma sum_witnesses : ∑ x, #(witnesses H x) = #(orderedTriangles H) := by
  classical
  rw [orderedTriangles, ← univ_product_univ, card_filter, sum_product]
  refine sum_congr rfl fun x _ => ?_
  rw [witnesses, card_filter]

private lemma dense_vertices (D : ℕ) (hD : 0 < D) (hU : 0 < Fintype.card U)
    (hdense : 8 * Fintype.card U ^ 3 ≤ D * #(orderedTriangles H)) :
    ∃ A : Finset U, 4 * Fintype.card U ≤ D * #A ∧
      ∀ x ∈ A, 4 * (D : ℝ)⁻¹ * Fintype.card (U × U) ≤ (#(witnesses H x) : ℝ) := by
  classical
  let m := Fintype.card U
  let A := univ.filter (fun x => 4 * m ^ 2 ≤ D * #(witnesses H x))
  have hsum : D * #(orderedTriangles H) ≤ #A * (D * m ^ 2) + m * (4 * m ^ 2) := by
    rw [← sum_witnesses, mul_sum]
    calc
      _ = (∑ x ∈ A, D * #(witnesses H x)) +
          ∑ x ∈ univ \ A, D * #(witnesses H x) := by
        rw [add_comm, sum_sdiff (subset_univ _)]
      _ ≤ _ := by
        apply Nat.add_le_add
        · calc
            _ ≤ ∑ _x ∈ A, D * m ^ 2 := by
              apply sum_le_sum
              intro x _
              apply Nat.mul_le_mul_left
              simpa only [m, Fintype.card_prod, pow_two] using card_le_univ (witnesses H x)
            _ = _ := by simp
        · calc
            _ ≤ ∑ _x ∈ univ \ A, 4 * m ^ 2 :=
              sum_le_sum fun x hx => le_of_lt (lt_of_not_ge
                fun h => (mem_sdiff.mp hx).2 (mem_filter.mpr ⟨mem_univ _, h⟩))
            _ = #(univ \ A) * (4 * m ^ 2) := by simp
            _ ≤ _ := Nat.mul_le_mul_right _ (card_le_univ _)
  refine ⟨A, ?_, ?_⟩
  · apply Nat.le_of_mul_le_mul_right (c := m ^ 2) _ (Nat.pow_pos hU)
    have h := hdense.trans hsum
    change 8 * m ^ 3 ≤ _ at h
    calc
      _ = 4 * m ^ 3 := by ring
      _ ≤ D * #A * m ^ 2 := by
        have h₁ : 8 * m ^ 3 = 4 * m ^ 3 + 4 * m ^ 3 := by ring
        have h₂ : #A * (D * m ^ 2) + m * (4 * m ^ 2) =
            D * #A * m ^ 2 + 4 * m ^ 3 := by ring
        omega
  · intro x hx
    have h := (mem_filter.mp hx).2
    have hcast : (4 : ℝ) * (m : ℝ) ^ 2 ≤ D * (#(witnesses H x) : ℝ) := by exact_mod_cast h
    have hd : (0 : ℝ) < D := by exact_mod_cast hD
    rw [Fintype.card_prod]
    push_cast
    have hle := (div_le_iff₀ hd).mpr (by simpa only [mul_comm (D : ℝ)] using hcast)
    change 4 * (D : ℝ)⁻¹ * ((m : ℝ) * (m : ℝ)) ≤ _
    simpa only [pow_two, div_eq_mul_inv, mul_right_comm (4 : ℝ), mul_assoc,
      mul_comm (D : ℝ)⁻¹] using hle

end DenseHost

section Assemble

variable {V U : Type*} [Fintype V] [Fintype U] [Nonempty U]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph U) [DecidableRel H.Adj]

private lemma nonempty_card_le_two {α : Type*} [DecidableEq α] {s : Finset α}
    (h : s.Nonempty) (h₂ : #s ≤ 2) : ∃ a b, s = {a, b} := by
  by_cases h₁ : #s = 1
  · obtain ⟨a, rfl⟩ := card_eq_one.mp h₁
    exact ⟨a, a, by simp⟩
  · have he : #s = 2 := by have := h.card_pos; omega
    obtain ⟨a, b, _, hab⟩ := card_eq_two.mp he
    exact ⟨a, b, hab⟩

private lemma demand_weights {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (P : β → Finset α) (hP : ∀ b, #(P b) ≤ 2) :
    ∃ w : α → ℕ, (∀ x, 0 < w x) ∧ (∑ x, w x) ≤ Fintype.card α + 4 * Fintype.card β ∧
      ∀ x, #((univ : Finset α).filter (fun y => ∃ b, x ∈ P b ∧ y ∈ P b)) ≤ w x := by
  classical
  let w (x : α) := 1 + ∑ b ∈ univ.filter (fun b => x ∈ P b), #(P b)
  refine ⟨w, fun x => by dsimp [w]; omega, ?_, ?_⟩
  · simp only [w, sum_add_distrib, sum_const, smul_eq_mul, mul_one, card_univ]
    apply Nat.add_le_add_left
    simp_rw [sum_filter]
    rw [sum_comm]
    calc
      _ = ∑ b, #(P b) * #(P b) := by
        apply sum_congr rfl
        intro b _
        rw [← sum_filter, filter_mem_eq_inter, univ_inter, sum_const, smul_eq_mul]
      _ ≤ ∑ _b : β, 4 := sum_le_sum fun b _ => Nat.mul_le_mul (hP b) (hP b)
      _ = _ := by simp [Nat.mul_comm]
  · intro x
    have heq : univ.filter (fun y => ∃ b, x ∈ P b ∧ y ∈ P b) =
        (univ.filter (fun b => x ∈ P b)).biUnion P := by
      ext y
      simp [mem_biUnion]
    rw [heq]
    exact card_biUnion_le.trans (by dsimp [w]; omega)

private lemma contained_of_dense_vertices (n D : ℕ) (hD : 1 < D)
    (hn : Fintype.card V = n)
    (hG : ∀ x y, G.Adj x y → ¬(3 ≤ G.degree x ∧ 3 ≤ G.degree y))
    (A : Finset U) (hA : 4 * D * (5 * n) ≤ #A)
    (hdegree : ∀ x ∈ A, 4 * (D : ℝ)⁻¹ * Fintype.card (U × U) ≤ (#(witnesses H x) : ℝ))
    (hthreshold : ((6 * n * Fintype.card U + 1 : ℕ) : ℝ) ≤
      2 * ((D : ℝ)⁻¹) ^ 3 * Fintype.card (U × U)) :
    G.IsContained H := by
  classical
  obtain ⟨I, hind, hdeg, hdom⟩ := independent_cover G hG
  let low := (univ : Finset V) \ I
  let blocks := low.image (block G I)
  let Block := ↥blocks
  let blockOf (x : V) (hx : x ∉ I) : Block :=
    ⟨block G I x, mem_image_of_mem _ (mem_sdiff.mpr ⟨mem_univ _, hx⟩)⟩
  have mem_blockOf (x : V) (hx : x ∉ I) : x ∈ (blockOf x hx).val := mem_insert_self _ _
  have mem_block_low (b : Block) (x : V) (hx : x ∈ b.val) : x ∉ I := by
    obtain ⟨u, hu, he⟩ := mem_image.mp b.property
    rw [← he] at hx
    exact ((mem_block G I).mp hx).elim
      (fun h => h.symm ▸ (mem_sdiff.mp hu).2) And.right
  have block_self (b : Block) (x : V) (hx : x ∈ b.val) :
      blockOf x (mem_block_low b x hx) = b := by
    obtain ⟨u, hu, he⟩ := mem_image.mp b.property
    apply Subtype.ext
    have hxu : x ∈ block G I u := he.symm ▸ hx
    exact (block_eq_of_mem G I hdeg hdom (mem_sdiff.mp hu).2 hxu).trans he
  have hblocks : Fintype.card Block ≤ n := by
    rw [Fintype.card_coe, ← hn]
    exact card_image_le.trans (card_le_univ _)
  have hI : Fintype.card ↥I ≤ n := by
    rw [Fintype.card_coe, ← hn]
    exact card_le_univ _
  let P (b : Block) : Finset ↥I := (b.val.biUnion (highNeighbors G I)).subtype (· ∈ I)
  have hP (b : Block) : #(P b) ≤ 2 := by
    obtain ⟨u, hu, he⟩ := mem_image.mp b.property
    have h := block_requirements_size G I hdeg hdom (mem_sdiff.mp hu).2
    rw [he] at h
    exact (card_subtype _ _).le.trans ((card_filter_le _ _).trans h)
  have hP_nonempty (b : Block) : (P b).Nonempty := by
    obtain ⟨u, hu, he⟩ := mem_image.mp b.property
    obtain ⟨i, hi, hui⟩ := hdom u (mem_sdiff.mp hu).2
    have hub : u ∈ b.val := he ▸ (mem_insert_self _ _ : u ∈ block G I u)
    refine ⟨⟨i, hi⟩, mem_subtype.mpr (mem_biUnion.mpr ⟨u, hub, ?_⟩)⟩
    exact mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hui, hi⟩
  let R (x y : ↥I) := ∃ b, x ∈ P b ∧ y ∈ P b
  obtain ⟨weight, hpos, hsum, hrows⟩ := demand_weights P hP
  have hweight : ∑ x, weight x ≤ 5 * n := by omega
  let T := 6 * n * Fintype.card U + 1
  have hsym : ∀ ⦃x y : ↥I⦄, R x y → R y x := by
    rintro x y ⟨b, hx, hy⟩
    exact ⟨b, hy, hx⟩
  obtain ⟨f, hfinj, _, hcommon⟩ :=
    embed_requirements (witnesses H) T D (5 * n) hD A hA hdegree hthreshold R
      hsym weight hpos hweight hrows
  let C (b : Block) : Finset (U × U) :=
    univ.filter fun e => H.Adj e.1 e.2 ∧ ∀ i ∈ P b, H.Adj (f i) e.1 ∧ H.Adj (f i) e.2
  have hC (b : Block) : T ≤ #(C b) := by
    obtain ⟨i, j, hij⟩ := nonempty_card_le_two (hP_nonempty b) (hP b)
    have hR : R i j := ⟨b, by simp [hij], by simp [hij]⟩
    refine (hcommon i j hR).trans (card_le_card ?_)
    intro e he
    have hi := (mem_filter.mp (mem_inter.mp he).1).2
    have hj := (mem_filter.mp (mem_inter.mp he).2).2
    refine mem_filter.mpr ⟨mem_univ _, hi.2.1, ?_⟩
    intro x hx
    rw [hij, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨hi.1, hi.2.2⟩
    · exact ⟨hj.1, hj.2.2⟩
  let occupied : Finset U := univ.image f
  have hoccupied : #occupied ≤ n := (card_image_le.trans (card_le_univ _)).trans hI
  obtain ⟨g, hg, hfree, hsplit⟩ := choose_edges n occupied hoccupied hblocks C (fun b => hC b)
  have hgdata (b : Block) : H.Adj (g b).1 (g b).2 ∧
      ∀ i ∈ P b, H.Adj (f i) (g b).1 ∧ H.Adj (f i) (g b).2 :=
    (mem_filter.mp (hg b)).2
  have hsmall (b : Block) : Fintype.card ↥b.val ≤ Fintype.card (Fin 2) := by
    obtain ⟨u, hu, he⟩ := mem_image.mp b.property
    rw [Fintype.card_coe, Fintype.card_fin, ← he]
    exact block_size G I hdeg hdom (mem_sdiff.mp hu).2
  let label (b : Block) : b.val ↪ Fin 2 :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (hsmall b))
  let place (b : Block) (v : b.val) : U :=
    if label b v = 0 then (g b).1 else (g b).2
  have place_congr (v : V) {b b' : Block} (h : b = b')
      (hv : v ∈ b.val) (hv' : v ∈ b'.val) : place b ⟨v, hv⟩ = place b' ⟨v, hv'⟩ := by
    subst b'
    rfl
  have hplace_mem (b : Block) (v : b.val) : place b v ∈ endpoints (g b) := by
    by_cases hv : label b v = 0 <;> simp [place, hv, endpoints]
  have hplace_inj (b : Block) : Function.Injective (place b) := by
    intro v w heq
    apply (label b).injective
    by_cases hv : label b v = 0 <;> by_cases hw : label b w = 0
    · exact hv.trans hw.symm
    · exact ((hgdata b).1.ne (by simpa [place, hv, hw] using heq)).elim
    · exact ((hgdata b).1.ne (by simpa [place, hv, hw] using heq.symm)).elim
    · exact Fin.ext (by
        have hv' := Fin.pos_iff_ne_zero.mpr hv
        have hw' := Fin.pos_iff_ne_zero.mpr hw
        omega)
  have hplace_edge (b : Block) {v w : b.val} (hne : v ≠ w) :
      H.Adj (place b v) (place b w) := by
    have hneq : place b v ≠ place b w := fun h => hne (hplace_inj b h)
    by_cases hv : label b v = 0 <;> by_cases hw : label b w = 0
    · simp [place, hv, hw] at hneq
    · simpa [place, hv, hw] using (hgdata b).1
    · simpa [place, hv, hw] using (hgdata b).1.symm
    · simp [place, hv, hw] at hneq
  let lowImage (v : V) (hv : v ∉ I) := place (blockOf v hv) ⟨v, mem_blockOf v hv⟩
  have lowImage_mem (v : V) (hv : v ∉ I) :
      lowImage v hv ∈ endpoints (g (blockOf v hv)) :=
    hplace_mem (blockOf v hv) ⟨v, mem_blockOf v hv⟩
  have high_low_edge (i : ↥I) (v : V) (hv : v ∉ I) (ha : G.Adj i.val v) :
      H.Adj (f i) (lowImage v hv) := by
    have hi : i ∈ P (blockOf v hv) := mem_subtype.mpr
      (mem_biUnion.mpr ⟨v, mem_blockOf v hv,
        mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha.symm, i.property⟩⟩)
    have hh := (hgdata (blockOf v hv)).2 i hi
    rcases (show lowImage v hv = (g (blockOf v hv)).1 ∨
        lowImage v hv = (g (blockOf v hv)).2 by
      simpa [endpoints] using lowImage_mem v hv)
      with h | h
    · rw [h]; exact hh.1
    · rw [h]; exact hh.2
  have hlow_inj {v w : V} (hv : v ∉ I) (hw : w ∉ I)
      (he : lowImage v hv = lowImage w hw) : v = w := by
    by_cases hb : blockOf v hv = blockOf w hw
    · let b := blockOf v hv
      have hwb : w ∈ b.val := by
        change w ∈ (blockOf v hv).val
        rw [hb]
        exact mem_blockOf w hw
      have hh : place b ⟨v, mem_blockOf v hv⟩ = place b ⟨w, hwb⟩ :=
        he.trans (place_congr w hb.symm (mem_blockOf w hw) hwb)
      exact congrArg Subtype.val (hplace_inj b hh)
    · have hm := lowImage_mem w hw
      rw [← he] at hm
      exact (Finset.disjoint_left.mp (hsplit _ _ hb) (lowImage_mem v hv) hm).elim
  have hlow_edge {v w : V} (hv : v ∉ I) (hw : w ∉ I) (ha : G.Adj v w) :
      H.Adj (lowImage v hv) (lowImage w hw) := by
    have hwb : w ∈ (blockOf v hv).val := (mem_block G I).mpr (Or.inr ⟨ha, hw⟩)
    have hb := block_self (blockOf v hv) w hwb
    have he : lowImage w hw = place (blockOf v hv) ⟨w, hwb⟩ :=
      place_congr w hb (mem_blockOf w hw) hwb
    rw [he]
    exact hplace_edge _ (fun h => ha.ne (congrArg Subtype.val h))
  have hcross_inj (x y : V) (hx : x ∈ I) (hy : y ∉ I) :
      f ⟨x, hx⟩ ≠ lowImage y hy := by
    intro he
    have hm : f ⟨x, hx⟩ ∈ occupied := mem_image_of_mem f (mem_univ _)
    rw [he] at hm
    exact Finset.disjoint_left.mp (hfree (blockOf y hy)) (lowImage_mem y hy) hm
  let F (v : V) : U := if hv : v ∈ I then f ⟨v, hv⟩ else lowImage v hv
  refine ⟨⟨⟨F, ?_⟩, ?_⟩⟩
  · intro x y ha
    by_cases hx : x ∈ I <;> by_cases hy : y ∈ I
    · exact (hind x hx y hy ha).elim
    · simpa [F, hx, hy] using high_low_edge ⟨x, hx⟩ y hy ha
    · simpa [F, hx, hy] using (high_low_edge ⟨y, hy⟩ x hx ha.symm).symm
    · simpa [F, hx, hy] using hlow_edge hx hy ha
  · intro x y he
    by_cases hx : x ∈ I <;> by_cases hy : y ∈ I
    · exact congrArg Subtype.val (hfinj (by simpa [F, hx, hy] using he))
    · exact (hcross_inj x y hx hy (by simpa [F, hx, hy] using he)).elim
    · exact (hcross_inj y x hy hx (by simpa [F, hx, hy] using he.symm)).elim
    · exact hlow_inj hx hy (by simpa [F, hx, hy] using he)

end Assemble

open MathlibExt.Combinatorics.SimpleGraph.GoodmanTriangleBound in
/--
**Alon's theorem on linear Ramsey numbers.** There is a real number $C > 0$ such that for every
natural number $n$ and every simple graph $G$ on $n$ vertices in which no two adjacent vertices
both have degree at least $3$, the diagonal Ramsey number $R(G, G)$ is at most $Cn$.

This answers Erdős Problem 800 affirmatively.

Source: Noga Alon, Subdivided graphs have linear
Ramsey numbers, Journal of Graph Theory 18 (1994), 343–347,
https://doi.org/10.1002/jgt.3190180406. Moved from
`OpenConjectures/Combinatorics/ErdosProblem800`.
-/
theorem conjecture_holds : conjecture := by
  classical
  obtain ⟨k, hk⟩ := MathlibExt.Combinatorics.Ramsey.ramsey_two_uniform (r := 2) (k := 3) (by decide)
  have hk3 : 3 ≤ k := by
    obtain ⟨s, hs, _⟩ := hk (fun _ => 0)
    simpa [hs] using card_le_univ s
  let D := 64 * k.choose 3
  have hD : 1 < D := by
    have hchoose := Nat.choose_pos hk3
    dsimp [D]
    omega
  let K := max (max 4 k) (8 * D ^ 3)
  have hK : 0 < K := lt_of_lt_of_le (by decide : 0 < 4)
    ((le_max_left 4 k).trans (le_max_left _ _))
  refine ⟨(K : ℝ), by exact_mod_cast hK, ?_⟩
  intro n V _ G _ hn hG
  by_cases hn0 : n = 0
  · have hzero_card : Fintype.card V = 0 := hn.trans hn0
    let _ : IsEmpty V := Fintype.card_eq_zero_iff.mp hzero_card
    have hzero : SimpleGraph.diagonalGraphRamsey G ≤ 0 := by
      apply Nat.sInf_le
      intro H
      left
      exact ⟨⟨⟨fun x => isEmptyElim x, fun {x} => isEmptyElim x⟩,
        fun x => isEmptyElim x⟩⟩
    simpa [hn0] using (Nat.cast_le (α := ℝ)).mpr hzero
  let m := K * n
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hmpos : 0 < m := Nat.mul_pos hK hnpos
  let _ : Nonempty (Fin m) := ⟨⟨0, hmpos⟩⟩
  have hm : max 4 k ≤ m := (le_max_left _ _).trans
    (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left K hnpos)
  have hmD : 8 * D ^ 3 * n ≤ m := Nat.mul_le_mul_right n (le_max_right _ _)
  have hbudget : 5 * D ^ 2 * n ≤ m := by
    refine (Nat.mul_le_mul_right n ?_).trans hmD
    have h := Nat.mul_le_mul_right (D ^ 2) (show 5 ≤ 8 * D by omega)
    simpa only [pow_succ D 2, Nat.mul_assoc, Nat.mul_comm (D ^ 2) D] using h
  have hthreshold : ((6 * n * Fintype.card (Fin m) + 1 : ℕ) : ℝ) ≤
      2 * ((D : ℝ)⁻¹) ^ 3 * Fintype.card (Fin m × Fin m) := by
    have h : (6 * n * m + 1) * D ^ 3 ≤ 2 * (m * m) := by
      calc
        _ ≤ (8 * n * m) * D ^ 3 := by
          apply Nat.mul_le_mul_right
          have hnm := Nat.mul_pos hnpos hmpos
          rw [Nat.mul_assoc 6, Nat.mul_assoc 8]
          omega
        _ = (8 * D ^ 3 * n) * m := by ring
        _ ≤ m * m := Nat.mul_le_mul_right _ hmD
        _ ≤ 2 * (m * m) := by omega
    have hh : ((6 * n * m + 1 : ℕ) : ℝ) * (D : ℝ) ^ 3 ≤
        2 * ((m : ℝ) * (m : ℝ)) := by exact_mod_cast h
    have hd : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
    have hh' := (le_div_iff₀ (pow_pos hd 3)).mpr hh
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, inv_pow,
      div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hh'
  have hprepare (Q : SimpleGraph (Fin m)) [DecidableRel Q.Adj]
      (hq : 8 * m ^ 3 ≤ D * #(orderedTriangles Q)) : G.IsContained Q := by
    obtain ⟨A, hA, hdeg⟩ := dense_vertices Q D (by omega) (by simpa using hmpos)
      (by simpa using hq)
    have hAsize : 4 * D * (5 * n) ≤ #A := by
      apply Nat.le_of_mul_le_mul_left (c := D) _ (by omega)
      calc
        _ = 4 * (5 * D ^ 2 * n) := by ring
        _ ≤ 4 * m := Nat.mul_le_mul_left _ hbudget
        _ ≤ _ := by simpa using hA
    exact contained_of_dense_vertices G Q n D hD hn hG A hAsize hdeg hthreshold
  have hramsey : SimpleGraph.diagonalGraphRamsey G ≤ m := by
    apply Nat.sInf_le
    intro H
    have hcount := mono_triangle_density hk3 hk H (by simpa using hm)
    rw [Fintype.card_fin] at hcount
    change m ^ 3 ≤ _ at hcount
    have hdensity : 8 * m ^ 3 ≤ D * max #(orderedTriangles H) #(orderedTriangles Hᶜ) := by
      simpa only [D, Nat.mul_assoc, show 64 = (8 : ℕ) * 8 by decide] using
        Nat.mul_le_mul_left 8 hcount
    rcases le_total #(orderedTriangles H) #(orderedTriangles Hᶜ) with hc | hc
    · rw [max_eq_right hc] at hdensity
      exact Or.inr (hprepare Hᶜ hdensity)
    · rw [max_eq_left hc] at hdensity
      exact Or.inl (hprepare H hdensity)
  have hreal : (SimpleGraph.diagonalGraphRamsey G : ℝ) ≤ (m : ℝ) := by exact_mod_cast hramsey
  simpa [m] using hreal

end MathlibExt.Combinatorics.ErdosProblem800Wanted
