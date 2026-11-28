/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import CSLibExt.Planning.MotionPlanning.ConfigurationSpace
public import CSLibExt.Planning.MotionPlanning.TwoSquares
public import CSLibExt.Planning.MotionPlanning.PathShortening

@[expose] public section

/-!
Two-squares visibility-graph minimum (finite-graph semantic core).

Context: visibility graphs as in LaValle, Planning Algorithms, Sec. 6.2.4
(cited for context only; all definitions and proofs here are self-contained).

Setup: closed squares `O1 = [0,1] × [0,1]` and `O2 = [2,3] × [0,1]` in the
plane, free space `G` the complement of the interior of their union, and
endpoints `s = (-1, 1/2)`, `t = (4, 1/2)`.  The full visibility graph has the
10 vertices `s`, `t` and the 8 obstacle corners; two vertices are adjacent
when the closed segment between them lies in `G`, weighted by Euclidean
distance.

Main result (`min_eq_walk`): the least `s`-`t` walk weight equals `3 + √5`,
attained by the top walk `[s, (0,1), (3,1), t]`.

Lower-bound method: a uniform potential `H` plus per-step bonuses for leaving
`s` / entering `t`.  Every valid step satisfies a potential-drop inequality
(`step_le`, by case analysis on the endpoint kinds); telescoping over a walk
(`walk_lower_aux`) plus at least one bonus of each kind (`outTotal_ge`,
`inTotal_ge`) yields the bound.  No path enumeration and no algorithm.

Imports: narrow `Mathlib` modules plus the configuration-space and
two-squares providers.

the visibility graph visGraph is loopless (adjacency requires distinct vertices); VisAdj remains the underlying geometric segment relation.
-/

namespace Cslib.Planning.MotionPlanning.TwoSquaresGraph

open VisibilityInstance

/-- Open interior of the left square. -/
def open1 : Set plane := {p | 0 < p 0 ∧ p 0 < 1 ∧ 0 < p 1 ∧ p 1 < 1}

/-- Open interior of the right square. -/
def open2 : Set plane := {p | 2 < p 0 ∧ p 0 < 3 ∧ 0 < p 1 ∧ p 1 < 1}

-- Vertices (`!₂[x, y]` denotes `WithLp.toLp 2 ![x, y]`; written explicitly).
/-- Corner `(1, 0)`. -/
def B : plane := WithLp.toLp 2 ![1, 0]

/-- Corner `(1, 1)`. -/
def C : plane := WithLp.toLp 2 ![1, 1]

/-- Corner `(2, 0)`. -/
def E : plane := WithLp.toLp 2 ![2, 0]

/-- Corner `(2, 1)`. -/
def Q : plane := WithLp.toLp 2 ![2, 1]

/-- Visibility adjacency: the closed segment between `a` and `b` lies in `G`. -/
def VisAdj : plane → plane → Prop := fun a b => segment ℝ a b ⊆ G

/-- Visibility adjacency is symmetric. -/
theorem VisAdj.symm {a b : plane} (h : VisAdj a b) : VisAdj b a := by
  unfold VisAdj at h ⊢
  rwa [segment_symm] at h

/-- The 10 graph vertices. -/
inductive Vtx
  | s | t | A | B | C | D | E | F | P | Q
  deriving DecidableEq

/-- Coordinates of each vertex. -/
noncomputable def coord : Vtx → plane
  | .s => s
  | .t => t
  | .A => cBotL
  | .B => B
  | .C => C
  | .D => cTopL
  | .E => E
  | .F => cBotR
  | .P => cTopR
  | .Q => Q

/-- Loopless visibility graph on vertices: distinct endpoints with visible coordinates. -/
def visGraph : SimpleGraph Vtx where
  Adj a b := a ≠ b ∧ VisAdj (coord a) (coord b)
  symm := ⟨fun _ _ h => ⟨fun he => h.1 he.symm, VisAdj.symm h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Uniform potential used for the lower bound. -/
private noncomputable def H (x : Vtx) : ℝ := (3 - (coord x) 0) + Real.sqrt 5 / 2

/-- Per-step bonus constant `√5/2 - 1 > 0`. -/
private noncomputable def c : ℝ := Real.sqrt 5 / 2 - 1

/-- Bonus for a non-loop step out of `s`. -/
private noncomputable def outExtra (a b : Vtx) : ℝ := if a = .s ∧ a ≠ b then c else 0

/-- Bonus for a non-loop step into `t`. -/
private noncomputable def inExtra (a b : Vtx) : ℝ := if b = .t ∧ a ≠ b then c else 0

/-- Total per-step bonus. -/
private noncomputable def extra (a b : Vtx) : ℝ := outExtra a b + inExtra a b

private noncomputable abbrev polyLen (l : List Vtx) : ℝ :=
  PathShortening.polyLen (l.map coord)

private lemma polyLen_cons (a b : Vtx) (rest : List Vtx) :
    polyLen (a :: b :: rest) = dist (coord a) (coord b) + polyLen (b :: rest) :=
  rfl

/-- Consecutive-vertex adjacency along a list. -/
private def ChainAdj : List Vtx → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => visGraph.Adj a b ∧ ChainAdj (b :: rest)

/-- Accumulated out-of-`s` bonus along a list. -/
private noncomputable def outTotal : List Vtx → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => outExtra a b + outTotal (b :: rest)

/-- Accumulated into-`t` bonus along a list. -/
private noncomputable def inTotal : List Vtx → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => inExtra a b + inTotal (b :: rest)

/-- Accumulated total bonus along a list. -/
private noncomputable def bonusTotal : List Vtx → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => extra a b + bonusTotal (b :: rest)

/-- Last element of a vertex list, if any. -/
private def last? : List Vtx → Option Vtx
  | [] => none
  | [x] => some x
  | _ :: b :: rest => last? (b :: rest)

/-- Walks from `s` to `t` with adjacent consecutive vertices. -/
private def IsWalk (l : List Vtx) : Prop :=
  l.head? = some .s ∧ last? l = some .t ∧ ChainAdj l

-- Coordinate computation infrastructure (via the coordinate projections).

private lemma add_c0 (x y : plane) : (x + y) 0 = x 0 + y 0 := by
  have h : (EuclideanSpace.proj (0 : Fin 2)) (x + y)
      = (EuclideanSpace.proj (0 : Fin 2)) x + (EuclideanSpace.proj (0 : Fin 2)) y :=
    map_add _ _ _
  simpa only [EuclideanSpace.coe_proj] using h
private lemma add_c1 (x y : plane) : (x + y) 1 = x 1 + y 1 := by
  have h : (EuclideanSpace.proj (1 : Fin 2)) (x + y)
      = (EuclideanSpace.proj (1 : Fin 2)) x + (EuclideanSpace.proj (1 : Fin 2)) y :=
    map_add _ _ _
  simpa only [EuclideanSpace.coe_proj] using h

private lemma sub_c0 (x y : plane) : (x - y) 0 = x 0 - y 0 := by
  have h : (EuclideanSpace.proj (0 : Fin 2)) (x - y)
      = (EuclideanSpace.proj (0 : Fin 2)) x - (EuclideanSpace.proj (0 : Fin 2)) y :=
    map_sub _ _ _
  simpa only [EuclideanSpace.coe_proj] using h

private lemma sub_c1 (x y : plane) : (x - y) 1 = x 1 - y 1 := by
  have h : (EuclideanSpace.proj (1 : Fin 2)) (x - y)
      = (EuclideanSpace.proj (1 : Fin 2)) x - (EuclideanSpace.proj (1 : Fin 2)) y :=
    map_sub _ _ _
  simpa only [EuclideanSpace.coe_proj] using h

private lemma smul_c0 (r : ℝ) (x : plane) : (r • x) 0 = r * x 0 := by
  have h : (EuclideanSpace.proj (0 : Fin 2)) (r • x)
      = r • (EuclideanSpace.proj (0 : Fin 2)) x :=
    map_smul _ _ _
  simpa only [EuclideanSpace.coe_proj, smul_eq_mul] using h

private lemma smul_c1 (r : ℝ) (x : plane) : (r • x) 1 = r * x 1 := by
  have h : (EuclideanSpace.proj (1 : Fin 2)) (r • x)
      = r • (EuclideanSpace.proj (1 : Fin 2)) x :=
    map_smul _ _ _
  simpa only [EuclideanSpace.coe_proj, smul_eq_mul] using h

private lemma seg_c0 (t : ℝ) (a b : plane) :
    ((1 - t) • a + t • b) 0 = (1 - t) * (a 0) + t * (b 0) := by
  rw [add_c0, smul_c0, smul_c0]

private lemma seg_c1 (t : ℝ) (a b : plane) :
    ((1 - t) • a + t • b) 1 = (1 - t) * (a 1) + t * (b 1) := by
  rw [add_c1, smul_c1, smul_c1]

-- Point coordinates.

private lemma s0 : s 0 = -1 := by
  simp only [s, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]

private lemma s1 : s 1 = 1 / 2 := by
  simp only [s, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]

private lemma t0 : t 0 = 4 := by
  simp only [t, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]

private lemma t1 : t 1 = 1 / 2 := by
  simp only [t, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]

private lemma cBotL0 : cBotL 0 = 0 := by
  simp only [cBotL, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]

private lemma cBotL1 : cBotL 1 = 0 := by
  simp only [cBotL, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]

private lemma B0 : B 0 = 1 := by
  simp only [B, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]

private lemma B1 : B 1 = 0 := by
  simp only [B, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]

private lemma C0 : C 0 = 1 := by
  simp only [C, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]

private lemma C1 : C 1 = 1 := by
  simp only [C, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]

private lemma cTopL0 : cTopL 0 = 0 := by
  simp only [cTopL, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]

private lemma cTopL1 : cTopL 1 = 1 := by
  simp only [cTopL, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]

private lemma E0 : E 0 = 2 := by
  simp only [E, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]

private lemma E1 : E 1 = 0 := by
  simp only [E, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]

private lemma cBotR0 : cBotR 0 = 3 := by
  simp only [cBotR, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]

private lemma cBotR1 : cBotR 1 = 0 := by
  simp only [cBotR, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]

private lemma cTopR0 : cTopR 0 = 3 := by
  simp only [cTopR, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]

private lemma cTopR1 : cTopR 1 = 1 := by
  simp only [cTopR, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]

private lemma Q0 : Q 0 = 2 := by
  simp only [Q, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]

private lemma Q1 : Q 1 = 1 := by
  simp only [Q, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons]

-- The open squares lie in the interior of the union.

private lemma hcont0 : Continuous fun p : plane => p 0 := by
  have h := ContinuousLinearMap.continuous (EuclideanSpace.proj (0 : Fin 2) : plane →L[ℝ] ℝ)
  simpa only [EuclideanSpace.coe_proj] using h

private lemma hcont1 : Continuous fun p : plane => p 1 := by
  have h := ContinuousLinearMap.continuous (EuclideanSpace.proj (1 : Fin 2) : plane →L[ℝ] ℝ)
  simpa only [EuclideanSpace.coe_proj] using h

private lemma open1_sub : open1 ⊆ interior (O1 ∪ O2) := by
  apply interior_maximal
  · intro p hp
    have hp' : 0 < p 0 ∧ p 0 < 1 ∧ 0 < p 1 ∧ p 1 < 1 := hp
    obtain ⟨h1, h2, h3, h4⟩ := hp'
    refine Or.inl ?_
    have g : (0:ℝ) ≤ p 0 ∧ p 0 ≤ 1 ∧ (0:ℝ) ≤ p 1 ∧ p 1 ≤ 1 :=
      ⟨le_of_lt h1, le_of_lt h2, le_of_lt h3, le_of_lt h4⟩
    exact g
  · have e : open1 = (fun p : plane => p 0) ⁻¹' Set.Ioo (0:ℝ) 1 ∩
        (fun p : plane => p 1) ⁻¹' Set.Ioo (0:ℝ) 1 := by
      ext p
      constructor
      · intro h
        have h' : 0 < p 0 ∧ p 0 < 1 ∧ 0 < p 1 ∧ p 1 < 1 := h
        obtain ⟨h1, h2, h3, h4⟩ := h'
        exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      · intro h
        have h' : (p 0 ∈ Set.Ioo (0:ℝ) 1) ∧ (p 1 ∈ Set.Ioo (0:ℝ) 1) := h
        obtain ⟨g1, g2⟩ := h'
        have h12 : 0 < p 0 ∧ p 0 < 1 := g1
        have h34 : 0 < p 1 ∧ p 1 < 1 := g2
        obtain ⟨h1, h2⟩ := h12
        obtain ⟨h3, h4⟩ := h34
        exact ⟨h1, h2, h3, h4⟩
    rw [e]
    exact IsOpen.inter (isOpen_Ioo.preimage hcont0) (isOpen_Ioo.preimage hcont1)

private lemma open2_sub : open2 ⊆ interior (O1 ∪ O2) := by
  apply interior_maximal
  · intro p hp
    have hp' : 2 < p 0 ∧ p 0 < 3 ∧ 0 < p 1 ∧ p 1 < 1 := hp
    obtain ⟨h1, h2, h3, h4⟩ := hp'
    refine Or.inr ?_
    have g : (2:ℝ) ≤ p 0 ∧ p 0 ≤ 3 ∧ (0:ℝ) ≤ p 1 ∧ p 1 ≤ 1 :=
      ⟨le_of_lt h1, le_of_lt h2, le_of_lt h3, le_of_lt h4⟩
    exact g
  · have e : open2 = (fun p : plane => p 0) ⁻¹' Set.Ioo (2:ℝ) 3 ∩
        (fun p : plane => p 1) ⁻¹' Set.Ioo (0:ℝ) 1 := by
      ext p
      constructor
      · intro h
        have h' : 2 < p 0 ∧ p 0 < 3 ∧ 0 < p 1 ∧ p 1 < 1 := h
        obtain ⟨h1, h2, h3, h4⟩ := h'
        exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      · intro h
        have h' : (p 0 ∈ Set.Ioo (2:ℝ) 3) ∧ (p 1 ∈ Set.Ioo (0:ℝ) 1) := h
        obtain ⟨g1, g2⟩ := h'
        have h12 : 2 < p 0 ∧ p 0 < 3 := g1
        have h34 : 0 < p 1 ∧ p 1 < 1 := g2
        obtain ⟨h1, h2⟩ := h12
        obtain ⟨h3, h4⟩ := h34
        exact ⟨h1, h2, h3, h4⟩
    rw [e]
    exact IsOpen.inter (isOpen_Ioo.preimage hcont0) (isOpen_Ioo.preimage hcont1)

private lemma openUnion_sub_interior : open1 ∪ open2 ⊆ interior (O1 ∪ O2) := by
  intro p hp
  rcases hp with h1 | h2
  · exact open1_sub h1
  · exact open2_sub h2

-- Square-root facts and edge distances.

private lemma h2s5 : (2:ℝ) ≤ Real.sqrt 5 := by
  have h4 : Real.sqrt 4 ≤ Real.sqrt 5 := Real.sqrt_le_sqrt (by norm_num)
  have h42 : Real.sqrt 4 = 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [h42] at h4
  exact h4

private lemma c_nonneg : 0 ≤ c := by
  simp only [c]
  linarith [h2s5]

private lemma dist_sA : dist (coord .s) (coord .A) = Real.sqrt 5 / 2 := by
  simp only [coord]
  exact dist_s_botL

theorem dist_sD : dist (coord .s) (coord .D) = Real.sqrt 5 / 2 := by
  simp only [coord]
  exact dist_s_topL

private lemma dist_Ft : dist (coord .F) (coord .t) = Real.sqrt 5 / 2 := by
  simp only [coord]
  exact dist_botR_t

theorem dist_Pt : dist (coord .P) (coord .t) = Real.sqrt 5 / 2 := by
  simp only [coord]
  exact dist_topR_t

theorem dist_DP : dist (coord .D) (coord .P) = 3 := by
  simp only [coord]
  exact dist_top_mid

-- Potential values.

private lemma Hs : H .s = 4 + Real.sqrt 5 / 2 := by
  simp only [H, coord, s, PiLp.toLp_apply, Matrix.cons_val_zero]
  ring
private lemma Ht : H .t = -1 + Real.sqrt 5 / 2 := by
  simp only [H, coord, t, PiLp.toLp_apply, Matrix.cons_val_zero]
  ring

private lemma HA : H .A = 3 + Real.sqrt 5 / 2 := by
  simp only [H, coord, cBotL, PiLp.toLp_apply, Matrix.cons_val_zero]
  ring

private lemma HD : H .D = 3 + Real.sqrt 5 / 2 := by
  simp only [H, coord, cTopL, PiLp.toLp_apply, Matrix.cons_val_zero]
  ring

private lemma HF : H .F = Real.sqrt 5 / 2 := by
  simp only [H, coord, cBotR, PiLp.toLp_apply, Matrix.cons_val_zero]
  ring

private lemma HP : H .P = Real.sqrt 5 / 2 := by
  simp only [H, coord, cTopR, PiLp.toLp_apply, Matrix.cons_val_zero]
  ring

-- Norm bridge: x-displacement bound.

private lemma abs_le_dist (p q : plane) : |p 0 - q 0| ≤ dist p q := by
  have h2 : ‖p - q‖ ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, sub_c0, sub_c1]
  calc |p 0 - q 0| = Real.sqrt ((p 0 - q 0) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (‖p - q‖ ^ 2) :=
        Real.sqrt_le_sqrt (by rw [h2]; linarith [sq_nonneg (p 1 - q 1)])
    _ = ‖p - q‖ := Real.sqrt_sq (norm_nonneg _)
    _ = dist p q := (dist_eq_norm _ _).symm

-- Positive adjacency facts (spot checks + upper-bound walk edges).

theorem adj_s_D : VisAdj (coord .s) (coord .D) := by
  unfold VisAdj
  simp only [coord]
  exact seg_top_left

theorem adj_s_A : VisAdj (coord .s) (coord .A) := by
  unfold VisAdj
  simp only [coord]
  exact seg_bot_left

theorem adj_D_P : VisAdj (coord .D) (coord .P) := by
  unfold VisAdj
  simp only [coord]
  exact top_middle_visible

theorem adj_P_t : VisAdj (coord .P) (coord .t) := by
  unfold VisAdj
  simp only [coord]
  exact seg_top_right

-- Non-adjacency facts, each witnessed by an interior point on the segment.

theorem not_adj_s_B : ¬ VisAdj (coord .s) (coord .B) := by
  unfold VisAdj
  simp only [coord]
  intro hsub
  have hmem : WithLp.toLp 2 ![1/5, 1/5] ∈ segment ℝ VisibilityInstance.s B := by
    rw [segment_eq_image]
    refine ⟨3/5, by show (0:ℝ) ≤ 3/5 ∧ 3/5 ≤ 1; norm_num, ?_⟩
    ext i
    show ((1 - 3/5) • VisibilityInstance.s + (3/5) • B) i
      = (WithLp.toLp 2 ![1/5, 1/5] : plane) i
    fin_cases i <;>
      simp only [Fin.mk_zero, Fin.mk_one, PiLp.toLp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, seg_c0, seg_c1, s0, s1, B0, B1] <;>
      norm_num
  have hG := hsub hmem
  have hI : WithLp.toLp 2 ![1/5, 1/5] ∈
      interior (VisibilityInstance.O1 ∪ VisibilityInstance.O2) := by
    apply openUnion_sub_interior
    refine Or.inl ?_
    simp only [open1, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    show (0:ℝ) < 1/5 ∧ (1/5:ℝ) < 1 ∧ (0:ℝ) < 1/5 ∧ (1/5:ℝ) < 1
    norm_num
  exact hG hI

theorem not_adj_s_C : ¬ VisAdj (coord .s) (coord .C) := by
  unfold VisAdj
  simp only [coord]
  intro hsub
  have hmem : WithLp.toLp 2 ![1/5, 4/5] ∈ segment ℝ VisibilityInstance.s C := by
    rw [segment_eq_image]
    refine ⟨3/5, by show (0:ℝ) ≤ 3/5 ∧ 3/5 ≤ 1; norm_num, ?_⟩
    ext i
    show ((1 - 3/5) • VisibilityInstance.s + (3/5) • C) i
      = (WithLp.toLp 2 ![1/5, 4/5] : plane) i
    fin_cases i <;>
      simp only [Fin.mk_zero, Fin.mk_one, PiLp.toLp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, seg_c0, seg_c1, s0, s1, C0, C1] <;>
      norm_num
  have hG := hsub hmem
  have hI : WithLp.toLp 2 ![1/5, 4/5] ∈
      interior (VisibilityInstance.O1 ∪ VisibilityInstance.O2) := by
    apply openUnion_sub_interior
    refine Or.inl ?_
    simp only [open1, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    show (0:ℝ) < 1/5 ∧ (1/5:ℝ) < 1 ∧ (0:ℝ) < 4/5 ∧ (4/5:ℝ) < 1
    norm_num
  exact hG hI

theorem not_adj_s_E : ¬ VisAdj (coord .s) (coord .E) := by
  unfold VisAdj
  simp only [coord]
  intro hsub
  have hmem : WithLp.toLp 2 ![1/5, 3/10] ∈ segment ℝ VisibilityInstance.s E := by
    rw [segment_eq_image]
    refine ⟨2/5, by show (0:ℝ) ≤ 2/5 ∧ 2/5 ≤ 1; norm_num, ?_⟩
    ext i
    show ((1 - 2/5) • VisibilityInstance.s + (2/5) • E) i
      = (WithLp.toLp 2 ![1/5, 3/10] : plane) i
    fin_cases i <;>
      simp only [Fin.mk_zero, Fin.mk_one, PiLp.toLp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, seg_c0, seg_c1, s0, s1, E0, E1] <;>
      norm_num
  have hG := hsub hmem
  have hI : WithLp.toLp 2 ![1/5, 3/10] ∈
      interior (VisibilityInstance.O1 ∪ VisibilityInstance.O2) := by
    apply openUnion_sub_interior
    refine Or.inl ?_
    simp only [open1, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    show (0:ℝ) < 1/5 ∧ (1/5:ℝ) < 1 ∧ (0:ℝ) < 3/10 ∧ (3/10:ℝ) < 1
    norm_num
  exact hG hI

theorem not_adj_s_F : ¬ VisAdj (coord .s) (coord .F) := by
  unfold VisAdj
  simp only [coord]
  intro hsub
  have hmem : WithLp.toLp 2 ![1/5, 7/20] ∈
      segment ℝ VisibilityInstance.s VisibilityInstance.cBotR := by
    rw [segment_eq_image]
    refine ⟨3/10, by show (0:ℝ) ≤ 3/10 ∧ 3/10 ≤ 1; norm_num, ?_⟩
    ext i
    show ((1 - 3/10) • VisibilityInstance.s + (3/10) • VisibilityInstance.cBotR) i
      = (WithLp.toLp 2 ![1/5, 7/20] : plane) i
    fin_cases i <;>
      simp only [Fin.mk_zero, Fin.mk_one, PiLp.toLp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, seg_c0, seg_c1, s0, s1, cBotR0, cBotR1] <;>
      norm_num
  have hG := hsub hmem
  have hI : WithLp.toLp 2 ![1/5, 7/20] ∈
      interior (VisibilityInstance.O1 ∪ VisibilityInstance.O2) := by
    apply openUnion_sub_interior
    refine Or.inl ?_
    simp only [open1, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    show (0:ℝ) < 1/5 ∧ (1/5:ℝ) < 1 ∧ (0:ℝ) < 7/20 ∧ (7/20:ℝ) < 1
    norm_num
  exact hG hI

theorem not_adj_s_P : ¬ VisAdj (coord .s) (coord .P) := by
  unfold VisAdj
  simp only [coord]
  intro hsub
  have hmem : WithLp.toLp 2 ![1/5, 13/20] ∈
      segment ℝ VisibilityInstance.s VisibilityInstance.cTopR := by
    rw [segment_eq_image]
    refine ⟨3/10, by show (0:ℝ) ≤ 3/10 ∧ 3/10 ≤ 1; norm_num, ?_⟩
    ext i
    show ((1 - 3/10) • VisibilityInstance.s + (3/10) • VisibilityInstance.cTopR) i
      = (WithLp.toLp 2 ![1/5, 13/20] : plane) i
    fin_cases i <;>
      simp only [Fin.mk_zero, Fin.mk_one, PiLp.toLp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, seg_c0, seg_c1, s0, s1, cTopR0, cTopR1] <;>
      norm_num
  have hG := hsub hmem
  have hI : WithLp.toLp 2 ![1/5, 13/20] ∈
      interior (VisibilityInstance.O1 ∪ VisibilityInstance.O2) := by
    apply openUnion_sub_interior
    refine Or.inl ?_
    simp only [open1, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    show (0:ℝ) < 1/5 ∧ (1/5:ℝ) < 1 ∧ (0:ℝ) < 13/20 ∧ (13/20:ℝ) < 1
    norm_num
  exact hG hI

theorem not_adj_s_Q : ¬ VisAdj (coord .s) (coord .Q) := by
  unfold VisAdj
  simp only [coord]
  intro hsub
  have hmem : WithLp.toLp 2 ![1/5, 7/10] ∈ segment ℝ VisibilityInstance.s Q := by
    rw [segment_eq_image]
    refine ⟨2/5, by show (0:ℝ) ≤ 2/5 ∧ 2/5 ≤ 1; norm_num, ?_⟩
    ext i
    show ((1 - 2/5) • VisibilityInstance.s + (2/5) • Q) i
      = (WithLp.toLp 2 ![1/5, 7/10] : plane) i
    fin_cases i <;>
      simp only [Fin.mk_zero, Fin.mk_one, PiLp.toLp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, seg_c0, seg_c1, s0, s1, Q0, Q1] <;>
      norm_num
  have hG := hsub hmem
  have hI : WithLp.toLp 2 ![1/5, 7/10] ∈
      interior (VisibilityInstance.O1 ∪ VisibilityInstance.O2) := by
    apply openUnion_sub_interior
    refine Or.inl ?_
    simp only [open1, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    show (0:ℝ) < 1/5 ∧ (1/5:ℝ) < 1 ∧ (0:ℝ) < 7/10 ∧ (7/10:ℝ) < 1
    norm_num
  exact hG hI

theorem not_adj_s_t : ¬ VisAdj (coord .s) (coord .t) := by
  unfold VisAdj
  simp only [coord]
  intro hsub
  have hmem : WithLp.toLp 2 ![1/2, 1/2] ∈
      segment ℝ VisibilityInstance.s VisibilityInstance.t := by
    rw [segment_eq_image]
    refine ⟨3/10, by show (0:ℝ) ≤ 3/10 ∧ 3/10 ≤ 1; norm_num, ?_⟩
    ext i
    show ((1 - 3/10) • VisibilityInstance.s + (3/10) • VisibilityInstance.t) i
      = (WithLp.toLp 2 ![1/2, 1/2] : plane) i
    fin_cases i <;>
      simp only [Fin.mk_zero, Fin.mk_one, PiLp.toLp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, seg_c0, seg_c1, s0, s1, t0, t1] <;>
      norm_num
  have hG := hsub hmem
  have hI : WithLp.toLp 2 ![1/2, 1/2] ∈
      interior (VisibilityInstance.O1 ∪ VisibilityInstance.O2) := by
    apply openUnion_sub_interior
    refine Or.inl ?_
    simp only [open1, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    show (0:ℝ) < 1/2 ∧ (1/2:ℝ) < 1 ∧ (0:ℝ) < 1/2 ∧ (1/2:ℝ) < 1
    norm_num
  exact hG hI

theorem not_adj_A_t : ¬ VisAdj (coord .A) (coord .t) := by
  unfold VisAdj
  simp only [coord]
  intro hsub
  have hmem : WithLp.toLp 2 ![12/5, 3/10] ∈
      segment ℝ VisibilityInstance.cBotL VisibilityInstance.t := by
    rw [segment_eq_image]
    refine ⟨3/5, by show (0:ℝ) ≤ 3/5 ∧ 3/5 ≤ 1; norm_num, ?_⟩
    ext i
    show ((1 - 3/5) • VisibilityInstance.cBotL + (3/5) • VisibilityInstance.t) i
      = (WithLp.toLp 2 ![12/5, 3/10] : plane) i
    fin_cases i <;>
      simp only [Fin.mk_zero, Fin.mk_one, PiLp.toLp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, seg_c0, seg_c1, cBotL0, cBotL1, t0, t1] <;>
      norm_num
  have hG := hsub hmem
  have hI : WithLp.toLp 2 ![12/5, 3/10] ∈
      interior (VisibilityInstance.O1 ∪ VisibilityInstance.O2) := by
    apply openUnion_sub_interior
    refine Or.inr ?_
    simp only [open2, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    show (2:ℝ) < 12/5 ∧ (12/5:ℝ) < 3 ∧ (0:ℝ) < 3/10 ∧ (3/10:ℝ) < 1
    norm_num
  exact hG hI

theorem not_adj_B_t : ¬ VisAdj (coord .B) (coord .t) := by
  unfold VisAdj
  simp only [coord]
  intro hsub
  have hmem : WithLp.toLp 2 ![5/2, 1/4] ∈
      segment ℝ B VisibilityInstance.t := by
    rw [segment_eq_image]
    refine ⟨1/2, by show (0:ℝ) ≤ 1/2 ∧ 1/2 ≤ 1; norm_num, ?_⟩
    ext i
    show ((1 - 1/2) • B + (1/2) • VisibilityInstance.t) i
      = (WithLp.toLp 2 ![5/2, 1/4] : plane) i
    fin_cases i <;>
      simp only [Fin.mk_zero, Fin.mk_one, PiLp.toLp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, seg_c0, seg_c1, B0, B1, t0, t1] <;>
      norm_num
  have hG := hsub hmem
  have hI : WithLp.toLp 2 ![5/2, 1/4] ∈
      interior (VisibilityInstance.O1 ∪ VisibilityInstance.O2) := by
    apply openUnion_sub_interior
    refine Or.inr ?_
    simp only [open2, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    show (2:ℝ) < 5/2 ∧ (5/2:ℝ) < 3 ∧ (0:ℝ) < 1/4 ∧ (1/4:ℝ) < 1
    norm_num
  exact hG hI

theorem not_adj_C_t : ¬ VisAdj (coord .C) (coord .t) := by
  unfold VisAdj
  simp only [coord]
  intro hsub
  have hmem : WithLp.toLp 2 ![5/2, 3/4] ∈
      segment ℝ C VisibilityInstance.t := by
    rw [segment_eq_image]
    refine ⟨1/2, by show (0:ℝ) ≤ 1/2 ∧ 1/2 ≤ 1; norm_num, ?_⟩
    ext i
    show ((1 - 1/2) • C + (1/2) • VisibilityInstance.t) i
      = (WithLp.toLp 2 ![5/2, 3/4] : plane) i
    fin_cases i <;>
      simp only [Fin.mk_zero, Fin.mk_one, PiLp.toLp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, seg_c0, seg_c1, C0, C1, t0, t1] <;>
      norm_num
  have hG := hsub hmem
  have hI : WithLp.toLp 2 ![5/2, 3/4] ∈
      interior (VisibilityInstance.O1 ∪ VisibilityInstance.O2) := by
    apply openUnion_sub_interior
    refine Or.inr ?_
    simp only [open2, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    show (2:ℝ) < 5/2 ∧ (5/2:ℝ) < 3 ∧ (0:ℝ) < 3/4 ∧ (3/4:ℝ) < 1
    norm_num
  exact hG hI

theorem not_adj_D_t : ¬ VisAdj (coord .D) (coord .t) := by
  unfold VisAdj
  simp only [coord]
  intro hsub
  have hmem : WithLp.toLp 2 ![12/5, 7/10] ∈
      segment ℝ VisibilityInstance.cTopL VisibilityInstance.t := by
    rw [segment_eq_image]
    refine ⟨3/5, by show (0:ℝ) ≤ 3/5 ∧ 3/5 ≤ 1; norm_num, ?_⟩
    ext i
    show ((1 - 3/5) • VisibilityInstance.cTopL + (3/5) • VisibilityInstance.t) i
      = (WithLp.toLp 2 ![12/5, 7/10] : plane) i
    fin_cases i <;>
      simp only [Fin.mk_zero, Fin.mk_one, PiLp.toLp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, seg_c0, seg_c1, cTopL0, cTopL1, t0, t1] <;>
      norm_num
  have hG := hsub hmem
  have hI : WithLp.toLp 2 ![12/5, 7/10] ∈
      interior (VisibilityInstance.O1 ∪ VisibilityInstance.O2) := by
    apply openUnion_sub_interior
    refine Or.inr ?_
    simp only [open2, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    show (2:ℝ) < 12/5 ∧ (12/5:ℝ) < 3 ∧ (0:ℝ) < 7/10 ∧ (7/10:ℝ) < 1
    norm_num
  exact hG hI

theorem not_adj_E_t : ¬ VisAdj (coord .E) (coord .t) := by
  unfold VisAdj
  simp only [coord]
  intro hsub
  have hmem : WithLp.toLp 2 ![14/5, 1/5] ∈
      segment ℝ E VisibilityInstance.t := by
    rw [segment_eq_image]
    refine ⟨2/5, by show (0:ℝ) ≤ 2/5 ∧ 2/5 ≤ 1; norm_num, ?_⟩
    ext i
    show ((1 - 2/5) • E + (2/5) • VisibilityInstance.t) i
      = (WithLp.toLp 2 ![14/5, 1/5] : plane) i
    fin_cases i <;>
      simp only [Fin.mk_zero, Fin.mk_one, PiLp.toLp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, seg_c0, seg_c1, E0, E1, t0, t1] <;>
      norm_num
  have hG := hsub hmem
  have hI : WithLp.toLp 2 ![14/5, 1/5] ∈
      interior (VisibilityInstance.O1 ∪ VisibilityInstance.O2) := by
    apply openUnion_sub_interior
    refine Or.inr ?_
    simp only [open2, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    show (2:ℝ) < 14/5 ∧ (14/5:ℝ) < 3 ∧ (0:ℝ) < 1/5 ∧ (1/5:ℝ) < 1
    norm_num
  exact hG hI

theorem not_adj_Q_t : ¬ VisAdj (coord .Q) (coord .t) := by
  unfold VisAdj
  simp only [coord]
  intro hsub
  have hmem : WithLp.toLp 2 ![14/5, 4/5] ∈
      segment ℝ Q VisibilityInstance.t := by
    rw [segment_eq_image]
    refine ⟨2/5, by show (0:ℝ) ≤ 2/5 ∧ 2/5 ≤ 1; norm_num, ?_⟩
    ext i
    show ((1 - 2/5) • Q + (2/5) • VisibilityInstance.t) i
      = (WithLp.toLp 2 ![14/5, 4/5] : plane) i
    fin_cases i <;>
      simp only [Fin.mk_zero, Fin.mk_one, PiLp.toLp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons, seg_c0, seg_c1, Q0, Q1, t0, t1] <;>
      norm_num
  have hG := hsub hmem
  have hI : WithLp.toLp 2 ![14/5, 4/5] ∈
      interior (VisibilityInstance.O1 ∪ VisibilityInstance.O2) := by
    apply openUnion_sub_interior
    refine Or.inr ?_
    simp only [open2, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    show (2:ℝ) < 14/5 ∧ (14/5:ℝ) < 3 ∧ (0:ℝ) < 4/5 ∧ (4/5:ℝ) < 1
    norm_num
  exact hG hI

-- Per-step lower bound: potential drop plus bonus.

private lemma step_mid (a b : Vtx) (ha : a ≠ .s) (hb : b ≠ .t)
    (_hadj : VisAdj (coord a) (coord b)) :
    extra a b + (H a - H b) ≤ dist (coord a) (coord b) := by
  have ho : outExtra a b = 0 := by
    simp only [outExtra]
    exact ite_eq_right (fun h => ha h.1)
  have hi : inExtra a b = 0 := by
    simp only [inExtra]
    exact ite_eq_right (fun h => hb h.1)
  have he : extra a b = 0 := by simp only [extra, ho, hi, add_zero]
  have h1 : (coord b) 0 - (coord a) 0 ≤ dist (coord a) (coord b) := by
    have h := le_trans (le_abs_self ((coord b) 0 - (coord a) 0))
      (abs_le_dist (coord b) (coord a))
    rwa [dist_comm] at h
  have hHab : H a - H b = (coord b) 0 - (coord a) 0 := by
    simp only [H]
    ring
  rw [he, zero_add, hHab]
  exact h1

private lemma step_s_row (b : Vtx) (hadj : VisAdj (coord .s) (coord b)) :
    extra .s b + (H .s - H b) ≤ dist (coord .s) (coord b) := by
  cases b
  · -- `.s`: trivial loop.
    have ho : outExtra .s .s = 0 := by
      simp only [outExtra]
      exact ite_eq_right (by decide)
    have hi : inExtra .s .s = 0 := by
      simp only [inExtra]
      exact ite_eq_right (by decide)
    have he : extra .s .s = 0 := by simp only [extra, ho, hi, add_zero]
    rw [he, sub_self, dist_self, zero_add]
  · -- `.t`: not adjacent.
    exact False.elim (not_adj_s_t hadj)
  · -- `.A`: edge of length `√5/2`.
    have ho : outExtra .s .A = c := by
      simp only [outExtra]
      exact ite_eq_left (by decide)
    have hi : inExtra .s .A = 0 := by
      simp only [inExtra]
      exact ite_eq_right (by decide)
    have he : extra .s .A = c := by simp only [extra, ho, hi, add_zero]
    rw [he, Hs, HA, dist_sA]
    simp only [c]
    exact le_of_eq (by ring)
  · -- `.B`: not adjacent.
    exact False.elim (not_adj_s_B hadj)
  · -- `.C`: not adjacent.
    exact False.elim (not_adj_s_C hadj)
  · -- `.D`: edge of length `√5/2`.
    have ho : outExtra .s .D = c := by
      simp only [outExtra]
      exact ite_eq_left (by decide)
    have hi : inExtra .s .D = 0 := by
      simp only [inExtra]
      exact ite_eq_right (by decide)
    have he : extra .s .D = c := by simp only [extra, ho, hi, add_zero]
    rw [he, Hs, HD, dist_sD]
    simp only [c]
    exact le_of_eq (by ring)
  · -- `.E`: not adjacent.
    exact False.elim (not_adj_s_E hadj)
  · -- `.F`: not adjacent.
    exact False.elim (not_adj_s_F hadj)
  · -- `.P`: not adjacent.
    exact False.elim (not_adj_s_P hadj)
  · -- `.Q`: not adjacent.
    exact False.elim (not_adj_s_Q hadj)

private lemma step_col_t (a : Vtx) (ha : a ≠ .s) (hadj : VisAdj (coord a) (coord .t)) :
    extra a .t + (H a - H .t) ≤ dist (coord a) (coord .t) := by
  cases a
  · -- `.s`: excluded by hypothesis.
    exact absurd rfl ha
  · -- `.t`: trivial loop.
    have ho : outExtra .t .t = 0 := by
      simp only [outExtra]
      exact ite_eq_right (by decide)
    have hi : inExtra .t .t = 0 := by
      simp only [inExtra]
      exact ite_eq_right (by decide)
    have he : extra .t .t = 0 := by simp only [extra, ho, hi, add_zero]
    rw [he, sub_self, dist_self, zero_add]
  · -- `.A`: not adjacent.
    exact False.elim (not_adj_A_t hadj)
  · -- `.B`: not adjacent.
    exact False.elim (not_adj_B_t hadj)
  · -- `.C`: not adjacent.
    exact False.elim (not_adj_C_t hadj)
  · -- `.D`: not adjacent.
    exact False.elim (not_adj_D_t hadj)
  · -- `.E`: not adjacent.
    exact False.elim (not_adj_E_t hadj)
  · -- `.F`: edge of length `√5/2`.
    have ho : outExtra .F .t = 0 := by
      simp only [outExtra]
      exact ite_eq_right (by decide)
    have hi : inExtra .F .t = c := by
      simp only [inExtra]
      exact ite_eq_left (by decide)
    have he : extra .F .t = c := by simp only [extra, ho, hi, zero_add]
    rw [he, HF, Ht, dist_Ft]
    simp only [c]
    exact le_of_eq (by ring)
  · -- `.P`: edge of length `√5/2`.
    have ho : outExtra .P .t = 0 := by
      simp only [outExtra]
      exact ite_eq_right (by decide)
    have hi : inExtra .P .t = c := by
      simp only [inExtra]
      exact ite_eq_left (by decide)
    have he : extra .P .t = c := by simp only [extra, ho, hi, zero_add]
    rw [he, HP, Ht, dist_Pt]
    simp only [c]
    exact le_of_eq (by ring)
  · -- `.Q`: not adjacent.
    exact False.elim (not_adj_Q_t hadj)

private lemma step_le (a b : Vtx) (hadj : VisAdj (coord a) (coord b)) :
    extra a b + (H a - H b) ≤ dist (coord a) (coord b) := by
  by_cases ha : a = .s
  · subst ha
    exact step_s_row b hadj
  · by_cases hb : b = .t
    · subst hb
      exact step_col_t a ha hadj
    · exact step_mid a b ha hb hadj

-- Bonus bookkeeping along walks.

private lemma outTotal_nonneg (l : List Vtx) : 0 ≤ outTotal l := by
  induction l with
  | nil =>
    show (0:ℝ) ≤ 0
    exact le_rfl
  | cons a tl ih =>
    cases tl with
    | nil =>
      show (0:ℝ) ≤ 0
      exact le_rfl
    | cons b rest =>
      have he : 0 ≤ outExtra a b := by
        simp only [outExtra]
        by_cases h : a = .s ∧ a ≠ b
        · rw [ite_eq_left h]
          exact c_nonneg
        · rw [ite_eq_right h]
      show 0 ≤ outExtra a b + outTotal (b :: rest)
      exact add_nonneg he ih

private lemma inTotal_nonneg (l : List Vtx) : 0 ≤ inTotal l := by
  induction l with
  | nil =>
    show (0:ℝ) ≤ 0
    exact le_rfl
  | cons a tl ih =>
    cases tl with
    | nil =>
      show (0:ℝ) ≤ 0
      exact le_rfl
    | cons b rest =>
      have he : 0 ≤ inExtra a b := by
        simp only [inExtra]
        by_cases h : b = .t ∧ a ≠ b
        · rw [ite_eq_left h]
          exact c_nonneg
        · rw [ite_eq_right h]
      show 0 ≤ inExtra a b + inTotal (b :: rest)
      exact add_nonneg he ih

private lemma bonusTotal_eq (l : List Vtx) : bonusTotal l = outTotal l + inTotal l := by
  induction l with
  | nil => simp only [bonusTotal, outTotal, inTotal, add_zero]
  | cons a tl ih =>
    cases tl with
    | nil => simp only [bonusTotal, outTotal, inTotal, add_zero]
    | cons b rest =>
      simp only [bonusTotal, outTotal, inTotal, extra]
      rw [ih]
      ring

private lemma outTotal_ge (l : List Vtx) :
    l.head? = some .s → last? l = some .t → c ≤ outTotal l := by
  induction l with
  | nil =>
    intro hhead _
    cases hhead
  | cons a tl ih =>
    intro hhead hlast
    cases tl with
    | nil =>
      cases hhead
      cases hlast
    | cons b rest =>
      cases hhead
      by_cases hb : b = .s
      · subst hb
        have ho : outExtra .s .s = 0 := by
          simp only [outExtra]
          exact ite_eq_right (by decide)
        have hrest : c ≤ outTotal (.s :: rest) := ih rfl hlast
        show c ≤ outExtra .s .s + outTotal (.s :: rest)
        rw [ho, zero_add]
        exact hrest
      · have ho : outExtra .s b = c := by
          simp only [outExtra]
          exact ite_eq_left ⟨trivial, fun h => hb h.symm⟩
        have hn : 0 ≤ outTotal (b :: rest) := outTotal_nonneg _
        show c ≤ outExtra .s b + outTotal (b :: rest)
        rw [ho]
        linarith

private lemma inTotal_ge (l : List Vtx) :
    last? l = some .t → ∀ (x : Vtx), l.head? = some x → x ≠ .t →
    c ≤ inTotal l := by
  induction l with
  | nil =>
    intro _ x hhead _
    cases hhead
  | cons a tl ih =>
    intro hlast x hhead hxt
    cases tl with
    | nil =>
      cases hlast
      cases hhead
      exact False.elim (hxt rfl)
    | cons b rest =>
      cases hhead
      by_cases h : b = .t ∧ a ≠ b
      · have hi : inExtra a b = c := by
          simp only [inExtra]
          exact ite_eq_left h
        have hn : 0 ≤ inTotal (b :: rest) := inTotal_nonneg _
        show c ≤ inExtra a b + inTotal (b :: rest)
        rw [hi]
        linarith
      · have hb : b ≠ .t := by
          intro hbt
          subst hbt
          exact h ⟨rfl, hxt⟩
        have hi0 : inExtra a b = 0 := by
          simp only [inExtra]
          exact ite_eq_right h
        have hrest : c ≤ inTotal (b :: rest) := ih hlast b rfl hb
        show c ≤ inExtra a b + inTotal (b :: rest)
        rw [hi0, zero_add]
        exact hrest

private lemma walk_lower_aux (l : List Vtx) :
    ChainAdj l → last? l = some .t → ∀ (x : Vtx), l.head? = some x →
    (H x - H .t) + bonusTotal l ≤ polyLen l := by
  induction l with
  | nil =>
    intro _ _ x hhead
    cases hhead
  | cons a tl ih =>
    intro hchain hlast x hhead
    cases tl with
    | nil =>
      cases hlast
      cases hhead
      simp only [polyLen, List.map_cons, List.map_nil,
        PathShortening.polyLen_singleton, bonusTotal, sub_self, add_zero]
      exact le_rfl
    | cons b rest =>
      cases hhead
      have hvis : visGraph.Adj a b ∧ ChainAdj (b :: rest) := hchain
      obtain ⟨hvis, hchain'⟩ := hvis
      have ih' := ih hchain' hlast b rfl
      have hstep := step_le a b hvis.2
      simp only [polyLen_cons, bonusTotal]
      linarith [hstep, ih']

private lemma walk_lower (l : List Vtx) (hw : IsWalk l) :
    3 + Real.sqrt 5 ≤ polyLen l := by
  obtain ⟨hhead, hlast, hchain⟩ := hw
  have haux := walk_lower_aux l hchain hlast .s hhead
  have hout := outTotal_ge l hhead hlast
  have hin := inTotal_ge l hlast .s hhead (by decide)
  have hbe := bonusTotal_eq l
  rw [Hs, Ht] at haux
  have hc : c = Real.sqrt 5 / 2 - 1 := rfl
  linarith [haux, hout, hin, hbe, hc]

-- Upper bound: the top walk `[s, (0,1), (3,1), t]`.

private lemma upper_valid : IsWalk [.s, .D, .P, .t] := by
  refine ⟨rfl, rfl, ?_⟩
  simp only [ChainAdj]
  exact ⟨⟨by decide, adj_s_D⟩, ⟨by decide, adj_D_P⟩, ⟨by decide, adj_P_t⟩,
    trivial⟩

private lemma upper_weight : polyLen [.s, .D, .P, .t] = 3 + Real.sqrt 5 := by
  simp only [polyLen, List.map_cons, List.map_nil,
    PathShortening.polyLen_cons_cons, PathShortening.polyLen_singleton,
    dist_sD, dist_DP, dist_Pt]
  ring

-- Minimum exists and equals `3 + √5`.

private theorem min_eq :
    IsLeast {w | ∃ l, IsWalk l ∧ polyLen l = w} (3 + Real.sqrt 5) := by
  refine ⟨?_, ?_⟩
  · exact ⟨[.s, .D, .P, .t], upper_valid, upper_weight⟩
  · rw [mem_lowerBounds]
    intro w hw
    obtain ⟨l, hl, rfl⟩ := hw
    exact walk_lower l hl


/-- Length of a graph walk, measured by its vertex list. -/
noncomputable def walkWeight {a b : Vtx} (p : visGraph.Walk a b) : ℝ :=
  PathShortening.polyLen (p.support.map coord)

private theorem last?_eq (l : List Vtx) : last? l = l.getLast? := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => rfl
      | cons y ys => exact ih

theorem head?_support {a b : Vtx} (p : visGraph.Walk a b) :
    p.support.head? = some a := by
  cases p with
  | nil => rfl
  | cons h q => rfl

private theorem last?_cons_of_ne_nil (x : Vtx) (l : List Vtx) (h : l ≠ []) :
    last? (x :: l) = last? l := by
  cases l with
  | nil => exact absurd rfl h
  | cons y ys => rfl

private theorem last?_support {a b : Vtx} (p : visGraph.Walk a b) :
    last? p.support = some b := by
  induction p with
  | nil => rfl
  | @cons u v w h p ih =>
      have h2 : last? (u :: p.support) = last? p.support :=
        last?_cons_of_ne_nil u p.support p.support_ne_nil
      rw [SimpleGraph.Walk.support_cons]
      exact h2.trans ih

private theorem chainAdj_cons_support {v w : Vtx} (p : visGraph.Walk v w) :
    ∀ {u : Vtx}, visGraph.Adj u v → ChainAdj (u :: p.support) := by
  induction p with
  | nil =>
      intro u hadj
      exact ⟨hadj, trivial⟩
  | @cons v' v'' w' h' p' ih =>
      intro u hadj
      rw [SimpleGraph.Walk.support_cons]
      exact ⟨hadj, ih h'⟩

private theorem chainAdj_support {a b : Vtx} (p : visGraph.Walk a b) :
    ChainAdj p.support := by
  cases p with
  | nil => trivial
  | @cons u v w h p' => exact chainAdj_cons_support p' h

private theorem isWalk_support (p : visGraph.Walk .s .t) : IsWalk p.support :=
  ⟨head?_support p, last?_support p, chainAdj_support p⟩

private theorem exists_walk_of_chain {a : Vtx} {l : List Vtx} (hhead : l.head? = some a)
    (hadj : ChainAdj l) {b : Vtx} (hlast : last? l = some b) :
    ∃ p : visGraph.Walk a b, p.support = l := by
  induction l generalizing a b with
  | nil => simp at hhead
  | cons x xs ih =>
      cases xs with
      | nil =>
          have hax : x = a := by simpa using hhead
          have hbx : x = b := by simpa [last?] using hlast
          subst a
          subst b
          exact ⟨.nil, SimpleGraph.Walk.support_nil⟩
      | cons y ys =>
          have hax : x = a := by simpa using hhead
          subst a
          obtain ⟨hxy, hadj'⟩ := hadj
          have hhead' : (y :: ys).head? = some y := rfl
          obtain ⟨p', hp'⟩ := ih hhead' hadj' hlast
          exact ⟨.cons hxy p', by simp [SimpleGraph.Walk.support_cons, hp']⟩

private theorem exists_walk_of_isWalk {l : List Vtx} (h : IsWalk l) : ∃ p : visGraph.Walk .s .t, p.support = l := by
  obtain ⟨hhead, hlast, hadj⟩ := h
  exact exists_walk_of_chain hhead hadj hlast

/-- Least `walkWeight` over `visGraph.Walk .s .t` equals `3 + Real.sqrt 5`. -/
theorem min_eq_walk : IsLeast {w | ∃ p : visGraph.Walk .s .t, walkWeight p = w} (3 + Real.sqrt 5) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨l, hwalk, hlen⟩ := min_eq.1
    obtain ⟨p, hp⟩ := exists_walk_of_isWalk hwalk
    exact ⟨p, by simpa only [walkWeight, hp] using hlen⟩
  · rw [mem_lowerBounds]
    intro w hw
    obtain ⟨p, hpw⟩ := hw
    have hlb : ∀ b ∈ {w | ∃ l, IsWalk l ∧ polyLen l = w}, 3 + Real.sqrt 5 ≤ b :=
      mem_lowerBounds.mp min_eq.2
    exact hlb w ⟨p.support, isWalk_support p, hpw⟩

end Cslib.Planning.MotionPlanning.TwoSquaresGraph
