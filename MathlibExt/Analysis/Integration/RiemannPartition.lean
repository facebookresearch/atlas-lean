/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Fin.Basic
public import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Riemann partitions of an interval

A partition of `[a, b]` is a strictly increasing finite sequence
`a = x₀ < x₁ < ⋯ < xₙ = b` of points. A tagged partition adds a choice of
a tag `ξₖ ∈ [xₖ₋₁, xₖ]` in each subinterval, and the Riemann sum of `f`
with respect to it is `∑ₖ f(ξₖ) (xₖ - xₖ₋₁)`. This file introduces the
two structures, the mesh (maximum subinterval length), and the basic API:
the subinterval lengths telescope to `b - a`, every tag lies in `[a, b]`,
and the Riemann sum of a constant function is that constant times `b - a`.

This is the book's set-up for the Riemann integral: the refinement bound
and the common-refinement theorem are in the companion files
`RiemannSumRefinement.lean` and `RiemannCommonRefinement.lean`.

Mathlib's `BoxIntegral` API has tagged prepartitions of boxes in `ℝⁿ`
(`BoxIntegral.TaggedPrepartition`) and their integral sums, but no
one-dimensional `Fin`-indexed partition of `[a, b]`, no mesh, and no
Riemann sum in this form.

## Main definitions

* `Partition a b`: a partition of `[a, b]`.
* `TaggedPartition a b`: a partition of `[a, b]` with a tag in each subinterval.
* `Partition.mesh`: the maximum subinterval length.
* `Partition.pointSet`: the set of partition points.
* `Partition.IsRefinement`: `Q` refines `P` when every point of `P` is a point of `Q`.
* `riemannSum f T`: `∑ₖ f(ξₖ) (xₖ - xₖ₋₁)`.

## Main results

* `Partition.a_le_b`: the endpoints of a partition satisfy `a ≤ b`.
* `Partition.sum_sub_eq`: the subinterval lengths telescope to `b - a`.
* `TaggedPartition.tag_mem_Icc`: every tag lies in `[a, b]`.
* `riemannSum_const`: the Riemann sum of a constant function is `c * (b - a)`.

Source: `v1/Atlas/RealAnalysis/targets.yaml`, Definitions (Partition),
(Tag), (Riemann sum), (Refinement), "The Riemann Integral section", and
`v1/Atlas/RealAnalysis/code/Integration/Basic.lean`
(`Partition`, `TaggedPartition`, `Partition.mesh`, `Partition.pointSet`,
`Partition.IsRefinement`, `riemannSum`) and
`v1/Atlas/RealAnalysis/code/Integration/ModulusContinuity.lean`
(`Partition.sum_sub_eq`, `TaggedPartition.tag_mem_Icc`). The
`riemannSum_const` lemma is not in v1.
-/

@[expose] public section

namespace MathlibExt.Analysis.Integration

/-- A partition of the closed interval `[a, b]`: a strictly increasing finite
sequence `a = x₀ < x₁ < ⋯ < xₙ = b` of points. The field `n` is the number
of subintervals, and `points` enumerates the `n + 1` endpoints. -/
structure Partition (a b : ℝ) where
  n : ℕ
  points : Fin (n + 1) → ℝ
  ordered : StrictMono points
  first : points 0 = a
  last : points (Fin.last n) = b

variable {a b : ℝ}

/-- A tagged partition of `[a, b]`: a partition together with a choice of a
tag `ξₖ ∈ [xₖ₋₁, xₖ]` in each subinterval. -/
structure TaggedPartition (a b : ℝ) extends Partition a b where
  tags : Fin n → ℝ
  tag_mem : ∀ i : Fin n, points i.castSucc ≤ tags i ∧ tags i ≤ points i.succ

/-- The mesh (or norm) `‖x‖` of a partition: the maximum length
`maxₖ (xₖ - xₖ₋₁)` of its subintervals. Defined to be `0` for the trivial
partition with `n = 0`. -/
noncomputable def Partition.mesh (P : Partition a b) : ℝ :=
  if h : P.n = 0 then 0
  else
    Finset.sup' (Finset.univ (α := Fin P.n))
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero h⟩⟩)
      (fun i => P.points i.succ - P.points i.castSucc)

/-- The underlying set `{x₀, x₁, …, xₙ}` of points of a partition. -/
def Partition.pointSet (P : Partition a b) : Set ℝ :=
  Set.range P.points

/-- `Q` is a refinement of `P` if every point of `P` appears in `Q`, i.e. the
underlying point set of `P` is contained in that of `Q`. -/
def Partition.IsRefinement (Q P : Partition a b) : Prop :=
  P.pointSet ⊆ Q.pointSet

/-- The Riemann sum `S_f(x, ξ) = ∑ₖ f(ξₖ) (xₖ - xₖ₋₁)` of a function `f`
with respect to a tagged partition `T`. -/
noncomputable def riemannSum (f : ℝ → ℝ) (T : TaggedPartition a b) : ℝ :=
  ∑ i : Fin T.n, f (T.tags i) * (T.points i.succ - T.points i.castSucc)

/-- The endpoints of a partition satisfy `a ≤ b`: the first point is `a`,
the last point is `b`, and the points are increasing. -/
lemma Partition.a_le_b (P : Partition a b) : a ≤ b := by
  have hle : P.points (0 : Fin (P.n + 1)) ≤ P.points (Fin.last P.n) :=
    P.ordered.monotone (Fin.zero_le _)
  rw [P.first, P.last] at hle
  exact hle

/-- If `a < b`, then any partition of `[a, b]` has at least one subinterval,
i.e. `0 < P.n`. -/
lemma Partition.n_pos_of_lt (hab : a < b) (P : Partition a b) : 0 < P.n := by
  by_contra h
  have hn : P.n = 0 := by omega
  have hlast : Fin.last P.n = (0 : Fin (P.n + 1)) := by ext; simp [hn]
  have hP := P.last; rw [hlast] at hP
  linarith [P.first]

/-- If `a < b`, then the mesh of any partition of `[a, b]` is strictly positive. -/
lemma Partition.mesh_pos_of_lt (hab : a < b) (P : Partition a b) :
    0 < P.mesh := by
  have hn : P.n ≠ 0 := (P.n_pos_of_lt hab).ne'
  have i₀ : Fin P.n := ⟨0, Nat.pos_of_ne_zero hn⟩
  unfold Partition.mesh
  rw [dite_eq_right hn]
  have hlt : P.points i₀.castSucc < P.points i₀.succ :=
    P.ordered Fin.castSucc_lt_succ
  calc (0 : ℝ) < P.points i₀.succ - P.points i₀.castSucc := sub_pos.mpr hlt
    _ ≤ Finset.sup' Finset.univ _
          (fun (i : Fin P.n) => P.points i.succ - P.points i.castSucc) :=
        Finset.le_sup' (fun (i : Fin P.n) => P.points i.succ - P.points i.castSucc)
          (Finset.mem_univ i₀)

/-- The Riemann sum over a trivial tagged partition (with `n = 0` subintervals)
is `0`, since it is an empty sum. -/
lemma riemannSum_eq_zero_of_n_eq_zero (f : ℝ → ℝ) (T : TaggedPartition a b)
    (h : T.n = 0) : riemannSum f T = 0 := by
  unfold riemannSum
  have : IsEmpty (Fin T.n) := by rw [h]; infer_instance
  exact Fintype.sum_empty _

/-- Each subinterval `[xᵢ, xᵢ₊₁]` of a partition has nonnegative length. -/
lemma Partition.succ_sub_castSucc_nonneg (P : Partition a b) (i : Fin P.n) :
    0 ≤ P.points i.succ - P.points i.castSucc :=
  sub_nonneg.mpr (P.ordered.monotone Fin.castSucc_lt_succ.le)

/-- Each subinterval length `xᵢ₊₁ - xᵢ` of a partition is bounded above by
the partition's mesh (i.e., the maximum subinterval length). -/
lemma Partition.le_mesh (P : Partition a b) (i : Fin P.n) :
    P.points i.succ - P.points i.castSucc ≤ P.mesh := by
  have hne : P.n ≠ 0 := Fin.pos i |>.ne'
  show P.points i.succ - P.points i.castSucc ≤
    (if h : P.n = 0 then (0 : ℝ) else Finset.sup' (Finset.univ (α := Fin P.n))
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero h⟩⟩)
      (fun i : Fin P.n => P.points i.succ - P.points i.castSucc))
  rw [dite_eq_right hne]
  exact Finset.le_sup' (fun i : Fin P.n => P.points i.succ - P.points i.castSucc)
    (Finset.mem_univ i)

/-- The subinterval lengths of a partition of `[a, b]` telescope to `b - a`:
`∑ᵢ (xᵢ₊₁ - xᵢ) = b - a`. -/
lemma Partition.sum_sub_eq (P : Partition a b) :
    ∑ i : Fin P.n, (P.points i.succ - P.points i.castSucc) = b - a := by
  set g : ℕ → ℝ := fun j => if h : j < P.n + 1 then P.points ⟨j, h⟩ else 0
  suffices h : ∑ i ∈ Finset.range P.n, (g (i + 1) - g i) = b - a by
    rw [← h, ← Fin.sum_univ_eq_sum_range (fun i => g (i + 1) - g i)]
    congr 1; ext i
    simp only [g, show (↑i : ℕ) + 1 < P.n + 1 from by omega,
      show (↑i : ℕ) < P.n + 1 from by omega, dite_eq_left]
    congr 1
  rw [Finset.sum_range_sub]
  simp only [g, show P.n < P.n + 1 from by omega, show (0 : ℕ) < P.n + 1 from by omega,
    dite_eq_left]
  rw [show (⟨P.n, by omega⟩ : Fin (P.n + 1)) = Fin.last P.n from Fin.ext rfl,
    show (⟨0, by omega⟩ : Fin (P.n + 1)) = (0 : Fin (P.n + 1)) from Fin.ext rfl,
    P.last, P.first]

/-- Every tag `ξᵢ` of a tagged partition of `[a, b]` lies in `[a, b]`. -/
lemma TaggedPartition.tag_mem_Icc (T : TaggedPartition a b) (i : Fin T.n) :
    T.tags i ∈ Set.Icc a b := by
  refine ⟨?_, ?_⟩
  · calc a = T.points 0 := T.first.symm
      _ ≤ T.points i.castSucc := T.ordered.monotone (Fin.zero_le _)
      _ ≤ T.tags i := (T.tag_mem i).1
  · calc T.tags i ≤ T.points i.succ := (T.tag_mem i).2
      _ ≤ T.points (Fin.last T.n) := T.ordered.monotone (Fin.le_last _)
      _ = b := T.last

/-- The Riemann sum of a constant function `c` over any tagged partition of
`[a, b]` is `c * (b - a)`. -/
lemma riemannSum_const (c : ℝ) (T : TaggedPartition a b) :
    riemannSum (fun _ => c) T = c * (b - a) := by
  unfold riemannSum
  rw [← Finset.mul_sum, T.toPartition.sum_sub_eq]

end MathlibExt.Analysis.Integration
