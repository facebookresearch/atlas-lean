/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Knot.RegularProjection

import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FinCases

@[expose] public section

namespace RegularProjectionTest

open MathlibExt.Topology.Knot.RegularProjection
open MathlibExt.Topology.Knot.Euclidean
open MathlibExt.Geometry.Euclidean.Ropelength

/-- Opposite darts have the same over/under status, while a quarter
turn changes it. -/
example (D : DartDiagram) (d : D.Dart) :
    D.isOver (D.opposite d) = D.isOver d ∧
      D.isOver (D.rot d) = !(D.isOver d) :=
  ⟨D.isOver_opposite d, D.isOver_rot d⟩

/-- Traversal as a permutation agrees with the direct next-dart map. -/
example (D : DartDiagram) (d : D.Dart) : D.nextPerm d = D.next d :=
  D.nextPerm_apply d

/-- The empty diagram with `k` isolated components has no crossings,
is alternating, and has component count `k`. -/
example (k : ℕ) :
    (DartDiagram.empty k).crossingCount = 0 ∧
      (DartDiagram.empty k).IsAlternating ∧
        (DartDiagram.empty k).componentCount = k :=
  ⟨DartDiagram.crossingCount_empty k, DartDiagram.isAlternating_empty k,
    DartDiagram.componentCount_empty k⟩

/-- One dart crossing whose adjacent darts are paired. Its two strand
cycles alternate, showing the local traversal condition is satisfiable. -/
def oneCrossingAlternating : DartDiagram where
  Vertex := Unit
  pair := fun d => (d.1, Equiv.swap (0 : Fin 4) 1 (Equiv.swap (2 : Fin 4) 3 d.2))
  pair_involutive := by
    intro d
    obtain ⟨v, i⟩ := d
    fin_cases i <;> rfl
  pair_ne_self := by
    intro d
    obtain ⟨v, i⟩ := d
    fin_cases i <;> simp [Equiv.swap_apply_def]
  isolated := 0

example : oneCrossingAlternating.crossingCount = 1 :=
  Fintype.card_unit

example : oneCrossingAlternating.IsAlternating := by
  intro d
  obtain ⟨v, i⟩ := d
  fin_cases i <;> simp [oneCrossingAlternating, DartDiagram.next,
    DartDiagram.isOver, DartDiagram.opposite, DartDiagram.rot,
    Equiv.swap_apply_def]

/-- The one-crossing diagram is a single unoriented component. The
oriented traversal has two cycles, `(0 3)` and `(1 2)`, which are the
two orientations of this one component, so component counting must
use unoriented strand connectivity. -/
example : oneCrossingAlternating.componentCount = 1 := by
  have h : ∀ d : oneCrossingAlternating.Dart,
      oneCrossingAlternating.SameComponent d ((), 0) := by
    intro d
    obtain ⟨v, i⟩ := d
    fin_cases i
    · exact Relation.EqvGen.refl _
    · exact oneCrossingAlternating.sameComponent_pair ((), 1)
    · exact oneCrossingAlternating.sameComponent_opposite ((), 2)
    · exact Relation.EqvGen.trans _ _ _
        (oneCrossingAlternating.sameComponent_pair ((), 3))
        (oneCrossingAlternating.sameComponent_opposite ((), 2))
  have hsub :
      Subsingleton (Quotient oneCrossingAlternating.componentSetoid) := by
    constructor
    intro q r
    obtain ⟨d, rfl⟩ := Quotient.exists_rep q
    obtain ⟨e, rfl⟩ := Quotient.exists_rep r
    apply Quotient.sound
    exact Relation.EqvGen.trans _ _ _ (h d)
      (Relation.EqvGen.symm _ _ (h e))
  have hcard :
      Nat.card (Quotient oneCrossingAlternating.componentSetoid) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨⟦((), 0)⟧⟩⟩
  simpa [DartDiagram.componentCount, oneCrossingAlternating] using hcard

/-- Plane and height recover the first two and third coordinates. -/
example (x : R3) :
    plane x 0 = x 0 ∧ plane x 1 = x 1 ∧ height x = x 2 :=
  ⟨rfl, rfl, rfl⟩

/-- Plane plus height determine a point in `R3`. -/
example {x y : R3} (hplane : plane x = plane y)
    (hheight : height x = height y) : x = y :=
  eq_of_plane_eq_of_height_eq hplane hheight

/-- Distinct parameter points over one projected point have different
heights, derived from injectivity and disjointness. -/
example {n : ℕ} (L : ParametrizedLink n)
    {a b : ParamPoint n} (hab : a ≠ b)
    (hproj : L.projPoint a = L.projPoint b) :
    L.heightAt a ≠ L.heightAt b :=
  L.heightAt_ne_of_projPoint_eq_of_ne hab hproj

/-- A regular crossing has exactly two parameter preimages. -/
example {n : ℕ} (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (p : L.Crossing) :
    ∃ a b : ParamPoint n, a ≠ b ∧ L.projPoint a = p.1 ∧
      L.projPoint b = p.1 ∧ ∀ c : ParamPoint n,
        L.projPoint c = p.1 → c = a ∨ c = b :=
  L.exists_pair_of_mem_doublePointSet hreg p.2

/-- The chosen over and under points satisfy their specifications and
the under point is strictly lower. -/
example {n : ℕ} (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (p : L.Crossing) :
    L.IsOverPoint p (L.overPoint hreg p) ∧
      L.IsUnderPoint p (L.underPoint hreg p) ∧
        L.heightAt (L.underPoint hreg p) <
          L.heightAt (L.overPoint hreg p) :=
  ⟨L.isOverPoint_overPoint hreg p, L.isUnderPoint_underPoint hreg p,
    L.heightAt_underPoint_lt_overPoint hreg p⟩

/-- Projected component traces assemble to the projection of the whole
trace. -/
example {n : ℕ} (L : ParametrizedLink n) :
    ⋃ i, Set.range (L.projCurve i) = plane '' L.trace :=
  L.iUnion_range_projCurve

/-- One traversal step stays in the same strand cycle, and isolated
components are counted in the component total. -/
example (D : DartDiagram) (d : D.Dart) :
    D.nextPerm.SameCycle d (D.next d) ∧
      D.isolated ≤ D.componentCount :=
  ⟨D.sameCycle_next d, D.isolated_le_componentCount⟩

/-- The over and under points project to the crossing and exhaust its
preimage. -/
example {n : ℕ} (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (p : L.Crossing) (c : ParamPoint n) (hc : L.projPoint c = p.1) :
    L.projPoint (L.overPoint hreg p) = p.1 ∧
      L.projPoint (L.underPoint hreg p) = p.1 ∧
        (c = L.overPoint hreg p ∨ c = L.underPoint hreg p) :=
  ⟨L.projPoint_overPoint hreg p, L.projPoint_underPoint hreg p,
    L.eq_overPoint_or_eq_underPoint_of_projPoint_eq hreg p c hc⟩

/-- Crossing count is zero with no double points and positive once a
crossing exists. -/
example {n : ℕ} (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (h : L.doublePointSet = ∅) : L.crossingCount hreg = 0 :=
  L.crossingCount_eq_zero_of_doublePointSet_eq_empty hreg h

example {n : ℕ} (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (p : L.Crossing) : 0 < L.crossingCount hreg :=
  L.crossingCount_pos_of_crossing hreg p

/-- The crossing number of a type is bounded by any regular projection
of any isotopic representative, is finite as soon as one regular
representative exists, and depends only on the isotopy type. -/
example {n : ℕ} {L L' : ParametrizedLink n} (h : L'.Isotopic L)
    (hreg : L'.IsRegularProjection) :
    L.crossingNumber ≤ (L'.crossingCount hreg : ℕ∞) ∧
      L.crossingNumber < ⊤ ∧
        L.crossingNumber = L'.crossingNumber :=
  ⟨L.crossingNumber_le_of_isotopic_of_isRegularProjection h hreg,
    L.crossingNumber_lt_top_of_isotopic_of_isRegularProjection h hreg,
    ParametrizedLink.crossingNumber_eq_of_isotopic h.symm⟩

/-- A crossing-free regular representative forces type crossing
number zero. -/
example {n : ℕ} {L L' : ParametrizedLink n} (h : L'.Isotopic L)
    (hreg : L'.IsRegularProjection) (hempty : L'.doublePointSet = ∅) :
    L.crossingNumber = 0 :=
  L.crossingNumber_eq_zero_of_isotopic_of_doublePointSet_eq_empty
    h hreg hempty

/-- At one crossing, the over preimage has over status, the under
preimage does not, and two distinct preimages of one crossing always
have opposite status. -/
example {n : ℕ} (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (p : L.Crossing)
    (ho : L.IsCrossingPreimage (L.overPoint hreg p))
    (hu : L.IsCrossingPreimage (L.underPoint hreg p)) :
    L.isOverAt hreg (L.overPoint hreg p) ho = true ∧
      L.isOverAt hreg (L.underPoint hreg p) hu = false :=
  ⟨L.isOverAt_overPoint hreg p ho, L.isOverAt_underPoint hreg p hu⟩

example {n : ℕ} (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    {a b : ParamPoint n} (ha : L.IsCrossingPreimage a)
    (hb : L.IsCrossingPreimage b) (hab : a ≠ b)
    (hproj : L.projPoint a = L.projPoint b) :
    L.isOverAt hreg a ha ≠ L.isOverAt hreg b hb :=
  L.isOverAt_ne_of_ne_of_projPoint_eq hreg ha hb hab hproj

/-- A crossing-free regular projection is alternating, so its type
admits an alternating diagram, and that property transfers across
isotopy. -/
example {n : ℕ} {L₁ L₂ : ParametrizedLink n} (h : L₁.Isotopic L₂)
    (hreg : L₁.IsRegularProjection) (hempty : L₁.doublePointSet = ∅) :
    L₂.AdmitsAlternatingDiagram :=
  ParametrizedLink.AdmitsAlternatingDiagram.of_isotopic h
    (L₁.admitsAlternatingDiagram_of_doublePointSet_eq_empty hreg hempty)

/-- A test parameter point on the unique component, at a chosen time
in the fundamental period. -/
def testPoint (t : ℝ) (ht : t ∈ Set.Ico 0 (2 * Real.pi)) :
    ParamPoint 1 :=
  ⟨0, t, ht⟩

theorem testPoint_t {t : ℝ} {ht : t ∈ Set.Ico 0 (2 * Real.pi)} :
    (testPoint t ht).t = t :=
  rfl

def p0 : ParamPoint 1 :=
  testPoint 0 (by
    simp only [Set.mem_Ico]
    exact ⟨le_rfl, by linarith [Real.pi_pos]⟩)

def p1 : ParamPoint 1 :=
  testPoint 1 (by
    simp only [Set.mem_Ico]
    exact ⟨by norm_num, by linarith [Real.pi_gt_three]⟩)

def p2 : ParamPoint 1 :=
  testPoint 2 (by
    simp only [Set.mem_Ico]
    exact ⟨by norm_num, by linarith [Real.pi_gt_three]⟩)

def p5 : ParamPoint 1 :=
  testPoint 5 (by
    simp only [Set.mem_Ico]
    exact ⟨by norm_num, by linarith [Real.pi_gt_three]⟩)

def p6 : ParamPoint 1 :=
  testPoint 6 (by
    simp only [Set.mem_Ico]
    exact ⟨by norm_num, by linarith [Real.pi_gt_three]⟩)

theorem p0_t : p0.t = 0 := rfl

theorem p1_t : p1.t = 1 := rfl

theorem p2_t : p2.t = 2 := rfl

theorem p5_t : p5.t = 5 := rfl

theorem p6_t : p6.t = 6 := rfl

/-- Ordinary (non-wrapping) arc: the midpoint time `1` lies in the
open arc from `0` to `2`. -/
example : inOpenArc p0 p2 p1 := by
  simp only [inOpenArc, p0_t, p1_t, p2_t]
  norm_num

/-- Wrap-around arc, upper part: time `6` lies in the open arc from
`5` around through `2π` to `1`. -/
example : inOpenArc p5 p1 p6 := by
  simp only [inOpenArc, p1_t, p5_t, p6_t]
  norm_num

/-- Wrap-around arc, lower part: time `0` lies in the open arc from
`5` around through `0` to `1`. -/
example : inOpenArc p5 p1 p0 := by
  simp only [inOpenArc, p0_t, p1_t, p5_t]
  norm_num

/-- Endpoints are excluded from the open arc. -/
example : ¬ inOpenArc p0 p2 p0 ∧ ¬ inOpenArc p0 p2 p2 := by
  simp only [inOpenArc, p0_t, p2_t]
  norm_num

/-- A time outside the ordinary arc is not in it, and an interior
time of the complementary arc is not in the wrap arc either. -/
example : ¬ inOpenArc p0 p2 p5 ∧ ¬ inOpenArc p5 p1 p2 := by
  simp only [inOpenArc, p0_t, p1_t, p2_t, p5_t]
  norm_num

/-- Cyclic adjacency is exactly its five defining components, and a
crossing preimage inside the open arc blocks adjacency. -/
example {n : ℕ} (L : ParametrizedLink n)
    {a b c : ParamPoint n} (hc : L.IsCrossingPreimage c)
    (hcomp : c.comp = a.comp) (harc : inOpenArc a b c) :
    ¬ L.CyclicallyAdjacent a b :=
  fun hadj => hadj.2.2.2.2 c hc hcomp harc

/-- The alternating condition is nonvacuous: a cyclically adjacent
pair with equal over/under status refutes it. -/
example {n : ℕ} (L : ParametrizedLink n)
    (hreg : L.IsRegularProjection) {a b : ParamPoint n}
    (hadj : L.CyclicallyAdjacent a b)
    (heq : L.isOverAt hreg a hadj.2.2.1 = L.isOverAt hreg b hadj.2.2.2.1) :
    ¬ L.IsAlternatingProjection hreg :=
  fun halt => halt a b hadj heq

end RegularProjectionTest
