/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Dart diagrams and regular projections of Euclidean links
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import MathlibExt.Topology.Knot.EuclideanLink

import Mathlib.Tactic.FinCases

@[expose] public section

open MathlibExt.Topology.Knot.Euclidean
open MathlibExt.Geometry.Euclidean.Ropelength

namespace MathlibExt.Topology.Knot.RegularProjection

/-!
# Normalized dart diagrams

A dart diagram is a finite four-valent shadow presented without local
frames: a crossing has four darts `Vertex × Fin 4`, in cyclic order.
Labels `0` and `2` are the two darts of the over-strand, labels `1` and
`3` are the two darts of the under-strand, and opposite darts differ by
`2`. A fixed-point-free involution `pair` glues darts across edge
segments. Strand traversal is `next d = opposite (pair d)`: cross the
edge segment, then go straight through the next crossing.

The `isolated` field counts components with no crossings; omitting it
would identify all crossingless unlinks. This is a combinatorial dart
layer. It does not by itself assert planarity or that a given Euclidean
link projects to the diagram; those ties are the concrete regular
projection definitions later in this file and the still-unproved
representation theorems listed there.
-/

/-- A normalized finite dart diagram. -/
structure DartDiagram where
  Vertex : Type
  [vertexFintype : Fintype Vertex]
  [vertexDecidableEq : DecidableEq Vertex]
  pair : Vertex × Fin 4 → Vertex × Fin 4
  pair_involutive : ∀ d, pair (pair d) = d
  pair_ne_self : ∀ d, pair d ≠ d
  isolated : ℕ

namespace DartDiagram

/-- Darts of a diagram: one incident half-edge at one crossing. -/
abbrev Dart (D : DartDiagram) : Type :=
  D.Vertex × Fin 4

instance (D : DartDiagram) : Fintype D.Dart := by
  letI := D.vertexFintype
  infer_instance

instance (D : DartDiagram) : DecidableEq D.Dart := by
  letI := D.vertexDecidableEq
  infer_instance

/-- Number of crossings. -/
def crossingCount (D : DartDiagram) : ℕ := by
  letI := D.vertexFintype
  exact Fintype.card D.Vertex

/-- Rotate a dart one step counterclockwise around its crossing. -/
def rot (D : DartDiagram) (d : D.Dart) : D.Dart :=
  (d.1, d.2 + 1)

/-- The dart opposite `d` at the same crossing. -/
def opposite (D : DartDiagram) (d : D.Dart) : D.Dart :=
  D.rot (D.rot d)

@[simp]
theorem opposite_eq {D : DartDiagram} (d : D.Dart) :
    D.opposite d = (d.1, d.2 + 2) := by
  obtain ⟨v, i⟩ := d
  fin_cases i <;> simp [DartDiagram.opposite, DartDiagram.rot]

/-- Whether a dart lies on the over-strand at its crossing. -/
def isOver (D : DartDiagram) (d : D.Dart) : Bool :=
  decide (d.2 = 0 ∨ d.2 = 2)

theorem isOver_opposite (D : DartDiagram) (d : D.Dart) :
    D.isOver (D.opposite d) = D.isOver d := by
  obtain ⟨v, i⟩ := d
  fin_cases i <;> simp [DartDiagram.isOver, DartDiagram.opposite, DartDiagram.rot]

theorem isOver_rot (D : DartDiagram) (d : D.Dart) :
    D.isOver (D.rot d) = !(D.isOver d) := by
  obtain ⟨v, i⟩ := d
  fin_cases i <;> simp [DartDiagram.isOver, DartDiagram.rot]

/-- The edge-pairing involution as a permutation of darts. -/
def pairPerm (D : DartDiagram) : Equiv.Perm D.Dart where
  toFun := D.pair
  invFun := D.pair
  left_inv := D.pair_involutive
  right_inv := D.pair_involutive

/-- Quarter-turn rotation as a permutation of darts. -/
def rotPerm (D : DartDiagram) : Equiv.Perm D.Dart where
  toFun := D.rot
  invFun := fun d => (d.1, d.2 - 1)
  left_inv := by intro d; simp [DartDiagram.rot]
  right_inv := by intro d; simp [DartDiagram.rot]

/-- Straight-through motion at a crossing as a permutation. -/
def oppositePerm (D : DartDiagram) : Equiv.Perm D.Dart :=
  D.rotPerm ^ 2

/-- One step of strand traversal: pair across an edge segment, then go
straight through the next crossing. -/
def next (D : DartDiagram) (d : D.Dart) : D.Dart :=
  D.opposite (D.pair d)

/-- Strand traversal as a permutation. -/
def nextPerm (D : DartDiagram) : Equiv.Perm D.Dart :=
  D.oppositePerm * D.pairPerm

@[simp]
theorem nextPerm_apply (D : DartDiagram) (d : D.Dart) :
    D.nextPerm d = D.next d := by
  show D.oppositePerm (D.pairPerm d) = D.next d
  simp [DartDiagram.next, DartDiagram.oppositePerm, DartDiagram.pairPerm,
    DartDiagram.rotPerm, DartDiagram.opposite, Equiv.Perm.coe_pow]

@[simp]
theorem pairPerm_apply (D : DartDiagram) (d : D.Dart) :
    D.pairPerm d = D.pair d :=
  rfl

@[simp]
theorem rotPerm_apply (D : DartDiagram) (d : D.Dart) :
    D.rotPerm d = D.rot d :=
  rfl

@[simp]
theorem oppositePerm_apply (D : DartDiagram) (d : D.Dart) :
    D.oppositePerm d = D.opposite d := by
  simp [DartDiagram.oppositePerm, DartDiagram.rotPerm, DartDiagram.opposite,
    Equiv.Perm.coe_pow]

/-- One traversal step stays in the same strand cycle, by definition of
the cycle relation. -/
theorem sameCycle_next (D : DartDiagram) (d : D.Dart) :
    D.nextPerm.SameCycle d (D.next d) :=
  ⟨1, by simp⟩

/-- A dart diagram is alternating when consecutive crossings on every
strand have opposite over/under status. Crossingless components are
alternating by the empty condition. -/
def IsAlternating (D : DartDiagram) : Prop :=
  ∀ d, D.isOver (D.next d) ≠ D.isOver d

instance (D : DartDiagram) : Decidable D.IsAlternating := by
  unfold DartDiagram.IsAlternating
  infer_instance

/-- Unoriented strand connectivity of darts: the equivalence
generated by crossing an edge segment (`pair`) and by going straight
through a crossing (`opposite`). The oriented traversal `next`
traverses every component twice, once in each orientation, so the
cycles of `nextPerm` are not themselves the components. -/
def SameComponent (D : DartDiagram) : D.Dart → D.Dart → Prop :=
  Relation.EqvGen (fun x y => y = D.pair x ∨ y = D.opposite x)

/-- The setoid of unoriented strand connectivity. -/
def componentSetoid (D : DartDiagram) : Setoid D.Dart :=
  Relation.EqvGen.setoid (fun x y => y = D.pair x ∨ y = D.opposite x)

theorem sameComponent_pair (D : DartDiagram) (d : D.Dart) :
    D.SameComponent d (D.pair d) :=
  Relation.EqvGen.rel _ _ (Or.inl rfl)

theorem sameComponent_opposite (D : DartDiagram) (d : D.Dart) :
    D.SameComponent d (D.opposite d) :=
  Relation.EqvGen.rel _ _ (Or.inr rfl)

/-- One oriented traversal step stays in the same component. -/
theorem sameComponent_next (D : DartDiagram) (d : D.Dart) :
    D.SameComponent d (D.next d) :=
  Relation.EqvGen.trans _ _ _ (D.sameComponent_pair d)
    (D.sameComponent_opposite _)

/-- Number of components: unoriented strand-connectivity classes of
darts plus the recorded isolated crossingless components. -/
noncomputable def componentCount (D : DartDiagram) : ℕ :=
  Nat.card (Quotient D.componentSetoid) + D.isolated

/-- Isolated crossingless components are counted in the total. -/
theorem isolated_le_componentCount (D : DartDiagram) :
    D.isolated ≤ D.componentCount :=
  Nat.le_add_left _ _

/-- The empty dart diagram with a prescribed number of isolated
components. It is alternating by convention and by the definition. -/
def empty (isolated : ℕ) : DartDiagram where
  Vertex := PEmpty
  pair := fun d => d.1.elim
  pair_involutive := fun d => d.1.elim
  pair_ne_self := fun d => d.1.elim
  isolated := isolated

@[simp]
theorem crossingCount_empty (k : ℕ) : (empty k).crossingCount = 0 := by
  unfold DartDiagram.crossingCount DartDiagram.empty
  exact Fintype.card_pempty

theorem isAlternating_empty (k : ℕ) : (empty k).IsAlternating := by
  intro d
  exact d.1.elim

theorem componentCount_empty (k : ℕ) : (empty k).componentCount = k := by
  unfold DartDiagram.componentCount DartDiagram.empty
  simp

end DartDiagram

/-- Euclidean plane for the fixed standard projection frame. -/
abbrev R2 : Type := EuclideanSpace ℝ (Fin 2)

/-- Standard projection forgetting the third coordinate. -/
def plane (x : R3) : R2 :=
  WithLp.toLp 2 (fun i => x (Fin.castSucc i))

/-- Height in the fixed standard projection frame. -/
def height (x : R3) : ℝ :=
  x 2

theorem eq_of_plane_eq_of_height_eq {x y : R3}
    (hplane : plane x = plane y) (hheight : height x = height y) :
    x = y := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i
  · exact congrFun (congrArg WithLp.ofLp hplane) 0
  · exact congrFun (congrArg WithLp.ofLp hplane) 1
  · exact hheight

/-- A point of a parametrized link represented by a component and one
parameter in the fundamental half-open period. -/
structure ParamPoint (n : ℕ) where
  comp : Fin n
  t : ℝ
  ht : t ∈ Set.Ico 0 (2 * Real.pi)

@[ext]
theorem ParamPoint.ext {n : ℕ} {a b : ParamPoint n}
    (hcomp : a.comp = b.comp) (ht : a.t = b.t) : a = b := by
  cases a
  cases b
  cases hcomp
  cases ht
  rfl

end MathlibExt.Topology.Knot.RegularProjection

namespace MathlibExt.Topology.Knot.Euclidean

/-- The Euclidean point represented by a parameter point. -/
def ParametrizedLink.point {n : ℕ} (L : ParametrizedLink n)
    (a : RegularProjection.ParamPoint n) : R3 :=
  (L.component a.comp).curve a.t

/-- The projected curve of one component. -/
def ParametrizedLink.projCurve {n : ℕ} (L : ParametrizedLink n)
    (i : Fin n) : ℝ → RegularProjection.R2 :=
  RegularProjection.plane ∘ (L.component i).curve

/-- The projected point represented by a parameter point. -/
def ParametrizedLink.projPoint {n : ℕ} (L : ParametrizedLink n)
    (a : RegularProjection.ParamPoint n) : RegularProjection.R2 :=
  RegularProjection.plane (L.point a)

/-- The projected derivative vector at a parameter point. This is the
plane projection of the ambient derivative; identifying it with the
derivative of the projected curve is a separate calculus lemma. -/
noncomputable def ParametrizedLink.tangent {n : ℕ} (L : ParametrizedLink n)
    (a : RegularProjection.ParamPoint n) : RegularProjection.R2 :=
  RegularProjection.plane (deriv (L.component a.comp).curve a.t)

/-- Height of a parameter point in the standard frame. -/
def ParametrizedLink.heightAt {n : ℕ} (L : ParametrizedLink n)
    (a : RegularProjection.ParamPoint n) : ℝ :=
  RegularProjection.height (L.point a)

/-- Projected points represented by at least two distinct parameter
points. -/
def ParametrizedLink.doublePointSet {n : ℕ} (L : ParametrizedLink n) :
    Set RegularProjection.R2 :=
  {p | ∃ a b : RegularProjection.ParamPoint n, a ≠ b ∧ L.projPoint a = p ∧ L.projPoint b = p}

/-- Regularity of the standard projection. This is a Prop-valued
structure over definitions from the link; it contains no chosen diagram,
crossing labels, or over/under data. Height distinctness at a double
point is proved below from injectivity and disjointness. -/
structure ParametrizedLink.IsRegularProjection {n : ℕ}
    (L : ParametrizedLink n) : Prop where
  cuspFree : ∀ a : RegularProjection.ParamPoint n, L.tangent a ≠ 0
  finiteDouble : L.doublePointSet.Finite
  noTriple : ∀ a b c : RegularProjection.ParamPoint n,
    L.projPoint a = L.projPoint b → L.projPoint b = L.projPoint c →
      a = b ∨ b = c ∨ a = c
  transverse : ∀ a b : RegularProjection.ParamPoint n, a ≠ b →
    L.projPoint a = L.projPoint b →
      LinearIndependent ℝ ![L.tangent a, L.tangent b]

/-- If two distinct parameter points have the same projection, their
heights differ. This is forced by component injectivity in one period
and pairwise disjoint component traces; over/under is therefore derived
from the parametrization rather than chosen. -/
theorem ParametrizedLink.heightAt_ne_of_projPoint_eq_of_ne {n : ℕ}
    (L : ParametrizedLink n) {a b : RegularProjection.ParamPoint n} (hab : a ≠ b)
    (hproj : L.projPoint a = L.projPoint b) :
    L.heightAt a ≠ L.heightAt b := by
  intro hheight
  apply hab
  have hpoint : L.point a = L.point b :=
    RegularProjection.eq_of_plane_eq_of_height_eq hproj hheight
  by_cases hcomp : a.comp = b.comp
  · have ht : a.t = b.t := by
      have hcompFun : L.component a.comp = L.component b.comp :=
        congrArg L.component hcomp
      have hpoint' : (L.component a.comp).curve a.t =
          (L.component b.comp).curve b.t := hpoint
      rw [← hcompFun] at hpoint'
      exact (L.component a.comp).injOn a.ht b.ht hpoint'
    exact RegularProjection.ParamPoint.ext hcomp ht
  · exfalso
    have hdis := L.pairwiseDisjoint (Set.mem_univ a.comp)
      (Set.mem_univ b.comp) hcomp
    have ha : (L.component a.comp).curve a.t ∈
        Set.range (L.component a.comp).curve := ⟨a.t, rfl⟩
    have hb : (L.component a.comp).curve a.t ∈
        Set.range (L.component b.comp).curve := ⟨b.t, hpoint.symm⟩
    exact Set.disjoint_left.mp hdis ha hb

/-- A crossing of the standard projection, as a point of the defined
double-point set. -/
abbrev ParametrizedLink.Crossing {n : ℕ} (L : ParametrizedLink n) : Type :=
  {p : RegularProjection.R2 // p ∈ L.doublePointSet}

/-- Crossing count of one regular projection. The regularity proof is
the finiteness gate; using `Nat.card` of the crossing subtype makes the
value proof-independent by definition. -/
noncomputable def ParametrizedLink.crossingCount {n : ℕ}
    (L : ParametrizedLink n) (_h : L.IsRegularProjection) : ℕ :=
  Nat.card L.Crossing

theorem ParametrizedLink.crossingCount_eq_of_isRegularProjection {n : ℕ}
    (L : ParametrizedLink n) (h₁ h₂ : L.IsRegularProjection) :
    L.crossingCount h₁ = L.crossingCount h₂ :=
  rfl

/-- Every point of the double-point set has exactly two parameter
preimages under a regular projection. -/
theorem ParametrizedLink.exists_pair_of_mem_doublePointSet {n : ℕ}
    (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    {p : RegularProjection.R2} (hp : p ∈ L.doublePointSet) :
    ∃ a b : RegularProjection.ParamPoint n, a ≠ b ∧ L.projPoint a = p ∧ L.projPoint b = p ∧
      ∀ c : RegularProjection.ParamPoint n, L.projPoint c = p → c = a ∨ c = b := by
  obtain ⟨a, b, hab, ha, hb⟩ := hp
  refine ⟨a, b, hab, ha, hb, fun c hc => ?_⟩
  have hab' : L.projPoint a = L.projPoint b := ha.trans hb.symm
  have hbc : L.projPoint b = L.projPoint c := hb.trans hc.symm
  rcases hreg.noTriple a b c hab' hbc with h | h | h
  · exact absurd h hab
  · exact Or.inr h.symm
  · exact Or.inl h.symm

/-- Specification of the over-strand preimage at a crossing: it lies
over the crossing point and every other preimage is strictly lower. -/
def ParametrizedLink.IsOverPoint {n : ℕ} (L : ParametrizedLink n)
    (p : L.Crossing) (a : RegularProjection.ParamPoint n) : Prop :=
  L.projPoint a = p.1 ∧ ∀ b : RegularProjection.ParamPoint n,
    L.projPoint b = p.1 → b = a ∨ L.heightAt b < L.heightAt a

/-- Specification of the under-strand preimage at a crossing. -/
def ParametrizedLink.IsUnderPoint {n : ℕ} (L : ParametrizedLink n)
    (p : L.Crossing) (a : RegularProjection.ParamPoint n) : Prop :=
  L.projPoint a = p.1 ∧ ∀ b : RegularProjection.ParamPoint n,
    L.projPoint b = p.1 → b = a ∨ L.heightAt a < L.heightAt b

/-- A regular crossing has a unique over-strand preimage. -/
theorem ParametrizedLink.existsUnique_isOverPoint {n : ℕ}
    (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (p : L.Crossing) : ∃! a, L.IsOverPoint p a := by
  obtain ⟨a, b, hab, ha, hb, hexact⟩ :=
    L.exists_pair_of_mem_doublePointSet hreg p.2
  have hne : L.heightAt a ≠ L.heightAt b :=
    L.heightAt_ne_of_projPoint_eq_of_ne hab (ha.trans hb.symm)
  rcases lt_trichotomy (L.heightAt a) (L.heightAt b) with hlt | heq | hgt
  · refine ⟨b, ⟨hb, ?_⟩, ?_⟩
    · intro c hc
      rcases hexact c hc with rfl | rfl
      · exact Or.inr hlt
      · exact Or.inl rfl
    · intro c hc
      rcases hexact c hc.1 with rfl | rfl
      · rcases hc.2 b hb with h | h
        · exact absurd h.symm hab
        · exact absurd h (not_lt.mpr hlt.le)
      · rfl
  · exact absurd heq hne
  · refine ⟨a, ⟨ha, ?_⟩, ?_⟩
    · intro c hc
      rcases hexact c hc with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr hgt
    · intro c hc
      rcases hexact c hc.1 with rfl | rfl
      · rfl
      · rcases hc.2 a ha with h | h
        · exact absurd h hab
        · exact absurd h (not_lt.mpr hgt.le)

/-- A regular crossing has a unique under-strand preimage. -/
theorem ParametrizedLink.existsUnique_isUnderPoint {n : ℕ}
    (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (p : L.Crossing) : ∃! a, L.IsUnderPoint p a := by
  obtain ⟨a, b, hab, ha, hb, hexact⟩ :=
    L.exists_pair_of_mem_doublePointSet hreg p.2
  have hne : L.heightAt a ≠ L.heightAt b :=
    L.heightAt_ne_of_projPoint_eq_of_ne hab (ha.trans hb.symm)
  rcases lt_trichotomy (L.heightAt a) (L.heightAt b) with hlt | heq | hgt
  · refine ⟨a, ⟨ha, ?_⟩, ?_⟩
    · intro c hc
      rcases hexact c hc with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr hlt
    · intro c hc
      rcases hexact c hc.1 with rfl | rfl
      · rfl
      · rcases hc.2 a ha with h | h
        · exact absurd h hab
        · exact absurd h (not_lt.mpr hlt.le)
  · exact absurd heq hne
  · refine ⟨b, ⟨hb, ?_⟩, ?_⟩
    · intro c hc
      rcases hexact c hc with rfl | rfl
      · exact Or.inr hgt
      · exact Or.inl rfl
    · intro c hc
      rcases hexact c hc.1 with rfl | rfl
      · rcases hc.2 b hb with h | h
        · exact absurd h.symm hab
        · exact absurd h (not_lt.mpr hgt.le)
      · rfl

/-- The over-strand preimage at a regular crossing, selected from the
proved unique specification. -/
noncomputable def ParametrizedLink.overPoint {n : ℕ}
    (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (p : L.Crossing) : RegularProjection.ParamPoint n :=
  Classical.choose (L.existsUnique_isOverPoint hreg p)

/-- The under-strand preimage at a regular crossing. -/
noncomputable def ParametrizedLink.underPoint {n : ℕ}
    (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (p : L.Crossing) : RegularProjection.ParamPoint n :=
  Classical.choose (L.existsUnique_isUnderPoint hreg p)

theorem ParametrizedLink.isOverPoint_overPoint {n : ℕ}
    (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (p : L.Crossing) : L.IsOverPoint p (L.overPoint hreg p) :=
  (Classical.choose_spec (L.existsUnique_isOverPoint hreg p)).1

theorem ParametrizedLink.isUnderPoint_underPoint {n : ℕ}
    (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (p : L.Crossing) : L.IsUnderPoint p (L.underPoint hreg p) :=
  (Classical.choose_spec (L.existsUnique_isUnderPoint hreg p)).1

/-- The over and under preimages at a crossing are distinct. -/
theorem ParametrizedLink.underPoint_ne_overPoint {n : ℕ}
    (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (p : L.Crossing) : L.underPoint hreg p ≠ L.overPoint hreg p := by
  intro hEq
  obtain ⟨a, b, hab, ha, hb, hexact⟩ :=
    L.exists_pair_of_mem_doublePointSet hreg p.2
  have hover := L.isOverPoint_overPoint hreg p
  have hunder := L.isUnderPoint_underPoint hreg p
  rcases hexact (L.overPoint hreg p) hover.1 with hoverEq | hoverEq
  · have hne : b ≠ L.overPoint hreg p := by
      intro h
      apply hab
      rw [hoverEq] at h
      exact h.symm
    have h1 := hover.2 b hb
    have h2 := hunder.2 b hb
    rw [hEq] at h2
    rcases h1 with h | h
    · exact hne h
    · rcases h2 with h' | h'
      · exact hne h'
      · exact absurd h (not_lt.mpr h'.le)
  · have hne : a ≠ L.overPoint hreg p := by
      intro h
      apply hab
      rw [hoverEq] at h
      exact h
    have h1 := hover.2 a ha
    have h2 := hunder.2 a ha
    rw [hEq] at h2
    rcases h1 with h | h
    · exact hne h
    · rcases h2 with h' | h'
      · exact hne h'
      · exact absurd h (not_lt.mpr h'.le)

/-- The under preimage is strictly below the over preimage. -/
theorem ParametrizedLink.heightAt_underPoint_lt_overPoint {n : ℕ}
    (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (p : L.Crossing) :
    L.heightAt (L.underPoint hreg p) < L.heightAt (L.overPoint hreg p) := by
  have hover := L.isOverPoint_overPoint hreg p
  have hunder := L.isUnderPoint_underPoint hreg p
  rcases hover.2 (L.underPoint hreg p) hunder.1 with h | h
  · exact absurd h (L.underPoint_ne_overPoint hreg p)
  · exact h

/-- The over preimage projects to the crossing point. -/
theorem ParametrizedLink.projPoint_overPoint {n : ℕ}
    (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (p : L.Crossing) : L.projPoint (L.overPoint hreg p) = p.1 :=
  (L.isOverPoint_overPoint hreg p).1

/-- The under preimage projects to the crossing point. -/
theorem ParametrizedLink.projPoint_underPoint {n : ℕ}
    (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (p : L.Crossing) : L.projPoint (L.underPoint hreg p) = p.1 :=
  (L.isUnderPoint_underPoint hreg p).1

/-- The over and under preimages exhaust the preimage of a regular
crossing: there is no third parameter point over it, and the two named
points are exactly the two that occur. -/
theorem ParametrizedLink.eq_overPoint_or_eq_underPoint_of_projPoint_eq {n : ℕ}
    (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (p : L.Crossing) (c : RegularProjection.ParamPoint n)
    (hc : L.projPoint c = p.1) :
    c = L.overPoint hreg p ∨ c = L.underPoint hreg p := by
  obtain ⟨a, b, hab, ha, hb, hexact⟩ :=
    L.exists_pair_of_mem_doublePointSet hreg p.2
  have hc' := hexact c hc
  have ho := hexact _ (L.projPoint_overPoint hreg p)
  have hu := hexact _ (L.projPoint_underPoint hreg p)
  have hne := L.underPoint_ne_overPoint hreg p
  rcases hc' with rfl | rfl <;> rcases ho with ho | ho <;>
    rcases hu with hu | hu <;> simp_all

/-- A regular projection with no double points has crossing count
zero. -/
theorem ParametrizedLink.crossingCount_eq_zero_of_doublePointSet_eq_empty
    {n : ℕ} (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (h : L.doublePointSet = ∅) : L.crossingCount hreg = 0 := by
  unfold ParametrizedLink.crossingCount ParametrizedLink.Crossing
  rw [Nat.card_eq_zero]
  exact Or.inl (Set.isEmpty_coe_sort.mpr h)

/-- A regular projection with a crossing has positive crossing
count. -/
theorem ParametrizedLink.crossingCount_pos_of_crossing {n : ℕ}
    (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (p : L.Crossing) : 0 < L.crossingCount hreg := by
  unfold ParametrizedLink.crossingCount
  exact @Nat.card_pos L.Crossing ⟨p⟩
    (@Finite.of_fintype _ hreg.finiteDouble.fintype)

/-- The crossing number of an oriented labeled ambient-isotopy type,
represented by `L`: the infimum, over all isotopic parametrized
representatives equipped with a regular standard projection, of the
number of double points of that projection. Changing the projection
direction is absorbed by varying the representative over its isotopy
class. The value is `⊤` in `ℕ∞` when no representative in the type is
known to admit a regular projection; existence of regular projections
in every type is the classical generic-direction theorem and is not
proved here. -/
noncomputable def ParametrizedLink.crossingNumber {n : ℕ}
    (L : ParametrizedLink n) : ℕ∞ :=
  ⨅ L' : ParametrizedLink n, ⨅ _ : L'.Isotopic L,
    ⨅ h : L'.IsRegularProjection, (L'.crossingCount h : ℕ∞)

/-- Any regular projection of any isotopic representative bounds the
crossing number of the type. -/
theorem ParametrizedLink.crossingNumber_le_of_isotopic_of_isRegularProjection
    {n : ℕ} {L L' : ParametrizedLink n} (h : L'.Isotopic L)
    (hreg : L'.IsRegularProjection) :
    L.crossingNumber ≤ (L'.crossingCount hreg : ℕ∞) :=
  (iInf₂_le L' h).trans (iInf_le _ hreg)

/-- A regular projection of the representative itself bounds the
crossing number of its type. -/
theorem ParametrizedLink.crossingNumber_le_self_of_isRegularProjection
    {n : ℕ} (L : ParametrizedLink n) (hreg : L.IsRegularProjection) :
    L.crossingNumber ≤ (L.crossingCount hreg : ℕ∞) :=
  L.crossingNumber_le_of_isotopic_of_isRegularProjection
    (ParametrizedLink.Isotopic.refl L) hreg

/-- If some isotopic representative admits a regular projection, the
crossing number of the type is finite. -/
theorem ParametrizedLink.crossingNumber_lt_top_of_isotopic_of_isRegularProjection
    {n : ℕ} {L L' : ParametrizedLink n} (h : L'.Isotopic L)
    (hreg : L'.IsRegularProjection) :
    L.crossingNumber < ⊤ :=
  (L.crossingNumber_le_of_isotopic_of_isRegularProjection h hreg).trans_lt
    (ENat.natCast_lt_top _)

/-- Crossing number depends only on the ambient-isotopy type. -/
theorem ParametrizedLink.crossingNumber_eq_of_isotopic {n : ℕ}
    {L₁ L₂ : ParametrizedLink n} (h : L₁.Isotopic L₂) :
    L₁.crossingNumber = L₂.crossingNumber := by
  apply le_antisymm
  · apply le_iInf₂
    intro L' h'
    apply le_iInf
    intro hreg
    exact ParametrizedLink.crossingNumber_le_of_isotopic_of_isRegularProjection
      (h'.trans h.symm) hreg
  · apply le_iInf₂
    intro L' h'
    apply le_iInf
    intro hreg
    exact ParametrizedLink.crossingNumber_le_of_isotopic_of_isRegularProjection
      (h'.trans h) hreg

/-- If some isotopic representative has a regular projection with no
double points, the crossing number of the type is zero. -/
theorem ParametrizedLink.crossingNumber_eq_zero_of_isotopic_of_doublePointSet_eq_empty
    {n : ℕ} {L L' : ParametrizedLink n} (h : L'.Isotopic L)
    (hreg : L'.IsRegularProjection) (hempty : L'.doublePointSet = ∅) :
    L.crossingNumber = 0 := by
  apply le_antisymm _ zero_le
  have hle := L.crossingNumber_le_of_isotopic_of_isRegularProjection h hreg
  rw [L'.crossingCount_eq_zero_of_doublePointSet_eq_empty hreg hempty] at hle
  exact hle

/-- A parameter point lies over a double point of the standard
projection. -/
def ParametrizedLink.IsCrossingPreimage {n : ℕ} (L : ParametrizedLink n)
    (a : RegularProjection.ParamPoint n) : Prop :=
  L.projPoint a ∈ L.doublePointSet

open Classical in
/-- Whether the strand at a crossing preimage is the over-strand of
its crossing, under a regular projection. -/
noncomputable def ParametrizedLink.isOverAt {n : ℕ}
    (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (a : RegularProjection.ParamPoint n)
    (ha : L.IsCrossingPreimage a) : Bool :=
  if a = L.overPoint hreg ⟨L.projPoint a, ha⟩ then true else false

theorem ParametrizedLink.isOverAt_overPoint {n : ℕ}
    (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (p : L.Crossing)
    (ha : L.IsCrossingPreimage (L.overPoint hreg p)) :
    L.isOverAt hreg (L.overPoint hreg p) ha = true := by
  have h : (⟨L.projPoint (L.overPoint hreg p), ha⟩ : L.Crossing) = p :=
    Subtype.ext (L.projPoint_overPoint hreg p)
  simp [ParametrizedLink.isOverAt, h]

theorem ParametrizedLink.isOverAt_underPoint {n : ℕ}
    (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (p : L.Crossing)
    (ha : L.IsCrossingPreimage (L.underPoint hreg p)) :
    L.isOverAt hreg (L.underPoint hreg p) ha = false := by
  have h : (⟨L.projPoint (L.underPoint hreg p), ha⟩ : L.Crossing) = p :=
    Subtype.ext (L.projPoint_underPoint hreg p)
  simp [ParametrizedLink.isOverAt, h, L.underPoint_ne_overPoint hreg p]

/-- The two preimages of one crossing have opposite over/under
status. -/
theorem ParametrizedLink.isOverAt_ne_of_ne_of_projPoint_eq {n : ℕ}
    (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    {a b : RegularProjection.ParamPoint n}
    (ha : L.IsCrossingPreimage a) (hb : L.IsCrossingPreimage b)
    (hab : a ≠ b) (hproj : L.projPoint a = L.projPoint b) :
    L.isOverAt hreg a ha ≠ L.isOverAt hreg b hb := by
  have key : ∀ p : L.Crossing, L.projPoint a = p.1 →
      L.projPoint b = p.1 → L.isOverAt hreg a ha ≠ L.isOverAt hreg b hb := by
    intro p hpa hpb
    have ha' := L.eq_overPoint_or_eq_underPoint_of_projPoint_eq hreg p a hpa
    have hb' := L.eq_overPoint_or_eq_underPoint_of_projPoint_eq hreg p b hpb
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hab
    · rw [L.isOverAt_overPoint hreg p ha, L.isOverAt_underPoint hreg p hb]
      decide
    · rw [L.isOverAt_underPoint hreg p ha, L.isOverAt_overPoint hreg p hb]
      decide
    · exact absurd rfl hab
  exact key ⟨L.projPoint a, ha⟩ rfl hproj.symm

/-- Whether `c` lies in the open counterclockwise arc from `a` to `b`
on the common parameter circle `[0, 2π)`. -/
def inOpenArc {n : ℕ} (a b c : RegularProjection.ParamPoint n) : Prop :=
  if a.t < b.t then a.t < c.t ∧ c.t < b.t else a.t < c.t ∨ c.t < b.t

/-- Two crossing preimages on one component are cyclically adjacent
when no other crossing preimage of that component lies in the open
arc from the first to the second. -/
def ParametrizedLink.CyclicallyAdjacent {n : ℕ}
    (L : ParametrizedLink n) (a b : RegularProjection.ParamPoint n) :
    Prop :=
  a.comp = b.comp ∧ a ≠ b ∧ L.IsCrossingPreimage a ∧
    L.IsCrossingPreimage b ∧
    ∀ c : RegularProjection.ParamPoint n, L.IsCrossingPreimage c →
      c.comp = a.comp → ¬ inOpenArc a b c

/-- A regular projection is alternating when cyclically consecutive
crossing visits along every component have opposite over/under
status. A component with at most one crossing preimage is
alternating vacuously. -/
def ParametrizedLink.IsAlternatingProjection {n : ℕ}
    (L : ParametrizedLink n) (hreg : L.IsRegularProjection) : Prop :=
  ∀ a b : RegularProjection.ParamPoint n,
    ∀ hadj : L.CyclicallyAdjacent a b,
      L.isOverAt hreg a hadj.2.2.1 ≠ L.isOverAt hreg b hadj.2.2.2.1

/-- A regular projection with no double points is alternating. -/
theorem ParametrizedLink.isAlternatingProjection_of_doublePointSet_eq_empty
    {n : ℕ} (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (hempty : L.doublePointSet = ∅) :
    L.IsAlternatingProjection hreg := by
  intro a _ hadj
  have hmem : L.projPoint a ∈ L.doublePointSet := hadj.2.2.1
  rw [hempty] at hmem
  exact (Set.notMem_empty _ hmem).elim

/-- An oriented labeled link type admits an alternating diagram when
some isotopic representative has an alternating regular projection. -/
def ParametrizedLink.AdmitsAlternatingDiagram {n : ℕ}
    (L : ParametrizedLink n) : Prop :=
  ∃ L' : ParametrizedLink n, L'.Isotopic L ∧
    ∃ hreg : L'.IsRegularProjection, L'.IsAlternatingProjection hreg

/-- Admitting an alternating diagram depends only on the
ambient-isotopy type. -/
theorem ParametrizedLink.AdmitsAlternatingDiagram.of_isotopic {n : ℕ}
    {L₁ L₂ : ParametrizedLink n} (h : L₁.Isotopic L₂)
    (hL : L₁.AdmitsAlternatingDiagram) :
    L₂.AdmitsAlternatingDiagram := by
  obtain ⟨L', h', hreg, halt⟩ := hL
  exact ⟨L', h'.trans h, hreg, halt⟩

/-- A link with a crossing-free regular projection admits an
alternating diagram (itself, vacuously). -/
theorem ParametrizedLink.admitsAlternatingDiagram_of_doublePointSet_eq_empty
    {n : ℕ} (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (hempty : L.doublePointSet = ∅) :
    L.AdmitsAlternatingDiagram :=
  ⟨L, ParametrizedLink.Isotopic.refl L, hreg,
    L.isAlternatingProjection_of_doublePointSet_eq_empty hreg hempty⟩

/-- The union of projected component traces is the plane projection of
the whole Euclidean trace. -/
theorem ParametrizedLink.iUnion_range_projCurve {n : ℕ}
    (L : ParametrizedLink n) :
    ⋃ i, Set.range (L.projCurve i) = RegularProjection.plane '' L.trace := by
  ext y
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_image]
  constructor
  · rintro ⟨i, t, rfl⟩
    refine ⟨(L.component i).curve t, ?_, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i, ⟨t, rfl⟩⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, t, rfl⟩ := Set.mem_iUnion.mp hx
    exact ⟨i, t, rfl⟩

end MathlibExt.Topology.Knot.Euclidean
