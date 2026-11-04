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

/-- **Dart diagram.** A dart diagram consists of a finite set $V$ of crossings, a
fixed-point-free involution $\mathrm{pair}$ of the set $V \times \{0, 1, 2, 3\}$ of darts, and a
natural number counting isolated crossingless components.

Darts $0, 1, 2, 3$ at a crossing are read in counterclockwise order, darts $0$ and $2$ form the
over-strand and darts $1$ and $3$ the under-strand, and $\mathrm{pair}$ glues darts across edge
segments. The structure does not by itself assert planarity. -/
structure DartDiagram where
  Vertex : Type
  [vertexFintype : Fintype Vertex]
  [vertexDecidableEq : DecidableEq Vertex]
  pair : Vertex × Fin 4 → Vertex × Fin 4
  pair_involutive : ∀ d, pair (pair d) = d
  pair_ne_self : ∀ d, pair d ≠ d
  isolated : ℕ

namespace DartDiagram

/-- **Darts of a dart diagram.** The darts of a dart diagram $D$ with crossing set $V$ are the
pairs $(v, i)$ with $v \in V$ and $i \in \{0, 1, 2, 3\}$; the dart $(v, i)$ is the $i$-th
incident half-edge at the crossing $v$. -/
abbrev Dart (D : DartDiagram) : Type :=
  D.Vertex × Fin 4

instance (D : DartDiagram) : Fintype D.Dart := by
  letI := D.vertexFintype
  infer_instance

instance (D : DartDiagram) : DecidableEq D.Dart := by
  letI := D.vertexDecidableEq
  infer_instance

/-- **Number of crossings of a dart diagram.** The crossing count of a dart diagram $D$ is the
number of vertices of $D$, each vertex being one crossing. -/
def crossingCount (D : DartDiagram) : ℕ := by
  letI := D.vertexFintype
  exact Fintype.card D.Vertex

/-- **Rotation of a dart.** For a dart diagram $D$, the rotation of a dart $(v, i)$ of $D$, with
$v$ a crossing and $i \in \mathbb{Z}/4$, is the dart $(v, i + 1)$: one step counterclockwise
around the crossing $v$. -/
def rot (D : DartDiagram) (d : D.Dart) : D.Dart :=
  (d.1, d.2 + 1)

/-- **Opposite dart.** For a dart diagram $D$ and a dart $d = (v, i)$ of $D$, the opposite dart
is obtained by rotating $d$ twice counterclockwise around its crossing $v$; it is the dart
$(v, i + 2)$, with labels taken modulo $4$. -/
def opposite (D : DartDiagram) (d : D.Dart) : D.Dart :=
  D.rot (D.rot d)

@[simp]
theorem opposite_eq {D : DartDiagram} (d : D.Dart) :
    D.opposite d = (d.1, d.2 + 2) := by
  obtain ⟨v, i⟩ := d
  fin_cases i <;> simp [DartDiagram.opposite, DartDiagram.rot]

/-- **Over-strand darts.** The four darts at a crossing of a dart diagram carry the labels
$0, 1, 2, 3$ in cyclic order. A dart lies on the over-strand at its crossing when its label is
$0$ or $2$. -/
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

/-- **Edge-pairing permutation.** For a dart diagram $D$, the edge-pairing permutation is the
edge-pairing involution of $D$ regarded as a permutation of the darts of $D$; it is its own
inverse. -/
def pairPerm (D : DartDiagram) : Equiv.Perm D.Dart where
  toFun := D.pair
  invFun := D.pair
  left_inv := D.pair_involutive
  right_inv := D.pair_involutive

/-- **Rotation permutation of darts.** For a dart diagram $D$, the rotation permutation is the
permutation of the darts of $D$ sending a dart $(v, i)$, with $v$ a crossing and
$i \in \mathbb{Z}/4$, to $(v, i + 1)$; its inverse sends $(v, i)$ to $(v, i - 1)$. -/
def rotPerm (D : DartDiagram) : Equiv.Perm D.Dart where
  toFun := D.rot
  invFun := fun d => (d.1, d.2 - 1)
  left_inv := by intro d; simp [DartDiagram.rot]
  right_inv := by intro d; simp [DartDiagram.rot]

/-- **Opposite-dart permutation.** For a dart diagram $D$, the opposite-dart permutation of the
darts of $D$ is the square of the quarter-turn rotation permutation: it sends the dart $(v, i)$
at crossing $v$ to the dart $(v, i + 2)$, with labels taken modulo $4$. -/
def oppositePerm (D : DartDiagram) : Equiv.Perm D.Dart :=
  D.rotPerm ^ 2

/-- **Strand traversal step.** For a dart diagram $D$ and a dart $d$ of $D$, the next dart
after $d$ is the dart opposite $\mathrm{pair}(d)$ at its crossing, where $\mathrm{pair}$ is
the edge-pairing involution of $D$: cross the edge segment at $d$, then go straight through
the crossing reached. -/
def next (D : DartDiagram) (d : D.Dart) : D.Dart :=
  D.opposite (D.pair d)

/-- **Strand traversal permutation.** For a dart diagram $D$, the strand traversal permutation
of the darts of $D$ is the edge-pairing permutation followed by the opposite-dart permutation:
it sends a dart $d$ to the dart opposite $\mathrm{pair}(d)$ at its crossing, where
$\mathrm{pair}$ is the edge-pairing involution of $D$. -/
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

/-- **A traversal step stays in its strand cycle.** Let $D$ be a dart diagram, and for a dart
$d$ of $D$ let $\operatorname{next}(d)$ be the dart reached from $d$ by crossing its edge
segment and then going straight through the next crossing. Then for every dart $d$ of $D$, the
darts $d$ and $\operatorname{next}(d)$ lie in the same cycle of the strand traversal
permutation of $D$, the permutation of the darts of $D$ that sends each dart $e$ to
$\operatorname{next}(e)$. -/
theorem sameCycle_next (D : DartDiagram) (d : D.Dart) :
    D.nextPerm.SameCycle d (D.next d) :=
  ⟨1, by simp⟩

/-- **Alternating dart diagrams.** A dart diagram is alternating when, for every dart $d$, the
dart $\operatorname{next}(d)$, reached from $d$ by crossing its edge segment and going straight
through the next crossing, has the opposite over/under status to $d$. In other words, consecutive
crossings on every strand have opposite over/under status.

Crossingless components impose no condition. -/
def IsAlternating (D : DartDiagram) : Prop :=
  ∀ d, D.isOver (D.next d) ≠ D.isOver d

instance (D : DartDiagram) : Decidable D.IsAlternating := by
  unfold DartDiagram.IsAlternating
  infer_instance

/-- **Same component relation on darts.** For a dart diagram $D$, two darts of $D$ lie in the
same component when they are related by the equivalence relation on darts generated by
$d \sim \operatorname{pair}(d)$, crossing an edge segment, and $d \sim \operatorname{opposite}(d)$,
going straight through a crossing.

The oriented traversal $\operatorname{next}$ traverses every component twice, once in each
orientation, so the cycles of the traversal permutation are not themselves the components. -/
def SameComponent (D : DartDiagram) : D.Dart → D.Dart → Prop :=
  Relation.EqvGen (fun x y => y = D.pair x ∨ y = D.opposite x)

/-- **Strand-connectivity relation on darts.** For a dart diagram $D$, this is the equivalence
relation on the darts of $D$ generated by relating each dart $d$ to its partner across an edge
segment and to the opposite dart of $d$ at the same crossing. Two darts are related exactly when
they lie on the same unoriented strand component. -/
def componentSetoid (D : DartDiagram) : Setoid D.Dart :=
  Relation.EqvGen.setoid (fun x y => y = D.pair x ∨ y = D.opposite x)

theorem sameComponent_pair (D : DartDiagram) (d : D.Dart) :
    D.SameComponent d (D.pair d) :=
  Relation.EqvGen.rel _ _ (Or.inl rfl)

theorem sameComponent_opposite (D : DartDiagram) (d : D.Dart) :
    D.SameComponent d (D.opposite d) :=
  Relation.EqvGen.rel _ _ (Or.inr rfl)

/-- **A traversal step stays in the same component.** For every dart $d$ of a dart diagram $D$,
the dart $\operatorname{next}(d)$ reached by one step of strand traversal lies in the same
component as $d$. -/
theorem sameComponent_next (D : DartDiagram) (d : D.Dart) :
    D.SameComponent d (D.next d) :=
  Relation.EqvGen.trans _ _ _ (D.sameComponent_pair d)
    (D.sameComponent_opposite _)

/-- **Number of components of a dart diagram.** The number of components of a dart diagram $D$ is
the number of classes of darts of $D$ under unoriented strand connectivity, plus the recorded
number of isolated crossingless components of $D$. -/
noncomputable def componentCount (D : DartDiagram) : ℕ :=
  Nat.card (Quotient D.componentSetoid) + D.isolated

/-- **Isolated components are counted in the component count.** For every dart diagram $D$,
the number of isolated crossingless components recorded in $D$ is at most the number of
components of $D$. -/
theorem isolated_le_componentCount (D : DartDiagram) :
    D.isolated ≤ D.componentCount :=
  Nat.le_add_left _ _

/-- **Empty dart diagram.** For a natural number $k$, the empty dart diagram with $k$ isolated
components has no crossings, hence no darts, and records $k$ isolated crossingless components.

It is alternating, since the alternating condition is vacuous when there are no darts. -/
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

/-- **Euclidean plane.** The space $\mathbb{R}^2$ with its Euclidean inner product and norm, the
target plane of the fixed standard projection frame. -/
abbrev R2 : Type := EuclideanSpace ℝ (Fin 2)

/-- **Standard projection to the plane.** The standard projection sends a point
$x = (x_0, x_1, x_2)$ of Euclidean 3-space to the point $(x_0, x_1)$ of the Euclidean plane,
forgetting the third coordinate. -/
def plane (x : R3) : R2 :=
  WithLp.toLp 2 (fun i => x (Fin.castSucc i))

/-- **Height in the standard projection frame.** The height of a point
$x = (x_1, x_2, x_3)$ of Euclidean 3-space is its third coordinate $x_3$. -/
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

/-- **Parameter point.** For a natural number $n$, a parameter point consists of a component
index $i \in \{0, \dots, n-1\}$ and a real parameter $t$ with $0 \le t < 2\pi$, the fundamental
half-open period. It represents the point at parameter $t$ of component $i$ of a parametrized
link with $n$ components. -/
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

/-- **Point of a link at a parameter point.** For a parametrized link $L$ with components
$\gamma_0, \dots, \gamma_{n-1} \colon \mathbb{R} \to \mathbb{R}^3$ and a parameter point
$a = (i, t)$, with $i < n$ and $t \in [0, 2\pi)$, the point of $L$ at $a$ is
$\gamma_i(t) \in \mathbb{R}^3$. -/
def ParametrizedLink.point {n : ℕ} (L : ParametrizedLink n)
    (a : RegularProjection.ParamPoint n) : R3 :=
  (L.component a.comp).curve a.t

/-- **Projected curve of a link component.** For a parametrized link $L$ with components
$\gamma_0, \dots, \gamma_{n-1} \colon \mathbb{R} \to \mathbb{R}^3$ and $i < n$, the projected curve
of component $i$ is the map $\mathbb{R} \to \mathbb{R}^2$, $t \mapsto \pi(\gamma_i(t))$, where
$\pi(x_0, x_1, x_2) = (x_0, x_1)$ is the standard projection forgetting the third coordinate. -/
def ParametrizedLink.projCurve {n : ℕ} (L : ParametrizedLink n)
    (i : Fin n) : ℝ → RegularProjection.R2 :=
  RegularProjection.plane ∘ (L.component i).curve

/-- **Projected point of a link at a parameter point.** For a parametrized link $L$ with
components $\gamma_0, \dots, \gamma_{n-1} \colon \mathbb{R} \to \mathbb{R}^3$ and a parameter point
$a = (i, t)$, with $i < n$ and $t \in [0, 2\pi)$, the projected point of $L$ at $a$ is
$\pi(\gamma_i(t)) \in \mathbb{R}^2$, where $\pi(x_0, x_1, x_2) = (x_0, x_1)$ forgets the third
coordinate. -/
def ParametrizedLink.projPoint {n : ℕ} (L : ParametrizedLink n)
    (a : RegularProjection.ParamPoint n) : RegularProjection.R2 :=
  RegularProjection.plane (L.point a)

/-- **Projected tangent vector.** Let $L$ be a parametrized link and let $a$ be a parameter point
of $L$, given by a component $i$ and a parameter $t$. The projected tangent vector of $L$ at $a$
is the vector of $\mathbb{R}^2$ obtained by applying the standard projection
$(x, y, z) \mapsto (x, y)$ to the derivative $\gamma_i'(t)$ of the curve $\gamma_i$ of the
$i$-th component of $L$ at $t$.

This is the projection of the ambient derivative; it is not defined as the derivative of the
projected curve. -/
noncomputable def ParametrizedLink.tangent {n : ℕ} (L : ParametrizedLink n)
    (a : RegularProjection.ParamPoint n) : RegularProjection.R2 :=
  RegularProjection.plane (deriv (L.component a.comp).curve a.t)

/-- **Height of a parameter point.** For a parametrized link $L$ with $n$ components and a
parameter point $a$ of $L$, the height of $L$ at $a$ is the height (the third coordinate) of
the point of Euclidean 3-space that $a$ represents on $L$. -/
def ParametrizedLink.heightAt {n : ℕ} (L : ParametrizedLink n)
    (a : RegularProjection.ParamPoint n) : ℝ :=
  RegularProjection.height (L.point a)

/-- **Double points of a link projection.** For an oriented labeled parametrized link $L$ with
$n$ components, the double-point set of $L$ is the set of points $p$ of the plane $\mathbb{R}^2$
for which there are two distinct parameter points of $L$ (each a component index together with a
parameter in $[0, 2\pi)$) whose images under the standard projection, which forgets the third
coordinate, both equal $p$. -/
def ParametrizedLink.doublePointSet {n : ℕ} (L : ParametrizedLink n) :
    Set RegularProjection.R2 :=
  {p | ∃ a b : RegularProjection.ParamPoint n, a ≠ b ∧ L.projPoint a = p ∧ L.projPoint b = p}

/-- **Regular projections.** Let $L$ be a parametrized link; a parameter point of $L$ is a
component of $L$ together with a parameter in $[0, 2\pi)$. The standard projection of $L$ to the
plane, which forgets the third coordinate, is regular when the following hold: at every parameter
point, the projection of the velocity vector of the component curve is nonzero; the double-point
set is finite; no three pairwise distinct parameter points have the same projection; and at any
two distinct parameter points with the same projection, the projected velocity vectors are
linearly independent over $\mathbb{R}$.

The condition records no diagram, crossing labels or over/under data. The heights at two distinct
parameter points with the same projection always differ, because each component is injective on
a period and the components are pairwise disjoint. -/
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

/-- **Points with the same projection have different heights.** Let $L$ be a parametrized link
with $n$ components. If two distinct parameter points $a \ne b$ of $L$ have the same projected
point, then the heights of $L$ at $a$ and at $b$ are different.

This is forced by component injectivity in one period and pairwise disjoint component traces;
over/under is therefore derived from the parametrization rather than chosen. -/
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

/-- **Crossings of a link projection.** Let $L$ be a parametrized link with $n$ components. A
crossing of $L$ is a point of the double-point set of $L$, that is, a point $p$ of the plane
$\mathbb{R}^2$ such that two distinct parameter points of $L$ both have image $p$ under the
standard projection forgetting the third coordinate. -/
abbrev ParametrizedLink.Crossing {n : ℕ} (L : ParametrizedLink n) : Type :=
  {p : RegularProjection.R2 // p ∈ L.doublePointSet}

/-- **Crossing count of a regular projection.** For a parametrized link $L$ whose standard
projection is regular, the crossing count of $L$ is the number of crossings of the projection,
that is, the number of points of its double-point set.

Regularity guarantees that the double-point set is finite, and the value does not depend on the
chosen proof of regularity. -/
noncomputable def ParametrizedLink.crossingCount {n : ℕ}
    (L : ParametrizedLink n) (_h : L.IsRegularProjection) : ℕ :=
  Nat.card L.Crossing

theorem ParametrizedLink.crossingCount_eq_of_isRegularProjection {n : ℕ}
    (L : ParametrizedLink n) (h₁ h₂ : L.IsRegularProjection) :
    L.crossingCount h₁ = L.crossingCount h₂ :=
  rfl

/-- **Double points have exactly two preimages.** Let $L$ be a parametrized link with $n$
components whose standard projection is regular, and let $p$ be a point of the double-point set
of $L$. Then there are parameter points $a \ne b$ of $L$ whose projected points are both $p$, and
every parameter point of $L$ whose projected point is $p$ is $a$ or $b$. -/
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

/-- **Being the over-strand preimage of a crossing.** Let $L$ be a parametrized link and $p$ a
crossing of its standard projection to the plane. A parameter point $a$ of $L$ is an over point
of $p$ when $a$ projects to $p$ and every other parameter point that projects to $p$ has strictly
smaller height than $a$. -/
def ParametrizedLink.IsOverPoint {n : ℕ} (L : ParametrizedLink n)
    (p : L.Crossing) (a : RegularProjection.ParamPoint n) : Prop :=
  L.projPoint a = p.1 ∧ ∀ b : RegularProjection.ParamPoint n,
    L.projPoint b = p.1 → b = a ∨ L.heightAt b < L.heightAt a

/-- **Being the under-strand preimage of a crossing.** Let $L$ be a parametrized link and $p$ a
crossing of its standard projection to the plane. A parameter point $a$ of $L$ is an under point
of $p$ when $a$ projects to $p$ and every other parameter point that projects to $p$ has strictly
greater height than $a$. -/
def ParametrizedLink.IsUnderPoint {n : ℕ} (L : ParametrizedLink n)
    (p : L.Crossing) (a : RegularProjection.ParamPoint n) : Prop :=
  L.projPoint a = p.1 ∧ ∀ b : RegularProjection.ParamPoint n,
    L.projPoint b = p.1 → b = a ∨ L.heightAt a < L.heightAt b

/-- **The over-strand preimage exists and is unique.** Let $L$ be a parametrized link with $n$
components whose standard projection is regular, and let $p$ be a crossing of that projection.
There is exactly one parameter point $a$ of $L$ that is an over-strand preimage of $p$: the
projected point of $a$ is $p$, and every other parameter point whose projected point is $p$ has
height strictly less than the height of $a$. -/
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

/-- **The under-strand preimage exists and is unique.** Let $L$ be a parametrized link with $n$
components whose standard projection is regular, and let $p$ be a crossing of that projection.
There is exactly one parameter point $a$ of $L$ that is an under-strand preimage of $p$: the
projected point of $a$ is $p$, and every other parameter point whose projected point is $p$ has
height strictly greater than the height of $a$. -/
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

/-- **Over-strand preimage of a crossing.** Let $L$ be a parametrized link with $n$ components
whose standard projection is regular, and let $p$ be a crossing of that projection. The
over-strand preimage of $p$ is the unique parameter point $a$ of $L$ that projects to $p$ and
such that every other parameter point projecting to $p$ has strictly smaller height than $a$. -/
noncomputable def ParametrizedLink.overPoint {n : ℕ}
    (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (p : L.Crossing) : RegularProjection.ParamPoint n :=
  Classical.choose (L.existsUnique_isOverPoint hreg p)

/-- **Under-strand preimage of a crossing.** Let $L$ be a parametrized link whose standard
projection is regular, and let $p$ be a crossing of this projection. The under-strand preimage
of $p$ is the unique parameter point $a$ of $L$ that projects to $p$ and whose height is strictly
less than the height of every other parameter point projecting to $p$; the height of a parameter
point is the third coordinate of the corresponding point of $L$ in $\mathbb{R}^3$. -/
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

/-- **Over and under preimages differ.** Let $L$ be a parametrized link whose standard projection
is regular, and let $p$ be a crossing of this projection. Then the under-strand preimage of $p$
and the over-strand preimage of $p$ are distinct parameter points of $L$. -/
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

/-- **The under-strand lies strictly below the over-strand.** Let $L$ be a parametrized link with
$n$ components whose standard projection is regular, and let $p$ be a crossing of that
projection. The height of $L$ at the under-strand preimage of $p$ is strictly less than its
height at the over-strand preimage of $p$. -/
theorem ParametrizedLink.heightAt_underPoint_lt_overPoint {n : ℕ}
    (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (p : L.Crossing) :
    L.heightAt (L.underPoint hreg p) < L.heightAt (L.overPoint hreg p) := by
  have hover := L.isOverPoint_overPoint hreg p
  have hunder := L.isUnderPoint_underPoint hreg p
  rcases hover.2 (L.underPoint hreg p) hunder.1 with h | h
  · exact absurd h (L.underPoint_ne_overPoint hreg p)
  · exact h

/-- **The over-strand preimage lies over its crossing.** Let $L$ be a parametrized link whose
standard projection is regular, and let $p$ be a crossing of $L$, that is, a point of the
double-point set of its projection. Then the projected point of the over-strand parameter point
at $p$ is $p$. -/
theorem ParametrizedLink.projPoint_overPoint {n : ℕ}
    (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (p : L.Crossing) : L.projPoint (L.overPoint hreg p) = p.1 :=
  (L.isOverPoint_overPoint hreg p).1

/-- **The under-strand preimage lies over its crossing.** Let $L$ be a parametrized link whose
standard projection is regular, and let $p$ be a crossing of $L$, that is, a point of the
double-point set of its projection. Then the projected point of the under-strand parameter point
at $p$ is $p$. -/
theorem ParametrizedLink.projPoint_underPoint {n : ℕ}
    (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (p : L.Crossing) : L.projPoint (L.underPoint hreg p) = p.1 :=
  (L.isUnderPoint_underPoint hreg p).1

/-- **The over and under preimages exhaust a crossing.** Let $L$ be a parametrized link with $n$
components whose standard projection is regular, and let $p$ be a crossing of that projection.
Every parameter point of $L$ whose projected point is $p$ is either the over-strand preimage or
the under-strand preimage of $p$. -/
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

/-- **A crossing-free regular projection has crossing count zero.** If a parametrized link $L$ has
a regular standard projection whose double-point set is empty, then the crossing count of $L$ is
$0$. -/
theorem ParametrizedLink.crossingCount_eq_zero_of_doublePointSet_eq_empty
    {n : ℕ} (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (h : L.doublePointSet = ∅) : L.crossingCount hreg = 0 := by
  unfold ParametrizedLink.crossingCount ParametrizedLink.Crossing
  rw [Nat.card_eq_zero]
  exact Or.inl (Set.isEmpty_coe_sort.mpr h)

/-- **A regular projection with a crossing has positive crossing count.** If a parametrized link
$L$ has a regular standard projection with at least one crossing, then the crossing count of $L$
is positive. -/
theorem ParametrizedLink.crossingCount_pos_of_crossing {n : ℕ}
    (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (p : L.Crossing) : 0 < L.crossingCount hreg := by
  unfold ParametrizedLink.crossingCount
  exact @Nat.card_pos L.Crossing ⟨p⟩
    (@Finite.of_fintype _ hreg.finiteDouble.fintype)

/-- **Crossing number of a link.** For an oriented labeled parametrized link $L$ with $n$
components, the crossing number of $L$ is the infimum in $\mathbb{N} \cup \{\infty\}$, over all
parametrized links $L'$ with $n$ components that are ambient isotopic to $L$ and whose standard
projection to the plane is regular, of the number of crossings (double points) of that
projection of $L'$. It is $\infty$ when no such $L'$ exists.

Changing the projection direction is absorbed by varying the representative over its isotopy
class. -/
noncomputable def ParametrizedLink.crossingNumber {n : ℕ}
    (L : ParametrizedLink n) : ℕ∞ :=
  ⨅ L' : ParametrizedLink n, ⨅ _ : L'.Isotopic L,
    ⨅ h : L'.IsRegularProjection, (L'.crossingCount h : ℕ∞)

/-- **Regular projections of isotopic links bound the crossing number.** Let $L$ and $L'$ be
oriented labeled parametrized links with $n$ components, with $L'$ ambient isotopic to $L$, and
suppose the standard projection of $L'$ to the plane is regular. Then the crossing number of $L$
is at most the number of crossings of this projection of $L'$. -/
theorem ParametrizedLink.crossingNumber_le_of_isotopic_of_isRegularProjection
    {n : ℕ} {L L' : ParametrizedLink n} (h : L'.Isotopic L)
    (hreg : L'.IsRegularProjection) :
    L.crossingNumber ≤ (L'.crossingCount hreg : ℕ∞) :=
  (iInf₂_le L' h).trans (iInf_le _ hreg)

/-- **A link's own regular projection bounds its crossing number.** If the standard projection of
an oriented labeled parametrized link $L$ to the plane is regular, then the crossing number of
$L$ is at most the number of crossings of this projection. -/
theorem ParametrizedLink.crossingNumber_le_self_of_isRegularProjection
    {n : ℕ} (L : ParametrizedLink n) (hreg : L.IsRegularProjection) :
    L.crossingNumber ≤ (L.crossingCount hreg : ℕ∞) :=
  L.crossingNumber_le_of_isotopic_of_isRegularProjection
    (ParametrizedLink.Isotopic.refl L) hreg

/-- **Finiteness of the crossing number.** Let $L$ and $L'$ be oriented labeled parametrized links
with $n$ components. If $L'$ is ambient isotopic to $L$ and the standard projection of $L'$ to
the plane is regular, then the crossing number of $L$ is finite. -/
theorem ParametrizedLink.crossingNumber_lt_top_of_isotopic_of_isRegularProjection
    {n : ℕ} {L L' : ParametrizedLink n} (h : L'.Isotopic L)
    (hreg : L'.IsRegularProjection) :
    L.crossingNumber < ⊤ :=
  (L.crossingNumber_le_of_isotopic_of_isRegularProjection h hreg).trans_lt
    (ENat.natCast_lt_top _)

/-- **The crossing number is an isotopy invariant.** If two parametrized links $L_1$ and $L_2$ with
$n$ components are isotopic, then $L_1$ and $L_2$ have the same crossing number. -/
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

/-- **Crossing number zero from a crossing-free representative.** Let $L$ and $L'$ be parametrized
links with $n$ components such that $L'$ is isotopic to $L$. If the standard projection of $L'$ is
regular and its double-point set is empty, then the crossing number of $L$ is $0$. -/
theorem ParametrizedLink.crossingNumber_eq_zero_of_isotopic_of_doublePointSet_eq_empty
    {n : ℕ} {L L' : ParametrizedLink n} (h : L'.Isotopic L)
    (hreg : L'.IsRegularProjection) (hempty : L'.doublePointSet = ∅) :
    L.crossingNumber = 0 := by
  apply le_antisymm _ zero_le
  have hle := L.crossingNumber_le_of_isotopic_of_isRegularProjection h hreg
  rw [L'.crossingCount_eq_zero_of_doublePointSet_eq_empty hreg hempty] at hle
  exact hle

/-- **Crossing preimages.** A parameter point $a$ of a parametrized link $L$ (a component of $L$
together with a parameter in $[0, 2\pi)$) is a crossing preimage when its image under the
standard projection to the plane lies in the double-point set of $L$. -/
def ParametrizedLink.IsCrossingPreimage {n : ℕ} (L : ParametrizedLink n)
    (a : RegularProjection.ParamPoint n) : Prop :=
  L.projPoint a ∈ L.doublePointSet

open Classical in
/-- **Over/under status at a crossing preimage.** Let $L$ be a parametrized link whose standard
projection to the plane is regular, and let $a$ be a crossing preimage of $L$. The over/under
status at $a$ is true when $a$ is the over-strand preimage of the crossing at the projection of
$a$, that is, the preimage of that crossing of greatest height, and false otherwise. -/
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

/-- **The two preimages of a crossing have opposite status.** Let $L$ be a parametrized link
whose standard projection to the plane is regular. If $a \ne b$ are crossing preimages of $L$ with
the same projection, then the over/under status at $a$ differs from the over/under status at $b$.
-/
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

/-- **Open arc on the parameter circle.** Let $a$, $b$, $c$ be parameter points with parameters
$s$, $u$, $t \in [0, 2\pi)$ respectively. Then $c$ lies in the open counterclockwise arc from $a$
to $b$ when $s < t < u$ in case $s < u$, and when $s < t$ or $t < u$ in case $u \le s$. Only the
parameters are compared; the components of $a$, $b$, $c$ play no role. -/
def inOpenArc {n : ℕ} (a b c : RegularProjection.ParamPoint n) : Prop :=
  if a.t < b.t then a.t < c.t ∧ c.t < b.t else a.t < c.t ∨ c.t < b.t

/-- **Cyclically adjacent crossing preimages.** Let $L$ be an oriented labeled parametrized link,
with each component parametrized by $t \in [0, 2\pi)$. Two distinct parameter points $a$ and $b$
of $L$ on the same component are cyclically adjacent, in this order, when both are crossing
preimages (they project to double points of the standard projection) and no crossing preimage on
that component lies in the open arc from $a$ to $b$ in the direction of increasing parameter,
wrapping around from $2\pi$ to $0$ when the parameter of $b$ is smaller than that of $a$. -/
def ParametrizedLink.CyclicallyAdjacent {n : ℕ}
    (L : ParametrizedLink n) (a b : RegularProjection.ParamPoint n) :
    Prop :=
  a.comp = b.comp ∧ a ≠ b ∧ L.IsCrossingPreimage a ∧
    L.IsCrossingPreimage b ∧
    ∀ c : RegularProjection.ParamPoint n, L.IsCrossingPreimage c →
      c.comp = a.comp → ¬ inOpenArc a b c

/-- **Alternating regular projections.** Let $L$ be a parametrized link whose standard projection
to the plane is regular. The projection is alternating when, for any two cyclically adjacent
crossing preimages $a$ and $b$ of $L$ (distinct, on the same component, with no other crossing
preimage of that component in the open arc of parameters from $a$ to $b$), the over/under status
at $a$ differs from the over/under status at $b$.

A component with at most one crossing preimage imposes no condition. -/
def ParametrizedLink.IsAlternatingProjection {n : ℕ}
    (L : ParametrizedLink n) (hreg : L.IsRegularProjection) : Prop :=
  ∀ a b : RegularProjection.ParamPoint n,
    ∀ hadj : L.CyclicallyAdjacent a b,
      L.isOverAt hreg a hadj.2.2.1 ≠ L.isOverAt hreg b hadj.2.2.2.1

/-- **Crossingless regular projections are alternating.** Let $L$ be a parametrized link whose
standard projection to the plane is regular. If the double-point set of this projection is empty,
then the projection is alternating. -/
theorem ParametrizedLink.isAlternatingProjection_of_doublePointSet_eq_empty
    {n : ℕ} (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (hempty : L.doublePointSet = ∅) :
    L.IsAlternatingProjection hreg := by
  intro a _ hadj
  have hmem : L.projPoint a ∈ L.doublePointSet := hadj.2.2.1
  rw [hempty] at hmem
  exact (Set.notMem_empty _ hmem).elim

/-- **Links admitting an alternating diagram.** A parametrized link $L$ with $n$ components admits
an alternating diagram when there is a parametrized link $L'$ isotopic to $L$ whose standard
projection is regular and alternating. -/
def ParametrizedLink.AdmitsAlternatingDiagram {n : ℕ}
    (L : ParametrizedLink n) : Prop :=
  ∃ L' : ParametrizedLink n, L'.Isotopic L ∧
    ∃ hreg : L'.IsRegularProjection, L'.IsAlternatingProjection hreg

/-- **Admitting an alternating diagram is an isotopy invariant.** Let $L_1$ and $L_2$ be
parametrized links with $n$ components. If $L_1$ is isotopic to $L_2$ and $L_1$ admits an
alternating diagram, then $L_2$ admits an alternating diagram. -/
theorem ParametrizedLink.AdmitsAlternatingDiagram.of_isotopic {n : ℕ}
    {L₁ L₂ : ParametrizedLink n} (h : L₁.Isotopic L₂)
    (hL : L₁.AdmitsAlternatingDiagram) :
    L₂.AdmitsAlternatingDiagram := by
  obtain ⟨L', h', hreg, halt⟩ := hL
  exact ⟨L', h'.trans h, hreg, halt⟩

/-- **Links with a crossing-free regular projection admit alternating diagrams.** If a
parametrized link $L$ has a regular standard projection whose double-point set is empty, then
$L$ admits an alternating diagram.

The witness is $L$ itself, whose projection is alternating vacuously since it has no crossings. -/
theorem ParametrizedLink.admitsAlternatingDiagram_of_doublePointSet_eq_empty
    {n : ℕ} (L : ParametrizedLink n) (hreg : L.IsRegularProjection)
    (hempty : L.doublePointSet = ∅) :
    L.AdmitsAlternatingDiagram :=
  ⟨L, ParametrizedLink.Isotopic.refl L, hreg,
    L.isAlternatingProjection_of_doublePointSet_eq_empty hreg hempty⟩

/-- **The projected trace is the union of the projected components.** For a parametrized link
$L$ with $n$ components, the union over all components $i$ of the images of the projected curves
of $L$ equals the image of the trace of $L$ under the standard projection to the plane. -/
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
