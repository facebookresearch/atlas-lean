/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.LinearAlgebra.Orientation
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
public import Mathlib.Geometry.Euclidean.Triangle
public import Mathlib.Data.Set.Card
public import Mathlib.Analysis.Convex.Independent
public import Mathlib.Geometry.Euclidean.Sphere.Basic

public import MathlibExt.Geometry.Metric
public import Mathlib.Logic.Equiv.Fin.Rotate
public import MathlibExt.Data.Set.Triplewise

@[expose] public section

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open scoped EuclideanGeometry Finset

/-- Oriented angles make sense in 2d.

Note: this can't blindly be added to mathlib as it creates an "instance diamond"
with an instance for modules satisfying `is_empty`. -/
noncomputable instance Module.orientedEuclideanSpaceFinTwo : Module.Oriented ℝ ℝ² (Fin 2) :=
  ⟨Basis.orientation <| PiLp.basisFun 2 _ _⟩

/- Two-dimensional Euclidean space resolves its finrank fact through Mathlib's
canonical scoped `EuclideanSpace` instance
(`Mathlib/Analysis/InnerProductSpace/PiL2.lean`). -/
open scoped EuclideanSpace EuclideanGeometry

open scoped Real

namespace EuclideanGeometry

variable {V P : Type*} {n : ℕ}

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

variable [Module.Oriented ℝ V (Fin 2)] [Fact (Module.finrank ℝ V = 2)] {p : Fin n → P}

/-- **Sets with no three collinear points.** A set $A$ of points in the plane is non-trilinear
if no three distinct points of $A$ lie on a common line. -/
def NonTrilinear (A : Set P) : Prop :=
  A.Triplewise (fun x y z ↦ ¬ Collinear ℝ {x, y, z})

/-- **Sets with no $n$ collinear points.** A set $S$ of points in a Euclidean affine space has no
$n$ collinear points if no subset of $S$ consisting of exactly $n$ points is collinear. -/
def NonCollinearFor (n : ℕ) (S : Set P) : Prop :=
  ∀ (A : Set P), A ⊆ S → A.Finite → A.ncard = n → ¬ Collinear ℝ A

omit [Module.Oriented ℝ V (Fin 2)] [Fact (Module.finrank ℝ V = 2)] in
lemma NonCollinearFor.subset {n : ℕ} {S T : Set P} (h : S ⊆ T) (hS : NonCollinearFor n T) :
    NonCollinearFor n S := by
  intro A hA hFin hCard
  exact hS A (hA.trans h) hFin hCard

/-- **Sets containing a convex $n$-gon.** A set $P \subseteq \mathbb{R}^2$ contains a convex
$n$-gon if there is a set $S \subseteq P$ of exactly $n$ points that is convex independent: no
point of $S$ lies in the convex hull of the other points of $S$. -/
def HasConvexNGon (n : ℕ) (P : Set ℝ²) : Prop :=
  ∃ S : Finset ℝ², S.card = n ∧ ↑S ⊆ P ∧
    ConvexIndependent ℝ (fun x : (↑S : Set ℝ²) => (x : ℝ²))

/-- **Counterclockwise convex polygons.** Let $P$ be an oriented two-dimensional Euclidean affine
space. Points $p_0, \dots, p_{n-1} \in P$ form a counterclockwise convex polygon if for all
indices $i < j < k$ the oriented angle $\measuredangle p_i p_j p_k$ at $p_j$ has sign $-1$, that
is, $p_i, p_j, p_k$ are not collinear and lie in counterclockwise order with respect to the
orientation of $P$. Every list of at most two points qualifies. -/
def IsCcwConvexPolygon (p : Fin n → P) : Prop :=
  ∀ ⦃i j k⦄, i < j → j < k → (∡ (p i) (p j) (p k)).sign = -1

theorem IsCcwConvexPolygon.sign_oangle (hp : IsCcwConvexPolygon p) {i j k : Fin n}
  (hij : i < j) (hjk : j < k) : (∡ (p i) (p j) (p k)).sign = -1 := hp hij hjk

set_option linter.docPrime false in
theorem IsCcwConvexPolygon.sign_oangle' (hp : IsCcwConvexPolygon p) {i j k : Fin n}
    (hij : i < j) (hjk : j < k) : (∡ (p j) (p k) (p i)).sign = -1 := by
  rw [EuclideanGeometry.oangle_rotate_sign]
  exact hp hij hjk

set_option linter.docPrime false in
theorem IsCcwConvexPolygon.sign_oangle'' (hp : IsCcwConvexPolygon p) {i j k : Fin n}
    (hij : i < j) (hjk : j < k) : (∡ (p k) (p i) (p j)).sign = -1 := by
  rw [← EuclideanGeometry.oangle_rotate_sign]
  exact hp hij hjk

theorem IsCcwConvexPolygon.sign_oangle_finRotate (hp : IsCcwConvexPolygon p)
    (hn : 3 ≤ n) (i : Fin n) :
    (∡ (p i) (p <| finRotate _ i) (p <| finRotate _ (finRotate _ i))).sign = -1 := by
  obtain ⟨n, rfl⟩ := le_iff_exists_add'.mp hn
  by_cases hi : i = Fin.last (n + 2)
  · rw [hi, finRotate_last, finRotate_apply_zero]
    exact hp.sign_oangle'' Fin.zero_lt_one Fin.one_lt_last
  by_cases hi' : finRotate _ i = Fin.last (n + 2)
  · rw [hi', finRotate_last]
    refine hp.sign_oangle' ?_ ((Fin.le_last _).lt_of_ne hi)
    rw [Fin.pos_iff_ne_zero]
    rintro rfl
    rw [finRotate_apply_zero] at hi'
    exact Fin.one_lt_last.ne hi'
  apply hp.sign_oangle <;> apply (lt_finRotate_iff_ne_last _).2 <;> assumption

@[simp] theorem isCcwConvexPolygon_zero (p : Fin 0 → P) : IsCcwConvexPolygon p := finZeroElim

@[simp] theorem isCcwConvexPolygon_one (p : Fin 1 → P) : IsCcwConvexPolygon p := by intro; omega

@[simp] theorem isCcwConvexPolygon_two (p : Fin 2 → P) : IsCcwConvexPolygon p := by intro; omega

set_option linter.docPrime false in
theorem isCcwConvexPolygon_four' {p : Fin 4 → P} :
    IsCcwConvexPolygon p ↔ (∡ (p 0) (p 1) (p 2)).sign = -1 ∧ (∡ (p 1) (p 2) (p 3)).sign = -1 ∧
    (∡ (p 2) (p 3) (p 0)).sign = -1 ∧ (∡ (p 3) (p 0) (p 1)).sign = -1 := by
  refine ⟨fun h ↦ ?_, fun ⟨h1, h2, h3, h4⟩ ↦ ?_⟩
  · obtain ⟨h01, h12, h23⟩ : (0 : Fin 4) < 1 ∧ (1 : Fin 4) < 2 ∧ (2 : Fin 4) < 3 := by simp
    · repeat' constructor
      · exact h.sign_oangle h01 h12
      · exact h.sign_oangle h12 h23
      · exact h.sign_oangle' (h01.trans h12) h23
      · exact h.sign_oangle'' h01 (h12.trans h23)
  · intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp at hij hjk
    · exact h1
    · rw [EuclideanGeometry.oangle_rotate_sign]
      exact h4
    · rw [← EuclideanGeometry.oangle_rotate_sign]
      exact h3
    · exact h2

@[simp]
theorem isCcwConvexPolygon_four (A B C D : P) :
    IsCcwConvexPolygon ![A, B, C, D] ↔
      (∡ A B C).sign = -1 ∧ (∡ B C D).sign = -1 ∧ (∡ C D A).sign = -1 ∧ (∡ D A B).sign = -1 :=
  isCcwConvexPolygon_four'

/-- **Convex polygons.** Points $p_0, \dots, p_{n-1}$ of an oriented two-dimensional Euclidean
affine space form a convex polygon if one of the lists $p_0, p_1, \dots, p_{n-1}$ and
$p_0, p_{n-1}, p_{n-2}, \dots, p_1$ is a counterclockwise convex polygon: for any three of its
entries $q, r, s$, in the order in which they occur in that list, the oriented angle
$\measuredangle q r s$ at $r$ has sign $-1$. Thus for $n \ge 3$ the points are the vertices of a
strictly convex polygon, listed counterclockwise or clockwise starting from $p_0$; every list of
at most two points qualifies. -/
def IsConvexPolygon {n : ℕ} (p : Fin n → P) : Prop :=
  IsCcwConvexPolygon p ∨ IsCcwConvexPolygon fun i => p (-i)

/-- **Affinely independent triples are convex polygons.** If three points $A, B, C$ of an oriented
two-dimensional Euclidean affine space are affinely independent, then $A, B, C$ form a convex
polygon. -/
theorem isConvexPolygon_three_of_affineIndependent {A B C : P}
    (hABC : AffineIndependent ℝ ![A, B, C]) : IsConvexPolygon ![A, B, C] := by
  rw [← oangle_ne_zero_and_ne_pi_iff_affineIndependent, ← Real.Angle.sign_ne_zero_iff] at hABC
  cases hsABC : (∡ A B C).sign
  · exact (hABC hsABC).elim
  · left
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp at hij hjk
    exact hsABC
  · right
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp at hij hjk
    rw [EuclideanGeometry.oangle_rev, Real.Angle.sign_neg, neg_eq_iff_eq_neg]
    exact (oangle_rotate_sign A B C).trans hsABC

theorem isConvexPolygon_three_iff_affineIndependent {A B C : P} :
    IsConvexPolygon ![A, B, C] ↔ AffineIndependent ℝ ![A, B, C] := by
  refine ⟨fun h => ?_, isConvexPolygon_three_of_affineIndependent⟩
  rw [← oangle_ne_zero_and_ne_pi_iff_affineIndependent, ← Real.Angle.sign_ne_zero_iff]
  let p := ![A, B, C]
  change IsConvexPolygon p at h
  change Real.Angle.sign (∡ (p 0) (p 1) (p 2)) ≠ 0
  cases h with
  | inl h =>
    rw [h.sign_oangle (by simp) (by simp)]
    rintro ⟨⟩
  | inr h =>
    suffices Real.Angle.sign (∡ (p 0) (p 2) (p 1)) = -1 by
      rw [← oangle_swap₂₃_sign, this]; rintro ⟨⟩
    exact h.sign_oangle (i := 0) (j := 1) (k := 2) (by simp) (by simp)

theorem isConvexPolygon_triangle (t : Affine.Triangle ℝ P) : IsConvexPolygon t.points := by
  have : t.points = ![t.points 0, t.points 1, t.points 2] := by ext i; fin_cases i <;> rfl
  rw [this, isConvexPolygon_three_iff_affineIndependent, ← this]
  exact t.independent

/-- **Oriented triangle area.** Let $\omega$ be the area form of the given orientation of the
Euclidean plane, so that $\omega(u, v)$ is the signed area of the parallelogram spanned by the
vectors $u$ and $v$. For points $a$, $b$, $c$ of the plane, the oriented area of the triangle
with vertices $a$, $b$, $c$ is the real number $\omega(a - c, b - c) / 2$.

It changes sign when two vertices are swapped, and it is positive when $a$, $b$, $c$ are in
counterclockwise order and negative when they are in clockwise order. -/
noncomputable def orientedTriangleArea (a b c : P) : ℝ :=
  positiveOrientation.areaForm (a -ᵥ c) (b -ᵥ c) / 2

lemma orientedTriangleArea_eq_det (a b c : ℝ²) :
    orientedTriangleArea a b c =
    Matrix.det !![a 0, b 0, c 0;
                  a 1, b 1, c 1;
                  1,   1,   1] / 2 := by
  rw [orientedTriangleArea, Orientation.areaForm_to_volumeForm,
    positiveOrientation.volumeForm_robust (EuclideanSpace.basisFun (Fin 2) ℝ) rfl,
    Module.Basis.det_apply]
  suffices (a 0 - c 0) * (b 1 - c 1) - (b 0 - c 0) * (a 1 - c 1) =
      a 0 * b 1 - a 0 * c 1 - b 0 * a 1 + b 0 * c 1 + c 0 * a 1 - c 0 * b 1 by
    simp [Matrix.det_fin_two, Matrix.det_fin_three, Module.Basis.toMatrix, this]
  ring

/-- **Maximum number of distinct distance counts.** For a finite set $X \subseteq \mathbb{R}^2$
and a point $x \in X$, let $R_X(x)$ be the number of distinct distances $\lvert y - x \rvert$
from $x$ to the points $y \in X$ other than $x$. For $n \in \mathbb{N}$, $g(n)$ is the maximum,
over all sets $X \subseteq \mathbb{R}^2$ of exactly $n$ points, of the number of distinct values
among the numbers $R_X(x)$ with $x \in X$. -/
noncomputable def maximalDistinctDistancesFrom (n : ℕ) : ℕ :=
  sSup {#(X.image (distinctDistancesFrom X)) | (X : Finset ℝ²) (_ : #X = n)}

/-- **Points in general position.** A set $X \subseteq \mathbb{R}^2$, finite or infinite, is in
_general position_ if no three distinct points of $X$ are collinear and no four distinct points
of $X$ lie on a common circle. -/
def InGeneralPosition (X : Set ℝ²) : Prop :=
  NonTrilinear X ∧ ∀ T ⊆ X, T.ncard = 4 → ¬Cospherical T

/-- **Right-angled triangles.** Points $a, b, c$ of a Euclidean affine space are the vertices of a
right-angled triangle if they are pairwise distinct and the unoriented angle at one of the three
vertices equals $\pi / 2$: $\angle bac = \pi / 2$, $\angle abc = \pi / 2$ or
$\angle bca = \pi / 2$.

The distinctness hypothesis rules out degenerate triples, whose angles can coincide with
$\pi / 2$. -/
def IsRightAngled (a b c : P) : Prop :=
  a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    (∠ b a c = π / 2 ∨ ∠ a b c = π / 2 ∨ ∠ b c a = π / 2)

/--
**Isosceles trapezoids.** Points $a, b, c, d \in \mathbb{R}^2$ are the vertices, in
counterclockwise order, of an isosceles trapezoid if they are in strictly convex position and
listed counterclockwise (for any three of them $p, q, r$, in the order in which they occur in the
list $a, b, c, d$, the oriented angle $\measuredangle p q r$ at $q$ has sign $-1$), the line
through $a$ and $b$ is parallel to the line through $c$ and $d$ (the two bases), and the
diagonals have equal length: $\operatorname{dist}(a, c) = \operatorname{dist}(b, d)$.

One pair of parallel sides together with equal diagonals is the classical characterization of an
isosceles trapezoid; in particular it rules out non-rectangular parallelograms.
-/
def IsIsoscelesTrapezoid (a b c d : ℝ²) : Prop :=
  IsCcwConvexPolygon ![a, b, c, d] ∧
  (affineSpan ℝ {a, b}).Parallel (affineSpan ℝ {c, d}) ∧
  dist a c = dist b d

end EuclideanGeometry

def IsIsosceles {α : Type*} [Dist α] (p q r : α) : Prop :=
  dist p q = dist q r ∨ dist q r = dist r p ∨ dist r p = dist p q

nonrec def Set.IsIsosceles {α : Type*} [Dist α] (A : Set α) :=
  Nonempty A ∧ A.Triplewise (IsIsosceles · · ·)

/-- **Isosceles-free sets.** A set $A$ in a space with a distance function $d$ is isosceles-free if
there are no three distinct points $x, y, z \in A$ such that two of the distances $d(x, y)$,
$d(y, z)$, $d(z, x)$ are equal. -/
def Set.IsIsoscelesFree {α : Type*} [Dist α] (A : Set α) : Prop :=
  A.Triplewise fun x y z ↦ ¬ _root_.IsIsosceles x y z

theorem Set.IsIsoscelesFree.mono {α : Type*} [Dist α] {s t : Set α} (h : t ⊆ s)
    (hs : s.IsIsoscelesFree) : t.IsIsoscelesFree :=
  Set.Triplewise.mono h hs
