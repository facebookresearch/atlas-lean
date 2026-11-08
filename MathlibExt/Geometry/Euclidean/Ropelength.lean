/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Ropelength core: thickness and contour length in Euclidean 3-space
-/
module

public import Mathlib.Geometry.Euclidean.Circumcenter
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import MathlibExt.Analysis.Calculus.CurveLength

@[expose] public section

namespace MathlibExt.Geometry.Euclidean.Ropelength

/-!
# Ropelength core in Euclidean 3-space

For three points in Euclidean 3-space, `circumradiusENN` is the ordinary
circumradius when the points are affinely independent and `⊤` when they
are collinear or not distinct. The thickness of a set is the infimum of
these extended circumradii over all triples of points of the set. Since
degenerate triples have value `⊤`, this is the usual infimum over
pairwise distinct triples without restricting the index set.

`contourLength` is extended variation on a compact interval, and
`ropelengthRatio` is contour length divided by the thickness of the
whole trace. These are the geometric quantities for one parametrized
curve. Infima over isotopy types, crossing numbers, and alternating
diagrams are separate later layers for catalogue constants 22a and 22b;
they are not defined in this core file.

Source: Optimization Problems, `constants/22a.md` and
`constants/22b.md`, frozen at teorth/optimizationproblems commit
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`, following Cantarella,
Kusner, and Sullivan, *On the minimum ropelength of knots and links*,
Invent. Math. 150 (2002), 257--286.
-/

/-- Euclidean 3-space. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The ordered triple `(p, q, r)` as a `Fin 3`-indexed family. -/
def triplePoints (p q r : R3) : Fin 3 → R3 :=
  ![p, q, r]

/-- The triangle with vertices `p`, `q`, and `r`, from an affine
independence proof. -/
def triangleOf (p q r : R3)
    (h : AffineIndependent ℝ (triplePoints p q r)) :
    Affine.Triangle ℝ R3 :=
  ⟨triplePoints p q r, h⟩

open Classical in
/-- The total extended circumradius of three points. Affinely
independent triples use Mathlib's simplex circumradius; every collinear
or coincident triple has value `⊤`, matching the convention that
collinear points determine a circle of infinite radius. -/
noncomputable def circumradiusENN (p q r : R3) : ENNReal :=
  if h : AffineIndependent ℝ (triplePoints p q r) then
    ENNReal.ofReal (triangleOf p q r h).circumradius
  else
    ⊤

theorem circumradiusENN_of_affineIndependent {p q r : R3}
    (h : AffineIndependent ℝ (triplePoints p q r)) :
    circumradiusENN p q r =
      ENNReal.ofReal (triangleOf p q r h).circumradius := by
  rw [circumradiusENN, dite_eq_left h]

/-- Agreement with the circumradius of every Mathlib triangle having the
same three ordered vertices. -/
theorem circumradiusENN_eq_ofReal_circumradius {p q r : R3}
    (t : Affine.Triangle ℝ R3) (h0 : t.points 0 = p)
    (h1 : t.points 1 = q) (h2 : t.points 2 = r) :
    circumradiusENN p q r = ENNReal.ofReal t.circumradius := by
  have hpoints : t.points = triplePoints p q r := by
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hind : AffineIndependent ℝ (triplePoints p q r) :=
    hpoints ▸ t.independent
  have htriangle : t = triangleOf p q r hind := by
    apply Affine.Simplex.ext
    intro i
    exact congrFun hpoints i
  rw [circumradiusENN_of_affineIndependent hind, ← htriangle]

theorem circumradiusENN_eq_top_of_not_affineIndependent {p q r : R3}
    (h : ¬AffineIndependent ℝ (triplePoints p q r)) :
    circumradiusENN p q r = ⊤ := by
  rw [circumradiusENN, dite_eq_right h]

/-- Collinear triples have infinite extended circumradius. -/
theorem circumradiusENN_eq_top_of_collinear {p q r : R3}
    (h : Collinear ℝ ({p, q, r} : Set R3)) :
    circumradiusENN p q r = ⊤ := by
  apply circumradiusENN_eq_top_of_not_affineIndependent
  have hnot := (collinear_iff_not_affineIndependent_set).mp h
  exact hnot

private theorem not_affineIndependent_of_apply_eq {p q r : R3}
    {i j : Fin 3} (hij : i ≠ j)
    (h : triplePoints p q r i = triplePoints p q r j) :
    ¬AffineIndependent ℝ (triplePoints p q r) := by
  intro hind
  exact hind.injective.ne hij h

/-- Coincident triples are degenerate, not radius zero. -/
theorem circumradiusENN_eq_top_of_eq_left {p q r : R3} (h : p = q) :
    circumradiusENN p q r = ⊤ := by
  apply circumradiusENN_eq_top_of_not_affineIndependent
  apply not_affineIndependent_of_apply_eq (i := 0) (j := 1) (by decide)
  simp [triplePoints, h]

theorem circumradiusENN_eq_top_of_eq_mid {p q r : R3} (h : p = r) :
    circumradiusENN p q r = ⊤ := by
  apply circumradiusENN_eq_top_of_not_affineIndependent
  apply not_affineIndependent_of_apply_eq (i := 0) (j := 2) (by decide)
  simp [triplePoints, h]

theorem circumradiusENN_eq_top_of_eq_right {p q r : R3} (h : q = r) :
    circumradiusENN p q r = ⊤ := by
  apply circumradiusENN_eq_top_of_not_affineIndependent
  apply not_affineIndependent_of_apply_eq (i := 1) (j := 2) (by decide)
  simp [triplePoints, h]

private theorem circumradiusENN_eq_of_triplePoints_eq_comp_symm
    {p q r p' q' r' : R3} (e : Fin 3 ≃ Fin 3)
    (hpoints : triplePoints p' q' r' = triplePoints p q r ∘ e.symm) :
    circumradiusENN p' q' r' = circumradiusENN p q r := by
  by_cases h : AffineIndependent ℝ (triplePoints p q r)
  · have h' : AffineIndependent ℝ (triplePoints p' q' r') := by
      rw [hpoints]
      exact (affineIndependent_equiv e.symm).2 h
    have htriangle :
        triangleOf p' q' r' h' = (triangleOf p q r h).reindex e := by
      apply Affine.Simplex.ext
      intro i
      exact congrFun hpoints i
    rw [circumradiusENN_of_affineIndependent h',
      circumradiusENN_of_affineIndependent h, htriangle,
      Affine.Simplex.circumradius_reindex]
  · have h' : ¬AffineIndependent ℝ (triplePoints p' q' r') := by
      intro hh
      apply h
      rw [hpoints] at hh
      exact (affineIndependent_equiv e.symm).1 hh
    rw [circumradiusENN_eq_top_of_not_affineIndependent h',
      circumradiusENN_eq_top_of_not_affineIndependent h]

/-- The extended circumradius is unchanged by swapping the first two
points. -/
theorem circumradiusENN_swap_left (p q r : R3) :
    circumradiusENN q p r = circumradiusENN p q r := by
  apply circumradiusENN_eq_of_triplePoints_eq_comp_symm
    (Equiv.swap (0 : Fin 3) 1)
  funext i
  fin_cases i <;> rfl

/-- The extended circumradius is unchanged by swapping the last two
points. -/
theorem circumradiusENN_swap_right (p q r : R3) :
    circumradiusENN p r q = circumradiusENN p q r := by
  apply circumradiusENN_eq_of_triplePoints_eq_comp_symm
    (Equiv.swap (1 : Fin 3) 2)
  funext i
  fin_cases i <;> rfl

/-- The extended circumradius is unchanged by reversing the triple. -/
theorem circumradiusENN_reverse (p q r : R3) :
    circumradiusENN r q p = circumradiusENN p q r := by
  apply circumradiusENN_eq_of_triplePoints_eq_comp_symm
    (Equiv.swap (0 : Fin 3) 2)
  funext i
  fin_cases i <;> rfl

private theorem circumradiusENN_affineIsometryEquiv
    (f : R3 ≃ᵃⁱ[ℝ] R3) (p q r : R3) :
    circumradiusENN (f p) (f q) (f r) = circumradiusENN p q r := by
  by_cases h : AffineIndependent ℝ (triplePoints p q r)
  · have h' : AffineIndependent ℝ (triplePoints (f p) (f q) (f r)) := by
      have hfun : triplePoints (f p) (f q) (f r) =
          f.toAffineIsometry.toAffineMap ∘ triplePoints p q r := by
        funext i
        fin_cases i <;> rfl
      rw [hfun]
      exact h.map' f.toAffineIsometry.toAffineMap
        f.toAffineIsometry.injective
    have htriangle :
        triangleOf (f p) (f q) (f r) h' =
          (triangleOf p q r h).map f.toAffineIsometry.toAffineMap
            f.toAffineIsometry.injective := by
      apply Affine.Simplex.ext
      intro i
      fin_cases i <;> rfl
    rw [circumradiusENN_of_affineIndependent h',
      circumradiusENN_of_affineIndependent h, htriangle,
      Affine.Simplex.circumradius_map]
  · have h' : ¬AffineIndependent ℝ (triplePoints (f p) (f q) (f r)) := by
      intro hh
      apply h
      have hfun : triplePoints p q r =
          f.symm.toAffineIsometry.toAffineMap ∘
            triplePoints (f p) (f q) (f r) := by
        funext i
        fin_cases i <;> simp [triplePoints]
      rw [hfun]
      exact hh.map' f.symm.toAffineIsometry.toAffineMap
        f.symm.toAffineIsometry.injective
    rw [circumradiusENN_eq_top_of_not_affineIndependent h',
      circumradiusENN_eq_top_of_not_affineIndependent h]

/-- The extended circumradius is translation invariant. -/
theorem circumradiusENN_vadd (v p q r : R3) :
    circumradiusENN (v +ᵥ p) (v +ᵥ q) (v +ᵥ r) =
      circumradiusENN p q r :=
  circumradiusENN_affineIsometryEquiv
    (AffineIsometryEquiv.constVAdd ℝ R3 v) p q r

/-- The thickness of a subset of Euclidean 3-space: the infimum of the
extended circumradii of all triples of points of the set. Degenerate
triples contribute `⊤`, so this is the infimum over pairwise distinct
triples. -/
noncomputable def thickness (s : Set R3) : ENNReal :=
  ⨅ p ∈ s, ⨅ q ∈ s, ⨅ r ∈ s, circumradiusENN p q r

/-- Thickness is at most the extended circumradius of every triple from
the set. -/
theorem thickness_le {s : Set R3} {p q r : R3}
    (hp : p ∈ s) (hq : q ∈ s) (hr : r ∈ s) :
    thickness s ≤ circumradiusENN p q r := by
  unfold thickness
  calc
    (⨅ p ∈ s, ⨅ q ∈ s, ⨅ r ∈ s, circumradiusENN p q r) ≤
        ⨅ q ∈ s, ⨅ r ∈ s, circumradiusENN p q r :=
      iInf₂_le p hp
    _ ≤ ⨅ r ∈ s, circumradiusENN p q r := iInf₂_le q hq
    _ ≤ circumradiusENN p q r := iInf₂_le r hr

/-- Thickness is antitone in the set: enlarging a set can only add
triples and hence can only decrease the infimum. -/
theorem thickness_anti {s t : Set R3} (h : s ⊆ t) :
    thickness t ≤ thickness s := by
  unfold thickness
  apply le_iInf₂
  intro p hp
  apply le_iInf₂
  intro q hq
  apply le_iInf₂
  intro r hr
  exact iInf₂_le_of_le p (h hp) (iInf₂_le_of_le q (h hq)
    (iInf₂_le_of_le r (h hr) le_rfl))

/-- The empty set has infinite thickness, as an empty infimum in
`ENNReal`. -/
@[simp]
theorem thickness_empty : thickness (∅ : Set R3) = ⊤ := by
  simp [thickness]

/-- A singleton has infinite thickness: its only triple is degenerate. -/
theorem thickness_singleton (p : R3) : thickness {p} = ⊤ := by
  apply le_antisymm le_top
  unfold thickness
  apply le_iInf₂
  intro x hx
  apply le_iInf₂
  intro y hy
  apply le_iInf₂
  intro z _hz
  simp only [Set.mem_singleton_iff] at hx hy
  rw [hx, hy, circumradiusENN_eq_top_of_eq_left rfl]

/-- The contour length of a parametrized curve on `[a, b]`, defined as
extended variation. For `C¹` curves this is the integral of speed by
`contourLength_eq_ofReal_integral_norm_deriv`. -/
noncomputable def contourLength (γ : ℝ → R3) (a b : ℝ) : ENNReal :=
  eVariationOn γ (Set.Icc a b)

/-- For a `C¹` curve, contour length is the integral of speed. -/
theorem contourLength_eq_ofReal_integral_norm_deriv {γ : ℝ → R3}
    {a b : ℝ} (hab : a ≤ b) (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b)) :
    contourLength γ a b =
      ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) :=
  MetaMathlibExt.curve_length_eq_integral_norm_deriv hab hγ

/-- The ropelength ratio of one parametrized curve on `[a, b]`:
contour length divided by the thickness of its whole trace. The
ropelength of a knot or link type is a further infimum of this ratio
over representatives of the type and is not defined here. -/
noncomputable def ropelengthRatio (γ : ℝ → R3) (a b : ℝ) : ENNReal :=
  contourLength γ a b / thickness (γ '' Set.Icc a b)

end MathlibExt.Geometry.Euclidean.Ropelength
