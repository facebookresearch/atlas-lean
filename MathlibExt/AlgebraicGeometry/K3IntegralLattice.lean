/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IntegralBetti
public import MathlibExt.AlgebraicGeometry.HolomorphicDeRham
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Data.Matrix.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The concrete integral K3 cup lattice on actual analytification

Cohomology is the integral constant-sheaf derived cohomology of the
canonical complex-point topology. The surface volume form consists of
actual holomorphic tangent two-covectors, nonzero at every point.
H^1(O_an) is the actual right-derived global-section module of the actual
holomorphic structure sheaf. The lattice target is the explicit integer
22-by-22 Gram matrix 3U plus two negative E8 Cartan blocks.

No cohomology vector space, free lattice, intersection pairing or Hodge
isometry is supplied as an input oracle. The requested comparison must
match every value of the actual integral cup product.

Source: Huybrechts, *Lectures on K3 surfaces*, Chapter1, Definition3.1
and Proposition3.5, https://www.math.uni-bonn.de/people/huybrech/K3Global.pdf.
This is a cup-lattice request; it asserts no rational Hodge Torelli theorem.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.K3IntegralLattice

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry
open AnalyticRealization HolomorphicDeRham

abbrev IntegralSecond (X : ComplexScheme) :=
  IntegralBetti.Cohomology (ComplexAnalytification.space X) 2
abbrev IntegralTop (X : ComplexScheme) :=
  IntegralBetti.Cohomology (ComplexAnalytification.space X) 4

variable (X : ComplexScheme) [AnalyticManifold X 2]

instance holomorphicEvaluation_additive :
    (SheafOfModules.evaluation (holomorphicRingSheaf X 2)
      (op (⊤ : Opens (ComplexAnalytification.space X)))).Additive := by
  unfold SheafOfModules.evaluation
  infer_instance

/-- Actual H^1 of the actual holomorphic structure sheaf. -/
abbrev holomorphicH1 :=
  ((SheafOfModules.evaluation (holomorphicRingSheaf X 2)
    (op (⊤ : Opens (ComplexAnalytification.space X)))).rightDerived 1).obj
      (SheafOfModules.unit (holomorphicRingSheaf X 2))

/-- A nowhere-vanishing actual holomorphic top form trivializes the analytic canonical line. -/
structure HolomorphicVolume where
  form : holomorphicForms X 2 ⊤ 2
  nonvanishing : ∀ x : ComplexAnalytification.space X, form.1 ⟨x, by trivial⟩ ≠ 0

/-- The edges of the `E₈` Dynkin diagram in Bourbaki's labelling, zero-based:
the chain `0-2-3-4-5-6-7` with vertex `1` attached to vertex `3`. -/
def e8Edges : Finset (ℕ × ℕ) := {(0, 2), (2, 3), (1, 3), (3, 4), (4, 5), (5, 6), (6, 7)}

/-- Adjacency in the `E₈` Dynkin diagram. -/
def e8Adjacent (a b : ℕ) : Prop := (a, b) ∈ e8Edges ∨ (b, a) ∈ e8Edges

instance : DecidableRel e8Adjacent := fun a b ↦
  inferInstanceAs (Decidable ((a, b) ∈ e8Edges ∨ (b, a) ∈ e8Edges))

/-- Explicit Gram matrix of `3U ⊕ E₈(-1) ⊕ E₈(-1)`, with no supplied lattice
data: indices `0, …, 5` form three hyperbolic planes, and `6, …, 13` and
`14, …, 21` form two negative `E₈` Cartan blocks. -/
def gram : Matrix (Fin 22) (Fin 22) ℤ := fun i j ↦
  if i.val < 6 then
    if j.val < 6 ∧ i.val / 2 = j.val / 2 ∧ i ≠ j then 1 else 0
  else if j.val < 6 then 0
  else if (i.val - 6) / 8 = (j.val - 6) / 8 then
    if (i.val - 6) % 8 = (j.val - 6) % 8 then -2
    else if e8Adjacent ((i.val - 6) % 8) ((j.val - 6) % 8) then 1 else 0
  else 0

/-- The actual integer bilinear expression of that fixed matrix. -/
def latticePairing (v w : Fin 22 → ℤ) : ℤ := ∑ i, ∑ j, v i * gram i j * w j

/-- An identification of the integral cohomology of a complex scheme $X$ with the K3 lattice:
$\mathbb{Z}$-linear isomorphisms $H^2(X^{\mathrm{an}}, \mathbb{Z}) \cong \mathbb{Z}^{22}$ and
$H^4(X^{\mathrm{an}}, \mathbb{Z}) \cong \mathbb{Z}$, for the cohomology of the constant sheaf
$\mathbb{Z}$ on the space of complex points of $X$, under which the cup product
$H^2 \times H^2 \to H^4$ becomes the bilinear form with Gram matrix `gram` of
$3U \oplus E_8(-1) \oplus E_8(-1)$. -/
structure IntegralCupComparison (X : ComplexScheme) where
  second : IntegralSecond X ≃ₗ[ℤ] (Fin 22 → ℤ)
  top : IntegralTop X ≃ₗ[ℤ] ℤ
  cup_normalization : ∀ x y : IntegralSecond X,
    top (IntegralBetti.cup (ComplexAnalytification.space X) x y) =
      latticePairing (second x) (second y)

end MathlibExt.AlgebraicGeometry.K3IntegralLattice
