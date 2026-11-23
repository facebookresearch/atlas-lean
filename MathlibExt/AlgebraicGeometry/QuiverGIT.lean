/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Actual finite-quiver representations and determinant linearizations

Arrow matrices and the product of vertex general linear groups fix the
representation scheme and its base-change action. The character is
`χθ(g)=∏ det(g_v)^θ_v`, and a polynomial semi-invariant satisfies
`f(g⋅M)=χθ(g)^m f(M)`. With this convention, King's numerical inequality
is `θ(dim W) ≥ 0` for every subrepresentation when `θ(dim M)=0`.

Sources: A. King, *Moduli of representations of finite-dimensional
algebras*, Quart. J. Math. 45 (1994), §3; M. Reineke,
https://arxiv.org/abs/0802.2147, §3, Theorem 3.8 and the displayed
semi-invariant/character formulas. Reineke's slope convention uses the
opposite sign in its determinant character, giving the same inequality.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.QuiverGIT

open CategoryTheory
open _root_.AlgebraicGeometry

universe u

/-- A finite quiver given by actual source and target maps on its finite
arrow set; parallel arrows and oriented cycles are allowed. -/
structure FiniteQuiver where
  Vertex : Type
  Arrow : Type
  [vertices : Fintype Vertex]
  [arrows : Fintype Arrow]
  [decVertices : DecidableEq Vertex]
  [decArrows : DecidableEq Arrow]
  source : Arrow → Vertex
  target : Arrow → Vertex

attribute [instance] FiniteQuiver.vertices FiniteQuiver.arrows
  FiniteQuiver.decVertices FiniteQuiver.decArrows

variable (Q : FiniteQuiver) (d : Q.Vertex → ℕ) (k : Type u) [Field k]

/-- The actual affine representation space of compatible arrow matrices. -/
abbrev Representation := (a : Q.Arrow) → Matrix (Fin (d (Q.target a))) (Fin (d (Q.source a))) k

/-- Every matrix entry is an actual coordinate of the affine scheme. -/
abbrev Coordinate := (a : Q.Arrow) × (Fin (d (Q.target a)) × Fin (d (Q.source a)))

/-- The actual polynomial ring of matrix-entry coordinates. -/
abbrev CoordinateRing := MvPolynomial (Coordinate Q d) k

/-- The actual affine representation scheme. -/
abbrev representationScheme : Scheme.{u} := Spec (CommRingCat.of (CoordinateRing Q d k))

/-- Vertex base changes are the actual product of general linear groups. -/
abbrev BaseChangeGroup := (v : Q.Vertex) → Matrix.GeneralLinearGroup (Fin (d v)) k

/-- The normalized action sends an arrow to `g_target A g_source⁻¹`. -/
def baseChange (g : BaseChangeGroup Q d k) (M : Representation Q d k) : Representation Q d k :=
  fun a ↦ (g (Q.target a)).val * M a * ((g (Q.source a))⁻¹).val

@[simp] theorem baseChange_one (M : Representation Q d k) : baseChange Q d k 1 M = M := by
  funext a
  simp [baseChange]

theorem baseChange_mul (g h : BaseChangeGroup Q d k) (M : Representation Q d k) :
    baseChange Q d k (g * h) M = baseChange Q d k g (baseChange Q d k h M) := by
  funext a
  simp [baseChange, Matrix.mul_assoc, mul_inv_rev]

/-- The determinant character is an actual monoid homomorphism to units. -/
def determinantCharacter (θ : Q.Vertex → ℤ) : BaseChangeGroup Q d k →* kˣ where
  toFun g := ∏ v, (Matrix.GeneralLinearGroup.det (g v)) ^ (θ v)
  map_one' := by simp
  map_mul' := by
    intro g h
    simp only [Pi.mul_apply, map_mul, mul_zpow]
    exact Finset.prod_mul_distrib

/-- Evaluate a polynomial at the actual arrow matrix entries. -/
def evaluate (M : Representation Q d k) (f : CoordinateRing Q d k) : k :=
  MvPolynomial.eval (fun x ↦ M x.1 x.2.1 x.2.2) f

/-- Polynomial semi-invariance is a global law for every actual base
change and every actual representation, not an assumption only on one orbit.
It is tested on rational points, so the field is infinite: there a polynomial
identity is determined by its values. Over a finite field the test degenerates
(every determinant character into `𝔽₂ˣ` is trivial, so the constant `1` would be
semi-invariant for every weight). -/
def IsSemiInvariant [Infinite k] (θ : Q.Vertex → ℤ) (m : ℕ) (f : CoordinateRing Q d k) :
    Prop :=
  ∀ (g : BaseChangeGroup Q d k) (M : Representation Q d k),
    evaluate Q d k (baseChange Q d k g M) f =
      (determinantCharacter Q d k θ g : k) ^ m * evaluate Q d k M f

/-- The actual semi-invariant nonvanishing definition of character
semistability, over an infinite field. -/
def CharacterSemistable [Infinite k] (θ : Q.Vertex → ℤ) (M : Representation Q d k) :
    Prop :=
  ∃ m : ℕ, 0 < m ∧ ∃ f : CoordinateRing Q d k,
    IsSemiInvariant Q d k θ m f ∧ evaluate Q d k M f ≠ 0

/-- The exact integer character weight of the fixed dimension vector. -/
def dimensionWeight (θ : Q.Vertex → ℤ) : ℤ := ∑ v, θ v * (d v : ℤ)

/-- Subrepresentations are actual compatible vertex submodules. -/
def IsSubrepresentation (M : Representation Q d k)
    (W : (v : Q.Vertex) → Submodule k (Fin (d v) → k)) : Prop :=
  ∀ a : Q.Arrow, (W (Q.source a)).map (Matrix.mulVecLin (M a)) ≤ W (Q.target a)

/-- Its numerical weight is computed from the actual dimensions of those submodules. -/
def subrepresentationWeight (θ : Q.Vertex → ℤ)
    (W : (v : Q.Vertex) → Submodule k (Fin (d v) → k)) : ℤ :=
  ∑ v, θ v * (Module.finrank k (W v) : ℤ)

/-- King's numerical condition, with the sign fixed by the displayed
covariant polynomial semi-invariant convention. -/
def NumericallySemistable (θ : Q.Vertex → ℤ) (M : Representation Q d k) : Prop :=
  ∀ W, IsSubrepresentation Q d k M W → 0 ≤ subrepresentationWeight Q d k θ W

end MathlibExt.AlgebraicGeometry.QuiverGIT
