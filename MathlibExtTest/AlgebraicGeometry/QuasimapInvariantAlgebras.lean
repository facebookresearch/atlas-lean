/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.QuasimapInvariantAlgebras
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Basic.Complex.Basic

/-!
# Tests for the local irrelevant-ideal condition of the GIT orbit map

The orbit map to `Proj` needs only that the basic opens of the positive-degree
homogeneous elements cover the source. On the punctured plane `𝔸² ∖ {0}`,
the source of the scalar quotient `𝔸² ∖ {0} → ℙ¹`, the two coordinates cover,
although they generate a proper ideal of its global sections `ℂ[x, y]`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MathlibExt.AlgebraicGeometry.QuasimapInvariantAlgebras

/-- Basic opens of two positive-degree homogeneous elements that cover suffice. -/
theorem irrelevantCovers_of_two {σ : Type*} {A : Type} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {X : Scheme.{0}}
    (f : A →+* Γ(X, ⊤)) {a b : A} {i j : ℕ} (hi : 0 < i) (hj : 0 < j) (ha : a ∈ 𝒜 i)
    (hb : b ∈ 𝒜 j) (h : X.basicOpen (f a) ⊔ X.basicOpen (f b) = ⊤) :
    IrrelevantCovers 𝒜 f := by
  refine eq_top_iff.mpr (h.symm.le.trans (sup_le ?_ ?_))
  · exact le_iSup (fun ir : Σ' i r, 0 < i ∧ r ∈ 𝒜 i ↦ X.basicOpen (f ir.2.1)) ⟨i, a, hi, ha⟩
  · exact le_iSup (fun ir : Σ' i r, 0 < i ∧ r ∈ 𝒜 i ↦ X.basicOpen (f ir.2.1)) ⟨j, b, hj, hb⟩

/-- The polynomial ring `ℂ[x, y]`. -/
abbrev PlaneRing := MvPolynomial (Fin 2) ℂ

/-- A polynomial as a global function on the affine plane. -/
def planeFunction (p : PlaneRing) : Γ(Spec (.of PlaneRing), ⊤) :=
  (Scheme.ΓSpecIso (.of PlaneRing)).inv p

/-- The punctured plane `D(x) ∪ D(y)`. -/
def puncturedPlane : (Spec (.of PlaneRing)).Opens :=
  (Spec (.of PlaneRing)).basicOpen (planeFunction (MvPolynomial.X 0)) ⊔
    (Spec (.of PlaneRing)).basicOpen (planeFunction (MvPolynomial.X 1))

/-- Restriction of polynomials to the punctured plane. -/
def puncturedRestriction : PlaneRing →+* Γ(puncturedPlane.toScheme, ⊤) :=
  puncturedPlane.ι.appTop.hom.comp (Scheme.ΓSpecIso (.of PlaneRing)).inv.hom

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- The degree grading of `ℂ[x, y]` satisfies the local condition on the punctured plane. -/
example : IrrelevantCovers (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) puncturedRestriction := by
  refine irrelevantCovers_of_two _ _ one_pos one_pos (MvPolynomial.isHomogeneous_X ℂ 0)
    (MvPolynomial.isHomogeneous_X ℂ 1) ?_
  have hx := Scheme.preimage_basicOpen puncturedPlane.ι (planeFunction (MvPolynomial.X 0))
  have hy := Scheme.preimage_basicOpen puncturedPlane.ι (planeFunction (MvPolynomial.X 1))
  change _ = puncturedPlane.toScheme.basicOpen (puncturedRestriction (MvPolynomial.X 0)) at hx
  change _ = puncturedPlane.toScheme.basicOpen (puncturedRestriction (MvPolynomial.X 1)) at hy
  rw [← hx, ← hy, ← Scheme.Hom.preimage_sup]
  exact puncturedPlane.ι_preimage_self
