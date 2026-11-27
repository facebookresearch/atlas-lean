/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The fan, affine-chart and face-map definitions specialize
TauCetiProject/TauCeti, revision
62bbc0596dc3539d488232e4e924a338548ea0a9,
TauCeti/Geometry/Toric/Algebraic/Fan/Basic.lean,
TauCeti/Geometry/Toric/Algebraic/AffineScheme.lean and FaceLocalization.lean.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in that repository's LICENSE.
Authors: The Tau Ceti contributors.
Modifications: use the standard lattice Z^n and actual Mathlib cone faces;
allow arbitrary commutative coefficients in the affine charts. The source's
completed fan-gluing theorem is a separate existing integration dependency.
-/
module

public import Mathlib.Geometry.Convex.Cone.Face.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.Fintype.BigOperators

/-!
# Actual finite-fan coordinates for Cox and tropical interfaces

Cones are actual rational salient pointed cones in R^n. Their intersections
are faces, and the fan is closed under actual cone faces. This includes
nonsimplicial fans. Every affine chart is the spectrum of the actual
dual-semigroup algebra; face maps preserve each character monomial.

The `Realization` contract identifies a supplied toric scheme through those
fixed charts and their Cartesian overlaps. It does not request the already
completed public-source fan-gluing constructor again.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FiniteToricCoordinates

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped BigOperators

abbrev Lattice (n : ℕ) := Fin n → ℤ
abbrev RealSpace (n : ℕ) := Fin n → ℝ
abbrev Cone (n : ℕ) := PointedCone ℝ (RealSpace n)

def latticeCast (n : ℕ) : Lattice n →+ RealSpace n where
  toFun a := fun i ↦ (a i : ℝ)
  map_zero' := by ext i; simp
  map_add' a b := by ext i; simp

def character (n : ℕ) (u : Lattice n) : RealSpace n →ₗ[ℝ] ℝ where
  toFun x := ∑ i, (u i : ℝ) * x i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.mul_sum, mul_left_comm]

def IsRational {n : ℕ} (σ : Cone n) : Prop :=
  ∃ s : Finset (Lattice n), σ = PointedCone.hull ℝ (latticeCast n '' (s : Set _))

structure FiniteFan (n : ℕ) where
  cones : Finset (Cone n)
  rational : ∀ σ ∈ cones, IsRational σ
  salient : ∀ σ ∈ cones, (σ : ConvexCone ℝ (RealSpace n)).Salient
  faces : ∀ σ ∈ cones, ∀ τ : Cone n, τ.IsFaceOf σ → τ ∈ cones
  intersection_face : ∀ σ ∈ cones, ∀ τ ∈ cones, (σ ⊓ τ).IsFaceOf σ

namespace FiniteFan

variable {n : ℕ} (F : FiniteFan n)

abbrev Face := {σ : Cone n // σ ∈ F.cones}

theorem inf_mem (σ τ : Face F) : σ.val ⊓ τ.val ∈ F.cones :=
  F.faces σ.val σ.property _ (F.intersection_face σ.val σ.property τ.val τ.property)

def intersection (σ τ : Face F) : Face F := ⟨σ.val ⊓ τ.val, F.inf_mem σ τ⟩

def support : Set (RealSpace n) := ⋃ σ ∈ F.cones, (σ : Set (RealSpace n))

def IsComplete : Prop := F.support = Set.univ

end FiniteFan

def coneSpan {n : ℕ} (σ : Cone n) : Submodule ℝ (RealSpace n) :=
  Submodule.span ℝ (σ : Set (RealSpace n))

def coneDimension {n : ℕ} (σ : Cone n) : ℕ := Module.finrank ℝ (coneSpan σ)

def coneLattice {n : ℕ} (σ : Cone n) : AddSubgroup (Lattice n) where
  carrier := {v | latticeCast n v ∈ coneSpan σ}
  zero_mem' := by simp [coneSpan]
  add_mem' ha hb := by simpa using (coneSpan σ).add_mem ha hb
  neg_mem' ha := by simpa using (coneSpan σ).neg_mem ha

def dualSemigroup {n : ℕ} (σ : Cone n) : AddSubmonoid (Lattice n) where
  carrier := {u | ∀ x ∈ σ, 0 ≤ character n u x}
  zero_mem' := by intro x hx; simp [character]
  add_mem' hu hv := by
    intro x hx
    simpa [character, add_mul, Finset.sum_add_distrib] using add_nonneg (hu x hx) (hv x hx)

def dualInclusion {n : ℕ} {σ τ : Cone n} (h : τ.IsFaceOf σ) :
    dualSemigroup σ →+ dualSemigroup τ where
  toFun u := ⟨u.val, fun x hx ↦ u.property x (h.le hx)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

abbrev CoordinateRing (k : Type) [CommRing k] {n : ℕ} (σ : Cone n) :=
  AddMonoidAlgebra k (dualSemigroup σ)

def faceRingMap (k : Type) [CommRing k] {n : ℕ} {σ τ : Cone n} (h : τ.IsFaceOf σ) :
    CoordinateRing k σ →ₐ[k] CoordinateRing k τ :=
  AddMonoidAlgebra.mapDomainAlgHom k k (dualInclusion h)

@[simp]
theorem faceRingMap_monomial (k : Type) [CommRing k] {n : ℕ} {σ τ : Cone n}
    (h : τ.IsFaceOf σ) (u : dualSemigroup σ) (a : k) :
    faceRingMap k h (AddMonoidAlgebra.single u a) =
      AddMonoidAlgebra.single (dualInclusion h u) a := by
  simp [faceRingMap]

abbrev SchemeOver (k : Type) [CommRing k] := Over (Spec (.of k))

def affineChart (k : Type) [CommRing k] {n : ℕ} (σ : Cone n) : SchemeOver k :=
  Over.mk (Spec.algebraMap k (CoordinateRing k σ))

def faceMap (k : Type) [CommRing k] {n : ℕ} {σ τ : Cone n} (h : τ.IsFaceOf σ) :
    affineChart k τ ⟶ affineChart k σ :=
  Over.homMk (Spec.map (CommRingCat.ofHom (faceRingMap k h).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hc : (faceRingMap k h).toRingHom.comp (algebraMap k (CoordinateRing k σ)) =
        algebraMap k (CoordinateRing k τ) :=
      RingHom.ext fun a ↦ (faceRingMap k h).commutes a
    rw [hc])

/-- A realization of the toric variety of a finite fan $F$ in $\mathbb{R}^n$ over a commutative ring
$k$: a $k$-scheme $X$ with, for every cone $\sigma$ of $F$, a $k$-morphism to $X$ from the affine
chart $U_\sigma = \operatorname{Spec} k[\sigma^\vee \cap \mathbb{Z}^n]$ (`affineChart`), such that
these charts are open immersions, compose with the face map $U_\tau \to U_\sigma$ to the chart of
$\tau$ whenever $\tau$ is a face of $\sigma$, cover $X$, and, for any two cones $\sigma$ and $\tau$,
make the square of $k$-schemes formed by the face maps $U_{\sigma \cap \tau} \to U_\sigma$,
$U_{\sigma \cap \tau} \to U_\tau$ and the charts of $\sigma$ and $\tau$ a pullback. -/
structure Realization (k : Type) [CommRing k] {n : ℕ} (F : FiniteFan n) where
  scheme : SchemeOver k
  chartMap : ∀ σ : F.Face, affineChart k σ.val ⟶ scheme
  face_naturality : ∀ (σ τ : F.Face) (h : τ.val.IsFaceOf σ.val),
    faceMap k h ≫ chartMap σ = chartMap τ
  [openCharts : ∀ σ : F.Face, IsOpenImmersion (chartMap σ).left]
  cover : ∀ x : scheme.left, ∃ σ : F.Face,
    x ∈ Set.range (chartMap σ).left
  overlaps : ∀ σ τ : F.Face,
    IsPullback
      (faceMap k (F.intersection_face σ.val σ.property τ.val τ.property))
      (faceMap k (by simpa [inf_comm] using
        F.intersection_face τ.val τ.property σ.val σ.property))
      (chartMap σ) (chartMap τ)

attribute [instance] Realization.openCharts

end MathlibExt.AlgebraicGeometry.FiniteToricCoordinates
