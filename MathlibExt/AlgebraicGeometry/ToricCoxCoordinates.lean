/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`TauCeti/Geometry/Toric/Algebraic/Fan/Scheme.lean` and
`TauCeti/Geometry/Toric/Algebraic/DualSemigroup/Basic.lean`
(TauCetiProject/TauCeti, revision 62bbc0596dc3539d488232e4e924a338548ea0a9):
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Tau Ceti contributors
Modifications: the ray-indexed chart dictionary uses the lattice `ℤ^n` with indexed ray faces
and Mathlib's additive monoid algebras with their face maps, and keeps the toric chart
realization as characterized input.
-/

module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.AlgebraicGeometry.Pullbacks
public import MathlibExt.AlgebraicGeometry.ComplexAnalytification

/-!
# Literal Cox coordinates, character kernel and existing toric charts

Faces and integral rays define actual positive cones and actual dual-lattice
semigroups. Smoothness means extension to an integral basis; completeness
and intersections are equalities of the computed real cones.

The Cox open consists of complex coordinate tuples whose zero coordinates
are contained in some cone. The Cox group is the actual kernel of the
ray-matrix character homomorphism on complex unit tori. Its coordinate action
and continuity are proved. The orbit quotient has its actual quotient topology.

Toric chart rings are C[σ∨∩M], with the literal face monomial maps. The input
chart realization records actual open immersions, cover and pullback overlaps,
exactly the completed finite-fan construction cited above. The new comparison
is normalized against every literal ray-pairing monomial and actual complex
scheme point; coefficient scalars are fixed by its map over Spec C.

Reference: D. Cox, *The homogeneous coordinate ring of a toric variety*,
https://arxiv.org/abs/alg-geom/9210008v3, §2, Theorem 2.1(ii--iii),
Lemmas 2.2--2.3, pp.5--9, including the stated analytic version.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ToricCoxCoordinates

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ComplexAnalytification
open scoped BigOperators

abbrev ComplexScheme := Over (Spec (.of ℂ))
abbrev CharacterLattice (n : ℕ) := Fin n → ℤ

structure FanData (n m : ℕ) where
  rays : Fin m → CharacterLattice n
  faces : Finset (Finset (Fin m))
  empty_mem : ∅ ∈ faces
  singleton_mem : ∀ i : Fin m, {i} ∈ faces
  downward : ∀ σ ∈ faces, ∀ τ, τ ⊆ σ → τ ∈ faces

variable {n m : ℕ} (F : FanData n m)

def pairing (u : CharacterLattice n) (i : Fin m) : ℤ := ∑ j, u j * F.rays i j

def coneSet (σ : Finset (Fin m)) : Set (Fin n → ℝ) :=
  {x | ∃ a : Fin m → ℝ, (∀ i, 0 ≤ a i) ∧ (∀ i, i ∉ σ → a i = 0) ∧
    ∀ j, x j = ∑ i, a i * (F.rays i j : ℝ)}

structure SmoothComplete : Prop where
  smooth : ∀ σ ∈ F.faces,
    ∃ b : Module.Basis (Fin n) ℤ (CharacterLattice n),
      ∃ e : σ → Fin n, Function.Injective e ∧ ∀ i : σ, F.rays i = b (e i)
  intersections : ∀ σ ∈ F.faces, ∀ τ ∈ F.faces,
    coneSet F σ ∩ coneSet F τ = coneSet F (σ ∩ τ)
  complete : (⋃ σ ∈ F.faces, coneSet F σ) = Set.univ

abbrev Face := {σ : Finset (Fin m) // σ ∈ F.faces}

def dualSemigroup (σ : Finset (Fin m)) : AddSubmonoid (CharacterLattice n) where
  carrier := {u | ∀ i ∈ σ, 0 ≤ pairing F u i}
  zero_mem' := by intro i hi; simp [pairing]
  add_mem' := by
    intro u v hu hv i hi
    simpa [pairing, add_mul, Finset.sum_add_distrib] using add_nonneg (hu i hi) (hv i hi)

def dualInclusion (σ τ : Finset (Fin m)) (h : τ ⊆ σ) :
    dualSemigroup F σ →+ dualSemigroup F τ where
  toFun u := ⟨u.val, fun i hi => u.property i (h hi)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

abbrev chartRing (σ : Finset (Fin m)) := AddMonoidAlgebra ℂ (dualSemigroup F σ)

def faceAlgebraMap (σ τ : Finset (Fin m)) (h : τ ⊆ σ) :
    chartRing F σ →ₐ[ℂ] chartRing F τ :=
  AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ (dualInclusion F σ τ h)

def chart (σ : Finset (Fin m)) : ComplexScheme :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ (chartRing F σ))))

def faceMap (σ τ : Finset (Fin m)) (h : τ ⊆ σ) : chart F τ ⟶ chart F σ :=
  Over.homMk (Spec.map (CommRingCat.ofHom (faceAlgebraMap F σ τ h).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hc : (faceAlgebraMap F σ τ h).toRingHom.comp (algebraMap ℂ (chartRing F σ)) =
        algebraMap ℂ (chartRing F τ) := by
      apply RingHom.ext
      intro z
      exact (faceAlgebraMap F σ τ h).commutes z
    rw [hc])

/-- Existing toric fan realization, fixed by its actual monomial charts. -/
structure ToricModel where
  X : ComplexScheme
  chartMap : ∀ σ : Face F, chart F σ.val ⟶ X
  [openCharts : ∀ σ : Face F, IsOpenImmersion (chartMap σ).left]
  cover : ∀ x : X.left, ∃ (σ : Face F) (y : (chart F σ.val).left), (chartMap σ).left y = x
  overlaps : ∀ σ τ : Face F,
    IsPullback (faceMap F σ.val (σ.val ∩ τ.val) Finset.inter_subset_left)
      (faceMap F τ.val (σ.val ∩ τ.val) Finset.inter_subset_right)
      (chartMap σ) (chartMap τ)
attribute [instance] ToricModel.openCharts

def coxLocus : Set (Fin m → ℂ) :=
  {z | ∃ σ ∈ F.faces, ∀ i, i ∉ σ → z i ≠ 0}
abbrev CoxOpen := {z : Fin m → ℂ // z ∈ coxLocus F}

def characterHom : (Fin m → ℂˣ) →* (Fin n → ℂˣ) where
  toFun g j := ∏ i, g i ^ (F.rays i j)
  map_one' := by funext j; simp
  map_mul' g h := by funext j; simp [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

abbrev CoxGroup := (characterHom F).ker

instance coxAction : MulAction (CoxGroup F) (CoxOpen F) where
  smul g z := ⟨fun i => (g.val i : ℂ) * z.val i, by
    obtain ⟨σ, hσ, hz⟩ := z.property
    exact ⟨σ, hσ, fun i hi => mul_ne_zero (Units.ne_zero (g.val i)) (hz i hi)⟩⟩
  one_smul z := by
    apply Subtype.ext
    funext i
    change (1 : ℂ) * z.val i = z.val i
    exact one_mul _
  mul_smul g h z := by
    apply Subtype.ext
    funext i
    change ((g.val i * h.val i : ℂˣ) : ℂ) * z.val i =
      (g.val i : ℂ) * ((h.val i : ℂ) * z.val i)
    simp [mul_assoc]

instance continuousCoxAction : ContinuousSMul (CoxGroup F) (CoxOpen F) where
  continuous_smul := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    have hg : Continuous (fun p : CoxGroup F × CoxOpen F => p.1.val i) :=
      (continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)
    have hz : Continuous (fun p : CoxGroup F × CoxOpen F => p.2.val i) :=
      (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)
    exact (Units.continuous_val.comp hg).mul hz

abbrev CoxQuotient := Quotient (MulAction.orbitRel (CoxGroup F) (CoxOpen F))

def coxMonomial (z : CoxOpen F) (u : CharacterLattice n) : ℂ :=
  ∏ i, z.val i ^ (pairing F u i)

def characterValue (σ : Finset (Fin m)) (u : dualSemigroup F σ)
    (p : space (chart F σ)) : ℂ :=
  ComplexPoints.eval
    ((Scheme.ΓSpecIso (.of (chartRing F σ))).inv (AddMonoidAlgebra.single u (1 : ℂ))) p
    (by simp [ComplexPoints.Mem])

/-- The Cox uniformization target is an actual orbit-space homeomorphism,
normalized on every monomial and every eligible affine chart. -/
structure CoxUniformization (M : ToricModel F) where
  homeomorphism : CoxQuotient F ≃ₜ space M.X
  normalization : ∀ (z : CoxOpen F) (σ : Face F)
      (_inChart : ∀ i, i ∉ σ.val → z.val i ≠ 0),
    ∃ p : space (chart F σ.val),
      homeomorphism (Quotient.mk'' z) = spaceMap (M.chartMap σ) p ∧
      ∀ u : dualSemigroup F σ.val, characterValue F σ.val u p = coxMonomial F z u.val

end MathlibExt.AlgebraicGeometry.ToricCoxCoordinates
