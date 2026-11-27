/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SmoothHarmonicBundleGeometry
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Topology.Sheaves.Sheaf

/-!
# Actual smooth sections and horizontal sheaves

Sections take values in the fibres of the native bundle core. Smoothness
uses every genuine bundle chart. The connection differentiates the actual
coordinate section and adds its literal matrix action. Horizontal sections
are its kernel on every frame and tangent vector. Their restriction is
function restriction and their sheaf is native sheafification.

The ordinary differentiation/addition/scalar/restriction facts are exact
source integration inputs for these fixed formulas. They contain no flatness,
local-system, metric, or Riemann--Hilbert conclusion. Sources: Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679, Geometry/Manifold/MFDeriv and
Geometry/Manifold/VectorBundle (Apache 2.0); Simpson alg-geom/9604005v1,
section 2, for the harmonic decomposition and horizontal realization.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HarmonicHorizontalSheaves

open _root_.CategoryTheory Opposite TopologicalSpace Set
open KahlerClassGeometry SmoothHarmonicBundleGeometry
open scoped Manifold ContDiff Matrix Matrix.Norms.Elementwise

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
  [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
  {r : ℕ} (B : SmoothComplexBundle n M r)

abbrev RoughSection (U : Opens M) := (x : U) → B.core.Fiber x.val

def coordinateSection (i : Fin B.count) (U : Opens M) (s : RoughSection B U)
    (x : M) : FiberCoordinates r := by
  classical
  exact if hx : x ∈ U then ((B.core.localTriv i) ⟨x, s ⟨x, hx⟩⟩).2 else 0

def IsSmoothSection (U : Opens M) (s : RoughSection B U) : Prop :=
  ∀ i, ContMDiffOn 𝓘(ℝ, Coordinates n) 𝓘(ℝ, FiberCoordinates r) ∞
    (coordinateSection B i U s) ((U : Set M) ∩ B.core.baseSet i)

def restrictSection {U V : Opens M} (h : V ≤ U) (s : RoughSection B U) : RoughSection B V :=
  fun x ↦ s ⟨x.val, h x.property⟩

def connectionValue (A : OneFormValue B) (i : Fin B.count) (U : Opens M)
    (s : RoughSection B U) (x : U) (u : Coordinates n) : FiberCoordinates r :=
  (show FiberCoordinates r from
    mfderivWithin 𝓘(ℝ, Coordinates n) 𝓘(ℝ, FiberCoordinates r)
      (coordinateSection B i U s) ((U : Set M) ∩ B.core.baseSet i) x.val u) +
    (A i x.val u) *ᵥ coordinateSection B i U s x.val

/-- For a smooth complex vector bundle $B$ on a complex manifold $M$ of dimension $n$, given by
trivializations, and, for each trivialization $i$, a matrix $A_i(x, u)$ depending on a point $x$ and
a tangent vector $u$ (`OneFormValue`, not required to be linear in $u$): the condition that, over
every open set, the zero section is smooth and smooth sections are closed under sums, complex
multiples and restriction to smaller open sets, and that, in every trivialization $i$, the
connection formula `connectionValue` (the derivative of the section's coordinates in trivialization
$i$ in the direction $u$, plus $A_i(x, u)$ applied to those coordinates) vanishes on the zero
section and, on smooth sections, is additive, $\mathbb{C}$-homogeneous and compatible with
restriction. -/
class SectionCalculus (A : OneFormValue B) : Prop where
  smooth_zero : ∀ U : Opens M, IsSmoothSection B U 0
  smooth_add : ∀ (U : Opens M) s t, IsSmoothSection B U s → IsSmoothSection B U t →
    IsSmoothSection B U (s + t)
  smooth_smul : ∀ (U : Opens M) (c : ℂ) s, IsSmoothSection B U s →
    IsSmoothSection B U (c • s)
  smooth_restrict : ∀ (U V : Opens M) (h : V ≤ U) s, IsSmoothSection B U s →
    IsSmoothSection B V (restrictSection B h s)
  zero : ∀ i (U : Opens M) (x : U), x.val ∈ B.core.baseSet i → ∀ u,
    connectionValue B A i U 0 x u = 0
  add : ∀ i (U : Opens M) s t, IsSmoothSection B U s → IsSmoothSection B U t →
    ∀ x : U, x.val ∈ B.core.baseSet i → ∀ u,
      connectionValue B A i U (s + t) x u =
        connectionValue B A i U s x u + connectionValue B A i U t x u
  smul : ∀ i (U : Opens M) (c : ℂ) s, IsSmoothSection B U s →
    ∀ x : U, x.val ∈ B.core.baseSet i → ∀ u,
    connectionValue B A i U (c • s) x u = c • connectionValue B A i U s x u
  restriction : ∀ i (U V : Opens M) (h : V ≤ U) s, IsSmoothSection B U s →
    ∀ x : V, x.val ∈ B.core.baseSet i → ∀ u,
      connectionValue B A i V (restrictSection B h s) x u =
        connectionValue B A i U s ⟨x.val, h x.property⟩ u

variable (A : OneFormValue B) [SectionCalculus B A]

def horizontalModule (U : Opens M) : Submodule ℂ (RoughSection B U) where
  carrier := {s | IsSmoothSection B U s ∧
    ∀ i (x : U), x.val ∈ B.core.baseSet i → ∀ u, connectionValue B A i U s x u = 0}
  zero_mem' := ⟨SectionCalculus.smooth_zero (B := B) (A := A) U,
    fun i x hx u ↦ SectionCalculus.zero (B := B) (A := A) i U x hx u⟩
  add_mem' hs ht := by
    refine ⟨SectionCalculus.smooth_add (B := B) (A := A) U _ _ hs.1 ht.1, ?_⟩
    intro i x hx u
    rw [SectionCalculus.add (B := B) (A := A) i U _ _ hs.1 ht.1 x hx u,
      hs.2 i x hx u, ht.2 i x hx u, add_zero]
  smul_mem' c s hs := by
    refine ⟨SectionCalculus.smooth_smul (B := B) (A := A) U c s hs.1, ?_⟩
    intro i x hx u
    rw [SectionCalculus.smul (B := B) (A := A) i U c s hs.1 x hx u, hs.2 i x hx u, smul_zero]

def horizontalRestriction {U V : Opens M} (h : V ≤ U) :
    horizontalModule B A U →ₗ[ℂ] horizontalModule B A V where
  toFun s := ⟨restrictSection B h s.val, by
    refine ⟨SectionCalculus.smooth_restrict (B := B) (A := A) U V h s.val s.property.1, ?_⟩
    intro i x hx u
    rw [SectionCalculus.restriction (B := B) (A := A) i U V h s.val s.property.1 x hx u]
    exact s.property.2 i ⟨x.val, h x.property⟩ hx u⟩
  map_add' _ _ := by apply Subtype.ext; rfl
  map_smul' _ _ := by apply Subtype.ext; rfl

def horizontalPresheaf : (Opens M)ᵒᵖ ⥤ ModuleCat.{0} ℂ where
  obj U := ModuleCat.of ℂ (horizontalModule B A U.unop)
  map f := ModuleCat.ofHom (horizontalRestriction B A f.unop.le)
  map_id U := by
    apply ModuleCat.hom_ext
    ext s
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext s
    rfl

def horizontalSheaf [HasSheafify (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)] :
    Sheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ) :=
  (presheafToSheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)).obj
    (horizontalPresheaf B A)

end MathlibExt.AlgebraicGeometry.HarmonicHorizontalSheaves
