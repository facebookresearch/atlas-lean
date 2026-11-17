/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ModelIntersectionDegrees
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Length
public import Mathlib.Topology.Irreducible

/-!
# The actual component cycles in local Chern sources

Components are indexed by the entire native set of irreducible components.
Each component is its reduced closed subscheme, with its actual generic
point. Its multiplicity is the composition length of the original scheme's
local ring at that point. Finite-length witnesses prevent a truncated
infinite length from becoming a spurious zero coefficient.

The intersection coefficient is the coherent subset-Euler degree of the
actual restricted line tuple, multiplied by this same local length and
divided by the original positive model denominators. No weights or degrees
are independently assigned. These data apply to nonreduced complex fibres
and nonarchimedean special fibres.

Source: Yuan--Zhang, arXiv:2105.13587v9, Section 4.2.2, printed p109,
Lemma 4.2.2 and Appendix A.6.2, printed pp245--246.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SchemeComponentIntersectionModels

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry ModelIntersectionDegrees

/-- Every original irreducible component occurs exactly once. -/
abbrev Component (X : Scheme.{0}) :=
  {C : Set X | C ∈ irreducibleComponents X}

/-- The actual reduced closed component, with its genuine generic point. -/
structure ReducedComponent (X : Scheme.{0}) (C : Component X) where
  scheme : Scheme.{0}
  inclusion : scheme ⟶ X
  [closed : IsClosedImmersion inclusion]
  [integral : IsIntegral scheme]
  image : Set.range inclusion = C.val
  genericPoint : scheme
  generic : _root_.closure ({genericPoint} : Set scheme) = Set.univ

attribute [instance] ReducedComponent.closed ReducedComponent.integral

/-- The multiplicity is the original local composition length. -/
def componentLength {X : Scheme.{0}} {C : Component X}
    (T : ReducedComponent X C) : ℕ∞ :=
  Module.length (X.presheaf.stalk (T.inclusion T.genericPoint))
    (X.presheaf.stalk (T.inclusion T.genericPoint))

/-- The whole component family retains actual finite multiplicities. -/
structure ComponentSources (X : Scheme.{0}) where
  [finite : Fintype (Component X)]
  frame : ∀ C : Component X, ReducedComponent X C
  lengthFinite : ∀ C, componentLength (frame C) ≠ ⊤

variable {K : Type} [Field K] (X : Over (Spec (.of K)))

/-- The component has the structure map inherited from the original scheme. -/
def ReducedComponent.asOver {C : Component X.left} (T : ReducedComponent X.left C) :
    Over (Spec (.of K)) := Over.mk (T.inclusion ≫ X.hom)

attribute [local instance] HasDerivedCategory.standard

variable [FourierMukai.HasDerivedPullbacks.{0}]
  [FourierMukai.HasDerivedPushforwards.{0}]
  [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
  (d : ℕ) (L : Fin d → X.left.Modules)

/-- Every restricted tuple has its actual coherent direct-image presentations. -/
structure ComponentIntersectionSources where
  components : ComponentSources X.left
  degree : ∀ C : Component X.left,
    DegreeData (ReducedComponent.asOver X (components.frame C)) d
      (fun i ↦ (Scheme.Modules.pullback (components.frame C).inclusion).obj (L i))

variable {X d L} (S : ComponentIntersectionSources X d L)

/-- The nonreduced component degree is computed from length and native Euler data. -/
def componentDegree (C : Component X.left) : ℤ :=
  ((componentLength (S.components.frame C)).toNat : ℤ) * mixedDegree (S.degree C)

/-- Original rational model denominators stay attached to the same tuple. -/
def componentCoefficient (e : Fin d → ℕ+) (C : Component X.left) : ℝ :=
  ((componentLength (S.components.frame C)).toNat : ℝ) *
    rationalMixedDegree (S.degree C) e

/-- Sum over all actual components, including the empty scheme branch. -/
def componentTotalDegree : ℤ := by
  letI := S.components.finite
  exact ∑ C : Component X.left, componentDegree S C

/-- The literal coefficient sum uses those same rational model denominators. -/
def componentTotalCoefficient (e : Fin d → ℕ+) : ℝ := by
  letI := S.components.finite
  exact ∑ C : Component X.left, componentCoefficient S e C

end MathlibExt.AlgebraicGeometry.SchemeComponentIntersectionModels
