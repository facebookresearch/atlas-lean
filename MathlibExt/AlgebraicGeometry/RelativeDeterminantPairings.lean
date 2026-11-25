/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BoundedProjectiveDeterminants
public import MathlibExt.AlgebraicGeometry.AffineDerivedCoefficientModules
public import MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.KrullDimension

/-!
# Actual affine determinant expressions for relative Deligne pairings

For `n + 1` actual line bundles, the alternating expression is
`det Rp_* (product (L_i - O_X))`. Every factor below is an actual
subset tensor of the given sheaves. Every presenting complex is a
bounded finite-projective representative of its native derived
pushforward after the specified affine base pullback. No two-term
amplitude, smoothness, chosen numerical height, or line trivialization
is built into this expression.

The affine expression alone does not provide global determinant
transport, descent, a metric, or adelic completion. Those constructions
must retain the actual scalar and cochain transition maps.

References: Knudsen--Mumford, *The projectivity of the moduli space of
stable curves I*, Sections 1--2; Yuan--Zhang, arXiv:2105.13587v9,
Section 4.2.1 (projective, finite-Tor-dimensional, pure relative dimension
scope) and Theorem 4.1.3 (the adelic extension).
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeDeterminantPairings

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open AlgebraicLineBundleFamilies CoherentCurveLinearSeries
open AffineDerivedCoefficientModules BoundedProjectiveDeterminants

attribute [local instance] HasDerivedCategory.standard

/-- Actual pure dimension of each irreducible component of every scheme fibre. -/
def IsPureRelativeDimension {X Y : Scheme.{0}} (f : X ⟶ Y) (n : ℕ) : Prop :=
  ∀ (y : Y) (Z : Set (f.fiber y)), Z ∈ irreducibleComponents (f.fiber y) →
    topologicalKrullDim Z = n

/-- The actual subset tensor; the empty subset is the structure module. -/
def subsetTensor {X : Scheme.{0}} {m : ℕ} (L : Fin m → X.Modules)
    (s : Finset (Fin m)) : X.Modules :=
  (s.sort (· ≤ ·)).foldr (fun i M ↦ moduleTensor X (L i) M) (structureModule X)

@[simp] theorem subsetTensor_empty {X : Scheme.{0}} {m : ℕ}
    (L : Fin m → X.Modules) : subsetTensor L ∅ = structureModule X := by
  simp [subsetTensor]

/-- The sign uses the cardinality of the actual complementary subset. -/
def IsPositive {m : ℕ} (s : Finset (Fin m)) : Prop := Even ((Finset.univ \ s).card)

variable [FourierMukai.HasDerivedPullbacks.{0}]
  [FourierMukai.HasDerivedPushforwards.{0}]
  [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]

/-- The actual derived direct image of a sheaf in degree zero. -/
def directImage {X Y : Scheme.{0}} (f : X ⟶ Y) (E : X.Modules) : FourierMukai.D Y :=
  (FourierMukai.derivedPushforward f).obj
    ((DerivedCategory.singleFunctor X.Modules 0).obj E)

/-- A genuine bounded affine presentation of this exact derived object. -/
structure AffinePresentation {Y : Scheme.{0}} (K : FourierMukai.D Y)
    (R : CommRingCat.{0}) (a : Spec R ⟶ Y) where
  complex : BoundedProjectiveDeterminants.Complex R
  comparison : (derivedTilde R).obj (DerivedCategory.Q.obj complex.cochain) ≅
    (FourierMukai.derivedPullback a).obj K

/-- Each factor is fixed by the actual tensor sheaf and actual direct image. -/
abbrev Presentations {X Y : Scheme.{0}} (f : X ⟶ Y) {m : ℕ}
    (L : Fin m → X.Modules) (R : CommRingCat.{0}) (a : Spec R ⟶ Y) :=
  ∀ s : Finset (Fin m), AffinePresentation (directImage f (subsetTensor L s)) R a

/-- The determinant factor, inverted exactly when the subset sign is negative. -/
def factor {X Y : Scheme.{0}} {f : X ⟶ Y} {m : ℕ} {L : Fin m → X.Modules}
    {R : CommRingCat.{0}} {a : Spec R ⟶ Y} (P : Presentations f L R a)
    (s : Finset (Fin m)) : ModuleCat.{0} R := by
  classical
  exact if IsPositive s then determinantObject R (P s).complex
    else ModuleCat.of R (Module.Dual R (determinantObject R (P s).complex))

/-- Literal ordered tensor of every subset factor in the determinant expression. -/
def localPairing {X Y : Scheme.{0}} {f : X ⟶ Y} {m : ℕ} {L : Fin m → X.Modules}
    {R : CommRingCat.{0}} {a : Spec R ⟶ Y} (P : Presentations f L R a) : ModuleCat.{0} R :=
  (Finset.univ : Finset (Finset (Fin m))).toList.foldr
    (fun s M ↦ factor P s ⊗ M) (𝟙_ (ModuleCat.{0} R))

end MathlibExt.AlgebraicGeometry.RelativeDeterminantPairings
