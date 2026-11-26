/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PlacewiseMetrizedLineModels
public import MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
public import MathlibExt.AlgebraicGeometry.GenericSectionMaps
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Boundary-controlled Cauchy metrics on actual algebraic lines

The gauge is the negative logarithm of the norm of an actual boundary
section. Its zero locus is the complement of the actual open immersion
in a proper compactification, tested by the native stalk map. Metric
differences are tested on every nonzero vector of the same completed
analytic fibre, at every place. The completion is the quotient by the
literal boundary-null difference relation.

This defines metric completion, separately from the arithmetic-model
approximation, nefness and Deligne-pairing producers.
Reference: Yuan--Zhang, arXiv:2105.13587v9, Sections 2.1--2.2.

This is a fixed-gauge completion: the gauge of the boundary is only required
to be nonnegative, and the boundary section is only tested on its
invertibility locus. It is not Yuan--Zhang's boundary completion
(arXiv:2105.13587v9, Section 2.4), which uses a projective model and an
effective Cartier boundary divisor with the given support (strictly effective
in the arithmetic case); results that need that boundary topology are not
stated in terms of this completion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BoundaryMetricCompletionModels

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open PlacewiseMetrizedLineModels CoherentCurveLinearSeries
open LineBundleTaskContracts GenericSectionMaps

variable {K : Type} [Field K] (A : AdelicField K) (X : Over (Spec (.of K)))

/-- An actual compactification and its actual boundary section. -/
structure Boundary where
  compactification : Over (Spec (.of K))
  [proper : IsProper compactification.hom]
  openMap : X ⟶ compactification
  [openImmersion : IsOpenImmersion openMap.left]
  dense : DenseRange openMap.left
  line : compactification.left.Modules
  isLine : IsLineBundle line
  sectionMap : structureModule compactification.left ⟶ line
  complement : ∀ y : compactification.left,
    y ∈ Set.range openMap.left ↔ IsIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map sectionMap.mapPresheaf)
  metric : MetrizedLine A X ((Scheme.Modules.pullback openMap.left).obj line)

def boundaryLine (B : Boundary A X) := (Scheme.Modules.pullback B.openMap.left).obj B.line

def boundarySection (B : Boundary A X) : Γ(boundaryLine A X B, ⊤) :=
  homSection X (pullbackSection B.openMap.left B.sectionMap)

def placeBoundarySection (B : Boundary A X) (v : A.places) :
    Γ(placeLine A X (boundaryLine A X B) v, ⊤) :=
  localPullbackSection (placeProjection A X v) (boundaryLine A X B) ⊤ ⊤ (by simp)
    (boundarySection A X B)

/-- The gauge is fixed by the actual boundary-section evaluation. -/
def gauge (B : Boundary A X) (v : A.places)
    (p : ValuedLineFibres.Point (A.completion v) (placeScheme A X v)) : ℝ :=
  -Real.log (norm B.metric v p
    (ValuedLineFibres.evaluateSection (A.completion v) (placeScheme A X v)
      (placeLine A X (boundaryLine A X B) v) (placeBoundarySection A X B v) p (by simp)))

structure EffectiveBoundary extends Boundary A X where
  nonnegative : ∀ v p, 0 ≤ gauge A X toBoundary v p

variable {A X} {L : X.left.Modules}

abbrev MetricSequence := ℕ → MetrizedLine A X L

def IsCauchy (B : EffectiveBoundary A X) (f : MetricSequence (A := A) (X := X) (L := L)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
    ∀ (v : A.places) (p : ValuedLineFibres.Point (A.completion v) (placeScheme A X v))
      (z : Fibre (f 0) v p), z ≠ 0 →
      |Real.log (norm (f m) v p z) - Real.log (norm (f n) v p z)| ≤
        ε * gauge A X B.toBoundary v p

abbrev CauchySequence (B : EffectiveBoundary A X) :=
  {f : MetricSequence (A := A) (X := X) (L := L) // IsCauchy B f}

def Equivalent (B : EffectiveBoundary A X)
    (f g : CauchySequence (L := L) B) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ (v : A.places) (p : ValuedLineFibres.Point (A.completion v) (placeScheme A X v))
      (z : Fibre (f.val 0) v p), z ≠ 0 →
      |Real.log (norm (f.val n) v p z) - Real.log (norm (g.val n) v p z)| ≤
        ε * gauge A X B.toBoundary v p

def sequenceSetoid (B : EffectiveBoundary A X) : Setoid (CauchySequence (L := L) B) where
  r := Equivalent B
  iseqv := by
    constructor
    · intro f ε hε
      refine ⟨0, ?_⟩
      intro n hn v p z hz
      simpa only [sub_self, abs_zero] using mul_nonneg (le_of_lt hε) (B.nonnegative v p)
    · intro f g h ε hε
      obtain ⟨N, hN⟩ := h ε hε
      refine ⟨N, ?_⟩
      intro n hn v p z hz
      simpa only [abs_sub_comm] using hN n hn v p z hz
    · intro f g h hfg hgh ε hε
      obtain ⟨N, hN⟩ := hfg (ε / 2) (by positivity)
      obtain ⟨M, hM⟩ := hgh (ε / 2) (by positivity)
      refine ⟨max N M, ?_⟩
      intro n hn v p z hz
      have hf := hN n ((le_max_left N M).trans hn) v p z hz
      have hg := hM n ((le_max_right N M).trans hn) v p z hz
      calc
        _ ≤ |Real.log (norm (f.val n) v p z) - Real.log (norm (g.val n) v p z)| +
            |Real.log (norm (g.val n) v p z) - Real.log (norm (h.val n) v p z)| :=
          abs_sub_le _ _ _
        _ ≤ (ε / 2) * gauge A X B.toBoundary v p +
            (ε / 2) * gauge A X B.toBoundary v p := add_le_add hf hg
        _ = ε * gauge A X B.toBoundary v p := by ring

abbrev BoundaryMetricCompletion (B : EffectiveBoundary A X) :=
  Quotient (sequenceSetoid (L := L) B)

end MathlibExt.AlgebraicGeometry.BoundaryMetricCompletionModels
