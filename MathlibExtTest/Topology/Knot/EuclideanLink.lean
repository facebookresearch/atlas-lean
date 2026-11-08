/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Knot.EuclideanLink

@[expose] public section

namespace EuclideanLinkTest

open MathlibExt.Topology.Knot.Euclidean
open MathlibExt.Geometry.Euclidean.Ropelength

/-- The identity ambient isotopy starts and remains at the identity. -/
example : AmbientIsotopy.id.H 0 = id := AmbientIsotopy.id.start

/-- Ambient-isotopy composition applies the two families in order. -/
example (Φ Ψ : AmbientIsotopy) (t : ℝ) (x : R3) :
    (Φ.comp Ψ).H t x = Ψ.H t (Φ.H t x) :=
  rfl

/-- Circle-reparametrization composition applies lifts in order. -/
example (σ τ : CircleReparam) (t : ℝ) :
    (σ.comp τ).f t = τ.f (σ.f t) :=
  rfl

/-- Knot ambient isotopy is reflexive, symmetric, and transitive. -/
example {K₁ K₂ K₃ : ParametrizedKnot} (h₁₂ : K₁.Isotopic K₂)
    (h₂₃ : K₂.Isotopic K₃) :
    K₁.Isotopic K₁ ∧ K₂.Isotopic K₁ ∧ K₁.Isotopic K₃ :=
  ⟨ParametrizedKnot.Isotopic.refl K₁, h₁₂.symm, h₁₂.trans h₂₃⟩

/-- Link ambient isotopy is reflexive, symmetric, and transitive. -/
example {n : ℕ} {L₁ L₂ L₃ : ParametrizedLink n}
    (h₁₂ : L₁.Isotopic L₂) (h₂₃ : L₂.Isotopic L₃) :
    L₁.Isotopic L₁ ∧ L₂.Isotopic L₁ ∧ L₁.Isotopic L₃ :=
  ⟨ParametrizedLink.Isotopic.refl L₁, h₁₂.symm, h₁₂.trans h₂₃⟩

/-- Every representative bounds its type ropelength. -/
example {n : ℕ} (L : ParametrizedLink n) :
    L.ropelength ≤ L.ropelengthRatio :=
  L.ropelength_le_ratio_self

/-- Isotopic representatives also bound the target type ropelength. -/
example {n : ℕ} {L L' : ParametrizedLink n} (h : L'.Isotopic L) :
    L.ropelength ≤ L'.ropelengthRatio :=
  ParametrizedLink.ropelength_le_ratio_of_isotopic h

/-- Type ropelength is invariant under ambient isotopy. -/
example {n : ℕ} {L₁ L₂ : ParametrizedLink n} (h : L₁.Isotopic L₂) :
    L₁.ropelength = L₂.ropelength :=
  ParametrizedLink.ropelength_eq_of_isotopic h

/-- A knot's one-component trace is its curve range. -/
example (K : ParametrizedKnot) :
    K.toLink.trace = Set.range K.curve :=
  ParametrizedKnot.trace_toLink K

/-- A knot's one-component total length is its own contour length. -/
example (K : ParametrizedKnot) :
    K.toLink.totalContourLength =
      contourLength K.curve 0 (2 * Real.pi) :=
  ParametrizedKnot.totalContourLength_toLink K

/-- Knot isotopy maps to one-component link isotopy. -/
example {K₁ K₂ : ParametrizedKnot} (h : K₁.Isotopic K₂) :
    K₁.toLink.Isotopic K₂.toLink :=
  h.toLink

/-- Knot type ropelength is defined through the one-component link. -/
example (K : ParametrizedKnot) :
    K.ropelength = K.toLink.ropelength :=
  rfl

end EuclideanLinkTest
