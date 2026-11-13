/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.ComplexAnalytification
public import Mathlib.Algebra.Polynomial.Eval.Defs

@[expose] public section

/-!
# Concrete complex-point evaluation tests

The point of the affine line attached to polynomial evaluation at `a` must
evaluate its coordinate to `a`. In particular, the points attached to `0` and
`1` must be distinct. These checks exercise the identification of global
sections with the coordinate ring and the direction of the spectrum functor.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped Polynomial
open MathlibExt.AlgebraicGeometry.ComplexAnalytification

namespace MathlibExtTest.AlgebraicGeometry.ComplexAnalytification

private def affineLine : Over (Spec (.of ℂ)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (Polynomial.C : ℂ →+* ℂ[X])))

private def point (a : ℂ) : ComplexPoints affineLine.hom :=
  ⟨Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)), by
    change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)) ≫
      Spec.map (CommRingCat.ofHom Polynomial.C) = 𝟙 _
    rw [← Spec.map_comp]
    have h : CommRingCat.ofHom Polynomial.C ≫
        CommRingCat.ofHom (Polynomial.evalRingHom a) =
          𝟙 (CommRingCat.of ℂ) := by
      ext r
      simp
    rw [h, Spec.map_id]⟩

private def coordinate : Γ(affineLine.left, ⊤) :=
  (Scheme.ΓSpecIso (.of ℂ[X])).inv Polynomial.X

private def coordinateValue (p : ComplexPoints affineLine.hom) : ℂ :=
  ComplexPoints.eval coordinate p p.hom.preimage_top

private theorem coordinateValue_point (a : ℂ) :
    coordinateValue (point a) = a := by
  change ((Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))).appTop ≫
    (Scheme.ΓSpecIso (.of ℂ)).hom)
      ((Scheme.ΓSpecIso (.of ℂ[X])).inv Polynomial.X) = a
  rw [Scheme.ΓSpecIso_naturality]
  simp

example (a : ℂ) : coordinateValue (point a) = a :=
  coordinateValue_point a

example : point 0 ≠ point 1 := by
  intro h
  have hvalues := congrArg coordinateValue h
  simp only [coordinateValue_point, zero_ne_one] at hvalues

end MathlibExtTest.AlgebraicGeometry.ComplexAnalytification
