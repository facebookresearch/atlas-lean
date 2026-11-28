/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RepresentationTheory.Homological.GroupCohomology.ZModRestrictDegreeThree
import MathlibExt.RepresentationTheory.Homological.GroupCohomology.LowDegreeThreeHomologyIso
import Mathlib.Algebra.Group.TypeTags.Basic
meta import Mathlib.Tactic.Ring
meta import Mathlib.Tactic.Abel

/-!
# A nonzero third cohomology class and integral coefficient restriction

On the cyclic group of order two, the product of the three coordinate characters is a
normalized three-cocycle with trivial coefficients in `ZMod 2`. It takes value one on three
nonidentity elements and zero when the middle entry is the identity. Every two-coboundary
has opposite values at those two tuples, which proves that this actual cohomology class is
nonzero. The additive integral-coefficient comparison retains the same nonzero class.
-/

open CategoryTheory groupCohomology

noncomputable section
set_option autoImplicit false

namespace DegreeThreeCyclicNonzeroTests

private abbrev R := ZMod 2
private abbrev G := Multiplicative R
private abbrev A : Rep R G := Rep.trivial R G R
private def s : G := Multiplicative.ofAdd (1 : R)

private lemma square_s : s * s = 1 := by decide

private def triple : cocycles₃ A :=
  ⟨fun g => g.1.toAdd * g.2.1.toAdd * g.2.2.toAdd,
    (mem_cocycles₃_def _).2 (fun g h i j => by
      change h.toAdd * i.toAdd * j.toAdd -
        (g.toAdd + h.toAdd) * i.toAdd * j.toAdd +
        g.toAdd * (h.toAdd + i.toAdd) * j.toAdd -
        g.toAdd * h.toAdd * (i.toAdd + j.toAdd) +
        g.toAdd * h.toAdd * i.toAdd = 0
      ring)⟩

private lemma triple_nonidentity : triple (s, s, s) = 1 := rfl
private lemma triple_middle_identity : triple (s, 1, s) = 0 := rfl

/-- The displayed differential, rather than a normalization assumption, relates these values. -/
private lemma boundary_opposite (f : G × G → A) :
    d₂₃ A f (s, s, s) = -d₂₃ A f (s, 1, s) := by
  change f (s, s) - f (s * s, s) + f (s, s * s) - f (s, s) =
    -(f (1, s) - f (s * 1, s) + f (s, 1 * s) - f (s, 1))
  rw [square_s, mul_one, one_mul]
  abel

private theorem class_nonzero : H3π A triple ≠ 0 := by
  intro hz
  obtain ⟨f, hf⟩ := (H3π_eq_zero_iff triple).1 hz
  have h₁ : d₂₃ A f (s, s, s) = 1 :=
    (congrFun hf (s, s, s)).trans triple_nonidentity
  have h₀ : d₂₃ A f (s, 1, s) = 0 :=
    (congrFun hf (s, 1, s)).trans triple_middle_identity
  have h := boundary_opposite f
  rw [h₁, h₀, neg_zero] at h
  exact one_ne_zero h

example : triple (s, s, s) = 1 := triple_nonidentity
example : triple (s, 1, s) = 0 := triple_middle_identity
example : H3π A triple ≠ 0 := class_nonzero

private abbrev integralCoefficients : Rep ℤ G := Rep.zmodRestrictInt 2 A
private def integralClass : H3 integralCoefficients :=
  H3π integralCoefficients (cocycles₃ZModRestrictIntEquiv 2 A triple)

/-- The actual scalar-restriction comparison sends the proved nonzero class to its image. -/
example : H3ZModRestrictIntAddEquiv 2 A (H3π A triple) = integralClass :=
  H3ZModRestrictIntAddEquiv_H3π 2 A triple

example : integralClass ≠ 0 := by
  intro hz
  apply class_nonzero
  apply (H3ZModRestrictIntAddEquiv 2 A).injective
  calc
    H3ZModRestrictIntAddEquiv 2 A (H3π A triple) = integralClass :=
      H3ZModRestrictIntAddEquiv_H3π 2 A triple
    _ = 0 := hz
    _ = H3ZModRestrictIntAddEquiv 2 A 0 := (map_zero _).symm

end DegreeThreeCyclicNonzeroTests
