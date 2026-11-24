/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.NearbyCycleGeometry
public import Mathlib.Tactic.NormNum

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ComplexAnalytification
open MathlibExt.AlgebraicGeometry.NearbyCycleGeometry

namespace NearbyCycleGeometryTest

variable (X : Over (Spec (.of ℂ))) (s : Γ(X.left, ⊤))

/-- A point of the exponential cover is a point `x` with a logarithm `z` of
`s(x)` normalized by `s(x) = exp(2πiz)`. -/
example (p : exponentialCover X s) :
    regularValue X s (coverProjection X s p) =
      Complex.exp (2 * Real.pi * Complex.I * p.val.2) :=
  p.property

/-- The cover lies over the punctured domain. -/
example (p : exponentialCover X s) : regularValue X s (coverProjection X s p) ≠ 0 :=
  (puncturedProjection X s p).property

/-- The deck translation by `n` moves only the logarithm coordinate, by `n`. -/
theorem deck_val (n : ℤ) (p : exponentialCover X s) :
    (deck X s n p).val = (p.val.1, p.val.2 + n) := rfl

/-- Deck translations form an action of `ℤ`. -/
example (p : exponentialCover X s) : deck X s 0 p = p := by
  apply Subtype.ext
  apply Prod.ext <;> simp [deck_val]

example (m n : ℤ) (p : exponentialCover X s) :
    deck X s (m + n) p = deck X s n (deck X s m p) :=
  deck_add_apply X s m n p

example (n : ℤ) (p : exponentialCover X s) : deck X s (-n) (deck X s n p) = p := by
  apply Subtype.ext
  apply Prod.ext <;> simp [deck_val]

/-- The deck translation by `1` is not the identity: it changes the logarithm. -/
example (p : exponentialCover X s) : deck X s 1 p ≠ p := by
  intro h
  have h2 := congrArg (fun q : exponentialCover X s ↦ q.val.2) h
  simp only [deck_val] at h2
  norm_num at h2

/-- Deck translations are automorphisms over `X`. -/
example (n : ℤ) : (deckIso X s n).hom ≫ coverProjection X s = coverProjection X s :=
  deckProjection X s n

/-- The cover projection factors through the punctured domain. -/
example : puncturedProjection X s ≫ puncturedInclusion X s = coverProjection X s :=
  puncturedProjection_comp X s

end NearbyCycleGeometryTest
