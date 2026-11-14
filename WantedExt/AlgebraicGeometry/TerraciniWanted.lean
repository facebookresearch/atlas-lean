/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AffineTangent
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Terracini's generic tangent formula

An explicit polynomial defines a nonempty principal open in the product
of the two irreducible affine varieties. On that open, the tangent of the
closure of their addition image is the sum of their tangents. Applying
this affine formula to cones supplies the projective join/secant input.
Characteristic zero supplies generic separability; it is not silently
asserted in arbitrary positive characteristic.

References:
* Zak, *Tangents and Secants of Algebraic Varieties*, Chapter I, §1.
* Landsberg, *Tensors: Geometry and Applications*, §5.3.
* Covered secant-cone source: AxiomMath/Stacks at
  c496df0d9beea9deaeabcea8492605f9a0a2313b,
  `StacksFrontier/AlgebraicGeometry/Variety/Projective/SecantCone.lean`.
  Its secant-direction dimension bounds are not requested again here.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.TerraciniWanted

open MathlibExt.AlgebraicGeometry.AffineTangent

variable {k : Type*} [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ}

/-- Terracini for actual addition and polynomial Zariski tangent modules. -/
theorem_wanted terracini (X Y : Set (Fin n → k))
    (hX : X = algebraicClosure X) (hY : Y = algebraicClosure Y)
    (hneX : X.Nonempty) (hneY : Y.Nonempty)
    (hprimeX : (vanishingIdeal X).IsPrime)
    (hprimeY : (vanishingIdeal Y).IsPrime) :
    ∃ F : MvPolynomial (Fin n ⊕ Fin n) k,
      (∃ p ∈ X, ∃ q ∈ Y, MvPolynomial.eval (Sum.elim p q) F ≠ 0) ∧
      ∀ p ∈ X, ∀ q ∈ Y, MvPolynomial.eval (Sum.elim p q) F ≠ 0 →
        tangentSet (additionImageClosure X Y) (p + q) =
          tangentSet X p ⊔ tangentSet Y q

end WantedExt.AlgebraicGeometry.TerraciniWanted
