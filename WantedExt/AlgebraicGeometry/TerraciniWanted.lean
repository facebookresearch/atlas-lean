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
* Zak, *Tangents and Secants of Algebraic Varieties*, Chapter II, §1,
  Proposition 1.10(b) (the projective relative-secant case).
* Landsberg, *Tensors: Geometry and Applications*, §5.3 (Terracini's lemma).
* Covered secant-cone source: AxiomMath/Stacks at
  c496df0d9beea9deaeabcea8492605f9a0a2313b,
  `StacksFrontier/AlgebraicGeometry/Variety/Projective/SecantCone.lean`.
  Its secant-direction dimension bounds are not requested again here.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.TerraciniWanted

open MvPolynomial MathlibExt.AlgebraicGeometry.AffineTangent

/-- **Terracini's lemma.** Let $k$ be an algebraically closed field of characteristic zero and
$X, Y ⊆ k^n$ nonempty Zariski-closed sets whose vanishing ideals are prime. Then there is a
polynomial $F$ in $2n$ variables, nonzero at some point of $X × Y$, such that for all $p ∈ X$ and
$q ∈ Y$ with $F(p, q) ≠ 0$, the Zariski tangent space at $p + q$ of the Zariski closure of $X + Y$
is the sum of the Zariski tangent spaces of $X$ at $p$ and of $Y$ at $q$. -/
theorem_wanted terracini {k : Type*} [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ}
    (X Y : Set (Fin n → k))
    (hX : X = zariskiClosure X) (hY : Y = zariskiClosure Y)
    (hneX : X.Nonempty) (hneY : Y.Nonempty)
    (hprimeX : (vanishingIdeal k X).IsPrime)
    (hprimeY : (vanishingIdeal k Y).IsPrime) :
    ∃ F : MvPolynomial (Fin n ⊕ Fin n) k,
      (∃ p ∈ X, ∃ q ∈ Y, eval (Sum.elim p q) F ≠ 0) ∧
      ∀ p ∈ X, ∀ q ∈ Y, eval (Sum.elim p q) F ≠ 0 →
        tangentSet (additionImageClosure X Y) (p + q) =
          tangentSet X p ⊔ tangentSet Y q

end WantedExt.AlgebraicGeometry.TerraciniWanted
