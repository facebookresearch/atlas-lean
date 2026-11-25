/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DirectWittBoundedStages
public import MathlibExt.AlgebraicGeometry.RelativeWittGeneralLinearOrbits

/-!
# Native loop quotient comparison with the direct W(R) lattice functor

The comparison is the original normalized general-linear loop quotient
followed by the actual direct-Witt coordinate dictionary. Every loop
insertion retains the original standard-lattice orbit square. This is a
completed transport of the shared quotient constructor, whose geometric
proof remains explicitly requested in its source packet.

Source: Zhu, arXiv:1407.8519v3, formula (0.1.2) and Section 1.2.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DirectWittQuotientTransport

open _root_.CategoryTheory
open RelativeWittUnramifiedNormalization DirectWittBoundedStages
open RelativeWittGeneralLinearOrbits RelativeWittIndRealizations
open NativeGeneralLinearSchemeCoordinates

variable (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] (n : ℕ)
  (M : UnramifiedModel p k n) (P : PointRealization (WittVector p k) n)
  (O : OrbitCoordinates p k (WittVector p k) (p : WittVector p k) n P M.extension M.matrix)
  (Q : QuotientComparison p k (WittVector p k) (p : WittVector p k)
    n P M.extension M.matrix O)

/-- The actual normalized loop quotient takes values in the direct W(R) lattice sheaf. -/
def comparison : quotientSheaf p k (WittVector p k) (p : WittVector p k) n P ≅
    (sheafification p k).obj M.functor :=
  Q.comparison ≪≫ (sheafification p k).mapIso (functorIso p k n M)

/-- The source loop orbit square is unchanged by the actual coordinate transport. -/
theorem comparison_normalized :
    (sheafification p k).map
        (quotientMap p k (WittVector p k) (p : WittVector p k) n P) ≫
      (comparison p k n M P O Q).hom =
    (sheafification p k).map O.map ≫
      (sheafification p k).map (functorIso p k n M).hom := by
  change (sheafification p k).map
      (quotientMap p k (WittVector p k) (p : WittVector p k) n P) ≫
    Q.comparison.hom ≫ (sheafification p k).map (functorIso p k n M).hom = _
  simpa only [Category.assoc] using
    congrArg (fun f ↦ f ≫ (sheafification p k).map (functorIso p k n M).hom) Q.normalized

end MathlibExt.AlgebraicGeometry.DirectWittQuotientTransport
