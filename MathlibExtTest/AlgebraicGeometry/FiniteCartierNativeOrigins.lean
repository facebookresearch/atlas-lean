/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.AffineGroupScheme.CartierDuality.FiniteLocallyFree

/-!
The finite Cartier dual is the actual finite dual of the original
coordinate Hopf algebra. Both directions and the double-dual evaluation
are the completed source port, over every commutative base ring.
No Dieudonne, Hodge--Tate or formal-Lie construction is inferred here.
-/

open CategoryTheory Opposite
open MathlibExt MathlibExt.FiniteLocallyFreeCommAffineGroupSchemeCat

noncomputable section

variable (R : Type) [CommRing R]
  (G : FiniteLocallyFreeCommAffineGroupSchemeCat (.of R))

example : cartierDual R G =
    (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
      R).functor.obj
        (op (FiniteLocallyFreeBicommutativeHopfAlgCat.dual (coordinateHopfAlgebra R G))) :=
  cartierDual_eq R G

example : G ≅ cartierDual R (cartierDual R G) := cartierDualDualIso R G

example : (cartierDuality R).inverse = (cartierDualFunctor R).rightOp :=
  cartierDuality_inverse R

#print axioms MathlibExt.ConvolutionDual.instHopfAlgebra
#print axioms MathlibExt.ConvolutionDual.evalBialgEquiv
#print axioms MathlibExt.ConvolutionDual.evalBialgEquiv_naturality
#print axioms MathlibExt.FiniteLocallyFreeBicommutativeHopfAlgCat.cartierDuality
#print axioms MathlibExt.FiniteLocallyFreeCommAffineGroupSchemeCat.cartierDuality
#print axioms MathlibExt.FiniteLocallyFreeCommAffineGroupSchemeCat.cartierDualDualIso
#print axioms
  MathlibExt.FiniteLocallyFreeCommAffineGroupSchemeCat.coordinateHopfAlgebraCartierDualIso
