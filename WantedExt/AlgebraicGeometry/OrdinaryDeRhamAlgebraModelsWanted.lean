/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.RingTheory.OrdinaryDeRhamAlgebraModels

/-!
# Wanted native ordinary de Rham DG-algebra assembly

The actual complex, differential, wedge product and unit are fixed
publicly. Assemble them as a native DG algebra, then construct the
coefficient-changing cochain map with multiplication/unit laws and
the specified generator images. No cohomology comparison, filtered
splitting or ring compatibility theorem is assumed in a module isomorphism.

Sources: Stacks 0FKF/0FKG and 0FKM; the attributed completed DeRhamSource port.
-/

namespace WantedExt.AlgebraicGeometry.OrdinaryDeRhamAlgebraModelsWanted

open MathlibExt.Algebra.Homology.DGCyclicBarModels
open MathlibExt.RingTheory.OrdinaryDeRhamAlgebraModels

universe u

/-- Assemble the native wedge/unit on the completed de Rham differential. -/
def_wanted ordinary_deRham_dg_algebra (R B : Type u) [CommRing R] [CommRing B]
    [Algebra R B] : Σ D : DGAlgebra R, DeRhamAlgebraModel R B D

/-- Construct the fixed coefficient-changing algebra map on all source generators. -/
def_wanted ordinary_deRham_coefficient_map (R S B C : Type u)
    [CommRing R] [CommRing S] [CommRing B] [CommRing C]
    [Algebra R S] [Algebra R B] [Algebra S C] [Algebra R C] [IsScalarTower R S C]
    (D : DGAlgebra R) (E : DGAlgebra S)
    (M : DeRhamAlgebraModel R B D) (N : DeRhamAlgebraModel S C E) (f : B →ₐ[R] C) :
  CoefficientMap R S B C M N f

end WantedExt.AlgebraicGeometry.OrdinaryDeRhamAlgebraModelsWanted
