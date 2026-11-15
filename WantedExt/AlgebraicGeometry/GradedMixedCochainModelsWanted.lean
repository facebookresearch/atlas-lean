/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Algebra.Homology.GradedMixedCochainModels

/-!
# Fixed weighted negative-cyclic cochain constructions

Construct the product complex and its functorial map for the actual
graded mixed input. Terms and differentials are fixed in the public
module. These requests do not assert degeneration, a symplectic form,
Calabi--Yau nondegeneracy or a cohomology comparison.

Source: PTVV, arXiv:1111.3209v4, §1.1 and Definitions 1.7--1.8.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.GradedMixedCochainModelsWanted

open CategoryTheory
open MathlibExt.Algebra.Homology.GradedMixedCochainModels

universe u

def_wanted negative_cyclic_model (k : Type u) [CommRing k]
    (G : GradedMixed k) (p : ℤ) : NegativeCyclicModel G p

def_wanted negative_cyclic_map (k : Type u) [CommRing k]
    (G H : GradedMixed k) (f : MixedMap G H) (p : ℤ)
    (M : NegativeCyclicModel G p) (N : NegativeCyclicModel H p) :
    {g : M.complex ⟶ N.complex // IsNegativeCyclicMap f p M N g}

end WantedExt.AlgebraicGeometry.GradedMixedCochainModelsWanted
