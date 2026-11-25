/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Algebra.Homology.DGCyclicBarModels

/-!
# Wanted assembly of the source-normalized DG cyclic bar

The input is an actual cochain monoid. The output is normalized on all
tensor-power terms, actual multiplication faces and actual unit
degeneracies. No degeneration or cyclic-homology comparison is an input.

Sources: Loday, Cyclic homology, §1.1; Kaledin,
arXiv:math/0611623v4, §1.3. Generic cochain tensor and braiding proofs are
already completed in MathlibExt.CategoryTheory.DGSource.
-/

namespace WantedExt.AlgebraicGeometry.DGCyclicBarModelsWanted

open MathlibExt.Algebra.Homology.DGCyclicBarModels

universe u

/-- Construct the actual simplicial bar from the fixed native generators. -/
def_wanted dg_cyclic_bar_model (k : Type u) [CommRing k] (A : DGAlgebra k) :
  CyclicBarModel A

end WantedExt.AlgebraicGeometry.DGCyclicBarModelsWanted
