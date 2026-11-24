/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.NormalizedTorsorOperations
public import MathlibExt.AlgebraicGeometry.ExpansionParameterModels

/-!
# Native contracted split-torus operations

The torus is the actual Laurent polynomial scheme with its all-test-unit
dictionary. The target supplies its actual tensor quotients, Cartesian
base changes, actual product unit and quotient-point-normalized coherence.
Source: Stacks Project, Tags 04UR and 0CQJ; DG arXiv:math/0005132v3, Sections 4--6.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.NormalizedTorsorOperationsWanted

open _root_.CategoryTheory _root_.MathlibExt.AlgebraicGeometry
open NormalizedTorsorOperations ExpansionParameterModels

def_wanted nativeSplitTorusTensorCalculus (r : ℕ) (T : TorusTheory ℂ r) :
    letI := T.group
    TensorCalculus (torusScheme ℂ r)

end WantedExt.AlgebraicGeometry.NormalizedTorsorOperationsWanted
