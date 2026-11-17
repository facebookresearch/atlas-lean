/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.MotivicPermutationBundleModels

/-!
# Constructing the fixed finite group and permutation module

The finite constant carrier and original free quotient are fixed before
the requests. The representation determines every component coordinate
of the pulled-back frame on every scheme-valued test.

Source: Voevodsky, arXiv:math/0107109v1, Construction 5.3.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MotivicPermutationBundleWanted

open MathlibExt.AlgebraicGeometry.MotivicFinitePermutationModels
open MathlibExt.AlgebraicGeometry.MotivicPermutationBundleModels

/-- Construct the finite etale group structure on the literal Spec of the finite product. -/
def_wanted finiteConstantGroup (k H : Type) [Field k] [Group H] [Fintype H] :
  ConstantGroupGeometry (k := k) (H := H)

/-- Construct the actual quotient module and its representation-normalized linear descent. -/
def_wanted associatedPermutationModule (k H : Type) [Field k] [Group H] [Fintype H]
    [C : ConstantGroupGeometry (k := k) (H := H)]
    (P : FreeQuotient (k := k) (H := H)) (n : ℕ)
    (r : H →* Equiv.Perm (Fin n)) : AssociatedPermutationModule P r

end WantedExt.AlgebraicGeometry.MotivicPermutationBundleWanted
