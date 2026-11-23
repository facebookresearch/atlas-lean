/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Languages.ContextFree.Parikh

/-!
# Parikh's theorem: the Parikh image of every context-free language is semilinear

The statement is registered here as a `theorem_wanted`. The
definitions `Cslib.Language.parikhVector`,
`Cslib.Language.parikhImage`, `Cslib.Language.IsLinear`, and
`Cslib.Language.IsSemilinear`, together with their basic closure
lemmas (images of unions, singletons, and the empty language; linear
implies semilinear; semilinear sets are closed under union), are
proved in `CSLibExt`. The full proof of Parikh's theorem needs the
derivation-tree / pumping analysis of context-free grammars (every
sufficiently large derivation tree contains a pumpable subtree, and
the Parikh vectors are controlled by finitely many minimal trees),
which is a large argument, so it is left as a `theorem_wanted`.
-/

@[expose] public section

namespace Cslib.ParikhWanted

open Cslib.Language

/-- The Parikh image of every context-free language is semilinear.
Source: Parikh, "On context-free languages", Journal of the ACM 13
(1966), 570-581. -/
public theorem_wanted parikh_image_isSemilinear {T : Type*} [DecidableEq T]
    {L : Language T} (hL : L.IsContextFree) : IsSemilinear (parikhImage L)

end Cslib.ParikhWanted
