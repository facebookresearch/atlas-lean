/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring

/-!
# Candido polynomial identity

This module formalizes the Candido polynomial identity.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Candido's identity.** For all elements $x$ and $y$ of a commutative semiring,
$2\left(x^4 + y^4 + (x + y)^4\right) = \left(x^2 + y^2 + (x + y)^2\right)^2$.

Source: Kunle Adegoke, "Fibonacci Identities via Fibonacci Functions."
Stable source URL: `https://cs.uwaterloo.ca/journals/JIS/VOL27/Adegoke/adegoke12.tex`,
exact source lines 826-833.
Verified source file SHA-256:
`ebe2bfa5fe4599897b5f3944fbec475e37d8ef74af7d901116b07e8b81ba229b`.
Verified span SHA-256:
`666219f8439f184b9da7c2158873a33719ddd55ed79872f20855058769c04aa8`.
Concept ID: `jis_grounded_5a29aec1bdb7de9c3392ef6a__candido_identity`. -/
theorem candido_identity {R : Type*} [CommSemiring R] (x y : R) :
    2 * (x ^ 4 + y ^ 4 + (x + y) ^ 4) = (x ^ 2 + y ^ 2 + (x + y) ^ 2) ^ 2 := by
  ring

end MetaMathlibExt
