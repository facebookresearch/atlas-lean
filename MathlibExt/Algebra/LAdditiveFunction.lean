/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Defs

namespace MetaMathlibExt

@[expose] public section

/-- **L-additive functions on a ring.** A function $f \colon K \to K$ on a ring $K$ is
L-additive when $f(mn) = f(m)\,n + f(n)\,m$ for all $m, n \in K$.

Source: concept ID `jis_term_bfd3fbfcad54dede5f5564d5`,
source ID `jis_source_e693bb8c36ef38f1abdf6e18`, lines 215-225. -/
def IsLAdditive {K : Type*} [Ring K] (f : K → K) : Prop :=
  ∀ m n, f (m * n) = f m * n + f n * m

end

end MetaMathlibExt
