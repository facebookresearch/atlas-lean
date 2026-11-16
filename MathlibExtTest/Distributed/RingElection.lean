/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Distributed.RingElection

@[expose] public section

/-- One step takes the max with the predecessor's value. -/
example (ρ : Fin 3 → Fin 3) (s : Fin 3 → ℕ) (i : Fin 3) :
    electStep ρ s i = max (s i) (s (ρ i)) := rfl

end
