/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthRootAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthMonomialSchreier

/-! Actual original word data for the 16 pointwise-octad permutations and 32 vanishing signs. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Original selected Mathieu words for every pointwise-octad permutation. -/
def generatedTwelfthRootKernelPermutationWord : Fin 16 → List (Fin 5 × Bool) :=
  ![
  [],
  [
    (1, false), (0, false), (2, false), (0, false), (1, false), (3, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (3, false),
    (1, false), (3, false), (1, false), (3, false), (1, false), (3, false),
    (1, false), (1, false), (0, false), (1, false), (0, false), (1, false),
    (3, false), (1, false), (3, false), (1, false)
  ],
  [
    (3, false), (1, false), (3, false), (1, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (0, false), (2, false), (0, false),
    (1, false), (0, false), (2, false), (0, false), (3, false), (1, false),
    (3, false), (1, false), (1, false), (0, false), (2, false), (0, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (0, false),
    (2, false), (0, false)
  ],
  [
    (3, false), (0, false), (4, true), (3, false), (0, false), (1, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (1, false),
    (0, false), (1, false), (0, false), (1, false), (0, false), (2, false),
    (0, false), (1, false), (0, false), (2, false), (0, false), (1, false),
    (0, false), (2, false), (0, false), (1, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (3, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (3, false), (1, false), (3, false),
    (1, false), (1, false), (0, false), (1, false), (0, false), (1, false),
    (3, false), (1, false), (3, false), (1, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (0, false), (2, false), (0, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (3, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (1, false), (0, false), (2, false),
    (0, false), (1, false), (0, false), (2, false), (0, false), (1, false),
    (0, false), (2, false), (0, false), (1, false), (0, false), (1, false),
    (0, false), (1, false), (1, false), (0, false), (2, false), (0, false),
    (1, false), (1, false), (0, false), (3, false), (4, false), (0, false),
    (3, false), (1, false), (0, false), (2, false), (0, false), (1, false),
    (3, false), (1, false), (0, false), (2, false), (0, false), (1, false),
    (3, false), (1, false), (3, false), (1, false), (3, false), (1, false),
    (3, false), (1, false), (1, false), (0, false), (1, false), (0, false),
    (1, false), (3, false), (1, false), (3, false), (1, false), (3, false),
    (0, false), (4, true), (3, false), (0, false), (1, false), (1, false),
    (0, false), (2, false), (0, false), (1, false), (1, false), (0, false),
    (1, false), (0, false), (1, false), (0, false), (2, false), (0, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (1, false), (0, false), (2, false),
    (0, false), (1, false), (3, false), (1, false), (0, false), (2, false),
    (0, false), (1, false), (3, false), (1, false), (3, false), (1, false),
    (1, false), (0, false), (1, false), (0, false), (1, false), (3, false),
    (1, false), (3, false), (1, false), (1, false), (0, false), (2, false),
    (0, false), (1, false), (0, false), (2, false), (0, false), (1, false),
    (0, false), (2, false), (0, false), (1, false), (0, false), (2, false),
    (0, false), (1, false), (3, false), (1, false), (0, false), (2, false),
    (0, false), (1, false), (1, false), (0, false), (2, false), (0, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (0, false), (1, false), (0, false),
    (1, false), (1, false), (0, false), (2, false), (0, false), (1, false),
    (1, false), (0, false), (3, false), (4, false), (0, false), (3, false),
    (3, false), (0, false), (4, true), (3, false), (0, false), (1, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (1, false),
    (0, false), (1, false), (0, false), (1, false), (0, false), (2, false),
    (0, false), (1, false), (0, false), (2, false), (0, false), (1, false),
    (0, false), (2, false), (0, false), (1, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (3, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (3, false), (1, false), (3, false),
    (1, false), (1, false), (0, false), (1, false), (0, false), (1, false),
    (3, false), (1, false), (3, false), (1, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (0, false), (2, false), (0, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (3, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (1, false), (0, false), (2, false),
    (0, false), (1, false), (0, false), (2, false), (0, false), (1, false),
    (0, false), (2, false), (0, false), (1, false), (0, false), (1, false),
    (0, false), (1, false), (1, false), (0, false), (2, false), (0, false),
    (1, false), (1, false), (0, false), (3, false), (4, false), (0, false),
    (3, false)
  ],
  [
    (1, false), (0, false), (2, false), (0, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (0, false), (2, false), (0, false),
    (3, false), (1, false), (3, false), (1, false), (1, false), (0, false),
    (1, false), (0, false), (1, false), (3, false), (1, false), (3, false),
    (1, false), (3, false), (1, false), (3, false), (1, false), (3, false),
    (1, false), (3, false), (1, false), (1, false), (0, false), (1, false),
    (0, false), (1, false), (3, false), (1, false), (3, false), (1, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (0, false), (2, false), (0, false)
  ],
  [
    (3, false), (1, false), (3, false), (1, false), (1, false), (0, false),
    (1, false), (0, false), (1, false), (3, false), (1, false), (3, false),
    (1, false), (3, false), (1, false), (3, false), (1, false), (3, false),
    (1, false), (3, false), (1, false), (1, false), (0, false), (1, false),
    (0, false), (1, false), (3, false), (1, false), (3, false), (1, false)
  ],
  [
    (3, false), (0, false), (4, true), (3, false), (0, false), (1, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (1, false),
    (0, false), (1, false), (0, false), (1, false), (0, false), (2, false),
    (0, false), (1, false), (0, false), (2, false), (0, false), (1, false),
    (0, false), (2, false), (0, false), (1, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (3, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (3, false), (1, false), (3, false),
    (1, false), (1, false), (0, false), (1, false), (0, false), (1, false),
    (3, false), (1, false), (3, false), (1, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (0, false), (2, false), (0, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (3, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (1, false), (0, false), (2, false),
    (0, false), (1, false), (0, false), (2, false), (0, false), (1, false),
    (0, false), (2, false), (0, false), (1, false), (0, false), (1, false),
    (0, false), (1, false), (1, false), (0, false), (2, false), (0, false),
    (1, false), (1, false), (0, false), (3, false), (4, false), (0, false),
    (3, false), (3, false), (1, false), (3, false), (1, false), (3, false),
    (0, false), (4, true), (3, false), (0, false), (1, false), (1, false),
    (0, false), (2, false), (0, false), (1, false), (1, false), (0, false),
    (1, false), (0, false), (1, false), (0, false), (2, false), (0, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (1, false), (0, false), (2, false),
    (0, false), (1, false), (3, false), (1, false), (0, false), (2, false),
    (0, false), (1, false), (3, false), (1, false), (3, false), (1, false),
    (1, false), (0, false), (1, false), (0, false), (1, false), (3, false),
    (1, false), (3, false), (1, false), (1, false), (0, false), (2, false),
    (0, false), (1, false), (0, false), (2, false), (0, false), (1, false),
    (0, false), (2, false), (0, false), (1, false), (0, false), (2, false),
    (0, false), (1, false), (3, false), (1, false), (0, false), (2, false),
    (0, false), (1, false), (1, false), (0, false), (2, false), (0, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (0, false), (1, false), (0, false),
    (1, false), (1, false), (0, false), (2, false), (0, false), (1, false),
    (1, false), (0, false), (3, false), (4, false), (0, false), (3, false),
    (3, false), (0, false), (4, true), (3, false), (0, false), (1, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (1, false),
    (0, false), (1, false), (0, false), (1, false), (0, false), (2, false),
    (0, false), (1, false), (0, false), (2, false), (0, false), (1, false),
    (0, false), (2, false), (0, false), (1, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (3, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (3, false), (1, false), (3, false),
    (1, false), (1, false), (0, false), (1, false), (0, false), (1, false),
    (3, false), (1, false), (3, false), (1, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (0, false), (2, false), (0, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (3, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (1, false), (0, false), (2, false),
    (0, false), (1, false), (0, false), (2, false), (0, false), (1, false),
    (0, false), (2, false), (0, false), (1, false), (0, false), (1, false),
    (0, false), (1, false), (1, false), (0, false), (2, false), (0, false),
    (1, false), (1, false), (0, false), (3, false), (4, false), (0, false),
    (3, false)
  ],
  [
    (1, false), (0, false), (2, false), (0, false), (1, false), (3, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (3, false),
    (1, false), (3, false), (1, false), (1, false), (0, false), (1, false),
    (0, false), (1, false), (3, false), (1, false), (3, false), (1, false)
  ],
  [
    (1, false), (0, false), (2, false), (0, false), (1, false), (3, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (1, false),
    (0, false), (2, false), (0, false), (1, false), (0, false), (2, false),
    (0, false), (1, false), (0, false), (2, false), (0, false), (1, false),
    (0, false), (1, false), (0, false), (1, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (1, false), (0, false), (3, false),
    (4, false), (0, false), (3, false), (3, false), (1, false), (3, false),
    (1, false), (1, false), (0, false), (1, false), (0, false), (1, false),
    (3, false), (1, false), (3, false), (1, false), (3, false), (1, false),
    (3, false), (1, false), (1, false), (0, false), (2, false), (0, false),
    (1, false), (3, false), (1, false), (0, false), (2, false), (0, false),
    (1, false), (1, false), (0, false), (2, false), (0, false), (1, false),
    (0, false), (2, false), (0, false), (1, false), (0, false), (2, false),
    (0, false), (1, false), (0, false), (1, false), (0, false), (1, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (1, false),
    (0, false), (3, false), (4, false), (0, false), (3, false), (3, false),
    (1, false), (3, false), (1, false), (1, false), (0, false), (1, false),
    (0, false), (1, false), (3, false), (1, false), (3, false), (1, false)
  ],
  [
    (1, false), (0, false), (2, false), (0, false), (1, false), (3, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (1, false),
    (0, false), (1, false), (0, false), (1, false)
  ],
  [
    (3, false), (1, false), (3, false), (1, false)
  ],
  [
    (1, false), (0, false), (2, false), (0, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (0, false), (2, false), (0, false),
    (3, false), (1, false), (3, false), (1, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (0, false), (2, false), (0, false),
    (1, false), (0, false), (2, false), (0, false)
  ],
  [
    (1, false), (0, false), (1, false), (0, false), (1, false), (3, false),
    (1, false), (3, false), (1, false), (1, false), (0, false), (1, false),
    (0, false), (1, false), (3, false), (1, false), (3, false), (1, false)
  ],
  [
    (1, false), (0, false), (2, false), (0, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (0, false), (2, false), (0, false),
    (1, false), (0, false), (1, false), (0, false), (1, false), (3, false),
    (1, false), (3, false), (1, false), (1, false), (0, false), (1, false),
    (0, false), (1, false), (3, false), (1, false), (3, false), (1, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (0, false), (2, false), (0, false)
  ],
  [
    (1, false), (0, false), (2, false), (0, false), (1, false), (3, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (1, false),
    (0, false), (2, false), (0, false), (1, false), (0, false), (2, false),
    (0, false), (1, false), (0, false), (2, false), (0, false), (1, false),
    (0, false), (1, false), (0, false), (1, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (1, false), (0, false), (3, false),
    (4, false), (0, false), (3, false), (1, false), (0, false), (1, false),
    (0, false), (1, false), (1, false), (0, false), (2, false), (0, false),
    (1, false), (3, false), (1, false), (0, false), (2, false), (0, false),
    (1, false), (1, false), (0, false), (2, false), (0, false), (1, false),
    (0, false), (2, false), (0, false), (1, false), (0, false), (2, false),
    (0, false), (1, false), (0, false), (1, false), (0, false), (1, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (1, false),
    (0, false), (3, false), (4, false), (0, false), (3, false), (3, false),
    (1, false), (3, false), (1, false), (1, false), (0, false), (1, false),
    (0, false), (1, false), (3, false), (1, false), (3, false), (1, false)
  ],
  [
    (3, false), (0, false), (4, true), (3, false), (0, false), (1, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (1, false),
    (0, false), (1, false), (0, false), (1, false), (0, false), (2, false),
    (0, false), (1, false), (0, false), (2, false), (0, false), (1, false),
    (0, false), (2, false), (0, false), (1, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (3, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (3, false), (1, false), (3, false),
    (1, false), (1, false), (0, false), (1, false), (0, false), (1, false),
    (3, false), (1, false), (3, false), (1, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (0, false), (2, false), (0, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (3, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (1, false), (0, false), (2, false),
    (0, false), (1, false), (0, false), (2, false), (0, false), (1, false),
    (0, false), (2, false), (0, false), (1, false), (0, false), (1, false),
    (0, false), (1, false), (1, false), (0, false), (2, false), (0, false),
    (1, false), (1, false), (0, false), (3, false), (4, false), (0, false),
    (3, false), (3, false), (1, false), (3, false), (1, false), (1, false),
    (0, false), (1, false), (0, false), (1, false), (3, false), (1, false),
    (3, false), (1, false), (3, false), (1, false), (3, false), (1, false),
    (3, false), (1, false), (3, false), (1, false), (1, false), (0, false),
    (1, false), (0, false), (1, false), (3, false), (1, false), (3, false),
    (1, false), (3, false), (0, false), (4, true), (3, false), (0, false),
    (1, false), (1, false), (0, false), (2, false), (0, false), (1, false),
    (1, false), (0, false), (1, false), (0, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (0, false), (2, false), (0, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (1, false),
    (0, false), (2, false), (0, false), (1, false), (3, false), (1, false),
    (0, false), (2, false), (0, false), (1, false), (3, false), (1, false),
    (3, false), (1, false), (1, false), (0, false), (1, false), (0, false),
    (1, false), (3, false), (1, false), (3, false), (1, false), (1, false),
    (0, false), (2, false), (0, false), (1, false), (0, false), (2, false),
    (0, false), (1, false), (0, false), (2, false), (0, false), (1, false),
    (0, false), (2, false), (0, false), (1, false), (3, false), (1, false),
    (0, false), (2, false), (0, false), (1, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (0, false), (2, false), (0, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (0, false),
    (1, false), (0, false), (1, false), (1, false), (0, false), (2, false),
    (0, false), (1, false), (1, false), (0, false), (3, false), (4, false),
    (0, false), (3, false), (3, false), (0, false), (4, true), (3, false),
    (0, false), (1, false), (1, false), (0, false), (2, false), (0, false),
    (1, false), (1, false), (0, false), (1, false), (0, false), (1, false),
    (0, false), (2, false), (0, false), (1, false), (0, false), (2, false),
    (0, false), (1, false), (0, false), (2, false), (0, false), (1, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (3, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (3, false),
    (1, false), (3, false), (1, false), (1, false), (0, false), (1, false),
    (0, false), (1, false), (3, false), (1, false), (3, false), (1, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (0, false), (2, false), (0, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (3, false),
    (1, false), (0, false), (2, false), (0, false), (1, false), (1, false),
    (0, false), (2, false), (0, false), (1, false), (0, false), (2, false),
    (0, false), (1, false), (0, false), (2, false), (0, false), (1, false),
    (0, false), (1, false), (0, false), (1, false), (1, false), (0, false),
    (2, false), (0, false), (1, false), (1, false), (0, false), (3, false),
    (4, false), (0, false), (3, false)
  ]
]

/-- Literal complete original forward coordinates of all sixteen distinct words. -/
def generatedTwelfthRootKernelPermutationForward : Fin 16 → Fin 24 → Fin 24 :=
  ![
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
  ![0, 1, 2, 3, 5, 4, 7, 6, 10, 11, 8, 9, 15, 14, 13, 12, 16, 17, 18, 19, 21, 20, 23, 22],
  ![0, 1, 2, 3, 6, 7, 4, 5, 11, 10, 9, 8, 13, 12, 15, 14, 16, 17, 18, 19, 22, 23, 20, 21],
  ![0, 1, 2, 3, 7, 6, 5, 4, 9, 8, 11, 10, 14, 15, 12, 13, 16, 17, 18, 19, 23, 22, 21, 20],
  ![0, 1, 2, 3, 8, 10, 11, 9, 4, 7, 5, 6, 20, 22, 23, 21, 16, 17, 18, 19, 12, 15, 13, 14],
  ![0, 1, 2, 3, 9, 11, 10, 8, 7, 4, 6, 5, 23, 21, 20, 22, 16, 17, 18, 19, 14, 13, 15, 12],
  ![0, 1, 2, 3, 10, 8, 9, 11, 5, 6, 4, 7, 21, 23, 22, 20, 16, 17, 18, 19, 15, 12, 14, 13],
  ![0, 1, 2, 3, 11, 9, 8, 10, 6, 5, 7, 4, 22, 20, 21, 23, 16, 17, 18, 19, 13, 14, 12, 15],
  ![0, 1, 2, 3, 12, 15, 13, 14, 20, 23, 21, 22, 4, 6, 7, 5, 16, 17, 18, 19, 8, 10, 11, 9],
  ![0, 1, 2, 3, 13, 14, 12, 15, 22, 21, 23, 20, 6, 4, 5, 7, 16, 17, 18, 19, 11, 9, 8, 10],
  ![0, 1, 2, 3, 14, 13, 15, 12, 23, 20, 22, 21, 7, 5, 4, 6, 16, 17, 18, 19, 9, 11, 10, 8],
  ![0, 1, 2, 3, 15, 12, 14, 13, 21, 22, 20, 23, 5, 7, 6, 4, 16, 17, 18, 19, 10, 8, 9, 11],
  ![0, 1, 2, 3, 20, 21, 22, 23, 12, 14, 15, 13, 8, 11, 9, 10, 16, 17, 18, 19, 4, 5, 6, 7],
  ![0, 1, 2, 3, 21, 20, 23, 22, 15, 13, 12, 14, 10, 9, 11, 8, 16, 17, 18, 19, 5, 4, 7, 6],
  ![0, 1, 2, 3, 22, 23, 20, 21, 13, 15, 14, 12, 11, 8, 10, 9, 16, 17, 18, 19, 6, 7, 4, 5],
  ![0, 1, 2, 3, 23, 22, 21, 20, 14, 12, 13, 15, 9, 10, 8, 11, 16, 17, 18, 19, 7, 6, 5, 4]
]

/-- Literal complete original backward coordinates, retaining the genuine word orientation. -/
def generatedTwelfthRootKernelPermutationBackward : Fin 16 → Fin 24 → Fin 24 :=
  ![
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
  ![0, 1, 2, 3, 5, 4, 7, 6, 10, 11, 8, 9, 15, 14, 13, 12, 16, 17, 18, 19, 21, 20, 23, 22],
  ![0, 1, 2, 3, 6, 7, 4, 5, 11, 10, 9, 8, 13, 12, 15, 14, 16, 17, 18, 19, 22, 23, 20, 21],
  ![0, 1, 2, 3, 7, 6, 5, 4, 9, 8, 11, 10, 14, 15, 12, 13, 16, 17, 18, 19, 23, 22, 21, 20],
  ![0, 1, 2, 3, 8, 10, 11, 9, 4, 7, 5, 6, 20, 22, 23, 21, 16, 17, 18, 19, 12, 15, 13, 14],
  ![0, 1, 2, 3, 9, 11, 10, 8, 7, 4, 6, 5, 23, 21, 20, 22, 16, 17, 18, 19, 14, 13, 15, 12],
  ![0, 1, 2, 3, 10, 8, 9, 11, 5, 6, 4, 7, 21, 23, 22, 20, 16, 17, 18, 19, 15, 12, 14, 13],
  ![0, 1, 2, 3, 11, 9, 8, 10, 6, 5, 7, 4, 22, 20, 21, 23, 16, 17, 18, 19, 13, 14, 12, 15],
  ![0, 1, 2, 3, 12, 15, 13, 14, 20, 23, 21, 22, 4, 6, 7, 5, 16, 17, 18, 19, 8, 10, 11, 9],
  ![0, 1, 2, 3, 13, 14, 12, 15, 22, 21, 23, 20, 6, 4, 5, 7, 16, 17, 18, 19, 11, 9, 8, 10],
  ![0, 1, 2, 3, 14, 13, 15, 12, 23, 20, 22, 21, 7, 5, 4, 6, 16, 17, 18, 19, 9, 11, 10, 8],
  ![0, 1, 2, 3, 15, 12, 14, 13, 21, 22, 20, 23, 5, 7, 6, 4, 16, 17, 18, 19, 10, 8, 9, 11],
  ![0, 1, 2, 3, 20, 21, 22, 23, 12, 14, 15, 13, 8, 11, 9, 10, 16, 17, 18, 19, 4, 5, 6, 7],
  ![0, 1, 2, 3, 21, 20, 23, 22, 15, 13, 12, 14, 10, 9, 11, 8, 16, 17, 18, 19, 5, 4, 7, 6],
  ![0, 1, 2, 3, 22, 23, 20, 21, 13, 15, 14, 12, 11, 8, 10, 9, 16, 17, 18, 19, 6, 7, 4, 5],
  ![0, 1, 2, 3, 23, 22, 21, 20, 14, 12, 13, 15, 9, 10, 8, 11, 16, 17, 18, 19, 7, 6, 5, 4]
]

/-- Original code labels whose actual physical Golay signs vanish on the entire octad. -/
def generatedTwelfthRootKernelSignLabel : Fin 32 → Fin 4096 :=
  ![0, 3, 4, 7, 9, 10, 13, 14, 96, 99, 100, 103, 105, 106, 109, 110,
    176, 179, 180, 183, 185, 186, 189, 190, 208, 211, 212, 215, 217, 218, 221, 222]

/-- The actual original octad positions, in the insertion order already used by the matrix. -/
def generatedTwelfthRootKernelOctadCoordinate : Fin 8 → Fin 24 :=
  ![0, 1, 2, 3, 16, 17, 18, 19]

/-- Every recorded word fixes each original physical octad coordinate individually. -/
theorem generatedTwelfth_root_kernel_permutation_octad : ∀ p : Fin 16, ∀ i : Fin 8,
    generatedTwelfthRootKernelPermutationForward p (generatedTwelfthRootKernelOctadCoordinate i) =
      generatedTwelfthRootKernelOctadCoordinate i := by
  decide +kernel

/-- The complete recorded arrays are genuine inverse permutations at every coordinate. -/
theorem generatedTwelfth_root_kernel_permutation_inverse : ∀ p : Fin 16, ∀ i : Fin 24,
    generatedTwelfthRootKernelPermutationForward p
      (generatedTwelfthRootKernelPermutationBackward p i) = i := by
  decide +kernel

/-- All sixteen original physical permutation arrays are distinct. -/
theorem generatedTwelfth_root_kernel_permutation_distinct : ∀ p q : Fin 16,
    (∀ i : Fin 24, generatedTwelfthRootKernelPermutationForward p i =
      generatedTwelfthRootKernelPermutationForward q i) → p = q := by
  decide +kernel

/-- Every original Golay sign is zero on every physical coordinate of the actual octad. -/
theorem generatedTwelfth_root_kernel_sign_octad : ∀ a : Fin 32, ∀ i : Fin 8,
    (sourceGeneratedSignCode (generatedTwelfthRootKernelSignLabel a)).val
      (generatedTwelfthRootKernelOctadCoordinate i) = 0 := by
  decide +kernel

/-- The original actual sign labels are distinct finite Golay coordinates. -/
theorem generatedTwelfth_root_kernel_sign_label_injective :
    Function.Injective generatedTwelfthRootKernelSignLabel := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
