/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.EuclidGameCalkinWilf

open MetaMathlibExt

-- The root is terminal, and its two arch tops occur in the second row.
example : euclidMoves (1, 1) = ∅ ∧ (3, 2) ∈ calkinWilfRow 2 ∧ (2, 3) ∈ calkinWilfRow 2 := by
  decide

-- The two distinct paths also give P-positions for an unequal pair with a common factor.
example : euclidPPosition 14 10 = true ∧ euclidPPosition 10 16 = true :=
  euclidPPosition_tops_of_arch 4 6 (by decide) (by decide) (by decide)

-- From the left arch top the move is forced, although the reply need not be.
example : euclidMoves (14, 10) = {(4, 10)} ∧ euclidMoves (4, 10) = {(4, 6), (4, 2)} := by
  decide

-- At the root both mixed grandchildren are P-positions, so the aunt cannot be one.
example : euclidPPosition 2 1 ≠ true := by
  have h := (euclidPPosition_aunt_xor_cousin 1 1 (by decide) (by decide)).1 (by decide)
  exact fun ha => h.mp ha (by decide)

-- At (4, 2) the female cousin is an N-position, so the uncle is a P-position.
example : euclidPPosition 4 6 = true :=
  ((euclidPPosition_aunt_xor_cousin 4 2 (by decide) (by decide)).2.2.1 (by decide)).mpr (by decide)
