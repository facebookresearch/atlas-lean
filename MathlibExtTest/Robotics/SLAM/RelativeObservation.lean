/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Robotics.SLAM.RelativeObservation

open Robotics.SLAM

-- Regular action of a group on itself: transforming the
-- pose `g` and the landmark `l` by the same `h` leaves
-- the relative observation unchanged, for arbitrary
-- group elements.
example {G : Type*} [Group G] (h g l : G) :
    (h * g)⁻¹ • (h • l) = g⁻¹ • l :=
  relativeObservation_invariant h g l

-- Permutations of `Fin 3` acting on points: with
-- `h = swap 0 1`, the transformed observation agrees.
example :
    ((Equiv.swap (0 : Fin 3) 1) * Equiv.swap (1 : Fin 3) 2)⁻¹ •
        (Equiv.swap (0 : Fin 3) 1) • (0 : Fin 3)
      = (Equiv.swap (1 : Fin 3) 2)⁻¹ • (0 : Fin 3) :=
  relativeObservation_invariant _ _ _

-- Transforming only the landmark generally changes the
-- observation: here the two sides differ.
example :
    (Equiv.swap (1 : Fin 3) 2)⁻¹ • (Equiv.swap (0 : Fin 3) 1) • (0 : Fin 3)
      ≠ (Equiv.swap (1 : Fin 3) 2)⁻¹ • (0 : Fin 3) := by decide

#print axioms relativeObservation_invariant
