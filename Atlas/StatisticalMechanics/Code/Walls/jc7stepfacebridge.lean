/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























import Mathlib
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartOrbit
import Code.Lattice.OrbitEncloses
import Code.Lattice.OrbitLoopBridge

open SimpleGraph Function Set

namespace StatMech

namespace Walls

open StatMech.Lattice









theorem jc7_dartFace_iterate_mem_olb_orbitLoop_support
    (K : Set (Site 2)) (hK : K.Finite) (e : Dart) (he : IsBoundaryDart K e) (n : ℕ) :
    dartFace ((dartNext K)^[n] e) ∈ (olb_orbitLoop K hK e he).support := by
  rw [olb_orbitLoop_support K hK e he]
  exact dartFace_iterate_mem_dartOrbitFaceLoop_support K hK e he n

end Walls

end StatMech
