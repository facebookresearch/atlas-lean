/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































import Mathlib
import Code.Percolation.ClusterReachesRay

open MeasureTheory Set
open scoped BigOperators
open StatMech.Lattice StatMech.ConfigSpace SimpleGraph
open StatMech.Percolation

namespace StatMech.Walls

variable {d : ℕ}












theorem bc_cutUnbounded (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d (removeSite 0 ω) x).Infinite) (n : ℕ) :
    ∃ y, y ∉ box d n ∧ Connected d (removeSite 0 ω) x y :=
  (cluster_infinite_iff (removeSite 0 ω) x).mp hinf n




theorem bc_cutUnbounded_eq_crr (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d (removeSite 0 ω) x).Infinite) (n : ℕ) :
    bc_cutUnbounded ω x hinf n = crr_removeSite_infinite_reaches_far ω x hinf n :=
  rfl













theorem bc_cutUnbounded_coord (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d (removeSite 0 ω) x).Infinite) (n : ℕ) :
    ∃ y, (∃ i : Fin d, n < (y i).natAbs) ∧ Connected d (removeSite 0 ω) x y :=
  crr_infinite_reaches_far_coord (removeSite 0 ω) x hinf n







theorem bc_cutUnbounded_converse (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (h : ∀ n : ℕ, ∃ y, y ∉ box d n ∧ Connected d (removeSite 0 ω) x y) :
    (cluster d (removeSite 0 ω) x).Infinite :=
  (cluster_infinite_iff (removeSite 0 ω) x).mpr h





theorem bc_cutUnbounded_iff (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    (cluster d (removeSite 0 ω) x).Infinite ↔
      ∀ n : ℕ, ∃ y, y ∉ box d n ∧ Connected d (removeSite 0 ω) x y :=
  cluster_infinite_iff (removeSite 0 ω) x

end StatMech.Walls
