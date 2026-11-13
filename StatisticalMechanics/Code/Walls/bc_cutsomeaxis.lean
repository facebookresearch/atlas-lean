/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























































import Mathlib
import Code.Percolation.ClusterReachesRay

open MeasureTheory Set
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Walls

open StatMech.Percolation

variable {d : ℕ}











theorem bc_exists_far_axis_of_notMem_box {y : Site d} {n : ℕ} (hyb : y ∉ box d n) :
    ∃ i : Fin d, n < (y i).natAbs := by
  rw [mem_box] at hyb
  push Not at hyb
  exact hyb












theorem bc_cut_some_axis_of_far_witness (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    {y : Site d} {n : ℕ} (hyb : y ∉ box d n) (hyc : Connected d (removeSite 0 ω) x y) :
    ∃ z, (∃ i : Fin d, n < (z i).natAbs) ∧ Connected d (removeSite 0 ω) x z :=
  ⟨y, bc_exists_far_axis_of_notMem_box hyb, hyc⟩













theorem bc_cut_reaches_far_coord (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d (removeSite 0 ω) x).Infinite) (n : ℕ) :
    ∃ y, (∃ i : Fin d, n < (y i).natAbs) ∧ Connected d (removeSite 0 ω) x y := by
  obtain ⟨y, hyb, hyc⟩ := crr_removeSite_infinite_reaches_far ω x hinf n
  exact bc_cut_some_axis_of_far_witness ω x hyb hyc




theorem bc_cut_some_axis (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d (removeSite 0 ω) x).Infinite) :
    ∀ n : ℕ, ∃ y, ∃ i : Fin d,
      n < (y i).natAbs ∧ Connected d (removeSite 0 ω) x y := by
  intro n
  obtain ⟨y, ⟨i, hi⟩, hyc⟩ := bc_cut_reaches_far_coord ω x hinf n
  exact ⟨y, i, hi, hyc⟩











theorem bc_some_axis (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d ω x).Infinite) (n : ℕ) :
    ∃ y, (∃ i : Fin d, n < (y i).natAbs) ∧ Connected d ω x y :=
  crr_infinite_reaches_far_coord ω x hinf n

end Walls

end StatMech
