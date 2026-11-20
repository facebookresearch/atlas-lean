/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































import Mathlib
import Code.Percolation.ClusterReachesRay
import Code.Walls.bc_cutunbounded
import Code.Walls.bkm_dccwitnessnezero

open MeasureTheory Set
open scoped BigOperators
open StatMech.Lattice StatMech.ConfigSpace SimpleGraph
open StatMech.Percolation

namespace StatMech.Walls

variable {d : ℕ}










theorem bc2_cluster_infinite_of_connected (ω : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (hinf : (cluster d (removeSite 0 ω) x).Infinite)
    (hxy : Connected d (removeSite 0 ω) x y) :
    (cluster d (removeSite 0 ω) y).Infinite := by
  rwa [← cluster_eq_of_connected hxy]





theorem bc2_connected_ne_zero (ω : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (hinf : (cluster d (removeSite 0 ω) x).Infinite)
    (hxy : Connected d (removeSite 0 ω) x y) :
    y ≠ 0 :=
  bkm_witness_ne_zero ω (bc2_cluster_infinite_of_connected ω hinf hxy)




















theorem bc2_cutUnbounded (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d (removeSite 0 ω) x).Infinite) (n : ℕ) :
    ∃ y, y ∉ box d n ∧ Connected d (removeSite 0 ω) x y ∧
      (cluster d (removeSite 0 ω) y).Infinite ∧ y ≠ 0 := by
  obtain ⟨y, hyb, hyc⟩ := crr_removeSite_infinite_reaches_far ω x hinf n
  exact ⟨y, hyb, hyc, bc2_cluster_infinite_of_connected ω hinf hyc,
    bc2_connected_ne_zero ω hinf hyc⟩










theorem bc2_cutUnbounded_coord (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d (removeSite 0 ω) x).Infinite) (n : ℕ) :
    ∃ y, (∃ i : Fin d, n < (y i).natAbs) ∧ Connected d (removeSite 0 ω) x y ∧
      (cluster d (removeSite 0 ω) y).Infinite ∧ y ≠ 0 := by
  obtain ⟨y, hyb, hyc, hyinf, hy0⟩ := bc2_cutUnbounded ω x hinf n
  rw [mem_box] at hyb
  push Not at hyb
  exact ⟨y, hyb, hyc, hyinf, hy0⟩








theorem bc2_cutUnbounded_converse (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (h : ∀ n : ℕ, ∃ y, y ∉ box d n ∧ Connected d (removeSite 0 ω) x y) :
    (cluster d (removeSite 0 ω) x).Infinite :=
  (cluster_infinite_iff (removeSite 0 ω) x).mpr h







theorem bc2_cutUnbounded_iff (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    (cluster d (removeSite 0 ω) x).Infinite ↔
      ∀ n : ℕ, ∃ y, y ∉ box d n ∧ Connected d (removeSite 0 ω) x y ∧
        (cluster d (removeSite 0 ω) y).Infinite ∧ y ≠ 0 := by
  constructor
  · intro hinf n; exact bc2_cutUnbounded ω x hinf n
  · intro h
    refine bc2_cutUnbounded_converse ω x (fun n => ?_)
    obtain ⟨y, hyb, hyc, _, _⟩ := h n
    exact ⟨y, hyb, hyc⟩









theorem bc2_cutUnbounded_proj (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d (removeSite 0 ω) x).Infinite) (n : ℕ) :
    ∃ y, y ∉ box d n ∧ Connected d (removeSite 0 ω) x y := by
  obtain ⟨y, hyb, hyc, _, _⟩ := bc2_cutUnbounded ω x hinf n
  exact ⟨y, hyb, hyc⟩

end StatMech.Walls
