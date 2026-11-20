/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.JordanExteriorClosure

open Set SimpleGraph Function
open StatMech.Lattice

namespace StatMech.Walls













theorem kc6_mem_leftRegion_iff_odd {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (z : Site 2) :
    z ∈ jec_leftRegion Vc ↔ Odd (jec_rayCount z Vc) := by
  rw [jec_mem_leftRegion, Nat.not_even_iff_odd]



theorem kc6_odd_rayCount_of_mem {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z : Site 2} (hz : z ∈ jec_leftRegion Vc) :
    Odd (jec_rayCount z Vc) :=
  (kc6_mem_leftRegion_iff_odd Vc z).mp hz



theorem kc6_mem_of_odd_rayCount {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z : Site 2} (hz : Odd (jec_rayCount z Vc)) :
    z ∈ jec_leftRegion Vc :=
  (kc6_mem_leftRegion_iff_odd Vc z).mpr hz










theorem kc6_notMem_leftRegion_iff_even {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (z : Site 2) :
    z ∉ jec_leftRegion Vc ↔ Even (jec_rayCount z Vc) := by
  rw [kc6_mem_leftRegion_iff_odd, Nat.not_odd_iff_even]



theorem kc6_mem_compl_leftRegion_iff_even {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (z : Site 2) :
    z ∈ (jec_leftRegion Vc)ᶜ ↔ Even (jec_rayCount z Vc) := by
  rw [Set.mem_compl_iff]
  exact kc6_notMem_leftRegion_iff_even Vc z



theorem kc6_even_rayCount_of_notMem {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z : Site 2} (hz : z ∉ jec_leftRegion Vc) :
    Even (jec_rayCount z Vc) :=
  (kc6_notMem_leftRegion_iff_even Vc z).mp hz



theorem kc6_notMem_of_even_rayCount {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z : Site 2} (hz : Even (jec_rayCount z Vc)) :
    z ∉ jec_leftRegion Vc :=
  (kc6_notMem_leftRegion_iff_even Vc z).mpr hz





theorem kc6_leftRegion_eq_setOf_odd {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    jec_leftRegion Vc = {z : Site 2 | Odd (jec_rayCount z Vc)} := by
  ext z
  rw [Set.mem_setOf_eq]
  exact kc6_mem_leftRegion_iff_odd Vc z











theorem kc6_farLeft_notMem_of_even {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {t : Site 2} (ht : Even (jec_rayCount t Vc)) :
    t ∉ jec_leftRegion Vc :=
  kc6_notMem_of_even_rayCount Vc ht









theorem kc6_evenOddRule_node :
    ∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a) (z : Site 2),
      z ∈ jec_leftRegion Vc ↔ Odd (jec_rayCount z Vc) :=
  fun _ Vc z => kc6_mem_leftRegion_iff_odd Vc z

end StatMech.Walls
