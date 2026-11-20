/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































import Mathlib
import Code.Percolation.BurtonKeaneClose
import Code.Percolation.BurtonKeaneAttachment
import Code.Percolation.HrouteHighDim
import Code.Percolation.TrifurcationConstruction

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

open DisjointPaths

variable {d : ℕ}
























theorem tfx_htrif_of_mergeFree
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hmf : ∀ (n : ℕ) (ω : ConfigSpace (Sym2 (Site d))),
      ω ∈ threeMeetBox d n → bka_MergeFree ω) :
    0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      0 < μ {ω | IsTrifurcation d ω 0} := by
  refine htrif_discharged μ hfe ?_
  refine hrHD_route_of_routing μ hfe ?_
  intro n
  exact bka_routing_of_mergeFree n (fun ω hω => hmf n ω hω)


















theorem bkc_htrif_bernoulli (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hmf : ∀ (n : ℕ) (ω : ConfigSpace (Sym2 (Site d))),
      ω ∈ threeMeetBox d n → bka_MergeFree ω) :
    0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = ⊤} →
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | IsTrifurcation d ω 0} :=
  tfx_htrif_of_mergeFree (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1)
    (bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0) hmf




















theorem tfx_burton_keane_bernoulli_of_mergeFree (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ),
      Tcount d ω n ≤ boxSV_boundaryCard d n)
    (hmf : ∀ (n : ℕ) (ω : ConfigSpace (Sym2 (Site d))),
      ω ∈ threeMeetBox d n → bka_MergeFree ω) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bkc_burton_keane_bernoulli hd p hp1 hp0 hbound (bkc_htrif_bernoulli p hp1 hp0 hmf)

end Percolation

end StatMech
