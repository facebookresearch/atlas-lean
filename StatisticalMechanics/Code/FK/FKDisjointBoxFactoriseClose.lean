/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































import Code.FK.FKWiredDomainMonotone
import Code.FK.FKDisjointBoxReduce

open MeasureTheory Filter Topology Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace StatMech

namespace FK

open ConfigSpace

variable {d : ℕ}











theorem fdf_exists_common_cross_box (P : Finset (Finset (Sym2 (Site d))))
    (g : Multiplicative (Site d)) :
    ∃ M : ℕ, ∀ T ∈ P, ∀ T' ∈ P,
      ∃ t : Finset (Sym2 (boxVerts d M)),
        T ∪ T'.image (fun e => g⁻¹ • e) = t.image (edgeIncl d M) := by
  classical
  
  set Q : Finset (Finset (Sym2 (Site d))) :=
    (P ×ˢ P).image (fun pr => pr.1 ∪ pr.2.image (fun e => g⁻¹ • e)) with hQ
  
  obtain ⟨M, hM⟩ := fwm_exists_realising_box Q
  refine ⟨M, fun T hT T' hT' => ?_⟩
  have hmem : (T ∪ T'.image (fun e => g⁻¹ • e)) ∈ Q := by
    rw [hQ, Finset.mem_image]
    exact ⟨(T, T'), Finset.mem_product.mpr ⟨hT, hT'⟩, rfl⟩
  exact hM _ hmem


























theorem fdf_factorise_of_finiteBoxDisjointProductDom {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hfin : ftb_FiniteBoxDisjointProductDom hp hp1
      (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))))) :
    fwm_WiredDisjointBoxFactorise hp hp1
      (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))) := by
  classical
  intro P N hreal
  
  obtain ⟨g, hg⟩ := hfin P N
  
  obtain ⟨M₀, hM₀⟩ := fdf_exists_common_cross_box P g
  
  have hev : ∀ᶠ m in atTop, (N ≤ m ∧ M₀ ≤ m) ∧ (∀ T ∈ P, ∀ T' ∈ P,
      (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (fmu_multiOpen T ∩
              (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
                ⁻¹' fmu_multiOpen T')
        ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
          * (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2)
              : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T')) :=
    ((Filter.eventually_ge_atTop N).and (Filter.eventually_ge_atTop M₀)).and hg
  obtain ⟨M, ⟨hNM, hM₀M⟩, hgM⟩ := hev.exists
  
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hNM
  refine ⟨g, r, fun T hT T' hT' => ?_⟩
  refine ⟨?_, hgM T hT T' hT'⟩
  
  obtain ⟨t₀, ht₀⟩ := hM₀ T hT T' hT'
  exact ⟨t₀.image (innerEdgeLE d hM₀M), fwm_realised_box_mono hM₀M ht₀⟩















theorem fdf_factorise_of_boxCap {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hcap : fdb_BoxConditionalProductCap (d := d) hp hp1) :
    fwm_WiredDisjointBoxFactorise hp hp1
      (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))) :=
  fdf_factorise_of_finiteBoxDisjointProductDom hp hp1
    (fdb_finiteBoxDisjointProductDom_of_boxCap hp hp1 hcap)



















theorem fdf_wiredIV_isErgodic_of_boxCap {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hcap : fdb_BoxConditionalProductCap (d := d) hp hp1) :
    IsErgodic (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  fwm_wiredIV_isErgodic_of_factorise hp hp1 (fdf_factorise_of_boxCap hp hp1 hcap)

end FK

end StatMech
