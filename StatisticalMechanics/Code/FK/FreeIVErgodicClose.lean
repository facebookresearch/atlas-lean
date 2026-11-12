/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































































import Code.FK.CrossBoxGeneralKeystone
import Code.FK.FKTwoBoxDecoupling
import Code.FK.FKWiredDomainMonotone
import Code.FK.FKMixingUpperClose

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

















theorem fie_freeIV_isErgodic_of_eq_wired {p : ℝ} (hd : 1 ≤ d) (hp : 0 < p) (hp1 : p < 1)
    (heq : (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))
      = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))) :
    IsErgodic (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) := by
  rw [heq]
  exact cbk_wiredIV_isErgodic hd hp hp1













def fie_FreeWiredAgree {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : Prop :=
  (∀ T : Finset (Sym2 (Site d)),
      (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T)
        = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T))
  ∧ (∀ (g : Multiplicative (Site d)) (T T' : Finset (Sym2 (Site d))),
      (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (fmu_multiOpen T ∩
              (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
                ⁻¹' fmu_multiOpen T')
        = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real
            (fmu_multiOpen T ∩
              (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
                ⁻¹' fmu_multiOpen T'))





theorem fie_agree_of_eq {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (heq : (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))
      = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))) :
    fie_FreeWiredAgree (d := d) hp hp1 := by
  refine ⟨fun T => ?_, fun g T T' => ?_⟩ <;> rw [heq]





theorem fie_freeWiredAgree_satisfiable {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (heq : (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))
      = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))) :
    fie_FreeWiredAgree (d := d) hp hp1 :=
  fie_agree_of_eq hp hp1 heq













theorem fie_freeUpperDecay_of_agree {p : ℝ} (hd : 1 ≤ d) (hp : 0 < p) (hp1 : p < 1)
    (hagree : fie_FreeWiredAgree (d := d) hp hp1) :
    fmu_UpperDecay (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) := by
  obtain ⟨hmass, hcross⟩ := hagree
  have hwired := fwm_upperDecay_of_factorise hp hp1 (cbk_wiredDisjointBoxFactorise_ge1 hd hp hp1)
  intro P δ hδ
  obtain ⟨g, hg⟩ := hwired P δ hδ
  refine ⟨g, fun T hT T' hT' => ?_⟩
  rw [hcross g T T', hmass T, hmass T']
  exact hg T hT T' hT'





















theorem fie_freeIV_isErgodic_of_agree {p : ℝ} (hd : 1 ≤ d) (hp : 0 < p) (hp1 : p < 1)
    (hagree : fie_FreeWiredAgree (d := d) hp hp1) :
    IsErgodic (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) := by
  set μ := (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
    : Measure (ConfigSpace (Sym2 (Site d)))) with hμdef
  have hμ : IsTranslationInvariant (G := Multiplicative (Site d)) μ :=
    bdp_freeIV_isTranslationInvariant hp hp1
  
  have hup := fie_freeUpperDecay_of_agree hd hp hp1 hagree
  
  refine fmu_freeIV_isErgodic_of_pairMixing hp hp1 ?_
  intro P δ hδ
  obtain ⟨g, hg⟩ := hup P (δ / 2) (by linarith)
  refine ⟨g, fun T hT T' hT' => ?_⟩
  
  have hlow : μ.real (fmu_multiOpen T) * μ.real (fmu_multiOpen T')
      ≤ μ.real (fmu_multiOpen T ∩
          (shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
            ⁻¹' fmu_multiOpen T') := by
    rw [fmu_shift_multiOpen g T']
    have hfkg := ftb_freeIV_fkg_multiOpen hp hp1 T (T'.image (fun e => g⁻¹ • e))
    have htrans : μ.real (fmu_multiOpen (T'.image (fun e => g⁻¹ • e)))
        = μ.real (fmu_multiOpen T') := by
      rw [← fmu_shift_multiOpen g T']
      exact fmc_real_preimage_shift hμ g (fmu_multiOpen_measurable T')
    rw [htrans] at hfkg
    exact hfkg
  have hup' := hg T hT T' hT'
  rw [abs_of_nonneg (by linarith)]
  linarith










theorem fie_freeIV_isErgodic_of_eq_wired' {p : ℝ} (hd : 1 ≤ d) (hp : 0 < p) (hp1 : p < 1)
    (heq : (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))
      = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))) :
    IsErgodic (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  fie_freeIV_isErgodic_of_agree hd hp hp1 (fie_agree_of_eq hp hp1 heq)

end FK

end StatMech
