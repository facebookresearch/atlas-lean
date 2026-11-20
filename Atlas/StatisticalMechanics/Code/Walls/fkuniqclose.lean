/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































import Code.FK.FreeWiredAgreeClose
import Code.FK.FKUniquenessFull

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
















theorem fku_free_eq_wired_cylinder (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hbad : p ∉ fwa_badP d) {N : ℕ} (hN : 1 ≤ N)
    {A : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hA : IsIncreasing A) :
    (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A)
      = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A) :=
  fwa_box_agree hd hp hp1 hbad hN hA























theorem fku_unique_off_countable (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hbad : p ∉ fwa_badP d)
    (phi : Measure (ConfigSpace (Sym2 (Site d))))
    (hsand : ∀ (N : ℕ), 1 ≤ N → ∀ {A : Set (ConfigSpace (Sym2 (boxVerts d N)))}, IsIncreasing A →
      (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A)
          ≤ phi.real (boxRestrict d N ⁻¹' A)
      ∧ phi.real (boxRestrict d N ⁻¹' A)
          ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A)) :
    ∀ (N : ℕ), 1 ≤ N → ∀ {A : Set (ConfigSpace (Sym2 (boxVerts d N)))}, IsIncreasing A →
      phi.real (boxRestrict d N ⁻¹' A)
          = (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A)
      ∧ phi.real (boxRestrict d N ⁻¹' A)
          = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A) := by
  intro N hN A hA
  exact dlr_sandwich_unique (hsand N hN hA) (fku_free_eq_wired_cylinder hd hp hp1 hbad hN hA)










theorem fku_uniqueness_capstone (hd : 1 ≤ d) :
    ∃ S : Set ℝ, S.Countable ∧
      ∀ p, 0 < p → p < 1 → p ∉ S →
        ∀ (hp : 0 < p) (hp1 : p < 1) (phi : Measure (ConfigSpace (Sym2 (Site d)))),
          (∀ (N : ℕ), 1 ≤ N → ∀ {A : Set (ConfigSpace (Sym2 (boxVerts d N)))}, IsIncreasing A →
            (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
                : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A)
                ≤ phi.real (boxRestrict d N ⁻¹' A)
            ∧ phi.real (boxRestrict d N ⁻¹' A)
                ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
                  : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A)) →
          ∀ (N : ℕ), 1 ≤ N → ∀ {A : Set (ConfigSpace (Sym2 (boxVerts d N)))}, IsIncreasing A →
            phi.real (boxRestrict d N ⁻¹' A)
                = (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
                  : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A)
            ∧ phi.real (boxRestrict d N ⁻¹' A)
                = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)
                  : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A) := by
  refine ⟨fwa_badP d, fwa_badP_countable hd, ?_⟩
  intro p hp0 hp01 hbad hp hp1 phi hsand
  exact fku_unique_off_countable hd hp hp1 hbad phi hsand




theorem fku_exists_good (hd : 1 ≤ d) :
    ∃ p : ℝ, 0 < p ∧ p < 1 ∧ p ∉ fwa_badP d :=
  fwa_exists_good hd

end FK

end StatMech
