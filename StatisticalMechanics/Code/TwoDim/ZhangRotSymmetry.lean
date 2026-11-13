/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Code.TwoDim.ZhangClose
import Code.TwoDim.SelfDualDichotomy

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatMech

namespace TwoDim

open StatMech.Lattice StatMech.Universality












theorem zrs_rotConfig_apply (ω : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    kdi_rotConfig ω e = ω (kdi_rotEdgeEquiv.symm e) := by
  rw [kdi_rotConfig, Equiv.piCongrLeft_apply, eq_rec_constant]





theorem zrs_rotConfig_monotone : Monotone (kdi_rotConfig) := by
  intro ω₁ ω₂ hle b
  rw [zrs_rotConfig_apply, zrs_rotConfig_apply]
  exact hle _




theorem zrs_rotPreimage_isIncreasing {A : Set (ConfigSpace (Sym2 (Site 2)))}
    (hA : IsIncreasing A) : IsIncreasing (kdi_rotConfig ⁻¹' A) :=
  IsUpperSet.preimage hA zrs_rotConfig_monotone



theorem zrs_rotPreimage_measurableSet {A : Set (ConfigSpace (Sym2 (Site 2)))}
    (hA : MeasurableSet A) : MeasurableSet (kdi_rotConfig ⁻¹' A) :=
  kdi_measurable_rotConfig hA







theorem zrs_rotPreimage_measureReal {A : Set (ConfigSpace (Sym2 (Site 2)))}
    (hA : MeasurableSet A) :
    halfMeasure.real (kdi_rotConfig ⁻¹' A) = halfMeasure.real A :=
  kdi_rotConfig_measurePreserving.measureReal_preimage hA.nullMeasurableSet











def zrs_rot (A : Set (ConfigSpace (Sym2 (Site 2)))) : Set (ConfigSpace (Sym2 (Site 2))) :=
  kdi_rotConfig ⁻¹' A







def zrs_sideFamily (base : Set (ConfigSpace (Sym2 (Site 2)))) :
    Fin 4 → Set (ConfigSpace (Sym2 (Site 2))) :=
  ![base, zrs_rot (zrs_rot base), zrs_rot base, zrs_rot (zrs_rot (zrs_rot base))]

@[simp] theorem zrs_sideFamily_zero (base : Set (ConfigSpace (Sym2 (Site 2)))) :
    zrs_sideFamily base 0 = base := rfl
@[simp] theorem zrs_sideFamily_one (base : Set (ConfigSpace (Sym2 (Site 2)))) :
    zrs_sideFamily base 1 = zrs_rot (zrs_rot base) := rfl
@[simp] theorem zrs_sideFamily_two (base : Set (ConfigSpace (Sym2 (Site 2)))) :
    zrs_sideFamily base 2 = zrs_rot base := rfl
@[simp] theorem zrs_sideFamily_three (base : Set (ConfigSpace (Sym2 (Site 2)))) :
    zrs_sideFamily base 3 = zrs_rot (zrs_rot (zrs_rot base)) := rfl



theorem zrs_sideFamily_isIncreasing {base : Set (ConfigSpace (Sym2 (Site 2)))}
    (hbase : IsIncreasing base) (i : Fin 4) : IsIncreasing (zrs_sideFamily base i) := by
  fin_cases i
  · exact hbase
  · exact zrs_rotPreimage_isIncreasing (zrs_rotPreimage_isIncreasing hbase)
  · exact zrs_rotPreimage_isIncreasing hbase
  · exact zrs_rotPreimage_isIncreasing
      (zrs_rotPreimage_isIncreasing (zrs_rotPreimage_isIncreasing hbase))



theorem zrs_sideFamily_measurableSet {base : Set (ConfigSpace (Sym2 (Site 2)))}
    (hbase : MeasurableSet base) (i : Fin 4) : MeasurableSet (zrs_sideFamily base i) := by
  fin_cases i
  · exact hbase
  · exact zrs_rotPreimage_measurableSet (zrs_rotPreimage_measurableSet hbase)
  · exact zrs_rotPreimage_measurableSet hbase
  · exact zrs_rotPreimage_measurableSet
      (zrs_rotPreimage_measurableSet (zrs_rotPreimage_measurableSet hbase))











theorem zrs_side_symmetry {base : Set (ConfigSpace (Sym2 (Site 2)))}
    (hbase : MeasurableSet base) (i : Fin 4) :
    halfMeasure.real (zrs_sideFamily base i) = halfMeasure.real (zrs_sideFamily base 0) := by
  have hρ := zrs_rotPreimage_measurableSet hbase
  have hρρ := zrs_rotPreimage_measurableSet hρ
  fin_cases i
  · rfl
  · 
    show halfMeasure.real (zrs_rot (zrs_rot base)) = halfMeasure.real base
    simp only [zrs_rot]
    rw [zrs_rotPreimage_measureReal hρ, zrs_rotPreimage_measureReal hbase]
  · 
    show halfMeasure.real (zrs_rot base) = halfMeasure.real base
    simp only [zrs_rot]
    rw [zrs_rotPreimage_measureReal hbase]
  · 
    show halfMeasure.real (zrs_rot (zrs_rot (zrs_rot base))) = halfMeasure.real base
    simp only [zrs_rot]
    rw [zrs_rotPreimage_measureReal hρρ, zrs_rotPreimage_measureReal hρ,
      zrs_rotPreimage_measureReal hbase]





























def zrs_geometricData_of_remaining
    {A B : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (base : ℕ → Set (ConfigSpace (Sym2 (Site 2))))
    (Err : ℕ → Set (ConfigSpace (Sym2 (Site 2))))
    (hbaseInc : ∀ n, IsIncreasing (base n))
    (hbaseM : ∀ n, MeasurableSet (base n))
    (herr : Tendsto (fun n => halfMeasure.real (Err n)) atTop (𝓝 0))
    (hunion : Tendsto (fun n =>
        halfMeasure.real (zrs_sideFamily (base n) 0 ∪ zrs_sideFamily (base n) 1
          ∪ zrs_sideFamily (base n) 2 ∪ zrs_sideFamily (base n) 3)) atTop (𝓝 1))
    (hmerge : ∀ n, zrs_sideFamily (base n) 0 ∩ zrs_sideFamily (base n) 1
        ⊆ (A n ∪ B n) ∪ Err n) :
    ZhangGeometricData halfMeasure A B where
  S := fun i n => zrs_sideFamily (base n) i
  Err := Err
  Sinc := fun i n => zrs_sideFamily_isIncreasing (hbaseInc n) i
  Sm := fun i n => zrs_sideFamily_measurableSet (hbaseM n) i
  Ssym := fun i n => zrs_side_symmetry (hbaseM n) i
  errTendsto := herr
  unionTendsto := hunion
  merge := hmerge





theorem zrs_geometricData_Ssym
    {A B : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (base : ℕ → Set (ConfigSpace (Sym2 (Site 2))))
    (Err : ℕ → Set (ConfigSpace (Sym2 (Site 2))))
    (hbaseInc : ∀ n, IsIncreasing (base n))
    (hbaseM : ∀ n, MeasurableSet (base n))
    (herr : Tendsto (fun n => halfMeasure.real (Err n)) atTop (𝓝 0))
    (hunion : Tendsto (fun n =>
        halfMeasure.real (zrs_sideFamily (base n) 0 ∪ zrs_sideFamily (base n) 1
          ∪ zrs_sideFamily (base n) 2 ∪ zrs_sideFamily (base n) 3)) atTop (𝓝 1))
    (hmerge : ∀ n, zrs_sideFamily (base n) 0 ∩ zrs_sideFamily (base n) 1
        ⊆ (A n ∪ B n) ∪ Err n) :
    ∀ i n, halfMeasure.real
        ((zrs_geometricData_of_remaining base Err hbaseInc hbaseM herr hunion hmerge).S i n)
      = halfMeasure.real
        ((zrs_geometricData_of_remaining base Err hbaseInc hbaseM herr hunion hmerge).S 0 n) :=
  (zrs_geometricData_of_remaining base Err hbaseInc hbaseM herr hunion hmerge).Ssym














theorem zrs_zhangUnion_of_remaining
    {A B : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (hpa : PositivelyAssociated halfMeasure)
    (base : ℕ → Set (ConfigSpace (Sym2 (Site 2))))
    (Err : ℕ → Set (ConfigSpace (Sym2 (Site 2))))
    (hbaseInc : ∀ n, IsIncreasing (base n))
    (hbaseM : ∀ n, MeasurableSet (base n))
    (herr : Tendsto (fun n => halfMeasure.real (Err n)) atTop (𝓝 0))
    (hunion : Tendsto (fun n =>
        halfMeasure.real (zrs_sideFamily (base n) 0 ∪ zrs_sideFamily (base n) 1
          ∪ zrs_sideFamily (base n) 2 ∪ zrs_sideFamily (base n) 3)) atTop (𝓝 1))
    (hmerge : ∀ n, zrs_sideFamily (base n) 0 ∩ zrs_sideFamily (base n) 1
        ⊆ (A n ∪ B n) ∪ Err n) :
    Tendsto (fun n => halfMeasure.real (A n ∪ B n)) atTop (𝓝 1) :=
  zhg_union_of_geometricData halfMeasure hpa
    (zrs_geometricData_of_remaining base Err hbaseInc hbaseM herr hunion hmerge)

end TwoDim

end StatMech
