/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ReferenceOutputKL

@[expose] public section

open MathlibExt.InformationTheory.ReferenceOutputKL MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace MathlibExtTest.InformationTheory.ReferenceOutputKL

/-- A product of two probability laws carries zero mutual information. -/
example {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) [IsProbabilityMeasure P] (R : Measure Y) [IsProbabilityMeasure R] :
    measureMutualInformation (⟨P.prod R, inferInstance⟩ : ProbabilityMeasure (X × Y)) = 0 :=
  measureMutualInformation_prod_eq_zero P R

/-- Against an independent reference the identity collapses to the output KL term. -/
example {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) [IsProbabilityMeasure P] (R Q : Measure Y) [IsProbabilityMeasure R]
    [IsProbabilityMeasure Q] :
    klDiv (P.prod R) (P.prod Q) = klDiv R Q :=
  klDiv_prod_prod_eq_klDiv P R Q

end MathlibExtTest.InformationTheory.ReferenceOutputKL
