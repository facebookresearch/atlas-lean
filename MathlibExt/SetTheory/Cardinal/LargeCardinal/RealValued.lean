/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Steven Warner
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 57, Logic 333, Logic 334, Logic 58

open Set Cardinal Function MeasureTheory

/-!
# `MathlibExt.SetTheory.Cardinal.LargeCardinal.RealValued`

## References

* Jech (for `IsNontrivialProbabilityMeasure`, `CarriesNontrivialMeasure`,
  `IsLeastCardinalWithNontrivialMeasure`, `nullIdeal`)

## References

* Jech (for `IsNontrivialProbabilityMeasure`, `CarriesNontrivialMeasure`,
  `IsLeastCardinalWithNontrivialMeasure`, `nullIdeal`)

## References

* Jech (for `IsNontrivialProbabilityMeasure`, `CarriesNontrivialMeasure`,
  `IsLeastCardinalWithNontrivialMeasure`, `nullIdeal`)

## References

* Jech (for `IsNontrivialProbabilityMeasure`, `CarriesNontrivialMeasure`,
  `IsLeastCardinalWithNontrivialMeasure`, `nullIdeal`)

## References

* Jech (for `IsNontrivialProbabilityMeasure`, `CarriesNontrivialMeasure`,
  `IsLeastCardinalWithNontrivialMeasure`, `nullIdeal`)

## References

* Jech (for `IsNontrivialProbabilityMeasure`, `CarriesNontrivialMeasure`,
  `IsLeastCardinalWithNontrivialMeasure`, `nullIdeal`)

## References

* Jech (for `IsNontrivialProbabilityMeasure`, `CarriesNontrivialMeasure`,
  `IsLeastCardinalWithNontrivialMeasure`, `nullIdeal`)
-/

namespace MetaMathlibExt

-- Logic 57: Nontrivial probability measure

/-- A measure μ defined on *all* subsets of I — i.e. a measure for the discrete
σ-algebra on I — is a *nontrivial probability measure* if μ(I) = 1 and
μ({x}) = 0 for every x ∈ I.
-/
def IsNontrivialProbabilityMeasure.{u} {I : Type u} (μ : @Measure I ⊤) : Prop :=
  @IsProbabilityMeasure I ⊤ μ ∧ @NullSingletonClass I ⊤ μ

-- Logic 333: Carries nontrivial measure

/-- A cardinal c carries a nontrivial measure iff there exists a set I
with |I|=c which carries a nontrivial probability measure μ defined
on all subsets of I.
-/
def CarriesNontrivialMeasure.{u} (c : Cardinal.{u}) : Prop :=
  ∃ I : Type u, #I = c ∧
    let : MeasurableSpace I := ⊤
    ∃ μ : Measure I, IsNontrivialProbabilityMeasure μ

-- Logic 334: Least cardinal that carries nontrivial measure

/-- κ is the least cardinal carrying a nontrivial measure if κ carries a nontrivial measure and no
smaller cardinal does.
-/
def IsLeastCardinalWithNontrivialMeasure.{u} (κ : Cardinal.{u}) : Prop :=
  IsLeast {c : Cardinal.{u} | CarriesNontrivialMeasure c} κ

-- Logic 58: Null ideal

/-- The *null ideal* of a measure μ is I_μ := { A ⊆ I ∣ μ(A) = 0 } -/
def nullIdeal.{u} {I : Type u} [MeasurableSpace I] (μ : Measure I) : Set (Set I) :=
  {A : Set I | μ A = 0}

end MetaMathlibExt

end
