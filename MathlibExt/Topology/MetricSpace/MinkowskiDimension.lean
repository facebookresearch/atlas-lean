/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Babak Modami
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.MetricSpace.CoveringNumbers

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Analysis 415, Analysis 416

/-!
# Upper Minkowski dimension; Lower Minkowski dimension

## References

* https://en.wikipedia.org/wiki/Minkowski%E2%80%93Bouligand_dimension (for `upperMinkowskiDim`,
  `lowerMinkowskiDim`)

## References

* https://en.wikipedia.org/wiki/Minkowski%E2%80%93Bouligand_dimension (for `upperMinkowskiDim`,
  `lowerMinkowskiDim`)

## References

* https://en.wikipedia.org/wiki/Minkowski%E2%80%93Bouligand_dimension (for `upperMinkowskiDim`,
  `lowerMinkowskiDim`)

## References

* https://en.wikipedia.org/wiki/Minkowski%E2%80%93Bouligand_dimension (for `upperMinkowskiDim`,
  `lowerMinkowskiDim`)

## References

* https://en.wikipedia.org/wiki/Minkowski%E2%80%93Bouligand_dimension (for `upperMinkowskiDim`,
  `lowerMinkowskiDim`)

## References

* https://en.wikipedia.org/wiki/Minkowski%E2%80%93Bouligand_dimension (for `upperMinkowskiDim`,
  `lowerMinkowskiDim`)

## References

* https://en.wikipedia.org/wiki/Minkowski%E2%80%93Bouligand_dimension (for `upperMinkowskiDim`,
  `lowerMinkowskiDim`)
-/

namespace MetaMathlibExt

-- Analysis 415: Upper Minkowski dimension

/-- Let E ⊆ X be a subset of a metric space X. For any ϵ>0 define the ϵ-covering number:
N_ϵ(E):=inf {n ∈ ℕ : E ⊂ ∪ᵢ₌₁ⁿ Bᵢ, ∀ i Bᵢ  is an open ball of radius  ϵ  }.
Note that when E is not bounded, the covering number is ∞ for all ϵ>0.

Then the upper Minkowski dimension of E is
limsup_{ϵ → 0} (log N_ϵ(E))/(log 1/ϵ)
-/
noncomputable def upperMinkowskiDim (X : Type) [MetricSpace X] (E : Set X) : ENNReal :=
  Filter.limsup (fun eps : Real =>
    if h : 0 < eps ∧ eps < 1 then
      let N := Metric.coveringNumber (NNReal.mk eps (le_of_lt h.1)) E
      if N = 0 then 0
      else if N.toNat = 0 then (Top.top : ENNReal)
      else ENNReal.ofReal (Real.log (N.toNat : Real) / Real.log (1/eps))
    else 0) (nhdsWithin (0 : Real) {x : ℝ | 0 < x})

-- Analysis 416: Lower Minkowski dimension

/-- Let E ⊆ X be a subset of a metric space X. For any ϵ>0 define the ϵ-covering number:
N_ϵ(E):=inf {n ∈ ℕ : E ⊂ ∪ᵢ₌₁ⁿ Bᵢ, ∀ i Bᵢ  is an open ball of radius  ϵ  }.
Note that when E is not bounded, the covering number is ∞ for all ϵ>0.

Then the lower Minkowski dimension of E is
liminf_{ϵ → 0} (log N_ϵ(E))/(log 1/ϵ)
-/
noncomputable def lowerMinkowskiDim (X : Type) [MetricSpace X] (E : Set X) : ENNReal :=
  Filter.liminf (fun eps : Real =>
    if h : 0 < eps ∧ eps < 1 then
      let N := Metric.coveringNumber (NNReal.mk eps (le_of_lt h.1)) E
      if N = 0 then 0
      else if N.toNat = 0 then (Top.top : ENNReal)
      else ENNReal.ofReal (Real.log (N.toNat : Real) / Real.log (1/eps))
    else 0) (nhdsWithin (0 : Real) {x : ℝ | 0 < x})

end MetaMathlibExt

end
