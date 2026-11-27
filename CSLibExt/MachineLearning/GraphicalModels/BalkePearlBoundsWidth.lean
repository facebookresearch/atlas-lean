/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.BalkePearlBounds
import Mathlib.Tactic.LinearCombination

/-!
# Balke–Pearl bounds: width at most the noncompliance rate

The first upper term minus the first lower term is the noncompliance rate, by normalization
of the observed law at each assignment. Taking the minimum of the upper terms and the maximum
of the lower terms can only narrow the interval.
-/

namespace WantedExt.Probability.Statistics.BalkePearlBoundsWanted

open Cslib.MachineLearning.GraphicalModels.BalkePearl

/-- **The width is at most the noncompliance rate.** For every
distribution `q` of the sixteen response types (a `TypeLaw`), the Balke–Pearl upper bound (5)
minus the lower bound (4), both computed from the observed law `q.obs`, is at most the
noncompliance rate `P(D = 1 | Z = 0) + P(D = 0 | Z = 1)
= p_{01.0} + p_{11.0} + p_{00.1} + p_{10.1}`, where `p_{yd.z} = q.obs y d z`.

Sources: A. Balke and J. Pearl, "Bounds on treatment effects from studies with imperfect
compliance", J. Amer. Statist. Assoc. 92 (1997) 1171–1176, p. 1173. -/
public theorem width_le_noncompliance (q : TypeLaw) :
    upperBound q.obs - lowerBound q.obs ≤
      q.obs false true false + q.obs true true false + q.obs false false true +
        q.obs true false true := by
  have hlo : lowerTerms q.obs 0 ≤ lowerBound q.obs :=
    Finset.le_sup' (lowerTerms q.obs) (Finset.mem_univ (0 : Fin 8))
  have hup : upperBound q.obs ≤ upperTerms q.obs 0 :=
    Finset.inf'_le (upperTerms q.obs) (Finset.mem_univ (0 : Fin 8))
  obtain ⟨-, hnormF, hnormT, -⟩ := obsForm_facts q.nonneg q.total_of_fintype
  calc
    upperBound q.obs - lowerBound q.obs ≤ upperTerms q.obs 0 - lowerTerms q.obs 0 :=
      sub_le_sub hup hlo
    _ = q.obs false true false + q.obs true true false + q.obs false false true +
        q.obs true false true := by
      change (1 - q.obs true false false - q.obs false true true) -
        (q.obs false false false + q.obs true true true - 1) = _
      simp only [TypeLaw.obs]
      linear_combination -hnormF - hnormT

end WantedExt.Probability.Statistics.BalkePearlBoundsWanted
