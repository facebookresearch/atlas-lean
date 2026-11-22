/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.IndependentIncrementsMarkovProperty

/-!
# Historical import for the independent-increments path identity

This module preserves the original source API of `BrownianMarkovProperty`.
Its declarations describe a time-dependent independent-increments identity.
The Lecture 37 Brownian/Wiener and right-continuous-filtration target remains deferred.
-/

@[expose] public section

namespace MathlibExt.Probability.BrownianMarkovProperty

export MathlibExt.Probability.IndependentIncrementsMarkovProperty (
  bmPrev
  bmInc
  bmShifted
  bmCenteredShift
  bmCenteredLaw
  bmPathExpectation
  BmAdapted
  BmIndepIncrements
  measurable_bmShifted
  measurable_bmCenteredShift
  bmCenteredLaw_isProbabilityMeasure
  measurable_bmInc_of_le
  bmPrev_insert_of_lt
  bmPrev_insert_self
  measure_inter_biInter_bmInc
  sum_bmInc_eq
  bmCentered_eq_sum_bmInc
  measurable_bmInc
  bmIncRectangles
  bmIncSigma
  measurableSet_bmInc_preimage
  measurable_bmInc_incSigma
  indep_bmIncSigma
  bmCenteredCylinders
  measurableSet_bmCentered_cylinder
  measurableSet_pi_eval_preimage
  indep_bmCenteredShift
  bmPathCylinders
  isPiSystem_bmPathCylinders
  pi_eq_generateFrom_bmPathCylinders
  bmCylRectangles
  isPiSystem_bmCylRectangles
  mem_generateFrom_bmCylRectangles
  prod_eq_generateFrom_bmCylRectangles
  bmPair
  bmPhi
  measurable_bmPair
  measurable_bmPhi
  bmPhi_bmPair
  measurable_section_bmCenteredLaw
  pair_section_rectangle
  pair_section_lintegral
  measurable_lintegral_bmPhi
  brownian_lintegral_shift
  measurable_bmPathExpectation
  bmPathExpectation_bound
  bmPathExpectation_setIntegral
  brownian_markov_setIntegral
  brownian_markov_condExp
)

end MathlibExt.Probability.BrownianMarkovProperty
