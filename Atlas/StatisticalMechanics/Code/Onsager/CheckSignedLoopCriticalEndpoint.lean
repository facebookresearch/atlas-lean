/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.SignedLoopPhaseEndpoint

open StatMech Onsager

#print axioms summable_ons_rectDualPathCriticalCycleCoverTerm
#print axioms tsum_ons_rectDualPathCriticalCycleCoverTerm
#print axioms tsum_ons_rectDualPathCriticalNormalizedCycleCoverTerm
#print axioms norm_tsum_ons_rectDualPathCriticalNormalizedCycleCoverTerm_le_one
#print axioms ons_rectDualPathCriticalNormalizedCycleCover_tendsto_freeState
#print axioms ons_signedLoopPhaseWeight_eq_critical_iff
#print axioms freeState_eq_plusState_of_magnetization_eq_zero
#print axioms freeState_twoPoint_exponential_below_isingBetaC
#print axioms plusState_twoPoint_longRange_above_isingBetaC
#print axioms isingBetaC_two_eq_ons_betaC_of_dual_fixed
#print axioms signedLoop_physical_phase_threshold
