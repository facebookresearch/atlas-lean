/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWConnectorTwoChannelStoppedConditionalLaw

namespace StatMech.Universality

#print axioms rlc_twoChannelActiveEvent_preimage
#print axioms RlcTwoChannelCompatibleExteriorFibre.trace_le_frozenExterior
#print axioms RlcTwoChannelCompatibleExteriorFibre.separate_le_inducedWiring
#print axioms rlc_twoChannel_edgeSubsetFibreCondEventMass_ge_separate
#print axioms
  rlc_twoChannel_edgeSubsetFibreCondEventMass_ge_of_retainedAnchor_staticCut
#print axioms rlc_twoChannel_bcProb_fibre_ge_of_retainedAnchor_staticCut
#print axioms
  rlc_twoChannelOutsideEventMass_lower_of_retainedAnchor_staticCut
#print axioms
  rlc_finiteExtremalPairCandidate_dependsOnOutside_twoChannel
#print axioms
  rlc_finiteExtremalPairCandidate_twoChannelMass_lower_of_retainedAnchor_staticCut

end StatMech.Universality
