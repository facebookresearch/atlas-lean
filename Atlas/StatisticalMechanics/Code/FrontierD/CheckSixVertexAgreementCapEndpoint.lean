/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierD.SixVertexAgreementCapEndpoint

open StatMech.FrontierD

#print axioms SixVertexDirectedTorusEdge.IsAgreement
#print axioms SixVertexDirectedSimpleArc.Follows
#print axioms SixVertexDirectedSimpleArc.IsAgreement
#print axioms sixVertexFourByTwo_agreement_followed_head
#print axioms SixVertexDirectedSimpleArc.agreement_tail_next
#print axioms sixVertexFourByTwo_agreementCap_hits_disagreementArcInterior
#print axioms sixVertexFourByTwo_no_internallyDisjointAgreementCap
