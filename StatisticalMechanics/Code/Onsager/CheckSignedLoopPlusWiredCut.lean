/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.SignedLoopPlusWiredCut

open StatMech Onsager

#print axioms ons_optionAnchoredEquiv_apply_vertexOfSite
#print axioms mem_plusWiredCut_iff
#print axioms ons_plusWiredCutLattice_eq_fvCutEdges
#print axioms card_plusWiredCut_eq_fvCutEdges
#print axioms ons_plusLowTempContourDenominator_eq_wired
#print axioms ons_plusWiredEndpointSign_eq_pathSign
#print axioms ons_plusLowTempPathNumerator_eq_wired
#print axioms integral_plusMeasure_twoPoint_eq_wiredCutRatio
