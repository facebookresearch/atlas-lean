/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.MonotoneAutomatonNearestMeasurable

open MeasureTheory Set
open StatMech Lattice FrontierA

#check measurableSet_pairNearestHighSet
#check measurable_pairNearestHighSet_encard
#check measurableSet_pairNearestHighFinset
#check measurable_pairNearestTransport

#print axioms StatMech.FrontierA.measurableSet_pairNearestHighSet
#print axioms StatMech.FrontierA.measurable_pairNearestTransport
