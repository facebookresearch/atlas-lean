/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierD.SixVertexActiveKeyComponentRouting

namespace StatMech.FrontierD

#print axioms SixVertexHorizontalTwoCycleFiberReconnectionComponents.toEmbedding
#print axioms sixVertexHorizontalTwoCycleFiberReconnectionComponentsOfEmbedding
#print axioms
  SixVertexHorizontalTwoCycleActiveKeyComponentRouting.toActiveKeyFiberRouting
#print axioms activeKeyFiberRoutings_of_componentRoutings
#print axioms twoCycleKeyCapacityHall_of_activeKeyComponentRoutings
#print axioms
  SixVertexHorizontalTwoCycleTokenReconnectionComponents.toSupportedMatching
#print axioms offDiagonalTwoCycleMatching_of_tokenComponentRoutings
#print axioms
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_tokenComponentRoutings

end StatMech.FrontierD
