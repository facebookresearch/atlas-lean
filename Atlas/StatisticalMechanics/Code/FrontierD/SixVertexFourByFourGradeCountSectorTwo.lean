/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Code.FrontierD.SixVertexFourByFourGradeCountTable

namespace StatMech.FrontierD

set_option maxHeartbeats 0 in

set_option maxRecDepth 100000 in
theorem sixVertexFourByFourDynamicGradeCount_sectorTwo_certificate :
    ∀ totalC : Fin 17,
      sixVertexFourDynamicGradeCount sixVertexFourByFourSectorTwo totalC.val =
        sixVertexFourByFourGradeCountTable 2 totalC := by
  decide +revert

end StatMech.FrontierD
