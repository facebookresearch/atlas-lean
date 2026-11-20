/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Code.FrontierD.SixVertexFourByFourDynamicCount

namespace StatMech.FrontierD

def sixVertexFourByFourGradeCountTable : Fin 5 → Fin 17 → Nat := ![
  ![16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![64, 0, 0, 0, 288, 0, 192, 0, 84, 0, 0, 0, 0, 0, 0, 0, 0],
  ![96, 0, 0, 0, 576, 0, 384, 0, 528, 0, 64, 0, 32, 0, 0, 0, 2],
  ![64, 0, 0, 0, 288, 0, 192, 0, 84, 0, 0, 0, 0, 0, 0, 0, 0],
  ![16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
]

end StatMech.FrontierD
