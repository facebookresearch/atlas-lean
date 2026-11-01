/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2RealRoots

/-! Exact physical-coordinate matrices checked against every original signed E8 root action. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators

/-- Twice each of the eighteen original generators in physical coordinates on octad 2052. -/
def generatedTwelfthSectionGeneratorTwice :
    Fin 18 → Matrix (Fin 8) (Fin 8) ℤ := ![
  ![
    ![2, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 0, 0, 0, 0, 0],
    ![0, 0, 0, 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, -2, 0, 0, 0],
    ![0, 0, 0, 0, 0, -2, 0, 0],
    ![0, 0, 0, 0, 0, 0, -2, 0],
    ![0, 0, 0, 0, 0, 0, 0, -2]
  ],
  ![
    ![2, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 0, 0, 0, 0, 0],
    ![0, 0, 0, 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, -2, 0, 0, 0],
    ![0, 0, 0, 0, 0, -2, 0, 0],
    ![0, 0, 0, 0, 0, 0, -2, 0],
    ![0, 0, 0, 0, 0, 0, 0, -2]
  ],
  ![
    ![2, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 0, 0, 0, 0, 0],
    ![0, 0, 0, 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 2, 0, 0, 0],
    ![0, 0, 0, 0, 0, 2, 0, 0],
    ![0, 0, 0, 0, 0, 0, 2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 2]
  ],
  ![
    ![2, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 0, 0, 0, 0, 0],
    ![0, 0, 0, 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, -2, 0, 0, 0],
    ![0, 0, 0, 0, 0, -2, 0, 0],
    ![0, 0, 0, 0, 0, 0, -2, 0],
    ![0, 0, 0, 0, 0, 0, 0, -2]
  ],
  ![
    ![2, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 0, 0, 0, 0, 0],
    ![0, 0, 0, 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 2, 0, 0, 0],
    ![0, 0, 0, 0, 0, 2, 0, 0],
    ![0, 0, 0, 0, 0, 0, -2, 0],
    ![0, 0, 0, 0, 0, 0, 0, -2]
  ],
  ![
    ![2, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 0, 0, 0, 0, 0],
    ![0, 0, 0, 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 2, 0, 0, 0],
    ![0, 0, 0, 0, 0, -2, 0, 0],
    ![0, 0, 0, 0, 0, 0, 2, 0],
    ![0, 0, 0, 0, 0, 0, 0, -2]
  ],
  ![
    ![2, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 0, 0, 0, 0, 0],
    ![0, 0, 0, 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 2, 0, 0, 0],
    ![0, 0, 0, 0, 0, -2, 0, 0],
    ![0, 0, 0, 0, 0, 0, 2, 0],
    ![0, 0, 0, 0, 0, 0, 0, -2]
  ],
  ![
    ![2, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 0, 0, 0, 0, 0],
    ![0, 0, 0, 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 2, 0, 0, 0],
    ![0, 0, 0, 0, 0, -2, 0, 0],
    ![0, 0, 0, 0, 0, 0, -2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 2]
  ],
  ![
    ![2, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2, 0, 0, 0, 0, 0, 0],
    ![0, 0, -2, 0, 0, 0, 0, 0],
    ![0, 0, 0, -2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 2, 0, 0, 0],
    ![0, 0, 0, 0, 0, -2, 0, 0],
    ![0, 0, 0, 0, 0, 0, -2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 2]
  ],
  ![
    ![2, 0, 0, 0, 0, 0, 0, 0],
    ![0, -2, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 0, 0, 0, 0, 0],
    ![0, 0, 0, -2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 2, 0, 0, 0],
    ![0, 0, 0, 0, 0, 2, 0, 0],
    ![0, 0, 0, 0, 0, 0, -2, 0],
    ![0, 0, 0, 0, 0, 0, 0, -2]
  ],
  ![
    ![2, 0, 0, 0, 0, 0, 0, 0],
    ![0, -2, 0, 0, 0, 0, 0, 0],
    ![0, 0, -2, 0, 0, 0, 0, 0],
    ![0, 0, 0, -2, 0, 0, 0, 0],
    ![0, 0, 0, 0, -2, 0, 0, 0],
    ![0, 0, 0, 0, 0, 2, 0, 0],
    ![0, 0, 0, 0, 0, 0, 2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 2]
  ],
  ![
    ![-2, 0, 0, 0, 0, 0, 0, 0],
    ![0, -2, 0, 0, 0, 0, 0, 0],
    ![0, 0, -2, 0, 0, 0, 0, 0],
    ![0, 0, 0, -2, 0, 0, 0, 0],
    ![0, 0, 0, 0, -2, 0, 0, 0],
    ![0, 0, 0, 0, 0, -2, 0, 0],
    ![0, 0, 0, 0, 0, 0, -2, 0],
    ![0, 0, 0, 0, 0, 0, 0, -2]
  ],
  ![
    ![0, 0, 0, 0, 0, 0, 2, 0],
    ![0, 2, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 2],
    ![0, 0, 0, 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 2, 0, 0, 0],
    ![0, 0, 0, 0, 0, 2, 0, 0],
    ![2, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 0, 0, 0, 0, 0]
  ],
  ![
    ![2, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 0, 0, 0, 0, 0],
    ![0, 2, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 2, 0, 0],
    ![0, 0, 0, 0, 2, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 2]
  ],
  ![
    ![0, 0, 2, 0, 0, 0, 0, 0],
    ![0, 0, 0, 2, 0, 0, 0, 0],
    ![2, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 2, 0, 0, 0],
    ![0, 0, 0, 0, 0, 2, 0, 0],
    ![0, 0, 0, 0, 0, 0, 2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 2]
  ],
  ![
    ![2, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 2, 0],
    ![0, 0, 0, 0, 0, 2, 0, 0],
    ![0, 0, 0, 0, 2, 0, 0, 0],
    ![0, 0, 0, 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 2]
  ],
  ![
    ![0, 0, 0, 0, 0, 2, 0, 0],
    ![2, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 2],
    ![0, 0, 0, 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 2, 0, 0, 0],
    ![0, 2, 0, 0, 0, 0, 0, 0]
  ],
  ![
    ![-1, 1, 1, 1, 0, 0, 0, 0],
    ![-1, 1, -1, -1, 0, 0, 0, 0],
    ![-1, -1, 1, -1, 0, 0, 0, 0],
    ![-1, -1, -1, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, -1, 1, 1, 1],
    ![0, 0, 0, 0, -1, 1, -1, -1],
    ![0, 0, 0, 0, -1, -1, 1, -1],
    ![0, 0, 0, 0, -1, -1, -1, 1]
  ]
]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 64000000 in
-- Every source row is checked against the frozen original root-action catalogue.
/-- The physical matrices agree with all 120 signed original source-root images. -/
theorem generatedTwelfthSectionGenerator_root_source :
    ∀ (g : Fin 18) (r : Fin 120),
      generatedTwelfthSectionGeneratorTwice g *ᵥ leechSeventhE8RootLocal r =
        (2 * leechSeventhE8RootImageSign g r) •
          leechSeventhE8RootLocal (leechSeventhE8RootImage g r) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
-- Every full integer orthogonality identity is checked, independently of root multiplicities.
/-- These original physical matrices are twice orthogonal matrices. -/
theorem generatedTwelfthSectionGenerator_orthogonal :
    ∀ g : Fin 18, generatedTwelfthSectionGeneratorTwice g *
      (generatedTwelfthSectionGeneratorTwice g).transpose = (4 : ℕ) • 1 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
