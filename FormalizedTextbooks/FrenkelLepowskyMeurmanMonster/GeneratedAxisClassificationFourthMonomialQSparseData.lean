/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialQMatrixData

/-! Sparse exact evaluation of the genuine extraspecial binary and central matrices. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Nonzero original binary coefficients of each finite matrix row. -/
def generatedFourthMonomialQBinarySupports : Fin 4 → Fin 24 → Finset (Fin 24) :=
  ![
    ![
      {0, 6, 10},
      {1, 6, 10},
      {1, 4, 5, 7, 8, 9},
      {3, 6, 10},
      {4},
      {0, 4, 5, 6, 7},
      {0, 4, 7},
      {0, 4, 10},
      {0, 2, 3, 4, 6, 9, 10},
      {0, 1, 3, 5, 6, 7, 9, 10},
      {0, 4, 6, 7, 10},
      {0, 1, 2, 5, 6, 8, 9, 11},
      {3, 4, 8, 10, 12, 17, 18, 19, 20, 21, 22, 23},
      {2, 3, 8, 9, 13, 14, 21, 23},
      {1, 3, 6, 20, 23},
      {0, 1, 2, 4, 6, 7, 8, 9, 10, 15, 20, 21},
      {0, 3, 6, 8, 14, 16, 17, 18, 19, 20, 22},
      {6, 7, 14, 17, 21, 23},
      {2, 3, 4, 5, 12, 13, 15, 17, 20, 21, 22, 23},
      {3, 5, 8, 10, 14, 17, 18, 21, 22},
      {0, 1, 3, 4, 7, 14, 23},
      {1, 3, 10, 14, 20, 21, 23},
      {0, 3, 7, 9, 12, 13, 15, 19, 20, 21, 22},
      {23}
    ],
    ![
      {0, 4, 5, 10},
      {1},
      {3, 4, 6, 7, 9, 10},
      {2, 5, 6, 7, 8, 10},
      {5, 10},
      {4, 10},
      {7},
      {6},
      {9, 10},
      {8, 10},
      {10},
      {8, 9, 10, 11},
      {4, 5, 8, 9, 12},
      {8, 9, 10, 13},
      {4, 6, 7, 8, 15},
      {5, 6, 7, 9, 14},
      {0, 2, 7, 12, 14, 17},
      {0, 3, 6, 12, 15, 16},
      {2, 3, 5, 9, 10, 14, 15, 19},
      {2, 3, 4, 8, 10, 14, 15, 18},
      {0, 1, 2, 7, 10, 15, 21, 23},
      {0, 1, 3, 6, 10, 14, 20, 23},
      {1, 6, 7, 8, 9, 12, 14, 15, 16, 17, 20, 21, 22, 23},
      {23}
    ],
    ![
      {0},
      {0, 1, 2, 3, 9},
      {1, 4, 5, 6, 7, 8, 9, 10},
      {1, 4, 6, 8, 10},
      {0, 4, 5, 7},
      {5},
      {0, 5, 6},
      {7},
      {1, 2, 4, 5, 6, 9, 10},
      {2, 3, 5, 7},
      {0, 5, 7, 10},
      {11},
      {1, 7, 9, 10, 12, 13, 16, 18, 22},
      {0, 5, 7, 9, 13, 14, 15, 20},
      {5, 7, 8, 9, 13, 20, 21},
      {5, 7, 8, 13, 21},
      {9, 14, 15, 16, 20},
      {1, 2, 3, 8, 9, 10, 14, 16, 17, 18, 20, 21, 22},
      {9, 14, 15, 18, 20},
      {0, 1, 2, 3, 8, 10, 14, 16, 19, 21, 22},
      {2, 3, 5, 7, 14, 15},
      {0, 1, 2, 4, 5, 6, 10, 13, 14, 20},
      {0, 5, 7, 9, 14, 15, 20, 22},
      {23}
    ],
    ![
      {0, 4, 5, 10},
      {1, 4, 6, 8, 10},
      {2},
      {3, 5, 6, 8, 9, 10},
      {4, 10},
      {5, 10},
      {6},
      {7},
      {8, 10},
      {9},
      {10},
      {9, 10, 11},
      {4, 5, 9, 12},
      {4, 6, 8, 9, 13},
      {9, 10, 14},
      {5, 6, 8, 15},
      {0, 1, 7, 12, 13, 16},
      {0, 3, 6, 7, 12, 15, 17},
      {1, 3, 5, 8, 10, 13, 15, 18},
      {4, 5, 9, 19},
      {1, 3, 6, 13, 15, 20},
      {0, 1, 2, 7, 10, 15, 21, 23},
      {2, 6, 9, 12, 13, 15, 16, 17, 20, 22, 23},
      {23}
    ]
  ]

/-- Sparse binary evaluation is a genuine linear map on the entire actual quotient space. -/
def generatedFourthMonomialQBinaryLinear (k : Fin 4) :
    Module.End (ZMod 2) (Fin 24 → ZMod 2) where
  toFun v i := ∑ j ∈ generatedFourthMonomialQBinarySupports k i, v j
  map_add' u v := by
    funext i
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c v := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]

/-- Every sparse coefficient equals the certified original binary matrix coefficient. -/
theorem generatedFourth_monomial_q_binary_coefficients : ∀ k : Fin 4, ∀ i j : Fin 24,
    generatedFourthMonomialQBinaryLinear k (Pi.single j 1) i =
      generatedFourthMonomialQBinaryMatrix k i j := by
  decide +kernel

/-- Sparse binary evaluation agrees with the original matrix on every vector. -/
theorem generatedFourth_monomial_q_binary_linear (k : Fin 4) (v : Fin 24 → ZMod 2) :
    generatedFourthMonomialQBinaryMatrix k *ᵥ v = generatedFourthMonomialQBinaryLinear k v := by
  have h : Matrix.toLin' (generatedFourthMonomialQBinaryMatrix k) =
      generatedFourthMonomialQBinaryLinear k := by
    apply (Pi.basisFun (ZMod 2) (Fin 24)).ext
    intro j
    ext i
    simp only [Pi.basisFun_apply, Matrix.toLin'_apply, Matrix.mulVec_single_one,
      Matrix.col_apply]
    exact (generatedFourth_monomial_q_binary_coefficients k i j).symm
  exact DFunLike.congr_fun h v

/-- Literal original central coefficients for corrected monomial word 0. -/
def generatedFourthMonomialQPhaseLiteral0 :
    Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![
    ![1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  ]

/-- The same original central polynomial, summed only at its nonzero coefficients. -/
def generatedFourthMonomialQPhaseFast0 (v : Fin 24 → ZMod 2) : ZMod 2 :=
  v 0 * v 0 +
    v 0 * v 2 +
    v 0 * v 4 +
    v 0 * v 6 +
    v 0 * v 7 +
    v 0 * v 9 +
    v 0 * v 10 +
    v 1 * v 2 +
    v 1 * v 3 +
    v 1 * v 6 +
    v 1 * v 8 +
    v 1 * v 9 +
    v 1 * v 10 +
    v 2 * v 2 +
    v 2 * v 3 +
    v 2 * v 4 +
    v 2 * v 7 +
    v 3 * v 3 +
    v 3 * v 6 +
    v 3 * v 8 +
    v 3 * v 9 +
    v 4 * v 6 +
    v 4 * v 7 +
    v 4 * v 9 +
    v 4 * v 10 +
    v 5 * v 7 +
    v 5 * v 10 +
    v 6 * v 6 +
    v 6 * v 8 +
    v 6 * v 9 +
    v 6 * v 10 +
    v 7 * v 7 +
    v 7 * v 9 +
    v 7 * v 10 +
    v 8 * v 8 +
    v 9 * v 10 +
    v 10 * v 10 +
    v 12 * v 12 +
    v 19 * v 19 +
    v 20 * v 20

/-- Literal original central coefficients for corrected monomial word 1. -/
def generatedFourthMonomialQPhaseLiteral1 :
    Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![
    ![0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  ]

/-- The same original central polynomial, summed only at its nonzero coefficients. -/
def generatedFourthMonomialQPhaseFast1 (v : Fin 24 → ZMod 2) : ZMod 2 :=
  v 0 * v 4 +
    v 0 * v 5 +
    v 0 * v 8 +
    v 0 * v 9 +
    v 1 * v 8 +
    v 1 * v 9 +
    v 1 * v 10 +
    v 2 * v 2 +
    v 2 * v 5 +
    v 2 * v 6 +
    v 2 * v 7 +
    v 2 * v 9 +
    v 3 * v 4 +
    v 3 * v 6 +
    v 3 * v 7 +
    v 3 * v 8 +
    v 4 * v 5 +
    v 4 * v 7 +
    v 4 * v 9 +
    v 5 * v 5 +
    v 5 * v 6 +
    v 5 * v 8 +
    v 6 * v 9 +
    v 6 * v 10 +
    v 7 * v 8 +
    v 7 * v 10 +
    v 8 * v 9 +
    v 8 * v 10 +
    v 9 * v 9 +
    v 9 * v 10 +
    v 12 * v 12 +
    v 13 * v 13 +
    v 14 * v 14 +
    v 16 * v 16 +
    v 17 * v 17

/-- Literal original central coefficients for corrected monomial word 2. -/
def generatedFourthMonomialQPhaseLiteral2 :
    Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![
    ![1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  ]

/-- The same original central polynomial, summed only at its nonzero coefficients. -/
def generatedFourthMonomialQPhaseFast2 (v : Fin 24 → ZMod 2) : ZMod 2 :=
  v 0 * v 0 +
    v 0 * v 1 +
    v 0 * v 7 +
    v 0 * v 9 +
    v 0 * v 10 +
    v 1 * v 2 +
    v 1 * v 3 +
    v 2 * v 2 +
    v 2 * v 3 +
    v 2 * v 4 +
    v 2 * v 5 +
    v 2 * v 6 +
    v 2 * v 9 +
    v 2 * v 10 +
    v 3 * v 4 +
    v 3 * v 6 +
    v 3 * v 7 +
    v 3 * v 9 +
    v 3 * v 10 +
    v 4 * v 5 +
    v 4 * v 7 +
    v 5 * v 6 +
    v 5 * v 7 +
    v 5 * v 9 +
    v 6 * v 6 +
    v 6 * v 7 +
    v 7 * v 9 +
    v 8 * v 9 +
    v 9 * v 9 +
    v 13 * v 13 +
    v 20 * v 20

/-- Literal original central coefficients for corrected monomial word 3. -/
def generatedFourthMonomialQPhaseLiteral3 :
    Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![
    ![1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  ]

/-- The same original central polynomial, summed only at its nonzero coefficients. -/
def generatedFourthMonomialQPhaseFast3 (v : Fin 24 → ZMod 2) : ZMod 2 :=
  v 0 * v 0 +
    v 0 * v 4 +
    v 0 * v 5 +
    v 0 * v 9 +
    v 1 * v 1 +
    v 1 * v 4 +
    v 1 * v 6 +
    v 1 * v 8 +
    v 1 * v 9 +
    v 2 * v 2 +
    v 2 * v 9 +
    v 2 * v 10 +
    v 3 * v 3 +
    v 3 * v 5 +
    v 3 * v 6 +
    v 3 * v 8 +
    v 4 * v 5 +
    v 4 * v 6 +
    v 4 * v 7 +
    v 4 * v 8 +
    v 5 * v 5 +
    v 5 * v 7 +
    v 5 * v 8 +
    v 5 * v 9 +
    v 6 * v 6 +
    v 6 * v 8 +
    v 6 * v 9 +
    v 6 * v 10 +
    v 7 * v 7 +
    v 7 * v 9 +
    v 8 * v 8 +
    v 8 * v 9 +
    v 9 * v 9 +
    v 9 * v 10 +
    v 12 * v 12 +
    v 16 * v 16 +
    v 17 * v 17 +
    v 20 * v 20

/-- The four literal original central matrices. -/
def generatedFourthMonomialQPhaseLiteral : Fin 4 → Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  ![generatedFourthMonomialQPhaseLiteral0, generatedFourthMonomialQPhaseLiteral1,
    generatedFourthMonomialQPhaseLiteral2, generatedFourthMonomialQPhaseLiteral3]

/-- The four original central polynomials with zero coefficients omitted. -/
def generatedFourthMonomialQPhaseFast : Fin 4 → (Fin 24 → ZMod 2) → ZMod 2 :=
  ![generatedFourthMonomialQPhaseFast0, generatedFourthMonomialQPhaseFast1,
    generatedFourthMonomialQPhaseFast2, generatedFourthMonomialQPhaseFast3]

/-- All2304 literal central coefficients equal their original checked row masks. -/
theorem generatedFourth_monomial_q_phase_literals : ∀ k : Fin 4,
    generatedFourthMonomialQPhaseMatrix k = generatedFourthMonomialQPhaseLiteral k := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Expand only the four fixed24 by24 coefficient arrays and collect their nonzero terms.
/-- Sparse evaluation retains every original diagonal and off-diagonal central coefficient. -/
theorem generatedFourth_monomial_q_phase_fast (k : Fin 4) (v : Fin 24 → ZMod 2) :
    generatedFourthLiftQMatrixPhase (generatedFourthMonomialQPhaseMatrix k) v =
      generatedFourthMonomialQPhaseFast k v := by
  unfold generatedFourthLiftQMatrixPhase
  rw [generatedFourth_monomial_q_phase_literals]
  fin_cases k
  · simp [Matrix.toBilin'_apply, generatedFourthMonomialQPhaseLiteral,
      generatedFourthMonomialQPhaseLiteral0, generatedFourthMonomialQPhaseFast,
      generatedFourthMonomialQPhaseFast0, Fin.sum_univ_succ]
    ring
  · simp [Matrix.toBilin'_apply, generatedFourthMonomialQPhaseLiteral,
      generatedFourthMonomialQPhaseLiteral1, generatedFourthMonomialQPhaseFast,
      generatedFourthMonomialQPhaseFast1, Fin.sum_univ_succ]
    ring
  · simp [Matrix.toBilin'_apply, generatedFourthMonomialQPhaseLiteral,
      generatedFourthMonomialQPhaseLiteral2, generatedFourthMonomialQPhaseFast,
      generatedFourthMonomialQPhaseFast2, Fin.sum_univ_succ]
    ring
  · simp [Matrix.toBilin'_apply, generatedFourthMonomialQPhaseLiteral,
      generatedFourthMonomialQPhaseLiteral3, generatedFourthMonomialQPhaseFast,
      generatedFourthMonomialQPhaseFast3, Fin.sum_univ_succ]
    ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
