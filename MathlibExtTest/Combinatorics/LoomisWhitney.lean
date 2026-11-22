/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.LoomisWhitney

@[expose] public section

open Finset MathlibExt.Combinatorics.LoomisWhitney

namespace MathlibExtTest.Combinatorics.LoomisWhitney

/-- The cube `{0,1}³` has 8 points and three projections of 4 points: equality `8² = 4·4·4`. -/
example : (univ : Finset (Fin 2 × Fin 2 × Fin 2)).card ^ 2 =
    ((univ : Finset (Fin 2 × Fin 2 × Fin 2)).image projYZ).card *
      ((univ : Finset (Fin 2 × Fin 2 × Fin 2)).image projXZ).card *
      ((univ : Finset (Fin 2 × Fin 2 × Fin 2)).image projXY).card := by
  decide

/-- The inequality on the cube, from the general theorem. -/
example : (univ : Finset (Fin 2 × Fin 2 × Fin 2)).card ^ 2 ≤
    ((univ : Finset (Fin 2 × Fin 2 × Fin 2)).image projYZ).card *
      ((univ : Finset (Fin 2 × Fin 2 × Fin 2)).image projXZ).card *
      ((univ : Finset (Fin 2 × Fin 2 × Fin 2)).image projXY).card :=
  card_sq_le_card_mul_card_mul_card _

/-- A strict instance: the three points `(0,0,0)`, `(1,1,0)`, `(1,0,1)` have pairwise distinct
projections, so `3² = 9 < 27 = 3·3·3`. -/
example : ({(0, 0, 0), (1, 1, 0), (1, 0, 1)} : Finset (Fin 2 × Fin 2 × Fin 2)).card ^ 2 <
    (({(0, 0, 0), (1, 1, 0), (1, 0, 1)} : Finset (Fin 2 × Fin 2 × Fin 2)).image projYZ).card *
      (({(0, 0, 0), (1, 1, 0), (1, 0, 1)} : Finset (Fin 2 × Fin 2 × Fin 2)).image projXZ).card *
      (({(0, 0, 0), (1, 1, 0), (1, 0, 1)} : Finset (Fin 2 × Fin 2 × Fin 2)).image projXY).card := by
  decide

/-- The empty set: `0 ≤ 0`. -/
example : (∅ : Finset (ℕ × ℕ × ℕ)).card ^ 2 ≤
    ((∅ : Finset (ℕ × ℕ × ℕ)).image projYZ).card * ((∅ : Finset (ℕ × ℕ × ℕ)).image projXZ).card *
      ((∅ : Finset (ℕ × ℕ × ℕ)).image projXY).card :=
  card_sq_le_card_mul_card_mul_card _

end MathlibExtTest.Combinatorics.LoomisWhitney
