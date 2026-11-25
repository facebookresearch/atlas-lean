/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.GijswijtBlockWordCurlingNumber

open MetaMathlibExt

-- Two copies of the first block of the second-order sequence have curling number two,
-- with the maximal exponent attained at the first block.
example : curlingNumber (gijswijtBlockWord 2 2 (fun _ => 2)) = 2 :=
  curlingNumber_blockWord_of_max (m := 1) (u := 2) (a := fun _ => 2) (by decide)
    (by decide) (fun _ _ _ => by decide) ⟨1, by decide, by decide, rfl⟩

-- Three copies of the first block of the third-order sequence have curling number
-- three, with the maximal exponent attained at the first block.
example : curlingNumber (gijswijtBlockWord 3 2 (fun _ => 3)) = 3 :=
  curlingNumber_blockWord_of_max (m := 2) (u := 2) (a := fun _ => 3) (by decide)
    (by decide) (fun _ _ _ => by decide) ⟨1, by decide, by decide, rfl⟩

-- The maximal exponent is attained at the second block: the word is two copies of
-- the second block followed by no copies of the first, and its curling number is two.
example :
    curlingNumber (gijswijtBlockWord 2 3 (fun i => if i = 2 then 2 else 0)) = 2 :=
  curlingNumber_blockWord_of_max (m := 1) (u := 3) (a := fun i => if i = 2 then 2 else 0)
    (by decide) (by decide) (by intro i _ _; split <;> omega)
    ⟨2, by decide, by decide, by simp⟩
