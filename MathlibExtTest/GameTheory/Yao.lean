/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.Yao

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

@[expose] public section

open MathlibExt.GameTheory.Yao

/-- Algorithms (`Fin 2`) and inputs (`Bool`) have distinct types, so the input
weights `q` must be indexed by inputs. -/
example (C : Fin 2 → Bool → ℚ) (q : Bool → ℚ) :
    ∃ a, (∑ y, q y * C a y) ≤ ∑ a', (1 / 2 : ℚ) * (∑ y, q y * C a' y) :=
  yao_exists_det C (fun _ => 1 / 2) q (fun _ => by norm_num)
    (by norm_num [Fin.sum_univ_two])

/-- Input side, with distinct algorithm (`Fin 2`) and input (`Bool`) types. -/
example (C : Fin 2 → Bool → ℚ) (p : Fin 2 → ℚ) :
    ∃ y, (∑ a, p a * C a y) ≥ ∑ y', (1 / 2 : ℚ) * (∑ a, p a * C a y') :=
  yao_exists_input C p (fun _ => 1 / 2) (fun _ => by norm_num)
    (by norm_num [Fintype.sum_bool])

end
