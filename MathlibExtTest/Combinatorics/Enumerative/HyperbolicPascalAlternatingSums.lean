/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.HyperbolicPascalAlternatingSums
import Mathlib.Tactic.NormNum

/-!
# Tests for weighted alternating row sums

Check the empty row, the interior step when both copy counts truncate to zero,
and the even and odd contributions of a three-entry row.
-/

namespace MetaMathlibExt.ghptRow_weighted_alternating_sum

example (q : ℕ) (α β : ℕ → ℂ) : ghptRow q α β 0 = [] := rfl

example : ghptInterior 2 [(0, 1), (1, 2), (2, 4), (0, 8)] =
    [(1, 3), (1, 6), (1, 12)] := rfl

example (q : ℕ) (v w : ℂ) :
    let r := (ghptRow q (fun n => (n : ℂ)) (fun n => 3 * n) 2).map Prod.snd
    (r.mapIdx fun i x => (if Even i then v else w) * x).sum = 8 * v + 4 * w := by
  dsimp only
  rw [(ghptRow_weighted_alternating_sum q 2 (fun n => (n : ℂ)) (fun n => 3 * n) v w).1]
  norm_num [ghptRow, ghptInterior, List.mapIdx_cons]

end MetaMathlibExt.ghptRow_weighted_alternating_sum
