/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Parallel.CRCW

@[expose] public section

/-- The max of writes `0, 3, 1` over `Fin 3` is written by some processor. -/
example : ∃ i, crcwMax (fun i : Fin 3 => ![0, 3, 1] i) = (fun i : Fin 3 => ![0, 3, 1] i) i :=
  crcwMax_mem (by norm_num) _

/-- Every write is at most the resolved cell value. -/
example (i : Fin 3) : (fun i : Fin 3 => ![0, 3, 1] i) i ≤ crcwMax (fun i : Fin 3 => ![0, 3, 1] i) :=
  le_crcwMax _ i

end
