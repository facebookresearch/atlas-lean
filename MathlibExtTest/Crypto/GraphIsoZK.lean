/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Crypto.GraphIsoZK

@[expose] public section

/-- Relabeling by the identity permutation changes nothing. -/
example (G : Fin 2 → Fin 2 → Bool) : graphAct 1 G = G := by
  funext u v
  rfl

end
