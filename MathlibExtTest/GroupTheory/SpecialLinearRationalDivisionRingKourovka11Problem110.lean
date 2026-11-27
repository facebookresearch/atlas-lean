/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.SpecialLinearRationalDivisionRingKourovka11Problem110

@[expose] public section

namespace MathlibExt.GroupTheory.SpecialLinearRationalDivisionRingKourovka11Problem110Wanted

example : ¬ specialLinearRationalEmbedsInDivisionRing :=
  specialLinearRationalEmbedsInDivisionRing_refuted

example : specialLinearRationalEmbedsInDivisionRing ↔
    ∃ (D : Type) (_ : DivisionRing D)
      (f : Matrix.SpecialLinearGroup (Fin 2) ℚ →* Dˣ), Function.Injective f :=
  Iff.rfl

end MathlibExt.GroupTheory.SpecialLinearRationalDivisionRingKourovka11Problem110Wanted
