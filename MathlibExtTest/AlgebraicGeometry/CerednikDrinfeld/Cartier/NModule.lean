/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.CerednikDrinfeld.Cartier.NModule

@[expose] public noncomputable section

namespace CartierNModuleTest

open CerednikDrinfeld CerednikDrinfeld.CartierN

universe u

variable {M : Type u} [AddCommGroup M]

/-- Consumer with the original binders: `λ` sends the class of `(m, m')` to `Π m + V m'`. -/
theorem exactSource (V Pi : M →+ M) (h : Pi.comp V = V.comp Pi) (m m' : M) :
    lambda V Pi h (cls V Pi m m') = Pi m + V m' :=
  lambda_cls V Pi h m m'

/-- For `V = Π = 0` nothing is divided out, so `NMod` is `M × M` and `λ` is zero. -/
example (m m' : M) :
    lambda (0 : M →+ M) 0 rfl (cls 0 0 m m') = 0 := by
  simp

end CartierNModuleTest
