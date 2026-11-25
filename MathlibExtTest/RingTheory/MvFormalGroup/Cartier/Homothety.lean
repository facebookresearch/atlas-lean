/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvFormalGroup.Cartier.Homothety

@[expose] public noncomputable section

namespace CartierModuleHomothetyTest

open MvFormalGroup MvFormalGroup.CartierModule

universe u

variable {p : ℕ} [Fact p.Prime] {d : ℕ} {R : Type u} [CommRing R]

/-- Consumer with the original binders: homotheties are multiplicative. -/
theorem exactSource {Φ : MvFormalGroup d R} [Φ.IsComm] (a b : R) (f : CartierModule p Φ) :
    homothety (a * b) f = homothety a (homothety b f) :=
  homothety_mul a b f

/-- The homothety by `1` is the identity. -/
example {Φ : MvFormalGroup d R} [Φ.IsComm] (f : CartierModule p Φ) : homothety 1 f = f :=
  homothety_one f

end CartierModuleHomothetyTest
