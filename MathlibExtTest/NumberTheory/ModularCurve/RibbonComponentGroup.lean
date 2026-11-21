/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularCurve.RibbonComponentGroup

open ModularCurve CerednikDrinfeld

/-- A concrete degeneracy datum: two edges over one vertex, of
width `1`. -/
def bananaData : DegeneracyData (Fin 2) (Fin 1) where
  a := fun _ => 0
  b := fun _ => 0
  w := fun _ => 1

/-- The ribbon kernel of the banana datum sits in the character
lattice. -/
example : ribbonKernel bananaData ≤ characterLattice (Fin 2) :=
  ribbonKernel_le_characterLattice bananaData

/-- Pushforward along the constant vertex map preserves degrees. -/
example (x : Fin 2 → ℤ) :
    degreeOn (Fin 1) (pushforward bananaData.a x) = degreeOn (Fin 2) x :=
  degreeOn_pushforward _ x

/-- The ribbon Gram pairing on the banana datum. -/
example (x y : ribbonKernel bananaData) :
    ribbonGram bananaData x y =
      ∑ e : Fin 2, (bananaData.w e : ℤ) * (x.1 e * y.1 e) :=
  ribbonGram_apply _ _ _

/-- The projection to the ribbon component group of the banana
datum. -/
example : Module.Dual ℤ ↥(ribbonKernel bananaData) →ₗ[ℤ]
    ribbonComponentGroup bananaData :=
  ribbonComponentGroupProj bananaData

/-- Membership in the ribbon kernel of the banana datum, unfolded. -/
example (x : Fin 2 → ℤ) :
    x ∈ ribbonKernel bananaData ↔
      ∀ i, jointDelta bananaData i x = 0 :=
  mem_ribbonKernel
