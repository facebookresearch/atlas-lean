/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularCurve.ComponentGroup

open ModularCurve

/-- A difference of unit vectors lies in the character lattice. -/
example : Pi.single (0 : Fin 2) (1 : ℤ) - Pi.single 1 1 ∈
    characterLattice (Fin 2) :=
  single_sub_single_mem (0 : Fin 2) 1

/-- The same difference is not detected by the degree: its degree
vanishes, while a single unit vector has degree `1`. -/
example : degreeOn (Fin 2) (Pi.single (0 : Fin 2) (1 : ℤ)) = 1 :=
  degreeOn_single (Fin 2) (0 : Fin 2) 1

/-- The width pairing on `Fin 2` with unit widths is the dot product. -/
example (D D' : Fin 2 → ℤ) :
    widthPairing (fun _ => 1) D D' = ∑ x : Fin 2, D x * D' x := by
  simp [widthPairing_apply]

/-- The component group and its projection for unit widths on
`Fin 2`. -/
example : Module.Dual ℤ (characterLattice (Fin 2)) →ₗ[ℤ]
    componentGroup (fun _ : Fin 2 => 1) :=
  componentGroupProj _

/-- A character evaluated at constant weights is trivial. -/
example (a : characterLattice (Fin 2)) (c : Multiplicative ℤ) :
    CharacterLattice.evalHom a (fun _ => c) = 1 :=
  CharacterLattice.evalHom_const a c

/-- Permuting by the swap equivalence preserves the character
lattice. -/
example (a : characterLattice (Fin 2)) :
    (CharacterLattice.permMap (Equiv.swap (0 : Fin 2) 1) a : Fin 2 → ℤ) 0 =
      (a : Fin 2 → ℤ) 1 := by
  simp
