/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.Spectra.EilenbergMacLane
import MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.Spectra.Stabilization

/-!
# Free/evaluation and stabilization consumers for actual HR

These checks use the same HR as a sphere module, a commutative ring
spectrum and the target of a universal free-spectrum map. Stabilization
restricts a free map through the actual suspended level structure map.
-/

noncomputable section

open CategoryTheory MonoidalCategory
open MathlibExt.SpectraSource
open MathlibExt.SpectraSource.SymmetricSpectrum

example : IsCommMonObj (eilenbergMacLane ℤ) := inferInstance

example (n : ℕ) (K : PointedSSet.{0})
    (f : K ⟶ (evaluation n).obj (eilenbergMacLane ℤ)) :
    freeι n K ≫ (evaluation n).map (freeDesc (eilenbergMacLane ℤ) f) = f := by
  simp

example (n : ℕ) (K : PointedSSet.{0})
    (f : K ⟶ (evaluation n).obj (eilenbergMacLane ℤ)) :
    freeStabilizationMap n K ≫ freeDesc (eilenbergMacLane ℤ) f =
      freeDesc (eilenbergMacLane ℤ)
        (PointedSSet.circle ◁ f ≫ (eilenbergMacLane ℤ).smashPowStructureMap n) :=
  freeStabilizationMap_comp_freeDesc n (eilenbergMacLane ℤ) f

example (X : SymmetricSpectrum) : tensorLeft X ⊣ Mod.internalHom X :=
  Mod.internalHomAdjunction X
