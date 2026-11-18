/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Engineering.Resource.PorousStorage

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum


/-!
# Tests for porous storage inventory

Pore volume 2 at phi = 1/4, V_bulk = 8; saturations (1/4, 3/4), densities (1, 2).
-/

namespace Engineering.Resource.PorousStorage.Tests

open Engineering.Resource.PorousStorage

-- phi = 1/4, V_bulk = 8: pore volume 2.
example : poreVolume (1 / 4) 8 = 2 := by
  simp only [poreVolume]
  norm_num

-- Saturations (1/4, 3/4) on Fin 2 fill it: phase volumes (1/2, 3/2).
example :
    ∑ i, phaseVolume (1 / 4) 8 ![1 / 4, 3 / 4] i = 2 := by
  simp only [phaseVolume, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

-- Phase masses for densities (1, 2) are (1/2, 3).
example : poreInventory (1 / 4) 8 ![1 / 4, 3 / 4] ![1, 2] 0 = 1 / 2 := by
  simp only [poreInventory, Matrix.cons_val_zero]
  norm_num

example : poreInventory (1 / 4) 8 ![1 / 4, 3 / 4] ![1, 2] 1 = 3 := by
  simp only [poreInventory, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

-- Endpoint saturations S = 0 and S = 1.
example : phaseVolume (1 / 4) 8 ![0, 1] 0 = 0 := by
  simp only [phaseVolume, Matrix.cons_val_zero]
  norm_num

example : phaseVolume (1 / 4) 8 ![0, 1] 1 = 2 := by
  simp only [phaseVolume, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

-- Saturations not summing to one do not fill the pore volume.
example :
    ∑ i, phaseVolume (1 / 4) 8 ![1 / 4, 1 / 4] i ≠ poreVolume (1 / 4) 8 := by
  simp only [phaseVolume, poreVolume, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

end Engineering.Resource.PorousStorage.Tests
