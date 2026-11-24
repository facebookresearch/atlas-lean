/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Stabilization
public import Mathlib.Algebra.Group.Prod

/-!
# Coefficient naturality of the two-block general linear group map

The canonical blockDiagonalHom commutes with the original entrywise ring
map on both blocks. The two finite index universes and the two coefficient
universes are independent. Only semiring structures and a unital ring
homomorphism are used.
-/

namespace Matrix.GeneralLinearGroup

universe uN uM uR uS

variable {n : Type uN} {m : Type uM}
variable [DecidableEq n] [DecidableEq m] [Fintype n] [Fintype m]
variable {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]

/-- Mapping both diagonal blocks gives the entrywise image of their block matrix. -/
public theorem blockDiagonalHom_mapRingHom_apply (f : R →+* S)
    (g : GL n R) (h : GL m R) :
    blockDiagonalHom n m S (mapRingHom f g, mapRingHom f h) =
      mapRingHom (n := n ⊕ m) f (blockDiagonalHom n m R (g, h)) := by
  symm
  apply Units.ext
  simp only [coe_mapRingHom, coe_blockDiagonalHom, Matrix.fromBlocks_map]
  have h0nm : (0 : Matrix n m R).map f = 0 := by
    ext i j
    exact f.map_zero
  have h0mn : (0 : Matrix m n R).map f = 0 := by
    ext i j
    exact f.map_zero
  rw [h0nm, h0mn]

/-- The original two-block homomorphism is natural under a coefficient ring map. -/
public theorem blockDiagonalHom_mapRingHom (f : R →+* S) :
    (blockDiagonalHom n m S).comp
        ((mapRingHom (n := n) f).prodMap (mapRingHom (n := m) f)) =
      (mapRingHom (n := n ⊕ m) f).comp (blockDiagonalHom n m R) := by
  apply MonoidHom.ext
  rintro ⟨g, h⟩
  exact blockDiagonalHom_mapRingHom_apply f g h

end Matrix.GeneralLinearGroup
