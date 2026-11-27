/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Product
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Instances.Matrix

/-!
# Continuous coefficient maps and product general linear groups

Let R,S be semirings with arbitrary topologies and I a finite index type in an independent
universe. Give finite matrices their coefficient product topologies and their general linear
groups the induced unit topologies. A continuous semiring homomorphism f:R→S induces the
continuous entrywise map GL(I,R)→GL(I,S). The coefficient product also gives a group
homeomorphism GL(I,R×S)≃GL(I,R)×GL(I,S).
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uI uR uS

variable {ι : Type uI} [Fintype ι] [DecidableEq ι]
variable {R : Type uR} {S : Type uS}
variable [Semiring R] [Semiring S]
variable [TopologicalSpace R] [TopologicalSpace S]
variable {f : R →+* S}

/-- **Continuity of a coefficient homomorphism on general linear groups.**

Let R,S be semirings with arbitrary topologies and I a finite index type in an independent
universe. Give finite matrices their coefficient product topologies and their general linear
groups the induced unit topologies. If f:R→S is a continuous semiring homomorphism, mapRingHom
f:GL(I,R)→GL(I,S), A↦(f(A(i,j)))_ij, is continuous.
-/
@[fun_prop]
theorem _root_.Continuous.generalLinearGroup_mapRingHom
    (hf : Continuous f) :
    Continuous (mapRingHom (n := ι) f) := by
  have hmatrix : Continuous (f.mapMatrix (m := ι)) := by
    change Continuous fun M : Matrix ι ι R => M.map f
    exact continuous_id.matrix_map hf
  change Continuous (Units.map (f.mapMatrix (m := ι)).toMonoidHom)
  exact Continuous.units_map _ hmatrix

/-- **General linear group over a product as a group homeomorphism.**

Let R,S be semirings with arbitrary topologies and I a finite index type in an independent
universe. Give finite matrices their coefficient product topologies and their general linear
groups the induced unit topologies. The continuous multiplicative equivalence
prodContinuousMulEquiv:GL(I,R×S)≃ₜ*GL(I,R)×GL(I,S) sends a matrix to its two coordinate
matrices, with continuous inverse given by entrywise pairing.
-/
def prodContinuousMulEquiv :
    GL ι (R × S) ≃ₜ* GL ι R × GL ι S := by
  let matrixEquiv :
      Matrix ι ι (R × S) ≃ₜ* Matrix ι ι R × Matrix ι ι S :=
    { __ := (Matrix.prodRingEquiv ι R S).toMulEquiv
      continuous_toFun := by
        change Continuous fun M : Matrix ι ι (R × S) =>
          (M.map (RingHom.fst R S), M.map (RingHom.snd R S))
        exact (continuous_id.matrix_map continuous_fst).prodMk
          (continuous_id.matrix_map continuous_snd)
      continuous_invFun := by
        change Continuous fun p : Matrix ι ι R × Matrix ι ι S =>
          (fun i j => (p.1 i j, p.2 i j))
        refine continuous_matrix fun i j => ?_
        exact ((continuous_apply_apply i j).comp continuous_fst).prodMk
          ((continuous_apply_apply i j).comp continuous_snd) }
  let productUnitsEquiv :
      (Matrix ι ι R × Matrix ι ι S)ˣ ≃ₜ* GL ι R × GL ι S :=
    { __ := MulEquiv.prodUnits
      continuous_toFun :=
        (Homeomorph.prodUnits
          (α := Matrix ι ι R) (β := Matrix ι ι S)).continuous
      continuous_invFun :=
        (Homeomorph.prodUnits
          (α := Matrix ι ι R) (β := Matrix ι ι S)).symm.continuous }
  exact (Units.mapContinuousMulEquiv matrixEquiv).trans productUnitsEquiv
end Matrix.GeneralLinearGroup
