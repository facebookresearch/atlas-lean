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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.StabilizeTo
import Mathlib.Topology.Algebra.Ring.Real

@[expose] public section

namespace MathlibExtTest.Matrix.GeneralLinearGroup.StabilizeTo

universe uR vR

private theorem literal_action
    (R : Type uR) [Semiring R] {n N : ℕ} (h : n ≤ N)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (↑(Matrix.GeneralLinearGroup.stabilizeTo R h g) :
        Matrix (Fin N) (Fin N) R) =
      Matrix.reindex
        (finCongr (Nat.add_sub_of_le h))
        (finCongr (Nat.add_sub_of_le h))
        (Matrix.reindex
          (finSumFinEquiv (m := n) (n := N - n))
          (finSumFinEquiv (m := n) (n := N - n))
          (Matrix.fromBlocks
            (↑g : Matrix (Fin n) (Fin n) R) 0 0 1)) :=
  Matrix.GeneralLinearGroup.coe_stabilizeTo R h g

private theorem cross_universe_naturality
    {R : Type uR} {S : Type vR} [Semiring R] [Semiring S]
    {n N : ℕ} (h : n ≤ N) (f : R →+* S)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    Matrix.GeneralLinearGroup.stabilizeTo S h
        (Matrix.GeneralLinearGroup.mapRingHom f g) =
      Matrix.GeneralLinearGroup.mapRingHom f
        (Matrix.GeneralLinearGroup.stabilizeTo R h g) :=
  DFunLike.congr_fun
    (Matrix.GeneralLinearGroup.stabilizeTo_mapRingHom h f) g

private theorem reflexive_coherence
    (R : Type uR) [Semiring R] (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    Matrix.GeneralLinearGroup.stabilizeTo R (le_refl n) g = g :=
  Matrix.GeneralLinearGroup.stabilizeTo_refl R n g

private theorem transitive_coherence
    (R : Type uR) [Semiring R] {n m N : ℕ}
    (hnm : n ≤ m) (hmN : m ≤ N)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    Matrix.GeneralLinearGroup.stabilizeTo R hmN
        (Matrix.GeneralLinearGroup.stabilizeTo R hnm g) =
      Matrix.GeneralLinearGroup.stabilizeTo R (hnm.trans hmN) g :=
  Matrix.GeneralLinearGroup.stabilizeTo_trans R hnm hmN g

private abbrev ZeroSemiring := Fin 0 → ℕ

private theorem zero_size_transitive
    (R : Type uR) [Semiring R] {m N : ℕ} (hmN : m ≤ N) :
    Matrix.GeneralLinearGroup.stabilizeTo R hmN
        (Matrix.GeneralLinearGroup.stabilizeTo R (Nat.zero_le m)
          (1 : Matrix.GeneralLinearGroup (Fin 0) R)) =
      Matrix.GeneralLinearGroup.stabilizeTo R (Nat.zero_le N) 1 :=
  Matrix.GeneralLinearGroup.stabilizeTo_trans R (Nat.zero_le m) hmN 1

private theorem zero_size_zero_ring (N : ℕ) :
    Matrix.GeneralLinearGroup.stabilizeTo ZeroSemiring (Nat.zero_le N)
        (1 : Matrix.GeneralLinearGroup (Fin 0) ZeroSemiring) = 1 :=
  map_one _

private theorem continuous_real {n N : ℕ} (h : n ≤ N) :
    Continuous (Matrix.GeneralLinearGroup.stabilizeTo ℝ h) :=
  Matrix.GeneralLinearGroup.continuous_stabilizeTo ℝ h

private theorem continuous_arbitrary_topology
    (R : Type uR) [Semiring R] [TopologicalSpace R]
    {n N : ℕ} (h : n ≤ N) :
    Continuous (Matrix.GeneralLinearGroup.stabilizeTo R h) :=
  Matrix.GeneralLinearGroup.continuous_stabilizeTo R h

end MathlibExtTest.Matrix.GeneralLinearGroup.StabilizeTo
