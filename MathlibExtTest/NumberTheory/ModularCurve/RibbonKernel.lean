/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularCurve.RibbonKernel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

open ModularCurve CerednikDrinfeld

/-- Consumer with the original binders: the ribbon kernel is characterized
by vanishing under both degeneracy pushforwards. -/
example {E V : Type*} [Fintype E] [DecidableEq V] (D : DegeneracyData E V)
    (x : E → ℤ) :
    x ∈ ribbonKernel D ↔ ∀ i, jointDelta D i x = 0 :=
  mem_ribbonKernel

/-- Two parallel edges from `0` to `1`, with widths `1` and `2`. -/
private def parallel : DegeneracyData (Fin 2) (Fin 2) where
  a _ := 0
  b _ := 1
  w := ![1, 2]

/-- Both degeneracy pushforwards add up the two edge values: the first at
vertex `0`, the second at vertex `1`. -/
example : jointDelta parallel 0 ![2, 5] = ![7, 0] ∧
    jointDelta parallel 1 ![2, 5] = ![0, 7] := by
  constructor <;> ext v <;> fin_cases v <;>
    simp [parallel, jointDelta, pushforward, degeneracyMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]

/-- The difference of the two edges lies in the ribbon kernel. -/
private theorem diff_mem : (![1, -1] : Fin 2 → ℤ) ∈ ribbonKernel parallel := by
  rw [mem_ribbonKernel]
  intro i
  ext v
  fin_cases i <;> fin_cases v <;>
    simp [parallel, jointDelta, pushforward, degeneracyMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]

/-- A single edge is not in the ribbon kernel. -/
example : (![1, 0] : Fin 2 → ℤ) ∉ ribbonKernel parallel := by
  rw [mem_ribbonKernel]
  intro h
  have h0 := congrFun (h 0) 0
  simp [parallel, jointDelta, pushforward, degeneracyMatrix, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two] at h0

/-- Edge `0` is a loop at vertex `0` and edge `1` runs from `0` to `1`, both of
width `1`: the two degeneracy maps differ. -/
private def loopAndEdge : DegeneracyData (Fin 2) (Fin 2) where
  a _ := 0
  b := ![0, 1]
  w _ := 1

/-- The ribbon kernel needs both pushforwards: `(1, -1)` is killed by the first
degeneracy pushforward of `loopAndEdge` but not by the second, so it is not in
the ribbon kernel. -/
example : pushforward loopAndEdge.a ![1, -1] = 0 ∧
    (![1, -1] : Fin 2 → ℤ) ∉ ribbonKernel loopAndEdge := by
  refine ⟨?_, fun h => ?_⟩
  · ext v
    fin_cases v <;>
      simp [loopAndEdge, pushforward, degeneracyMatrix, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two]
  · have h1 := congrFun (LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp h 1)) 1
    simp [loopAndEdge, jointDelta, pushforward, degeneracyMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two] at h1

/-- The ribbon kernel lies in the character lattice. -/
example : ribbonKernel parallel ≤ characterLattice (Fin 2) :=
  ribbonKernel_le_characterLattice parallel

/-- The Gram pairing weights the edges by their widths: the difference of the
two edges pairs with itself to `1 + 2 = 3`. -/
example : ribbonGram parallel ⟨_, diff_mem⟩ ⟨_, diff_mem⟩ = 3 := by
  decide

/-- The swap of the two edges. -/
private def swapMat : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

/-- The swap of the two parallel edges, with the identity on vertices, as
Hecke data with no bad prime. -/
private def swapHecke : HeckeData parallel where
  T _ := swapMat
  Tv _ := 1
  comm _ _ := Commute.refl _
  commv _ _ := Commute.refl _
  S := ∅
  good_equivariant _ _ i x := by
    ext v
    fin_cases i <;> fin_cases v <;>
      simp [parallel, swapMat, jointDelta, pushforward, degeneracyMatrix,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two, add_comm]
  kernel_stable _ x hx i := by
    have hx0 := congrFun (hx 0) 0
    have hx1 := congrFun (hx 1) 1
    simp [parallel, jointDelta, pushforward, degeneracyMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two] at hx0 hx1
    ext v
    fin_cases i <;> fin_cases v <;>
      simp [parallel, swapMat, jointDelta, pushforward, degeneracyMatrix,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> omega

/-- The prime `2`. -/
private def prime2 : Nat.Primes := ⟨2, Nat.prime_two⟩

/-- The swap acts on the ribbon kernel by `-1`: it sends the difference of the
edges to its negative. -/
example : heckeKernelMap swapHecke prime2 ⟨_, diff_mem⟩ = -⟨_, diff_mem⟩ := by
  apply Subtype.ext
  ext e
  fin_cases e <;>
    simp [heckeKernelMap, swapHecke, swapMat, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
