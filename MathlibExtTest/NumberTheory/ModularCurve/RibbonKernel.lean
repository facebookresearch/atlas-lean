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

/-- The quotient graph of the integer path modulo translation by two has two vertices and two
edges. Read from its two edges oriented from the even vertex to the odd one (the two parallel edges
of `parallel`), `D.a` and `D.b` take values in disjoint sets of vertices, and the ribbon kernel is
the graph's rank-one cycle lattice, spanned by `(1, -1)`. -/
example : ribbonKernel parallel = Submodule.span ℤ {![1, -1]} := by
  apply le_antisymm
  · intro x hx
    have h0 := congrFun (mem_ribbonKernel.mp hx 0) 0
    simp [parallel, jointDelta, pushforward, degeneracyMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] at h0
    rw [Submodule.mem_span_singleton]
    exact ⟨x 0, by ext i; fin_cases i <;> simp; omega⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact diff_mem

/-- The four dart orbits of the integer path modulo translation by two, ordered by starting
parity: `0 → 1` and `0 → -1` start at the even vertex `0`, `1 → 2` and `1 → 0` at the odd vertex
`1`. Every width is `1`. -/
private def pathDarts : DegeneracyData (Fin 4) (Fin 2) where
  a := ![0, 0, 1, 1]
  b := ![1, 1, 0, 0]
  w _ := 1

/-- `(1, -1, 0, 0)` lies in the ribbon kernel of the four dart orbits. -/
private theorem pathDarts_mem₁ : (![1, -1, 0, 0] : Fin 4 → ℤ) ∈ ribbonKernel pathDarts := by
  rw [mem_ribbonKernel]
  intro i
  ext v
  fin_cases i <;> fin_cases v <;>
    simp [pathDarts, jointDelta, pushforward, degeneracyMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]

/-- `(0, 0, 1, -1)` lies in the ribbon kernel of the four dart orbits. -/
private theorem pathDarts_mem₂ : (![0, 0, 1, -1] : Fin 4 → ℤ) ∈ ribbonKernel pathDarts := by
  rw [mem_ribbonKernel]
  intro i
  ext v
  fin_cases i <;> fin_cases v <;>
    simp [pathDarts, jointDelta, pushforward, degeneracyMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]

/-- On all four dart orbits of the integer path modulo translation by two, the ribbon kernel has
rank two: it is spanned by the independent differences `(1, -1, 0, 0)` and `(0, 0, 1, -1)`, while
the quotient graph's cycle lattice has rank one. -/
example : ribbonKernel pathDarts = Submodule.span ℤ {![1, -1, 0, 0], ![0, 0, 1, -1]} ∧
    LinearIndependent ℤ ![(![1, -1, 0, 0] : Fin 4 → ℤ), ![0, 0, 1, -1]] := by
  refine ⟨le_antisymm (fun x hx => ?_) ?_, LinearIndependent.pair_iff.mpr fun s t h => ?_⟩
  · have h0 := congrFun (mem_ribbonKernel.mp hx 0) 0
    have h1 := congrFun (mem_ribbonKernel.mp hx 0) 1
    simp [pathDarts, jointDelta, pushforward, degeneracyMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four] at h0 h1
    exact Submodule.mem_span_pair.mpr ⟨x 0, x 2, by ext i; fin_cases i <;> simp <;> omega⟩
  · rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨pathDarts_mem₁, pathDarts_mem₂⟩
  · have h0 := congrFun h 0
    have h2 := congrFun h 2
    simp at h0 h2
    exact ⟨h0, h2⟩

/-- At unit widths, the Gram matrix of those two differences is `diag(2, 2)`. -/
example : ribbonGram pathDarts ⟨_, pathDarts_mem₁⟩ ⟨_, pathDarts_mem₁⟩ = 2 ∧
    ribbonGram pathDarts ⟨_, pathDarts_mem₁⟩ ⟨_, pathDarts_mem₂⟩ = 0 ∧
    ribbonGram pathDarts ⟨_, pathDarts_mem₂⟩ ⟨_, pathDarts_mem₂⟩ = 2 := by
  decide

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
