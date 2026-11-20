/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKQgt4SquareDualCoverageGeometry
import Code.FrontierD.FKQgt4SquareBoxClusterUnion
import Code.FK.PeriodicPlanarGraph

open Set SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation StatMech.Universality
open StatMech.FK.PeriodicPlanar

noncomputable section

private def squareDualBoundaryShift : Site 2 := ![1, 1]



theorem squareDualBoundaryShift_flankFaces_eq_sharedPrimalEdge
    {p q : Site 2} (hpq : (hypercubicLattice 2).Adj p q) :
    Sym2.map (square.shift squareDualBoundaryShift) (flankFaces p q) =
      sharedPrimalEdge p q := by
  rcases adj_cases hpq with ⟨h0, hpq1 | hqp1⟩ | ⟨h1, hpq0 | hqp0⟩
  · have hp : p = ![p 0, p 1] := by ext i; fin_cases i <;> simp
    have hq : q = ![p 0, p 1 - 1] := by
      ext i
      fin_cases i
      · simpa [h0]
      · simp; omega
    rw [hp, hq]
    simp [flankFaces, sharedPrimalEdge, squareDualBoundaryShift,
      square, siteTranslate, Sym2.map_mk]
  · have hp : p = ![p 0, p 1] := by ext i; fin_cases i <;> simp
    have hq : q = ![p 0, p 1 + 1] := by
      ext i
      fin_cases i
      · simpa [h0]
      · simp; omega
    rw [hp, hq]
    simp [flankFaces, sharedPrimalEdge, squareDualBoundaryShift,
      square, siteTranslate, Sym2.map_mk]
  · have hp : p = ![p 0, p 1] := by ext i; fin_cases i <;> simp
    have hq : q = ![p 0 - 1, p 1] := by
      ext i
      fin_cases i
      · simp; omega
      · simpa [h1]
    rw [hp, hq]
    simp [flankFaces, sharedPrimalEdge, squareDualBoundaryShift,
      square, siteTranslate, Sym2.map_mk,
      show p 0 ≠ p 0 - 1 by omega]
  · have hp : p = ![p 0, p 1] := by ext i; fin_cases i <;> simp
    have hq : q = ![p 0 + 1, p 1] := by
      ext i
      fin_cases i
      · simp; omega
      · simpa [h1]
    rw [hp, hq]
    simp [flankFaces, sharedPrimalEdge, squareDualBoundaryShift,
      square, siteTranslate, Sym2.map_mk]



theorem sharedPrimalEdge_open_of_faceDual_closed
    (omega : ConfigSpace (Sym2 (Site 2)))
    (K : Set (Site 2))
    (hclosed : ∀ {x y}, x ∈ K → (fci_faceOpenDual omega).Adj x y → y ∈ K)
    {x y : Site 2} (hxy : (hypercubicLattice 2).Adj x y)
    (hboundary : s(x, y) ∈ boundaryEdgeSet K) :
    omega (sharedPrimalEdge x y) = true := by
  have hstraddle : edgeStraddles K s(x, y) :=
    (edgeStraddles_iff_mem_boundaryEdgeSet K hxy).mpr hboundary
  rw [edgeStraddles_mk] at hstraddle
  cases hopen : omega (sharedPrimalEdge x y) with
  | false =>
      exfalso
      have hdual : (fci_faceOpenDual omega).Adj x y := ⟨hxy, hopen⟩
      by_cases hx : x ∈ K
      · exact (hstraddle.mp hx) (hclosed hx hdual)
      · have hy : y ∈ K := by
          by_contra hy
          exact hx (hstraddle.mpr hy)
        exact hx (hclosed hy hdual.symm)
  | true => rfl


theorem squareDualClusterCoverage_fill_closed
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Nat)
    (hfinite : ∀ x : Site 2,
      (cluster 2 (fci_faceDualConfig omega) x).Finite) :
    let S := squareDualClusterCoverage omega n
    let hS := squareDualClusterCoverage_finite omega n hfinite
    ∀ {x y}, x ∈ squareHoleFill S hS →
      (fci_faceOpenDual omega).Adj x y → y ∈ squareHoleFill S hS := by
  dsimp only
  exact squareHoleFill_closed_of_faceDual_closed omega _ _
    (squareDualClusterCoverage_closed omega n)



noncomputable def squareDualClusterCoverage_boundaryHom
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Nat)
    (hfinite : ∀ x : Site 2,
      (cluster 2 (fci_faceDualConfig omega) x).Finite) :
    let S := squareDualClusterCoverage omega n
    let hS := squareDualClusterCoverage_finite omega n hfinite
    faceBoundaryGraph (squareHoleFill S hS) →g openSubgraph 2 omega := by
  dsimp only
  let S := squareDualClusterCoverage omega n
  let hS : S.Finite := squareDualClusterCoverage_finite omega n hfinite
  let K := squareHoleFill S hS
  have hKclosed : ∀ {x y}, x ∈ K →
      (fci_faceOpenDual omega).Adj x y → y ∈ K :=
    squareHoleFill_closed_of_faceDual_closed omega S hS
      (squareDualClusterCoverage_closed omega n)
  refine
    { toFun := square.shift squareDualBoundaryShift
      map_rel' := ?_ }
  intro f g hfg
  have hlat : (hypercubicLattice 2).Adj
      (square.shift squareDualBoundaryShift f)
      (square.shift squareDualBoundaryShift g) :=
    (square.shift_adj squareDualBoundaryShift f g).2 hfg.1
  refine ⟨hlat, ?_⟩
  have hedge : symPrimalSym s(f, g) ∈ boundaryEdgeSet K :=
    symPrimalSym_mem_boundaryEdgeSet
      ((SimpleGraph.mem_edgeSet _).2 hfg)
  have hinverse : flankFacesSym (symPrimal f g) = s(f, g) :=
    flankFacesSym_symPrimal hfg.1
  rw [symPrimalSym_mk] at hedge
  generalize heq : symPrimal f g = e at hedge hinverse
  induction e using Sym2.inductionOn with
  | _ p q =>
      rw [flankFacesSym_mk] at hinverse
      have hpq : (hypercubicLattice 2).Adj p q :=
        (SimpleGraph.mem_edgeSet _).1 hedge.1
      have hopen := sharedPrimalEdge_open_of_faceDual_closed
        omega K hKclosed hpq hedge
      have hshift := squareDualBoundaryShift_flankFaces_eq_sharedPrimalEdge hpq
      rw [hinverse, Sym2.map_mk] at hshift
      rwa [hshift]

end

end StatMech.FrontierD
