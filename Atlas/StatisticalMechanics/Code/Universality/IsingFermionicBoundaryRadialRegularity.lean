/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalBoundaryAverage
import Code.Universality.IsingFermionicEndpointPointwise









namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section



theorem fkIsingSquareBoundaryRadialPatchFullObservable_quad
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (heven : Even (i + j)) :
    IsingSquareSHolomorphicQuad
      (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
        ⟨i - 1, by omega⟩ ⟨j, by omega⟩)
      (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
        ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩)
      (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
        ⟨i, by omega⟩ ⟨j - 1, by omega⟩)
      (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
        ⟨i, by omega⟩ ⟨j, by omega⟩) := by
  let ii : Fin m := ⟨i, by omega⟩
  let jj : Fin m := ⟨j, by omega⟩
  let x := fkIsingSquareRadialPatchVertex n m hm ii jj
  have heast : fkIsingSquareDirectionAvailable n x .east := by
    simpa [x, ii, jj, fkIsingSquareRadialPatchDirection, heven] using
      fkIsingSquareRadialPatchDirection_available n m hm ii jj
  have hnorth : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, ii, jj, fkIsingSquareDirectionAvailable,
      fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf_eq]
    have hmod := Nat.even_iff.mp heven
    omega
  have hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, ii, jj, fkIsingSquareDirectionAvailable,
      fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf_eq]
    have hmod := Nat.even_iff.mp heven
    omega
  have hsouth : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, ii, jj, fkIsingSquareDirectionAvailable,
      fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf_eq]
    have hmod := Nat.even_iff.mp heven
    omega
  have hquad := fkIsingSquareBoundaryFullVertexFullObservable_quad
    n hn x heast hnorth hwest hsouth
  change IsingSquareSHolomorphicQuad
    (fkIsingSquareBoundaryFullMedialObservable n hn
      (fkIsingSquareDirectionEdge n x .south hsouth))
    (fkIsingSquareBoundaryFullMedialObservable n hn
      (fkIsingSquareDirectionEdge n x .west hwest))
    (fkIsingSquareBoundaryFullMedialObservable n hn
      (fkIsingSquareDirectionEdge n x .north hnorth))
    (fkIsingSquareBoundaryFullMedialObservable n hn
      (fkIsingSquareDirectionEdge n x .east heast)) at hquad
  have hoddS : ¬ Even (i - 1 + j) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hS : fkIsingSquareRadialPatchEdge n m hm
        ⟨i - 1, by omega⟩ ⟨j, by omega⟩ =
      fkIsingSquareDirectionEdge n x .south hsouth := by
    rw [fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ hoddS]
    apply Subtype.ext
    simp only [fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [x, ii, jj, fkIsingSquareRadialPatchVertex,
        fkIsingSquareRadialPatchHalf_eq, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.even_iff.mp heven <;> omega
  have hevenW : Even (i - 1 + (j - 1)) := by
    rw [Nat.even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hW : fkIsingSquareRadialPatchEdge n m hm
        ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ =
      fkIsingSquareDirectionEdge n x .west hwest := by
    rw [fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ hevenW]
    apply Subtype.ext
    simp only [fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [x, ii, jj, fkIsingSquareRadialPatchVertex,
        fkIsingSquareRadialPatchHalf_eq, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.even_iff.mp heven <;> omega
  have hoddN : ¬ Even (i + (j - 1)) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hN : fkIsingSquareRadialPatchEdge n m hm
        ⟨i, by omega⟩ ⟨j - 1, by omega⟩ =
      fkIsingSquareDirectionEdge n x .north hnorth := by
    rw [fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ hoddN]
    apply Subtype.ext
    simp only [fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    left
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [x, ii, jj, fkIsingSquareRadialPatchVertex,
        fkIsingSquareRadialPatchHalf_eq, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.even_iff.mp heven <;> omega
  have hE : fkIsingSquareRadialPatchEdge n m hm
        ⟨i, by omega⟩ ⟨j, by omega⟩ =
      fkIsingSquareDirectionEdge n x .east heast := by
    rw [fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ heven]
  simpa only [fkIsingSquareBoundaryRadialPatchFullObservable,
    hS, hW, hN, hE] using hquad



theorem fkIsingSquareBoundaryRadialPatchFullObservable_quad_of_odd
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (hodd : ¬ Even (i + j)) :
    IsingSquareSHolomorphicQuad
      (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
        ⟨i, by omega⟩ ⟨j - 1, by omega⟩)
      (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
        ⟨i, by omega⟩ ⟨j, by omega⟩)
      (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
        ⟨i - 1, by omega⟩ ⟨j, by omega⟩)
      (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
        ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩) := by
  let p : FKIsingSquareRadialPatchDualNode m :=
    ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), hodd⟩
  let c := fkIsingSquareRadialPatchDualFullFace n m hm (by omega) p
  have hevenN : Even (i + (j - 1)) := by
    rw [Nat.even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hN : fkIsingSquareRadialPatchEdge n m hm
        ⟨i, by omega⟩ ⟨j - 1, by omega⟩ = faceNorthEdge n c := by
    rw [fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ hevenN]
    apply Subtype.ext
    simp only [faceNorthEdge, fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    left
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [c, p, faceNWVertex, fkIsingSquareRadialPatchVertex,
        fkIsingSquareRadialPatchHalf_eq, fkIsingSquareInteriorCellKey,
        fkIsingSquareRadialPatchDualFullFace, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.not_even_iff.mp hodd <;> omega
  have hE : fkIsingSquareRadialPatchEdge n m hm
        ⟨i, by omega⟩ ⟨j, by omega⟩ = faceEastEdge n c := by
    rw [fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ hodd]
    apply Subtype.ext
    simp only [faceEastEdge, fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    left
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [c, p, faceSEVertex, fkIsingSquareRadialPatchVertex,
        fkIsingSquareRadialPatchHalf_eq, fkIsingSquareInteriorCellKey,
        fkIsingSquareRadialPatchDualFullFace, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.not_even_iff.mp hodd <;> omega
  have hevenS : Even (i - 1 + j) := by
    rw [Nat.even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hS : fkIsingSquareRadialPatchEdge n m hm
        ⟨i - 1, by omega⟩ ⟨j, by omega⟩ = faceSouthEdge n c := by
    rw [fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ hevenS]
    apply Subtype.ext
    simp only [faceSouthEdge, fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    left
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [c, p, faceSWVertex, fkIsingSquareRadialPatchVertex,
        fkIsingSquareRadialPatchHalf_eq, fkIsingSquareInteriorCellKey,
        fkIsingSquareRadialPatchDualFullFace, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.not_even_iff.mp hodd <;> omega
  have hoddW : ¬ Even (i - 1 + (j - 1)) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hW : fkIsingSquareRadialPatchEdge n m hm
        ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ = faceWestEdge n c := by
    rw [fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ hoddW]
    apply Subtype.ext
    simp only [faceWestEdge, fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    left
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [c, p, faceSWVertex, fkIsingSquareRadialPatchVertex,
        fkIsingSquareRadialPatchHalf_eq, fkIsingSquareInteriorCellKey,
        fkIsingSquareRadialPatchDualFullFace, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.not_even_iff.mp hodd <;> omega
  have hnotN : (faceNorthEdge n c).1 ∉
      fkIsingSquarePerimeterPrimalEdgeFinset n := by
    rw [← hN]
    exact fkIsingSquareRadialPatchEdge_not_mem_perimeter
      n m hm ⟨i, by omega⟩ ⟨j - 1, by omega⟩
  have hnotE : (faceEastEdge n c).1 ∉
      fkIsingSquarePerimeterPrimalEdgeFinset n := by
    rw [← hE]
    exact fkIsingSquareRadialPatchEdge_not_mem_perimeter
      n m hm ⟨i, by omega⟩ ⟨j, by omega⟩
  have hnotS : (faceSouthEdge n c).1 ∉
      fkIsingSquarePerimeterPrimalEdgeFinset n := by
    rw [← hS]
    exact fkIsingSquareRadialPatchEdge_not_mem_perimeter
      n m hm ⟨i - 1, by omega⟩ ⟨j, by omega⟩
  have hnotW : (faceWestEdge n c).1 ∉
      fkIsingSquarePerimeterPrimalEdgeFinset n := by
    rw [← hW]
    exact fkIsingSquareRadialPatchEdge_not_mem_perimeter
      n m hm ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
  have hquad := fkIsingSquareBoundaryFullFaceFullObservable_quad
    n hn c hnotN hnotE hnotS hnotW
  unfold fkIsingSquareBoundaryRadialPatchFullObservable
  rw [hN, hE, hS, hW]
  exact hquad


noncomputable def fkIsingSquareBoundaryRadialPatchFullObservableExtension
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) : Nat → Nat → Complex :=
  fun i j ↦
    if hi : i < m then
      if hj : j < m then
        fkIsingSquareBoundaryRadialPatchFullObservable
          n m hn hm ⟨i, hi⟩ ⟨j, hj⟩
      else 0
    else 0

@[simp] theorem fkIsingSquareBoundaryRadialPatchFullObservableExtension_apply
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (i j : Nat) (hi : i < m) (hj : j < m) :
    fkIsingSquareBoundaryRadialPatchFullObservableExtension n m hn hm i j =
      fkIsingSquareBoundaryRadialPatchFullObservable
        n m hn hm ⟨i, hi⟩ ⟨j, hj⟩ := by
  simp [fkIsingSquareBoundaryRadialPatchFullObservableExtension, hi, hj]


theorem fkIsingSquareBoundaryRadialPatchFullObservable_cellCR
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hi : i + 2 < m) (hj : j + 2 < m) :
    IsingCellCRAt
      (fkIsingSquareBoundaryRadialPatchFullObservableExtension n m hn hm) i j := by
  by_cases heven : Even (i + 1 + (j + 1))
  · have hquad := fkIsingSquareBoundaryRadialPatchFullObservable_quad
      n m (i + 1) (j + 1) hn hm (by omega) (by omega)
      (by omega) (by omega) heven
    unfold IsingCellCRAt
      fkIsingSquareBoundaryRadialPatchFullObservableExtension
    simp [show i < m by omega, show i + 1 < m by omega,
      show j < m by omega, show j + 1 < m by omega]
    simpa using hquad.2.2
  · have hquad := fkIsingSquareBoundaryRadialPatchFullObservable_quad_of_odd
      n m (i + 1) (j + 1) hn hm (by omega) (by omega)
      (by omega) (by omega) heven
    unfold IsingCellCRAt
      fkIsingSquareBoundaryRadialPatchFullObservableExtension
    simp [show i < m by omega, show i + 1 < m by omega,
      show j < m by omega, show j + 1 < m by omega]
    have h := hquad.2.2
    simp only [Nat.add_sub_cancel] at h
    linear_combination -h


theorem fkIsingSquareBoundaryRadialPatchFullObservable_leapfrog_harmonic
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hi : i + 3 < m) (hj : j + 3 < m) :
    fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨i, by omega⟩ ⟨j, by omega⟩ +
        fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨i, by omega⟩ ⟨j + 2, by omega⟩ +
        fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨i + 2, by omega⟩ ⟨j, by omega⟩ +
        fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨i + 2, by omega⟩ ⟨j + 2, by omega⟩ =
      4 * fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
        ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ := by
  have hSW := fkIsingSquareBoundaryRadialPatchFullObservable_cellCR
    n m i j hn hm (by omega) (by omega)
  have hSE := fkIsingSquareBoundaryRadialPatchFullObservable_cellCR
    n m (i + 1) j hn hm (by omega) (by omega)
  have hNW := fkIsingSquareBoundaryRadialPatchFullObservable_cellCR
    n m i (j + 1) hn hm (by omega) (by omega)
  have hNE := fkIsingSquareBoundaryRadialPatchFullObservable_cellCR
    n m (i + 1) (j + 1) hn hm (by omega) (by omega)
  have h := isingCellCRAt_leapfrog_harmonic
    (fkIsingSquareBoundaryRadialPatchFullObservableExtension n m hn hm)
    i j hSW hSE hNW hNE
  simpa [fkIsingSquareBoundaryRadialPatchFullObservableExtension,
    show i < m by omega, show j < m by omega,
    show i + 1 < m by omega, show j + 1 < m by omega,
    show i + 2 < m by omega, show j + 2 < m by omega] using h


noncomputable def fkIsingSquareBoundaryRadialPatchFullObservableWindow
    (n m baseI baseJ R : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m) :
    IsingLeapfrogBox R → Complex :=
  fun p ↦ fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
    ⟨baseI + p.1.1, by have := p.1.2; omega⟩
    ⟨baseJ + p.2.1, by have := p.2.2; omega⟩


theorem fkIsingSquareBoundaryRadialPatchFullObservableWindow_harmonic
    (n m baseI baseJ R : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m) :
    IsingLeapfrogHarmonicOnBox R
      (fkIsingSquareBoundaryRadialPatchFullObservableWindow
        n m baseI baseJ R hn hm hfitI hfitJ) := by
  intro p hp
  have hx0 : 0 < p.1.1 := by
    unfold isingLeapfrogBoxBoundary at hp
    omega
  have hy0 : 0 < p.2.1 := by
    unfold isingLeapfrogBoxBoundary at hp
    omega
  have hxR : p.1.1 + 1 < R + 1 := by
    have hxle := p.1.2
    unfold isingLeapfrogBoxBoundary at hp
    omega
  have hyR : p.2.1 + 1 < R + 1 := by
    have hyle := p.2.2
    unfold isingLeapfrogBoxBoundary at hp
    omega
  have hphysical :=
    fkIsingSquareBoundaryRadialPatchFullObservable_leapfrog_harmonic
      n m (baseI + p.1.1 - 1) (baseJ + p.2.1 - 1) hn hm
      (by omega) (by omega)
  have hSW :
      fkIsingSquareBoundaryRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ (isingLeapfrogSW R p) =
        fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨baseI + p.1.1 - 1, by omega⟩
          ⟨baseJ + p.2.1 - 1, by omega⟩ := by
    unfold fkIsingSquareBoundaryRadialPatchFullObservableWindow
      isingLeapfrogSW isingLeapfrogWest isingLeapfrogSouth
    congr 2 <;> simp only <;> omega
  have hNW :
      fkIsingSquareBoundaryRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ (isingLeapfrogNW R p hp) =
        fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨baseI + p.1.1 - 1, by omega⟩
          ⟨baseJ + p.2.1 - 1 + 2, by omega⟩ := by
    unfold fkIsingSquareBoundaryRadialPatchFullObservableWindow
      isingLeapfrogNW isingLeapfrogWest isingLeapfrogNorth
    congr 2 <;> simp only <;> omega
  have hSE :
      fkIsingSquareBoundaryRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ (isingLeapfrogSE R p hp) =
        fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨baseI + p.1.1 - 1 + 2, by omega⟩
          ⟨baseJ + p.2.1 - 1, by omega⟩ := by
    unfold fkIsingSquareBoundaryRadialPatchFullObservableWindow
      isingLeapfrogSE isingLeapfrogEast isingLeapfrogSouth
    congr 2 <;> simp only <;> omega
  have hNE :
      fkIsingSquareBoundaryRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ (isingLeapfrogNE R p hp) =
        fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨baseI + p.1.1 - 1 + 2, by omega⟩
          ⟨baseJ + p.2.1 - 1 + 2, by omega⟩ := by
    unfold fkIsingSquareBoundaryRadialPatchFullObservableWindow
      isingLeapfrogNE isingLeapfrogEast isingLeapfrogNorth
    congr 2 <;> simp only <;> omega
  have hC :
      fkIsingSquareBoundaryRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ p =
        fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨baseI + p.1.1 - 1 + 1, by omega⟩
          ⟨baseJ + p.2.1 - 1 + 1, by omega⟩ := by
    unfold fkIsingSquareBoundaryRadialPatchFullObservableWindow
    congr 2 <;> omega
  rw [hSW, hNW, hSE, hNE, hC]
  exact hphysical



theorem fkIsingSquareBoundaryRadialPatchFullObservableWindow_physicalNormalized_normSq_sub_le_diffusive
    (n m baseI baseJ R rho : Nat) (mesh : Real)
    (hn : 0 < n) (hm : m ≤ n)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hmesh : 0 < mesh)
    (p p' : IsingLeapfrogBox R) (hrho : 0 < rho)
    (hp : IsingLeapfrogInteriorMargin R rho p)
    (hp' : IsingLeapfrogInteriorMargin R rho p')
    (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
    Complex.normSq
        (fkIsingSquareBoundaryRadialPatchFullObservableWindow
              n m baseI baseJ R hn hm hfitI hfitJ p /
            (Real.sqrt (2 * mesh) : Complex) -
          fkIsingSquareBoundaryRadialPatchFullObservableWindow
              n m baseI baseJ R hn hm hfitI hfitJ p' /
            (Real.sqrt (2 * mesh) : Complex)) ≤
      (1032080 / (rho : Real) ^ 3) *
        ∑ q, Complex.normSq
          (fkIsingSquareBoundaryRadialPatchFullObservableWindow
              n m baseI baseJ R hn hm hfitI hfitJ q /
            (Real.sqrt (2 * mesh) : Complex)) := by
  let F := fkIsingSquareBoundaryRadialPatchFullObservableWindow
    n m baseI baseJ R hn hm hfitI hfitJ
  have hraw : Complex.normSq (F p - F p') ≤
      (1032080 / (rho : Real) ^ 3) * ∑ q, Complex.normSq (F q) :=
    (fkIsingSquareBoundaryRadialPatchFullObservableWindow_harmonic
      n m baseI baseJ R hn hm hfitI hfitJ).normSq_sub_le_of_diffusiveGradient
        isingLeapfrogDiffusiveGradientBound_fermionic p p' hrho hp hp' hpp'
  have hsqrtSq : Real.sqrt (2 * mesh) ^ 2 = 2 * mesh := by
    rw [Real.sq_sqrt]
    positivity
  have hnorm (z : Complex) :
      Complex.normSq (z / (Real.sqrt (2 * mesh) : Complex)) =
        Complex.normSq z / (2 * mesh) := by
    rw [Complex.normSq_div]
    congr 1
    rw [Complex.normSq_eq_norm_sq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 (by positivity))]
    exact hsqrtSq
  change Complex.normSq
      (F p / (Real.sqrt (2 * mesh) : Complex) -
        F p' / (Real.sqrt (2 * mesh) : Complex)) ≤ _
  rw [← sub_div, hnorm]
  simp_rw [hnorm, ← Finset.sum_div]
  have hden : 0 < 2 * mesh := by positivity
  calc
    Complex.normSq (F p - F p') / (2 * mesh) ≤
        ((1032080 / (rho : Real) ^ 3) *
          ∑ q, Complex.normSq (F q)) / (2 * mesh) :=
      div_le_div_of_nonneg_right hraw hden.le
    _ = _ := by ring


noncomputable def fkIsingSquareBoundaryRadialPatchDeepVariation
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) : Real :=
  (∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r,
      |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
            n m hn hm d.snd -
        FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
            n m hn hm d.fst|) +
    ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
      |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
            n m hn hm hm2 d.snd -
        FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
            n m hn hm hm2 d.fst|

theorem fkIsingSquareBoundaryRadialPatchDeepVariation_nonneg
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) :
    0 ≤ fkIsingSquareBoundaryRadialPatchDeepVariation
      n m hn hm hm2 r := by
  unfold fkIsingSquareBoundaryRadialPatchDeepVariation
  positivity



theorem fkIsingSquareBoundaryRadialPatchDeepVariation_le
    (n m r : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (hr : 0 < r) :
    fkIsingSquareBoundaryRadialPatchDeepVariation n m hn hm hm2 r ≤
      16 * (m : Real) ^ 2 / (r : Real) := by
  let Vp : Real :=
    ∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r,
      |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
            n m hn hm d.snd -
        FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
            n m hn hm d.fst|
  let Vd : Real :=
    ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
      |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
            n m hn hm hm2 d.snd -
        FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
            n m hn hm hm2 d.fst|
  have hVp0 : 0 ≤ Vp := by
    dsimp only [Vp]
    positivity
  have hVd0 : 0 ≤ Vd := by
    dsimp only [Vd]
    positivity
  have hscaledVp0 : 0 ≤ (1 / (m : Real)) * Vp := by positivity
  have hscaledVd0 : 0 ≤ (1 / (m : Real)) * Vd := by positivity
  have htarget0 : 0 ≤ 8 * (m : Real) / (r : Real) := by positivity
  have hVpSq : ((1 / (m : Real)) * Vp) ^ 2 ≤
      (8 * (m : Real) / (r : Real)) ^ 2 := by
    calc
      _ ≤ 64 * (m : Real) ^ 2 / (r : Real) ^ 2 :=
        fkIsingSquareBoundaryRadialPatchPrimal_physicalDeepVariation_sq_le
          n m hn hm hm2 r hr
      _ = _ := by ring
  have hVdSq : ((1 / (m : Real)) * Vd) ^ 2 ≤
      (8 * (m : Real) / (r : Real)) ^ 2 := by
    calc
      _ ≤ 64 * (m : Real) ^ 2 / (r : Real) ^ 2 :=
        fkIsingSquareBoundaryRadialPatchDual_physicalDeepVariation_sq_le
          n m hn hm hm2 r hr
      _ = _ := by ring
  have hVpScaled : (1 / (m : Real)) * Vp ≤
      8 * (m : Real) / (r : Real) :=
    (sq_le_sq₀ hscaledVp0 htarget0).mp hVpSq
  have hVdScaled : (1 / (m : Real)) * Vd ≤
      8 * (m : Real) / (r : Real) :=
    (sq_le_sq₀ hscaledVd0 htarget0).mp hVdSq
  have hm0 : (m : Real) ≠ 0 := by positivity
  have hVp : Vp ≤ 8 * (m : Real) ^ 2 / (r : Real) := by
    calc
      Vp = (m : Real) * ((1 / (m : Real)) * Vp) := by field_simp
      _ ≤ (m : Real) * (8 * (m : Real) / (r : Real)) := by gcongr
      _ = _ := by ring
  have hVd : Vd ≤ 8 * (m : Real) ^ 2 / (r : Real) := by
    calc
      Vd = (m : Real) * ((1 / (m : Real)) * Vd) := by field_simp
      _ ≤ (m : Real) * (8 * (m : Real) / (r : Real)) := by gcongr
      _ = _ := by ring
  change Vp + Vd ≤ _
  calc
    Vp + Vd ≤ 8 * (m : Real) ^ 2 / (r : Real) +
        8 * (m : Real) ^ 2 / (r : Real) := add_le_add hVp hVd
    _ = 16 * (m : Real) ^ 2 / (r : Real) := by ring


theorem fkIsingSquareBoundaryRadialPatch_deepCell_physicalNormalized_energy_le
    (n m : Nat) (mesh : Real) (hn : 0 < n) (hm : m ≤ n)
    (hm2 : 2 ≤ m) (hmesh : 0 < mesh) (r : Nat) :
    mesh ^ 2 *
        ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
          Complex.normSq
            (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
                ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩ /
              (Real.sqrt (2 * mesh) : Complex)) ≤
      mesh * fkIsingSquareBoundaryRadialPatchDeepVariation
        n m hn hm hm2 r := by
  have hsqrtSq : Real.sqrt (2 * mesh) ^ 2 = 2 * mesh := by
    rw [Real.sq_sqrt]
    positivity
  have hnorm (z : Complex) :
      Complex.normSq (z / (Real.sqrt (2 * mesh) : Complex)) =
        Complex.normSq z / (2 * mesh) := by
    rw [Complex.normSq_div]
    congr 1
    rw [Complex.normSq_eq_norm_sq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 (by positivity))]
    exact hsqrtSq
  have hraw :=
    fkIsingSquareBoundaryRadialPatch_deepCell_normSq_sum_le_variation
      n m hn hm hm2 r
  simp_rw [hnorm]
  rw [← Finset.sum_div]
  calc
    mesh ^ 2 *
        ((∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
          Complex.normSq
            (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
              ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩)) / (2 * mesh)) =
      mesh / 2 *
        ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
          Complex.normSq
            (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
              ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩) := by
        field_simp
    _ ≤ mesh / 2 *
        (2 * fkIsingSquareBoundaryRadialPatchDeepVariation
          n m hn hm hm2 r) :=
      mul_le_mul_of_nonneg_left (by
        simpa [fkIsingSquareBoundaryRadialPatchDeepVariation] using hraw)
        (by positivity)
    _ = _ := by ring



theorem fkIsingSquareBoundaryRadialPatchFullObservableWindow_deep_energy_le
    (n m baseI baseJ R : Nat) (mesh : Real)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hmesh : 0 < mesh) (r : Nat)
    (hdeep : ∀ p : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ p ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 r) :
    mesh ^ 2 *
        ∑ p : IsingLeapfrogBox R,
          Complex.normSq
            (fkIsingSquareBoundaryRadialPatchFullObservableWindow
                n m baseI baseJ R hn hm hfitI hfitJ p /
              (Real.sqrt (2 * mesh) : Complex)) ≤
      mesh * fkIsingSquareBoundaryRadialPatchDeepVariation
        n m hn hm hm2 r := by
  have hwindow :=
    fkIsingSquareBoundaryRadialPatchNormalizedWindow_energy_le_deepCell
      n m baseI baseJ R mesh hn hm hm2 hfitI hfitJ r hdeep
  have hscaled := mul_le_mul_of_nonneg_left hwindow (sq_nonneg mesh)
  have hdeepEnergy :=
    fkIsingSquareBoundaryRadialPatch_deepCell_physicalNormalized_energy_le
      n m mesh hn hm hm2 hmesh r
  exact hscaled.trans hdeepEnergy


theorem fkIsingSquareBoundaryRadialPatchFullObservableWindow_deep_diffusive
    (n m baseI baseJ R rho : Nat) (mesh : Real)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hmesh : 0 < mesh) (r : Nat)
    (hdeep : ∀ q : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 r)
    (p p' : IsingLeapfrogBox R) (hrho : 0 < rho)
    (hp : IsingLeapfrogInteriorMargin R rho p)
    (hp' : IsingLeapfrogInteriorMargin R rho p')
    (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
    mesh ^ 2 * Complex.normSq
        (fkIsingSquareBoundaryRadialPatchFullObservableWindow
              n m baseI baseJ R hn hm hfitI hfitJ p /
            (Real.sqrt (2 * mesh) : Complex) -
          fkIsingSquareBoundaryRadialPatchFullObservableWindow
              n m baseI baseJ R hn hm hfitI hfitJ p' /
            (Real.sqrt (2 * mesh) : Complex)) ≤
      (1032080 / (rho : Real) ^ 3) * mesh *
        fkIsingSquareBoundaryRadialPatchDeepVariation n m hn hm hm2 r := by
  have hgradient :=
    fkIsingSquareBoundaryRadialPatchFullObservableWindow_physicalNormalized_normSq_sub_le_diffusive
      n m baseI baseJ R rho mesh hn hm hfitI hfitJ hmesh
      p p' hrho hp hp' hpp'
  have henergy :=
    fkIsingSquareBoundaryRadialPatchFullObservableWindow_deep_energy_le
      n m baseI baseJ R mesh hn hm hm2 hfitI hfitJ hmesh r hdeep
  have hfactor : 0 ≤ 1032080 / (rho : Real) ^ 3 := by positivity
  calc
    _ ≤ mesh ^ 2 *
        ((1032080 / (rho : Real) ^ 3) *
          ∑ q : IsingLeapfrogBox R,
            Complex.normSq
              (fkIsingSquareBoundaryRadialPatchFullObservableWindow
                  n m baseI baseJ R hn hm hfitI hfitJ q /
                (Real.sqrt (2 * mesh) : Complex))) :=
      mul_le_mul_of_nonneg_left hgradient (sq_nonneg mesh)
    _ = (1032080 / (rho : Real) ^ 3) *
        (mesh ^ 2 *
          ∑ q : IsingLeapfrogBox R,
            Complex.normSq
              (fkIsingSquareBoundaryRadialPatchFullObservableWindow
                  n m baseI baseJ R hn hm hfitI hfitJ q /
                (Real.sqrt (2 * mesh) : Complex))) := by ring
    _ ≤ (1032080 / (rho : Real) ^ 3) *
        (mesh * fkIsingSquareBoundaryRadialPatchDeepVariation
          n m hn hm hm2 r) := mul_le_mul_of_nonneg_left henergy hfactor
    _ = _ := by ring



theorem fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_neighbor_norm_sub_le
    (n m baseI baseJ R rho : Nat) (mesh d H V : Real)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hmesh : 0 < mesh) (r : Nat)
    (hdeep : ∀ q : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 r)
    (hV : fkIsingSquareBoundaryRadialPatchDeepVariation
      n m hn hm hm2 r ≤ V)
    (hd : 0 ≤ d) (hH : 0 ≤ H)
    (hradius : d ≤ mesh * (rho : Real))
    (hscale : 1032080 * V ≤ H ^ 2 * d ^ 3)
    (p p' : IsingLeapfrogBox R) (hrho : 0 < rho)
    (hp : IsingLeapfrogInteriorMargin R rho p)
    (hp' : IsingLeapfrogInteriorMargin R rho p')
    (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
    ‖fkIsingSquareBoundaryRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ p /
          (Real.sqrt (2 * mesh) : Complex) -
        fkIsingSquareBoundaryRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ p' /
          (Real.sqrt (2 * mesh) : Complex)‖ ≤ mesh * H := by
  let F := fun q : IsingLeapfrogBox R ↦
    fkIsingSquareBoundaryRadialPatchFullObservableWindow
      n m baseI baseJ R hn hm hfitI hfitJ q /
        (Real.sqrt (2 * mesh) : Complex)
  have hdiff : mesh ^ 2 * Complex.normSq (F p - F p') ≤
      (1032080 / (rho : Real) ^ 3) * mesh *
        fkIsingSquareBoundaryRadialPatchDeepVariation n m hn hm hm2 r := by
    simpa [F] using
      fkIsingSquareBoundaryRadialPatchFullObservableWindow_deep_diffusive
        n m baseI baseJ R rho mesh hn hm hm2 hfitI hfitJ hmesh r
        hdeep p p' hrho hp hp' hpp'
  have hfactor : 0 ≤ (1032080 / (rho : Real) ^ 3) * mesh := by positivity
  have hdiffV : mesh ^ 2 * Complex.normSq (F p - F p') ≤
      (1032080 / (rho : Real) ^ 3) * mesh * V :=
    hdiff.trans (mul_le_mul_of_nonneg_left hV hfactor)
  have hrhoReal : 0 < (rho : Real) := by positivity
  have hradiusPow : d ^ 3 ≤ (mesh * (rho : Real)) ^ 3 :=
    pow_le_pow_left₀ hd hradius 3
  have hscale' : 1032080 * V ≤
      H ^ 2 * (mesh * (rho : Real)) ^ 3 :=
    hscale.trans (mul_le_mul_of_nonneg_left hradiusPow (sq_nonneg H))
  have hdiv : 1032080 * V / (rho : Real) ^ 3 ≤ H ^ 2 * mesh ^ 3 := by
    apply (div_le_iff₀ (pow_pos hrhoReal 3)).2
    calc
      1032080 * V ≤ H ^ 2 * (mesh * (rho : Real)) ^ 3 := hscale'
      _ = (H ^ 2 * mesh ^ 3) * (rho : Real) ^ 3 := by ring
  have hrhs : (1032080 / (rho : Real) ^ 3) * mesh * V ≤
      mesh ^ 4 * H ^ 2 := by
    calc
      (1032080 / (rho : Real) ^ 3) * mesh * V =
          mesh * (1032080 * V / (rho : Real) ^ 3) := by ring
      _ ≤ mesh * (H ^ 2 * mesh ^ 3) :=
        mul_le_mul_of_nonneg_left hdiv hmesh.le
      _ = mesh ^ 4 * H ^ 2 := by ring
  have hfinal : mesh ^ 2 * Complex.normSq (F p - F p') ≤
      mesh ^ 4 * H ^ 2 := hdiffV.trans hrhs
  have hmult : mesh ^ 2 * ‖F p - F p'‖ ^ 2 ≤
      mesh ^ 2 * (mesh * H) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact hfinal.trans_eq (by ring)
  have hsquare : ‖F p - F p'‖ ^ 2 ≤ (mesh * H) ^ 2 :=
    le_of_mul_le_mul_left hmult (pow_pos hmesh 2)
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hmesh.le hH)).mp hsquare



theorem fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_neighbor_halfScale
    (n m baseI baseJ R rho r : Nat)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m) (hr : 0 < r)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hdeep : ∀ q : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 r)
    (hmr : m ≤ 2 * r) (hmrho : m ≤ 2 * rho)
    (p p' : IsingLeapfrogBox R) (hrho : 0 < rho)
    (hp : IsingLeapfrogInteriorMargin R rho p)
    (hp' : IsingLeapfrogInteriorMargin R rho p')
    (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
    ‖fkIsingSquareBoundaryRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ p /
          (Real.sqrt (2 * (1 / (m : Real))) : Complex) -
        fkIsingSquareBoundaryRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ p' /
          (Real.sqrt (2 * (1 / (m : Real))) : Complex)‖ ≤
      (1 / (m : Real)) * Real.sqrt (264212480 * (m : Real)) := by
  have hmpos : 0 < (m : Real) := by positivity
  have hmesh : 0 < 1 / (m : Real) := by positivity
  have hV : fkIsingSquareBoundaryRadialPatchDeepVariation
      n m hn hm hm2 r ≤ 32 * (m : Real) := by
    calc
      _ ≤ 16 * (m : Real) ^ 2 / (r : Real) :=
        fkIsingSquareBoundaryRadialPatchDeepVariation_le
          n m r hn hm hm2 hr
      _ ≤ 32 * (m : Real) := by
        apply (div_le_iff₀ (by positivity : (0 : Real) < r)).2
        have hmr' : (m : Real) ≤ 2 * (r : Real) := by exact_mod_cast hmr
        nlinarith
  have hradius : (1 / 2 : Real) ≤
      (1 / (m : Real)) * (rho : Real) := by
    rw [one_div_mul_eq_div]
    apply (le_div_iff₀ hmpos).2
    have hmrho' : (m : Real) ≤ 2 * (rho : Real) := by exact_mod_cast hmrho
    linarith
  have hH : 0 ≤ Real.sqrt (264212480 * (m : Real)) :=
    Real.sqrt_nonneg _
  have hscale :
      1032080 * (32 * (m : Real)) ≤
        Real.sqrt (264212480 * (m : Real)) ^ 2 * (1 / 2 : Real) ^ 3 := by
    rw [Real.sq_sqrt (by positivity)]
    norm_num
    ring_nf
    rfl
  exact
    fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_neighbor_norm_sub_le
      n m baseI baseJ R rho (1 / (m : Real)) (1 / 2)
      (Real.sqrt (264212480 * (m : Real))) (32 * (m : Real))
      hn hm hm2 hfitI hfitJ hmesh r hdeep hV (by norm_num) hH
      hradius hscale p p' hrho hp hp' hpp'

end

end StatMech.Universality
