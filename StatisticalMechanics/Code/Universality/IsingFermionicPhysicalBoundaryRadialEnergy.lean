/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone
import Code.Universality.IsingFermionicSquareWindowRealization









namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section


noncomputable def fkIsingSquareBoundaryRadialPatchFullObservable
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (i j : Fin m) : Complex :=
  fkIsingSquareBoundaryFullMedialObservable n hn
    (fkIsingSquareRadialPatchEdge n m hm i j)


theorem fkIsingSquareRadialPatchEdge_not_mem_perimeter
    (n m : Nat) (hm : m ≤ n) (i j : Fin m) :
    (fkIsingSquareRadialPatchEdge n m hm i j).1 ∉
      fkIsingSquarePerimeterPrimalEdgeFinset n := by
  exact fkIsingSquareInteriorRadialCell_not_mem_perimeter n
    (fkIsingSquareRadialPatchCell n m hm i j)



theorem fkIsingSquareBoundaryRadialPatchFullObservable_projection
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (i j : Fin m) (s : FKIsingMedialSide) :
    isingProj
        (fkIsingSquareWiredDirectedTangent n hn
          (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s)))
        (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm i j) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s)) := by
  exact fkIsingSquareBoundaryFullMedialObservable_projection n hn _
    (fkIsingSquareRadialPatchEdge_not_mem_perimeter n m hm i j) s


noncomputable def fkIsingSquareBoundaryRadialPatchFullValue
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (i j : Fin m) : Real :=
  fkIsingSquareRadialPatchFullValue n m hm hm2
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive i j

@[simp] theorem fkIsingSquareBoundaryRadialPatchFullValue_of_even
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (i j : Fin m) (h : Even (i.1 + j.1)) :
    fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2 i j =
      FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
        n m hn hm ⟨(i, j), h⟩ := by
  simp [fkIsingSquareBoundaryRadialPatchFullValue,
    fkIsingSquareRadialPatchFullValue,
    FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue, h]

@[simp] theorem fkIsingSquareBoundaryRadialPatchFullValue_of_odd
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (i j : Fin m) (h : ¬ Even (i.1 + j.1)) :
    fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2 i j =
      FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
        n m hn hm hm2 ⟨(i, j), h⟩ := by
  simp [fkIsingSquareBoundaryRadialPatchFullValue,
    fkIsingSquareRadialPatchFullValue,
    FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue, h]


theorem fkIsingSquareBoundaryRadialPatchIncidence_gap
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (i j : Fin m) (s : FKIsingMedialSide) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (fkIsingSquareFullFaceOfRadialIncidence n hn
            (fkIsingSquareRadialPatchIncidence n m hn hm i j s)) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
          (fkIsingSquareInteriorRadialEndpoint n hn
            (fkIsingSquareRadialPatchIncidence n m hn hm i j s)) =
      Complex.normSq
        (isingProj
          (fkIsingSquareWiredDirectedTangent n hn
            (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s)))
          (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm i j)) := by
  rw [fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex]
  change fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s)) = _
  exact fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
    n hn _ (fkIsingSquareRadialPatchEdge_not_mem_perimeter n m hm i j) s


theorem fkIsingSquareBoundaryRadialPatchIncidence_increment_eq_normSq_projection
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (i j : Fin m) (s : FKIsingMedialSide) :
    fkIsingSquareBoundaryLayerRadialIncrement n hn
        (fkIsingSquareRadialPatchIncidence n m hn hm i j s) =
      Complex.normSq
        (isingProj
          (fkIsingSquareWiredDirectedTangent n hn
            (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s)))
          (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm i j)) := by
  change fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s)) = _
  exact fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
    n hn _ (fkIsingSquareRadialPatchEdge_not_mem_perimeter n m hm i j) s



theorem fkIsingSquareRadialPatchDualFullFace_adj_iff
    (n m : Nat) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (p q : FKIsingSquareRadialPatchDualNode m) :
    (fkIsingSquareFullFaceGraph n).Adj
        (fkIsingSquareRadialPatchDualFullFace n m hm hm2 p)
        (fkIsingSquareRadialPatchDualFullFace n m hm hm2 q) ↔
      (fkIsingSquareRadialPatchDualGraph m).Adj p q := by
  have hpmod := Nat.not_even_iff.mp p.2
  have hqmod := Nat.not_even_iff.mp q.2
  simp only [fkIsingSquareFullFaceGraph,
    fkIsingSquareRadialPatchDualGraph]
  simp only [fkIsingSquareRadialPatchDualFullFace, Prod.mk.injEq,
    Fin.mk.injEq]
  omega



theorem fkIsingSquareBoundaryRadialPatchPrimal_laplacian_eq_full
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (p : FKIsingSquareRadialPatchPrimalNode m)
    (hp : ¬ fkIsingSquareRadialPatchPrimalBoundary m p) :
    isingFiniteGraphLaplacian (fkIsingSquareRadialPatchPrimalGraph n m hm)
        (FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
          n m hn hm) p =
      isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareRadialPatchPrimalFullVertex n m hm p) := by
  classical
  let embed := fkIsingSquareRadialPatchPrimalFullVertex n m hm
  let H := (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
  have hi0 : 0 < p.1.1.1 := by
    by_contra h
    apply hp
    left
    omega
  have hi1 : p.1.1.1 + 1 < m := by
    have hi := p.1.1.2
    by_contra h
    apply hp
    right; left
    omega
  have hj0 : 0 < p.1.2.1 := by
    by_contra h
    apply hp
    right; right; left
    omega
  have hj1 : p.1.2.1 + 1 < m := by
    have hj := p.1.2.2
    by_contra h
    apply hp
    right; right; right
    omega
  unfold isingFiniteGraphLaplacian
  apply Finset.sum_bij (fun q _ ↦ embed q)
  · intro q hq
    simpa [fkIsingSquareRadialPatchPrimalGraph, embed] using hq
  · intro a ha b hb hab
    exact fkIsingSquareRadialPatchPrimalNodeVertex_injective n m hm hab
  · intro y hy
    have hadj : (fkSquareBoxPlanar n).G.Adj (embed p) y := by
      simpa only [SimpleGraph.mem_neighborFinset] using hy
    have hcases :=
      (fkIsingSquareRadialPatch_adj_iff_diagonal
        n m p.1.1.1 p.1.2.1 hm hi0 hi1 hj0 hj1 p.2 y).1
        (by simpa [embed, fkIsingSquareRadialPatchPrimalFullVertex,
          fkIsingSquareRadialPatchPrimalNodeVertex] using hadj)
    rcases hcases with hne | hnw | hsw | hse
    · let q : FKIsingSquareRadialPatchPrimalNode m :=
        ⟨(⟨p.1.1.1 + 1, hi1⟩, ⟨p.1.2.1 + 1, hj1⟩), by
          change Even ((p.1.1.1 + 1) + (p.1.2.1 + 1))
          rw [Nat.even_iff]
          have hmod := Nat.even_iff.mp p.2
          omega⟩
      rw [hne] at hadj
      refine ⟨q, ?_, ?_⟩
      · simpa [fkIsingSquareRadialPatchPrimalGraph, embed, q] using hadj
      · simpa [embed, q, fkIsingSquareRadialPatchPrimalFullVertex,
          fkIsingSquareRadialPatchPrimalNodeVertex] using hne.symm
    · let q : FKIsingSquareRadialPatchPrimalNode m :=
        ⟨(⟨p.1.1.1 + 1, hi1⟩, ⟨p.1.2.1 - 1, by omega⟩), by
          change Even ((p.1.1.1 + 1) + (p.1.2.1 - 1))
          rw [Nat.even_iff]
          have hmod := Nat.even_iff.mp p.2
          omega⟩
      rw [hnw] at hadj
      refine ⟨q, ?_, ?_⟩
      · simpa [fkIsingSquareRadialPatchPrimalGraph, embed, q] using hadj
      · simpa [embed, q, fkIsingSquareRadialPatchPrimalFullVertex,
          fkIsingSquareRadialPatchPrimalNodeVertex] using hnw.symm
    · let q : FKIsingSquareRadialPatchPrimalNode m :=
        ⟨(⟨p.1.1.1 - 1, by omega⟩, ⟨p.1.2.1 - 1, by omega⟩), by
          change Even ((p.1.1.1 - 1) + (p.1.2.1 - 1))
          rw [Nat.even_iff]
          have hmod := Nat.even_iff.mp p.2
          omega⟩
      rw [hsw] at hadj
      refine ⟨q, ?_, ?_⟩
      · simpa [fkIsingSquareRadialPatchPrimalGraph, embed, q] using hadj
      · simpa [embed, q, fkIsingSquareRadialPatchPrimalFullVertex,
          fkIsingSquareRadialPatchPrimalNodeVertex] using hsw.symm
    · let q : FKIsingSquareRadialPatchPrimalNode m :=
        ⟨(⟨p.1.1.1 - 1, by omega⟩, ⟨p.1.2.1 + 1, hj1⟩), by
          change Even ((p.1.1.1 - 1) + (p.1.2.1 + 1))
          rw [Nat.even_iff]
          have hmod := Nat.even_iff.mp p.2
          omega⟩
      rw [hse] at hadj
      refine ⟨q, ?_, ?_⟩
      · simpa [fkIsingSquareRadialPatchPrimalGraph, embed, q] using hadj
      · simpa [embed, q, fkIsingSquareRadialPatchPrimalFullVertex,
          fkIsingSquareRadialPatchPrimalNodeVertex] using hse.symm
  · intro q hq
    rfl




theorem fkIsingSquareBoundaryRadialPatchDual_laplacian_eq_full
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (p : FKIsingSquareRadialPatchDualNode m)
    (hp : ¬ fkIsingSquareRadialPatchDualBoundary m p) :
    isingFiniteGraphLaplacian (fkIsingSquareRadialPatchDualGraph m)
        (FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
          n m hn hm hm2) p =
      isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
        (fkIsingSquareRadialPatchDualFullFace n m hm hm2 p) := by
  classical
  let embed := fkIsingSquareRadialPatchDualFullFace n m hm hm2
  let H := (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
  have hi0 : 0 < p.1.1.1 := by
    by_contra h
    apply hp
    left
    omega
  have hi1 : p.1.1.1 + 1 < m := by
    have hi := p.1.1.2
    by_contra h
    apply hp
    right; left
    omega
  have hj0 : 0 < p.1.2.1 := by
    by_contra h
    apply hp
    right; right; left
    omega
  have hj1 : p.1.2.1 + 1 < m := by
    have hj := p.1.2.2
    by_contra h
    apply hp
    right; right; right
    omega
  unfold isingFiniteGraphLaplacian
  apply Finset.sum_bij (fun q _ ↦ embed q)
  · intro q hq
    rw [SimpleGraph.mem_neighborFinset] at hq ⊢
    exact (fkIsingSquareRadialPatchDualFullFace_adj_iff
      n m hm hm2 p q).2 hq
  · intro a ha b hb hab
    exact fkIsingSquareRadialPatchDualFullFace_injective n m hm hm2 hab
  · intro y hy
    have hadj : (fkIsingSquareFullFaceGraph n).Adj (embed p) y := by
      simpa only [SimpleGraph.mem_neighborFinset] using hy
    change
      ((embed p).1 = y.1 ∧
          ((embed p).2.1 + 1 = y.2.1 ∨ y.2.1 + 1 = (embed p).2.1)) ∨
        ((embed p).2 = y.2 ∧
          ((embed p).1.1 + 1 = y.1.1 ∨ y.1.1 + 1 = (embed p).1.1)) at hadj
    rcases hadj with ⟨hx, hyN | hyS⟩ | ⟨hyc, hxE | hxW⟩
    · let q : FKIsingSquareRadialPatchDualNode m :=
        ⟨(⟨p.1.1.1 + 1, hi1⟩, ⟨p.1.2.1 - 1, by omega⟩), by
          change ¬ Even ((p.1.1.1 + 1) + (p.1.2.1 - 1))
          rw [Nat.not_even_iff]
          have hmod := Nat.not_even_iff.mp p.2
          omega⟩
      have hhalf :
          (p.1.1.1 + 1 + (p.1.2.1 - 1) + 1) / 2 =
            (p.1.1.1 + p.1.2.1 + 1) / 2 := by
        congr 1
        omega
      have heq : embed q = y := by
        apply Prod.ext <;> apply Fin.ext
        · calc
            (embed q).1.1 = (embed p).1.1 := by
              simp [embed, q, fkIsingSquareRadialPatchDualFullFace, hhalf]
            _ = y.1.1 := congrArg Fin.val hx
        · calc
            (embed q).2.1 = (embed p).2.1 + 1 := by
              simp [embed, q, fkIsingSquareRadialPatchDualFullFace, hhalf]
              omega
            _ = y.2.1 := hyN
      refine ⟨q, ?_, heq⟩
      rw [SimpleGraph.mem_neighborFinset,
        ← fkIsingSquareRadialPatchDualFullFace_adj_iff n m hm hm2]
      change (fkIsingSquareFullFaceGraph n).Adj (embed p) (embed q)
      rw [heq]
      simpa only [SimpleGraph.mem_neighborFinset] using hy
    · let q : FKIsingSquareRadialPatchDualNode m :=
        ⟨(⟨p.1.1.1 - 1, by omega⟩, ⟨p.1.2.1 + 1, hj1⟩), by
          change ¬ Even ((p.1.1.1 - 1) + (p.1.2.1 + 1))
          rw [Nat.not_even_iff]
          have hmod := Nat.not_even_iff.mp p.2
          omega⟩
      have hhalf :
          (p.1.1.1 - 1 + (p.1.2.1 + 1) + 1) / 2 =
            (p.1.1.1 + p.1.2.1 + 1) / 2 := by
        congr 1
        omega
      have heq : embed q = y := by
        apply Prod.ext <;> apply Fin.ext
        · calc
            (embed q).1.1 = (embed p).1.1 := by
              simp [embed, q, fkIsingSquareRadialPatchDualFullFace, hhalf]
            _ = y.1.1 := congrArg Fin.val hx
        · have hq : (embed q).2.1 + 1 = (embed p).2.1 := by
            simp [embed, q, fkIsingSquareRadialPatchDualFullFace, hhalf]
            omega
          omega
      refine ⟨q, ?_, heq⟩
      rw [SimpleGraph.mem_neighborFinset,
        ← fkIsingSquareRadialPatchDualFullFace_adj_iff n m hm hm2]
      change (fkIsingSquareFullFaceGraph n).Adj (embed p) (embed q)
      rw [heq]
      simpa only [SimpleGraph.mem_neighborFinset] using hy
    · let q : FKIsingSquareRadialPatchDualNode m :=
        ⟨(⟨p.1.1.1 + 1, hi1⟩, ⟨p.1.2.1 + 1, hj1⟩), by
          change ¬ Even ((p.1.1.1 + 1) + (p.1.2.1 + 1))
          rw [Nat.not_even_iff]
          have hmod := Nat.not_even_iff.mp p.2
          omega⟩
      have hhalf :
          (p.1.1.1 + 1 + (p.1.2.1 + 1) + 1) / 2 =
            (p.1.1.1 + p.1.2.1 + 1) / 2 + 1 := by
        have hmod := Nat.not_even_iff.mp p.2
        omega
      have heq : embed q = y := by
        apply Prod.ext <;> apply Fin.ext
        · calc
            (embed q).1.1 = (embed p).1.1 + 1 := by
              simp [embed, q, fkIsingSquareRadialPatchDualFullFace, hhalf]
              omega
            _ = y.1.1 := hxE
        · calc
            (embed q).2.1 = (embed p).2.1 := by
              simp [embed, q, fkIsingSquareRadialPatchDualFullFace, hhalf]
              omega
            _ = y.2.1 := congrArg Fin.val hyc
      refine ⟨q, ?_, heq⟩
      rw [SimpleGraph.mem_neighborFinset,
        ← fkIsingSquareRadialPatchDualFullFace_adj_iff n m hm hm2]
      change (fkIsingSquareFullFaceGraph n).Adj (embed p) (embed q)
      rw [heq]
      simpa only [SimpleGraph.mem_neighborFinset] using hy
    · let q : FKIsingSquareRadialPatchDualNode m :=
        ⟨(⟨p.1.1.1 - 1, by omega⟩, ⟨p.1.2.1 - 1, by omega⟩), by
          change ¬ Even ((p.1.1.1 - 1) + (p.1.2.1 - 1))
          rw [Nat.not_even_iff]
          have hmod := Nat.not_even_iff.mp p.2
          omega⟩
      have hhalf :
          (p.1.1.1 - 1 + (p.1.2.1 - 1) + 1) / 2 + 1 =
            (p.1.1.1 + p.1.2.1 + 1) / 2 := by
        have hmod := Nat.not_even_iff.mp p.2
        omega
      have heq : embed q = y := by
        apply Prod.ext <;> apply Fin.ext
        · have hq : (embed q).1.1 + 1 = (embed p).1.1 := by
            simp [embed, q, fkIsingSquareRadialPatchDualFullFace, hhalf]
            omega
          omega
        · calc
            (embed q).2.1 = (embed p).2.1 := by
              simp [embed, q, fkIsingSquareRadialPatchDualFullFace, hhalf]
              omega
            _ = y.2.1 := congrArg Fin.val hyc
      refine ⟨q, ?_, heq⟩
      rw [SimpleGraph.mem_neighborFinset,
        ← fkIsingSquareRadialPatchDualFullFace_adj_iff n m hm hm2]
      change (fkIsingSquareFullFaceGraph n).Adj (embed p) (embed q)
      rw [heq]
      simpa only [SimpleGraph.mem_neighborFinset] using hy
  · intro q hq
    rfl



theorem fkIsingSquareBoundaryRadialPatchPrimal_superharmonicOn
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) :
    IsingFiniteGraphSuperharmonicOn
      (fkIsingSquareRadialPatchPrimalGraph n m hm)
      (fkIsingSquareRadialPatchPrimalBoundary m)
      (FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
        n m hn hm) := by
  intro p hp
  rw [fkIsingSquareBoundaryRadialPatchPrimal_laplacian_eq_full
    n m hn hm p hp]
  let x := fkIsingSquareRadialPatchPrimalFullVertex n m hm p
  have heast : fkIsingSquareDirectionAvailable n x .east := by
    have h := fkIsingSquareRadialPatchDirection_available n m hm p.1.1 p.1.2
    simpa [x, fkIsingSquareRadialPatchPrimalFullVertex,
      fkIsingSquareRadialPatchPrimalNodeVertex,
      fkIsingSquareRadialPatchDirection, p.2] using h
  have hnorth : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, fkIsingSquareRadialPatchPrimalFullVertex,
      fkIsingSquareRadialPatchPrimalNodeVertex,
      fkIsingSquareDirectionAvailable, fkIsingSquareRadialPatchVertex,
      fkIsingSquareRadialPatchHalf_eq]
    have hmod := Nat.even_iff.mp p.2
    omega
  have hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareRadialPatchPrimalFullVertex,
      fkIsingSquareRadialPatchPrimalNodeVertex,
      fkIsingSquareDirectionAvailable, fkIsingSquareRadialPatchVertex,
      fkIsingSquareRadialPatchHalf_eq]
    have hmod := Nat.even_iff.mp p.2
    omega
  have hsouth : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, fkIsingSquareRadialPatchPrimalFullVertex,
      fkIsingSquareRadialPatchPrimalNodeVertex,
      fkIsingSquareDirectionAvailable, fkIsingSquareRadialPatchVertex,
      fkIsingSquareRadialPatchHalf_eq]
    have hmod := Nat.even_iff.mp p.2
    omega
  exact
    FKIsingSquareBoundaryLayerVertexIntegratedPrimitive.vertex_laplacian_nonpos_of_interior
      n hn x heast hnorth hwest hsouth



theorem fkIsingSquareBoundaryRadialPatchDual_subharmonicOn
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m) :
    IsingFiniteGraphSubharmonicOn
      (fkIsingSquareRadialPatchDualGraph m)
      (fkIsingSquareRadialPatchDualBoundary m)
      (FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
        n m hn hm hm2) := by
  intro p hp
  rw [fkIsingSquareBoundaryRadialPatchDual_laplacian_eq_full
    n m hn hm hm2 p hp]
  let c := fkIsingSquareRadialPatchDualFullFace n m hm hm2 p
  have hi0 : 0 < p.1.1.1 := by
    by_contra h
    apply hp
    left
    omega
  have hi1 : p.1.1.1 + 1 < m := by
    have hi := p.1.1.2
    by_contra h
    apply hp
    right; left
    omega
  have hj0 : 0 < p.1.2.1 := by
    by_contra h
    apply hp
    right; right; left
    omega
  have hj1 : p.1.2.1 + 1 < m := by
    have hj := p.1.2.2
    by_contra h
    apply hp
    right; right; right
    omega
  have heast : c.1.1 + 1 < 2 * n := by
    simp [c, fkIsingSquareRadialPatchDualFullFace]
    have hmod := Nat.not_even_iff.mp p.2
    omega
  have hnorth : c.2.1 + 1 < 2 * n := by
    simp [c, fkIsingSquareRadialPatchDualFullFace]
    have hmod := Nat.not_even_iff.mp p.2
    omega
  have hwest : 0 < c.1.1 := by
    simp [c, fkIsingSquareRadialPatchDualFullFace]
    have hmod := Nat.not_even_iff.mp p.2
    omega
  have hsouth : 0 < c.2.1 := by
    simp [c, fkIsingSquareRadialPatchDualFullFace]
    have hmod := Nat.not_even_iff.mp p.2
    omega
  exact
    FKIsingSquareBoundaryLayerIntegratedPrimitive.face_laplacian_nonneg_of_interior
      n hn c heast hnorth hwest hsouth


theorem fkIsingSquareBoundaryRadialPatchPrimal_physicalDeepVariation_sq_le
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) (hr : 0 < r) :
    ((1 / (m : Real)) *
      ∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r,
        |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
              n m hn hm d.snd -
          FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
              n m hn hm d.fst|) ^ 2 ≤
      64 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
  let S := fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r
  let f := FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
    n m hn hm
  have hrange :=
    (FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatch_unitRange_of_fullSquareGhost
      n m hn hm hm2).1
  have hraw := isingFiniteGraph_compactVariation_sq_le_of_superharmonicOn
    (fkIsingSquareRadialPatchPrimalGraph n m hm)
    (fkIsingSquareRadialPatchPrimalBoundary m)
    (fkIsingSquareRadialPatchPrimalTentCutoff n m hm (by omega) r)
    f 0 1 1 (4 * (m : Real) ^ 2 / (r : Real) ^ 2) S
    (fkIsingSquareBoundaryRadialPatchPrimal_superharmonicOn n m hn hm)
    (fun p ↦ (hrange p).1) (fun p ↦ (hrange p).2)
    (fkIsingSquareRadialPatchPrimalTentCutoff_support n m hm (by omega) r)
    (by norm_num)
    (fkIsingSquareRadialPatchPrimalTentCutoff_one n m hm (by omega) r hr)
    (fkIsingSquareRadialPatchPrimalTentCutoff_energy_le
      n m hm (by omega) r hr)
  have hcardNat : S.card ≤ 4 * m ^ 2 :=
    fkIsingSquareRadialPatchPrimalDeepDarts_card_le n m hm (by omega) r
  have hcard : (S.card : Real) ≤ 4 * (m : Real) ^ 2 := by
    exact_mod_cast hcardNat
  let V : Real := ∑ d ∈ S, |f d.snd - f d.fst|
  have hraw' : V ^ 2 ≤ 16 * (S.card : Real) * (m : Real) ^ 2 /
      (r : Real) ^ 2 := by
    change V ^ 2 ≤ _
    convert hraw using 1 <;> simp [V] <;> ring
  have hV : V ^ 2 ≤ 64 * (m : Real) ^ 4 / (r : Real) ^ 2 := by
    calc
      _ ≤ 16 * (S.card : Real) * (m : Real) ^ 2 / (r : Real) ^ 2 := hraw'
      _ ≤ 16 * (4 * (m : Real) ^ 2) * (m : Real) ^ 2 /
          (r : Real) ^ 2 := by gcongr
      _ = 64 * (m : Real) ^ 4 / (r : Real) ^ 2 := by ring
  change ((1 / (m : Real)) * V) ^ 2 ≤ _
  calc
    _ = (1 / (m : Real) ^ 2) * V ^ 2 := by ring
    _ ≤ (1 / (m : Real) ^ 2) *
        (64 * (m : Real) ^ 4 / (r : Real) ^ 2) :=
      mul_le_mul_of_nonneg_left hV (by positivity)
    _ = _ := by field_simp


theorem fkIsingSquareBoundaryRadialPatchDual_physicalDeepVariation_sq_le
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) (hr : 0 < r) :
    ((1 / (m : Real)) *
      ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
        |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
              n m hn hm hm2 d.snd -
          FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
              n m hn hm hm2 d.fst|) ^ 2 ≤
      64 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
  let S := fkIsingSquareRadialPatchDualDeepDarts m hm2 r
  let f := FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
    n m hn hm hm2
  have hrange :=
    (FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatch_unitRange_of_fullSquareGhost
      n m hn hm hm2).2
  have hraw := isingFiniteGraph_compactVariation_sq_le_of_subharmonicOn
    (fkIsingSquareRadialPatchDualGraph m)
    (fkIsingSquareRadialPatchDualBoundary m)
    (fkIsingSquareRadialPatchDualTentCutoff m hm2 r)
    f 0 1 1 (4 * (m : Real) ^ 2 / (r : Real) ^ 2) S
    (fkIsingSquareBoundaryRadialPatchDual_subharmonicOn n m hn hm hm2)
    (fun p ↦ (hrange p).1) (fun p ↦ (hrange p).2)
    (fkIsingSquareRadialPatchDualTentCutoff_support m hm2 r)
    (by norm_num)
    (fkIsingSquareRadialPatchDualTentCutoff_one m hm2 r hr)
    (fkIsingSquareRadialPatchDualTentCutoff_energy_le m hm2 r hr)
  have hcardNat : S.card ≤ 4 * m ^ 2 :=
    fkIsingSquareRadialPatchDualDeepDarts_card_le m hm2 r
  have hcard : (S.card : Real) ≤ 4 * (m : Real) ^ 2 := by
    exact_mod_cast hcardNat
  let V : Real := ∑ d ∈ S, |f d.snd - f d.fst|
  have hraw' : V ^ 2 ≤ 16 * (S.card : Real) * (m : Real) ^ 2 /
      (r : Real) ^ 2 := by
    change V ^ 2 ≤ _
    convert hraw using 1 <;> simp [V] <;> ring
  have hV : V ^ 2 ≤ 64 * (m : Real) ^ 4 / (r : Real) ^ 2 := by
    calc
      _ ≤ 16 * (S.card : Real) * (m : Real) ^ 2 / (r : Real) ^ 2 := hraw'
      _ ≤ 16 * (4 * (m : Real) ^ 2) * (m : Real) ^ 2 /
          (r : Real) ^ 2 := by gcongr
      _ = 64 * (m : Real) ^ 4 / (r : Real) ^ 2 := by ring
  change ((1 / (m : Real)) * V) ^ 2 ≤ _
  calc
    _ = (1 / (m : Real) ^ 2) * V ^ 2 := by ring
    _ ≤ (1 / (m : Real) ^ 2) *
        (64 * (m : Real) ^ 4 / (r : Real) ^ 2) :=
      mul_le_mul_of_nonneg_left hV (by positivity)
    _ = _ := by field_simp


noncomputable def fkIsingSquareBoundaryRadialPatchHorizontalSignedIncrement
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m) :
    Nat → Nat → Real := fun i j ↦
  let x := fkIsingSquareBoundaryLayerRadialIncrement n hn
    (fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos i j)
  if Even (i + j) then x else -x


noncomputable def fkIsingSquareBoundaryRadialPatchVerticalSignedIncrement
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m) :
    Nat → Nat → Real := fun i j ↦
  let x := fkIsingSquareBoundaryLayerRadialIncrement n hn
    (fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos i j)
  if Even (i + j) then x else -x

theorem fkIsingSquareBoundaryRadialPatchFullValue_horizontal_increment
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (i j : Nat) (hi : i + 1 < m) (hj : j < m) :
    fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
          ⟨i + 1, hi⟩ ⟨j, hj⟩ -
        fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
          ⟨i, by omega⟩ ⟨j, hj⟩ =
      fkIsingSquareBoundaryRadialPatchHorizontalSignedIncrement
        n m hn hm (by omega) i j := by
  let e := fkIsingSquareRadialPatchHorizontalIncidence
    n m hn hm (by omega) i j
  have hc := fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex
    n hn e
  by_cases heven : Even (i + j)
  · have hnext : ¬ Even ((i + 1) + j) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp heven
      omega
    rw [fkIsingSquareRadialPatchHorizontal_face_of_even
        n m hn hm (by omega) i j hi hj heven,
      fkIsingSquareRadialPatchHorizontal_endpoint_of_even
        n m hn hm (by omega) i j hi hj heven] at hc
    simpa [fkIsingSquareBoundaryRadialPatchFullValue,
      fkIsingSquareRadialPatchFullValue,
      FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue,
      FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue,
      fkIsingSquareBoundaryRadialPatchHorizontalSignedIncrement,
      heven, hnext, e] using hc
  · have hnext : Even ((i + 1) + j) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp heven
      omega
    rw [fkIsingSquareRadialPatchHorizontal_face_of_odd
        n m hn hm (by omega) i j hi hj heven,
      fkIsingSquareRadialPatchHorizontal_endpoint_of_odd
        n m hn hm (by omega) i j hi hj heven] at hc
    simp only [fkIsingSquareBoundaryRadialPatchFullValue,
      fkIsingSquareRadialPatchFullValue, hnext, heven,
      dite_true, dite_false,
      fkIsingSquareBoundaryRadialPatchHorizontalSignedIncrement, if_false]
    change _ = -fkIsingSquareBoundaryLayerRadialIncrement n hn e
    linarith

theorem fkIsingSquareBoundaryRadialPatchFullValue_vertical_increment
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (i j : Nat) (hi : i < m) (hj : j + 1 < m) :
    fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
          ⟨i, hi⟩ ⟨j + 1, hj⟩ -
        fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
          ⟨i, hi⟩ ⟨j, by omega⟩ =
      fkIsingSquareBoundaryRadialPatchVerticalSignedIncrement
        n m hn hm (by omega) i j := by
  let e := fkIsingSquareRadialPatchVerticalIncidence
    n m hn hm (by omega) i j
  have hc := fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex
    n hn e
  by_cases heven : Even (i + j)
  · have hnext : ¬ Even (i + (j + 1)) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp heven
      omega
    rw [fkIsingSquareRadialPatchVertical_face_of_even
        n m hn hm (by omega) i j hi hj heven,
      fkIsingSquareRadialPatchVertical_endpoint_of_even
        n m hn hm (by omega) i j hi hj heven] at hc
    simpa [fkIsingSquareBoundaryRadialPatchFullValue,
      fkIsingSquareRadialPatchFullValue,
      FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue,
      FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue,
      fkIsingSquareBoundaryRadialPatchVerticalSignedIncrement,
      heven, hnext, e] using hc
  · have hnext : Even (i + (j + 1)) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp heven
      omega
    rw [fkIsingSquareRadialPatchVertical_face_of_odd
        n m hn hm (by omega) i j hi hj heven,
      fkIsingSquareRadialPatchVertical_endpoint_of_odd
        n m hn hm (by omega) i j hi hj heven] at hc
    simp only [fkIsingSquareBoundaryRadialPatchFullValue,
      fkIsingSquareRadialPatchFullValue, hnext, heven,
      dite_true, dite_false,
      fkIsingSquareBoundaryRadialPatchVerticalSignedIncrement, if_false]
    change _ = -fkIsingSquareBoundaryLayerRadialIncrement n hn e
    linarith



theorem fkIsingSquareBoundaryRadialPatch_normSq_full_le_diagonalVariation
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (i j : Nat) (hi : i + 1 < m) (hj : j + 1 < m) :
    Complex.normSq
        (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨i, by omega⟩ ⟨j, by omega⟩) ≤
      2 *
        (|fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
              ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ -
            fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
              ⟨i, by omega⟩ ⟨j, by omega⟩| +
          |fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
              ⟨i + 1, hi⟩ ⟨j, by omega⟩ -
            fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
              ⟨i, by omega⟩ ⟨j + 1, hj⟩|) := by
  let ii : Fin m := ⟨i, by omega⟩
  let jj : Fin m := ⟨j, by omega⟩
  let F := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm ii jj
  let e := fkIsingSquareRadialPatchEdge n m hm ii jj
  let H := fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
  have hbottom := fkIsingSquareBoundaryRadialPatchFullValue_horizontal_increment
    n m hn hm hm2 i j hi (by omega)
  have htop := fkIsingSquareBoundaryRadialPatchFullValue_horizontal_increment
    n m hn hm hm2 i (j + 1) hi hj
  have hleft := fkIsingSquareBoundaryRadialPatchFullValue_vertical_increment
    n m hn hm hm2 i j (by omega) hj
  have hright := fkIsingSquareBoundaryRadialPatchFullValue_vertical_increment
    n m hn hm hm2 (i + 1) j hi hj
  have hinc (s : FKIsingMedialSide) :=
    fkIsingSquareBoundaryRadialPatchIncidence_increment_eq_normSq_projection
      n m hn hm ii jj s
  by_cases heven : Even (i + j)
  · have htopOdd : ¬ Even (i + (j + 1)) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp heven
      omega
    have hrightOdd : ¬ Even (i + 1 + j) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp heven
      omega
    have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal := by
      dsimp [e, ii, jj]
      rw [fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ heven,
        fkIsingSquareOrientedEdge_directionEdge]
      rfl
    rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
      ⟨hW, hE, hS, hN⟩
    simp only [fkIsingSquareBoundaryRadialPatchHorizontalSignedIncrement,
      fkIsingSquareBoundaryRadialPatchVerticalSignedIncrement,
      heven, htopOdd, hrightOdd, if_true, if_false] at hbottom htop hleft hright
    rw [fkIsingSquareRadialPatchHorizontalIncidence_bottom
        n m hn hm (by omega) i j (by omega) (by omega)] at hbottom
    rw [fkIsingSquareRadialPatchHorizontalIncidence_top_of_cell
        n m hn hm (by omega) i j (by omega) (by omega)] at htop
    rw [fkIsingSquareRadialPatchVerticalIncidence_left
        n m hn hm (by omega) i j (by omega) (by omega)] at hleft
    rw [fkIsingSquareRadialPatchVerticalIncidence_right_of_cell
        n m hn hm (by omega) i j (by omega) (by omega)] at hright
    simp only [fkIsingSquareRadialPatchBottomSide,
      fkIsingSquareRadialPatchTopSide, fkIsingSquareRadialPatchLeftSide,
      fkIsingSquareRadialPatchRightSide, heven, if_true] at hbottom htop hleft hright
    have hdiagPrimal : H ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ -
          H ⟨i, by omega⟩ ⟨j, by omega⟩ =
        Complex.normSq (isingProj Complex.I F) -
          Complex.normSq (isingProj (-1) F) := by
      dsimp [H, F, e, ii, jj] at hW hE hS hN ⊢
      calc
        _ = (fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                ⟨i, by omega⟩ ⟨j + 1, hj⟩ -
              fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                ⟨i, by omega⟩ ⟨j, by omega⟩) +
            (fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ -
              fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                ⟨i, by omega⟩ ⟨j + 1, hj⟩) := by ring
        _ = fkIsingSquareBoundaryLayerRadialIncrement n hn
              (fkIsingSquareRadialPatchIncidence n m hn hm ii jj .south) -
            fkIsingSquareBoundaryLayerRadialIncrement n hn
              (fkIsingSquareRadialPatchIncidence n m hn hm ii jj .east) := by
                rw [hleft, htop]
                ring
        _ = _ := by
          rw [hinc .south, hinc .east, hS, hE]
    have hdiagDual : H ⟨i + 1, hi⟩ ⟨j, by omega⟩ -
          H ⟨i, by omega⟩ ⟨j + 1, hj⟩ =
        Complex.normSq (isingProj 1 F) -
          Complex.normSq (isingProj Complex.I F) := by
      dsimp [H, F, e, ii, jj] at hW hE hS hN ⊢
      calc
        _ = (fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                ⟨i + 1, hi⟩ ⟨j, by omega⟩ -
              fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                ⟨i, by omega⟩ ⟨j, by omega⟩) -
            (fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                ⟨i, by omega⟩ ⟨j + 1, hj⟩ -
              fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                ⟨i, by omega⟩ ⟨j, by omega⟩) := by ring
        _ = fkIsingSquareBoundaryLayerRadialIncrement n hn
              (fkIsingSquareRadialPatchIncidence n m hn hm ii jj .west) -
            fkIsingSquareBoundaryLayerRadialIncrement n hn
              (fkIsingSquareRadialPatchIncidence n m hn hm ii jj .south) := by
                rw [hbottom, hleft]
        _ = _ := by
          rw [hinc .west, hinc .south, hW, hS]
    dsimp [F, H, ii, jj] at hdiagPrimal hdiagDual ⊢
    rw [hdiagPrimal, hdiagDual]
    exact isingProj_normSq_le_two_mul_diagonal_variation _

  · have htopEven : Even (i + (j + 1)) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp heven
      omega
    have hrightEven : Even (i + 1 + j) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp heven
      omega
    have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical := by
      dsimp [e, ii, jj]
      rw [fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ heven,
        fkIsingSquareOrientedEdge_directionEdge]
      rfl
    rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn e haxis with
      ⟨hW, hE, hS, hN⟩
    simp only [fkIsingSquareBoundaryRadialPatchHorizontalSignedIncrement,
      fkIsingSquareBoundaryRadialPatchVerticalSignedIncrement,
      heven, htopEven, hrightEven, if_true, if_false] at hbottom htop hleft hright
    rw [fkIsingSquareRadialPatchHorizontalIncidence_bottom
        n m hn hm (by omega) i j (by omega) (by omega)] at hbottom
    rw [fkIsingSquareRadialPatchHorizontalIncidence_top_of_cell
        n m hn hm (by omega) i j (by omega) (by omega)] at htop
    rw [fkIsingSquareRadialPatchVerticalIncidence_left
        n m hn hm (by omega) i j (by omega) (by omega)] at hleft
    rw [fkIsingSquareRadialPatchVerticalIncidence_right_of_cell
        n m hn hm (by omega) i j (by omega) (by omega)] at hright
    simp only [fkIsingSquareRadialPatchBottomSide,
      fkIsingSquareRadialPatchTopSide, fkIsingSquareRadialPatchLeftSide,
      fkIsingSquareRadialPatchRightSide, heven, if_false] at hbottom htop hleft hright
    have hclosed := isingPrimitiveIncrement_local_closed 1 Complex.I F
      (by norm_num) (by norm_num)
    unfold isingPrimitiveIncrement at hclosed
    have hdiagPrimal : H ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ -
          H ⟨i, by omega⟩ ⟨j, by omega⟩ =
        Complex.normSq (isingProj Complex.I F) -
          Complex.normSq (isingProj (-1) F) := by
      have hraw : H ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ -
            H ⟨i, by omega⟩ ⟨j, by omega⟩ =
          Complex.normSq (isingProj 1 F) -
            Complex.normSq (isingProj (-Complex.I) F) := by
        dsimp [H, F, e, ii, jj] at hW hE hS hN ⊢
        calc
          _ = (fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                  ⟨i, by omega⟩ ⟨j + 1, hj⟩ -
                fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                  ⟨i, by omega⟩ ⟨j, by omega⟩) +
              (fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                  ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ -
                fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                  ⟨i, by omega⟩ ⟨j + 1, hj⟩) := by ring
          _ = -fkIsingSquareBoundaryLayerRadialIncrement n hn
                (fkIsingSquareRadialPatchIncidence n m hn hm ii jj .west) +
              fkIsingSquareBoundaryLayerRadialIncrement n hn
                (fkIsingSquareRadialPatchIncidence n m hn hm ii jj .south) := by
                  rw [hleft, htop]
          _ = _ := by
            rw [hinc .west, hinc .south, hW, hS]
            ring
      linarith
    have hdiagDual : H ⟨i + 1, hi⟩ ⟨j, by omega⟩ -
          H ⟨i, by omega⟩ ⟨j + 1, hj⟩ =
        Complex.normSq (isingProj 1 F) -
          Complex.normSq (isingProj Complex.I F) := by
      have hraw : H ⟨i + 1, hi⟩ ⟨j, by omega⟩ -
            H ⟨i, by omega⟩ ⟨j + 1, hj⟩ =
          Complex.normSq (isingProj (-Complex.I) F) -
            Complex.normSq (isingProj (-1) F) := by
        dsimp [H, F, e, ii, jj] at hW hE hS hN ⊢
        calc
          _ = (fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                  ⟨i + 1, hi⟩ ⟨j, by omega⟩ -
                fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                  ⟨i, by omega⟩ ⟨j, by omega⟩) -
              (fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                  ⟨i, by omega⟩ ⟨j + 1, hj⟩ -
                fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
                  ⟨i, by omega⟩ ⟨j, by omega⟩) := by ring
          _ = -fkIsingSquareBoundaryLayerRadialIncrement n hn
                (fkIsingSquareRadialPatchIncidence n m hn hm ii jj .north) +
              fkIsingSquareBoundaryLayerRadialIncrement n hn
                (fkIsingSquareRadialPatchIncidence n m hn hm ii jj .west) := by
                  rw [hbottom, hleft]
                  ring
          _ = _ := by
            rw [hinc .north, hinc .west, hN, hW]
            ring
      linarith
    dsimp [F, H, ii, jj] at hdiagPrimal hdiagDual ⊢
    rw [hdiagPrimal, hdiagDual]
    exact isingProj_normSq_le_two_mul_diagonal_variation _


noncomputable def fkIsingSquareBoundaryRadialPatchCellDiagonalVariation
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (c : FKIsingSquareRadialPatchInteriorCell m) : Real :=
  |fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
        ⟨c.1.1 + 1, by omega⟩ ⟨c.2.1 + 1, by omega⟩ -
      fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
        ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩| +
    |fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
        ⟨c.1.1 + 1, by omega⟩ ⟨c.2.1, by omega⟩ -
      fkIsingSquareBoundaryRadialPatchFullValue n m hn hm hm2
        ⟨c.1.1, by omega⟩ ⟨c.2.1 + 1, by omega⟩|

theorem fkIsingSquareBoundaryRadialPatchCellDiagonalVariation_eq_cellDarts
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (c : FKIsingSquareRadialPatchInteriorCell m) :
    fkIsingSquareBoundaryRadialPatchCellDiagonalVariation
        n m hn hm hm2 c =
      |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
            n m hn hm
            (fkIsingSquareRadialPatchCellPrimalDart n m hm c).snd -
        FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
            n m hn hm
            (fkIsingSquareRadialPatchCellPrimalDart n m hm c).fst| +
      |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
            n m hn hm hm2
            (fkIsingSquareRadialPatchCellDualDart m c).snd -
        FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
            n m hn hm hm2
            (fkIsingSquareRadialPatchCellDualDart m c).fst| := by
  classical
  by_cases h : Even (c.1.1 + c.2.1)
  · have h11 : Even ((c.1.1 + 1) + (c.2.1 + 1)) := by
      rw [Nat.even_iff]
      have hmod := Nat.even_iff.mp h
      omega
    have h10 : ¬ Even ((c.1.1 + 1) + c.2.1) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp h
      omega
    have h01 : ¬ Even (c.1.1 + (c.2.1 + 1)) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp h
      omega
    simp [fkIsingSquareBoundaryRadialPatchCellDiagonalVariation,
      fkIsingSquareRadialPatchCellPrimalDart,
      fkIsingSquareRadialPatchCellDualDart,
      fkIsingSquareRadialPatchCellPrimalTail,
      fkIsingSquareRadialPatchCellPrimalHead,
      fkIsingSquareRadialPatchCellDualTail,
      fkIsingSquareRadialPatchCellDualHead,
      fkIsingSquareBoundaryRadialPatchFullValue,
      fkIsingSquareRadialPatchFullValue,
      FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue,
      FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue,
      h, h11, h10, h01]
  · have h11 : ¬ Even ((c.1.1 + 1) + (c.2.1 + 1)) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.not_even_iff.mp h
      omega
    have h10 : Even ((c.1.1 + 1) + c.2.1) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp h
      omega
    have h01 : Even (c.1.1 + (c.2.1 + 1)) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp h
      omega
    simp [fkIsingSquareBoundaryRadialPatchCellDiagonalVariation,
      fkIsingSquareRadialPatchCellPrimalDart,
      fkIsingSquareRadialPatchCellDualDart,
      fkIsingSquareRadialPatchCellPrimalTail,
      fkIsingSquareRadialPatchCellPrimalHead,
      fkIsingSquareRadialPatchCellDualTail,
      fkIsingSquareRadialPatchCellDualHead,
      fkIsingSquareBoundaryRadialPatchFullValue,
      fkIsingSquareRadialPatchFullValue,
      FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue,
      FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue,
      h, h11, h10, h01]
    rw [add_comm]
    congr 1
    exact abs_sub_comm _ _

theorem fkIsingSquareBoundaryRadialPatch_normSq_full_le_cellDiagonalVariation
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (c : FKIsingSquareRadialPatchInteriorCell m) :
    Complex.normSq
        (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩) ≤
      2 * fkIsingSquareBoundaryRadialPatchCellDiagonalVariation
        n m hn hm hm2 c := by
  exact fkIsingSquareBoundaryRadialPatch_normSq_full_le_diagonalVariation
    n m hn hm hm2 c.1.1 c.2.1 (by omega) (by omega)



theorem fkIsingSquareBoundaryRadialPatch_deepCellDiagonalVariation_sum_le
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) :
    (∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
        fkIsingSquareBoundaryRadialPatchCellDiagonalVariation
          n m hn hm hm2 c) ≤
      (∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts
          n m hm (by omega) r,
        |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
              n m hn hm d.snd -
          FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
              n m hn hm d.fst|) +
      ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
        |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
              n m hn hm hm2 d.snd -
          FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
              n m hn hm hm2 d.fst| := by
  classical
  let C := fkIsingSquareRadialPatchDeepCells n m hm hm2 r
  let Sp := fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r
  let Sd := fkIsingSquareRadialPatchDualDeepDarts m hm2 r
  let pd := fkIsingSquareRadialPatchCellPrimalDart n m hm
  let dd := fkIsingSquareRadialPatchCellDualDart m
  let fp := fun d : (fkIsingSquareRadialPatchPrimalGraph n m hm).Dart ↦
    |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
          n m hn hm d.snd -
      FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
          n m hn hm d.fst|
  let fd := fun d : (fkIsingSquareRadialPatchDualGraph m).Dart ↦
    |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
          n m hn hm hm2 d.snd -
      FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
          n m hn hm hm2 d.fst|
  have hpInject : Set.InjOn pd (C : Set _) :=
    (fkIsingSquareRadialPatchCellPrimalDart_injective n m hm).injOn
  have hdInject : Set.InjOn dd (C : Set _) :=
    (fkIsingSquareRadialPatchCellDualDart_injective m).injOn
  have hpSubset : C.image pd ⊆ Sp := by
    intro d hd
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hd
    exact (Finset.mem_filter.mp hc).2.1
  have hdSubset : C.image dd ⊆ Sd := by
    intro d hd
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hd
    exact (Finset.mem_filter.mp hc).2.2
  have hpSum : (∑ c ∈ C, fp (pd c)) ≤ ∑ d ∈ Sp, fp d := by
    rw [← Finset.sum_image hpInject]
    exact Finset.sum_le_sum_of_subset_of_nonneg hpSubset
      (fun d _ _ ↦ abs_nonneg _)
  have hdSum : (∑ c ∈ C, fd (dd c)) ≤ ∑ d ∈ Sd, fd d := by
    rw [← Finset.sum_image hdInject]
    exact Finset.sum_le_sum_of_subset_of_nonneg hdSubset
      (fun d _ _ ↦ abs_nonneg _)
  simp_rw [fkIsingSquareBoundaryRadialPatchCellDiagonalVariation_eq_cellDarts
    n m hn hm hm2]
  change (∑ c ∈ C, (fp (pd c) + fd (dd c))) ≤ _
  rw [Finset.sum_add_distrib]
  exact add_le_add hpSum hdSum


theorem fkIsingSquareBoundaryRadialPatch_deepCell_normSq_sum_le_variation
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) :
    (∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
        Complex.normSq
          (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
            ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩)) ≤
      2 *
        ((∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts
            n m hm (by omega) r,
          |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
                n m hn hm d.snd -
            FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
                n m hn hm d.fst|) +
        ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
          |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
                n m hn hm hm2 d.snd -
            FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
                n m hn hm hm2 d.fst|) := by
  calc
    _ ≤ ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
        2 * fkIsingSquareBoundaryRadialPatchCellDiagonalVariation
          n m hn hm hm2 c := by
      apply Finset.sum_le_sum
      intro c hc
      exact fkIsingSquareBoundaryRadialPatch_normSq_full_le_cellDiagonalVariation
        n m hn hm hm2 c
    _ = 2 * (∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
        fkIsingSquareBoundaryRadialPatchCellDiagonalVariation
          n m hn hm hm2 c) := by simp_rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (fkIsingSquareBoundaryRadialPatch_deepCellDiagonalVariation_sum_le
        n m hn hm hm2 r) (by norm_num)



theorem fkIsingSquareBoundaryRadialPatchWindowCarrier_normalized_normSq_le
    (n m baseI baseJ R : Nat) (mesh : Real)
    (hn : 0 < n) (hm : m ≤ n)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hmesh : 0 < mesh) (p : IsingLeapfrogBox R) :
    Complex.normSq
        ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).normalizedFermionicObservable
          mesh
          (fkIsingSquareRadialPatchWindowCarrier
            n m baseI baseJ R hm hfitI hfitJ p)) ≤
      Complex.normSq
        (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
              ⟨baseI + p.1.1, by have := p.1.2; omega⟩
              ⟨baseJ + p.2.1, by have := p.2.2; omega⟩ /
          (Real.sqrt (2 * mesh) : Complex)) := by
  let i : Fin m := ⟨baseI + p.1.1, by have := p.1.2; omega⟩
  let j : Fin m := ⟨baseJ + p.2.1, by have := p.2.2; omega⟩
  let e := fkIsingSquareRadialPatchEdge n m hm i j
  let F := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm i j
  let t := fkIsingSquareWiredDirectedTangent n hn (.dart (e, .west))
  have ht : Complex.normSq t = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    simp [t, fkIsingSquareWiredDirectedTangent, Complex.norm_exp]
  have hproj : Complex.normSq (isingProj t F) ≤ Complex.normSq F := by
    have hpair := isingProj_normSq_add_neg t F ht
    have hnonneg := Complex.normSq_nonneg (isingProj (-t) F)
    linarith
  have hobs :
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (e, .west)) = isingProj t F := by
    exact (fkIsingSquareBoundaryRadialPatchFullObservable_projection
      n m hn hm i j .west).symm
  have hsqrt : 0 < Real.sqrt (2 * mesh) := Real.sqrt_pos.2 (by positivity)
  have hnorm (z : Complex) :
      Complex.normSq (z / (Real.sqrt (2 * mesh) : Complex)) =
        Complex.normSq z / (2 * mesh) := by
    rw [Complex.normSq_div]
    congr 1
    rw [Complex.normSq_eq_norm_sq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hsqrt, Real.sq_sqrt (by positivity)]
  change Complex.normSq
      ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (e, .west)) /
        (Real.sqrt (2 * mesh) : Complex)) ≤
    Complex.normSq (F / (Real.sqrt (2 * mesh) : Complex))
  rw [hobs, hnorm, hnorm]
  exact div_le_div_of_nonneg_right hproj (by positivity)

end

end StatMech.Universality
