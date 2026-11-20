/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalRangeTransfer
import Code.Universality.IsingFermionicPhysicalDeepEnergy
import Code.Universality.IsingFermionicPhysicalFullSquareGhost
import Code.Universality.IsingFermionicPhysicalFullSquarePrimitive










namespace StatMech.Universality

noncomputable section



theorem fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_sq_le_of_ghostComparison
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) (hr : 0 < r) (base : Real)
    (hprimalLower : ∀ p, 0 ≤
      fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p)
    (hdualUpper : ∀ q,
      fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q ≤ 1) :
    (((1 / (m : Real)) ^ 2) *
        ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
          Complex.normSq
            (fkIsingSquareRadialPatchFullObservable n m hn hm
                ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩ /
              (Real.sqrt (2 * (1 / (m : Real))) : Complex))) ^ 2 ≤
      256 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
  let mesh : Real := 1 / (m : Real)
  let E : Real := mesh ^ 2 *
    ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
      Complex.normSq
        (fkIsingSquareRadialPatchFullObservable n m hn hm
            ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩ /
          (Real.sqrt (2 * mesh) : Complex))
  let Vp : Real :=
    ∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r,
      |fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.snd -
        fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.fst|
  let Vd : Real :=
    ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
      |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd -
        fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|
  have hmesh : 0 < mesh := by
    dsimp only [mesh]
    positivity
  have hbridge : E ≤ mesh * (Vp + Vd) := by
    exact fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_le
      n m mesh hn hm hm2 hmesh r base
  have hp : (mesh * Vp) ^ 2 ≤
      64 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
    simpa only [mesh, Vp] using
      (fkIsingSquareRadialPatchPrimal_physicalDeepVariation_sq_le_of_ghostComparison
        n m hn hm hm2 r hr base hprimalLower hdualUpper)
  have hd : (mesh * Vd) ^ 2 ≤
      64 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
    simpa only [mesh, Vd] using
      (fkIsingSquareRadialPatchDual_physicalDeepVariation_sq_le_of_ghostComparison
        n m hn hm hm2 r hr base hprimalLower hdualUpper)
  let C : Real := 64 * (m : Real) ^ 2 / (r : Real) ^ 2
  have hsum : (mesh * (Vp + Vd)) ^ 2 ≤
      256 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
    have hp' : (mesh * Vp) ^ 2 ≤ C := hp
    have hd' : (mesh * Vd) ^ 2 ≤ C := hd
    have hparallelogram := sq_nonneg (mesh * Vp - mesh * Vd)
    have hfour : (mesh * (Vp + Vd)) ^ 2 ≤ 4 * C := by
      nlinarith
    convert hfour using 1 <;> simp only [C] <;> ring
  have hE0 : 0 ≤ E := by
    apply mul_nonneg (sq_nonneg mesh)
    apply Finset.sum_nonneg
    intro c hc
    exact Complex.normSq_nonneg _
  have hVp0 : 0 ≤ Vp := by
    apply Finset.sum_nonneg
    intro d hd
    exact abs_nonneg _
  have hVd0 : 0 ≤ Vd := by
    apply Finset.sum_nonneg
    intro d hd
    exact abs_nonneg _
  have hright0 : 0 ≤ mesh * (Vp + Vd) :=
    mul_nonneg hmesh.le (add_nonneg hVp0 hVd0)
  change E ^ 2 ≤ _
  exact ((sq_le_sq₀ hE0 hright0).2 hbridge).trans hsum


theorem fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_sq_le_fixedFraction
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) (hr : 0 < r) (base K : Real) (hK : 0 ≤ K)
    (hmr : (m : Real) ≤ K * (r : Real))
    (hprimalLower : ∀ p, 0 ≤
      fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p)
    (hdualUpper : ∀ q,
      fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q ≤ 1) :
    (((1 / (m : Real)) ^ 2) *
        ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
          Complex.normSq
            (fkIsingSquareRadialPatchFullObservable n m hn hm
                ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩ /
              (Real.sqrt (2 * (1 / (m : Real))) : Complex))) ^ 2 ≤
      256 * K ^ 2 := by
  have hmain :=
    fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_sq_le_of_ghostComparison
      n m hn hm hm2 r hr base hprimalLower hdualUpper
  refine hmain.trans ?_
  have hsquare : (m : Real) ^ 2 ≤ (K * (r : Real)) ^ 2 :=
    (sq_le_sq₀ (by positivity) (mul_nonneg hK (by positivity))).2 hmr
  rw [div_le_iff₀ (sq_pos_of_pos (by exact_mod_cast hr : (0 : Real) < r))]
  nlinarith




theorem fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_sq_le_of_fullSquareGhost
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) (hr : 0 < r) (base : Real)
    (vertexH : FKIsingSquareFullVertexNode n → Real)
    (faceH : FKIsingSquareFullFaceNode n → Real)
    (hvertexModified : ∀ x,
      ¬ fkIsingSquareFullVertexFixedBoundary n x →
        isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) vertexH x +
          isingFermionicGhostRate
            (fkIsingSquareFullVertexGhostMultiplicity n) x *
              (1 - vertexH x) ≤ 0)
    (hvertexFixed : ∀ x,
      fkIsingSquareFullVertexFixedBoundary n x → 0 ≤ vertexH x)
    (hfaceModified : ∀ c,
      ¬ fkIsingSquareFullFaceFixedBoundary n c →
        0 ≤ isingFiniteGraphLaplacian
          (fkIsingSquareFullFaceGraph n) faceH c +
            isingFermionicGhostRate
              (fkIsingSquareFullFaceGhostMultiplicity n) c *
                (0 - faceH c))
    (hfaceFixed : ∀ c,
      fkIsingSquareFullFaceFixedBoundary n c → faceH c ≤ 1)
    (hprimalRestriction : ∀ p,
      fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p =
        vertexH (fkIsingSquareRadialPatchPrimalFullVertex n m hm p))
    (hdualRestriction : ∀ q,
      fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q =
        faceH (fkIsingSquareRadialPatchDualFullFace n m hm hm2 q)) :
    (((1 / (m : Real)) ^ 2) *
        ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
          Complex.normSq
            (fkIsingSquareRadialPatchFullObservable n m hn hm
                ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩ /
              (Real.sqrt (2 * (1 / (m : Real))) : Complex))) ^ 2 ≤
      256 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
  obtain ⟨hprimal, hdual⟩ :=
    fkIsingSquareRadialPatch_unitRange_of_fullSquareGhost
      n m hn hm hm2 base vertexH faceH
      hvertexModified hvertexFixed hfaceModified hfaceFixed
      hprimalRestriction hdualRestriction
  exact
    fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_sq_le_of_ghostComparison
      n m hn hm hm2 r hr base
      (fun p ↦ (hprimal p).1) (fun q ↦ (hdual q).2)



theorem fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_sq_le_of_fullSquareGhost_compatible
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) (hr : 0 < r) (base : Real)
    (vertexH : FKIsingSquareFullVertexNode n → Real)
    (faceH : FKIsingSquareFullFaceNode n → Real)
    (hvertexModified : ∀ x,
      ¬ fkIsingSquareFullVertexFixedBoundary n x →
        isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) vertexH x +
          isingFermionicGhostRate
            (fkIsingSquareFullVertexGhostMultiplicity n) x *
              (1 - vertexH x) ≤ 0)
    (hvertexFixed : ∀ x,
      fkIsingSquareFullVertexFixedBoundary n x → 0 ≤ vertexH x)
    (hfaceModified : ∀ c,
      ¬ fkIsingSquareFullFaceFixedBoundary n c →
        0 ≤ isingFiniteGraphLaplacian
          (fkIsingSquareFullFaceGraph n) faceH c +
            isingFermionicGhostRate
              (fkIsingSquareFullFaceGhostMultiplicity n) c *
                (0 - faceH c))
    (hfaceFixed : ∀ c,
      fkIsingSquareFullFaceFixedBoundary n c → faceH c ≤ 1)
    (hcompatible :
      FKIsingSquareFullPrimitiveCompatible n hn vertexH faceH)
    (hbase : fkIsingSquareRadialPatchFullValue
      n m hm hm2 vertexH faceH ⟨0, by omega⟩ ⟨0, by omega⟩ = base) :
    (((1 / (m : Real)) ^ 2) *
        ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
          Complex.normSq
            (fkIsingSquareRadialPatchFullObservable n m hn hm
                ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩ /
              (Real.sqrt (2 * (1 / (m : Real))) : Complex))) ^ 2 ≤
      256 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
  apply
    fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_sq_le_of_fullSquareGhost
      n m hn hm hm2 r hr base vertexH faceH hvertexModified hvertexFixed
        hfaceModified hfaceFixed
  · exact fkIsingSquareRadialPatchPrimalValue_eq_full_of_compatible
      n m hn hm hm2 base vertexH faceH hcompatible hbase
  · exact fkIsingSquareRadialPatchDualValue_eq_full_of_compatible
      n m hn hm hm2 base vertexH faceH hcompatible hbase

end

end StatMech.Universality
