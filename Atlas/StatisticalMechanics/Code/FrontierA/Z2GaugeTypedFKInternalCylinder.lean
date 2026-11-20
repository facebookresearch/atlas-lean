/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierA.Z2GaugeTypedFKCylinderGeometry
import Code.FrontierA.Z2GaugeInfiniteVolume

open scoped BigOperators symmDiff

namespace StatMech.FrontierA

noncomputable section

abbrev oddCubeSide (m : Nat) := 2 * m + 1


def cubicalInternalCentralSheet (N m : Nat) (hNm : N <= m) :
    Finset (CubicalPlaquette (oddCubeSide m) (oddCubeSide m) (oddCubeSide m)) :=
  (Finset.univ : Finset (Fin N × Fin N)).image fun ij =>
    CubicalPlaquette.xy
      ⟨m + ij.1.val, by dsimp [oddCubeSide]; omega⟩
      ⟨m + ij.2.val, by dsimp [oddCubeSide]; omega⟩
      ⟨m, by dsimp [oddCubeSide]; omega⟩

theorem mem_cubicalInternalCentralSheet_iff
    (N m : Nat) (hNm : N <= m)
    (i j : Fin (oddCubeSide m)) (f : Fin (oddCubeSide m + 1)) :
    CubicalPlaquette.xy i j f ∈ cubicalInternalCentralSheet N m hNm ↔
      m <= i.val ∧ i.val < m + N ∧
      m <= j.val ∧ j.val < m + N ∧ f.val = m := by
  constructor
  · intro hp
    obtain ⟨ij, _, heq⟩ := Finset.mem_image.mp hp
    simp only [CubicalPlaquette.xy.injEq] at heq
    have hi := congrArg Fin.val heq.1.symm
    have hj := congrArg Fin.val heq.2.1.symm
    have hf := congrArg Fin.val heq.2.2.symm
    simp only at hi hj hf
    constructor
    · omega
    constructor
    · omega
    constructor
    · omega
    constructor <;> omega
  · rintro ⟨hi0, hi1, hj0, hj1, hf⟩
    let x : Fin N := ⟨i.val - m, by omega⟩
    let y : Fin N := ⟨j.val - m, by omega⟩
    apply Finset.mem_image.mpr
    refine ⟨(x, y), Finset.mem_univ _, ?_⟩
    rw [CubicalPlaquette.xy.injEq]
    constructor
    · apply Fin.ext
      dsimp [x]
      omega
    constructor
    · apply Fin.ext
      dsimp [y]
      omega
    · apply Fin.ext
      exact hf.symm


def cubicalInternalCentralBlockSpin (N m : Nat) :
    CubicalDualVertex (oddCubeSide m) (oddCubeSide m) (oddCubeSide m) -> Bool
  | none => false
  | some q => decide
      (m <= q.x.val ∧ q.x.val < m + N ∧
       m <= q.y.val ∧ q.y.val < m + N ∧
       m - N <= q.z.val ∧ q.z.val < m)

theorem cubicalInternalCentralSheet_subset_cut
    (N m : Nat) (hN : 0 < N) (hNm : N <= m) :
    cubicalInternalCentralSheet N m hNm ⊆
      multibondCut
        (cubicalDualEnds
          (a := oddCubeSide m) (b := oddCubeSide m) (c := oddCubeSide m))
        (cubicalInternalCentralBlockSpin N m) := by
  intro p hp
  obtain ⟨ij, _, rfl⟩ := Finset.mem_image.mp hp
  let zBelow : Fin (oddCubeSide m) :=
    ⟨m - 1, by dsimp [oddCubeSide]; omega⟩
  let zAbove : Fin (oddCubeSide m) :=
    ⟨m, by dsimp [oddCubeSide]; omega⟩
  let face : Fin (oddCubeSide m + 1) :=
    ⟨m, by dsimp [oddCubeSide]; omega⟩
  have hback : finBackward face = some zBelow := by
    rw [finBackward_eq_some_iff]
    apply Fin.ext
    dsimp [face, zBelow]
    omega
  have hforward : finForward face = some zAbove := by
    rw [finForward_eq_some_iff]
    apply Fin.ext
    rfl
  rw [mem_multibondCut]
  simp [cubicalDualEnds, face, hback, hforward,
    cubicalInternalCentralBlockSpin, zBelow, zAbove]
  omega



def cubicalInternalCentralComplement (N m : Nat) (hNm : N <= m) :
    Finset (CubicalPlaquette (oddCubeSide m) (oddCubeSide m) (oddCubeSide m)) :=
  multibondCut cubicalDualEnds (cubicalInternalCentralBlockSpin N m) \
    cubicalInternalCentralSheet N m hNm

theorem internalCentralCut_eq_sheet_union_complement
    (N m : Nat) (hN : 0 < N) (hNm : N <= m) :
    multibondCut cubicalDualEnds (cubicalInternalCentralBlockSpin N m) =
      cubicalInternalCentralSheet N m hNm ∪
        cubicalInternalCentralComplement N m hNm := by
  have hsub := cubicalInternalCentralSheet_subset_cut N m hN hNm
  ext p
  simp only [cubicalInternalCentralComplement, Finset.mem_union,
    Finset.mem_sdiff]
  constructor
  · intro hp
    by_cases hD : p ∈ cubicalInternalCentralSheet N m hNm
    · exact Or.inl hD
    · exact Or.inr ⟨hp, hD⟩
  · rintro (hp | ⟨hp, _⟩)
    · exact hsub hp
    · exact hp

theorem internalCentralCut_eq_sheet_symmDiff_complement
    (N m : Nat) (hN : 0 < N) (hNm : N <= m) :
    multibondCut cubicalDualEnds (cubicalInternalCentralBlockSpin N m) =
      cubicalInternalCentralSheet N m hNm ∆
        cubicalInternalCentralComplement N m hNm := by
  have hsub := cubicalInternalCentralSheet_subset_cut N m hN hNm
  ext p
  simp only [cubicalInternalCentralComplement, Finset.mem_symmDiff,
    Finset.mem_sdiff]
  constructor
  · intro hp
    by_cases hD : p ∈ cubicalInternalCentralSheet N m hNm
    · exact Or.inl ⟨hD, fun h => h.2 hD⟩
    · exact Or.inr ⟨⟨hp, hD⟩, hD⟩
  · rintro (⟨hp, _⟩ | ⟨⟨hp, _⟩, _⟩)
    · exact hsub hp
    · exact hp

def cubicalInternalCentralInnerVertices (N m : Nat) (hNm : N <= m) :
    Finset (CubicalDualVertex (oddCubeSide m) (oddCubeSide m) (oddCubeSide m)) :=
  typedMarkedBondVertices
    (typedTrueEndpoint cubicalDualEnds
      (cubicalInternalCentralBlockSpin N m))
    (cubicalInternalCentralComplement N m hNm)

def cubicalInternalCentralUpperVertices (N m : Nat) (hNm : N <= m) :
    Finset (CubicalDualVertex (oddCubeSide m) (oddCubeSide m) (oddCubeSide m)) :=
  typedMarkedBondVertices
    (typedFalseEndpoint cubicalDualEnds
      (cubicalInternalCentralBlockSpin N m))
    (cubicalInternalCentralSheet N m hNm)



def cubicalInternalCentralUpperCoordinateVertices
    (N m : Nat) (hNm : N <= m) :
    Finset (CubicalDualVertex (oddCubeSide m) (oddCubeSide m) (oddCubeSide m)) :=
  (Finset.univ : Finset (Fin N × Fin N)).image fun ij =>
    some (CubicalCell.mk
      ⟨m + ij.1.val, by dsimp [oddCubeSide]; omega⟩
      ⟨m + ij.2.val, by dsimp [oddCubeSide]; omega⟩
      ⟨m, by dsimp [oddCubeSide]; omega⟩)

theorem cubicalInternalCentralUpperVertices_eq_coordinate
    (N m : Nat) (hN : 0 < N) (hNm : N <= m) :
    cubicalInternalCentralUpperVertices N m hNm =
      cubicalInternalCentralUpperCoordinateVertices N m hNm := by
  let zBelow : Fin (oddCubeSide m) :=
    ⟨m - 1, by dsimp [oddCubeSide]; omega⟩
  let zAbove : Fin (oddCubeSide m) :=
    ⟨m, by dsimp [oddCubeSide]; omega⟩
  let face : Fin (oddCubeSide m + 1) :=
    ⟨m, by dsimp [oddCubeSide]; omega⟩
  have hback : finBackward face = some zBelow := by
    rw [finBackward_eq_some_iff]
    apply Fin.ext
    dsimp [face, zBelow]
    omega
  have hforward : finForward face = some zAbove := by
    rw [finForward_eq_some_iff]
    apply Fin.ext
    rfl
  unfold cubicalInternalCentralUpperVertices typedMarkedBondVertices
    cubicalInternalCentralSheet cubicalInternalCentralUpperCoordinateVertices
  rw [Finset.image_image]
  apply Finset.image_congr
  intro ij _
  simp [typedFalseEndpoint, cubicalDualEnds, face, hback, hforward,
    cubicalInternalCentralBlockSpin, zBelow, zAbove]
  omega


def cubicalInternalCentralBoundaryVertices
    (N m : Nat) :
    Finset (CubicalDualVertex (oddCubeSide m) (oddCubeSide m) (oddCubeSide m)) :=
  ((Finset.univ : Finset
      (CubicalCell (oddCubeSide m) (oddCubeSide m) (oddCubeSide m))).filter
    fun q =>
      m <= q.x.val ∧ q.x.val < m + N ∧
      m <= q.y.val ∧ q.y.val < m + N ∧
      m - N <= q.z.val ∧ q.z.val < m ∧
      (q.x.val = m ∨ q.x.val + 1 = m + N ∨
       q.y.val = m ∨ q.y.val + 1 = m + N ∨
       q.z.val = m - N)).image some

theorem cubicalInternalCentralInnerVertices_subset_boundary
    (N m : Nat) (hN : 0 < N) (hNm : N < m) :
    cubicalInternalCentralInnerVertices N m hNm.le ⊆
      cubicalInternalCentralBoundaryVertices N m := by
  intro v hv
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
  have hcut : p ∈ multibondCut cubicalDualEnds
      (cubicalInternalCentralBlockSpin N m) :=
    (Finset.mem_sdiff.mp hp).1
  have hnot : p ∉ cubicalInternalCentralSheet N m hNm.le :=
    (Finset.mem_sdiff.mp hp).2
  have htrue := typedTrueEndpoint_spin_eq_true_of_mem_cut
    cubicalDualEnds (cubicalInternalCentralBlockSpin N m) p hcut
  cases hmark : typedTrueEndpoint cubicalDualEnds
      (cubicalInternalCentralBlockSpin N m) p with
  | none =>
      simp [cubicalInternalCentralBlockSpin, hmark] at htrue
  | some q =>
      have htrueQ : cubicalInternalCentralBlockSpin N m (some q) = true := by
        simpa [hmark] using htrue
      have hin :
          m <= q.x.val ∧ q.x.val < m + N ∧
          m <= q.y.val ∧ q.y.val < m + N ∧
          m - N <= q.z.val ∧ q.z.val < m := by
        simpa [cubicalInternalCentralBlockSpin] using htrueQ
      have hpCells : q ∈ cubicalPlaquetteCells p := by
        by_cases hchi : cubicalInternalCentralBlockSpin N m
            (cubicalDualEnds p).1 = true
        · have hfirst : (cubicalDualEnds p).1 = some q := by
            rw [← hmark]
            simp [typedTrueEndpoint, hchi]
          unfold cubicalPlaquetteCells
          rw [hfirst]
          simp
        · have hfalse : cubicalInternalCentralBlockSpin N m
              (cubicalDualEnds p).1 = false := by
            cases h : cubicalInternalCentralBlockSpin N m
                (cubicalDualEnds p).1
            · rfl
            · exact (hchi h).elim
          have hsecond : (cubicalDualEnds p).2 = some q := by
            rw [← hmark]
            simp [typedTrueEndpoint, hfalse]
          unfold cubicalPlaquetteCells
          rw [hsecond]
          simp
      have hpFace : p ∈ cubicalCellFaces q :=
        (mem_cubicalPlaquetteCells_iff_mem_cellFaces q p).mp hpCells
      apply Finset.mem_image.mpr
      refine ⟨q, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hin.1, hin.2.1, hin.2.2.1, hin.2.2.2.1,
        hin.2.2.2.2.1, hin.2.2.2.2.2, ?_⟩
      by_contra hboundary
      simp only [not_or] at hboundary
      rcases hboundary with ⟨hx0, hx1, hy0, hy1, hz0⟩
      simp only [cubicalCellFaces, Finset.mem_insert,
        Finset.mem_singleton] at hpFace
      rcases hpFace with hp | hp | hp | hp | hp | hp
      · subst p
        let prev : Fin (oddCubeSide m) :=
          ⟨q.z.val - 1, by dsimp [oddCubeSide]; omega⟩
        have hb : finBackward q.z.castSucc = some prev := by
          rw [finBackward_eq_some_iff]
          apply Fin.ext
          dsimp [prev]
          omega
        have hf : finForward q.z.castSucc = some q.z := by
          rw [finForward_eq_some_iff]
        rw [mem_multibondCut] at hcut
        simp only [cubicalDualEnds, hb, hf, Option.map_some] at hcut
        have hprev : cubicalInternalCentralBlockSpin N m
            (some (CubicalCell.mk q.x q.y prev)) = true := by
          simp [cubicalInternalCentralBlockSpin, prev]
          omega
        rw [hprev, htrueQ] at hcut
        exact hcut rfl
      · subst p
        let next : Fin (oddCubeSide m) :=
          ⟨q.z.val + 1, by dsimp [oddCubeSide]; omega⟩
        have hb : finBackward q.z.succ = some q.z := by
          rw [finBackward_eq_some_iff]
        have hf : finForward q.z.succ = some next := by
          rw [finForward_eq_some_iff]
          apply Fin.ext
          rfl
        rw [mem_cubicalInternalCentralSheet_iff] at hnot
        simp only [Fin.val_succ] at hnot
        rw [mem_multibondCut] at hcut
        simp only [cubicalDualEnds, hb, hf, Option.map_some] at hcut
        have hnext : cubicalInternalCentralBlockSpin N m
            (some (CubicalCell.mk q.x q.y next)) = true := by
          simp [cubicalInternalCentralBlockSpin, next]
          omega
        rw [htrueQ, hnext] at hcut
        exact hcut rfl
      · subst p
        let prev : Fin (oddCubeSide m) :=
          ⟨q.y.val - 1, by dsimp [oddCubeSide]; omega⟩
        have hb : finBackward q.y.castSucc = some prev := by
          rw [finBackward_eq_some_iff]
          apply Fin.ext
          dsimp [prev]
          omega
        have hf : finForward q.y.castSucc = some q.y := by
          rw [finForward_eq_some_iff]
        rw [mem_multibondCut] at hcut
        simp only [cubicalDualEnds, hb, hf, Option.map_some] at hcut
        have hprev : cubicalInternalCentralBlockSpin N m
            (some (CubicalCell.mk q.x prev q.z)) = true := by
          simp [cubicalInternalCentralBlockSpin, prev]
          omega
        rw [hprev, htrueQ] at hcut
        exact hcut rfl
      · subst p
        let next : Fin (oddCubeSide m) :=
          ⟨q.y.val + 1, by dsimp [oddCubeSide]; omega⟩
        have hb : finBackward q.y.succ = some q.y := by
          rw [finBackward_eq_some_iff]
        have hf : finForward q.y.succ = some next := by
          rw [finForward_eq_some_iff]
          apply Fin.ext
          rfl
        rw [mem_multibondCut] at hcut
        simp only [cubicalDualEnds, hb, hf, Option.map_some] at hcut
        have hnext : cubicalInternalCentralBlockSpin N m
            (some (CubicalCell.mk q.x next q.z)) = true := by
          simp [cubicalInternalCentralBlockSpin, next]
          omega
        rw [htrueQ, hnext] at hcut
        exact hcut rfl
      · subst p
        let prev : Fin (oddCubeSide m) :=
          ⟨q.x.val - 1, by dsimp [oddCubeSide]; omega⟩
        have hb : finBackward q.x.castSucc = some prev := by
          rw [finBackward_eq_some_iff]
          apply Fin.ext
          dsimp [prev]
          omega
        have hf : finForward q.x.castSucc = some q.x := by
          rw [finForward_eq_some_iff]
        rw [mem_multibondCut] at hcut
        simp only [cubicalDualEnds, hb, hf, Option.map_some] at hcut
        have hprev : cubicalInternalCentralBlockSpin N m
            (some (CubicalCell.mk prev q.y q.z)) = true := by
          simp [cubicalInternalCentralBlockSpin, prev]
          omega
        rw [hprev, htrueQ] at hcut
        exact hcut rfl
      · subst p
        let next : Fin (oddCubeSide m) :=
          ⟨q.x.val + 1, by dsimp [oddCubeSide]; omega⟩
        have hb : finBackward q.x.succ = some q.x := by
          rw [finBackward_eq_some_iff]
        have hf : finForward q.x.succ = some next := by
          rw [finForward_eq_some_iff]
          apply Fin.ext
          rfl
        rw [mem_multibondCut] at hcut
        simp only [cubicalDualEnds, hb, hf, Option.map_some] at hcut
        have hnext : cubicalInternalCentralBlockSpin N m
            (some (CubicalCell.mk next q.y q.z)) = true := by
          simp [cubicalInternalCentralBlockSpin, next]
          omega
        rw [htrueQ, hnext] at hcut
        exact hcut rfl



theorem cubicalInternalCentralDisconnections_subset_consistency
    (N m : Nat) (hN : 0 < N) (hNm : N <= m) :
    finiteEventInter
        ((cubicalInternalCentralInnerVertices N m hNm).product
          (cubicalInternalCentralUpperVertices N m hNm))
        (fun uv => typedFKDisconnEvent cubicalDualEnds uv.1 uv.2) ⊆
      typedFKConsistencyEvent cubicalDualEnds
        (cubicalInternalCentralSheet N m hNm) := by
  apply typedTwoCutMarkedDisconnections_subset_consistency
    cubicalDualEnds
    (cubicalDualEnds_ne
      (by simp [oddCubeSide]) (by simp [oddCubeSide])
      (by simp [oddCubeSide]))
    (cubicalInternalCentralSheet N m hNm)
    (cubicalInternalCentralComplement N m hNm)
    (cubicalInternalCentralSheet N m hNm)
    (cubicalInternalCentralBlockSpin N m)
    (cubicalInternalCentralBlockSpin N m)
  · exact internalCentralCut_eq_sheet_symmDiff_complement N m hN hNm
  · rw [Finset.union_comm]
    exact internalCentralCut_eq_sheet_union_complement N m hN hNm


theorem cubicalInternalCentral_consistencyMass_ge_product
    (N m : Nat) (hN : 0 < N) (hNm : N <= m)
    (J : CubicalPlaquette (oddCubeSide m) (oddCubeSide m) (oddCubeSide m) -> Real)
    (hJ : forall p, 0 <= J p) :
    (∏ uv ∈ (cubicalInternalCentralInnerVertices N m hNm).product
        (cubicalInternalCentralUpperVertices N m hNm),
      (1 - multibondIsingTwoPoint cubicalDualEnds J uv.1 uv.2)) <=
      multibondIsingPartition cubicalDualEnds
          (multibondTwistCoupling J (cubicalInternalCentralSheet N m hNm)) /
        multibondIsingPartition cubicalDualEnds J := by
  apply multibondIsing_twist_ratio_ge_pair_correlation_product
    cubicalDualEnds J hJ (cubicalInternalCentralSheet N m hNm)
    (cubicalInternalCentralInnerVertices N m hNm)
    (cubicalInternalCentralUpperVertices N m hNm)
  exact cubicalInternalCentralDisconnections_subset_consistency N m hN hNm




theorem cubicalInternalCentralWilsonExpectation_ge_product
    (N m : Nat) (hN : 0 < N) (hNm : N <= m)
    (K : CubicalPlaquette (oddCubeSide m) (oddCubeSide m) (oddCubeSide m) -> Real)
    (hK : forall p, 0 < K p) :
    (∏ uv ∈ (cubicalInternalCentralInnerVertices N m hNm).product
        (cubicalInternalCentralUpperVertices N m hNm),
      (1 - multibondIsingTwoPoint cubicalDualEnds
        (fun p => gaugeDualCoupling (K p)) uv.1 uv.2)) <=
      gaugeWilsonExpectation cubicalPlaquetteIncidence K
        (gaugeSurfaceBoundary cubicalPlaquetteIncidence
          (cubicalInternalCentralSheet N m hNm)) := by
  rw [cubicalWilsonExpectation_eq_twistedIsingPartitionRatio_of_surface
    (by simp [oddCubeSide]) (by simp [oddCubeSide])
    (by simp [oddCubeSide]) K hK (cubicalInternalCentralSheet N m hNm)]
  exact cubicalInternalCentral_consistencyMass_ge_product N m hN hNm
    (fun p => gaugeDualCoupling (K p))
    (fun p => (gaugeDualCoupling_pos (hK p)).le)

end

end StatMech.FrontierA
