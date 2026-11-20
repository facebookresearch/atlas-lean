/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone









namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

def vertexGhostGraph (n : Nat) :
    SimpleGraph (Option (FKIsingSquareFullVertexNode n)) :=
  isingFiniteGhostGraph (fkIsingSquareFullVertexGraph n)
    (isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n))

noncomputable def vertexGhostConductance (n : Nat) :
    Option (FKIsingSquareFullVertexNode n) →
      Option (FKIsingSquareFullVertexNode n) → Real :=
  isingFiniteGhostConductance (fkIsingSquareFullVertexGraph n)
    (isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n))

def vertexDirichletBoundary
    (n : Nat) : Option (FKIsingSquareFullVertexNode n) → Prop :=
  isingFiniteGhostBoundaryWith (fkIsingSquareFullVertexFixedBoundary n)

def vertexGhostPrimitive
    (n : Nat) (hn : 0 < n) :
    Option (FKIsingSquareFullVertexNode n) → Real :=
  isingFiniteGhostExtension 1
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive

def faceGhostGraph (n : Nat) :
    SimpleGraph (Option (FKIsingSquareFullFaceNode n)) :=
  isingFiniteGhostGraph (fkIsingSquareFullFaceGraph n)
    (isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n))

noncomputable def faceGhostConductance (n : Nat) :
    Option (FKIsingSquareFullFaceNode n) →
      Option (FKIsingSquareFullFaceNode n) → Real :=
  isingFiniteGhostConductance (fkIsingSquareFullFaceGraph n)
    (isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n))

def faceDirichletBoundary
    (n : Nat) : Option (FKIsingSquareFullFaceNode n) → Prop :=
  isingFiniteGhostBoundaryWith (fkIsingSquareFullFaceFixedBoundary n)

def faceGhostPrimitive
    (n : Nat) (hn : 0 < n) :
    Option (FKIsingSquareFullFaceNode n) → Real :=
  isingFiniteGhostExtension 0
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive

theorem vertexGhostConductance_nonneg (n : Nat) :
    ∀ x y, 0 ≤ vertexGhostConductance n x y := by
  exact isingFiniteGhostConductance_nonneg
    (fkIsingSquareFullVertexGraph n)
    (isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n))
    (isingFermionicGhostRate_nonneg
      (fkIsingSquareFullVertexGhostMultiplicity n))

theorem vertexGhostConductance_pos_of_adj (n : Nat) :
    ∀ ⦃x y⦄, (vertexGhostGraph n).Adj x y →
      0 < vertexGhostConductance n x y := by
  exact isingFiniteGhostConductance_pos_of_adj
    (fkIsingSquareFullVertexGraph n)
    (isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n))

theorem vertexGhost_reaches_boundary (n : Nat) :
    ∀ x, ∃ b, vertexDirichletBoundary n b ∧
      (vertexGhostGraph n).Reachable x b := by
  apply isingFiniteGhostGraph_reachable_boundaryWith
    (fkIsingSquareFullVertexGraph n)
    (isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n))
    (fkIsingSquareFullVertexFixedBoundary n)
  intro x
  obtain ⟨b, hb, hxb⟩ := fkIsingSquareFullVertex_reaches_fixed_or_ghost n x
  refine ⟨b, ?_, hxb⟩
  rcases hb with hb | hb
  · exact Or.inl hb
  · exact Or.inr ((isingFermionicGhostRate_pos_iff
      (fkIsingSquareFullVertexGhostMultiplicity n) b).2 hb)

theorem faceGhostConductance_nonneg (n : Nat) :
    ∀ x y, 0 ≤ faceGhostConductance n x y := by
  exact isingFiniteGhostConductance_nonneg
    (fkIsingSquareFullFaceGraph n)
    (isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n))
    (isingFermionicGhostRate_nonneg
      (fkIsingSquareFullFaceGhostMultiplicity n))

theorem faceGhostConductance_pos_of_adj (n : Nat) :
    ∀ ⦃x y⦄, (faceGhostGraph n).Adj x y →
      0 < faceGhostConductance n x y := by
  exact isingFiniteGhostConductance_pos_of_adj
    (fkIsingSquareFullFaceGraph n)
    (isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n))

theorem faceGhost_reaches_boundary (n : Nat) :
    ∀ x, ∃ b, faceDirichletBoundary n b ∧
      (faceGhostGraph n).Reachable x b := by
  apply isingFiniteGhostGraph_reachable_boundaryWith
    (fkIsingSquareFullFaceGraph n)
    (isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n))
    (fkIsingSquareFullFaceFixedBoundary n)
  intro c
  obtain ⟨b, hb, hcb⟩ := fkIsingSquareFullFace_reaches_fixed_or_ghost n c
  refine ⟨b, ?_, hcb⟩
  rcases hb with hb | hb
  · exact Or.inl hb
  · exact Or.inr ((isingFermionicGhostRate_pos_iff
      (fkIsingSquareFullFaceGhostMultiplicity n) b).2 hb)

theorem vertexGhostPrimitive_superharmonicOn
    (n : Nat) (hn : 0 < n) :
    IsingFiniteWeightedSuperharmonicOn (vertexGhostConductance n)
      (vertexDirichletBoundary n) (vertexGhostPrimitive n hn) := by
  exact isingFiniteGhostExtension_superharmonicOn_boundaryWith
    (fkIsingSquareFullVertexGraph n)
    (isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n))
    (fkIsingSquareFullVertexFixedBoundary n) 1
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
    (vertex_modifiedLaplacian_nonpos_of_not_wiredArc n hn)

theorem faceGhostPrimitive_subharmonicOn
    (n : Nat) (hn : 0 < n) :
    IsingFiniteWeightedSubharmonicOn (faceGhostConductance n)
      (faceDirichletBoundary n) (faceGhostPrimitive n hn) := by
  exact isingFiniteGhostExtension_subharmonicOn_boundaryWith
    (fkIsingSquareFullFaceGraph n)
    (isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n))
    (fkIsingSquareFullFaceFixedBoundary n) 0
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
    (face_modifiedLaplacian_nonneg_of_not_fixedBoundary n hn)



noncomputable def vertexDirichlet
    (n : Nat) (hn : 0 < n) :
    Option (FKIsingSquareFullVertexNode n) → Real :=
  Classical.choose (isingFiniteWeighted_exists_harmonic_extension
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n) (vertexGhostPrimitive n hn))

theorem vertexDirichlet_harmonicOn
    (n : Nat) (hn : 0 < n) :
    IsingFiniteWeightedHarmonicOn (vertexGhostConductance n)
      (vertexDirichletBoundary n) (vertexDirichlet n hn) :=
  (Classical.choose_spec (isingFiniteWeighted_exists_harmonic_extension
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n) (vertexGhostPrimitive n hn))).1

theorem vertexDirichlet_boundary
    (n : Nat) (hn : 0 < n) (x : Option (FKIsingSquareFullVertexNode n))
    (hx : vertexDirichletBoundary n x) :
    vertexDirichlet n hn x = vertexGhostPrimitive n hn x :=
  (Classical.choose_spec (isingFiniteWeighted_exists_harmonic_extension
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n) (vertexGhostPrimitive n hn))).2 x hx



noncomputable def faceDirichlet
    (n : Nat) (hn : 0 < n) :
    Option (FKIsingSquareFullFaceNode n) → Real :=
  Classical.choose (isingFiniteWeighted_exists_harmonic_extension
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n) (faceGhostPrimitive n hn))

theorem faceDirichlet_harmonicOn
    (n : Nat) (hn : 0 < n) :
    IsingFiniteWeightedHarmonicOn (faceGhostConductance n)
      (faceDirichletBoundary n) (faceDirichlet n hn) :=
  (Classical.choose_spec (isingFiniteWeighted_exists_harmonic_extension
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n) (faceGhostPrimitive n hn))).1

theorem faceDirichlet_boundary
    (n : Nat) (hn : 0 < n) (c : Option (FKIsingSquareFullFaceNode n))
    (hc : faceDirichletBoundary n c) :
    faceDirichlet n hn c = faceGhostPrimitive n hn c :=
  (Classical.choose_spec (isingFiniteWeighted_exists_harmonic_extension
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n) (faceGhostPrimitive n hn))).2 c hc

theorem vertexDirichlet_le_ghostPrimitive
    (n : Nat) (hn : 0 < n) :
    ∀ x, vertexDirichlet n hn x ≤ vertexGhostPrimitive n hn x := by
  apply isingFiniteWeighted_harmonic_le_superharmonic
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexDirichlet n hn)
    (vertexGhostPrimitive n hn) (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n) (vertexDirichlet_harmonicOn n hn)
    (vertexGhostPrimitive_superharmonicOn n hn)
  intro x hx
  exact (vertexDirichlet_boundary n hn x hx).le

theorem faceGhostPrimitive_le_dirichlet
    (n : Nat) (hn : 0 < n) :
    ∀ c, faceGhostPrimitive n hn c ≤ faceDirichlet n hn c := by
  apply isingFiniteWeighted_subharmonic_le_harmonic
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceGhostPrimitive n hn)
    (faceDirichlet n hn) (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n) (faceGhostPrimitive_subharmonicOn n hn)
    (faceDirichlet_harmonicOn n hn)
  intro c hc
  exact (faceDirichlet_boundary n hn c hc).ge

theorem vertexDirichlet_nonneg
    (n : Nat) (hn : 0 < n) : ∀ x, 0 ≤ vertexDirichlet n hn x := by
  apply isingFiniteWeighted_const_le_superharmonic
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexDirichlet n hn) 0
    (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n)
  · intro x hx
    exact (vertexDirichlet_harmonicOn n hn x hx).le
  · intro x hx
    rw [vertexDirichlet_boundary n hn x hx]
    cases x with
    | none => simp [vertexGhostPrimitive, isingFiniteGhostExtension]
    | some x =>
        change fkIsingSquareFullVertexFixedBoundary n x at hx
        simp [vertexGhostPrimitive, isingFiniteGhostExtension,
          vertex_fixedBoundary_eq_zero n hn x hx]

theorem vertexDirichlet_le_one
    (n : Nat) (hn : 0 < n) : ∀ x, vertexDirichlet n hn x ≤ 1 := by
  apply isingFiniteWeighted_subharmonic_le_const
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n) (vertexDirichlet n hn) 1
    (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n)
  · intro x hx
    exact (vertexDirichlet_harmonicOn n hn x hx).ge
  · intro x hx
    rw [vertexDirichlet_boundary n hn x hx]
    cases x with
    | none => simp [vertexGhostPrimitive, isingFiniteGhostExtension]
    | some x =>
        change fkIsingSquareFullVertexFixedBoundary n x at hx
        simp [vertexGhostPrimitive, isingFiniteGhostExtension,
          vertex_fixedBoundary_eq_zero n hn x hx]

theorem faceDirichlet_nonneg
    (n : Nat) (hn : 0 < n) : ∀ c, 0 ≤ faceDirichlet n hn c := by
  apply isingFiniteWeighted_const_le_superharmonic
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceDirichlet n hn) 0
    (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n)
  · intro c hc
    exact (faceDirichlet_harmonicOn n hn c hc).le
  · intro c hc
    rw [faceDirichlet_boundary n hn c hc]
    cases c with
    | none => simp [faceGhostPrimitive, isingFiniteGhostExtension]
    | some c =>
        change fkIsingSquareFullFaceFixedBoundary n c at hc
        simp [faceGhostPrimitive, isingFiniteGhostExtension,
          face_fixedBoundary_eq_one n hn c hc]

theorem faceDirichlet_le_one
    (n : Nat) (hn : 0 < n) : ∀ c, faceDirichlet n hn c ≤ 1 := by
  apply isingFiniteWeighted_subharmonic_le_const
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n) (faceDirichlet n hn) 1
    (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n)
  · intro c hc
    exact (faceDirichlet_harmonicOn n hn c hc).ge
  · intro c hc
    rw [faceDirichlet_boundary n hn c hc]
    cases c with
    | none => simp [faceGhostPrimitive, isingFiniteGhostExtension]
    | some c =>
        change fkIsingSquareFullFaceFixedBoundary n c at hc
        simp [faceGhostPrimitive, isingFiniteGhostExtension,
          face_fixedBoundary_eq_one n hn c hc]



theorem physicalIncidence_dirichlet_sandwich
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    vertexDirichlet n hn
          (some (fkIsingSquareInteriorRadialEndpoint n hn e)) ≤
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
          (fkIsingSquareInteriorRadialEndpoint n hn e) ∧
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
          (fkIsingSquareInteriorRadialEndpoint n hn e) ≤
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (fkIsingSquareFullFaceOfRadialIncidence n hn e) ∧
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (fkIsingSquareFullFaceOfRadialIncidence n hn e) ≤
        faceDirichlet n hn
          (some (fkIsingSquareFullFaceOfRadialIncidence n hn e)) := by
  constructor
  · simpa [vertexGhostPrimitive] using
      vertexDirichlet_le_ghostPrimitive n hn
        (some (fkIsingSquareInteriorRadialEndpoint n hn e))
  constructor
  · exact fkIsingSquareBoundaryLayerCoordinateOneForm_vertex_le_face n hn e
  · simpa [faceGhostPrimitive] using
      faceGhostPrimitive_le_dirichlet n hn
        (some (fkIsingSquareFullFaceOfRadialIncidence n hn e))



theorem physicalIncidence_close_of_dirichlet_close
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn)
    (target eps : Real)
    (hvertex : |vertexDirichlet n hn
        (some (fkIsingSquareInteriorRadialEndpoint n hn e)) - target| ≤ eps)
    (hface : |faceDirichlet n hn
        (some (fkIsingSquareFullFaceOfRadialIncidence n hn e)) - target| ≤ eps) :
    |(fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareInteriorRadialEndpoint n hn e) - target| ≤ eps ∧
      |(fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
        (fkIsingSquareFullFaceOfRadialIncidence n hn e) - target| ≤ eps := by
  rcases physicalIncidence_dirichlet_sandwich n hn e with
    ⟨hDirVertex, hVertexFace, hFaceDir⟩
  rw [abs_le] at hvertex hface
  constructor
  · rw [abs_le]
    constructor <;> linarith [hvertex.1, hface.2]
  · rw [abs_le]
    constructor <;> linarith [hvertex.1, hface.2]




theorem radialPatch_unitRange_and_dirichlet_sandwich
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m) :
    ((∀ p, 0 ≤ radialPatchPrimalValue n m hn hm p ∧
        radialPatchPrimalValue n m hn hm p ≤ 1) ∧
      (∀ q, 0 ≤ radialPatchDualValue n m hn hm hm2 q ∧
        radialPatchDualValue n m hn hm hm2 q ≤ 1)) ∧
      ∀ e : FKIsingSquareInteriorRadialIncidence n hn,
        vertexDirichlet n hn
              (some (fkIsingSquareInteriorRadialEndpoint n hn e)) ≤
            (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
              (fkIsingSquareInteriorRadialEndpoint n hn e) ∧
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
              (fkIsingSquareInteriorRadialEndpoint n hn e) ≤
            (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
              (fkIsingSquareFullFaceOfRadialIncidence n hn e) ∧
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
              (fkIsingSquareFullFaceOfRadialIncidence n hn e) ≤
            faceDirichlet n hn
              (some (fkIsingSquareFullFaceOfRadialIncidence n hn e)) := by
  exact ⟨radialPatch_unitRange_of_fullSquareGhost n m hn hm hm2,
    physicalIncidence_dirichlet_sandwich n hn⟩



theorem finiteSquare_integratedPrimitive_dirichletComparison
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m) :
    ((∀ p, 0 ≤ radialPatchPrimalValue n m hn hm p ∧
        radialPatchPrimalValue n m hn hm p ≤ 1) ∧
      (∀ q, 0 ≤ radialPatchDualValue n m hn hm hm2 q ∧
        radialPatchDualValue n m hn hm hm2 q ≤ 1)) ∧
      (∀ x, 0 ≤ vertexDirichlet n hn x ∧ vertexDirichlet n hn x ≤ 1) ∧
      (∀ c, 0 ≤ faceDirichlet n hn c ∧ faceDirichlet n hn c ≤ 1) ∧
      ∀ e : FKIsingSquareInteriorRadialIncidence n hn,
        vertexDirichlet n hn
              (some (fkIsingSquareInteriorRadialEndpoint n hn e)) ≤
            (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
              (fkIsingSquareInteriorRadialEndpoint n hn e) ∧
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
              (fkIsingSquareInteriorRadialEndpoint n hn e) ≤
            (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
              (fkIsingSquareFullFaceOfRadialIncidence n hn e) ∧
          (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
              (fkIsingSquareFullFaceOfRadialIncidence n hn e) ≤
            faceDirichlet n hn
              (some (fkIsingSquareFullFaceOfRadialIncidence n hn e)) := by
  refine ⟨radialPatch_unitRange_of_fullSquareGhost n m hn hm hm2,
    ?_, ?_, physicalIncidence_dirichlet_sandwich n hn⟩
  · intro x
    exact ⟨vertexDirichlet_nonneg n hn x, vertexDirichlet_le_one n hn x⟩
  · intro c
    exact ⟨faceDirichlet_nonneg n hn c, faceDirichlet_le_one n hn c⟩

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality
