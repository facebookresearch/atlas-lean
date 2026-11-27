/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.MinimalFibration.Realization.FiniteBaseLocalTriviality
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.TopCatRealizedHornOpenCover
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationFiniteConnectedFactor
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationPullbackMono
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.HornRLPSingularRLP
public import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic
public import MathlibExt.Topology.Category.TopCat.PreimageSubspacePullback
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MinimalFibration.Stability
public import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex

/-!
# Realized horn lifting for minimal simplicial fibrations

For a minimal simplicial fibration p:E→B in any universe u, geometric realization |p| lifts
against every realized horn inclusion |Λⁱ[m]|→|Δ[m]|, m≥1 and 0≤i≤m.

For a finite connected base this follows from local product charts with a fixed realized fiber.
For an arbitrary base, each horn lifting problem factors through a finite connected subcomplex
and is transported through the realization comparison for a pullback along its inclusion.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Simplicial
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet

private theorem terminal_mem_realizedHornRLP (F : TopCat.{u}) :
    TopCat.realizedHornInclusions.{u}.rlp (terminal.from F) := by
  rw [TopCat.hornRLP_iff_toSSet_mem_J_rlp]
  rw [← SSet.modelCategoryQuillen.fibration_iff.{u}]
  rw [← isFibrant_iff_of_isTerminal _
    (IsTerminal.isTerminalObj TopCat.toSSet _ terminalIsTerminal)]
  exact TopCat.toSSet_obj_kanComplex F

private theorem trivialBundle_mem_realizedHornRLP
    {F E B : TopCat.{u}} {p : E ⟶ B}
    (h : TrivialBundleWithFiber F p) :
    TopCat.realizedHornInclusions.{u}.rlp p := by
  have hs : IsPullback p h.r (terminal.from B) (terminal.from F) :=
    IsPullback.of_is_product' h.isLimit terminalIsTerminal
  exact MorphismProperty.of_isPullback hs.flip
    (terminal_mem_realizedHornRLP F)

private theorem trivialBundleOver_restrictPreimage_mem_realizedHornRLP
    {F E B : TopCat.{u}} {p : E ⟶ B}
    (U : TopologicalSpace.Opens B)
    (h : MorphismProperty.TrivialBundleWithFiberOver F p
      (AlgebraicTopology.subspaceIncl (U : Set B))) :
    TopCat.realizedHornInclusions.{u}.rlp
      (TopCat.ofHom (p.hom.restrictPreimage U)) := by
  let q : TopCat.of (p.hom ⁻¹' (U : Set B)) ⟶ TopCat.of U :=
    TopCat.ofHom (p.hom.restrictPreimage U)
  have hq : q = AlgebraicTopology.subspaceMap p
      (fun _ hx => hx :
        Set.MapsTo p (p.hom ⁻¹' (U : Set B)) (U : Set B)) := by
    rfl
  have sq :=
    (AlgebraicTopology.isPullback_preimageSubspace p (U : Set B)).flip
  rw [← hq] at sq
  let e : TopCat.of (p.hom ⁻¹' (U : Set B)) ≅ h.E' :=
    sq.isoIsPullback E (TopCat.of U) h.sq
  have he : e.hom ≫ h.p' = q :=
    sq.isoIsPullback_hom_snd E (TopCat.of U) h.sq
  exact trivialBundle_mem_realizedHornRLP
    (TrivialBundleWithFiber.ofIso e he h.trivial)

/-- Let p:E→B be a minimal simplicial fibration in universe u, with B finite and connected. The
topological map |p|:|E|→|B| has the right lifting property against every realized horn inclusion
|Λⁱ[m]|→|Δ[m]| for m≥1 and 0≤i≤m. -/
theorem toTop_map_mem_realizedHornRLP_of_minimal_finite_connected
    {E B : SSet.{u}} [B.Finite] [B.IsConnected]
    (p : E ⟶ B) (hp : MinimalFibration.IsMinimalFibration p) :
    TopCat.realizedHornInclusions.{u}.rlp (SSet.toTop.map p) := by
  classical
  let b₀ : B _⦋0⦌ := Classical.choice SSet.IsConnected.nonempty
  choose U hz htriv using fun z =>
    SSet.exists_local_trivialBundleWithFiber_toTop p hp b₀ z
  apply TopCat.realizedHornRLP_of_openCover U
  · apply TopologicalSpace.IsOpenCover.of_sets (fun z => (U z).2)
    ext z
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨z, hz z⟩
  · intro z
    exact trivialBundleOver_restrictPreimage_mem_realizedHornRLP
      (U z) (htriv z).some

/-- For any minimal simplicial fibration p:E→B in universe u, |p|:|E|→|B| has the right lifting
property against every realized horn inclusion |Λⁱ[m]|→|Δ[m]|, m≥1 and 0≤i≤m. The base B is
arbitrary in this statement. -/
theorem toTop_map_mem_realizedHornRLP_of_minimal
    {E B : SSet.{u}} (p : E ⟶ B)
    (hp : MinimalFibration.IsMinimalFibration p) :
    TopCat.realizedHornInclusions.{u}.rlp (SSet.toTop.map p) := by
  intro A₀ D₀ i hi
  have hi' := hi
  simp only [TopCat.realizedHornInclusions,
    MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨j⟩⟩ := hi
  let iHorn := SSet.toTop.map (SSet.horn (n + 1) j).ι
  let _ : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
  have hNe : Nonempty (Fin (n + 2)) :=
    ⟨⟨0, Nat.zero_lt_succ _⟩⟩
  have hStd : PathConnectedSpace
      (Convexity.StdSimplex ℝ (Fin (n + 2))) :=
    @Convexity.StdSimplex.pathConnectedSpace _ hNe
  let _ : PathConnectedSpace
      (SSet.toTop.obj (Δ[n + 1] : SSet.{u})) :=
    @Homeomorph.pathConnectedSpace _ _ _ _ hStd
      (SimplexCategory.toTopHomeo ⦋n + 1⦌).symm
  constructor
  intro top bottom sq
  obtain ⟨Y, hYfin, hYconn, s, hs, bottomY, hbottom⟩ :=
    SSet.exists_factor_thru_finite_connected_of_topCatHom bottom
  let _ : Y.Finite := hYfin
  let _ : Y.IsConnected := hYconn
  let _ : Mono s := hs
  let q : pullback s p ⟶ Y := pullback.fst s p
  let e : pullback s p ⟶ E := pullback.snd s p
  have hqmin : MinimalFibration.IsMinimalFibration q :=
    MinimalFibration.isMinimalFibration_pullback_fst p s hp
  have hqRLP : TopCat.realizedHornInclusions.{u}.rlp
      (SSet.toTop.map q) :=
    toTop_map_mem_realizedHornRLP_of_minimal_finite_connected q hqmin
  have hpb : IsPullback (SSet.toTop.map q) (SSet.toTop.map e)
      (SSet.toTop.map s) (SSet.toTop.map p) :=
    (IsPullback.of_hasPullback s p).map_toTop_of_mono
  have hcompat : (iHorn ≫ bottomY) ≫ SSet.toTop.map s =
      top ≫ SSet.toTop.map p := by
    rw [Category.assoc, ← hbottom]
    exact sq.w.symm
  let topY := hpb.lift (iHorn ≫ bottomY) top hcompat
  have sqY : CommSq topY iHorn (SSet.toTop.map q) bottomY :=
    ⟨hpb.lift_fst (iHorn ≫ bottomY) top hcompat⟩
  have hLiftY : sqY.HasLift := (hqRLP iHorn hi').sq_hasLift sqY
  let lY := hLiftY.exists_lift.some
  exact CommSq.HasLift.mk' ⟨lY.l ≫ SSet.toTop.map e,
    by
      calc
        iHorn ≫ (lY.l ≫ SSet.toTop.map e) =
            (iHorn ≫ lY.l) ≫ SSet.toTop.map e := by rw [Category.assoc]
        _ = topY ≫ SSet.toTop.map e := by rw [lY.fac_left]
        _ = top := hpb.lift_snd (iHorn ≫ bottomY) top hcompat,
    by
      calc
        (lY.l ≫ SSet.toTop.map e) ≫ SSet.toTop.map p =
            lY.l ≫ (SSet.toTop.map e ≫ SSet.toTop.map p) :=
          Category.assoc _ _ _
        _ = lY.l ≫ (SSet.toTop.map q ≫ SSet.toTop.map s) := by
          rw [hpb.w]
        _ = (lY.l ≫ SSet.toTop.map q) ≫ SSet.toTop.map s := by
          rw [Category.assoc]
        _ = bottomY ≫ SSet.toTop.map s := by rw [lY.fac_right]
        _ = bottom := hbottom.symm⟩

end SSet
