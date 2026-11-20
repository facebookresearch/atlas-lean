/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldTransverseAssembly











open MeasureTheory Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}



def PeriodicGraph.translatedFiniteInfinitePairConnectionEvent
    (P : PeriodicGraph V) (z : Site 2) (L R : Finset V) (N : Nat) :
    Set (ConfigSpace (Sym2 V)) :=
  P.translateEvent z (P.finiteInfinitePairConnectionEvent L R N)

theorem PeriodicGraph.translatedFiniteInfinitePairConnectionEvent_measurableSet
    (P : PeriodicGraph V) (z : Site 2) (L R : Finset V) (N : Nat) :
    MeasurableSet (P.translatedFiniteInfinitePairConnectionEvent z L R N) :=
  P.translateEvent_measurableSet z
    (P.finiteInfinitePairConnectionEvent_measurableSet L R N)



theorem PeriodicGraph.translatedFiniteInfinitePairConnectionEvent_measureReal
    (P : PeriodicGraph V)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu)
    (z : Site 2) (L R : Finset V) (N : Nat) :
    mu.real (P.translatedFiniteInfinitePairConnectionEvent z L R N) =
      mu.real (P.finiteInfinitePairConnectionEvent L R N) := by
  exact congrArg ENNReal.toReal
    (P.translateEvent_measure_eq mu hTI z
      (P.finiteInfinitePairConnectionEvent_measurableSet L R N))


def PeriodicGraph.shiftGraphHom
    (P : PeriodicGraph V) (z : Site 2) : P.graph →g P.graph where
  toFun := P.shift z
  map_rel' := fun {_ _} h => (P.shift_adj z _ _).2 h

@[simp] theorem PeriodicGraph.shiftGraphHom_apply
    (P : PeriodicGraph V) (z : Site 2) (v : V) :
    P.shiftGraphHom z v = P.shift z v := rfl




theorem PeriodicGraph.translatedFiniteInfinitePairConnectionEvent_graphWalk
    (P : PeriodicGraph V) {omega : ConfigSpace (Sym2 V)}
    {z : Site 2} {L R : Finset V} {N : Nat}
    (h : omega ∈ P.translatedFiniteInfinitePairConnectionEvent z L R N) :
    ∃ x ∈ L.image (P.shift (-z)), ∃ y ∈ R.image (P.shift (-z)),
      ∃ q : P.graph.Walk x y,
        (∀ v ∈ q.support,
          v ∈ (P.orbitBox (P.bufferedRadius N)).image (P.shift (-z))) ∧
        ∀ {u v : V}, s(u, v) ∈ q.edges → omega s(u, v) = true := by
  obtain ⟨x, hx, y, hy, q, hsupport, hopen⟩ :=
    P.finiteInfinitePairConnectionEvent_graphWalk h
  let shiftHom := P.shiftGraphHom (-z)
  let qz : P.graph.Walk (P.shift (-z) x) (P.shift (-z) y) :=
    q.map shiftHom
  refine ⟨P.shift (-z) x, Finset.mem_image.2 ⟨x, hx, rfl⟩,
    P.shift (-z) y, Finset.mem_image.2 ⟨y, hy, rfl⟩, qz, ?_, ?_⟩
  · intro v hv
    change v ∈ (q.map shiftHom).support at hv
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    exact Finset.mem_image.2 ⟨u, hsupport u hu, rfl⟩
  · intro u v huv
    change s(u, v) ∈ (q.map shiftHom).edges at huv
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at huv
    obtain ⟨e, he, heq⟩ := huv
    induction e using Sym2.inductionOn with
    | _ a b =>
      have heOpen := hopen (u := a) (v := b) he
      change omega (Sym2.map (P.shift (-z)) s(a, b)) = true at heOpen
      simpa only [shiftHom, PeriodicGraph.shiftGraphHom_apply] using
        heq ▸ heOpen




theorem PeriodicGraph.exists_uniformRadius_highProbability_translatedFiniteEvent
    (P : PeriodicGraph V)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ n : Nat, ∀ zL zR : Site 2, ∃ N : Nat, ∀ z : Site 2,
      1 - epsilon < mu.real
        (P.translatedFiniteInfinitePairConnectionEvent z
          ((P.orbitBox n).image (P.shift zL))
          ((P.orbitBox n).image (P.shift zR)) N) := by
  obtain ⟨n, hn⟩ :=
    P.exists_uniformRadius_highProbability_translatedBoxPairConnection
      mu hTI hunique hepsilon
  refine ⟨n, ?_⟩
  intro zL zR
  obtain ⟨N, hN⟩ := hn zL zR
  refine ⟨N, ?_⟩
  intro z
  rw [P.translatedFiniteInfinitePairConnectionEvent_measureReal
    mu hTI z]
  exact hN



theorem PeriodicPlanarDualPair.dualMeasure_measureReal
    {W : Type*} [DecidableEq W] [Countable W]
    {Pdual : PeriodicGraph W}
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    {A : Set (ConfigSpace (Sym2 W))} (hA : MeasurableSet A) :
    (D.dualMeasure mu).real A =
      mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' A) := by
  unfold PeriodicPlanarDualPair.dualMeasure Measure.real
  rw [Measure.map_apply
    (continuous_dualConfigEquiv D.edgeDual).measurable hA]




theorem PeriodicPlanarDualPair.exists_uniformRadius_highProbability_complementaryDualFiniteEvent
    {W : Type*} [DecidableEq W] [Countable W]
    {Pdual : PeriodicGraph W}
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hdualUnique : D.dualMeasure mu
      {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ n : Nat, ∀ zL zR : Site 2, ∃ N : Nat, ∀ z : Site 2,
      1 - epsilon < mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        Pdual.translatedFiniteInfinitePairConnectionEvent z
          ((Pdual.orbitBox n).image (Pdual.shift zL))
          ((Pdual.orbitBox n).image (Pdual.shift zR)) N) := by
  let muDual := D.dualMeasure mu
  letI : IsProbabilityMeasure muDual := by
    dsimp only [muDual, PeriodicPlanarDualPair.dualMeasure]
    exact Measure.isProbabilityMeasure_map
      (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable
  obtain ⟨n, hn⟩ :=
    Pdual.exists_uniformRadius_highProbability_translatedFiniteEvent
      muDual (D.dualMeasure_isTranslationInvariant mu hTI) hdualUnique hepsilon
  refine ⟨n, ?_⟩
  intro zL zR
  obtain ⟨N, hN⟩ := hn zL zR
  refine ⟨N, ?_⟩
  intro z
  rw [← D.dualMeasure_measureReal mu
    (Pdual.translatedFiniteInfinitePairConnectionEvent_measurableSet
      z ((Pdual.orbitBox n).image (Pdual.shift zL))
        ((Pdual.orbitBox n).image (Pdual.shift zR)) N)]
  exact hN z






theorem PeriodicPlaneEmbedding.exists_verticalGap_shift_orbitBox_middleThird
    (E : PeriodicPlaneEmbedding P) (N : Nat) (B s : Real) :
    ∃ gap : Int, 0 < (gap : Real) ∧ ∃ z : Site 2,
      z 0 = 0 ∧
      ∀ v ∈ (P.orbitBox (P.bufferedRadius N)).image (P.shift (-z)),
        (2 * s + (s + gap)) / 3 + B < E.vertexCoord v 1 ∧
          E.vertexCoord v 1 < (s + 2 * (s + gap)) / 3 - B := by
  let M := E.orbitBoxCoordinateBound (P.bufferedRadius N) (1 : Fin 2)
  obtain ⟨k, hk⟩ := exists_nat_ge (|s| + B + M)
  let K : Nat := k + 1
  let gap : Int := 6 * (K : Int)
  let z : Site 2 := verticalShift (-3 * (K : Int))
  have hKM : |s| + B + M < (K : Real) := by
    dsimp only [K]
    norm_num
    linarith
  have hK0 : 0 < (K : Real) := by
    positivity
  refine ⟨gap, ?_, z, ?_, ?_⟩
  · dsimp only [gap]
    push_cast
    positivity
  · simp [z]
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    have huBound := E.abs_vertexCoord_le_orbitBoxCoordinateBound
      hu (1 : Fin 2)
    have hsUpper : s ≤ |s| := le_abs_self s
    have hsLower : -s ≤ |s| := neg_le_abs s
    rw [E.vertexCoord_shift]
    have hz : ((-z) 1 : Real) = 3 * (K : Real) := by
      simp [z, verticalShift]
    rw [hz]
    change
      (2 * s + (s + (gap : Real))) / 3 + B <
          E.vertexCoord u 1 + 3 * (K : Real) ∧
        E.vertexCoord u 1 + 3 * (K : Real) <
          (s + 2 * (s + (gap : Real))) / 3 - B
    have hgap : (gap : Real) = 6 * (K : Real) := by
      simp [gap]
    rw [hgap]
    rw [abs_le] at huBound
    constructor <;> linarith

namespace PeriodicPlanarDualPair

variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}





theorem exists_verticalGap_translatedDualPlacement
    (D : PeriodicPlanarDualPair P Pdual) (N : Nat) (Bd s a b : Real)
    {Ld Rd : Finset W}
    (hLd : ∀ y ∈ Ld,
      D.primalEmbedding.coordinates (D.dualEmbedding.vertex y) 0 < a)
    (hRd : ∀ y ∈ Rd,
      b < D.primalEmbedding.coordinates (D.dualEmbedding.vertex y) 0) :
    ∃ gap : Int, 0 < (gap : Real) ∧ ∃ z : Site 2,
      (∀ y ∈ Ld.image (Pdual.shift (-z)),
        D.primalEmbedding.coordinates (D.dualEmbedding.vertex y) 0 < a) ∧
      (∀ y ∈ Rd.image (Pdual.shift (-z)),
        b < D.primalEmbedding.coordinates (D.dualEmbedding.vertex y) 0) ∧
      ∀ v ∈ (Pdual.orbitBox (Pdual.bufferedRadius N)).image
          (Pdual.shift (-z)),
        (2 * s + (s + gap)) / 3 + Bd <
            D.dualEmbedding.vertexCoord v 1 ∧
          D.dualEmbedding.vertexCoord v 1 <
            (s + 2 * (s + gap)) / 3 - Bd := by
  obtain ⟨gap, hgap, z, hz0, hbox⟩ :=
    D.dualEmbedding.exists_verticalGap_shift_orbitBox_middleThird
      N Bd s
  refine ⟨gap, hgap, z, ?_, ?_, hbox⟩
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
    have huLeft := hLd u hu
    rw [D.coordinates_eq] at huLeft ⊢
    change D.dualEmbedding.vertexCoord u 0 < a at huLeft
    change D.dualEmbedding.vertexCoord (Pdual.shift (-z) u) 0 < a
    rw [D.dualEmbedding.vertexCoord_shift]
    simp [hz0, huLeft]
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
    have huRight := hRd u hu
    rw [D.coordinates_eq] at huRight ⊢
    change b < D.dualEmbedding.vertexCoord u 0 at huRight
    change b < D.dualEmbedding.vertexCoord (Pdual.shift (-z) u) 0
    rw [D.dualEmbedding.vertexCoord_shift]
    simp [hz0, huRight]




theorem translatedFiniteStripPrimal_dualPairConnection_disjoint
    (D : PeriodicPlanarDualPair P Pdual)
    (omega : ConfigSpace (Sym2 V))
    {z : Site 2} {Bp Bd r s : Real} {gap : Int} {np N : Nat}
    {Lp Rp : Finset V} {Ld Rd : Finset W}
    (hBp0 : 0 ≤ Bp) (hBd0 : 0 ≤ Bd)
    (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ Bp)
    (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ Bd)
    (hgap : 0 < (gap : Real))
    (hLpDeep : (Lp : Set V) ⊆
      D.primalEmbedding.rightHalfPlaneVertices (r + Bp))
    (hLd : ∀ y ∈ Ld.image (Pdual.shift (-z)),
      D.primalEmbedding.coordinates (D.dualEmbedding.vertex y) 0 <
        r - Bp - 1)
    (hRd : ∀ y ∈ Rd.image (Pdual.shift (-z)),
      r + np + Bp + 1 <
        D.primalEmbedding.coordinates (D.dualEmbedding.vertex y) 0)
    (hbox : ∀ v ∈ (Pdual.orbitBox (Pdual.bufferedRadius N)).image
        (Pdual.shift (-z)),
      (2 * s + (s + gap)) / 3 + Bd <
          D.dualEmbedding.vertexCoord v 1 ∧
        D.dualEmbedding.vertexCoord v 1 <
          (s + 2 * (s + gap)) / 3 - Bd)
    (hprimal : omega ∈
      D.primalEmbedding.finiteStripJoinedBoundaryArmEvent
        r s (s + gap) np Lp Rp)
    (hdual : dualConfigEquiv D.edgeDual omega ∈
      Pdual.translatedFiniteInfinitePairConnectionEvent z Ld Rd N) : False := by
  have hsgap : s < s + (gap : Real) := by linarith
  have hpgeom :=
    D.primalEmbedding.finiteStripJoinedBoundaryArmEvent_barrierGeometry
      hBp hBp0 hsgap hLpDeep hprimal
  dsimp only at hpgeom
  obtain ⟨hab, hCD, xl, xu, xj, lower, upper,
    hlowerNil, hupperNil, hlowerOpen, hupperOpen,
    hlowerBottom, hupperTop, hlowerX, hupperX⟩ := hpgeom
  obtain ⟨yl, hyl, yr, hyr, dual, hdualSupport, hdualOpen⟩ :=
    Pdual.translatedFiniteInfinitePairConnectionEvent_graphWalk hdual
  have hdualLeft := hLd yl hyl
  have hdualRight := hRd yr hyr
  have hylr : yl ≠ yr := by
    intro heq
    subst yr
    linarith
  have hdualNil : ¬ dual.Nil := SimpleGraph.Walk.not_nil_of_ne hylr
  have hdualY' : ∀ t : unitInterval,
      (2 * s + (s + (gap : Real))) / 3 <
          D.dualEmbedding.coordinates (D.dualEmbedding.walkArc dual t) 1 ∧
        D.dualEmbedding.coordinates (D.dualEmbedding.walkArc dual t) 1 <
          (s + 2 * (s + (gap : Real))) / 3 := by
    apply D.dualEmbedding.walkArc_coord_strict_bounds_of_support
      hBd0 hBd (1 : Fin 2) dual
    intro v hv
    exact hbox v (hdualSupport v hv)
  have hdualY : ∀ t : unitInterval,
      (2 * s + (s + (gap : Real))) / 3 <
          D.primalEmbedding.coordinates (D.dualEmbedding.walkArc dual t) 1 ∧
        D.primalEmbedding.coordinates (D.dualEmbedding.walkArc dual t) 1 <
          (s + 2 * (s + (gap : Real))) / 3 := by
    intro t
    simpa only [D.coordinates_eq] using hdualY' t
  exact D.no_open_dual_transverse_walk_of_joined_primal_arms
    omega hab hCD lower upper dual hlowerNil hupperNil hdualNil
    hlowerOpen hupperOpen hdualOpen hdualLeft hdualRight
    hlowerBottom hupperTop hlowerX hupperX hdualY





theorem exists_verticalGap_translatedFiniteStripPrimal_dualPairConnection_disjoint
    (D : PeriodicPlanarDualPair P Pdual)
    {Bp Bd r s : Real} {np N : Nat}
    {Lp Rp : Finset V} {Ld Rd : Finset W}
    (hBp0 : 0 ≤ Bp) (hBd0 : 0 ≤ Bd)
    (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ Bp)
    (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ Bd)
    (hLpDeep : (Lp : Set V) ⊆
      D.primalEmbedding.rightHalfPlaneVertices (r + Bp))
    (hLd : ∀ y ∈ Ld,
      D.primalEmbedding.coordinates (D.dualEmbedding.vertex y) 0 <
        r - Bp - 1)
    (hRd : ∀ y ∈ Rd,
      r + np + Bp + 1 <
        D.primalEmbedding.coordinates (D.dualEmbedding.vertex y) 0) :
    ∃ gap : Int, ∃ z : Site 2, 0 < (gap : Real) ∧
      ∀ omega : ConfigSpace (Sym2 V),
        omega ∈ D.primalEmbedding.finiteStripJoinedBoundaryArmEvent
            r s (s + gap) np Lp Rp →
          dualConfigEquiv D.edgeDual omega ∈
              Pdual.translatedFiniteInfinitePairConnectionEvent z Ld Rd N →
            False := by
  obtain ⟨gap, hgap, z, hLdZ, hRdZ, hbox⟩ :=
    D.exists_verticalGap_translatedDualPlacement N Bd s
      (a := r - Bp - 1) (b := r + np + Bp + 1) hLd hRd
  refine ⟨gap, z, hgap, ?_⟩
  intro omega hprimal hdual
  exact D.translatedFiniteStripPrimal_dualPairConnection_disjoint
    omega hBp0 hBd0 hBp hBd hgap hLpDeep hLdZ hRdZ hbox hprimal hdual





theorem exists_verticalGap_translatedFiniteEvents_measureReal_add_le_one
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {Bp Bd r s : Real} {np N : Nat}
    {Lp Rp : Finset V} {Ld Rd : Finset W}
    (hBp0 : 0 ≤ Bp) (hBd0 : 0 ≤ Bd)
    (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ Bp)
    (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ Bd)
    (hLpDeep : (Lp : Set V) ⊆
      D.primalEmbedding.rightHalfPlaneVertices (r + Bp))
    (hLd : ∀ y ∈ Ld,
      D.primalEmbedding.coordinates (D.dualEmbedding.vertex y) 0 <
        r - Bp - 1)
    (hRd : ∀ y ∈ Rd,
      r + np + Bp + 1 <
        D.primalEmbedding.coordinates (D.dualEmbedding.vertex y) 0) :
    ∃ gap : Int, ∃ z : Site 2, 0 < (gap : Real) ∧
      mu.real (D.primalEmbedding.finiteStripJoinedBoundaryArmEvent
          r s (s + gap) np Lp Rp) +
        mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          Pdual.translatedFiniteInfinitePairConnectionEvent z Ld Rd N) ≤ 1 := by
  obtain ⟨gap, z, hgap, hdisjoint⟩ :=
    D.exists_verticalGap_translatedFiniteStripPrimal_dualPairConnection_disjoint
      hBp0 hBd0 hBp hBd hLpDeep hLd hRd
  let A := D.primalEmbedding.finiteStripJoinedBoundaryArmEvent
    r s (s + gap) np Lp Rp
  let C := (dualConfigEquiv D.edgeDual) ⁻¹'
    Pdual.translatedFiniteInfinitePairConnectionEvent z Ld Rd N
  have hAC : Disjoint A C := by
    rw [Set.disjoint_left]
    intro omega hA hC
    exact hdisjoint omega hA hC
  have hCmeas : MeasurableSet C :=
    (Pdual.translatedFiniteInfinitePairConnectionEvent_measurableSet
      z Ld Rd N).preimage
        (continuous_dualConfigEquiv D.edgeDual).measurable
  have hunion : mu.real (A ∪ C) ≤ 1 := measureReal_le_one
  rw [measureReal_union hAC hCmeas] at hunion
  exact ⟨gap, z, hgap, hunion⟩




theorem exists_verticalGap_not_both_translatedFiniteEvents_highProbability
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {Bp Bd r s epsilon : Real} {np N : Nat}
    {Lp Rp : Finset V} {Ld Rd : Finset W}
    (hepsilon : epsilon < 1 / 2)
    (hBp0 : 0 ≤ Bp) (hBd0 : 0 ≤ Bd)
    (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ Bp)
    (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ Bd)
    (hLpDeep : (Lp : Set V) ⊆
      D.primalEmbedding.rightHalfPlaneVertices (r + Bp))
    (hLd : ∀ y ∈ Ld,
      D.primalEmbedding.coordinates (D.dualEmbedding.vertex y) 0 <
        r - Bp - 1)
    (hRd : ∀ y ∈ Rd,
      r + np + Bp + 1 <
        D.primalEmbedding.coordinates (D.dualEmbedding.vertex y) 0) :
    ∃ gap : Int, ∃ z : Site 2, 0 < (gap : Real) ∧
      ¬(1 - epsilon <
          mu.real (D.primalEmbedding.finiteStripJoinedBoundaryArmEvent
            r s (s + gap) np Lp Rp) ∧
        1 - epsilon < mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          Pdual.translatedFiniteInfinitePairConnectionEvent z Ld Rd N)) := by
  obtain ⟨gap, z, hgap, hsum⟩ :=
    D.exists_verticalGap_translatedFiniteEvents_measureReal_add_le_one
      mu hBp0 hBd0 hBp hBd hLpDeep hLd hRd
  refine ⟨gap, z, hgap, ?_⟩
  rintro ⟨hprimal, hdual⟩
  linarith

end PeriodicPlanarDualPair

end StatMech.FK.PeriodicPlanar
