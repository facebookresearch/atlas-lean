/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.StripDualBlocking

/-!
# A translated dual crossing blocks a primal strip connection

Translated dual pair connections, their probability under the dual measure, and the planar
duality bound: a primal strip event and a translated dual crossing of the strip cannot both have
probability above one half.

## i. Overview

`translatedFiniteInfinitePairConnectionEvent z L R N` is the pair connection event of
`Sheffield.DualTransverse` translated by `z`; under a translation-invariant measure it has the
same probability for every `z`, so the high-probability pair connection holds uniformly in `z`.
Pulled back through the edge duality `dualConfigEquiv D.edgeDual`, this applies to the dual
configuration when the dual measure `D.dualMeasure mu` has a.s. a unique infinite cluster.

Geometrically, for dual sets `Ld` left of `x = r - Bp - 1` and `Rd` right of
`x = r + np + Bp + 1`, a vertical translate `z` and a positive integer gap can be chosen so that
the whole translated buffered dual orbit box lies in the middle third of the horizontal strip
between heights `s` and `s + gap`. A primal open configuration in
`finiteStripJoinedBoundaryArmEvent r s (s + gap) np Lp Rp` joins the lower boundary ray to the
upper boundary ray across this strip, while the translated dual pair connection gives a dual open
path from `Ld` to `Rd` crossing the strip horizontally; a primal and a dual open path cannot cross
(`Sheffield.HalfPlaneBarrier`), so the two events are disjoint and their probabilities add to
at most one.

Headline fidelity.
- `translatedFiniteStripPrimal_dualPairConnection_disjoint`,
  `exists_verticalGap_translatedFiniteEvents_measureReal_add_le_one` and
  `exists_verticalGap_not_both_translatedFiniteEvents_highProbability` are unconditional
  (deterministic planar duality plus geometry; only the embedding bounds `Bp`, `Bd` and the
  placement hypotheses on `Lp`, `Ld`, `Rd` are assumed).
- `PeriodicGraph.exists_uniformRadius_highProbability_translatedFiniteEvent` is conditional on
  translation invariance and a.s. uniqueness of the infinite cluster.
- `PeriodicPlanarDualPair.exists_uniformRadius_highProbability_complementaryDualFiniteEvent` is
  conditional on translation invariance of `mu` and a.s. uniqueness of the dual infinite cluster.
  Used together with a high-probability primal strip estimate (which needs a unique primal
  infinite cluster), it contradicts the bound above: this is a reductio step in Sheffield's proof
  that primal and dual unique infinite clusters cannot coexist.

## ii. Key results

- `translatedFiniteStripPrimal_dualPairConnection_disjoint` : the primal strip event and the
  translated dual crossing are disjoint.
- `exists_verticalGap_not_both_translatedFiniteEvents_highProbability` : they cannot both have
  probability `> 1 - ε` for `ε < 1/2`.
- `PeriodicPlanarDualPair.exists_uniformRadius_highProbability_complementaryDualFiniteEvent` :
  dual uniqueness makes the translated dual crossing likely, uniformly in the translate.

## iii. Table of contents

- A. Translated pair connection events
- B. Pair connections of the dual configuration
- C. Vertical gaps and the duality bound

## iv. References

- S. Sheffield, *Random Surfaces*, Astérisque 304 (2005), Ch. 9.
- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Ch. 6.
-/

@[expose] public section

open MeasureTheory Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

/-! ## A. Translated pair connection events -/

/-- The pair connection event between `L` and `R` at radius `N`, translated by `z`. -/
def PeriodicGraph.translatedFiniteInfinitePairConnectionEvent
    (P : PeriodicGraph V) (z : Site 2) (L R : Finset V) (N : Nat) :
    Set (ConfigSpace (Sym2 V)) :=
  P.translateEvent z (P.finiteInfinitePairConnectionEvent L R N)

/-- The translated pair connection event is measurable. -/
lemma PeriodicGraph.translatedFiniteInfinitePairConnectionEvent_measurableSet
    (P : PeriodicGraph V) (z : Site 2) (L R : Finset V) (N : Nat) :
    MeasurableSet (P.translatedFiniteInfinitePairConnectionEvent z L R N) :=
  P.translateEvent_measurableSet z
    (P.finiteInfinitePairConnectionEvent_measurableSet L R N)

/-- Under a translation-invariant measure, translating the pair connection event does not change its
probability. -/
lemma PeriodicGraph.translatedFiniteInfinitePairConnectionEvent_measureReal
    (P : PeriodicGraph V)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu)
    (z : Site 2) (L R : Finset V) (N : Nat) :
    mu.real (P.translatedFiniteInfinitePairConnectionEvent z L R N) =
      mu.real (P.finiteInfinitePairConnectionEvent L R N) := by
  exact congrArg ENNReal.toReal
    (P.translateEvent_measure_eq mu hTI z
      (P.finiteInfinitePairConnectionEvent_measurableSet L R N))

/-- The lattice translation by `z` as a graph homomorphism of the periodic graph. -/
def PeriodicGraph.shiftGraphHom
    (P : PeriodicGraph V) (z : Site 2) : P.graph →g P.graph where
  toFun := P.shift z
  map_rel' := fun {_ _} h => (P.shift_adj z _ _).2 h

omit [Countable V] in
/-- The translation homomorphism acts as `P.shift z`. -/
@[simp] lemma PeriodicGraph.shiftGraphHom_apply
    (P : PeriodicGraph V) (z : Site 2) (v : V) :
    P.shiftGraphHom z v = P.shift z v := rfl

omit [Countable V] in
/-- On the translated pair connection event there is an open walk between the `-z`-translates of `L`
and `R` inside the `-z`-translate of the buffered orbit box. -/
lemma PeriodicGraph.translatedFiniteInfinitePairConnectionEvent_graphWalk
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

/-- Under translation invariance and a.s. uniqueness, there is an orbit-box radius `n` such that any
two translated boxes are joined with probability `> 1 - ε`, uniformly in the translate `z` of the
event. -/
lemma PeriodicGraph.exists_uniformRadius_highProbability_translatedFiniteEvent
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

/-! ## B. Pair connections of the dual configuration -/

/-- The dual measure of a measurable event is the primal probability of its preimage under the edge
duality. -/
lemma PeriodicPlanarDualPair.dualMeasure_measureReal
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

/-- If `mu` is translation invariant and the dual measure has a.s. a unique infinite cluster, the
translated dual pair connection, pulled back to primal configurations, has probability `> 1 - ε`
uniformly in the translate. -/
lemma PeriodicPlanarDualPair.exists_uniformRadius_highProbability_complementaryDualFiniteEvent
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
  let _ : IsProbabilityMeasure muDual := by
    dsimp only [muDual, PeriodicPlanarDualPair.dualMeasure]
    exact (Measure.isProbabilityMeasure_map_iff
      (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable).mpr inferInstance
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

/-! ## C. Vertical gaps and the duality bound -/

omit [Countable V] in
/-- There are a positive integer gap and a vertical translate `z` placing the `-z`-translated
buffered orbit box, thickened by `B`, in the open middle third of the strip between heights `s` and
`s + gap`. -/
lemma PeriodicPlaneEmbedding.exists_verticalGap_shift_orbitBox_middleThird
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

/-- Dual version of `exists_verticalGap_shift_orbitBox_middleThird` that also keeps `Ld` left of `x
= a` and `Rd` right of `x = b` after the vertical translation. -/
lemma exists_verticalGap_translatedDualPlacement
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

/-- Planar duality: a primal configuration joining the two boundary rays across the strip of height
`gap` and a translated dual open path from `Ld` to `Rd` through the middle third of the strip cannot
occur together. -/
lemma translatedFiniteStripPrimal_dualPairConnection_disjoint
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

/-- There are a gap and a translate for which the primal strip event and the translated dual pair
connection are disjoint. -/
lemma exists_verticalGap_translatedFiniteStripPrimal_dualPairConnection_disjoint
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

/-- For some gap and translate, the probabilities of the primal strip event and of the translated
dual pair connection add to at most one. -/
lemma exists_verticalGap_translatedFiniteEvents_measureReal_add_le_one
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

/-- For `ε < 1/2` and some gap and translate, the primal strip event and the translated dual pair
connection do not both have probability `> 1 - ε`. -/
lemma exists_verticalGap_not_both_translatedFiniteEvents_highProbability
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
