/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.TriangularOffCentre
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.HexagonalSharpness

/-!
# Translated hexagonal boxes and domination by wired boundary conditions

Translated boxes of the hexagonal lattice, translation invariance of their wired crossing
probabilities, and the comparison showing that a wired FK measure on a large box, seen on a
translated sub-box, is dominated by the wired measure of the sub-box.

## i. Overview

`hexagonalTransBox R x` is the box of radius `R` centered at the site `x`; its hexagonal vertices
are the pairs `(z, b)` with `z` in the box. The translation map `hexagonalTransEquiv R x` from the
centered box sends `(z, b)` to `(z + x.1, b)` if `x` is black, and composes with the color-swapping
reflection `hexagonalReflect` if `x` is white, so that the root `(0, false)` goes to `x`; it is a
graph isomorphism (`hexagonalTransEquiv_adj`). Hence the wired FK probability that the center is
joined to the shell of radius `k` does not depend on `x`
(`hexagonalTransShellEvent_betaMean_eq_centeredFullMass`). If `x.1 ∈ Λ_n` and `2k < n`, the
translated box of radius `2k` sits inside the box of radius `2n` away from its boundary, and for
every increasing event `A` of the translated box, its probability under the measure wired at the
large box is at most its probability under the measure wired at the translated box
(`hexagonalTransBox_activeBCMean_le`, `q ≥ 1`), using the induced-wiring lemmas of
`TriangularOffCentre` (comparison of boundary conditions and domain Markov property).

Fidelity: all results are unconditional (with `q ≥ 1`, `β > 0` where stated).

## ii. Key results

- `hexagonalTransShellEvent_betaMean_eq_centeredFullMass` : translation invariance of wired
  shell-crossing probabilities. Unconditional.
- `hexagonalTransBox_activeBCMean_le` : increasing events of a translated sub-box are less likely
  under the outer wired measure than under the sub-box wired measure. Unconditional (`q ≥ 1`).

## iii. Table of contents

- A. Translated hexagonal boxes
- B. Shell events and translation invariance
- C. Domination by the wired measure of a sub-box

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), §§4.2–4.3.
- H. Duminil-Copin, A. Raoufi and V. Tassion, *Sharp phase transition for the random-cluster
  and Potts models via decision trees*, Ann. of Math. 189 (2019) 75–99.
-/

@[expose] public section

open scoped BigOperators
open Finset Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice
open StatMech.OSSS.RevealmentConstruction
open StatMech.OSSS.FiniteGraphBoundaryDifferential

noncomputable section

/-! ## A. Translated hexagonal boxes -/

/-- The box of radius `R` of the hexagonal lattice centered at `x`. -/
abbrev hexagonalTransBox (R : Nat) (x : Site 2) : Set (Site 2) :=
  StatMech.FK.fvs_transBox 2 R x

/-- The hexagonal vertices `(z, b)` with `z` in the translated box `x + Λ_R`. -/
abbrev HexagonalTransBoxVertex (R : Nat) (x : Site 2) :=
  ↑((hexagonalTransBox R x) ×ˢ (Set.univ : Set Bool))

/-- Translated-box vertices as pairs of a box site and a color. -/
def hexagonalTransBoxVertexEquiv (R : Nat) (x : Site 2) :
    (StatMech.FK.fvs_transBoxVerts 2 R x × Bool) ≃
      HexagonalTransBoxVertex R x where
  toFun y := ⟨(y.1.1, y.2), ⟨y.1.2, Set.mem_univ _⟩⟩
  invFun y := (⟨y.1.1, y.2.1⟩, y.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The translated-box vertices form a finite type. -/
noncomputable instance (R : Nat) (x : Site 2) :
    Fintype (HexagonalTransBoxVertex R x) :=
  Fintype.ofEquiv (StatMech.FK.fvs_transBoxVerts 2 R x × Bool)
    (hexagonalTransBoxVertexEquiv R x)

/-- The inclusion of translated-box vertices into the hexagonal lattice. -/
def hexagonalTransBoxEmbedding (R : Nat) (x : Site 2) :
    HexagonalTransBoxVertex R x → HexVertex :=
  Subtype.val

/-- The hexagonal lattice restricted to the translated box. -/
def hexagonalTransBoxGraph (R : Nat) (x : Site 2) :
    SimpleGraph (HexagonalTransBoxVertex R x) :=
  SimpleGraph.comap (hexagonalTransBoxEmbedding R x) hexagonalGraph

/-- Classical decidability of adjacency in the translated box graph. -/
noncomputable instance (R : Nat) (x : Site 2) :
    DecidableRel (hexagonalTransBoxGraph R x).Adj := Classical.decRel _

/-- The inclusion of a translated box into a centered box containing it. -/
def hexagonalTransBoxIncl {R N : Nat} {x : Site 2}
    (hsub : hexagonalTransBox R x ⊆ box 2 N) :
    HexagonalTransBoxVertex R x -> HexagonalBoxVertex N :=
  fun y => ⟨y.1, ⟨hsub y.2.1, Set.mem_univ _⟩⟩

@[simp] lemma hexagonalTransBoxIncl_val {R N : Nat} {x : Site 2}
    (hsub : hexagonalTransBox R x ⊆ box 2 N)
    (y : HexagonalTransBoxVertex R x) :
    (hexagonalTransBoxIncl hsub y).1.1 = y.1.1 := rfl

lemma hexagonalTransBoxIncl_injective {R N : Nat} {x : Site 2}
    (hsub : hexagonalTransBox R x ⊆ box 2 N) :
    Function.Injective (hexagonalTransBoxIncl hsub) := by
  intro y z hyz
  apply Subtype.ext
  exact congrArg (fun w : HexagonalBoxVertex N => (w : HexVertex)) hyz

/-- The boundary of the translated box: sites at sup-distance exactly `R` from `x`. -/
def hexagonalTransBoxBoundary (R : Nat) (x : Site 2)
    (y : HexagonalTransBoxVertex R x) : Prop :=
  y.1.1 - x ∈ vertexBoundary 2 R

open scoped Classical in
/-- The sites of the translated box at sup-distance `k` from `x`. -/
noncomputable def hexagonalTransBoxShell (R k : Nat) (x : Site 2) :
    Finset (HexagonalTransBoxVertex R x) :=
  Finset.univ.filter fun y => y.1.1 - x ∈ vertexBoundary 2 k

/-- The vertex `x` as the center of the translated box. -/
def hexagonalTransBoxCenter (R : Nat) (x : HexVertex) :
    HexagonalTransBoxVertex R x.1 :=
  ⟨x, by simp [StatMech.FK.fvs_transBox]⟩

/-- The point reflection `(z, b) ↦ (-z, !b)` of the hexagonal lattice, which swaps the two colors.
-/
def hexagonalReflect (y : HexVertex) : HexVertex := (-y.1, !y.2)

lemma hexagonalReflect_adj (u v : HexVertex) :
    hexagonalGraph.Adj u v ↔
      hexagonalGraph.Adj (hexagonalReflect u) (hexagonalReflect v) := by
  rw [hexagonalGraph_adj, hexagonalGraph_adj]
  constructor
  · rintro (⟨hu, hv, i, h⟩ | ⟨hv, hu, i, h⟩)
    · refine Or.inr ⟨by simp [hexagonalReflect, hv],
          by simp [hexagonalReflect, hu], i, ?_⟩
      dsimp [hexagonalReflect]
      calc
        -u.1 - -v.1 = v.1 - u.1 := by abel
        _ = hexagonalStep i := h
    · refine Or.inl ⟨by simp [hexagonalReflect, hu],
          by simp [hexagonalReflect, hv], i, ?_⟩
      dsimp [hexagonalReflect]
      calc
        -v.1 - -u.1 = u.1 - v.1 := by abel
        _ = hexagonalStep i := h
  · rintro (⟨hu, hv, i, h⟩ | ⟨hv, hu, i, h⟩)
    · have hu' : u.2 = true := by
        cases hu0 : u.2 <;> simp_all [hexagonalReflect]
      have hv' : v.2 = false := by
        cases hv0 : v.2 <;> simp_all [hexagonalReflect]
      refine Or.inr ⟨hv', hu', i, ?_⟩
      dsimp [hexagonalReflect] at h
      calc
        u.1 - v.1 = -v.1 - -u.1 := by abel
        _ = hexagonalStep i := h
    · have hv' : v.2 = true := by
        cases hv0 : v.2 <;> simp_all [hexagonalReflect]
      have hu' : u.2 = false := by
        cases hu0 : u.2 <;> simp_all [hexagonalReflect]
      refine Or.inl ⟨hu', hv', i, ?_⟩
      dsimp [hexagonalReflect] at h
      calc
        v.1 - u.1 = -u.1 - -v.1 := by abel
        _ = hexagonalStep i := h

/-- The lattice isomorphism from the centered box to the translated box sending the root `(0,
false)` to `x`: a translation if `x` is black, a translation composed with `hexagonalReflect` if `x`
is white. -/
def hexagonalTransEquiv (R : Nat) (x : HexVertex) :
    HexagonalBoxVertex R ≃ HexagonalTransBoxVertex R x.1 where
  toFun y := if x.2 then
      ⟨(x.1 - y.1.1, !y.1.2), by
        refine ⟨?_, Set.mem_univ _⟩
        simpa [StatMech.FK.fvs_transBox] using y.2.1⟩
    else
      ⟨(y.1.1 + x.1, y.1.2), by
        refine ⟨?_, Set.mem_univ _⟩
        simpa [StatMech.FK.fvs_transBox] using y.2.1⟩
  invFun y := if x.2 then
      ⟨(x.1 - y.1.1, !y.1.2), by
        refine ⟨?_, Set.mem_univ _⟩
        intro i
        have hi := y.2.1 i
        change (x.1 i - y.1.1 i).natAbs ≤ R
        rw [show x.1 i - y.1.1 i = -(y.1.1 i - x.1 i) by ring,
          Int.natAbs_neg]
        exact hi⟩
    else
      ⟨(y.1.1 - x.1, y.1.2), by
        refine ⟨?_, Set.mem_univ _⟩
        simpa [StatMech.FK.fvs_transBox] using y.2.1⟩
  left_inv y := by
    cases hx : x.2
    · simp only [Bool.false_eq_true, ↓reduceIte]
      apply Subtype.ext
      apply Prod.ext
      · ext i
        simp
      · rfl
    · simp only [↓reduceIte]
      apply Subtype.ext
      apply Prod.ext
      · ext i
        simp
      · simp
  right_inv y := by
    cases hx : x.2
    · simp only [Bool.false_eq_true, ↓reduceIte]
      apply Subtype.ext
      apply Prod.ext
      · ext i
        simp
      · rfl
    · simp only [↓reduceIte]
      apply Subtype.ext
      apply Prod.ext
      · ext i
        simp
      · simp

lemma hexagonalTransEquiv_adj (R : Nat) (x : HexVertex)
    (u v : HexagonalBoxVertex R) :
    (hexagonalBoxGraph R).Adj u v ↔
      (hexagonalTransBoxGraph R x.1).Adj
        (hexagonalTransEquiv R x u)
        (hexagonalTransEquiv R x v) := by
  cases hx : x.2
  · simp only [hexagonalBoxGraph, hexagonalTransBoxGraph,
      SimpleGraph.comap_adj, hexagonalBoxEmbedding,
      hexagonalTransBoxEmbedding, hexagonalTransEquiv, hx,
      Bool.false_eq_true, ↓reduceIte]
    exact (hexagonal.shift_adj x.1 u.1 v.1).symm
  · have href := hexagonalReflect_adj (hexagonalBoxEmbedding R u)
        (hexagonalBoxEmbedding R v)
    have hshift := (hexagonal.shift_adj x.1
      (hexagonalReflect (hexagonalBoxEmbedding R u))
      (hexagonalReflect (hexagonalBoxEmbedding R v))).symm
    simp only [hexagonalBoxGraph, hexagonalTransBoxGraph,
      SimpleGraph.comap_adj, hexagonalBoxEmbedding,
      hexagonalTransBoxEmbedding, hexagonalTransEquiv, hx, ↓reduceIte]
    constructor
    · intro huv
      have hs := hshift.mp (href.mp huv)
      simpa [hexagonal, hexTranslate_apply, hexagonalReflect, hexagonalBoxEmbedding,
        sub_eq_add_neg, add_comm] using hs
    · intro huv
      have hs : hexagonalGraph.Adj
          (hexagonal.shift x.1 (hexagonalReflect u.1))
          (hexagonal.shift x.1 (hexagonalReflect v.1)) := by
        simpa [hexagonal, hexTranslate_apply, hexagonalReflect,
          sub_eq_add_neg, add_comm] using huv
      exact href.mpr (hshift.mpr hs)

@[simp] lemma hexagonalTransEquiv_center (R : Nat) (x : HexVertex) :
    hexagonalTransEquiv R x (hexagonalBoxRoot R) =
      hexagonalTransBoxCenter R x := by
  rcases x with ⟨x, b⟩
  cases b <;> apply Subtype.ext <;>
    simp [hexagonalTransEquiv, hexagonalBoxRoot, hexagonalTransBoxCenter]

open scoped Classical in
lemma hexagonalTransEquiv_mem_shell (R k : Nat) (x : HexVertex)
    (y : HexagonalBoxVertex R) :
    hexagonalTransEquiv R x y ∈ hexagonalTransBoxShell R k x.1 ↔
      y ∈ hexagonalBoxShell R k := by
  cases hx : x.2 <;>
    simp [hexagonalTransEquiv, hx, hexagonalTransBoxShell, hexagonalBoxShell,
      sub_eq_add_neg, Int.natAbs_neg]

/-- The first endpoint of a translated-box edge. -/
noncomputable def hexagonalTransBoxEndU (R : Nat) (x : Site 2) :
    (hexagonalTransBoxGraph R x).edgeSet -> HexagonalTransBoxVertex R x :=
  fun e => e.1.out.1

/-- The second endpoint of a translated-box edge. -/
noncomputable def hexagonalTransBoxEndV (R : Nat) (x : Site 2) :
    (hexagonalTransBoxGraph R x).edgeSet -> HexagonalTransBoxVertex R x :=
  fun e => e.1.out.2

/-! ## B. Shell events and translation invariance -/

/-- The event that the center of the translated box is joined to its shell of radius `k`. -/
def hexagonalTransShellEvent (R k : Nat) (x : HexVertex) :
    Set (ConfigSpace (hexagonalTransBoxGraph R x.1).edgeSet) :=
  openCrossEvent (hexagonalTransBoxEndU R x.1) (hexagonalTransBoxEndV R x.1)
    (hexagonalTransBoxCenter R x) (hexagonalTransBoxShell R k x.1)

/-- The event that the origin is joined to the shell of radius `k` in the centered box. -/
def hexagonalCenteredShellEvent (R k : Nat) :
    Set (ConfigSpace (hexagonalBoxGraph R).edgeSet) :=
  openCrossEvent (hexagonalBoxEndU R) (hexagonalBoxEndV R)
    (hexagonalBoxRoot R) (hexagonalBoxShell R k)

lemma hexagonalTransShellEvent_increasing (R k : Nat) (x : HexVertex) :
    IsIncreasing (hexagonalTransShellEvent R k x) :=
  openCrossEvent_isIncreasing _ _ _ _

lemma hexagonalCenteredShellEvent_increasing (R k : Nat) :
    IsIncreasing (hexagonalCenteredShellEvent R k) :=
  openCrossEvent_isIncreasing _ _ _ _

/-- The centered shell-crossing event for configurations of all vertex pairs of the box. -/
def hexagonalCenteredShellFullEvent (R k : Nat) :
    Set (ConfigSpace (Sym2 (HexagonalBoxVertex R))) :=
  {omega | ∃ y ∈ hexagonalBoxShell R k,
    (openSub (hexagonalBoxGraph R) omega).Reachable (hexagonalBoxRoot R) y}

/-- The translated shell-crossing event for configurations of all vertex pairs of the translated
box. -/
def hexagonalTransShellFullEvent (R k : Nat) (x : HexVertex) :
    Set (ConfigSpace (Sym2 (HexagonalTransBoxVertex R x.1))) :=
  {omega | ∃ y ∈ hexagonalTransBoxShell R k x.1,
    (openSub (hexagonalTransBoxGraph R x.1) omega).Reachable
      (hexagonalTransBoxCenter R x) y}

lemma restrictActive_preimage_hexagonalCenteredShellEvent
    (R k : Nat) :
    restrictActive (hexagonalBoxGraph R) ⁻¹'
        hexagonalCenteredShellEvent R k =
      hexagonalCenteredShellFullEvent R k := by
  ext omega
  change ConnOpenSet (hexagonalBoxEndU R) (hexagonalBoxEndV R)
      (restrictActive (hexagonalBoxGraph R) omega)
      (hexagonalBoxRoot R) (hexagonalBoxShell R k) ↔
    ∃ y ∈ hexagonalBoxShell R k,
      (openSub (hexagonalBoxGraph R) omega).Reachable (hexagonalBoxRoot R) y
  unfold hexagonalBoxEndU hexagonalBoxEndV
  rw [connOpenSet_edgeSet_iff_openSub]
  rw [openSub_extendActive_restrictActive_eq]
  simp

lemma restrictActive_preimage_hexagonalTransShellEvent
    (R k : Nat) (x : HexVertex) :
    restrictActive (hexagonalTransBoxGraph R x.1) ⁻¹'
        hexagonalTransShellEvent R k x =
      hexagonalTransShellFullEvent R k x := by
  ext omega
  change ConnOpenSet (hexagonalTransBoxEndU R x.1)
      (hexagonalTransBoxEndV R x.1)
      (restrictActive (hexagonalTransBoxGraph R x.1) omega)
      (hexagonalTransBoxCenter R x) (hexagonalTransBoxShell R k x.1) ↔
    ∃ y ∈ hexagonalTransBoxShell R k x.1,
      (openSub (hexagonalTransBoxGraph R x.1) omega).Reachable
        (hexagonalTransBoxCenter R x) y
  unfold hexagonalTransBoxEndU hexagonalTransBoxEndV
  rw [connOpenSet_edgeSet_iff_openSub]
  rw [openSub_extendActive_restrictActive_eq]
  simp

lemma reCfgIso_preimage_hexagonalCenteredShellFullEvent
    (R k : Nat) (x : HexVertex) :
    reCfgIso (hexagonalTransEquiv R x) ⁻¹'
        hexagonalCenteredShellFullEvent R k =
      hexagonalTransShellFullEvent R k x := by
  ext omega
  let sigma := hexagonalTransEquiv R x
  let iso := fvs_openSubIso (hexagonalBoxGraph R)
    (hexagonalTransBoxGraph R x.1) sigma
    (hexagonalTransEquiv_adj R x) omega
  constructor
  · rintro ⟨y, hy, hreach⟩
    refine ⟨sigma y, (hexagonalTransEquiv_mem_shell R k x y).2 hy, ?_⟩
    rw [← hexagonalTransEquiv_center R x]
    exact iso.reachable_iff.mpr hreach
  · rintro ⟨y, hy, hreach⟩
    let y0 : HexagonalBoxVertex R := sigma.symm y
    refine ⟨y0, ?_, ?_⟩
    · apply (hexagonalTransEquiv_mem_shell R k x y0).1
      simpa [sigma, y0] using hy
    · apply iso.reachable_iff.mp
      change (openSub (hexagonalTransBoxGraph R x.1) omega).Reachable
        (sigma (hexagonalBoxRoot R)) (sigma y0)
      rw [hexagonalTransEquiv_center]
      simpa [sigma, y0] using hreach

lemma hexagonalTransEquiv_boundary (R : Nat) (x : HexVertex)
    (y : HexagonalBoxVertex R) :
    y ∈ hexagonalBoxShell R R ↔
      hexagonalTransBoxBoundary R x.1
        (hexagonalTransEquiv R x y) := by
  cases hx : x.2 <;>
    simp [hexagonalBoxShell, hexagonalTransBoxBoundary,
      hexagonalTransEquiv, hx, sub_eq_add_neg, Int.natAbs_neg]

open scoped Classical in
lemma hexagonalTransShellEvent_activeBCMean_eq_centeredFullMass
    (R k : Nat) (x : HexVertex) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    activeBCMean (hexagonalTransBoxGraph R x.1)
        (boundaryCliqueGraph (hexagonalTransBoxBoundary R x.1))
        (fun _ => p) q
        ((hexagonalTransShellEvent R k x).indicator fun _ => (1 : Real)) =
      ∑ omega : ConfigSpace (Sym2 (HexagonalBoxVertex R)),
        (hexagonalCenteredShellFullEvent R k).indicator
            (fun _ => (1 : Real)) omega *
          wiredFkProb (hexagonalBoxGraph R)
            (fun y => y ∈ hexagonalBoxShell R R) p q omega := by
  rw [activeBCMean_boundaryClique_eq_wired
    (hexagonalTransBoxGraph R x.1) (hexagonalTransBoxBoundary R x.1)
    hp hp1 hq]
  calc
    (∑ omega : ConfigSpace (Sym2 (HexagonalTransBoxVertex R x.1)),
        (hexagonalTransShellEvent R k x).indicator (fun _ => (1 : Real))
            (restrictActive (hexagonalTransBoxGraph R x.1) omega) *
          wiredFkProb (hexagonalTransBoxGraph R x.1)
            (hexagonalTransBoxBoundary R x.1) p q omega) =
      ∑ omega : ConfigSpace (Sym2 (HexagonalTransBoxVertex R x.1)),
        (hexagonalTransShellFullEvent R k x).indicator
            (fun _ => (1 : Real)) omega *
          wiredFkProb (hexagonalTransBoxGraph R x.1)
            (hexagonalTransBoxBoundary R x.1) p q omega := by
      apply Finset.sum_congr rfl
      intro omega _
      have hevent :
          restrictActive (hexagonalTransBoxGraph R x.1) omega ∈
              hexagonalTransShellEvent R k x ↔
            omega ∈ hexagonalTransShellFullEvent R k x := by
        rw [← Set.mem_preimage]
        exact Set.ext_iff.mp
          (restrictActive_preimage_hexagonalTransShellEvent R k x) omega
      by_cases h : restrictActive (hexagonalTransBoxGraph R x.1) omega ∈
          hexagonalTransShellEvent R k x
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hevent.mp h)]
      · rw [Set.indicator_of_notMem h,
          Set.indicator_of_notMem (mt hevent.mpr h)]
    _ = ∑ omega : ConfigSpace (Sym2 (HexagonalBoxVertex R)),
        (hexagonalCenteredShellFullEvent R k).indicator
            (fun _ => (1 : Real)) omega *
          wiredFkProb (hexagonalBoxGraph R)
            (fun y => y ∈ hexagonalBoxShell R R) p q omega := by
      rw [← cdc_eventMassProb_reCfgIso_inv
        (hexagonalTransEquiv R x)
        (wiredFkProb (hexagonalBoxGraph R)
          (fun y => y ∈ hexagonalBoxShell R R) p q)
        (wiredFkProb (hexagonalTransBoxGraph R x.1)
          (hexagonalTransBoxBoundary R x.1) p q)
        (fun omega => fvs_wiredFkProb_reCfgIso
          (hexagonalBoxGraph R) (hexagonalTransBoxGraph R x.1)
          (fun y => y ∈ hexagonalBoxShell R R)
          (hexagonalTransBoxBoundary R x.1)
          (hexagonalTransEquiv R x)
          (hexagonalTransEquiv_adj R x)
          (hexagonalTransEquiv_boundary R x) p q omega)
        (hexagonalCenteredShellFullEvent R k)]
      rw [reCfgIso_preimage_hexagonalCenteredShellFullEvent]

open scoped Classical in
lemma hexagonalTransShellEvent_betaMean_eq_centeredFullMass
    (R k : Nat) (x : HexVertex) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta) :
    activeBCMean (hexagonalTransBoxGraph R x.1)
        (boundaryCliqueGraph (hexagonalTransBoxBoundary R x.1))
        (betaParams (fun _ => 1) beta) q
        ((hexagonalTransShellEvent R k x).indicator fun _ => (1 : Real)) =
      ∑ omega : ConfigSpace (Sym2 (HexagonalBoxVertex R)),
        (hexagonalCenteredShellFullEvent R k).indicator
            (fun _ => (1 : Real)) omega *
          wiredFkProb (hexagonalBoxGraph R)
            (fun y => y ∈ hexagonalBoxShell R R)
            (1 - Real.exp (-beta)) q omega := by
  have hp : 0 < 1 - Real.exp (-beta) := by
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : 1 - Real.exp (-beta) < 1 := by
    linarith [Real.exp_pos (-beta)]
  have hparam : betaParams (fun _ : Sym2 (HexagonalTransBoxVertex R x.1) => 1) beta =
      fun _ => 1 - Real.exp (-beta) := by
    funext e
    simp [betaParams]
  rw [hparam]
  exact hexagonalTransShellEvent_activeBCMean_eq_centeredFullMass
    R k x hp hp1 hq

/-! ## C. Domination by the wired measure of a sub-box -/

lemma hexagonalTransBox_subset_double
    {n k : Nat} {x : Site 2} (hx : x ∈ box 2 n) (hkn : 2 * k < n) :
    hexagonalTransBox (2 * k) x ⊆ box 2 (2 * n) := by
  intro y hy i
  have hyi : ((y - x) i).natAbs <= 2 * k := hy i
  have hxi : (x i).natAbs <= n := hx i
  have heq : y i = (y i - x i) + x i := by ring
  calc
    (y i).natAbs = ((y i - x i) + x i).natAbs := by rw [← heq]
    _ <= (y i - x i).natAbs + (x i).natAbs := Int.natAbs_add_le _ _
    _ = ((y - x) i).natAbs + (x i).natAbs := by simp [Pi.sub_apply]
    _ <= 2 * k + n := Nat.add_le_add hyi hxi
    _ <= 2 * n := by omega

open scoped Classical in
lemma hexagonalTransBox_outer_margin
    {n k : Nat} {x : Site 2} (hx : x ∈ box 2 n) (hkn : 2 * k < n)
    (y : HexagonalTransBoxVertex (2 * k) x) :
    hexagonalTransBoxIncl (hexagonalTransBox_subset_double hx hkn) y ∉
      hexagonalBoxShell (2 * n) (2 * n) := by
  intro hybdry
  have hycoord := (Finset.mem_filter.mp hybdry).2.2
  have hybox : y.1.1 ∈ box 2 (2 * n - 1) := by
    intro i
    have hyi : ((y.1.1 - x) i).natAbs <= 2 * k := y.2.1 i
    have hxi : (x i).natAbs <= n := hx i
    have heq : y.1.1 i = (y.1.1 i - x i) + x i := by ring
    calc
      (y.1.1 i).natAbs = ((y.1.1 i - x i) + x i).natAbs := by rw [← heq]
      _ <= (y.1.1 i - x i).natAbs + (x i).natAbs := Int.natAbs_add_le _ _
      _ = ((y.1.1 - x) i).natAbs + (x i).natAbs := by simp [Pi.sub_apply]
      _ <= 2 * k + n := Nat.add_le_add hyi hxi
      _ <= 2 * n - 1 := by omega
  exact hycoord hybox

lemma hexagonal_adj_sub_right (x : Site 2) {y z : HexVertex}
    (hyz : hexagonalGraph.Adj y z) :
    hexagonalGraph.Adj (y.1 - x, y.2) (z.1 - x, z.2) := by
  rw [hexagonalGraph_adj] at hyz ⊢
  rcases hyz with ⟨hy, hz, i, h⟩ | ⟨hz, hy, i, h⟩
  · refine Or.inl ⟨hy, hz, i, ?_⟩
    calc
      (z.1 - x) - (y.1 - x) = z.1 - y.1 := by abel
      _ = hexagonalStep i := h
  · refine Or.inr ⟨hz, hy, i, ?_⟩
    calc
      (y.1 - x) - (z.1 - x) = y.1 - z.1 := by abel
      _ = hexagonalStep i := h

lemma hexagonalTransBox_boundary_of_adj_outside
    {R : Nat} (hR : 1 <= R) {x : Site 2}
    (y : HexagonalTransBoxVertex R x) (z : HexVertex)
    (hyz : hexagonalGraph.Adj y.1 z) (hz : z.1 ∉ hexagonalTransBox R x) :
    hexagonalTransBoxBoundary R x y := by
  have hybox : y.1.1 - x ∈ box 2 R := y.2.1
  have hzstep : z.1 - x ∈ box 2 (R + 1) := by
    have hadj : hexagonalGraph.Adj (y.1.1 - x, y.1.2) (z.1 - x, z.2) :=
      hexagonal_adj_sub_right x hyz
    exact hexagonal_adj_mem_box_succ hybox hadj
  refine ⟨hybox, ?_⟩
  intro hsmall
  have hzR : z.1 - x ∈ box 2 R := by
    have hadj : hexagonalGraph.Adj (y.1.1 - x, y.1.2) (z.1 - x, z.2) :=
      hexagonal_adj_sub_right x hyz
    exact hexagonal_adj_mem_box_of_mem_pred hR hsmall hadj
  exact hz hzR

open scoped Classical in
lemma hexagonalTransBox_inducedWiring_le
    {n k : Nat} {x : Site 2} (hx : x ∈ box 2 n)
    (hk : 1 <= k) (hkn : 2 * k < n)
    (psi : ConfigSpace (Sym2 (HexagonalBoxVertex (2 * n)))) :
    ocd_inducedWiring (hexagonalBoxGraph (2 * n))
        (hexagonalTransBoxIncl (hexagonalTransBox_subset_double hx hkn))
        (fun y => y ∈ hexagonalBoxShell (2 * n) (2 * n)) psi <=
      boundaryCliqueGraph (hexagonalTransBoxBoundary (2 * k) x) := by
  let hsub := hexagonalTransBox_subset_double hx hkn
  apply StatMech.FK.ocd_comapInducedWiring_le hexagonalGraph
    (hexagonalTransBoxIncl hsub)
    (fun _ => rfl) (hexagonalTransBoxIncl_injective hsub)
    (fun y => y ∈ hexagonalBoxShell (2 * n) (2 * n))
    (hexagonalTransBoxBoundary (2 * k) x)
  · intro y
    exact hexagonalTransBox_outer_margin hx hkn y
  · intro y z hyz hz
    apply hexagonalTransBox_boundary_of_adj_outside (by omega) y z hyz
    intro hzcoord
    exact hz ⟨hzcoord, Set.mem_univ _⟩

open scoped Classical in
/-- Comparison of boundary conditions for translated hexagonal boxes: for `q ≥ 1` and an increasing
event of the box of radius `2k` at `x`, its probability under the measure wired at `Λ_{2n}` is at
most its probability under the measure wired at the translated box (Grimmett, *The Random-Cluster
Model*, §4.2). -/
theorem hexagonalTransBox_activeBCMean_le
    {n k : Nat} {x : Site 2} (hx : x ∈ box 2 n)
    (hk : 1 <= k) (hkn : 2 * k < n)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    {A : Set (ConfigSpace (hexagonalTransBoxGraph (2 * k) x).edgeSet)}
    (hA : IsIncreasing A) :
    activeBCMean (hexagonalBoxGraph (2 * n))
        (boundaryCliqueGraph
          (fun y => y ∈ hexagonalBoxShell (2 * n) (2 * n)))
        (betaParams (fun _ => 1) beta) q
        (fun rho => A.indicator (fun _ => (1 : Real))
          (ocd_innerRestrictActive
            (hexagonalTransBoxGraph (2 * k) x)
            (hexagonalBoxGraph (2 * n))
            (hexagonalTransBoxIncl
              (hexagonalTransBox_subset_double hx hkn))
            (ocd_comapAdjMatch hexagonalGraph
              (hexagonalTransBoxIncl
                (hexagonalTransBox_subset_double hx hkn))
              (fun _ => rfl)) rho)) <=
      activeBCMean (hexagonalTransBoxGraph (2 * k) x)
        (boundaryCliqueGraph (hexagonalTransBoxBoundary (2 * k) x))
        (betaParams (fun _ => 1) beta) q
        (A.indicator fun _ => (1 : Real)) := by
  let hsub := hexagonalTransBox_subset_double hx hkn
  let iota := hexagonalTransBoxIncl hsub
  have hadjm : ocd_AdjMatch (hexagonalTransBoxGraph (2 * k) x)
      (hexagonalBoxGraph (2 * n)) iota :=
    ocd_comapAdjMatch hexagonalGraph iota (fun _ => rfl)
  have hparam : ocd_ParamCompatible iota
      (betaParams (fun _ => 1) beta)
      (betaParams (fun _ => 1) beta) := by
    intro e
    simp [betaParams]
  have hwire := fun psi => hexagonalTransBox_inducedWiring_le
    hx hk hkn psi
  exact ocd_wired_inner_dominated_activeBCMean
    (hexagonalTransBoxGraph (2 * k) x) (hexagonalBoxGraph (2 * n)) iota
    (fun y => y ∈ hexagonalBoxShell (2 * n) (2 * n))
    (hexagonalTransBoxIncl_injective hsub) hadjm
    (hexagonalTransBoxBoundary (2 * k) x) hparam
    (betaParams_pos (fun _ => by norm_num) hbeta)
    (betaParams_lt_one (fun _ => 1) beta)
    (betaParams_pos (fun _ => by norm_num) hbeta)
    (betaParams_lt_one (fun _ => 1) beta) hq hwire hA

end

end StatMech.FK.PeriodicPlanar
