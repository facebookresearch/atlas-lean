/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.OSSS.FiniteGraphBoundaryDifferential
import Code.OSSS.DecisionTreeReindex
import Code.FK.TriHexCoarseGeometry





open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice
open StatMech.OSSS RevealmentConstruction LindebergTree DecisionTree
open StatMech.OSSS.FiniteGraphBoundaryDifferential

abbrev HexagonalBoxVertex (n : Nat) :=
  ↑((box 2 n) ×ˢ (Set.univ : Set Bool))

noncomputable instance (n : Nat) : Fintype (HexagonalBoxVertex n) :=
  ((box_finite 2 n).prod Set.finite_univ).fintype

def hexagonalBoxEmbedding (n : Nat) : HexagonalBoxVertex n → HexVertex :=
  Subtype.val

def hexagonalBoxGraph (n : Nat) : SimpleGraph (HexagonalBoxVertex n) :=
  SimpleGraph.comap (hexagonalBoxEmbedding n) hexagonalGraph

noncomputable instance (n : Nat) : DecidableRel (hexagonalBoxGraph n).Adj :=
  Classical.decRel _

def hexagonalBoxRoot (n : Nat) : HexagonalBoxVertex n :=
  ⟨(0, false), by simp⟩

noncomputable def hexagonalBoxShell (n k : Nat) : Finset (HexagonalBoxVertex n) :=
  Finset.univ.filter fun x => (x.1.1 : Site 2) ∈ vertexBoundary 2 k

noncomputable def hexagonalBoxEndU (n : Nat) :
    (hexagonalBoxGraph n).edgeSet → HexagonalBoxVertex n :=
  fun e => e.1.out.1

noncomputable def hexagonalBoxEndV (n : Nat) :
    (hexagonalBoxGraph n).edgeSet → HexagonalBoxVertex n :=
  fun e => e.1.out.2

@[simp] theorem hexagonalBox_end_coherent
    (n : Nat) (e : (hexagonalBoxGraph n).edgeSet) :
    e.1 = s(hexagonalBoxEndU n e, hexagonalBoxEndV n e) := by
  exact e.1.out_eq.symm

theorem hexagonalBox_end_adj
    (n : Nat) (e : (hexagonalBoxGraph n).edgeSet) :
    (hexagonalBoxGraph n).Adj
      (hexagonalBoxEndU n e) (hexagonalBoxEndV n e) := by
  have he : (hexagonalBoxGraph n).Adj e.1.out.1 e.1.out.2 := by
    rw [← SimpleGraph.mem_edgeSet]
    have hout : s(e.1.out.1, e.1.out.2) = e.1 := e.1.out_eq
    rw [hout]
    exact e.2
  exact he


def hexagonalBoxVertInclLE {n m : Nat} (h : n ≤ m) :
    HexagonalBoxVertex n → HexagonalBoxVertex m :=
  fun x => ⟨x.1, ⟨box_mono 2 h x.2.1, Set.mem_univ _⟩⟩

def hexagonalBoxEdgeLE {n m : Nat} (h : n ≤ m) :
    (hexagonalBoxGraph n).edgeSet → (hexagonalBoxGraph m).edgeSet := fun e =>
  ⟨Sym2.map (hexagonalBoxVertInclLE h) e.1, by
    have hpair : Sym2.map (hexagonalBoxVertInclLE h) e.1 =
        s(hexagonalBoxVertInclLE h e.1.out.1,
          hexagonalBoxVertInclLE h e.1.out.2) := by
      calc
        Sym2.map (hexagonalBoxVertInclLE h) e.1 =
            Sym2.map (hexagonalBoxVertInclLE h)
              s(e.1.out.1, e.1.out.2) := by
          exact congrArg (Sym2.map (hexagonalBoxVertInclLE h))
            e.1.out_eq.symm
        _ = _ := by rw [Sym2.map_mk]
    rw [hpair, SimpleGraph.mem_edgeSet]
    have he : (hexagonalBoxGraph n).Adj e.1.out.1 e.1.out.2 := by
      rw [← SimpleGraph.mem_edgeSet,
        show s(e.1.out.1, e.1.out.2) = e.1 from e.1.out_eq]
      exact e.2
    simpa [hexagonalBoxGraph, hexagonalBoxEmbedding,
      hexagonalBoxVertInclLE, boxVertInclLE] using he⟩

theorem hexagonalBoxEdgeLE_injective {n m : Nat} (h : n ≤ m) :
    Function.Injective (hexagonalBoxEdgeLE h) := by
  intro e f hef
  apply Subtype.ext
  have hv := congrArg Subtype.val hef
  change Sym2.map (hexagonalBoxVertInclLE h) e.1 =
    Sym2.map (hexagonalBoxVertInclLE h) f.1 at hv
  have hinj : Function.Injective (hexagonalBoxVertInclLE h) := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : HexagonalBoxVertex m => (z : HexVertex)) hxy
  exact (Sym2.map.injective hinj) hv

theorem hexagonal_adj_mem_box_succ
    {k : Nat} {x y : HexVertex} (hx : x.1 ∈ box 2 k)
    (hxy : hexagonalGraph.Adj x y) :
    y.1 ∈ box 2 (k + 1) := by
  rw [hexagonalGraph_adj] at hxy
  rcases hxy with ⟨_, _, i, h⟩ | ⟨_, _, i, h⟩
  · intro j
    have hj := hx j
    fin_cases i <;> fin_cases j <;>
      simp [hexagonalStep, funext_iff] at h hj ⊢ <;> omega
  · intro j
    have hj := hx j
    fin_cases i <;> fin_cases j <;>
      simp [hexagonalStep, funext_iff] at h hj ⊢ <;> omega

theorem hexagonal_adj_mem_box_of_mem_pred
    {k : Nat} (hk : 1 ≤ k) {x y : HexVertex}
    (hx : x.1 ∈ box 2 (k - 1)) (hxy : hexagonalGraph.Adj x y) :
    y.1 ∈ box 2 k := by
  simpa [Nat.sub_add_cancel hk] using hexagonal_adj_mem_box_succ hx hxy

theorem hexagonalBox_reachOpen_crosses
    {n k m : Nat} (hk : 1 ≤ k) (hkm : k ≤ m)
    (omega : ConfigSpace (hexagonalBoxGraph n).edgeSet)
    (h : ConnOpenSet (hexagonalBoxEndU n) (hexagonalBoxEndV n) omega
      (hexagonalBoxRoot n) (hexagonalBoxShell n m)) :
    ConnOpenSet (hexagonalBoxEndU n) (hexagonalBoxEndV n) omega
      (hexagonalBoxRoot n) (hexagonalBoxShell n k) := by
  obtain ⟨b, hb, hreach⟩ := h
  have hbOuter : b.1.1 ∉ box 2 (k - 1) := by
    have hbN := (Finset.mem_filter.mp hb).2.2
    intro hbk
    exact hbN (box_mono 2 (by omega) hbk)
  have hroot : (hexagonalBoxRoot n).1.1 ∈ box 2 (k - 1) := by
    intro j
    simp [hexagonalBoxRoot]
  have hfirst : ∀ {x b : HexagonalBoxVertex n},
      ReachOpen (hexagonalBoxEndU n) (hexagonalBoxEndV n) omega x b →
      x.1.1 ∈ box 2 (k - 1) → b.1.1 ∉ box 2 (k - 1) →
      ConnOpenSet (hexagonalBoxEndU n) (hexagonalBoxEndV n) omega x
        (hexagonalBoxShell n k) := by
    intro x b hr
    induction hr with
    | refl x => intro hx hnot; exact (hnot hx).elim
    | @step x y z e hopen hpair hrest ih =>
        intro hx hz
        have hxy : (hexagonalBoxGraph n).Adj x y := by
          rcases hpair with hpair | hpair
          · rw [← hpair.1, ← hpair.2]
            exact hexagonalBox_end_adj n e
          · rw [← hpair.1, ← hpair.2]
            exact (hexagonalBox_end_adj n e).symm
        by_cases hy : y.1.1 ∈ box 2 (k - 1)
        · obtain ⟨w, hw, hwy⟩ := ih hy hz
          exact ⟨w, hw, ReachOpen.step e hopen hpair hwy⟩
        · have hyk : y.1.1 ∈ box 2 k :=
            hexagonal_adj_mem_box_of_mem_pred hk hx hxy
          refine ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyk, hy⟩,
            ReachOpen.step e hopen hpair (ReachOpen.refl y)⟩
  exact hfirst hreach hroot hbOuter

theorem hexagonalBoxGraph_edgeSet_nonempty (n : Nat) (hn : 1 ≤ n) :
    Nonempty (hexagonalBoxGraph n).edgeSet := by
  let x : HexagonalBoxVertex n := hexagonalBoxRoot n
  let yFull := hexagonalNeighbor (hexagonalBoxEmbedding n x) 0
  let y : HexagonalBoxVertex n :=
    ⟨yFull, ⟨by
      intro j
      fin_cases j <;>
        simp [yFull, x, hexagonalBoxRoot, hexagonalBoxEmbedding,
          hexagonalNeighbor, hexagonalStep] <;> omega, Set.mem_univ _⟩⟩
  refine ⟨⟨s(x, y), ?_⟩⟩
  change hexagonalGraph.Adj (hexagonalBoxEmbedding n x)
    (hexagonalBoxEmbedding n y)
  simpa [y, yFull, hexagonalBoxEmbedding] using
    hexagonal_adj_neighbor (hexagonalBoxEmbedding n x) 0

noncomputable def hexagonalBoxBoundaryGraph (n : Nat) :
    SimpleGraph (HexagonalBoxVertex n) :=
  boundaryCliqueGraph fun x => x ∈ hexagonalBoxShell n n

noncomputable def hexagonalBoxCrossMass
    (n : Nat) (q beta : Real) : Real :=
  FK.activeBCProbOf (hexagonalBoxGraph n) (hexagonalBoxBoundaryGraph n)
    (FK.betaParams (fun _ => 1) beta) q
    (openCrossEvent (hexagonalBoxEndU n) (hexagonalBoxEndV n)
      (hexagonalBoxRoot n) (hexagonalBoxShell n n))

noncomputable def hexagonalBoxConnMass
    (n : Nat) (q beta : Real) (x : HexagonalBoxVertex n) (k : Nat) : Real :=
  Lindeberg.mean
    (FK.activeBCProb (hexagonalBoxGraph n) (hexagonalBoxBoundaryGraph n)
      (FK.betaParams (fun _ => 1) beta) q)
    (fun omega => if ConnOpenSet (hexagonalBoxEndU n)
      (hexagonalBoxEndV n) omega x (hexagonalBoxShell n k) then 1 else 0)



noncomputable def hexagonalInnerCrossInd (n : Nat) :
    ConfigSpace (hexagonalBoxGraph (2 * n)).edgeSet → Real := fun omega =>
  (openCrossEvent (hexagonalBoxEndU n) (hexagonalBoxEndV n)
    (hexagonalBoxRoot n) (hexagonalBoxShell n n)).indicator (fun _ => 1)
      (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) omega)

theorem hexagonalInnerCrossInd_monotone (n : Nat) :
    Monotone (hexagonalInnerCrossInd n) := by
  intro omega eta hle
  apply (openCrossEvent_isIncreasing (hexagonalBoxEndU n)
    (hexagonalBoxEndV n) (hexagonalBoxRoot n)
    (hexagonalBoxShell n n)).indicator_monotone
  intro e
  exact hle (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n) e)

theorem hexagonalInnerCrossInd_idem (n : Nat)
    (omega : ConfigSpace (hexagonalBoxGraph (2 * n)).edgeSet) :
    hexagonalInnerCrossInd n omega * hexagonalInnerCrossInd n omega =
      hexagonalInnerCrossInd n omega := by
  unfold hexagonalInnerCrossInd
  rw [Set.indicator_apply]
  split_ifs <;> norm_num

noncomputable def hexagonalOuterInnerConn
    (n : Nat) (q beta : Real) (x : HexagonalBoxVertex n) (k : Nat) : Real :=
  Lindeberg.mean
    (FK.activeBCProb (hexagonalBoxGraph (2 * n))
      (hexagonalBoxBoundaryGraph (2 * n))
      (FK.betaParams (fun _ => 1) beta) q)
    (fun omega => if ConnOpenSet (hexagonalBoxEndU n) (hexagonalBoxEndV n)
      (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
      x (hexagonalBoxShell n k) then 1 else 0)

noncomputable def hexagonalOuterInnerDenom
    (n : Nat) (q beta : Real) : Real :=
  let M := (Finset.univ : Finset (HexagonalBoxVertex n)).sup'
    ⟨hexagonalBoxRoot n, Finset.mem_univ _⟩
    (fun x => ∑ k : ↑(Finset.Icc 1 n),
      hexagonalOuterInnerConn n q beta x k)
  2 * (1 + M) / (n : Real)

noncomputable def hexagonalOuterInnerTheta
    (q beta : Real) (n : Nat) : Real :=
  if n = 0 then 1 else
    Lindeberg.mean
      (FK.activeBCProb (hexagonalBoxGraph (2 * n))
        (hexagonalBoxBoundaryGraph (2 * n))
        (FK.betaParams (fun _ => 1) beta) q)
      (hexagonalInnerCrossInd n)

noncomputable def hexagonalOuterInnerThetaPrime
    (n : Nat) (q beta : Real) : Real :=
  deriv (fun b => hexagonalOuterInnerTheta q b n) beta

noncomputable def hexagonalOuterInnerSig
    (n : Nat) (q beta : Real) : Real :=
  ∑ k ∈ Finset.range n, hexagonalOuterInnerTheta q beta k

theorem hexagonalOuterInnerDenom_pos
    (n : Nat) (hn : 1 ≤ n) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    0 < hexagonalOuterInnerDenom n q beta := by
  let mu := FK.activeBCProb (hexagonalBoxGraph (2 * n))
    (hexagonalBoxBoundaryGraph (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  let M := (Finset.univ : Finset (HexagonalBoxVertex n)).sup'
    ⟨hexagonalBoxRoot n, Finset.mem_univ _⟩
    (fun x => ∑ k : ↑(Finset.Icc 1 n),
      hexagonalOuterInnerConn n q beta x k)
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hmu0 : ∀ omega, 0 ≤ mu omega := fun omega =>
    (FK.activeBCProb_pos _ _
      (FK.betaParams_pos (fun _ => by norm_num) hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq0 omega).le
  have hconn0 : ∀ x k, 0 ≤ hexagonalOuterInnerConn n q beta x k := by
    intro x k
    unfold hexagonalOuterInnerConn
    exact RevealmentTranslation.mean_indicator_nonneg hmu0 _
  have hM : 0 ≤ M := by
    let x : HexagonalBoxVertex n := hexagonalBoxRoot n
    have hx : x ∈ (Finset.univ : Finset (HexagonalBoxVertex n)) := Finset.mem_univ _
    have hx0 : 0 ≤ ∑ k : ↑(Finset.Icc 1 n),
        hexagonalOuterInnerConn n q beta x k :=
      Finset.sum_nonneg fun k _ => hconn0 x k
    exact hx0.trans (Finset.le_sup'
      (fun y => ∑ k : ↑(Finset.Icc 1 n),
        hexagonalOuterInnerConn n q beta y k) hx)
  have hnR : 0 < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  unfold hexagonalOuterInnerDenom
  change 0 < 2 * (1 + M) / (n : Real)
  positivity



theorem hexagonal_outer_inner_hcov
    (n : Nat) (hn : 1 ≤ n) (q beta D : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) (hD : 0 < D)
    (hsum : ∀ e : (hexagonalBoxGraph n).edgeSet,
      (∑ k : ↑(Finset.Icc 1 n),
        (Lindeberg.mean
          (FK.activeBCProb (hexagonalBoxGraph (2 * n))
            (hexagonalBoxBoundaryGraph (2 * n))
            (FK.betaParams (fun _ => 1) beta) q)
          (fun omega => if ConnOpenSet (hexagonalBoxEndU n)
            (hexagonalBoxEndV n)
            (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
            (hexagonalBoxEndU n e) (hexagonalBoxShell n k)
            then (1 : Real) else 0) +
        Lindeberg.mean
          (FK.activeBCProb (hexagonalBoxGraph (2 * n))
            (hexagonalBoxBoundaryGraph (2 * n))
            (FK.betaParams (fun _ => 1) beta) q)
          (fun omega => if ConnOpenSet (hexagonalBoxEndU n)
            (hexagonalBoxEndV n)
            (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
            (hexagonalBoxEndV n e) (hexagonalBoxShell n k)
            then (1 : Real) else 0))) ≤
        (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D) :
    let mu := FK.activeBCProb (hexagonalBoxGraph (2 * n))
      (hexagonalBoxBoundaryGraph (2 * n))
      (FK.betaParams (fun _ => 1) beta) q
    Lindeberg.mean mu (hexagonalInnerCrossInd n) *
        (1 - Lindeberg.mean mu (hexagonalInnerCrossInd n)) / D ≤
      ∑ e, Lindeberg.cov mu (hexagonalInnerCrossInd n) (Lindeberg.coord e) := by
  let mu := FK.activeBCProb (hexagonalBoxGraph (2 * n))
    (hexagonalBoxBoundaryGraph (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hJ : ∀ e : Sym2 (HexagonalBoxVertex (2 * n)),
      0 < (fun _ => (1 : Real)) e := fun _ => by norm_num
  have hmain := hcov_reindexed_openCross_mass mu
    (FK.activeBCProb_pos _ _ (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq0)
    (FK.activeBCProb_sum_eq_one _ _ (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq0)
    (FK.activeBCProb_FKGLatticeCondition _ _ (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq)
    (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n))
    (hexagonalBoxEdgeLE_injective (by omega : n ≤ 2 * n))
    (hexagonalBoxEndU n) (hexagonalBoxEndV n) (hexagonalBoxRoot n)
    (Finset.univ : Finset (hexagonalBoxGraph n).edgeSet).toList
    (by simp) (hexagonalBoxShell n) (hexagonalBoxShell n)
    (by simp) (by simp) (by
      intro k hk
      simp [hexagonalBoxShell, hexagonalBoxRoot, vertexBoundary] at hk)
    (by
      intro k m hk hkm omega h
      exact hexagonalBox_reachOpen_crosses hk hkm omega h)
    n hn D hD hsum
  simpa [mu, hexagonalInnerCrossInd] using hmain



theorem hexagonal_outer_inner_hcov_geom
    (n : Nat) (hn : 1 ≤ n) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    let mu := FK.activeBCProb (hexagonalBoxGraph (2 * n))
      (hexagonalBoxBoundaryGraph (2 * n))
      (FK.betaParams (fun _ => 1) beta) q
    Lindeberg.mean mu (hexagonalInnerCrossInd n) *
        (1 - Lindeberg.mean mu (hexagonalInnerCrossInd n)) /
          hexagonalOuterInnerDenom n q beta ≤
      ∑ e, Lindeberg.cov mu (hexagonalInnerCrossInd n) (Lindeberg.coord e) := by
  let mu := FK.activeBCProb (hexagonalBoxGraph (2 * n))
    (hexagonalBoxBoundaryGraph (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  let M := (Finset.univ : Finset (HexagonalBoxVertex n)).sup'
    ⟨hexagonalBoxRoot n, Finset.mem_univ _⟩
    (fun x => ∑ k : ↑(Finset.Icc 1 n),
      hexagonalOuterInnerConn n q beta x k)
  let D := 2 * (1 + M) / (n : Real)
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hmu0 : ∀ omega, 0 ≤ mu omega := fun omega =>
    (FK.activeBCProb_pos _ _
      (FK.betaParams_pos (fun _ => by norm_num) hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq0 omega).le
  have hconn0 : ∀ x k, 0 ≤ hexagonalOuterInnerConn n q beta x k := by
    intro x k
    unfold hexagonalOuterInnerConn
    exact RevealmentTranslation.mean_indicator_nonneg hmu0 _
  have hM : 0 ≤ M := by
    let x : HexagonalBoxVertex n := hexagonalBoxRoot n
    have hx : x ∈ (Finset.univ : Finset (HexagonalBoxVertex n)) := Finset.mem_univ _
    have hx0 : 0 ≤ ∑ k : ↑(Finset.Icc 1 n),
        hexagonalOuterInnerConn n q beta x k :=
      Finset.sum_nonneg fun k _ => hconn0 x k
    exact hx0.trans (Finset.le_sup'
      (fun y => ∑ k : ↑(Finset.Icc 1 n),
        hexagonalOuterInnerConn n q beta y k) hx)
  have hnR : 0 < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hD : 0 < D := by dsimp [D]; positivity
  have hsum : ∀ e : (hexagonalBoxGraph n).edgeSet,
      (∑ k : ↑(Finset.Icc 1 n),
        (Lindeberg.mean mu (fun omega => if ConnOpenSet
          (hexagonalBoxEndU n) (hexagonalBoxEndV n)
          (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
          (hexagonalBoxEndU n e) (hexagonalBoxShell n k)
          then (1 : Real) else 0) +
        Lindeberg.mean mu (fun omega => if ConnOpenSet
          (hexagonalBoxEndU n) (hexagonalBoxEndV n)
          (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
          (hexagonalBoxEndV n e) (hexagonalBoxShell n k)
          then (1 : Real) else 0))) ≤
        (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D := by
    intro e
    have hu := Finset.le_sup'
      (fun x => ∑ k : ↑(Finset.Icc 1 n),
        hexagonalOuterInnerConn n q beta x k)
      (Finset.mem_univ (hexagonalBoxEndU n e))
    have hv := Finset.le_sup'
      (fun x => ∑ k : ↑(Finset.Icc 1 n),
        hexagonalOuterInnerConn n q beta x k)
      (Finset.mem_univ (hexagonalBoxEndV n e))
    have hcard : (Fintype.card (↑(Finset.Icc 1 n)) : Real) = n := by
      rw [Fintype.card_coe, Nat.card_Icc]
      norm_num
    rw [Finset.sum_add_distrib]
    change
      (∑ k : ↑(Finset.Icc 1 n),
          hexagonalOuterInnerConn n q beta (hexagonalBoxEndU n e) k) +
        (∑ k : ↑(Finset.Icc 1 n),
          hexagonalOuterInnerConn n q beta (hexagonalBoxEndV n e) k) ≤
        (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D
    calc
      _ ≤ M + M := add_le_add hu hv
      _ ≤ (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D := by
        rw [hcard]
        dsimp [D]
        rw [mul_div_cancel₀ _ hnR.ne']
        linarith
  have hmain := hexagonal_outer_inner_hcov n hn q beta D hq hbeta hD
    (by simpa [mu] using hsum)
  simpa [hexagonalOuterInnerDenom, mu, M, D] using hmain



theorem hexagonal_outer_inner_differential_logistic
    (n : Nat) (hn : 1 ≤ n) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    hexagonalOuterInnerTheta q beta n *
        (1 - hexagonalOuterInnerTheta q beta n) /
          hexagonalOuterInnerDenom n q beta ≤
      hexagonalOuterInnerThetaPrime n q beta := by
  letI : Nonempty (hexagonalBoxGraph (2 * n)).edgeSet :=
    hexagonalBoxGraph_edgeSet_nonempty (2 * n) (by omega)
  let G := hexagonalBoxGraph (2 * n)
  let C := hexagonalBoxBoundaryGraph (2 * n)
  let J : Sym2 (HexagonalBoxVertex (2 * n)) → Real := fun _ => 1
  let mu := FK.activeBCProb G C (FK.betaParams J beta) q
  let f := hexagonalInnerCrossInd n
  have hJ : ∀ e, 0 < J e := fun _ => by simp [J]
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hcov : Lindeberg.mean mu f * (1 - Lindeberg.mean mu f) /
        hexagonalOuterInnerDenom n q beta ≤
      ∑ e, Lindeberg.cov mu f (Lindeberg.coord e) := by
    simpa [G, C, J, mu, f] using
      hexagonal_outer_inner_hcov_geom n hn q beta hq hbeta
  have hpos : ∀ omega, 0 < mu omega :=
    FK.activeBCProb_pos G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0
  have hmu1 : ∑ omega, mu omega = 1 :=
    FK.activeBCProb_sum_eq_one G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0
  have hFKG : FKGLatticeCondition mu :=
    FK.activeBCProb_FKGLatticeCondition G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq
  have hf : Monotone f := hexagonalInnerCrossInd_monotone n
  have hcov0 : ∀ e : G.edgeSet,
      0 ≤ FK.activeBCCov G C (FK.betaParams J beta) q f
        (Lindeberg.coord e) := by
    intro e
    rw [← ActiveBoundaryDifferential.cov_activeBC_eq]
    exact LindebergTree.cov_coord_nonneg hpos hmu1 hFKG hf e
  have hderiv := FK.hasDerivAt_activeBCMean_beta_sum G C hJ hbeta hq0 f
  have hderivEq :
      deriv (fun b => FK.activeBCMean G C (FK.betaParams J b) q f) beta =
        ∑ e : G.edgeSet, (J e.1 / (1 - Real.exp (-(beta * J e.1)))) *
          FK.activeBCCov G C (FK.betaParams J beta) q f
            (Lindeberg.coord e) := by
    rw [hderiv.deriv]
    simp only [FK.betaParams]
  have hpref : ∀ e : G.edgeSet,
      (1 : Real) ≤ J e.1 / (1 - Real.exp (-(beta * J e.1))) := by
    intro e
    have hden : 0 < 1 - Real.exp (-beta) := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
      linarith
    simp only [J, mul_one]
    rw [le_div_iff₀ hden]
    linarith [Real.exp_pos (-beta)]
  have hRusso :
      ∑ e : G.edgeSet, FK.activeBCCov G C (FK.betaParams J beta) q f
          (Lindeberg.coord e) ≤
        deriv (fun b => FK.activeBCMean G C (FK.betaParams J b) q f) beta := by
    rw [hderivEq]
    simpa using RussoPrefactor.rp_prefactor_extraction
      (fun e : G.edgeSet => J e.1 / (1 - Real.exp (-(beta * J e.1))))
      (fun e => FK.activeBCCov G C (FK.betaParams J beta) q f
        (Lindeberg.coord e)) 1 hpref hcov0
  have hmain := hcov.trans (by
    simpa [ActiveBoundaryDifferential.cov_activeBC_eq] using hRusso)
  have hn0 : n ≠ 0 := by omega
  simpa [hexagonalOuterInnerTheta, hexagonalOuterInnerThetaPrime,
    hn0, G, C, J, mu, f] using hmain

noncomputable def hexagonalBoxDenom
    (n : Nat) (q beta : Real) : Real :=
  let M := (Finset.univ : Finset (HexagonalBoxVertex n)).sup'
    ⟨hexagonalBoxRoot n, Finset.mem_univ _⟩ (fun x => ∑ k : ↑(Finset.Icc 1 n),
      hexagonalBoxConnMass n q beta x k)
  2 * (1 + M) / (n : Real)

theorem hexagonalBox_differential_inequality
    (n : Nat) (hn : 1 ≤ n) (q beta beta0 : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) (hbeta0 : beta ≤ beta0) :
    ∃ c : Real, 0 < c ∧
      c * (hexagonalBoxCrossMass n q beta /
        hexagonalBoxDenom n q beta) ≤
      deriv (hexagonalBoxCrossMass n q) beta := by
  letI : Nonempty (hexagonalBoxGraph n).edgeSet :=
    hexagonalBoxGraph_edgeSet_nonempty n hn
  letI : Nonempty (HexagonalBoxVertex n) := ⟨hexagonalBoxRoot n⟩
  let mu := FK.activeBCProb (hexagonalBoxGraph n)
    (hexagonalBoxBoundaryGraph n) (FK.betaParams (fun _ => 1) beta) q
  let M := (Finset.univ : Finset (HexagonalBoxVertex n)).sup'
    ⟨hexagonalBoxRoot n, Finset.mem_univ _⟩ (fun x => ∑ k : ↑(Finset.Icc 1 n),
      hexagonalBoxConnMass n q beta x k)
  let D := 2 * (1 + M) / (n : Real)
  have hconn0 : ∀ x k, 0 ≤ hexagonalBoxConnMass n q beta x k := by
    intro x k
    unfold hexagonalBoxConnMass Lindeberg.mean
    exact Finset.sum_nonneg fun omega _ => mul_nonneg (by
      change 0 ≤ if ConnOpenSet (hexagonalBoxEndU n) (hexagonalBoxEndV n)
        omega x (hexagonalBoxShell n k) then (1 : Real) else 0
      split_ifs <;> norm_num)
        (FK.activeBCProb_pos (hexagonalBoxGraph n) (hexagonalBoxBoundaryGraph n)
          (FK.betaParams_pos (fun _ => by norm_num) hbeta)
          (FK.betaParams_lt_one (fun _ => 1) beta)
          (zero_lt_one.trans_le hq) omega).le
  have hM : 0 ≤ M := by
    let x : HexagonalBoxVertex n := hexagonalBoxRoot n
    have hx : x ∈ (Finset.univ : Finset (HexagonalBoxVertex n)) := Finset.mem_univ _
    have hx0 : 0 ≤ ∑ k : ↑(Finset.Icc 1 n),
        hexagonalBoxConnMass n q beta x k :=
      Finset.sum_nonneg fun k _ => hconn0 x k
    exact hx0.trans
      (Finset.le_sup' (fun y => ∑ k : ↑(Finset.Icc 1 n),
        hexagonalBoxConnMass n q beta y k) hx)
  have hnR : 0 < (n : Real) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hD : 0 < D := by dsimp [D]; positivity
  have hsum : ∀ e : (hexagonalBoxGraph n).edgeSet,
      (∑ k : ↑(Finset.Icc 1 n),
        (Lindeberg.mean mu (fun omega => if ConnOpenSet
          (hexagonalBoxEndU n) (hexagonalBoxEndV n) omega
          (hexagonalBoxEndU n e) (hexagonalBoxShell n k) then 1 else 0) +
        Lindeberg.mean mu (fun omega => if ConnOpenSet
          (hexagonalBoxEndU n) (hexagonalBoxEndV n) omega
          (hexagonalBoxEndV n e) (hexagonalBoxShell n k) then 1 else 0))) ≤
        (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D := by
    intro e
    have hu := Finset.le_sup' (fun x => ∑ k : ↑(Finset.Icc 1 n),
      hexagonalBoxConnMass n q beta x k)
      (Finset.mem_univ (hexagonalBoxEndU n e))
    have hv := Finset.le_sup' (fun x => ∑ k : ↑(Finset.Icc 1 n),
      hexagonalBoxConnMass n q beta x k)
      (Finset.mem_univ (hexagonalBoxEndV n e))
    have hcard : (Fintype.card (↑(Finset.Icc 1 n)) : Real) = n := by
      rw [Fintype.card_coe, Nat.card_Icc]
      norm_num
    rw [Finset.sum_add_distrib]
    change
      (∑ k : ↑(Finset.Icc 1 n),
          hexagonalBoxConnMass n q beta (hexagonalBoxEndU n e) k) +
        (∑ k : ↑(Finset.Icc 1 n),
          hexagonalBoxConnMass n q beta (hexagonalBoxEndV n e) k) ≤
        (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D
    calc
      _ ≤ M + M := add_le_add hu hv
      _ ≤ (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D := by
        rw [hcard]
        dsimp [D]
        rw [mul_div_cancel₀ _ hnR.ne']
        linarith
  obtain ⟨c, hc, hmain⟩ := activeBC_openCross_differential_inequality
    (hexagonalBoxGraph n) (hexagonalBoxBoundaryGraph n) (fun _ => 1)
    (fun _ => by norm_num) q beta beta0 hq hbeta hbeta0
    (hexagonalBoxEndU n) (hexagonalBoxEndV n)
    (hexagonalBox_end_coherent n) (hexagonalBoxRoot n)
    (Finset.univ : Finset (hexagonalBoxGraph n).edgeSet).toList
    (by simp) (hexagonalBoxShell n) (hexagonalBoxShell n)
    (by simp) (by simp) (by
      intro k hk
      simp [hexagonalBoxShell, hexagonalBoxRoot, vertexBoundary] at hk)
    (by
      intro k m hk hkm omega h
      exact hexagonalBox_reachOpen_crosses hk hkm omega h)
    n hn D hD hsum
  refine ⟨c, hc, ?_⟩
  simpa [hexagonalBoxCrossMass, hexagonalBoxDenom, M, D] using hmain

end StatMech.FK.PeriodicPlanar
