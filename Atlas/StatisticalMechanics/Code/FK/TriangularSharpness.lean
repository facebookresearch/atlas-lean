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

abbrev TriangularBoxVertex (n : Nat) := boxVerts 2 n

def triangularBoxGraph (n : Nat) : SimpleGraph (TriangularBoxVertex n) :=
  SimpleGraph.comap Subtype.val triangularGraph

noncomputable instance (n : Nat) : DecidableRel (triangularBoxGraph n).Adj :=
  Classical.decRel _

def triangularBoxRoot (n : Nat) : TriangularBoxVertex n := ⟨0, by simp⟩

noncomputable def triangularBoxShell (n k : Nat) : Finset (TriangularBoxVertex n) :=
  Finset.univ.filter fun x => (x.1 : Site 2) ∈ vertexBoundary 2 k

noncomputable def triangularBoxEndU (n : Nat) :
    (triangularBoxGraph n).edgeSet → TriangularBoxVertex n :=
  fun e => e.1.out.1

noncomputable def triangularBoxEndV (n : Nat) :
    (triangularBoxGraph n).edgeSet → TriangularBoxVertex n :=
  fun e => e.1.out.2

@[simp] theorem triangularBox_end_coherent
    (n : Nat) (e : (triangularBoxGraph n).edgeSet) :
    e.1 = s(triangularBoxEndU n e, triangularBoxEndV n e) := by
  exact e.1.out_eq.symm

theorem triangularBox_end_adj
    (n : Nat) (e : (triangularBoxGraph n).edgeSet) :
    (triangularBoxGraph n).Adj
      (triangularBoxEndU n e) (triangularBoxEndV n e) := by
  have he : (triangularBoxGraph n).Adj e.1.out.1 e.1.out.2 := by
    rw [← SimpleGraph.mem_edgeSet]
    have hout : s(e.1.out.1, e.1.out.2) = e.1 := e.1.out_eq
    rw [hout]
    exact e.2
  exact he


def triangularBoxEdgeLE {n m : Nat} (h : n ≤ m) :
    (triangularBoxGraph n).edgeSet → (triangularBoxGraph m).edgeSet := fun e =>
  ⟨innerEdgeLE 2 h e.1, by
    have hpair : innerEdgeLE 2 h e.1 =
        s(boxVertInclLE 2 h e.1.out.1, boxVertInclLE 2 h e.1.out.2) := by
      unfold innerEdgeLE
      calc
        Sym2.map (boxVertInclLE 2 h) e.1 =
            Sym2.map (boxVertInclLE 2 h) s(e.1.out.1, e.1.out.2) := by
          exact congrArg (Sym2.map (boxVertInclLE 2 h)) e.1.out_eq.symm
        _ = _ := by rw [Sym2.map_mk]
    rw [hpair, SimpleGraph.mem_edgeSet]
    have he : (triangularBoxGraph n).Adj e.1.out.1 e.1.out.2 := by
      rw [← SimpleGraph.mem_edgeSet,
        show s(e.1.out.1, e.1.out.2) = e.1 from e.1.out_eq]
      exact e.2
    exact he⟩

theorem triangularBoxEdgeLE_injective {n m : Nat} (h : n ≤ m) :
    Function.Injective (triangularBoxEdgeLE h) := by
  intro e f hef
  apply Subtype.ext
  have hv := congrArg Subtype.val hef
  change innerEdgeLE 2 h e.1 = innerEdgeLE 2 h f.1 at hv
  have hinj : Function.Injective (boxVertInclLE 2 h) := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : boxVerts 2 m => (z : Site 2)) hxy
  exact (Sym2.map.injective hinj) hv

theorem triangular_adj_mem_box_succ
    {k : Nat} {x y : Site 2} (hx : x ∈ box 2 k)
    (hxy : triangularGraph.Adj x y) :
    y ∈ box 2 (k + 1) := by
  rw [triangularGraph_adj] at hxy
  obtain ⟨i, h | h⟩ := hxy
  · intro j
    have hj := hx j
    fin_cases i <;> fin_cases j <;>
      simp [triangularStep, funext_iff] at h hj ⊢ <;> omega
  · intro j
    have hj := hx j
    fin_cases i <;> fin_cases j <;>
      simp [triangularStep, funext_iff] at h hj ⊢ <;> omega

theorem triangular_adj_mem_box_of_mem_pred
    {k : Nat} (hk : 1 ≤ k) {x y : Site 2}
    (hx : x ∈ box 2 (k - 1)) (hxy : triangularGraph.Adj x y) :
    y ∈ box 2 k := by
  simpa [Nat.sub_add_cancel hk] using triangular_adj_mem_box_succ hx hxy

theorem triangularBox_reachOpen_crosses
    {n k m : Nat} (hk : 1 ≤ k) (hkm : k ≤ m)
    (omega : ConfigSpace (triangularBoxGraph n).edgeSet)
    (h : ConnOpenSet (triangularBoxEndU n) (triangularBoxEndV n) omega
      (triangularBoxRoot n) (triangularBoxShell n m)) :
    ConnOpenSet (triangularBoxEndU n) (triangularBoxEndV n) omega
      (triangularBoxRoot n) (triangularBoxShell n k) := by
  obtain ⟨b, hb, hreach⟩ := h
  have hbOuter : b.1 ∉ box 2 (k - 1) := by
    have hbN := (Finset.mem_filter.mp hb).2.2
    intro hbk
    exact hbN (box_mono 2 (by omega) hbk)
  have hroot : (triangularBoxRoot n).1 ∈ box 2 (k - 1) := by
    intro j
    simp [triangularBoxRoot]
  have hfirst : ∀ {x b : TriangularBoxVertex n},
      ReachOpen (triangularBoxEndU n) (triangularBoxEndV n) omega x b →
      x.1 ∈ box 2 (k - 1) → b.1 ∉ box 2 (k - 1) →
      ConnOpenSet (triangularBoxEndU n) (triangularBoxEndV n) omega x
        (triangularBoxShell n k) := by
    intro x b hr
    induction hr with
    | refl x => intro hx hnot; exact (hnot hx).elim
    | @step x y z e hopen hpair hrest ih =>
        intro hx hz
        have hxy : (triangularBoxGraph n).Adj x y := by
          rcases hpair with hpair | hpair
          · rw [← hpair.1, ← hpair.2]
            exact triangularBox_end_adj n e
          · rw [← hpair.1, ← hpair.2]
            exact (triangularBox_end_adj n e).symm
        by_cases hy : y.1 ∈ box 2 (k - 1)
        · obtain ⟨w, hw, hwy⟩ := ih hy hz
          exact ⟨w, hw, ReachOpen.step e hopen hpair hwy⟩
        · have hyk : y.1 ∈ box 2 k :=
            triangular_adj_mem_box_of_mem_pred hk hx hxy
          refine ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyk, hy⟩,
            ReachOpen.step e hopen hpair (ReachOpen.refl y)⟩
  exact hfirst hreach hroot hbOuter

theorem triangularBoxGraph_edgeSet_nonempty (n : Nat) (hn : 1 ≤ n) :
    Nonempty (triangularBoxGraph n).edgeSet := by
  let x : TriangularBoxVertex n := triangularBoxRoot n
  let y : TriangularBoxVertex n := ⟨triangularNeighbor x.1 (0, true), by
    intro j
    fin_cases j <;>
      simp [x, triangularBoxRoot, triangularNeighbor, triangularStep] <;> omega⟩
  refine ⟨⟨s(x, y), ?_⟩⟩
  change triangularGraph.Adj x.1 y.1
  exact triangular_adj_neighbor x.1 (0, true)

noncomputable def triangularBoxBoundaryGraph (n : Nat) :
    SimpleGraph (TriangularBoxVertex n) :=
  boundaryCliqueGraph fun x => x ∈ triangularBoxShell n n

noncomputable def triangularBoxCrossMass
    (n : Nat) (q beta : Real) : Real :=
  FK.activeBCProbOf (triangularBoxGraph n) (triangularBoxBoundaryGraph n)
    (FK.betaParams (fun _ => 1) beta) q
    (openCrossEvent (triangularBoxEndU n) (triangularBoxEndV n)
      (triangularBoxRoot n) (triangularBoxShell n n))

noncomputable def triangularBoxConnMass
    (n : Nat) (q beta : Real) (x : TriangularBoxVertex n) (k : Nat) : Real :=
  Lindeberg.mean
    (FK.activeBCProb (triangularBoxGraph n) (triangularBoxBoundaryGraph n)
      (FK.betaParams (fun _ => 1) beta) q)
    (fun omega => if ConnOpenSet (triangularBoxEndU n)
      (triangularBoxEndV n) omega x (triangularBoxShell n k) then 1 else 0)



noncomputable def triangularInnerCrossInd (n : Nat) :
    ConfigSpace (triangularBoxGraph (2 * n)).edgeSet → Real := fun omega =>
  (openCrossEvent (triangularBoxEndU n) (triangularBoxEndV n)
    (triangularBoxRoot n) (triangularBoxShell n n)).indicator (fun _ => 1)
      (restrictConfig (triangularBoxEdgeLE (by omega : n ≤ 2 * n)) omega)

theorem triangularInnerCrossInd_monotone (n : Nat) :
    Monotone (triangularInnerCrossInd n) := by
  intro omega eta hle
  apply (openCrossEvent_isIncreasing (triangularBoxEndU n)
    (triangularBoxEndV n) (triangularBoxRoot n)
    (triangularBoxShell n n)).indicator_monotone
  intro e
  exact hle (triangularBoxEdgeLE (by omega : n ≤ 2 * n) e)

theorem triangularInnerCrossInd_idem (n : Nat)
    (omega : ConfigSpace (triangularBoxGraph (2 * n)).edgeSet) :
    triangularInnerCrossInd n omega * triangularInnerCrossInd n omega =
      triangularInnerCrossInd n omega := by
  unfold triangularInnerCrossInd
  rw [Set.indicator_apply]
  split_ifs <;> norm_num

noncomputable def triangularOuterInnerConn
    (n : Nat) (q beta : Real) (x : TriangularBoxVertex n) (k : Nat) : Real :=
  Lindeberg.mean
    (FK.activeBCProb (triangularBoxGraph (2 * n))
      (triangularBoxBoundaryGraph (2 * n))
      (FK.betaParams (fun _ => 1) beta) q)
    (fun omega => if ConnOpenSet (triangularBoxEndU n) (triangularBoxEndV n)
      (restrictConfig (triangularBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
      x (triangularBoxShell n k) then 1 else 0)

noncomputable def triangularOuterInnerDenom
    (n : Nat) (q beta : Real) : Real :=
  let M := (Finset.univ : Finset (TriangularBoxVertex n)).sup'
    ⟨triangularBoxRoot n, Finset.mem_univ _⟩
    (fun x => ∑ k : ↑(Finset.Icc 1 n),
      triangularOuterInnerConn n q beta x k)
  2 * (1 + M) / (n : Real)

noncomputable def triangularOuterInnerTheta
    (q beta : Real) (n : Nat) : Real :=
  if n = 0 then 1 else
    Lindeberg.mean
      (FK.activeBCProb (triangularBoxGraph (2 * n))
        (triangularBoxBoundaryGraph (2 * n))
        (FK.betaParams (fun _ => 1) beta) q)
      (triangularInnerCrossInd n)

noncomputable def triangularOuterInnerThetaPrime
    (n : Nat) (q beta : Real) : Real :=
  deriv (fun b => triangularOuterInnerTheta q b n) beta

noncomputable def triangularOuterInnerSig
    (n : Nat) (q beta : Real) : Real :=
  ∑ k ∈ Finset.range n, triangularOuterInnerTheta q beta k

theorem triangularOuterInnerDenom_pos
    (n : Nat) (hn : 1 ≤ n) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    0 < triangularOuterInnerDenom n q beta := by
  let mu := FK.activeBCProb (triangularBoxGraph (2 * n))
    (triangularBoxBoundaryGraph (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  let M := (Finset.univ : Finset (TriangularBoxVertex n)).sup'
    ⟨triangularBoxRoot n, Finset.mem_univ _⟩
    (fun x => ∑ k : ↑(Finset.Icc 1 n),
      triangularOuterInnerConn n q beta x k)
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hmu0 : ∀ omega, 0 ≤ mu omega := fun omega =>
    (FK.activeBCProb_pos _ _
      (FK.betaParams_pos (fun _ => by norm_num) hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq0 omega).le
  have hconn0 : ∀ x k, 0 ≤ triangularOuterInnerConn n q beta x k := by
    intro x k
    unfold triangularOuterInnerConn
    exact RevealmentTranslation.mean_indicator_nonneg hmu0 _
  have hM : 0 ≤ M := by
    let x : TriangularBoxVertex n := triangularBoxRoot n
    have hx : x ∈ (Finset.univ : Finset (TriangularBoxVertex n)) := Finset.mem_univ _
    have hx0 : 0 ≤ ∑ k : ↑(Finset.Icc 1 n),
        triangularOuterInnerConn n q beta x k :=
      Finset.sum_nonneg fun k _ => hconn0 x k
    exact hx0.trans (Finset.le_sup'
      (fun y => ∑ k : ↑(Finset.Icc 1 n),
        triangularOuterInnerConn n q beta y k) hx)
  have hnR : 0 < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  unfold triangularOuterInnerDenom
  change 0 < 2 * (1 + M) / (n : Real)
  positivity



theorem triangular_outer_inner_hcov
    (n : Nat) (hn : 1 ≤ n) (q beta D : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) (hD : 0 < D)
    (hsum : ∀ e : (triangularBoxGraph n).edgeSet,
      (∑ k : ↑(Finset.Icc 1 n),
        (Lindeberg.mean
          (FK.activeBCProb (triangularBoxGraph (2 * n))
            (triangularBoxBoundaryGraph (2 * n))
            (FK.betaParams (fun _ => 1) beta) q)
          (fun omega => if ConnOpenSet (triangularBoxEndU n)
            (triangularBoxEndV n)
            (restrictConfig (triangularBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
            (triangularBoxEndU n e) (triangularBoxShell n k)
            then (1 : Real) else 0) +
        Lindeberg.mean
          (FK.activeBCProb (triangularBoxGraph (2 * n))
            (triangularBoxBoundaryGraph (2 * n))
            (FK.betaParams (fun _ => 1) beta) q)
          (fun omega => if ConnOpenSet (triangularBoxEndU n)
            (triangularBoxEndV n)
            (restrictConfig (triangularBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
            (triangularBoxEndV n e) (triangularBoxShell n k)
            then (1 : Real) else 0))) ≤
        (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D) :
    let mu := FK.activeBCProb (triangularBoxGraph (2 * n))
      (triangularBoxBoundaryGraph (2 * n))
      (FK.betaParams (fun _ => 1) beta) q
    Lindeberg.mean mu (triangularInnerCrossInd n) *
        (1 - Lindeberg.mean mu (triangularInnerCrossInd n)) / D ≤
      ∑ e, Lindeberg.cov mu (triangularInnerCrossInd n) (Lindeberg.coord e) := by
  let mu := FK.activeBCProb (triangularBoxGraph (2 * n))
    (triangularBoxBoundaryGraph (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hJ : ∀ e : Sym2 (TriangularBoxVertex (2 * n)),
      0 < (fun _ => (1 : Real)) e := fun _ => by norm_num
  have hmain := hcov_reindexed_openCross_mass mu
    (FK.activeBCProb_pos _ _ (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq0)
    (FK.activeBCProb_sum_eq_one _ _ (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq0)
    (FK.activeBCProb_FKGLatticeCondition _ _ (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq)
    (triangularBoxEdgeLE (by omega : n ≤ 2 * n))
    (triangularBoxEdgeLE_injective (by omega : n ≤ 2 * n))
    (triangularBoxEndU n) (triangularBoxEndV n) (triangularBoxRoot n)
    (Finset.univ : Finset (triangularBoxGraph n).edgeSet).toList
    (by simp) (triangularBoxShell n) (triangularBoxShell n)
    (by simp) (by simp) (by
      intro k hk
      simp [triangularBoxShell, triangularBoxRoot, vertexBoundary] at hk)
    (by
      intro k m hk hkm omega h
      exact triangularBox_reachOpen_crosses hk hkm omega h)
    n hn D hD hsum
  simpa [mu, triangularInnerCrossInd] using hmain



theorem triangular_outer_inner_hcov_geom
    (n : Nat) (hn : 1 ≤ n) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    let mu := FK.activeBCProb (triangularBoxGraph (2 * n))
      (triangularBoxBoundaryGraph (2 * n))
      (FK.betaParams (fun _ => 1) beta) q
    Lindeberg.mean mu (triangularInnerCrossInd n) *
        (1 - Lindeberg.mean mu (triangularInnerCrossInd n)) /
          triangularOuterInnerDenom n q beta ≤
      ∑ e, Lindeberg.cov mu (triangularInnerCrossInd n) (Lindeberg.coord e) := by
  let mu := FK.activeBCProb (triangularBoxGraph (2 * n))
    (triangularBoxBoundaryGraph (2 * n))
    (FK.betaParams (fun _ => 1) beta) q
  let M := (Finset.univ : Finset (TriangularBoxVertex n)).sup'
    ⟨triangularBoxRoot n, Finset.mem_univ _⟩
    (fun x => ∑ k : ↑(Finset.Icc 1 n),
      triangularOuterInnerConn n q beta x k)
  let D := 2 * (1 + M) / (n : Real)
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hmu0 : ∀ omega, 0 ≤ mu omega := fun omega =>
    (FK.activeBCProb_pos _ _
      (FK.betaParams_pos (fun _ => by norm_num) hbeta)
      (FK.betaParams_lt_one (fun _ => 1) beta) hq0 omega).le
  have hconn0 : ∀ x k, 0 ≤ triangularOuterInnerConn n q beta x k := by
    intro x k
    unfold triangularOuterInnerConn
    exact RevealmentTranslation.mean_indicator_nonneg hmu0 _
  have hM : 0 ≤ M := by
    let x : TriangularBoxVertex n := triangularBoxRoot n
    have hx : x ∈ (Finset.univ : Finset (TriangularBoxVertex n)) := Finset.mem_univ _
    have hx0 : 0 ≤ ∑ k : ↑(Finset.Icc 1 n),
        triangularOuterInnerConn n q beta x k :=
      Finset.sum_nonneg fun k _ => hconn0 x k
    exact hx0.trans (Finset.le_sup'
      (fun y => ∑ k : ↑(Finset.Icc 1 n),
        triangularOuterInnerConn n q beta y k) hx)
  have hnR : 0 < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hD : 0 < D := by dsimp [D]; positivity
  have hsum : ∀ e : (triangularBoxGraph n).edgeSet,
      (∑ k : ↑(Finset.Icc 1 n),
        (Lindeberg.mean mu (fun omega => if ConnOpenSet
          (triangularBoxEndU n) (triangularBoxEndV n)
          (restrictConfig (triangularBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
          (triangularBoxEndU n e) (triangularBoxShell n k)
          then (1 : Real) else 0) +
        Lindeberg.mean mu (fun omega => if ConnOpenSet
          (triangularBoxEndU n) (triangularBoxEndV n)
          (restrictConfig (triangularBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
          (triangularBoxEndV n e) (triangularBoxShell n k)
          then (1 : Real) else 0))) ≤
        (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D := by
    intro e
    have hu := Finset.le_sup'
      (fun x => ∑ k : ↑(Finset.Icc 1 n),
        triangularOuterInnerConn n q beta x k)
      (Finset.mem_univ (triangularBoxEndU n e))
    have hv := Finset.le_sup'
      (fun x => ∑ k : ↑(Finset.Icc 1 n),
        triangularOuterInnerConn n q beta x k)
      (Finset.mem_univ (triangularBoxEndV n e))
    have hcard : (Fintype.card (↑(Finset.Icc 1 n)) : Real) = n := by
      rw [Fintype.card_coe, Nat.card_Icc]
      norm_num
    rw [Finset.sum_add_distrib]
    change
      (∑ k : ↑(Finset.Icc 1 n),
          triangularOuterInnerConn n q beta (triangularBoxEndU n e) k) +
        (∑ k : ↑(Finset.Icc 1 n),
          triangularOuterInnerConn n q beta (triangularBoxEndV n e) k) ≤
        (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D
    calc
      _ ≤ M + M := add_le_add hu hv
      _ ≤ (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D := by
        rw [hcard]
        dsimp [D]
        rw [mul_div_cancel₀ _ hnR.ne']
        linarith
  have hmain := triangular_outer_inner_hcov n hn q beta D hq hbeta hD
    (by simpa [mu] using hsum)
  simpa [triangularOuterInnerDenom, mu, M, D] using hmain



theorem triangular_outer_inner_differential_logistic
    (n : Nat) (hn : 1 ≤ n) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    triangularOuterInnerTheta q beta n *
        (1 - triangularOuterInnerTheta q beta n) /
          triangularOuterInnerDenom n q beta ≤
      triangularOuterInnerThetaPrime n q beta := by
  letI : Nonempty (triangularBoxGraph (2 * n)).edgeSet :=
    triangularBoxGraph_edgeSet_nonempty (2 * n) (by omega)
  let G := triangularBoxGraph (2 * n)
  let C := triangularBoxBoundaryGraph (2 * n)
  let J : Sym2 (TriangularBoxVertex (2 * n)) → Real := fun _ => 1
  let mu := FK.activeBCProb G C (FK.betaParams J beta) q
  let f := triangularInnerCrossInd n
  have hJ : ∀ e, 0 < J e := fun _ => by simp [J]
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hcov : Lindeberg.mean mu f * (1 - Lindeberg.mean mu f) /
        triangularOuterInnerDenom n q beta ≤
      ∑ e, Lindeberg.cov mu f (Lindeberg.coord e) := by
    simpa [G, C, J, mu, f] using
      triangular_outer_inner_hcov_geom n hn q beta hq hbeta
  have hpos : ∀ omega, 0 < mu omega :=
    FK.activeBCProb_pos G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0
  have hmu1 : ∑ omega, mu omega = 1 :=
    FK.activeBCProb_sum_eq_one G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0
  have hFKG : FKGLatticeCondition mu :=
    FK.activeBCProb_FKGLatticeCondition G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq
  have hf : Monotone f := triangularInnerCrossInd_monotone n
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
  simpa [triangularOuterInnerTheta, triangularOuterInnerThetaPrime,
    hn0, G, C, J, mu, f] using hmain

noncomputable def triangularBoxDenom
    (n : Nat) (q beta : Real) : Real :=
  let M := (Finset.univ : Finset (TriangularBoxVertex n)).sup'
    ⟨triangularBoxRoot n, Finset.mem_univ _⟩ (fun x => ∑ k : ↑(Finset.Icc 1 n),
      triangularBoxConnMass n q beta x k)
  2 * (1 + M) / (n : Real)

theorem triangularBox_differential_inequality
    (n : Nat) (hn : 1 ≤ n) (q beta beta0 : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) (hbeta0 : beta ≤ beta0) :
    ∃ c : Real, 0 < c ∧
      c * (triangularBoxCrossMass n q beta /
        triangularBoxDenom n q beta) ≤
      deriv (triangularBoxCrossMass n q) beta := by
  letI : Nonempty (triangularBoxGraph n).edgeSet :=
    triangularBoxGraph_edgeSet_nonempty n hn
  letI : Nonempty (TriangularBoxVertex n) := ⟨triangularBoxRoot n⟩
  let mu := FK.activeBCProb (triangularBoxGraph n)
    (triangularBoxBoundaryGraph n) (FK.betaParams (fun _ => 1) beta) q
  let M := (Finset.univ : Finset (TriangularBoxVertex n)).sup'
    ⟨triangularBoxRoot n, Finset.mem_univ _⟩ (fun x => ∑ k : ↑(Finset.Icc 1 n),
      triangularBoxConnMass n q beta x k)
  let D := 2 * (1 + M) / (n : Real)
  have hconn0 : ∀ x k, 0 ≤ triangularBoxConnMass n q beta x k := by
    intro x k
    unfold triangularBoxConnMass Lindeberg.mean
    exact Finset.sum_nonneg fun omega _ => mul_nonneg (by
      change 0 ≤ if ConnOpenSet (triangularBoxEndU n) (triangularBoxEndV n)
        omega x (triangularBoxShell n k) then (1 : Real) else 0
      split_ifs <;> norm_num)
        (FK.activeBCProb_pos (triangularBoxGraph n) (triangularBoxBoundaryGraph n)
          (FK.betaParams_pos (fun _ => by norm_num) hbeta)
          (FK.betaParams_lt_one (fun _ => 1) beta)
          (zero_lt_one.trans_le hq) omega).le
  have hM : 0 ≤ M := by
    let x : TriangularBoxVertex n := triangularBoxRoot n
    have hx : x ∈ (Finset.univ : Finset (TriangularBoxVertex n)) := Finset.mem_univ _
    have hx0 : 0 ≤ ∑ k : ↑(Finset.Icc 1 n),
        triangularBoxConnMass n q beta x k :=
      Finset.sum_nonneg fun k _ => hconn0 x k
    exact hx0.trans
      (Finset.le_sup' (fun y => ∑ k : ↑(Finset.Icc 1 n),
        triangularBoxConnMass n q beta y k) hx)
  have hnR : 0 < (n : Real) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hD : 0 < D := by dsimp [D]; positivity
  have hsum : ∀ e : (triangularBoxGraph n).edgeSet,
      (∑ k : ↑(Finset.Icc 1 n),
        (Lindeberg.mean mu (fun omega => if ConnOpenSet
          (triangularBoxEndU n) (triangularBoxEndV n) omega
          (triangularBoxEndU n e) (triangularBoxShell n k) then 1 else 0) +
        Lindeberg.mean mu (fun omega => if ConnOpenSet
          (triangularBoxEndU n) (triangularBoxEndV n) omega
          (triangularBoxEndV n e) (triangularBoxShell n k) then 1 else 0))) ≤
        (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D := by
    intro e
    have hu := Finset.le_sup' (fun x => ∑ k : ↑(Finset.Icc 1 n),
      triangularBoxConnMass n q beta x k)
      (Finset.mem_univ (triangularBoxEndU n e))
    have hv := Finset.le_sup' (fun x => ∑ k : ↑(Finset.Icc 1 n),
      triangularBoxConnMass n q beta x k)
      (Finset.mem_univ (triangularBoxEndV n e))
    have hcard : (Fintype.card (↑(Finset.Icc 1 n)) : Real) = n := by
      rw [Fintype.card_coe, Nat.card_Icc]
      norm_num
    rw [Finset.sum_add_distrib]
    change
      (∑ k : ↑(Finset.Icc 1 n),
          triangularBoxConnMass n q beta (triangularBoxEndU n e) k) +
        (∑ k : ↑(Finset.Icc 1 n),
          triangularBoxConnMass n q beta (triangularBoxEndV n e) k) ≤
        (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D
    calc
      _ ≤ M + M := add_le_add hu hv
      _ ≤ (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D := by
        rw [hcard]
        dsimp [D]
        rw [mul_div_cancel₀ _ hnR.ne']
        linarith
  obtain ⟨c, hc, hmain⟩ := activeBC_openCross_differential_inequality
    (triangularBoxGraph n) (triangularBoxBoundaryGraph n) (fun _ => 1)
    (fun _ => by norm_num) q beta beta0 hq hbeta hbeta0
    (triangularBoxEndU n) (triangularBoxEndV n)
    (triangularBox_end_coherent n) (triangularBoxRoot n)
    (Finset.univ : Finset (triangularBoxGraph n).edgeSet).toList
    (by simp) (triangularBoxShell n) (triangularBoxShell n)
    (by simp) (by simp) (by
      intro k hk
      simp [triangularBoxShell, triangularBoxRoot, vertexBoundary] at hk)
    (by
      intro k m hk hkm omega h
      exact triangularBox_reachOpen_crosses hk hkm omega h)
    n hn D hD hsum
  refine ⟨c, hc, ?_⟩
  simpa [triangularBoxCrossMass, triangularBoxDenom, M, D] using hmain

end StatMech.FK.PeriodicPlanar
