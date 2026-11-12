/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.OSSS.ActiveBoundaryDifferential
import Code.FK.InfiniteVolume
import Code.FK.ActiveBoundaryEquiv
import Code.Lattice.SegmentConn

open scoped BigOperators Classical
open Finset Set

namespace StatMech
namespace OSSS
namespace WiredBoxDifferential

open Lattice RevealmentConstruction AdaptiveCovLowerGeom
open ActiveBoundaryDifferential
open FK RevealmentTranslation


def boxActiveEdge (d n : Nat) :
    (boxGraph d n).edgeSet -> Sym2 (Site d) :=
  fun e => edgeIncl d n e.1



noncomputable def boxActiveEndU (d n : Nat) :
    (boxGraph d n).edgeSet -> Site d :=
  fun e => (e.1.out.1 : boxVerts d n)


noncomputable def boxActiveEndV (d n : Nat) :
    (boxGraph d n).edgeSet -> Site d :=
  fun e => (e.1.out.2 : boxVerts d n)

theorem boxActiveEdge_injective (d n : Nat) :
    Function.Injective (boxActiveEdge d n) := by
  intro e f h
  apply Subtype.ext
  exact edgeIncl_injective d n h

theorem boxActiveEdge_eq_endpoints (d n : Nat)
    (e : (boxGraph d n).edgeSet) :
    boxActiveEdge d n e = s(boxActiveEndU d n e, boxActiveEndV d n e) := by
  change edgeIncl d n e.1 =
    s(((e.1.out.1 : boxVerts d n) : Site d),
      ((e.1.out.2 : boxVerts d n) : Site d))
  calc
    edgeIncl d n e.1 = edgeIncl d n s(e.1.out.1, e.1.out.2) :=
      congrArg (edgeIncl d n) e.1.out_eq.symm
    _ = s(((e.1.out.1 : boxVerts d n) : Site d),
        ((e.1.out.2 : boxVerts d n) : Site d)) := by
      rw [edgeIncl, Sym2.map_mk]

theorem boxActiveEnd_adj (d n : Nat) (e : (boxGraph d n).edgeSet) :
    (hypercubicLattice d).Adj (boxActiveEndU d n e) (boxActiveEndV d n e) := by
  have he : (boxGraph d n).Adj e.1.out.1 e.1.out.2 := by
    rw [← SimpleGraph.mem_edgeSet]
    have hout : s(e.1.out.1, e.1.out.2) = e.1 := e.1.out_eq
    rw [hout]
    exact e.2
  exact he


noncomputable def osssBoxFinset (d n : Nat) : Finset (Site d) :=
  (box_finite d n).toFinset

@[simp] theorem mem_osssBoxFinset {d n : Nat} {x : Site d} :
    x ∈ osssBoxFinset d n <-> x ∈ box d n := by
  rw [osssBoxFinset, Set.Finite.mem_toFinset]


noncomputable def osssBoundaryFinset (d n : Nat) : Finset (Site d) :=
  (vertexBoundary_finite d n).toFinset

@[simp] theorem mem_osssBoundaryFinset {d n : Nat} {x : Site d} :
    x ∈ osssBoundaryFinset d n <-> x ∈ vertexBoundary d n := by
  rw [osssBoundaryFinset, Set.Finite.mem_toFinset]

theorem origin_mem_osssBoxFinset (d n : Nat) :
    (0 : Site d) ∈ osssBoxFinset d n := by
  rw [mem_osssBoxFinset]
  intro i
  simp

theorem origin_not_mem_osssBoundaryFinset (d k : Nat) :
    (0 : Site d) ∉ osssBoundaryFinset d k := by
  rw [mem_osssBoundaryFinset]
  intro h
  exact h.2 (by intro i; simp)

theorem boxActiveEndU_mem (d n : Nat) (e : (boxGraph d n).edgeSet) :
    boxActiveEndU d n e ∈ osssBoxFinset d n := by
  rw [mem_osssBoxFinset]
  exact e.1.out.1.property

theorem boxActiveEndV_mem (d n : Nat) (e : (boxGraph d n).edgeSet) :
    boxActiveEndV d n e ∈ osssBoxFinset d n := by
  rw [mem_osssBoxFinset]
  exact e.1.out.2.property


noncomputable def wiredBoxBoundaryGraph (d n : Nat) :
    SimpleGraph (boxVerts d n) :=
  Lattice.boundaryCliqueGraph (boxBoundary d n)

noncomputable instance instDecidableRelWiredBoxBoundaryGraph (d n : Nat) :
    DecidableRel (wiredBoxBoundaryGraph d n).Adj := Classical.decRel _


noncomputable def wiredFullCrossMass (d n : Nat) (q beta : Real) : Real :=
  ∑ omega : ConfigSpace (Sym2 (boxVerts d n)),
    (FK.restrictActive (boxGraph d n) ⁻¹'
      crossEvent (boxActiveEdge d n) 0 (vertexBoundary d n)).indicator
        (fun _ => (1 : Real)) omega *
      wiredFkProb (boxGraph d n) (boxBoundary d n)
        (1 - Real.exp (-beta)) q omega

theorem activeBox_crossProb_eq_wiredFull
    (d n : Nat) (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    FK.activeBCProbOf (boxGraph d n) (wiredBoxBoundaryGraph d n)
        (FK.betaParams (fun _ => 1) beta) q
        (crossEvent (boxActiveEdge d n) 0 (vertexBoundary d n)) =
      wiredFullCrossMass d n q beta := by
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    have hexp : Real.exp (-beta) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hp1 : p < 1 := by
    unfold p
    linarith [Real.exp_pos (-beta)]
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hparam : FK.betaParams (fun _ : Sym2 (boxVerts d n) => (1 : Real)) beta =
      fun _ => p := by
    funext e
    simp [FK.betaParams, p]
  rw [hparam]
  simpa [wiredBoxBoundaryGraph, wiredFullCrossMass, p] using
    FK.activeBCProbOf_boundaryClique_eq_wired (boxGraph d n)
      (boxBoundary d n) hp hp1 hq0
      (crossEvent (boxActiveEdge d n) 0 (vertexBoundary d n))

theorem activeBox_cross_deriv_eq_wiredFull
    (d n : Nat) (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    deriv (fun b => FK.activeBCProbOf (boxGraph d n)
        (wiredBoxBoundaryGraph d n) (FK.betaParams (fun _ => 1) b) q
        (crossEvent (boxActiveEdge d n) 0 (vertexBoundary d n))) beta =
      deriv (wiredFullCrossMass d n q) beta := by
  have hevent : ∀ᶠ b in nhds beta, 0 < b := Ioi_mem_nhds hbeta
  have heq : (fun b => FK.activeBCProbOf (boxGraph d n)
        (wiredBoxBoundaryGraph d n) (FK.betaParams (fun _ => 1) b) q
        (crossEvent (boxActiveEdge d n) 0 (vertexBoundary d n))) =ᶠ[nhds beta]
      wiredFullCrossMass d n q := by
    filter_upwards [hevent] with b hb
    exact activeBox_crossProb_eq_wiredFull d n q b hq hb
  exact heq.deriv_eq

theorem boxGraph_edgeSet_nonempty (d n : Nat) (hd : 1 <= d) (hn : 1 <= n) :
    Nonempty (boxGraph d n).edgeSet := by
  let j : Fin d := ⟨0, hd⟩
  let x0 : Site d := 0
  let x1 : Site d := Function.update x0 j 1
  have hx0 : x0 ∈ box d n := by
    intro i
    simp [x0]
  have hx1 : x1 ∈ box d n := by
    intro i
    by_cases hi : i = j
    · subst i
      simpa [x1, x0] using hn
    · simp [x1, x0, Function.update_of_ne hi]
  let v0 : boxVerts d n := ⟨x0, hx0⟩
  let v1 : boxVerts d n := ⟨x1, hx1⟩
  refine ⟨⟨s(v0, v1), ?_⟩⟩
  rw [SimpleGraph.mem_edgeSet]
  change (hypercubicLattice d).Adj x0 x1
  have hstep := Lattice.adj_update_succ x0 j 0
  simpa [x1, x0] using hstep

noncomputable def wiredActiveTheta (d n : Nat) (q beta : Real) : Real :=
  Lindeberg.mean
    (FK.activeBCProb (boxGraph d n) (wiredBoxBoundaryGraph d n)
      (FK.betaParams (fun _ => 1) beta) q)
    (crossIndG (boxActiveEdge d n) 0 n)

noncomputable def wiredActiveDenom (d n : Nat) (q beta : Real) : Real :=
  4 * (osssBoxFinset d n).sup' (by
      exact ⟨0, origin_mem_osssBoxFinset d n⟩)
    (fun x => ∑ j ∈ Finset.range n,
      Lindeberg.mean
        (FK.activeBCProb (boxGraph d n) (wiredBoxBoundaryGraph d n)
          (FK.betaParams (fun _ => 1) beta) q)
        (fun omega => if ConnectedToSet d
          (liftCfg (boxActiveEdge d n) omega) x (centeredBoundary x j)
          then (1 : Real) else 0)) / (n : Real)



theorem wired_box_differential_inequality
    (d n : Nat) (hd : 1 <= d) (hn : 1 <= n)
    (q beta beta0 : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (hbeta0 : beta <= beta0) :
    exists c : Real, 0 < c ∧
      c * (Lindeberg.mean
          (FK.activeBCProb (boxGraph d n) (wiredBoxBoundaryGraph d n)
            (FK.betaParams (fun _ => 1) beta) q)
          (crossIndG (boxActiveEdge d n) 0 n) /
        (4 * (osssBoxFinset d n).sup' (by
            exact ⟨0, origin_mem_osssBoxFinset d n⟩)
          (fun x => ∑ j ∈ Finset.range n,
            Lindeberg.mean
              (FK.activeBCProb (boxGraph d n) (wiredBoxBoundaryGraph d n)
                (FK.betaParams (fun _ => 1) beta) q)
              (fun omega => if ConnectedToSet d
                (liftCfg (boxActiveEdge d n) omega) x (centeredBoundary x j)
                then (1 : Real) else 0)) / (n : Real))) <=
      deriv (fun b => FK.activeBCProbOf (boxGraph d n)
        (wiredBoxBoundaryGraph d n) (FK.betaParams (fun _ => 1) b) q
        (crossEvent (boxActiveEdge d n) 0 (vertexBoundary d n))) beta := by
  letI : Nonempty (boxGraph d n).edgeSet := boxGraph_edgeSet_nonempty d n hd hn
  let Lambda := osssBoxFinset d n
  have hne : Lambda.Nonempty := ⟨0, origin_mem_osssBoxFinset d n⟩
  let disc0 : Nat -> Finset (Site d) := osssBoundaryFinset d
  let C := wiredBoxBoundaryGraph d n
  let J : Sym2 (boxVerts d n) -> Real := fun _ => 1
  have hJ : forall e, 0 < J e := fun _ => by norm_num
  have hinj := boxActiveEdge_injective d n
  have hcoh := boxActiveEdge_eq_endpoints d n
  have hadj := boxActiveEnd_adj d n
  have hl : forall e : (boxGraph d n).edgeSet,
      e ∈ (Finset.univ : Finset (boxGraph d n).edgeSet).toList := by simp
  have hdisc0sub : ∀ k, ∀ x ∈ disc0 k, x ∈ vertexBoundary d k := by
    intro k x hx
    simpa [disc0] using hx
  have hdisc0sup : ∀ k, ∀ x ∈ vertexBoundary d k, x ∈ disc0 k := by
    intro k x hx
    simpa [disc0] using hx
  have hoB : forall k, (0 : Site d) ∉ disc0 k := by
    intro k
    exact origin_not_mem_osssBoundaryFinset d k
  have ho : forall k : Nat, 1 <= k -> (0 : Site d) ∈ box d (k - 1) := by
    intro k hk i
    simp
  have hLu : forall e : (boxGraph d n).edgeSet,
      boxActiveEndU d n e ∈ Lambda := boxActiveEndU_mem d n
  have hLv : forall e : (boxGraph d n).edgeSet,
      boxActiveEndV d n e ∈ Lambda := boxActiveEndV_mem d n
  have hUbox : forall e : (boxGraph d n).edgeSet,
      boxActiveEndU d n e ∈ box d n := fun e => e.1.out.1.property
  have hVbox : forall e : (boxGraph d n).edgeSet,
      boxActiveEndV d n e ∈ box d n := fun e => e.1.out.2.property
  have hmain := activeBC_fk_differential_inequality
    (boxGraph d n) C J hJ q beta beta0 hq hbeta hbeta0 hinj hcoh hadj
    (0 : Site d) (Finset.univ : Finset (boxGraph d n).edgeSet).toList hl
    disc0 hdisc0sub hdisc0sup hoB ho n hn Lambda hne hLu hLv hUbox hVbox
  simpa [C, J, Lambda, disc0] using hmain



theorem wired_box_differential_inequality_full
    (d n : Nat) (hd : 1 <= d) (hn : 1 <= n)
    (q beta beta0 : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (hbeta0 : beta <= beta0) :
    exists c : Real, 0 < c ∧
      c * (wiredActiveTheta d n q beta / wiredActiveDenom d n q beta) <=
        deriv (wiredFullCrossMass d n q) beta := by
  obtain ⟨c, hc, hmain⟩ := wired_box_differential_inequality
    d n hd hn q beta beta0 hq hbeta hbeta0
  rw [activeBox_cross_deriv_eq_wiredFull d n q beta hq hbeta] at hmain
  exact ⟨c, hc, by
    simpa [wiredActiveTheta, wiredActiveDenom] using hmain⟩

end WiredBoxDifferential
end OSSS
end StatMech
