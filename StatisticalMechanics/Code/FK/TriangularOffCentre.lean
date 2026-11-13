/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriangularSharpness
import Code.FK.BoundaryEdgeAbsorption
import Code.OSSS.FKSharpnessWeightedDomainActive










open scoped BigOperators Classical
open Finset Set SimpleGraph

namespace StatMech.FK

open StatMech.Lattice
open StatMech.OSSS.RevealmentConstruction
open StatMech.OSSS.FiniteGraphBoundaryDifferential

noncomputable section

variable {V : Type*} [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable {Sin Sout : Set V} [Fintype Sin] [Fintype Sout]



theorem ocd_comapAdjMatch
    (iota : Sin -> Sout) (hiotaVal : forall x, (iota x : V) = (x : V)) :
    ocd_AdjMatch (SimpleGraph.comap Subtype.val G)
      (SimpleGraph.comap Subtype.val G) iota := by
  intro x y
  rw [SimpleGraph.comap_adj, SimpleGraph.comap_adj, hiotaVal x, hiotaVal y]




theorem ocd_comap_bdryIn_of_outsideGraph_adj
    (iota : Sin -> Sout) (hiotaVal : forall x, (iota x : V) = (x : V))
    (bdryOut : Sout -> Prop) [DecidablePred bdryOut]
    (bdryIn : Sin -> Prop) [DecidablePred bdryIn]
    (hmargin : forall x : Sin, ¬ bdryOut (iota x))
    (hbdryIn : forall (x : Sin) (z : V), G.Adj x.1 z -> z ∉ Sin -> bdryIn x)
    (psi : ConfigSpace (Sym2 Sout)) {x : Sin} {z : Sout}
    (h : (ocd_outsideGraph (SimpleGraph.comap Subtype.val G)
      iota bdryOut psi).Adj (iota x) z) :
    bdryIn x := by
  rw [ocd_outsideGraph_adj] at h
  rcases h with ⟨hadj, _, hrange⟩ | ⟨_, hb, _⟩
  · have hznot : (z : V) ∉ Sin := by
      intro hz
      refine hrange ⟨s(x, ⟨(z : V), hz⟩), ?_⟩
      rw [ocd_innerEdge_mk]
      have hzeq : iota ⟨(z : V), hz⟩ = z :=
        Subtype.ext (hiotaVal ⟨(z : V), hz⟩)
      rw [hzeq]
    have hadj' : G.Adj x.1 z.1 := by
      rw [SimpleGraph.comap_adj] at hadj
      rw [hiotaVal x] at hadj
      exact hadj
    exact hbdryIn x z.1 hadj' hznot
  · exact absurd hb (hmargin x)




theorem ocd_comapInducedWiring_le
    (iota : Sin -> Sout) (hiotaVal : forall x, (iota x : V) = (x : V))
    (hiota : Function.Injective iota)
    (bdryOut : Sout -> Prop) [DecidablePred bdryOut]
    (bdryIn : Sin -> Prop) [DecidablePred bdryIn]
    (hmargin : forall x : Sin, ¬ bdryOut (iota x))
    (hbdryIn : forall (x : Sin) (z : V), G.Adj x.1 z -> z ∉ Sin -> bdryIn x)
    (psi : ConfigSpace (Sym2 Sout)) :
    ocd_inducedWiring (SimpleGraph.comap Subtype.val G) iota bdryOut psi <=
      boundaryCliqueGraph bdryIn := by
  intro x y hxy
  obtain ⟨hne, hreach⟩ := hxy
  rw [boundaryCliqueGraph_adj]
  refine ⟨hne, ?_, ?_⟩
  · have hne' : iota x ≠ iota y := fun h => hne (hiota h)
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    rcases hreach.cases_head with heq | ⟨z, hadj, _⟩
    · exact absurd heq hne'
    · exact ocd_comap_bdryIn_of_outsideGraph_adj G iota hiotaVal
        bdryOut bdryIn hmargin hbdryIn psi hadj
  · have hreach' :
        (ocd_outsideGraph (SimpleGraph.comap Subtype.val G)
          iota bdryOut psi).Reachable (iota y) (iota x) := hreach.symm
    have hne' : iota y ≠ iota x := fun h => hne (hiota h).symm
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach'
    rcases hreach'.cases_head with heq | ⟨z, hadj, _⟩
    · exact absurd heq hne'
    · exact ocd_comap_bdryIn_of_outsideGraph_adj G iota hiotaVal
        bdryOut bdryIn hmargin hbdryIn psi hadj



theorem ocd_comapInducedWiring_le_equiv
    (e : V ≃ V) (he : ∀ x y, G.Adj (e x) (e y) ↔ G.Adj x y)
    (iota : Sin -> Sout) (hiotaVal : ∀ x, (iota x : V) = e (x : V))
    (hiota : Function.Injective iota)
    (bdryOut : Sout -> Prop) [DecidablePred bdryOut]
    (bdryIn : Sin -> Prop) [DecidablePred bdryIn]
    (hmargin : ∀ x : Sin, ¬ bdryOut (iota x))
    (hbdryIn : ∀ (x : Sin) (z : V), G.Adj x.1 z -> z ∉ Sin -> bdryIn x)
    (psi : ConfigSpace (Sym2 Sout)) :
    ocd_inducedWiring (SimpleGraph.comap Subtype.val G) iota bdryOut psi <=
      boundaryCliqueGraph bdryIn := by
  have hfirst : ∀ (x : Sin) (z : Sout),
      (ocd_outsideGraph (SimpleGraph.comap Subtype.val G)
        iota bdryOut psi).Adj (iota x) z -> bdryIn x := by
    intro x z h
    rw [ocd_outsideGraph_adj] at h
    rcases h with ⟨hadj, _, hrange⟩ | ⟨_, hb, _⟩
    · have hznot : e.symm (z : V) ∉ Sin := by
        intro hz
        refine hrange ⟨s(x, ⟨e.symm (z : V), hz⟩), ?_⟩
        rw [ocd_innerEdge_mk]
        have hzeq : iota ⟨e.symm (z : V), hz⟩ = z := by
          apply Subtype.ext
          rw [hiotaVal]
          exact e.apply_symm_apply (z : V)
        rw [hzeq]
      have hadj' : G.Adj x.1 (e.symm (z : V)) := by
        rw [SimpleGraph.comap_adj, hiotaVal x] at hadj
        apply (he x.1 (e.symm (z : V))).mp
        simpa using hadj
      exact hbdryIn x (e.symm (z : V)) hadj' hznot
    · exact absurd hb (hmargin x)
  intro x y hxy
  obtain ⟨hne, hreach⟩ := hxy
  rw [boundaryCliqueGraph_adj]
  refine ⟨hne, ?_, ?_⟩
  · have hne' : iota x ≠ iota y := fun h => hne (hiota h)
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    rcases hreach.cases_head with heq | ⟨z, hadj, _⟩
    · exact absurd heq hne'
    · exact hfirst x z hadj
  · have hreach' :
        (ocd_outsideGraph (SimpleGraph.comap Subtype.val G)
          iota bdryOut psi).Reachable (iota y) (iota x) := hreach.symm
    have hne' : iota y ≠ iota x := fun h => hne (hiota h).symm
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach'
    rcases hreach'.cases_head with heq | ⟨z, hadj, _⟩
    · exact absurd heq hne'
    · exact hfirst y z hadj

end

end StatMech.FK

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice
open StatMech.OSSS.RevealmentConstruction
open StatMech.OSSS.FiniteGraphBoundaryDifferential

noncomputable section



abbrev triangularTransBox (R : Nat) (x : Site 2) : Set (Site 2) :=
  StatMech.FK.fvs_transBox 2 R x

abbrev TriangularTransBoxVertex (R : Nat) (x : Site 2) :=
  {y : Site 2 // y ∈ triangularTransBox R x}

def triangularTransBoxGraph (R : Nat) (x : Site 2) :
    SimpleGraph (TriangularTransBoxVertex R x) :=
  SimpleGraph.comap Subtype.val triangularGraph

noncomputable instance (R : Nat) (x : Site 2) :
    DecidableRel (triangularTransBoxGraph R x).Adj := Classical.decRel _

def triangularTransBoxIncl {R N : Nat} {x : Site 2}
    (hsub : triangularTransBox R x ⊆ box 2 N) :
    TriangularTransBoxVertex R x -> TriangularBoxVertex N :=
  fun y => ⟨y.1, hsub y.2⟩

@[simp] theorem triangularTransBoxIncl_val {R N : Nat} {x : Site 2}
    (hsub : triangularTransBox R x ⊆ box 2 N)
    (y : TriangularTransBoxVertex R x) :
    (triangularTransBoxIncl hsub y : Site 2) = y.1 := rfl

theorem triangularTransBoxIncl_injective {R N : Nat} {x : Site 2}
    (hsub : triangularTransBox R x ⊆ box 2 N) :
    Function.Injective (triangularTransBoxIncl hsub) := by
  intro y z hyz
  apply Subtype.ext
  exact congrArg (fun w : TriangularBoxVertex N => (w : Site 2)) hyz


def triangularTransBoxBoundary (R : Nat) (x : Site 2)
    (y : TriangularTransBoxVertex R x) : Prop :=
  y.1 - x ∈ vertexBoundary 2 R

noncomputable def triangularTransBoxShell (R k : Nat) (x : Site 2) :
    Finset (TriangularTransBoxVertex R x) :=
  Finset.univ.filter fun y => y.1 - x ∈ vertexBoundary 2 k

def triangularTransBoxCenter (R : Nat) (x : Site 2) :
    TriangularTransBoxVertex R x :=
  ⟨x, by simp [StatMech.FK.fvs_transBox]⟩



theorem triangularTransEquiv_adj (R : Nat) (x : Site 2)
    (u v : TriangularBoxVertex R) :
    (triangularBoxGraph R).Adj u v ↔
      (triangularTransBoxGraph R x).Adj
        (StatMech.FK.fvs_transEquiv 2 R x u)
        (StatMech.FK.fvs_transEquiv 2 R x v) := by
  rw [triangularBoxGraph, triangularTransBoxGraph,
    SimpleGraph.comap_adj, SimpleGraph.comap_adj,
    StatMech.FK.fvs_transEquiv_val, StatMech.FK.fvs_transEquiv_val,
    triangularGraph_adj, triangularGraph_adj]
  unfold triangularAdj
  constructor
  · rintro ⟨i, h | h⟩
    · refine ⟨i, Or.inl ?_⟩
      calc
        (v.1 + x) - (u.1 + x) = v.1 - u.1 := by abel
        _ = triangularStep i := h
    · refine ⟨i, Or.inr ?_⟩
      calc
        (u.1 + x) - (v.1 + x) = u.1 - v.1 := by abel
        _ = triangularStep i := h
  · rintro ⟨i, h | h⟩
    · refine ⟨i, Or.inl ?_⟩
      calc
        v.1 - u.1 = (v.1 + x) - (u.1 + x) := by abel
        _ = triangularStep i := h
    · refine ⟨i, Or.inr ?_⟩
      calc
        u.1 - v.1 = (u.1 + x) - (v.1 + x) := by abel
        _ = triangularStep i := h

@[simp] theorem triangularTransEquiv_center (R : Nat) (x : Site 2) :
    StatMech.FK.fvs_transEquiv 2 R x (triangularBoxRoot R) =
      triangularTransBoxCenter R x := by
  apply Subtype.ext
  funext i
  simp [triangularBoxRoot, triangularTransBoxCenter]

theorem triangularTransEquiv_mem_shell (R k : Nat) (x : Site 2)
    (y : TriangularBoxVertex R) :
    StatMech.FK.fvs_transEquiv 2 R x y ∈ triangularTransBoxShell R k x ↔
      y ∈ triangularBoxShell R k := by
  simp [triangularTransBoxShell, triangularBoxShell,
    StatMech.FK.fvs_transEquiv_val]

noncomputable def triangularTransBoxEndU (R : Nat) (x : Site 2) :
    (triangularTransBoxGraph R x).edgeSet -> TriangularTransBoxVertex R x :=
  fun e => e.1.out.1

noncomputable def triangularTransBoxEndV (R : Nat) (x : Site 2) :
    (triangularTransBoxGraph R x).edgeSet -> TriangularTransBoxVertex R x :=
  fun e => e.1.out.2



def triangularTransShellEvent (R k : Nat) (x : Site 2) :
    Set (ConfigSpace (triangularTransBoxGraph R x).edgeSet) :=
  openCrossEvent (triangularTransBoxEndU R x) (triangularTransBoxEndV R x)
    (triangularTransBoxCenter R x) (triangularTransBoxShell R k x)



def triangularCenteredShellEvent (R k : Nat) :
    Set (ConfigSpace (triangularBoxGraph R).edgeSet) :=
  openCrossEvent (triangularBoxEndU R) (triangularBoxEndV R)
    (triangularBoxRoot R) (triangularBoxShell R k)

theorem triangularTransShellEvent_increasing (R k : Nat) (x : Site 2) :
    IsIncreasing (triangularTransShellEvent R k x) :=
  openCrossEvent_isIncreasing _ _ _ _

theorem triangularCenteredShellEvent_increasing (R k : Nat) :
    IsIncreasing (triangularCenteredShellEvent R k) :=
  openCrossEvent_isIncreasing _ _ _ _



theorem reachOpen_edgeSet_iff_openSub_reachable
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (omega : ConfigSpace H.edgeSet) (u v : W) :
    ReachOpen (fun e : H.edgeSet => e.1.out.1)
        (fun e : H.edgeSet => e.1.out.2) omega u v ↔
      (openSub H (extendActive H omega)).Reachable u v := by
  constructor
  · intro h
    induction h with
    | refl w => exact SimpleGraph.Reachable.refl w
    | @step a b c e hopen hpair _ ih =>
        have hedge : (openSub H (extendActive H omega)).Adj
            e.1.out.1 e.1.out.2 := by
          rw [openSub_adj]
          refine ⟨?_, ?_⟩
          · rw [← SimpleGraph.mem_edgeSet]
            have hout : s(e.1.out.1, e.1.out.2) = e.1 := e.1.out_eq
            rw [hout]
            exact e.2
          · calc
              extendActive H omega s(e.1.out.1, e.1.out.2) =
                  extendActive H omega e.1 := congrArg _ e.1.out_eq
              _ = omega e := extendActive_apply H omega e
              _ = true := hopen
        rcases hpair with ⟨hU, hV⟩ | ⟨hU, hV⟩
        · rw [hU, hV] at hedge
          exact hedge.reachable.trans ih
        · rw [hU, hV] at hedge
          exact hedge.symm.reachable.trans ih
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact ReachOpen.refl u
    | @tail a b _ hab ih =>
        rw [openSub_adj] at hab
        let e : H.edgeSet := ⟨s(a, b), by
          rw [SimpleGraph.mem_edgeSet]
          exact hab.1⟩
        have hopen : omega e = true := by
          have hext := extendActive_apply H omega e
          have hopenfull : extendActive H omega s(a, b) = true := hab.2
          exact hext.symm.trans hopenfull
        have hepair :
            ((fun e : H.edgeSet => e.1.out.1) e = a ∧
              (fun e : H.edgeSet => e.1.out.2) e = b) ∨
            ((fun e : H.edgeSet => e.1.out.1) e = b ∧
              (fun e : H.edgeSet => e.1.out.2) e = a) := by
          have hout : s(e.1.out.1, e.1.out.2) = s(a, b) := e.1.out_eq
          exact Sym2.eq_iff.mp hout
        exact ih.trans (ReachOpen.step e hopen hepair (ReachOpen.refl b))

theorem connOpenSet_edgeSet_iff_openSub
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (omega : ConfigSpace H.edgeSet) (u : W) (B : Set W) :
    ConnOpenSet (fun e : H.edgeSet => e.1.out.1)
        (fun e : H.edgeSet => e.1.out.2) omega u B ↔
      ∃ v ∈ B, (openSub H (extendActive H omega)).Reachable u v := by
  simp only [ConnOpenSet]
  apply exists_congr
  intro v
  apply and_congr_right
  intro _
  exact reachOpen_edgeSet_iff_openSub_reachable H omega u v

def triangularCenteredShellFullEvent (R k : Nat) :
    Set (ConfigSpace (Sym2 (TriangularBoxVertex R))) :=
  {omega | ∃ y ∈ triangularBoxShell R k,
    (openSub (triangularBoxGraph R) omega).Reachable (triangularBoxRoot R) y}

def triangularTransShellFullEvent (R k : Nat) (x : Site 2) :
    Set (ConfigSpace (Sym2 (TriangularTransBoxVertex R x))) :=
  {omega | ∃ y ∈ triangularTransBoxShell R k x,
    (openSub (triangularTransBoxGraph R x) omega).Reachable
      (triangularTransBoxCenter R x) y}



theorem restrictActive_preimage_triangularCenteredShellEvent
    (R k : Nat) :
    restrictActive (triangularBoxGraph R) ⁻¹'
        triangularCenteredShellEvent R k =
      triangularCenteredShellFullEvent R k := by
  ext omega
  change ConnOpenSet (triangularBoxEndU R) (triangularBoxEndV R)
      (restrictActive (triangularBoxGraph R) omega)
      (triangularBoxRoot R) (triangularBoxShell R k) ↔
    ∃ y ∈ triangularBoxShell R k,
      (openSub (triangularBoxGraph R) omega).Reachable (triangularBoxRoot R) y
  unfold triangularBoxEndU triangularBoxEndV
  rw [connOpenSet_edgeSet_iff_openSub]
  rw [openSub_extendActive_restrictActive_eq]
  simp

theorem restrictActive_preimage_triangularTransShellEvent
    (R k : Nat) (x : Site 2) :
    restrictActive (triangularTransBoxGraph R x) ⁻¹'
        triangularTransShellEvent R k x =
      triangularTransShellFullEvent R k x := by
  ext omega
  change ConnOpenSet (triangularTransBoxEndU R x)
      (triangularTransBoxEndV R x)
      (restrictActive (triangularTransBoxGraph R x) omega)
      (triangularTransBoxCenter R x) (triangularTransBoxShell R k x) ↔
    ∃ y ∈ triangularTransBoxShell R k x,
      (openSub (triangularTransBoxGraph R x) omega).Reachable
        (triangularTransBoxCenter R x) y
  unfold triangularTransBoxEndU triangularTransBoxEndV
  rw [connOpenSet_edgeSet_iff_openSub]
  rw [openSub_extendActive_restrictActive_eq]
  simp



theorem reCfgIso_preimage_triangularCenteredShellFullEvent
    (R k : Nat) (x : Site 2) :
    reCfgIso (StatMech.FK.fvs_transEquiv 2 R x) ⁻¹'
        triangularCenteredShellFullEvent R k =
      triangularTransShellFullEvent R k x := by
  ext omega
  let sigma := StatMech.FK.fvs_transEquiv 2 R x
  let iso := fvs_openSubIso (triangularBoxGraph R)
    (triangularTransBoxGraph R x) sigma
    (triangularTransEquiv_adj R x) omega
  constructor
  · rintro ⟨y, hy, hreach⟩
    refine ⟨sigma y, (triangularTransEquiv_mem_shell R k x y).2 hy, ?_⟩
    rw [← triangularTransEquiv_center R x]
    exact iso.reachable_iff.mpr hreach
  · rintro ⟨y, hy, hreach⟩
    let y0 : TriangularBoxVertex R := sigma.symm y
    refine ⟨y0, ?_, ?_⟩
    · apply (triangularTransEquiv_mem_shell R k x y0).1
      simpa [sigma, y0] using hy
    · apply iso.reachable_iff.mp
      change (openSub (triangularTransBoxGraph R x) omega).Reachable
        (sigma (triangularBoxRoot R)) (sigma y0)
      rw [triangularTransEquiv_center]
      simpa [sigma, y0] using hreach



theorem triangularTransEquiv_boundary (R : Nat) (x : Site 2)
    (y : TriangularBoxVertex R) :
    y ∈ triangularBoxShell R R ↔
      triangularTransBoxBoundary R x
        (StatMech.FK.fvs_transEquiv 2 R x y) := by
  simp [triangularBoxShell, triangularTransBoxBoundary,
    StatMech.FK.fvs_transEquiv_val]




theorem triangularTransShellEvent_activeBCMean_eq_centeredFullMass
    (R k : Nat) (x : Site 2) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    activeBCMean (triangularTransBoxGraph R x)
        (boundaryCliqueGraph (triangularTransBoxBoundary R x))
        (fun _ => p) q
        ((triangularTransShellEvent R k x).indicator fun _ => (1 : Real)) =
      ∑ omega : ConfigSpace (Sym2 (TriangularBoxVertex R)),
        (triangularCenteredShellFullEvent R k).indicator
            (fun _ => (1 : Real)) omega *
          wiredFkProb (triangularBoxGraph R)
            (fun y => y ∈ triangularBoxShell R R) p q omega := by
  rw [activeBCMean_boundaryClique_eq_wired
    (triangularTransBoxGraph R x) (triangularTransBoxBoundary R x)
    hp hp1 hq]
  calc
    (∑ omega : ConfigSpace (Sym2 (TriangularTransBoxVertex R x)),
        (triangularTransShellEvent R k x).indicator (fun _ => (1 : Real))
            (restrictActive (triangularTransBoxGraph R x) omega) *
          wiredFkProb (triangularTransBoxGraph R x)
            (triangularTransBoxBoundary R x) p q omega) =
      ∑ omega : ConfigSpace (Sym2 (TriangularTransBoxVertex R x)),
        (triangularTransShellFullEvent R k x).indicator
            (fun _ => (1 : Real)) omega *
          wiredFkProb (triangularTransBoxGraph R x)
            (triangularTransBoxBoundary R x) p q omega := by
      apply Finset.sum_congr rfl
      intro omega _
      have hevent :
          restrictActive (triangularTransBoxGraph R x) omega ∈
              triangularTransShellEvent R k x ↔
            omega ∈ triangularTransShellFullEvent R k x := by
        rw [← Set.mem_preimage]
        exact Set.ext_iff.mp
          (restrictActive_preimage_triangularTransShellEvent R k x) omega
      by_cases h : restrictActive (triangularTransBoxGraph R x) omega ∈
          triangularTransShellEvent R k x
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hevent.mp h)]
      · rw [Set.indicator_of_notMem h,
          Set.indicator_of_notMem (mt hevent.mpr h)]
    _ = ∑ omega : ConfigSpace (Sym2 (TriangularBoxVertex R)),
        (triangularCenteredShellFullEvent R k).indicator
            (fun _ => (1 : Real)) omega *
          wiredFkProb (triangularBoxGraph R)
            (fun y => y ∈ triangularBoxShell R R) p q omega := by
      rw [← cdc_eventMassProb_reCfgIso_inv
        (StatMech.FK.fvs_transEquiv 2 R x)
        (wiredFkProb (triangularBoxGraph R)
          (fun y => y ∈ triangularBoxShell R R) p q)
        (wiredFkProb (triangularTransBoxGraph R x)
          (triangularTransBoxBoundary R x) p q)
        (fun omega => fvs_wiredFkProb_reCfgIso
          (triangularBoxGraph R) (triangularTransBoxGraph R x)
          (fun y => y ∈ triangularBoxShell R R)
          (triangularTransBoxBoundary R x)
          (StatMech.FK.fvs_transEquiv 2 R x)
          (triangularTransEquiv_adj R x)
          (triangularTransEquiv_boundary R x) p q omega)
        (triangularCenteredShellFullEvent R k)]
      rw [reCfgIso_preimage_triangularCenteredShellFullEvent]


theorem triangularTransShellEvent_betaMean_eq_centeredFullMass
    (R k : Nat) (x : Site 2) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta) :
    activeBCMean (triangularTransBoxGraph R x)
        (boundaryCliqueGraph (triangularTransBoxBoundary R x))
        (betaParams (fun _ => 1) beta) q
        ((triangularTransShellEvent R k x).indicator fun _ => (1 : Real)) =
      ∑ omega : ConfigSpace (Sym2 (TriangularBoxVertex R)),
        (triangularCenteredShellFullEvent R k).indicator
            (fun _ => (1 : Real)) omega *
          wiredFkProb (triangularBoxGraph R)
            (fun y => y ∈ triangularBoxShell R R)
            (1 - Real.exp (-beta)) q omega := by
  have hp : 0 < 1 - Real.exp (-beta) := by
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : 1 - Real.exp (-beta) < 1 := by
    linarith [Real.exp_pos (-beta)]
  have hparam : betaParams (fun _ : Sym2 (TriangularTransBoxVertex R x) => 1) beta =
      fun _ => 1 - Real.exp (-beta) := by
    funext e
    simp [betaParams]
  rw [hparam]
  exact triangularTransShellEvent_activeBCMean_eq_centeredFullMass
    R k x hp hp1 hq


theorem triangularTransBox_subset_double
    {n k : Nat} {x : Site 2} (hx : x ∈ box 2 n) (hkn : 2 * k < n) :
    triangularTransBox (2 * k) x ⊆ box 2 (2 * n) := by
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



theorem triangularTransBox_outer_margin
    {n k : Nat} {x : Site 2} (hx : x ∈ box 2 n) (hkn : 2 * k < n)
    (y : TriangularTransBoxVertex (2 * k) x) :
    triangularTransBoxIncl (triangularTransBox_subset_double hx hkn) y ∉
      triangularBoxShell (2 * n) (2 * n) := by
  intro hybdry
  have hycoord := (Finset.mem_filter.mp hybdry).2.2
  have hybox : y.1 ∈ box 2 (2 * n - 1) := by
    intro i
    have hyi : ((y.1 - x) i).natAbs <= 2 * k := y.2 i
    have hxi : (x i).natAbs <= n := hx i
    have heq : y.1 i = (y.1 i - x i) + x i := by ring
    calc
      (y.1 i).natAbs = ((y.1 i - x i) + x i).natAbs := by rw [← heq]
      _ <= (y.1 i - x i).natAbs + (x i).natAbs := Int.natAbs_add_le _ _
      _ = ((y.1 - x) i).natAbs + (x i).natAbs := by simp [Pi.sub_apply]
      _ <= 2 * k + n := Nat.add_le_add hyi hxi
      _ <= 2 * n - 1 := by omega
  exact hycoord hybox

theorem triangular_adj_sub_right (x : Site 2) {y z : Site 2}
    (hyz : triangularGraph.Adj y z) :
    triangularGraph.Adj (y - x) (z - x) := by
  rw [triangularGraph_adj] at hyz ⊢
  obtain ⟨i, h | h⟩ := hyz
  · refine ⟨i, Or.inl ?_⟩
    calc
      (z - x) - (y - x) = z - y := by abel
      _ = triangularStep i := h
  · refine ⟨i, Or.inr ?_⟩
    calc
      (y - x) - (z - x) = y - z := by abel
      _ = triangularStep i := h



theorem triangularTransBox_boundary_of_adj_outside
    {R : Nat} (hR : 1 <= R) {x : Site 2}
    (y : TriangularTransBoxVertex R x) (z : Site 2)
    (hyz : triangularGraph.Adj y.1 z) (hz : z ∉ triangularTransBox R x) :
    triangularTransBoxBoundary R x y := by
  have hybox : y.1 - x ∈ box 2 R := y.2
  have hzstep : z - x ∈ box 2 (R + 1) := by
    have hadj : triangularGraph.Adj (y.1 - x) (z - x) :=
      triangular_adj_sub_right x hyz
    exact triangular_adj_mem_box_succ hybox hadj
  refine ⟨hybox, ?_⟩
  intro hsmall
  have hzR : z - x ∈ box 2 R := by
    have hadj : triangularGraph.Adj (y.1 - x) (z - x) :=
      triangular_adj_sub_right x hyz
    exact triangular_adj_mem_box_of_mem_pred hR hsmall hadj
  exact hz hzR



theorem triangularTransBox_inducedWiring_le
    {n k : Nat} {x : Site 2} (hx : x ∈ box 2 n)
    (hk : 1 <= k) (hkn : 2 * k < n)
    (psi : ConfigSpace (Sym2 (TriangularBoxVertex (2 * n)))) :
    ocd_inducedWiring (triangularBoxGraph (2 * n))
        (triangularTransBoxIncl (triangularTransBox_subset_double hx hkn))
        (fun y => y ∈ triangularBoxShell (2 * n) (2 * n)) psi <=
      boundaryCliqueGraph (triangularTransBoxBoundary (2 * k) x) := by
  let hsub := triangularTransBox_subset_double hx hkn
  apply StatMech.FK.ocd_comapInducedWiring_le triangularGraph
    (triangularTransBoxIncl hsub)
    (fun _ => rfl) (triangularTransBoxIncl_injective hsub)
    (fun y => y ∈ triangularBoxShell (2 * n) (2 * n))
    (triangularTransBoxBoundary (2 * k) x)
  · intro y
    exact triangularTransBox_outer_margin hx hkn y
  · intro y z hyz hz
    exact triangularTransBox_boundary_of_adj_outside (by omega) y z hyz hz



theorem triangularTransBox_activeBCMean_le
    {n k : Nat} {x : Site 2} (hx : x ∈ box 2 n)
    (hk : 1 <= k) (hkn : 2 * k < n)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    {A : Set (ConfigSpace (triangularTransBoxGraph (2 * k) x).edgeSet)}
    (hA : IsIncreasing A) :
    activeBCMean (triangularBoxGraph (2 * n))
        (boundaryCliqueGraph
          (fun y => y ∈ triangularBoxShell (2 * n) (2 * n)))
        (betaParams (fun _ => 1) beta) q
        (fun rho => A.indicator (fun _ => (1 : Real))
          (ocd_innerRestrictActive
            (triangularTransBoxGraph (2 * k) x)
            (triangularBoxGraph (2 * n))
            (triangularTransBoxIncl
              (triangularTransBox_subset_double hx hkn))
            (ocd_comapAdjMatch triangularGraph
              (triangularTransBoxIncl
                (triangularTransBox_subset_double hx hkn))
              (fun _ => rfl)) rho)) <=
      activeBCMean (triangularTransBoxGraph (2 * k) x)
        (boundaryCliqueGraph (triangularTransBoxBoundary (2 * k) x))
        (betaParams (fun _ => 1) beta) q
        (A.indicator fun _ => (1 : Real)) := by
  let hsub := triangularTransBox_subset_double hx hkn
  let iota := triangularTransBoxIncl hsub
  have hadjm : ocd_AdjMatch (triangularTransBoxGraph (2 * k) x)
      (triangularBoxGraph (2 * n)) iota :=
    ocd_comapAdjMatch triangularGraph iota (fun _ => rfl)
  have hparam : ocd_ParamCompatible iota
      (betaParams (fun _ => 1) beta)
      (betaParams (fun _ => 1) beta) := by
    intro e
    simp [betaParams]
  have hwire := fun psi => triangularTransBox_inducedWiring_le
    hx hk hkn psi
  exact ocd_wired_inner_dominated_activeBCMean
    (triangularTransBoxGraph (2 * k) x) (triangularBoxGraph (2 * n)) iota
    (fun y => y ∈ triangularBoxShell (2 * n) (2 * n))
    (triangularTransBoxIncl_injective hsub) hadjm
    (triangularTransBoxBoundary (2 * k) x) hparam
    (betaParams_pos (fun _ => by norm_num) hbeta)
    (betaParams_lt_one (fun _ => 1) beta)
    (betaParams_pos (fun _ => by norm_num) hbeta)
    (betaParams_lt_one (fun _ => 1) beta) hq hwire hA

end

end StatMech.FK.PeriodicPlanar
