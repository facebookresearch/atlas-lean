/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.ClusterExplorationFreeBoundary
import Code.FK.FKDisjointBoxDomainMarkov










open SimpleGraph

namespace StatMech.FK

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


def clusterAdaptiveInsideEdges (roots : Finset V)
    (rho : ConfigSpace (Sym2 V)) : Finset (Sym2 V) :=
  clusterUnexploredPairEdges G rho roots

theorem mem_clusterAdaptiveInsideEdges_iff (roots : Finset V)
    (rho : ConfigSpace (Sym2 V)) (e : Sym2 V) :
    e ∈ clusterAdaptiveInsideEdges G roots rho ↔
      ∃ x y : V, e = s(x, y) ∧
        ¬ ClusterExploredVertex G rho roots x ∧
        ¬ ClusterExploredVertex G rho roots y := by
  classical
  rw [clusterAdaptiveInsideEdges, clusterUnexploredPairEdges,
    ocd_mem_innerEdgeFinset]
  constructor
  · rintro ⟨edge, rfl⟩
    induction edge using Sym2.ind with
    | _ x y =>
        exact ⟨x.1, y.1, ocd_innerEdge_mk _ x y, x.2, y.2⟩
  · rintro ⟨x, y, rfl, hx, hy⟩
    let x' : ClusterUnexploredVertex G rho roots := ⟨x, hx⟩
    let y' : ClusterUnexploredVertex G rho roots := ⟨y, hy⟩
    exact ⟨s(x', y'), ocd_innerEdge_mk _ x' y'⟩


def clusterAdaptiveProjection (roots : Finset V)
    (rho : ConfigSpace (Sym2 V)) : ConfigSpace (Sym2 V) :=
  projOff (clusterAdaptiveInsideEdges G roots rho) rho

theorem clusterAdaptiveProjection_le (roots : Finset V)
    (rho : ConfigSpace (Sym2 V)) :
    clusterAdaptiveProjection G roots rho ≤ rho := by
  intro e
  unfold clusterAdaptiveProjection projOff
  by_cases he : e ∈ clusterAdaptiveInsideEdges G roots rho <;> simp [he]

theorem clusterAdaptiveProjection_eq_of_not_mem (roots : Finset V)
    (rho : ConfigSpace (Sym2 V)) {e : Sym2 V}
    (he : e ∉ clusterAdaptiveInsideEdges G roots rho) :
    clusterAdaptiveProjection G roots rho e = rho e := by
  unfold clusterAdaptiveProjection projOff
  simp [he]

theorem not_mem_clusterAdaptiveInsideEdges_of_explored_left
    (roots : Finset V) (rho : ConfigSpace (Sym2 V)) {x y : V}
    (hx : ClusterExploredVertex G rho roots x) :
    s(x, y) ∉ clusterAdaptiveInsideEdges G roots rho := by
  intro hmem
  rcases (mem_clusterAdaptiveInsideEdges_iff G roots rho _).1 hmem with
    ⟨u, v, huv, hu, hv⟩
  rcases Sym2.eq_iff.mp huv with ⟨hxu, _⟩ | ⟨hxv, _⟩
  · exact hu (hxu ▸ hx)
  · exact hv (hxv ▸ hx)

theorem clusterAdaptiveProjection_openAdj_of_explored
    (roots : Finset V) (rho : ConfigSpace (Sym2 V)) {x y : V}
    (hx : ClusterExploredVertex G rho roots x)
    (hxy : (openSub G rho).Adj x y) :
    (openSub G (clusterAdaptiveProjection G roots rho)).Adj x y := by
  refine ⟨hxy.1, ?_⟩
  rw [clusterAdaptiveProjection_eq_of_not_mem G roots rho
    (not_mem_clusterAdaptiveInsideEdges_of_explored_left
      G roots rho hx)]
  exact hxy.2

theorem clusterExploredVertex_projection_of_explored
    (roots : Finset V) (rho : ConfigSpace (Sym2 V)) {v : V}
    (hv : ClusterExploredVertex G rho roots v) :
    ClusterExploredVertex G (clusterAdaptiveProjection G roots rho)
      roots v := by
  rcases hv with ⟨r, hr, hreach⟩
  refine ⟨r, hr, ?_⟩
  let source := r
  let Gold := openSub G rho
  let Gnew := openSub G (clusterAdaptiveProjection G roots rho)
  let liftWalk : ∀ {x y : V}, Gold.Walk x y →
      Gold.Reachable source x → Gnew.Walk x y := by
    intro x y path
    induction path with
    | nil => intro _; exact SimpleGraph.Walk.nil
    | @cons x y z hxy path ih =>
        intro hsx
        exact SimpleGraph.Walk.cons
          (clusterAdaptiveProjection_openAdj_of_explored G roots rho
            ⟨r, hr, hsx⟩ hxy)
          (ih (hsx.trans hxy.reachable))
  exact hreach.elim fun path =>
    ⟨liftWalk path (SimpleGraph.Reachable.refl source)⟩

theorem clusterExploredVertex_of_projection (roots : Finset V)
    (rho : ConfigSpace (Sym2 V)) {v : V}
    (hv : ClusterExploredVertex G (clusterAdaptiveProjection G roots rho)
      roots v) :
    ClusterExploredVertex G rho roots v := by
  rcases hv with ⟨r, hr, hreach⟩
  exact ⟨r, hr, hreach.mono (openSub_mono G
    (clusterAdaptiveProjection_le G roots rho))⟩


theorem clusterExploredVertex_projection_iff (roots : Finset V)
    (rho : ConfigSpace (Sym2 V)) (v : V) :
    ClusterExploredVertex G (clusterAdaptiveProjection G roots rho) roots v ↔
      ClusterExploredVertex G rho roots v :=
  ⟨clusterExploredVertex_of_projection G roots rho,
    clusterExploredVertex_projection_of_explored G roots rho⟩


theorem clusterRootReachable_projection_iff (roots : Finset V)
    (rho : ConfigSpace (Sym2 V)) {r : V} (hr : r ∈ roots) (v : V) :
    (openSub G (clusterAdaptiveProjection G roots rho)).Reachable r v ↔
      (openSub G rho).Reachable r v := by
  constructor
  · intro hreach
    exact hreach.mono (openSub_mono G
      (clusterAdaptiveProjection_le G roots rho))
  · intro hreach
    let Gold := openSub G rho
    let Gnew := openSub G (clusterAdaptiveProjection G roots rho)
    let liftWalk : ∀ {x y : V}, Gold.Walk x y →
        Gold.Reachable r x → Gnew.Walk x y := by
      intro x y path
      induction path with
      | nil => intro _; exact SimpleGraph.Walk.nil
      | @cons x y z hxy path ih =>
          intro hrx
          exact SimpleGraph.Walk.cons
            (clusterAdaptiveProjection_openAdj_of_explored G roots rho
              ⟨r, hr, hrx⟩ hxy)
            (ih (hrx.trans hxy.reachable))
    exact hreach.elim fun path =>
      ⟨liftWalk path (SimpleGraph.Reachable.refl r)⟩

theorem clusterAdaptiveInsideEdges_projection (roots : Finset V)
    (rho : ConfigSpace (Sym2 V)) :
    clusterAdaptiveInsideEdges G roots
        (clusterAdaptiveProjection G roots rho) =
      clusterAdaptiveInsideEdges G roots rho := by
  ext e
  rw [mem_clusterAdaptiveInsideEdges_iff,
    mem_clusterAdaptiveInsideEdges_iff]
  constructor
  · rintro ⟨x, y, he, hx, hy⟩
    exact ⟨x, y, he,
      fun h => hx ((clusterExploredVertex_projection_iff G roots rho x).2 h),
      fun h => hy ((clusterExploredVertex_projection_iff G roots rho y).2 h)⟩
  · rintro ⟨x, y, he, hx, hy⟩
    exact ⟨x, y, he,
      fun h => hx ((clusterExploredVertex_projection_iff G roots rho x).1 h),
      fun h => hy ((clusterExploredVertex_projection_iff G roots rho y).1 h)⟩


theorem clusterAdaptiveProjection_idem (roots : Finset V)
    (rho : ConfigSpace (Sym2 V)) :
    clusterAdaptiveProjection G roots
        (clusterAdaptiveProjection G roots rho) =
      clusterAdaptiveProjection G roots rho := by
  change projOff
      (clusterAdaptiveInsideEdges G roots
        (clusterAdaptiveProjection G roots rho))
      (clusterAdaptiveProjection G roots rho) =
    clusterAdaptiveProjection G roots rho
  rw [clusterAdaptiveInsideEdges_projection]
  unfold clusterAdaptiveProjection
  exact projOff_idem _ _



theorem clusterRootReachable_agreesOff_iff (roots : Finset V)
    (psi rho : ConfigSpace (Sym2 V))
    (hagree : AgreesOff (clusterAdaptiveInsideEdges G roots psi) psi rho)
    {r : V} (hr : r ∈ roots) (v : V) :
    (openSub G psi).Reachable r v ↔ (openSub G rho).Reachable r v := by
  let Gpsi := openSub G psi
  let Grho := openSub G rho
  have transfer : ∀ {x y : V}, ClusterExploredVertex G psi roots x →
      (Gpsi.Adj x y ↔ Grho.Adj x y) := by
    intro x y hx
    have hnot : s(x, y) ∉ clusterAdaptiveInsideEdges G roots psi :=
      not_mem_clusterAdaptiveInsideEdges_of_explored_left
        G roots psi hx
    have heq := hagree s(x, y) hnot
    constructor
    · rintro ⟨hadj, hopen⟩
      exact ⟨hadj, heq.symm ▸ hopen⟩
    · rintro ⟨hadj, hopen⟩
      exact ⟨hadj, heq ▸ hopen⟩
  constructor
  · intro hreach
    let liftWalk : ∀ {x y : V}, Gpsi.Walk x y →
        Gpsi.Reachable r x → Grho.Walk x y := by
      intro x y path
      induction path with
      | nil => intro _; exact SimpleGraph.Walk.nil
      | @cons x y z hxy path ih =>
          intro hrx
          exact SimpleGraph.Walk.cons
            ((transfer ⟨r, hr, hrx⟩).1 hxy)
            (ih (hrx.trans hxy.reachable))
    exact hreach.elim fun path =>
      ⟨liftWalk path (SimpleGraph.Reachable.refl r)⟩
  · intro hreach
    let liftWalk : ∀ {x y : V}, Grho.Walk x y →
        Gpsi.Reachable r x → Gpsi.Walk x y := by
      intro x y path
      induction path with
      | nil => intro _; exact SimpleGraph.Walk.nil
      | @cons x y z hxy path ih =>
          intro hrx
          have hxyPsi := (transfer ⟨r, hr, hrx⟩).2 hxy
          exact SimpleGraph.Walk.cons hxyPsi
            (ih (hrx.trans hxyPsi.reachable))
    exact hreach.elim fun path =>
      ⟨liftWalk path (SimpleGraph.Reachable.refl r)⟩

theorem clusterExploredVertex_agreesOff_iff (roots : Finset V)
    (psi rho : ConfigSpace (Sym2 V))
    (hagree : AgreesOff (clusterAdaptiveInsideEdges G roots psi) psi rho)
    (v : V) :
    ClusterExploredVertex G psi roots v ↔
      ClusterExploredVertex G rho roots v := by
  constructor
  · rintro ⟨r, hr, hrv⟩
    exact ⟨r, hr,
      (clusterRootReachable_agreesOff_iff G roots psi rho hagree hr v).1 hrv⟩
  · rintro ⟨r, hr, hrv⟩
    exact ⟨r, hr,
      (clusterRootReachable_agreesOff_iff G roots psi rho hagree hr v).2 hrv⟩

theorem clusterAdaptiveInsideEdges_eq_of_agreesOff (roots : Finset V)
    (psi rho : ConfigSpace (Sym2 V))
    (hagree : AgreesOff (clusterAdaptiveInsideEdges G roots psi) psi rho) :
    clusterAdaptiveInsideEdges G roots rho =
      clusterAdaptiveInsideEdges G roots psi := by
  ext e
  rw [mem_clusterAdaptiveInsideEdges_iff,
    mem_clusterAdaptiveInsideEdges_iff]
  constructor
  · rintro ⟨x, y, he, hx, hy⟩
    exact ⟨x, y, he,
      fun h => hx ((clusterExploredVertex_agreesOff_iff
        G roots psi rho hagree x).1 h),
      fun h => hy ((clusterExploredVertex_agreesOff_iff
        G roots psi rho hagree y).1 h)⟩
  · rintro ⟨x, y, he, hx, hy⟩
    exact ⟨x, y, he,
      fun h => hx ((clusterExploredVertex_agreesOff_iff
        G roots psi rho hagree x).2 h),
      fun h => hy ((clusterExploredVertex_agreesOff_iff
        G roots psi rho hagree y).2 h)⟩



theorem clusterAdaptiveProjection_filter_eq_condFibre (roots : Finset V)
    (psi : ConfigSpace (Sym2 V))
    (hpsi : clusterAdaptiveProjection G roots psi = psi) :
    Finset.univ.filter
        (fun rho => clusterAdaptiveProjection G roots rho = psi) =
      condFibre (clusterAdaptiveInsideEdges G roots psi) psi := by
  ext rho
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_condFibre]
  constructor
  · intro hproj
    have hF : clusterAdaptiveInsideEdges G roots rho =
        clusterAdaptiveInsideEdges G roots psi := by
      rw [← clusterAdaptiveInsideEdges_projection G roots rho, hproj]
    intro e he
    have hval := congrFun hproj e
    have hnotRho : e ∉ clusterAdaptiveInsideEdges G roots rho := by
      rwa [hF]
    rw [← hval]
    exact (clusterAdaptiveProjection_eq_of_not_mem
      G roots rho hnotRho).symm
  · intro hagree
    have hF := clusterAdaptiveInsideEdges_eq_of_agreesOff
      G roots psi rho hagree
    unfold clusterAdaptiveProjection
    rw [hF]
    have hproj := projOff_eq_of_agreesOff hagree
    rw [hproj]
    simpa [clusterAdaptiveProjection] using hpsi

end

end StatMech.FK
