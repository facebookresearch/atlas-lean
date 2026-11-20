/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarDualBurtonKeane
import Code.FK.PeriodicPlanarSheffieldWholeArcCrosscut












open MeasureTheory Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

namespace PeriodicPlanarDualPair



def primalDualPatternSupport
    (D : PeriodicPlanarDualPair P Pdual)
    (primal : Finset (Sym2 V)) (dual : Finset (Sym2 W)) :
    Finset (Sym2 V) :=
  primal ∪ dual.map D.edgeDual.symm.toEmbedding



def primalDualOpenPattern
    (D : PeriodicPlanarDualPair P Pdual)
    (primal : Finset (Sym2 V)) (dual : Finset (Sym2 W)) :
    ConfigSpace ↑(D.primalDualPatternSupport primal dual) :=
  fun e => decide (e.1 ∈ primal)


theorem setPattern_primalDualOpenPattern_primal
    (D : PeriodicPlanarDualPair P Pdual)
    (primal : Finset (Sym2 V)) (dual : Finset (Sym2 W))
    (omega : ConfigSpace (Sym2 V)) {e : Sym2 V} (he : e ∈ primal) :
    setPattern (D.primalDualPatternSupport primal dual)
        (D.primalDualOpenPattern primal dual) omega e = true := by
  have heSupport : e ∈ D.primalDualPatternSupport primal dual :=
    Finset.mem_union_left _ he
  rw [setPattern_of_mem (D.primalDualOpenPattern primal dual) heSupport]
  simp [primalDualOpenPattern, he]



theorem setPattern_primalDualOpenPattern_dual
    (D : PeriodicPlanarDualPair P Pdual)
    (primal : Finset (Sym2 V)) (dual : Finset (Sym2 W))
    (hcompat : Disjoint primal (dual.map D.edgeDual.symm.toEmbedding))
    (omega : ConfigSpace (Sym2 V)) {e : Sym2 W} (he : e ∈ dual) :
    dualConfigEquiv D.edgeDual
        (setPattern (D.primalDualPatternSupport primal dual)
          (D.primalDualOpenPattern primal dual) omega) e = true := by
  have hePre : D.edgeDual.symm e ∈
      dual.map D.edgeDual.symm.toEmbedding := by
    exact Finset.mem_map.mpr ⟨e, he, rfl⟩
  have heNotPrimal : D.edgeDual.symm e ∉ primal := by
    intro hmem
    exact Finset.disjoint_left.mp hcompat hmem hePre
  have heSupport : D.edgeDual.symm e ∈
      D.primalDualPatternSupport primal dual :=
    Finset.mem_union_right _ hePre
  simp only [dualConfigEquiv_apply]
  rw [setPattern_of_mem (D.primalDualOpenPattern primal dual) heSupport]
  simp [primalDualOpenPattern, heNotPrimal]




theorem exists_primal_dual_open_iff_disjoint
    (D : PeriodicPlanarDualPair P Pdual)
    (primal : Finset (Sym2 V)) (dual : Finset (Sym2 W)) :
    (∃ omega : ConfigSpace (Sym2 V),
      (∀ e ∈ primal, omega e = true) ∧
      (∀ e ∈ dual, dualConfigEquiv D.edgeDual omega e = true)) ↔
      Disjoint primal (dual.map D.edgeDual.symm.toEmbedding) := by
  constructor
  · rintro ⟨omega, hpopen, hdopen⟩
    rw [Finset.disjoint_left]
    intro e hePrimal heDualPre
    obtain ⟨f, hfDual, hfe⟩ := Finset.mem_map.mp heDualPre
    change D.edgeDual.symm f = e at hfe
    have hopen := hpopen e hePrimal
    have hdualOpen := hdopen f hfDual
    have hopenPre : omega (D.edgeDual.symm f) = true := by
      rw [hfe]
      exact hopen
    simp only [dualConfigEquiv_apply, hopenPre, Bool.not_true] at hdualOpen
    exact Bool.false_ne_true hdualOpen
  · intro hcompat
    let omega : ConfigSpace (Sym2 V) := fun _ => false
    let omega' := setPattern (D.primalDualPatternSupport primal dual)
      (D.primalDualOpenPattern primal dual) omega
    refine ⟨omega', ?_, ?_⟩
    · intro e he
      exact D.setPattern_primalDualOpenPattern_primal
        primal dual omega he
    · intro e he
      exact D.setPattern_primalDualOpenPattern_dual
        primal dual hcompat omega he



theorem setPattern_primalDualOpenPattern_of_not_mem
    (D : PeriodicPlanarDualPair P Pdual)
    (primal : Finset (Sym2 V)) (dual : Finset (Sym2 W))
    (omega : ConfigSpace (Sym2 V)) {e : Sym2 V}
    (he : e ∉ D.primalDualPatternSupport primal dual) :
    setPattern (D.primalDualPatternSupport primal dual)
        (D.primalDualOpenPattern primal dual) omega e = omega e := by
  exact setPattern_of_not_mem (D.primalDualOpenPattern primal dual) he omega





theorem setPattern_primalDualOpenPattern_preserves_walks
    (D : PeriodicPlanarDualPair P Pdual)
    (primal : Finset (Sym2 V)) (dual : Finset (Sym2 W))
    (omega : ConfigSpace (Sym2 V))
    {x y : V} {a b : W}
    (p : P.graph.Walk x y) (q : Pdual.graph.Walk a b)
    (hpopen : ∀ {u v : V}, s(u, v) ∈ p.edges →
      omega s(u, v) = true)
    (hqopen : ∀ {u v : W}, s(u, v) ∈ q.edges →
      dualConfigEquiv D.edgeDual omega s(u, v) = true)
    (hpavoid : ∀ {u v : V}, s(u, v) ∈ p.edges →
      s(u, v) ∉ D.primalDualPatternSupport primal dual)
    (hqavoid : ∀ {u v : W}, s(u, v) ∈ q.edges →
      D.edgeDual.symm s(u, v) ∉
        D.primalDualPatternSupport primal dual) :
    (∀ {u v : V}, s(u, v) ∈ p.edges →
      setPattern (D.primalDualPatternSupport primal dual)
        (D.primalDualOpenPattern primal dual) omega s(u, v) = true) ∧
    (∀ {u v : W}, s(u, v) ∈ q.edges →
      dualConfigEquiv D.edgeDual
        (setPattern (D.primalDualPatternSupport primal dual)
          (D.primalDualOpenPattern primal dual) omega) s(u, v) = true) := by
  constructor
  · intro u v huv
    rw [setPattern_of_not_mem (D.primalDualOpenPattern primal dual)
      (hpavoid huv)]
    exact hpopen huv
  · intro u v huv
    simp only [dualConfigEquiv_apply]
    rw [setPattern_of_not_mem (D.primalDualOpenPattern primal dual)
      (hqavoid huv)]
    simpa only [dualConfigEquiv_apply] using hqopen huv

omit [DecidableEq W] [Countable W] in


theorem exists_walk_of_walk_edge_replacements
    {G : SimpleGraph W} {x y : W} (q : G.Walk x y)
    (S : Set W) (good : Sym2 W → Prop)
    (hqS : ∀ w ∈ q.support, w ∈ S)
    (hreplace : ∀ {u v : W}, s(u, v) ∈ q.edges →
      ∃ r : G.Walk u v,
        (∀ {a b : W}, s(a, b) ∈ r.edges → good s(a, b)) ∧
        ∀ w ∈ r.support, w ∈ S) :
    ∃ r : G.Walk x y,
      (∀ {a b : W}, s(a, b) ∈ r.edges → good s(a, b)) ∧
      ∀ w ∈ r.support, w ∈ S := by
  induction q with
  | nil =>
      refine ⟨.nil, ?_, ?_⟩
      · simp
      · intro w hw
        exact hqS w (by simpa using hw)
  | @cons x u y hxu q ih =>
      obtain ⟨step, hstepGood, hstepS⟩ :=
        hreplace (u := x) (v := u) (by simp)
      have hqTailS : ∀ w ∈ q.support, w ∈ S := by
        intro w hw
        exact hqS w (by simp [hw])
      have hqTailReplace : ∀ {a b : W}, s(a, b) ∈ q.edges →
          ∃ r : G.Walk a b,
            (∀ {c d : W}, s(c, d) ∈ r.edges → good s(c, d)) ∧
            ∀ w ∈ r.support, w ∈ S := by
        intro a b hab
        exact hreplace (by simp [hab])
      obtain ⟨tail, htailGood, htailS⟩ := ih hqTailS hqTailReplace
      refine ⟨step.append tail, ?_, ?_⟩
      · intro a b hab
        rw [SimpleGraph.Walk.edges_append] at hab
        rcases List.mem_append.mp hab with hab | hab
        · exact hstepGood hab
        · exact htailGood hab
      · intro w hw
        rw [SimpleGraph.Walk.mem_support_append_iff] at hw
        exact hw.elim (hstepS w) (htailS w)




theorem setPattern_complementaryDual_walk_of_edge_replacements
    (D : PeriodicPlanarDualPair P Pdual)
    (I : Finset (Sym2 V)) (eta : ConfigSpace ↑I)
    (omega : ConfigSpace (Sym2 V))
    {a b : W} (q : Pdual.graph.Walk a b) (S : Set W)
    (hqopen : ∀ {u v : W}, s(u, v) ∈ q.edges →
      dualConfigEquiv D.edgeDual omega s(u, v) = true)
    (hqS : ∀ w ∈ q.support, w ∈ S)
    (hreplace : ∀ {u v : W}, s(u, v) ∈ q.edges →
      D.edgeDual.symm s(u, v) ∈ I →
      ∃ r : Pdual.graph.Walk u v,
        (∀ {c d : W}, s(c, d) ∈ r.edges →
          dualConfigEquiv D.edgeDual (setPattern I eta omega) s(c, d) = true) ∧
        ∀ w ∈ r.support, w ∈ S) :
    ∃ r : Pdual.graph.Walk a b,
      (∀ {u v : W}, s(u, v) ∈ r.edges →
        dualConfigEquiv D.edgeDual (setPattern I eta omega) s(u, v) = true) ∧
      ∀ w ∈ r.support, w ∈ S := by
  apply exists_walk_of_walk_edge_replacements q S
    (fun e => dualConfigEquiv D.edgeDual (setPattern I eta omega) e = true)
    hqS
  intro u v huv
  by_cases hchanged : D.edgeDual.symm s(u, v) ∈ I
  · exact hreplace huv hchanged
  · let step : Pdual.graph.Walk u v := .cons (q.adj_of_mem_edges huv) .nil
    refine ⟨step, ?_, ?_⟩
    · intro c d hcd
      have heq : s(c, d) = s(u, v) := by
        simpa only [step, SimpleGraph.Walk.edges_cons,
          SimpleGraph.Walk.edges_nil, List.mem_singleton] using hcd
      rw [heq]
      simp only [dualConfigEquiv_apply]
      rw [setPattern_of_not_mem eta hchanged]
      simpa only [dualConfigEquiv_apply] using hqopen huv
    · intro w hw
      have hwCases : w = u ∨ w = v := by
        simpa only [step, SimpleGraph.Walk.support_cons,
          SimpleGraph.Walk.support_nil, List.mem_cons, List.mem_singleton,
          List.not_mem_nil, or_false]
          using hw
      have huS : u ∈ S := hqS u (q.fst_mem_support_of_mem_edges huv)
      have hvS : v ∈ S := hqS v (q.snd_mem_support_of_mem_edges huv)
      rcases hwCases with hwu | hwv
      · simpa [hwu] using huS
      · simpa [hwv] using hvS

omit [Countable V] in


theorem measureReal_pos_of_setPattern_preimage
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (I : Finset (Sym2 V)) (eta : ConfigSpace ↑I)
    (hac : mu.map (setPattern I eta) ≪ mu)
    {A B : Set (ConfigSpace (Sym2 V))}
    (hB : MeasurableSet B) (hApos : 0 < mu.real A)
    (hsub : A ⊆ setPattern I eta ⁻¹' B) :
    0 < mu.real B := by
  by_contra hnot
  have hBreal : mu.real B = 0 :=
    le_antisymm (not_lt.mp hnot) measureReal_nonneg
  have hBzero : mu B = 0 :=
    ((ENNReal.toReal_eq_zero_iff (mu B)).mp hBreal).resolve_right
      (measure_ne_top mu _)
  have hmapZero := hac hBzero
  rw [Measure.map_apply (measurable_setPattern I eta) hB] at hmapZero
  have hAzero : mu A = 0 :=
    le_antisymm ((measure_mono hsub).trans_eq hmapZero) bot_le
  unfold Measure.real at hApos
  rw [hAzero] at hApos
  norm_num at hApos



theorem measureReal_pos_of_primalDualOpenPattern_preimage
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (hpattern : ∀ (I : Finset (Sym2 V)) (eta : ConfigSpace ↑I),
      mu.map (setPattern I eta) ≪ mu)
    (primal : Finset (Sym2 V)) (dual : Finset (Sym2 W))
    {A B : Set (ConfigSpace (Sym2 V))}
    (hB : MeasurableSet B) (hApos : 0 < mu.real A)
    (hsub : A ⊆
      setPattern (D.primalDualPatternSupport primal dual)
        (D.primalDualOpenPattern primal dual) ⁻¹' B) :
    0 < mu.real B := by
  exact measureReal_pos_of_setPattern_preimage mu
    (D.primalDualPatternSupport primal dual)
    (D.primalDualOpenPattern primal dual)
    (hpattern _ _) hB hApos hsub

end PeriodicPlanarDualPair

end StatMech.FK.PeriodicPlanar
