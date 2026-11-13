/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FK.PeriodicPlanarPercolationApproximation
import Code.FK.PcNontrivial

open MeasureTheory Set SimpleGraph Filter Topology
open scoped Classical BigOperators

namespace StatMech.FK.PeriodicPlanar

universe u

variable {V : Type u} [DecidableEq V]




def PeriodicGraph.shiftIso (P : PeriodicGraph V) (z : Lattice.Site 2) :
    P.graph ≃g P.graph where
  toEquiv := P.shift z
  map_rel_iff' := fun {x y} => P.shift_adj z x y


noncomputable def PeriodicGraph.vertexDegree (P : PeriodicGraph V) (v : V) : Nat :=
  @SimpleGraph.degree V P.graph v (P.locallyFinite v)

theorem PeriodicGraph.degree_shift (P : PeriodicGraph V) (z : Lattice.Site 2) (v : V) :
    P.vertexDegree (P.shift z v) = P.vertexDegree v := by
  unfold PeriodicGraph.vertexDegree
  rw [← @SimpleGraph.card_neighborSet_eq_degree V P.graph (P.shift z v)
      (P.locallyFinite _),
    ← @SimpleGraph.card_neighborSet_eq_degree V P.graph v (P.locallyFinite _)]
  exact (@Fintype.card_congr _ _ (P.locallyFinite _) (P.locallyFinite _)
    ((P.shiftIso z).mapNeighborSet v)).symm


noncomputable def PeriodicGraph.degreeBound (P : PeriodicGraph V) : Nat :=
  P.fundamentalDomain.sup P.vertexDegree

theorem PeriodicGraph.degree_le_degreeBound (P : PeriodicGraph V) (v : V) :
    P.vertexDegree v ≤ P.degreeBound := by
  obtain ⟨z, u, hu, rfl⟩ := P.covers v
  rw [P.degree_shift]
  exact Finset.le_sup hu




def RootedWalkCode (G : SimpleGraph V) [SimpleGraph.LocallyFinite G]
    (u : V) : Nat → Type u
  | 0 => ULift.{u} PUnit
  | n + 1 => Σ w : G.neighborSet u, RootedWalkCode G w n

noncomputable instance instFintypeRootedWalkCode
    (G : SimpleGraph V) [SimpleGraph.LocallyFinite G] (u : V) (n : Nat) :
    Fintype (RootedWalkCode G u n) := by
  induction n generalizing u with
  | zero => exact Fintype.ofEquiv PUnit Equiv.ulift.symm
  | succ n ih =>
      dsimp only [RootedWalkCode]
      letI (w : G.neighborSet u) : Fintype (RootedWalkCode G w n) := ih w
      infer_instance


def RootedWalkCode.toWalk
    (G : SimpleGraph V) [SimpleGraph.LocallyFinite G] {u : V} :
    {n : Nat} → RootedWalkCode G u n → Σ v, G.Walk u v
  | 0, _ => ⟨u, .nil⟩
  | n + 1, ⟨w, c⟩ =>
      let p := toWalk G c
      ⟨p.1, p.2.cons w.property⟩

@[simp] theorem RootedWalkCode.length_toWalk
    (G : SimpleGraph V) [SimpleGraph.LocallyFinite G]
    {u : V} {n : Nat} (c : RootedWalkCode G u n) :
    (c.toWalk G).2.length = n := by
  induction n generalizing u with
  | zero => cases c; rfl
  | succ n ih =>
      rcases c with ⟨w, c⟩
      simp only [RootedWalkCode.toWalk, Walk.length_cons, ih]


def RootedWalkCode.ofWalk
    (G : SimpleGraph V) [SimpleGraph.LocallyFinite G] {u v : V} :
    (p : G.Walk u v) → RootedWalkCode G u p.length
  | .nil => ULift.up PUnit.unit
  | .cons h p => ⟨⟨_, h⟩, ofWalk G p⟩

@[simp] theorem RootedWalkCode.toWalk_ofWalk_endpoint
    (G : SimpleGraph V) [SimpleGraph.LocallyFinite G]
    {u v : V} (p : G.Walk u v) :
    ((RootedWalkCode.ofWalk G p).toWalk G).1 = v := by
  induction p with
  | nil => rfl
  | cons h p ih => simpa [RootedWalkCode.ofWalk, RootedWalkCode.toWalk] using ih

theorem RootedWalkCode.toWalk_ofWalk
    (G : SimpleGraph V) [SimpleGraph.LocallyFinite G]
    {u v : V} (p : G.Walk u v) :
    (RootedWalkCode.ofWalk G p).toWalk G = ⟨v, p⟩ := by
  induction p with
  | nil => rfl
  | @cons u v w h p ih =>
      simp only [RootedWalkCode.ofWalk]
      change (let pp := (RootedWalkCode.ofWalk G p).toWalk G
        (⟨pp.1, pp.2.cons h⟩ : Sigma (fun x : V => G.Walk u x))) =
          (⟨w, Walk.cons h p⟩ : Sigma (fun x : V => G.Walk u x))
      rw [ih]

theorem RootedWalkCode.toWalk_cast
    (G : SimpleGraph V) [SimpleGraph.LocallyFinite G]
    {u : V} {m n : Nat} (h : m = n) (c : RootedWalkCode G u m) :
    (h ▸ c).toWalk G = c.toWalk G := by
  cases h
  rfl



theorem card_rootedWalkCode_le
    (G : SimpleGraph V) [SimpleGraph.LocallyFinite G]
    {D : Nat} (hD : ∀ v, G.degree v ≤ D) (u : V) (n : Nat) :
    Fintype.card (RootedWalkCode G u n) ≤ D ^ n := by
  induction n generalizing u with
  | zero => simp [RootedWalkCode]
  | succ n ih =>
      change Fintype.card (Σ w : G.neighborSet u, RootedWalkCode G w n) ≤ D ^ (n + 1)
      rw [Fintype.card_sigma]
      calc
        ∑ w : G.neighborSet u, Fintype.card (RootedWalkCode G w n)
            ≤ ∑ _w : G.neighborSet u, D ^ n :=
              Finset.sum_le_sum fun w _ => ih w
        _ = Fintype.card (G.neighborSet u) * D ^ n := by
          rw [Finset.sum_const, Nat.nsmul_eq_mul, Finset.card_univ]
        _ = G.degree u * D ^ n := by
          rw [SimpleGraph.card_neighborSet_eq_degree]
        _ ≤ D * D ^ n := Nat.mul_le_mul_right _ (hD u)
        _ = D ^ (n + 1) := by rw [pow_succ']


noncomputable def rootedReachableFinset
    (G : SimpleGraph V) [SimpleGraph.LocallyFinite G]
    (u : V) (n : Nat) : Finset V :=
  (Finset.univ : Finset (Σ k : Fin n, RootedWalkCode G u k)).image
    (fun kc => (kc.2.toWalk G).1)

theorem endpoint_mem_rootedReachableFinset
    (G : SimpleGraph V) [SimpleGraph.LocallyFinite G]
    {u v : V} (p : G.Walk u v) {n : Nat} (hp : p.length < n) :
    v ∈ rootedReachableFinset G u n := by
  rw [rootedReachableFinset, Finset.mem_image]
  refine ⟨⟨⟨p.length, hp⟩, RootedWalkCode.ofWalk G p⟩, Finset.mem_univ _, ?_⟩
  exact RootedWalkCode.toWalk_ofWalk_endpoint G p


def walkOpenEvent {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | ∀ e ∈ p.edges, omega e = true}

theorem isClopen_walkOpenEvent {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    IsClopen (walkOpenEvent p) := by
  have heq : walkOpenEvent p =
      ⋂ e ∈ (p.edges.toFinset : Set (Sym2 V)),
        {omega : ConfigSpace (Sym2 V) | omega e = true} := by
    ext omega
    simp [walkOpenEvent]
  rw [heq]
  have hsingle : ∀ e : Sym2 V,
      IsClopen {omega : ConfigSpace (Sym2 V) | omega e = true} := by
    intro e
    change IsClopen ((fun omega : ConfigSpace (Sym2 V) => omega e) ⁻¹' {true})
    exact IsClopen.preimage (isClopen_discrete _)
      (StatMech.ConfigSpace.continuous_eval e)
  exact Set.Finite.isClopen_biInter p.edges.toFinset.finite_toSet
    (fun e _ => hsingle e)

theorem isIncreasing_walkOpenEvent {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    IsIncreasing (walkOpenEvent p) := by
  intro omega eta home hopen e he
  have hle := home e
  rw [hopen e he] at hle
  exact le_antisymm le_top hle


def rootedOpenPathEvent
    (G : SimpleGraph V) [SimpleGraph.LocallyFinite G] (u : V) (n : Nat) :
    Set (ConfigSpace (Sym2 V)) :=
  ⋃ (c : RootedWalkCode G u n) (_ : (c.toWalk G).2.IsPath),
    walkOpenEvent (c.toWalk G).2

theorem isClopen_rootedOpenPathEvent
    (G : SimpleGraph V) [SimpleGraph.LocallyFinite G] (u : V) (n : Nat) :
    IsClopen (rootedOpenPathEvent G u n) := by
  rw [rootedOpenPathEvent]
  apply isClopen_iUnion_of_finite
  intro c
  by_cases hc : (c.toWalk G).2.IsPath
  · rw [Set.iUnion_eq_if, if_pos hc]
    exact isClopen_walkOpenEvent _
  · rw [Set.iUnion_eq_if, if_neg hc]
    exact isClopen_empty

theorem isIncreasing_rootedOpenPathEvent
    (G : SimpleGraph V) [SimpleGraph.LocallyFinite G] (u : V) (n : Nat) :
    IsIncreasing (rootedOpenPathEvent G u n) := by
  apply isUpperSet_iUnion₂
  intro c _
  exact isIncreasing_walkOpenEvent _

theorem PeriodicGraph.openSubgraph_le (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) : P.openSubgraph omega ≤ P.graph := by
  intro x y hxy
  exact hxy.1

theorem PeriodicGraph.open_of_mem_walk_edges
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V))
    {u v : V} (p : (P.openSubgraph omega).Walk u v)
    {e : Sym2 V} (he : e ∈ p.edges) : omega e = true := by
  have hedge := p.edges_subset_edgeSet he
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet, P.openSubgraph_adj] at hedge
      exact hedge.2



noncomputable def PeriodicGraph.rootedOpenPathEvent
    (P : PeriodicGraph V) (n : Nat) : Set (ConfigSpace (Sym2 V)) := by
  letI : SimpleGraph.LocallyFinite P.graph := P.locallyFinite
  exact StatMech.FK.PeriodicPlanar.rootedOpenPathEvent P.graph P.root n



theorem PeriodicGraph.percolationEvent_subset_rootedOpenPathEvent
    (P : PeriodicGraph V) (n : Nat) :
    P.percolationEvent ⊆ P.rootedOpenPathEvent n := by
  letI : SimpleGraph.LocallyFinite P.graph := P.locallyFinite
  rw [PeriodicGraph.rootedOpenPathEvent]
  intro omega hinf
  let B := rootedReachableFinset P.graph P.root n
  obtain ⟨w, hwcluster, hwoutside⟩ :=
    (hinf.diff B.finite_toSet).nonempty
  have hreach : (P.openSubgraph omega).Reachable P.root w := hwcluster
  obtain ⟨q, hqpath⟩ := hreach.exists_isPath
  let p := q.mapLe (P.openSubgraph_le omega)
  have hpoutside : w ∉ B := hwoutside
  have hpLength : p.length = q.length := by
    exact Walk.length_map (SimpleGraph.Hom.ofLE (P.openSubgraph_le omega)) q
  have hlen : n ≤ q.length := by
    by_contra hnot
    have hlt : p.length < n := by
      rw [hpLength]
      exact Nat.lt_of_not_ge hnot
    exact hpoutside (endpoint_mem_rootedReachableFinset P.graph p hlt)
  let qt := q.take n
  let pt := qt.mapLe (P.openSubgraph_le omega)
  have hptLength : pt.length = qt.length := by
    exact Walk.length_map (SimpleGraph.Hom.ofLE (P.openSubgraph_le omega)) qt
  have hptlen : pt.length = n := by
    rw [hptLength]
    exact Walk.take_length q n |>.trans (Nat.min_eq_left hlen)
  let c0 := RootedWalkCode.ofWalk P.graph pt
  let c : RootedWalkCode P.graph P.root n := hptlen ▸ c0
  rw [StatMech.FK.PeriodicPlanar.rootedOpenPathEvent, Set.mem_iUnion₂]
  refine ⟨c, ?_, ?_⟩
  · dsimp only [c, c0]
    rw [RootedWalkCode.toWalk_cast]
    rw [RootedWalkCode.toWalk_ofWalk]
    exact (hqpath.take n).mapLe (P.openSubgraph_le omega)
  · dsimp only [c, c0]
    rw [RootedWalkCode.toWalk_cast]
    rw [RootedWalkCode.toWalk_ofWalk]
    intro e he
    rw [Walk.edges_mapLe_eq_edges] at he
    exact P.open_of_mem_walk_edges omega qt he



section Countable

variable [Countable V]



theorem PeriodicGraph.wiredBufferedMeasure_real_eq
    (P : PeriodicGraph V) (m : Nat) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace (Sym2 V))) (hA : MeasurableSet A) :
    (P.wiredBufferedMeasure m hp hp1 hq : Measure (ConfigSpace (Sym2 V))).real A =
      ∑ omega : ConfigSpace (Sym2 (P.BufferedVertex m)),
        (P.extendEdge (P.bufferedRadius m) ⁻¹' A).indicator (fun _ => (1 : Real)) omega *
          wiredFkProb (P.bufferedGraph m) (P.bufferedBoundary m) p q omega := by
  classical
  have hmap : (P.wiredBufferedMeasure m hp hp1 hq : Measure _).real A =
      ((P.wiredBufferedPMF m hp hp1 hq).toMeasure
        (P.extendEdge (P.bufferedRadius m) ⁻¹' A)).toReal := by
    unfold PeriodicGraph.wiredBufferedMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (P.measurable_extendEdge (P.bufferedRadius m)) hA]
  rw [hmap, PMF.toMeasure_apply_fintype, ENNReal.toReal_sum (fun a _ => ?_)]
  · apply Finset.sum_congr rfl
    intro omega _
    by_cases homega : omega ∈ P.extendEdge (P.bufferedRadius m) ⁻¹' A
    · rw [Set.indicator_of_mem homega, Set.indicator_of_mem homega,
        PeriodicGraph.wiredBufferedPMF, wiredFkPMF, PMF.ofFintype_apply,
        ENNReal.toReal_ofReal
          (wiredFkProb_nonneg (P.bufferedGraph m) (P.bufferedBoundary m)
            hp hp1 hq omega), one_mul]
    · rw [Set.indicator_of_notMem homega, Set.indicator_of_notMem homega]
      simp
  · by_cases ha : a ∈ P.extendEdge (P.bufferedRadius m) ⁻¹' A
    · rw [Set.indicator_of_mem ha, PeriodicGraph.wiredBufferedPMF,
        wiredFkPMF, PMF.ofFintype_apply]
      exact ENNReal.ofReal_ne_top
    · rw [Set.indicator_of_notMem ha]
      simp

theorem PeriodicGraph.range_of_extendEdge_true
    (P : PeriodicGraph V) (r : Nat)
    (omega : ConfigSpace (Sym2 (P.OrbitVertex r)))
    (e : Sym2 V) (h : P.extendEdge r omega e = true) :
    e ∈ Set.range (P.edgeIncl r) := by
  by_contra hc
  unfold PeriodicGraph.extendEdge at h
  rw [dif_neg hc] at h
  exact Bool.false_ne_true h

theorem PeriodicGraph.orbitEdge_mem_of_edgeIncl_mem
    (P : PeriodicGraph V) (r : Nat)
    (be : Sym2 (P.OrbitVertex r))
    (he : P.edgeIncl r be ∈ P.graph.edgeSet) :
    be ∈ (P.orbitGraph r).edgeFinset := by
  induction be using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        PeriodicGraph.orbitGraph, SimpleGraph.comap_adj]
      simpa [PeriodicGraph.edgeIncl, Sym2.map_mk,
        SimpleGraph.mem_edgeSet] using he



theorem PeriodicGraph.exists_bufferedPathEdges
    (P : PeriodicGraph V) (m : Nat) {u v : V}
    (p : P.graph.Walk u v) (hp : p.IsPath)
    (hrange : ∀ e ∈ p.edges,
      e ∈ Set.range (P.edgeIncl (P.bufferedRadius m))) :
    ∃ F : Finset (Sym2 (P.BufferedVertex m)),
      F ⊆ (P.bufferedGraph m).edgeFinset ∧
      F.card = p.length ∧
      (P.extendEdge (P.bufferedRadius m) ⁻¹' walkOpenEvent p ⊆
        {omega | ∀ be ∈ F, omega be = true}) := by
  classical
  let E := p.edges.toFinset
  have hEmem : ∀ e : E, (e : Sym2 V) ∈ p.edges := by
    intro e
    apply List.mem_toFinset.mp
    exact e.2
  let bef : E → Sym2 (P.BufferedVertex m) :=
    fun e => (hrange e.1 (hEmem e)).choose
  have hbef : ∀ e : E,
      P.edgeIncl (P.bufferedRadius m) (bef e) = e :=
    fun e => (hrange e.1 (hEmem e)).choose_spec
  refine ⟨Finset.univ.image bef, ?_, ?_, ?_⟩
  · intro be hbe
    rw [Finset.mem_image] at hbe
    obtain ⟨e, _, rfl⟩ := hbe
    apply P.orbitEdge_mem_of_edgeIncl_mem
    rw [hbef]
    exact p.edges_subset_edgeSet (hEmem e)
  · rw [Finset.card_image_of_injective]
    · rw [Finset.card_univ, Fintype.card_coe]
      dsimp only [E]
      rw [List.toFinset_card_of_nodup hp.isTrail.edges_nodup, Walk.length_edges]
    · intro a b hab
      apply Subtype.ext
      have := congrArg (P.edgeIncl (P.bufferedRadius m)) hab
      simpa only [hbef] using this
  · intro omega homega be hbe
    rw [Finset.mem_image] at hbe
    obtain ⟨e, _, rfl⟩ := hbe
    have hopen : P.extendEdge (P.bufferedRadius m) omega e = true :=
      homega e (hEmem e)
    rw [← hbef e, P.extendEdge_edgeIncl] at hopen
    exact hopen



theorem PeriodicGraph.bernoulli_buffered_walkOpenEvent_le
    (P : PeriodicGraph V) (m : Nat) {u v : V}
    (path : P.graph.Walk u v) (hpath : path.IsPath)
    {p : Real} (hp : 0 < p) (hp1 : p < 1) :
    ∑ omega : ConfigSpace (Sym2 (P.BufferedVertex m)),
      (P.extendEdge (P.bufferedRadius m) ⁻¹' walkOpenEvent path).indicator
          (fun _ => (1 : Real)) omega *
        fkProb (P.bufferedGraph m) p 1 omega ≤ p ^ path.length := by
  classical
  by_cases hempty :
      (P.extendEdge (P.bufferedRadius m) ⁻¹' walkOpenEvent path) = ∅
  · rw [hempty]
    simp only [Set.indicator_empty, zero_mul, Finset.sum_const_zero]
    positivity
  · rw [← Set.not_nonempty_iff_eq_empty, not_not] at hempty
    obtain ⟨omega0, homega0⟩ := hempty
    have hrange : ∀ e ∈ path.edges,
        e ∈ Set.range (P.edgeIncl (P.bufferedRadius m)) := by
      intro e he
      exact P.range_of_extendEdge_true _ omega0 e (homega0 e he)
    obtain ⟨F, hFedge, hFcard, hFcont⟩ :=
      P.exists_bufferedPathEdges m path hpath hrange
    calc
      ∑ omega : ConfigSpace (Sym2 (P.BufferedVertex m)),
          (P.extendEdge (P.bufferedRadius m) ⁻¹' walkOpenEvent path).indicator
              (fun _ => (1 : Real)) omega *
            fkProb (P.bufferedGraph m) p 1 omega
          ≤ ∑ omega : ConfigSpace (Sym2 (P.BufferedVertex m)),
              (if ∀ e ∈ F, omega e = true then (1 : Real) else 0) *
                fkProb (P.bufferedGraph m) p 1 omega := by
            apply Finset.sum_le_sum
            intro omega _
            apply mul_le_mul_of_nonneg_right _
              (fkProb_nonneg (P.bufferedGraph m) hp hp1 one_pos omega)
            by_cases homega :
                omega ∈ P.extendEdge (P.bufferedRadius m) ⁻¹' walkOpenEvent path
            · rw [Set.indicator_of_mem homega]
              have hforced := hFcont homega
              change ∀ e ∈ F, omega e = true at hforced
              rw [if_pos hforced]
            · rw [Set.indicator_of_notMem homega]
              split <;> positivity
      _ = p ^ F.card := fkProbOne_cylinder (P.bufferedGraph m) hp hp1 F hFedge
      _ = p ^ path.length := by rw [hFcard]



theorem PeriodicGraph.wiredBufferedMeasure_rootedOpenPathEvent_le
    (P : PeriodicGraph V) (m n : Nat) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    (P.wiredBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.rootedOpenPathEvent n) ≤
      ((P.degreeBound : Real) * p) ^ n := by
  classical
  letI : SimpleGraph.LocallyFinite P.graph := P.locallyFinite
  let A := StatMech.FK.PeriodicPlanar.rootedOpenPathEvent P.graph P.root n
  have hAeq : P.rootedOpenPathEvent n = A := by
    rfl
  have hAmeas : MeasurableSet A :=
    IsClopen.measurableSet_configSpace
      (isClopen_rootedOpenPathEvent P.graph P.root n)
  rw [hAeq, P.wiredBufferedMeasure_real_eq m hp hp1
    (zero_lt_one.trans_le hq) A hAmeas]
  have hinc : IsIncreasing
      (P.extendEdge (P.bufferedRadius m) ⁻¹' A) := by
    intro omega eta home hmem
    exact isIncreasing_rootedOpenPathEvent P.graph P.root n
      (P.monotone_extendEdge (P.bufferedRadius m) home) hmem
  have hHolley :
      (∑ omega : ConfigSpace (Sym2 (P.BufferedVertex m)),
          (P.extendEdge (P.bufferedRadius m) ⁻¹' A).indicator
              (fun _ => (1 : Real)) omega *
            wiredFkProb (P.bufferedGraph m) (P.bufferedBoundary m) p q omega) ≤
        ∑ omega : ConfigSpace (Sym2 (P.BufferedVertex m)),
          (P.extendEdge (P.bufferedRadius m) ⁻¹' A).indicator
              (fun _ => (1 : Real)) omega *
            fkProb (P.bufferedGraph m) p 1 omega :=
    wiredFkProb_le_fkProbOne_increasing (P.bufferedGraph m)
      (P.bufferedBoundary m) hp hp1 hq hinc
  refine hHolley.trans ?_
  let S : Finset (RootedWalkCode P.graph P.root n) :=
    Finset.univ.filter (fun c => (c.toWalk P.graph).2.IsPath)
  have hsplit : ∀ omega : ConfigSpace (Sym2 (P.BufferedVertex m)),
      (P.extendEdge (P.bufferedRadius m) ⁻¹' A).indicator
          (fun _ => (1 : Real)) omega ≤
        ∑ c ∈ S,
          (P.extendEdge (P.bufferedRadius m) ⁻¹'
            walkOpenEvent (c.toWalk P.graph).2).indicator
              (fun _ => (1 : Real)) omega := by
    intro omega
    by_cases homega : omega ∈ P.extendEdge (P.bufferedRadius m) ⁻¹' A
    · rw [Set.indicator_of_mem homega]
      change P.extendEdge (P.bufferedRadius m) omega ∈ A at homega
      dsimp only [A] at homega
      rw [StatMech.FK.PeriodicPlanar.rootedOpenPathEvent,
        Set.mem_iUnion₂] at homega
      obtain ⟨c, hcpath, hcopen⟩ := homega
      have hcS : c ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcpath⟩
      have hterm : omega ∈ P.extendEdge (P.bufferedRadius m) ⁻¹'
          walkOpenEvent (c.toWalk P.graph).2 := hcopen
      have hle := Finset.single_le_sum
        (f := fun c =>
          (P.extendEdge (P.bufferedRadius m) ⁻¹'
            walkOpenEvent (c.toWalk P.graph).2).indicator
              (fun _ => (1 : Real)) omega)
        (fun c _ => Set.indicator_nonneg (fun _ _ => zero_le_one) omega) hcS
      simpa only [Set.indicator_of_mem hterm] using hle
    · rw [Set.indicator_of_notMem homega]
      exact Finset.sum_nonneg fun c _ =>
        Set.indicator_nonneg (fun _ _ => zero_le_one) omega
  calc
    ∑ omega : ConfigSpace (Sym2 (P.BufferedVertex m)),
        (P.extendEdge (P.bufferedRadius m) ⁻¹' A).indicator
            (fun _ => (1 : Real)) omega *
          fkProb (P.bufferedGraph m) p 1 omega
        ≤ ∑ omega : ConfigSpace (Sym2 (P.BufferedVertex m)),
            (∑ c ∈ S,
              (P.extendEdge (P.bufferedRadius m) ⁻¹'
                walkOpenEvent (c.toWalk P.graph).2).indicator
                  (fun _ => (1 : Real)) omega) *
              fkProb (P.bufferedGraph m) p 1 omega := by
          apply Finset.sum_le_sum
          intro omega _
          exact mul_le_mul_of_nonneg_right (hsplit omega)
            (fkProb_nonneg (P.bufferedGraph m) hp hp1 one_pos omega)
    _ = ∑ c ∈ S, ∑ omega : ConfigSpace (Sym2 (P.BufferedVertex m)),
          (P.extendEdge (P.bufferedRadius m) ⁻¹'
            walkOpenEvent (c.toWalk P.graph).2).indicator
              (fun _ => (1 : Real)) omega *
            fkProb (P.bufferedGraph m) p 1 omega := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro omega _
          rw [Finset.sum_mul]
    _ ≤ ∑ _c ∈ S, p ^ n := by
          apply Finset.sum_le_sum
          intro c hc
          have hcpath : (c.toWalk P.graph).2.IsPath :=
            (Finset.mem_filter.mp hc).2
          simpa only [RootedWalkCode.length_toWalk] using
            P.bernoulli_buffered_walkOpenEvent_le m
              (c.toWalk P.graph).2 hcpath hp hp1
    _ = (S.card : Real) * p ^ n := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((P.degreeBound ^ n : Nat) : Real) * p ^ n := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hp.le n)
          exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _) |>.trans
            (card_rootedWalkCode_le P.graph
              (fun v => P.degree_le_degreeBound v) P.root n))
    _ = ((P.degreeBound : Real) * p) ^ n := by
          push_cast
          rw [mul_pow]

theorem PeriodicGraph.isClopen_rootedOpenPathEvent
    (P : PeriodicGraph V) (n : Nat) :
    IsClopen (P.rootedOpenPathEvent n) := by
  letI : SimpleGraph.LocallyFinite P.graph := P.locallyFinite
  exact StatMech.FK.PeriodicPlanar.isClopen_rootedOpenPathEvent
    P.graph P.root n


theorem PeriodicGraph.wiredPercolationProbability_le_pow_degreeBound
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) (n : Nat) :
    P.wiredPercolationProbability p q ≤
      ((P.degreeBound : Real) * p) ^ n := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  rw [PeriodicGraph.wiredPercolationProbability, dif_pos ⟨⟨hp, hp1⟩, hq0⟩]
  obtain ⟨phi, _hphi, hlimit⟩ :=
    P.wiredBufferedInfiniteVolume_isLimit hp hp1 hq0
  let nu := (P.wiredBufferedInfiniteVolume hp hp1 hq0 :
    ProbabilityMeasure (ConfigSpace (Sym2 V)))
  have hmono : (nu : Measure (ConfigSpace (Sym2 V))).real P.percolationEvent ≤
      (nu : Measure (ConfigSpace (Sym2 V))).real (P.rootedOpenPathEvent n) := by
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (P.percolationEvent_subset_rootedOpenPathEvent n))
  have hbound : (nu : Measure (ConfigSpace (Sym2 V))).real
      (P.rootedOpenPathEvent n) ≤ ((P.degreeBound : Real) * p) ^ n := by
    apply le_of_tendsto
      (hlimit.tendsto_real_of_isClopen (P.isClopen_rootedOpenPathEvent n))
    exact Filter.Eventually.of_forall fun k =>
      P.wiredBufferedMeasure_rootedOpenPathEvent_le (phi k) n hp hp1 hq
  exact hmono.trans hbound



theorem PeriodicGraph.wiredPercolationProbability_eq_zero_of_degreeBound_mul_lt_one
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (hsmall : (P.degreeBound : Real) * p < 1) :
    P.wiredPercolationProbability p q = 0 := by
  have hbase : 0 ≤ (P.degreeBound : Real) * p := mul_nonneg (Nat.cast_nonneg _) hp.le
  have htend : Tendsto (fun n : Nat => ((P.degreeBound : Real) * p) ^ n)
      atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase hsmall
  have hle : P.wiredPercolationProbability p q ≤ 0 :=
    ge_of_tendsto htend (Filter.Eventually.of_forall fun n =>
      P.wiredPercolationProbability_le_pow_degreeBound hp hp1 hq n)
  exact le_antisymm hle (P.wiredPercolationProbability_nonneg p q)



theorem PeriodicGraph.criticalPoint_pos
    (P : PeriodicGraph V) {q : Real} (hq : 1 ≤ q) :
    0 < P.criticalPoint q := by
  let D : Real := P.degreeBound
  let p : Real := 1 / (2 * (D + 1))
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hden : 0 < 2 * (D + 1) := by positivity
  have hp : 0 < p := by dsimp only [p]; positivity
  have hp1 : p < 1 := by
    dsimp only [p]
    rw [div_lt_one hden]
    linarith
  have hsmall : D * p < 1 := by
    dsimp only [p]
    rw [mul_one_div, div_lt_one hden]
    linarith
  have hzero : P.wiredPercolationProbability p q = 0 :=
    P.wiredPercolationProbability_eq_zero_of_degreeBound_mul_lt_one
      hp hp1 hq (by simpa only [D] using hsmall)
  have hmem : p ∈ P.subcriticalSet q := ⟨⟨hp, hp1⟩, hzero⟩
  have hle : p ≤ P.criticalPoint q :=
    le_csSup (P.subcriticalSet_bddAbove q) hmem
  exact hp.trans_le hle



theorem PeriodicGraph.criticalPoints_mem_Ioo_of_bidirectionalCoverage_qge_one
    {W : Type*} [DecidableEq W] [Countable W]
    (P : PeriodicGraph V) (Pdual : PeriodicGraph W) {q : Real}
    (hq : 1 ≤ q)
    (hcoverage : DualSubcriticalCoverage
      (fun r => Pdual.wiredPercolates r q) (P.criticalPoint q) q)
    (hcoverageDual : DualSubcriticalCoverage
      (fun r => P.wiredPercolates r q) (Pdual.criticalPoint q) q) :
    P.criticalPoint q ∈ Ioo (0 : Real) 1 ∧
      Pdual.criticalPoint q ∈ Ioo (0 : Real) 1 := by
  exact P.criticalPoints_mem_Ioo_of_bidirectionalCoverage Pdual
    (zero_lt_one.trans_le hq) (P.criticalPoint_pos hq)
      (Pdual.criticalPoint_pos hq)
      (P.wiredPercolationProbability_monotoneOn hq)
      (Pdual.wiredPercolationProbability_monotoneOn hq)
      hcoverage hcoverageDual



theorem PeriodicGraph.dualCritical_relation_of_bidirectionalCoverage_noCoexistence
    {W : Type*} [DecidableEq W] [Countable W]
    (P : PeriodicGraph V) (Pdual : PeriodicGraph W) {q : Real}
    (hq : 1 ≤ q)
    (hcoverage : DualSubcriticalCoverage
      (fun r => Pdual.wiredPercolates r q) (P.criticalPoint q) q)
    (hcoverageDual : DualSubcriticalCoverage
      (fun r => P.wiredPercolates r q) (Pdual.criticalPoint q) q)
    (hnoCoexistence : DualNoCoexistence
      (fun r => P.wiredPercolates r q)
      (fun r => Pdual.wiredPercolates r q) q) :
    BeffaraDC.dualParam (P.criticalPoint q) q = Pdual.criticalPoint q ∧
      (P.criticalPoint q / (1 - P.criticalPoint q)) *
        (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
  obtain ⟨hpc, hpcDual⟩ :=
    P.criticalPoints_mem_Ioo_of_bidirectionalCoverage_qge_one
      Pdual hq hcoverage hcoverageDual
  exact P.dualCritical_relation_of_noCoexistence Pdual
    hpc hpcDual hq hcoverage hnoCoexistence

end Countable

end StatMech.FK.PeriodicPlanar
