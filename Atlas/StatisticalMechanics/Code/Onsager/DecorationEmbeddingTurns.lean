/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationEmbeddingDisjoint





namespace StatMech.Onsager

def ons_decEdgeMicroDarts (L : ℕ) (d e : ons_Dart L) :
    List (ons_Dart (8 * L)) :=
  let r := ons_decEdgeRouteDirs L d e
  let p₀ := ons_decEmbedVertex L d
  let p₁ := ons_dirStep (8 * L) (r 0) p₀
  let p₂ := ons_dirStep (8 * L) (r 1) p₁
  let p₃ := ons_dirStep (8 * L) (r 2) p₂
  [(p₀, r 0), (p₁, r 1), (p₂, r 2), (p₃, r 3)]

@[simp] theorem ons_decEdgeMicroDarts_length
    (L : ℕ) (d e : ons_Dart L) :
    (ons_decEdgeMicroDarts L d e).length = 4 := by
  simp [ons_decEdgeMicroDarts]

theorem ons_decEdgeMicroDarts_sites
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hde : (ons_decGraph L).Adj d e) :
    (ons_decEdgeMicroDarts L d e).map (fun a => a.1) =
      (ons_decEdgeRoute L d e hde).support.dropLast := by
  rw [ons_decEdgeRoute_support]
  simp [ons_decEdgeMicroDarts, ons_decEdgeRouteVertices]

theorem ons_decEdgeMicroDarts_edges
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hde : (ons_decGraph L).Adj d e) :
    (ons_decEdgeMicroDarts L d e).map (ons_portEdge (8 * L)) =
      (ons_decEdgeRoute L d e hde).edges := by
  letI : Fact (2 < 8 * L) := ⟨by
    have := (Fact.out : 2 < L)
    omega⟩
  simp [ons_decEdgeMicroDarts, ons_portEdge, ons_decEdgeRoute,
    ons_fourDirStepWalk, SimpleGraph.Walk.edges,
    SimpleGraph.Walk.darts]

theorem ons_decEdgeMicroDarts_sum_exponentX_external
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hrev : e = ons_dartRev L d) :
    ((ons_decEdgeMicroDarts L d e).map
      (fun a => ons_dirExponentX a.2)).sum =
        4 * ons_dirExponentX d.2 := by
  subst e
  rcases d with ⟨p, mu⟩
  fin_cases mu <;>
    simp [ons_decEdgeMicroDarts, ons_decEdgeRouteDirs,
      ons_dartRev, ons_dirExponentX]

theorem ons_decEdgeMicroDarts_sum_exponentY_external
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hrev : e = ons_dartRev L d) :
    ((ons_decEdgeMicroDarts L d e).map
      (fun a => ons_dirExponentY a.2)).sum =
        4 * ons_dirExponentY d.2 := by
  subst e
  rcases d with ⟨p, mu⟩
  fin_cases mu <;>
    simp [ons_decEdgeMicroDarts, ons_decEdgeRouteDirs,
      ons_dartRev, ons_dirExponentY]

theorem ons_decEdgeMicroDarts_sum_exponentX_internal
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hint : ons_decInternalAdj d e) :
    ((ons_decEdgeMicroDarts L d e).map
      (fun a => ons_dirExponentX a.2)).sum =
        2 * (ons_dirExponentX e.2 - ons_dirExponentX d.2) := by
  rcases d with ⟨p, mu⟩
  rcases e with ⟨q, nu⟩
  have hpq : p = q := hint.1
  subst q
  fin_cases mu <;> fin_cases nu <;>
    simp [ons_decInternalAdj, ons_decEdgeMicroDarts,
      ons_decEdgeRouteDirs, ons_dartRev, ons_dirStep,
      ons_dirExponentX] at hint ⊢

theorem ons_decEdgeMicroDarts_sum_exponentY_internal
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hint : ons_decInternalAdj d e) :
    ((ons_decEdgeMicroDarts L d e).map
      (fun a => ons_dirExponentY a.2)).sum =
        2 * (ons_dirExponentY e.2 - ons_dirExponentY d.2) := by
  rcases d with ⟨p, mu⟩
  rcases e with ⟨q, nu⟩
  have hpq : p = q := hint.1
  subst q
  fin_cases mu <;> fin_cases nu <;>
    simp [ons_decInternalAdj, ons_decEdgeMicroDarts,
      ons_decEdgeRouteDirs, ons_dartRev, ons_dirStep,
      ons_dirExponentY] at hint ⊢

@[simp] theorem ons_dirExponentX_dartRev
    (L : ℕ) (d : ons_Dart L) :
    ons_dirExponentX (ons_dartRev L d).2 =
      -ons_dirExponentX d.2 := by
  rcases d with ⟨p, mu⟩
  fin_cases mu <;> simp [ons_dartRev, ons_dirExponentX]

@[simp] theorem ons_dirExponentY_dartRev
    (L : ℕ) (d : ons_Dart L) :
    ons_dirExponentY (ons_dartRev L d).2 =
      -ons_dirExponentY d.2 := by
  rcases d with ⟨p, mu⟩
  fin_cases mu <;> simp [ons_dartRev, ons_dirExponentY]

def ons_decExpandedDartList
    (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) : List (ons_Dart (8 * L)) :=
  p.darts.flatMap (fun a => ons_decEdgeMicroDarts L a.fst a.snd)

theorem ons_decExpandedDartList_sum_exponentX
    (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) :
    ((ons_decExpandedDartList L p).map
      (fun a => ons_dirExponentX a.2)).sum =
        2 * (ons_dirExponentX v.2 - ons_dirExponentX u.2) +
          8 * ((ons_decWalkExternalDarts p).map
            (fun a => ons_dirExponentX a.2)).sum := by
  induction p with
  | nil => simp [ons_decExpandedDartList, ons_decWalkExternalDarts]
  | @cons u w v huw p ih =>
      simp only [ons_decExpandedDartList, SimpleGraph.Walk.darts_cons,
        List.flatMap_cons, List.map_append, List.sum_append]
      have ih' :
          ((List.flatMap
            (fun a => ons_decEdgeMicroDarts L a.fst a.snd) p.darts).map
              (fun a => ons_dirExponentX a.2)).sum =
            2 * (ons_dirExponentX v.2 - ons_dirExponentX w.2) +
              8 * ((ons_decWalkExternalDarts p).map
                (fun a => ons_dirExponentX a.2)).sum := by
        simpa only [ons_decExpandedDartList] using ih
      by_cases hrev : w = ons_dartRev L u
      · rw [ons_decEdgeMicroDarts_sum_exponentX_external L u w hrev,
          ons_decWalkExternalDarts_cons_external huw p hrev]
        simp only [List.map_cons, List.sum_cons]
        have hexp : ons_dirExponentX w.2 =
            -ons_dirExponentX u.2 := by
          rw [hrev, ons_dirExponentX_dartRev]
        rw [ih', hexp]
        ring
      · have hint : ons_decInternalAdj u w := by
          change ons_decAdj L u w at huw
          exact huw.resolve_left hrev
        rw [ons_decEdgeMicroDarts_sum_exponentX_internal L u w hint]
        have hext :
            ons_decWalkExternalDarts (SimpleGraph.Walk.cons huw p) =
              ons_decWalkExternalDarts p := by
          simp [ons_decWalkExternalDarts, ons_decDartIsExternal, hrev]
        rw [hext, ih']
        ring

theorem ons_decExpandedDartList_sum_exponentY
    (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) :
    ((ons_decExpandedDartList L p).map
      (fun a => ons_dirExponentY a.2)).sum =
        2 * (ons_dirExponentY v.2 - ons_dirExponentY u.2) +
          8 * ((ons_decWalkExternalDarts p).map
            (fun a => ons_dirExponentY a.2)).sum := by
  induction p with
  | nil => simp [ons_decExpandedDartList, ons_decWalkExternalDarts]
  | @cons u w v huw p ih =>
      simp only [ons_decExpandedDartList, SimpleGraph.Walk.darts_cons,
        List.flatMap_cons, List.map_append, List.sum_append]
      have ih' :
          ((List.flatMap
            (fun a => ons_decEdgeMicroDarts L a.fst a.snd) p.darts).map
              (fun a => ons_dirExponentY a.2)).sum =
            2 * (ons_dirExponentY v.2 - ons_dirExponentY w.2) +
              8 * ((ons_decWalkExternalDarts p).map
                (fun a => ons_dirExponentY a.2)).sum := by
        simpa only [ons_decExpandedDartList] using ih
      by_cases hrev : w = ons_dartRev L u
      · rw [ons_decEdgeMicroDarts_sum_exponentY_external L u w hrev,
          ons_decWalkExternalDarts_cons_external huw p hrev]
        simp only [List.map_cons, List.sum_cons]
        have hexp : ons_dirExponentY w.2 =
            -ons_dirExponentY u.2 := by
          rw [hrev, ons_dirExponentY_dartRev]
        rw [ih', hexp]
        ring
      · have hint : ons_decInternalAdj u w := by
          change ons_decAdj L u w at huw
          exact huw.resolve_left hrev
        rw [ons_decEdgeMicroDarts_sum_exponentY_internal L u w hint]
        have hext :
            ons_decWalkExternalDarts (SimpleGraph.Walk.cons huw p) =
              ons_decWalkExternalDarts p := by
          simp [ons_decWalkExternalDarts, ons_decDartIsExternal, hrev]
        rw [hext, ih']
        ring

theorem ons_decWalkExternalDarts_sum_eq_cycleDartLoop
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) (f : ons_Dart L → ℤ) :
    ((ons_decWalkExternalDarts q).map f).sum =
      ∑ k, f (ons_decCycleDartLoop q k) := by
  let ext := ons_decWalkExternalDarts q
  have hhead : ext.head? = some d :=
    ons_decWalkExternalDarts_head q hq hsnd
  have hext : ext = d :: ext.tail := by
    apply List.eq_cons_of_mem_head?
    simpa [hhead]
  calc
    ((ons_decWalkExternalDarts q).map f).sum =
        f d + (ext.tail.map f).sum := by rw [show ons_decWalkExternalDarts q = ext from rfl, hext]; simp
    _ = f d + (ext.tail.reverse.map f).sum := by
      rw [List.map_reverse, List.sum_reverse]
    _ = ((ons_decCycleDartList q).map f).sum := by
      rw [ons_decCycleDartList_eq]
      rfl
    _ = ((List.ofFn (ons_decCycleDartLoop q)).map f).sum :=
      congrArg (fun l => (l.map f).sum)
        (ons_decCycleDartList_ofFn q).symm
    _ = ∑ k, f (ons_decCycleDartLoop q k) := by
      rw [List.map_ofFn, List.sum_ofFn]
      rfl

@[simp] theorem ons_decExpandedDartList_length
    (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) :
    (ons_decExpandedDartList L p).length = 4 * p.length := by
  induction p with
  | nil => simp [ons_decExpandedDartList]
  | @cons u w v huw p ih =>
      simp only [ons_decExpandedDartList, SimpleGraph.Walk.darts_cons,
        List.flatMap_cons, List.length_append,
        ons_decEdgeMicroDarts_length, SimpleGraph.Walk.length_cons]
      have ih' :
          (List.flatMap (fun a => ons_decEdgeMicroDarts L a.fst a.snd)
            p.darts).length = 4 * p.length := by
        simpa only [ons_decExpandedDartList] using ih
      rw [ih']
      ring

theorem ons_decExpandedDartList_sites
    (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) :
    (ons_decExpandedDartList L p).map (fun a => a.1) =
      (ons_decEmbedWalk L p).support.dropLast := by
  rw [← (ons_decEmbedWalk L p).map_fst_darts]
  induction p with
  | nil => simp [ons_decExpandedDartList, ons_decEmbedWalk]
  | @cons u w v huw p ih =>
      rw [ons_decExpandedDartList, SimpleGraph.Walk.darts_cons,
        List.flatMap_cons, List.map_append,
        ons_decEdgeMicroDarts_sites L u w huw, ons_decEmbedWalk,
        SimpleGraph.Walk.darts_append, List.map_append,
        ← (ons_decEdgeRoute L u w huw).map_fst_darts]
      apply congrArg (fun t =>
        (ons_decEdgeRoute L u w huw).darts.map (fun a => a.fst) ++ t)
      simpa only [ons_decExpandedDartList] using ih

theorem ons_decExpandedDartList_edges
    (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) :
    (ons_decExpandedDartList L p).map (ons_portEdge (8 * L)) =
      (ons_decEmbedWalk L p).edges := by
  induction p with
  | nil => simp [ons_decExpandedDartList, ons_decEmbedWalk]
  | @cons u w v huw p ih =>
      rw [ons_decExpandedDartList, SimpleGraph.Walk.darts_cons,
        List.flatMap_cons, List.map_append,
        ons_decEdgeMicroDarts_edges L u w huw, ons_decEmbedWalk,
        SimpleGraph.Walk.edges_append]
      simpa only [ons_decExpandedDartList] using congrArg
        (fun t => (ons_decEdgeRoute L u w huw).edges ++ t) ih

theorem ons_decEdgeMicroDarts_isChain
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hde : (ons_decGraph L).Adj d e) :
    List.IsChain
      (fun a b : ons_Dart (8 * L) =>
        ons_dirStep (8 * L) a.2 a.1 = b.1)
      (ons_decEdgeMicroDarts L d e) := by
  simp [ons_decEdgeMicroDarts]

theorem ons_decEdgeMicroDarts_last_step
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hde : (ons_decGraph L).Adj d e)
    {a : ons_Dart (8 * L)}
    (ha : a ∈ (ons_decEdgeMicroDarts L d e).getLast?) :
    ons_dirStep (8 * L) a.2 a.1 = ons_decEmbedVertex L e := by
  have haeq :
      (ons_dirStep (8 * L) (ons_decEdgeRouteDirs L d e 2)
        (ons_dirStep (8 * L) (ons_decEdgeRouteDirs L d e 1)
          (ons_dirStep (8 * L) (ons_decEdgeRouteDirs L d e 0)
            (ons_decEmbedVertex L d))),
        ons_decEdgeRouteDirs L d e 3) = a := by
    simpa [ons_decEdgeMicroDarts] using ha
  subst a
  exact ons_decEdgeRoute_endpoint L d e hde

theorem ons_decExpandedDartList_head_site
    (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) {a : ons_Dart (8 * L)}
    (ha : a ∈ (ons_decExpandedDartList L p).head?) :
    a.1 = ons_decEmbedVertex L u := by
  cases p with
  | nil => simp [ons_decExpandedDartList] at ha
  | @cons u w v huw p =>
      have haeq : (ons_decEmbedVertex L u,
          ons_decEdgeRouteDirs L u w 0) = a := by
        simpa [ons_decExpandedDartList,
          ons_decEdgeMicroDarts] using ha
      exact (congrArg (fun z : ons_Dart (8 * L) => z.1) haeq).symm

theorem ons_decExpandedDartList_isChain
    (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) :
    List.IsChain
      (fun a b : ons_Dart (8 * L) =>
        ons_dirStep (8 * L) a.2 a.1 = b.1)
      (ons_decExpandedDartList L p) := by
  induction p with
  | nil => exact .nil
  | @cons u w v huw p ih =>
      rw [ons_decExpandedDartList, SimpleGraph.Walk.darts_cons,
        List.flatMap_cons]
      apply (ons_decEdgeMicroDarts_isChain L u w huw).append ih
      intro a ha b hb
      calc
        ons_dirStep (8 * L) a.2 a.1 = ons_decEmbedVertex L w :=
          ons_decEdgeMicroDarts_last_step L u w huw ha
        _ = b.1 := (ons_decExpandedDartList_head_site L p hb).symm

theorem ons_decExpandedDartList_last_step
    (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) {a : ons_Dart (8 * L)}
    (ha : a ∈ (ons_decExpandedDartList L p).getLast?) :
    ons_dirStep (8 * L) a.2 a.1 = ons_decEmbedVertex L v := by
  induction p with
  | nil => simp [ons_decExpandedDartList] at ha
  | @cons u w v huw p ih =>
      cases p with
      | nil =>
          apply ons_decEdgeMicroDarts_last_step L u w huw
          simpa [ons_decExpandedDartList] using ha
      | @cons w z v hwz p =>
          apply ih
          simpa [ons_decExpandedDartList,
            ons_decEdgeMicroDarts] using ha

def ons_decExpandedRoot
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) : ons_Dart (8 * L) :=
  (ons_decExpandedDartList L q).headD (ons_decEmbedVertex L d, 0)

theorem ons_decExpandedRoot_site
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle) :
    (ons_decExpandedRoot L q).1 = ons_decEmbedVertex L d := by
  have hne : ons_decExpandedDartList L q ≠ [] := by
    rw [List.ne_nil_iff_length_pos, ons_decExpandedDartList_length]
    have hqpos : 0 < q.length :=
      SimpleGraph.Walk.not_nil_iff_lt_length.mp hq.not_nil
    omega
  obtain ⟨a, t, hat⟩ := List.exists_cons_of_ne_nil hne
  have ha : a ∈ (ons_decExpandedDartList L q).head? := by
    rw [hat]
    simp
  have hsite := ons_decExpandedDartList_head_site L q ha
  simpa [ons_decExpandedRoot, hat] using hsite

theorem ons_decExpandedDartList_isChain_closed
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle) :
    List.IsChain
      (fun a b : ons_Dart (8 * L) =>
        ons_dirStep (8 * L) a.2 a.1 = b.1)
      (ons_decExpandedDartList L q ++
        [ons_decExpandedRoot L q]) := by
  apply (ons_decExpandedDartList_isChain L q).append (.singleton _)
  intro a ha b hb
  have hbhead : b = ons_decExpandedRoot L q := by
    have hroot : ons_decExpandedRoot L q = b := by simpa using hb
    exact hroot.symm
  subst b
  calc
    ons_dirStep (8 * L) a.2 a.1 = ons_decEmbedVertex L d :=
      ons_decExpandedDartList_last_step L q ha
    _ = (ons_decExpandedRoot L q).1 :=
      (ons_decExpandedRoot_site L q hq).symm

theorem ons_decExpandedDartList_length_pos
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle) :
    0 < (ons_decExpandedDartList L q).length := by
  rw [ons_decExpandedDartList_length]
  have hqpos : 0 < q.length :=
    SimpleGraph.Walk.not_nil_iff_lt_length.mp hq.not_nil
  omega

def ons_decExpandedGeometricLoop
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) :
    Fin (ons_decExpandedDartList L q).length → ons_Dart (8 * L) :=
  (ons_decExpandedDartList L q).get

theorem ons_decExpandedGeometricLoop_sum_exponentX
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) :
    ∑ k, ons_dirExponentX (ons_decExpandedGeometricLoop L q k).2 =
      8 * ((ons_decWalkExternalDarts q).map
        (fun a => ons_dirExponentX a.2)).sum := by
  let f : ons_Dart (8 * L) → ℤ := fun a => ons_dirExponentX a.2
  calc
    ∑ k, f (ons_decExpandedGeometricLoop L q k) =
        (List.ofFn (fun k => f (ons_decExpandedGeometricLoop L q k))).sum :=
      List.sum_ofFn.symm
    _ = ((List.ofFn (ons_decExpandedGeometricLoop L q)).map f).sum := by
      simp [List.map_ofFn, Function.comp_def]
    _ = ((ons_decExpandedDartList L q).map f).sum := by
      change ((List.ofFn (ons_decExpandedDartList L q).get).map f).sum = _
      rw [List.ofFn_get]
    _ = _ := by
      simpa [f] using ons_decExpandedDartList_sum_exponentX L q

theorem ons_decExpandedGeometricLoop_sum_exponentY
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) :
    ∑ k, ons_dirExponentY (ons_decExpandedGeometricLoop L q k).2 =
      8 * ((ons_decWalkExternalDarts q).map
        (fun a => ons_dirExponentY a.2)).sum := by
  let f : ons_Dart (8 * L) → ℤ := fun a => ons_dirExponentY a.2
  calc
    ∑ k, f (ons_decExpandedGeometricLoop L q k) =
        (List.ofFn (fun k => f (ons_decExpandedGeometricLoop L q k))).sum :=
      List.sum_ofFn.symm
    _ = ((List.ofFn (ons_decExpandedGeometricLoop L q)).map f).sum := by
      simp [List.map_ofFn, Function.comp_def]
    _ = ((ons_decExpandedDartList L q).map f).sum := by
      change ((List.ofFn (ons_decExpandedDartList L q).get).map f).sum = _
      rw [List.ofFn_get]
    _ = _ := by
      simpa [f] using ons_decExpandedDartList_sum_exponentY L q

theorem ons_decExpandedGeometricLoop_edgeSet
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) :
    ons_dartEdgeSet (ons_decExpandedGeometricLoop L q) =
      (ons_decEmbedWalk L q).edges.toFinset := by
  classical
  rw [← ons_decExpandedDartList_edges]
  ext e
  simp [ons_dartEdgeSet, ons_decExpandedGeometricLoop]

theorem ons_decExpandedRoot_eq_zero
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle) :
    letI : NeZero (ons_decExpandedDartList L q).length :=
      ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
    ons_decExpandedRoot L q = ons_decExpandedGeometricLoop L q 0 := by
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  have hne : ons_decExpandedDartList L q ≠ [] :=
    List.ne_nil_iff_length_pos.mpr
      (ons_decExpandedDartList_length_pos L q hq)
  obtain ⟨a, t, hat⟩ := List.exists_cons_of_ne_nil hne
  simp [ons_decExpandedRoot, ons_decExpandedGeometricLoop, hat]

theorem ons_decExpandedGeometricLoop_valid
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle) :
    letI : NeZero (ons_decExpandedDartList L q).length :=
      ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
    ∀ k : Fin (ons_decExpandedDartList L q).length,
      ons_dirStep (8 * L) (ons_decExpandedGeometricLoop L q k).2
          (ons_decExpandedGeometricLoop L q k).1 =
        (ons_decExpandedGeometricLoop L q (k + 1)).1 := by
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  apply ons_isChain_closed_ofFn
    (R := fun a b : ons_Dart (8 * L) =>
      ons_dirStep (8 * L) a.2 a.1 = b.1)
    (ons_decExpandedGeometricLoop L q)
  change List.IsChain _
    (List.ofFn (ons_decExpandedDartList L q).get ++
      [(ons_decExpandedDartList L q).get 0])
  rw [List.ofFn_get]
  have hroot : ons_decExpandedRoot L q =
      (ons_decExpandedDartList L q).get 0 := by
    simpa [ons_decExpandedGeometricLoop] using
      ons_decExpandedRoot_eq_zero L q hq
  rw [← hroot]
  exact ons_decExpandedDartList_isChain_closed L q hq

theorem ons_decExpandedGeometricLoop_site_injective
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle) :
    Function.Injective
      (fun k : Fin (ons_decExpandedDartList L q).length =>
        (ons_decExpandedGeometricLoop L q k).1) := by
  have hemb := ons_decEmbedWalk_isCycle L q hq
  have hdrop : (ons_decEmbedWalk L q).support.dropLast.Nodup := by
    have hrev := ((SimpleGraph.Walk.isCycle_def
      (ons_decEmbedWalk L q).reverse).mp hemb.reverse).2.2
    simpa [SimpleGraph.Walk.support_reverse] using hrev
  have hsites : ((ons_decExpandedDartList L q).map (fun a => a.1)).Nodup := by
    rw [ons_decExpandedDartList_sites]
    exact hdrop
  intro i j hij
  have hinjOn := List.inj_on_of_nodup_map hsites
  have hget : (ons_decExpandedDartList L q).get i =
      (ons_decExpandedDartList L q).get j :=
    hinjOn (List.get_mem _ i) (List.get_mem _ j) (by
      simpa [ons_decExpandedGeometricLoop] using hij)
  exact List.nodup_iff_injective_get.mp
    (hsites.of_map (fun a => a.1)) hget

def ons_decExpandedKWLoop
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle) :
    Fin (ons_decExpandedDartList L q).length → ons_Dart (8 * L) := by
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  exact fun k => ons_decExpandedGeometricLoop L q (-k)

theorem ons_decExpandedKWLoop_edgeSet
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle) :
    ons_dartEdgeSet (ons_decExpandedKWLoop L q hq) =
      (ons_decEmbedWalk L q).edges.toFinset := by
  classical
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  rw [← ons_decExpandedGeometricLoop_edgeSet L q]
  ext e
  simp only [ons_dartEdgeSet, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨-k, by simp [ons_decExpandedKWLoop]⟩
  · rintro ⟨k, rfl⟩
    exact ⟨-k, by simp [ons_decExpandedKWLoop]⟩

theorem ons_decExpandedKWLoop_sum_exponentX
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) :
    ∑ k, ons_dirExponentX (ons_decExpandedKWLoop L q hq k).2 =
      8 * ∑ k, ons_dirExponentX (ons_decCycleDartLoop q k).2 := by
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  calc
    ∑ k, ons_dirExponentX (ons_decExpandedKWLoop L q hq k).2 =
        ∑ k, ons_dirExponentX
          (ons_decExpandedGeometricLoop L q k).2 := by
      change (∑ k, ons_dirExponentX
        (ons_decExpandedGeometricLoop L q (-k)).2) = _
      exact Equiv.sum_comp (Equiv.neg _)
        (fun k => ons_dirExponentX
          (ons_decExpandedGeometricLoop L q k).2)
    _ = 8 * ((ons_decWalkExternalDarts q).map
        (fun a => ons_dirExponentX a.2)).sum :=
      ons_decExpandedGeometricLoop_sum_exponentX L q
    _ = _ := by
      rw [ons_decWalkExternalDarts_sum_eq_cycleDartLoop q hq hsnd]

theorem ons_decExpandedKWLoop_sum_exponentY
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) :
    ∑ k, ons_dirExponentY (ons_decExpandedKWLoop L q hq k).2 =
      8 * ∑ k, ons_dirExponentY (ons_decCycleDartLoop q k).2 := by
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  calc
    ∑ k, ons_dirExponentY (ons_decExpandedKWLoop L q hq k).2 =
        ∑ k, ons_dirExponentY
          (ons_decExpandedGeometricLoop L q k).2 := by
      change (∑ k, ons_dirExponentY
        (ons_decExpandedGeometricLoop L q (-k)).2) = _
      exact Equiv.sum_comp (Equiv.neg _)
        (fun k => ons_dirExponentY
          (ons_decExpandedGeometricLoop L q k).2)
    _ = 8 * ((ons_decWalkExternalDarts q).map
        (fun a => ons_dirExponentY a.2)).sum :=
      ons_decExpandedGeometricLoop_sum_exponentY L q
    _ = _ := by
      rw [ons_decWalkExternalDarts_sum_eq_cycleDartLoop q hq hsnd]

theorem ons_decExpandedKWLoop_valid
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle) :
    letI : NeZero (ons_decExpandedDartList L q).length :=
      ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
    ∀ k : Fin (ons_decExpandedDartList L q).length,
      (ons_decExpandedKWLoop L q hq k).1 =
        ons_dirStep (8 * L) (ons_decExpandedKWLoop L q hq (k + 1)).2
          (ons_decExpandedKWLoop L q hq (k + 1)).1 := by
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  intro k
  have h := ons_decExpandedGeometricLoop_valid L q hq (-(k + 1))
  have hi : -(k + 1) + 1 = -k := by abel
  rw [hi] at h
  simpa [ons_decExpandedKWLoop] using h.symm

theorem ons_decExpandedKWLoop_site_injective
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle) :
    Function.Injective
      (fun k : Fin (ons_decExpandedDartList L q).length =>
        (ons_decExpandedKWLoop L q hq k).1) := by
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  intro i j hij
  have hneg : -i = -j :=
    ons_decExpandedGeometricLoop_site_injective L q hq (by
      simpa [ons_decExpandedKWLoop] using hij)
  exact neg_injective hneg

theorem ons_decExpandedKWLoop_site_mem_embedSupport
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (k : Fin (ons_decExpandedDartList L q).length) :
    (ons_decExpandedKWLoop L q hq k).1 ∈
      (ons_decEmbedWalk L q).support := by
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  have hmem : ons_decExpandedGeometricLoop L q (-k) ∈
      ons_decExpandedDartList L q :=
    List.get_mem _ (-k)
  have hsite : (ons_decExpandedGeometricLoop L q (-k)).1 ∈
      (ons_decExpandedDartList L q).map (fun a => a.1) :=
    List.mem_map.mpr ⟨_, hmem, rfl⟩
  rw [ons_decExpandedDartList_sites] at hsite
  apply List.mem_of_mem_dropLast
  simpa [ons_decExpandedKWLoop] using hsite

theorem ons_decExpandedKWLoop_sites_disjoint
    (L : ℕ) [Fact (2 < L)]
    {d e : ons_Dart L}
    (q : (ons_decGraph L).Walk d d)
    (p : (ons_decGraph L).Walk e e)
    (hq : q.IsCycle) (hp : p.IsCycle)
    (hdisj : Disjoint q.toSubgraph.verts p.toSubgraph.verts) :
    ∀ (i : Fin (ons_decExpandedDartList L q).length)
      (j : Fin (ons_decExpandedDartList L p).length),
      (ons_decExpandedKWLoop L q hq i).1 ≠
        (ons_decExpandedKWLoop L p hp j).1 := by
  have hsupp :=
    ons_decEmbedWalk_support_disjoint_of_toSubgraph L q p hdisj
  intro i j
  intro hij
  apply (List.disjoint_left.mp hsupp)
    (ons_decExpandedKWLoop_site_mem_embedSupport L q hq i)
  rw [hij]
  exact ons_decExpandedKWLoop_site_mem_embedSupport L p hp j

theorem ons_decExpandedKWLoop_nonUturn
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle) :
    letI : NeZero (ons_decExpandedDartList L q).length :=
      ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
    ∀ k : Fin (ons_decExpandedDartList L q).length,
      (ons_decExpandedKWLoop L q hq k).2 ≠
        (ons_decExpandedKWLoop L q hq (k + 1)).2 + 2 := by
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  let v := ons_decExpandedKWLoop L q hq
  have hvalid := ons_decExpandedKWLoop_valid L q hq
  have hinj := ons_decExpandedKWLoop_site_injective L q hq
  have hn : 2 < (ons_decExpandedDartList L q).length := by
    have := ons_decExpandedDartList_length_pos L q hq
    rw [ons_decExpandedDartList_length]
    have hqthree := hq.three_le_length
    omega
  have htwo : (2 : Fin (ons_decExpandedDartList L q).length) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    change 2 % (ons_decExpandedDartList L q).length = 0 at hv
    rw [Nat.mod_eq_of_lt hn] at hv
    omega
  intro k hdir
  have hprev := hvalid (k - 1)
  have heq : (v (k - 1)).1 = (v (k + 1)).1 := by
    calc
      (v (k - 1)).1 = ons_dirStep (8 * L) (v k).2 (v k).1 := by
        simpa [v] using hprev
      _ = ons_dirStep (8 * L) ((v (k + 1)).2 + 2)
          (ons_dirStep (8 * L) (v (k + 1)).2 (v (k + 1)).1) := by
        rw [hdir, hvalid k]
      _ = (v (k + 1)).1 :=
        ons_dirStep_opposite (8 * L) (v (k + 1)).2 (v (k + 1)).1
  have hidx : k - 1 = k + 1 := hinj heq
  have hm : (-1 : Fin (ons_decExpandedDartList L q).length) = 1 := by
    calc
      -1 = -k + (k - 1) := by abel
      _ = -k + (k + 1) := by rw [hidx]
      _ = 1 := by abel
  apply htwo
  calc
    (2 : Fin (ons_decExpandedDartList L q).length) = 1 + 1 := by
      apply Fin.ext
      simp [Fin.val_add, Nat.mod_eq_of_lt hn]
    _ = -1 + 1 := by rw [hm]
    _ = 0 := neg_add_cancel 1



theorem ons_decEmbedWalk_evenHomology_eq
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) :
    ons_evenHomology (8 * L) (ons_decEmbedWalk L q).edges.toFinset =
      ons_evenHomology L (ons_walkOriginalEdges q) := by
  letI : Fact (2 < 8 * L) := ⟨by
    have := (Fact.out : 2 < L)
    omega⟩
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  let loop := ons_decCycleDartLoop q
  have hvalid := ons_decCycleDartLoop_valid q hq hsnd
  obtain ⟨mx, my, hmx, hmy⟩ := ons_loop_winding_exists loop hvalid
  have hmxRefined :
      (∑ k, ons_dirExponentX (ons_decExpandedKWLoop L q hq k).2) =
        ((8 * L : ℕ) : ℤ) * mx := by
    rw [ons_decExpandedKWLoop_sum_exponentX L q hq hsnd]
    change 8 * (∑ k, ons_dirExponentX (loop k).2) = _
    rw [hmx]
    push_cast
    ring
  have hmyRefined :
      (∑ k, ons_dirExponentY (ons_decExpandedKWLoop L q hq k).2) =
        ((8 * L : ℕ) : ℤ) * my := by
    rw [ons_decExpandedKWLoop_sum_exponentY L q hq hsnd]
    change 8 * (∑ k, ons_dirExponentY (loop k).2) = _
    rw [hmy]
    push_cast
    ring
  have hrefined :=
    ons_evenHomology_dartEdgeSet_eq_windingParity
      (ons_decExpandedKWLoop L q hq)
      (ons_decExpandedKWLoop_valid L q hq)
      (ons_decExpandedKWLoop_site_injective L q hq)
      (ons_decExpandedKWLoop_nonUturn L q hq)
      mx my hmxRefined hmyRefined
  have horiginal :=
    ons_evenHomology_dartEdgeSet_eq_windingParity_of_portEdge_injective
      loop hvalid
      (ons_decCycleDartLoop_portEdge_injective q hq hsnd)
      mx my hmx hmy
  rw [ons_decExpandedKWLoop_edgeSet L q hq] at hrefined
  rw [ons_decCycleDartLoop_edgeSet q hq hsnd] at horiginal
  exact hrefined.trans horiginal.symm

theorem ons_decExpanded_turnProduct_eq_neg_one_of_zero_winding
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hx : ∑ k, ons_dirExponentX (ons_decExpandedKWLoop L q hq k).2 = 0)
    (hy : ∑ k, ons_dirExponentY (ons_decExpandedKWLoop L q hq k).2 = 0) :
    letI : NeZero (ons_decExpandedDartList L q).length :=
      ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
    ∏ k, ons_turnW ons_turnRoot
        (ons_decExpandedKWLoop L q hq (k + 1)).2
        (ons_decExpandedKWLoop L q hq k).2 = -1 := by
  letI : Fact (2 < 8 * L) := ⟨by
    have := (Fact.out : 2 < L)
    omega⟩
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  have hroot : ons_turnRoot ≠ 0 := by
    intro h
    have hs := ons_turnRoot_sq
    rw [h] at hs
    have hs' : (0 : ℂ) = Complex.I := by simpa using hs
    exact Complex.I_ne_zero hs'.symm
  apply ons_contractible_turnProduct_eq_neg_one
    ons_turnRoot hroot ons_turnRoot_sq (ons_decExpandedKWLoop L q hq)
    (ons_decExpandedKWLoop_valid L q hq)
    (ons_decExpandedKWLoop_site_injective L q hq)
    (ons_decExpandedKWLoop_nonUturn L q hq) hx hy
  rw [ons_decExpandedDartList_length]
  have := hq.three_le_length
  omega

end StatMech.Onsager
