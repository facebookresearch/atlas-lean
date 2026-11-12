/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationWalkExtract










namespace StatMech.Onsager

open BigOperators



theorem ons_isChain_closed_ofFn
    {alpha : Type*} {R : alpha → alpha → Prop}
    {n : ℕ} [NeZero n] (f : Fin n → alpha)
    (hchain : List.IsChain R (List.ofFn f ++ [f 0])) :
    ∀ k : Fin n, R (f k) (f (k + 1)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  intro k
  by_cases hk : k = Fin.last m
  · subst k
    have hclose := (List.isChain_append.mp hchain).2.2
    have hrel := hclose
      ((List.ofFn f).getLast (by simp))
        (List.getLast_mem_getLast? (by simp))
      (f 0) (by simp)
    rw [List.getLast_ofFn] at hrel
    simpa using hrel
  · have hklt : k < Fin.last m :=
      lt_of_le_of_ne (Fin.le_last k) hk
    have hi : k.val + 1 < m + 1 := by
      simpa [Fin.lt_iff_val_lt_val] using hklt
    have hlinear : List.IsChain R (List.ofFn f) :=
      hchain.left_of_append
    have hrel := (List.isChain_ofFn.mp hlinear) k.val hi
    have hnext : k + 1 = ⟨k.val + 1, hi⟩ := by
      apply Fin.ext
      exact Fin.val_add_one_of_lt hklt
    rw [hnext]
    exact hrel

theorem ons_decDartIsExternal_symm {L : ℕ}
    (a : (ons_decGraph L).Dart) :
    ons_decDartIsExternal a.symm = ons_decDartIsExternal a := by
  unfold ons_decDartIsExternal
  apply Bool.decide_congr
  change a.fst = ons_dartRev L a.snd ↔
    a.snd = ons_dartRev L a.fst
  constructor <;> intro h
  · rw [h, ons_dartRev_involutive]
  · rw [h, ons_dartRev_involutive]



theorem ons_decWalkExternalDarts_head_site
    {L : ℕ} {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) {d : ons_Dart L}
    (hd : d ∈ (ons_decWalkExternalDarts p).head?) :
    d.1 = u.1 := by
  induction p with
  | nil => simp [ons_decWalkExternalDarts] at hd
  | @cons u w v h p ih =>
      by_cases hrev : w = ons_dartRev L u
      · rw [ons_decWalkExternalDarts_cons_external h p hrev] at hd
        have hud : u = d := by simpa using hd
        exact congrArg Prod.fst hud.symm
      · have hext : ¬ ons_decDartIsExternal
            (⟨(u, w), h⟩ : (ons_decGraph L).Dart) := by
          simp [ons_decDartIsExternal, hrev]
        have hd' : d ∈ (ons_decWalkExternalDarts p).head? := by
          simpa [ons_decWalkExternalDarts, hext] using hd
        have hsite : u.1 = w.1 := by
          change ons_decAdj L u w at h
          rcases h with h | h
          · exact (hrev h).elim
          · exact h.1
        exact (ih hd').trans hsite.symm



theorem ons_decWalkExternalDarts_isChain
    {L : ℕ} {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) :
    List.IsChain
      (fun d e : ons_Dart L =>
        ons_dirStep L d.2 d.1 = e.1)
      (ons_decWalkExternalDarts p) := by
  induction p with
  | nil => exact .nil
  | @cons u w v h p ih =>
      by_cases hrev : w = ons_dartRev L u
      · rw [ons_decWalkExternalDarts_cons_external h p hrev]
        apply ih.cons
        intro e he
        have heSite := ons_decWalkExternalDarts_head_site p he
        calc
          ons_dirStep L u.2 u.1 = w.1 := by rw [hrev]; rfl
          _ = e.1 := heSite.symm
      · have hext : ¬ ons_decDartIsExternal
            (⟨(u, w), h⟩ : (ons_decGraph L).Dart) := by
          simp [ons_decDartIsExternal, hrev]
        simpa [ons_decWalkExternalDarts, hext] using ih



theorem ons_decWalkExternalDarts_reverse
    {L : ℕ} {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) :
    ons_decWalkExternalDarts p.reverse =
      (ons_decWalkExternalDarts p).reverse.map (ons_dartRev L) := by
  rw [ons_decWalkExternalDarts, SimpleGraph.Walk.darts_reverse,
    List.filter_reverse, List.map_reverse, ons_decWalkExternalDarts,
    List.map_reverse]
  induction p.darts with
  | nil => rfl
  | cons a l ih =>
      simp only [List.map_cons, List.filter_cons]
      rw [ons_decDartIsExternal_symm]
      split
      · rename_i ha
        have haext : a.snd = ons_dartRev L a.fst := by
          simpa [ons_decDartIsExternal] using ha
        simp [ih, haext]
      · simp [ih]



theorem ons_decWalkExternalDarts_getLast_site
    {L : ℕ} {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) {d : ons_Dart L}
    (hd : d ∈ (ons_decWalkExternalDarts p).getLast?) :
    ons_dirStep L d.2 d.1 = v.1 := by
  have hdrev : ons_dartRev L d ∈
      ((ons_decWalkExternalDarts p).reverse.map
        (ons_dartRev L)).head? := by
    have hhead : (ons_decWalkExternalDarts p).reverse.head? = some d := by
      simpa using hd
    rw [List.head?_map, hhead]
    simp
  rw [← ons_decWalkExternalDarts_reverse p] at hdrev
  have hsite := ons_decWalkExternalDarts_head_site p.reverse hdrev
  simpa [ons_dartRev] using hsite



theorem ons_decWalkExternalDarts_isChain_closed
    {L : ℕ} {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) :
    List.IsChain
      (fun e f : ons_Dart L =>
        ons_dirStep L e.2 e.1 = f.1)
      (ons_decWalkExternalDarts q ++ [d]) := by
  apply (ons_decWalkExternalDarts_isChain q).append (.singleton d)
  intro e he f hf
  have hfd : f = d := (by simpa using hf : d = f).symm
  subst f
  exact ons_decWalkExternalDarts_getLast_site q he



theorem ons_decCycleFirstReturn_isChain_KW
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) :
    List.IsChain
      (fun e f : ons_Dart L =>
        e.1 = ons_dirStep L f.2 f.1)
      (ons_decCycleFirstReturn q) := by
  let ext := ons_decWalkExternalDarts q
  have hhead : ext.head? = some d :=
    ons_decWalkExternalDarts_head q hq hsnd
  have hext : ext = d :: ext.tail := by
    apply List.eq_cons_of_mem_head?
    simpa [hhead]
  have hclosed := ons_decWalkExternalDarts_isChain_closed q
  have hreverse : List.IsChain
      (fun e f : ons_Dart L =>
        ons_dirStep L f.2 f.1 = e.1)
      (ext ++ [d]).reverse := by
    exact List.isChain_reverse.mpr hclosed
  have hfirst : ons_decCycleFirstReturn q = (ext ++ [d]).reverse := by
    calc
      ons_decCycleFirstReturn q =
          d :: ext.tail.reverse ++ [d] := rfl
      _ = (d :: ext.tail ++ [d]).reverse := by simp
      _ = (ext ++ [d]).reverse := by rw [hext]; simp
  rw [hfirst]
  exact hreverse.imp (fun {_ _} h => h.symm)



theorem ons_KWmatWeightedPhase_entry_factor
    (L : ℕ) (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega u v : ℂ) (d2 d1 : ons_Dart L) :
    ons_KWmatWeightedPhase L weight omega u v d2 d1 =
      weight (ons_portEdge L d1) *
        ons_KWmatWeightedPhase L (fun _ => 1) omega u v d2 d1 := by
  unfold ons_KWmatWeightedPhase ons_KWmatWeighted
  split <;> ring



theorem ons_edgeWeight_KWmatWeightedPhase_factor
    (L : ℕ) (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega u v : ℂ) (s : List (ons_Dart L)) :
    ons_edgeWeight (ons_KWmatWeightedPhase L weight omega u v) s =
      ((s.tail.map (fun d => weight (ons_portEdge L d))).prod) *
        ons_edgeWeight
          (ons_KWmatWeightedPhase L (fun _ => 1) omega u v) s := by
  induction s with
  | nil => simp
  | cons d2 rest ih =>
      cases rest with
      | nil => simp
      | cons d1 t =>
          rw [ons_edgeWeight_cons_cons, ons_edgeWeight_cons_cons,
            ons_KWmatWeightedPhase_entry_factor, ih]
          simp only [List.tail_cons, List.map_cons, List.prod_cons]
          ring



theorem ons_decCycleFirstReturn_weight_factor
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d)
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega u v : ℂ) :
    ons_edgeWeight (ons_KWmatWeightedPhase L weight omega u v)
        (ons_decCycleFirstReturn q) =
      (∏ edge ∈ ons_walkOriginalEdges q, weight edge) *
        ons_edgeWeight
          (ons_KWmatWeightedPhase L (fun _ => 1) omega u v)
          (ons_decCycleFirstReturn q) := by
  rw [ons_edgeWeight_KWmatWeightedPhase_factor]
  congr 1
  let ext := ons_decWalkExternalDarts q
  have hhead : ext.head? = some d :=
    ons_decWalkExternalDarts_head q hq hsnd
  have hext : ext = d :: ext.tail := by
    apply List.eq_cons_of_mem_head?
    simpa [hhead]
  have htail : (ons_decCycleFirstReturn q).tail = ext.reverse := by
    change (d :: ext.tail.reverse ++ [d]).tail = ext.reverse
    rw [hext]
    simp
  rw [htail, List.map_reverse, List.prod_reverse,
    ons_walkOriginalEdges_prod_eq_externalDarts q hq weight]

end StatMech.Onsager
