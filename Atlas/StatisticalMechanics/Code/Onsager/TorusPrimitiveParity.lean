/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Onsager.TorusPrimitiveWinding



namespace StatMech.Onsager

open SimpleGraph

private theorem isChain_closed_ofFn
    {α : Type*} {r : α → α → Prop}
    {n : ℕ} [NeZero n] (f : Fin n → α)
    (hstep : ∀ k : Fin n, r (f k) (f (k + 1))) :
    List.IsChain r (List.ofFn f ++ [f 0]) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  apply List.IsChain.append
  · rw [List.isChain_ofFn]
    intro i hi
    let k : Fin (m + 1) := ⟨i, by omega⟩
    have hk : k ≠ Fin.last m := by
      intro h
      have := Fin.mk.inj_iff.mp h
      omega
    have hnext : k + 1 = ⟨i + 1, by omega⟩ := by
      apply Fin.ext
      exact Fin.val_add_one_of_lt (lt_of_le_of_ne (Fin.le_last k) hk)
    simpa [k, hnext] using hstep k
  · exact .singleton _
  · intro x hx y hy
    have hxlast : x = f (Fin.last m) := by
      rw [List.getLast?_eq_getLast (by simp), List.getLast_ofFn] at hx
      simpa using hx.symm
    have hyzero : y = f 0 := by simpa using hy.symm
    subst x
    subst y
    simpa using hstep (Fin.last m)

private theorem zipWith_closed_ofFn
    {α β : Type*} {n : ℕ} [NeZero n]
    (g : α → α → β) (f : Fin n → α) :
    List.zipWith g (List.ofFn f ++ [f 0])
        (List.ofFn f ++ [f 0]).tail =
      List.ofFn fun k : Fin n ↦ g (f k) (f (k + 1)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [List.ofFn_succ]
  simp only [List.cons_append, List.tail_cons]
  apply List.ext_getElem
  · simp
  · intro i hi h'i
    simp only [List.length_zipWith] at hi
    simp only [List.getElem_zipWith, List.getElem_ofFn]
    have hiN : i < m + 1 := by simpa using h'i
    let k : Fin (m + 1) := ⟨i, hiN⟩
    have hsource :
        (f 0 :: (List.ofFn (fun j : Fin m ↦ f j.succ) ++ [f 0]))[i] =
          f k := by
      cases i with
      | zero => simp [k]
      | succ i =>
          have hiM : i < m := by omega
          simp [List.getElem_append, hiM, k]
    have htarget :
        (List.ofFn (fun j : Fin m ↦ f j.succ) ++ [f 0])[i] =
          f (k + 1) := by
      by_cases hiM : i < m
      · simp [List.getElem_append, hiM, k]
        congr 1
        apply Fin.ext
        have hk : k < Fin.last m := by
          change i < m
          exact hiM
        exact (Fin.val_add_one_of_lt hk).symm
      · have hiEq : i = m := by omega
        subst i
        simp only [List.getElem_append, List.length_ofFn, lt_self_iff_false,
          ↓reduceDIte, Nat.sub_self, List.getElem_singleton, Fin.isValue]
        congr 1
        apply Fin.ext
        have hklast : k = Fin.last m := by
          apply Fin.ext
          simp [k]
        rw [hklast, Fin.last_add_one]
    rw [hsource, htarget]

private theorem closed_ofFn_tail_nodup
    {α : Type*} {n : ℕ} [NeZero n]
    (f : Fin n → α) (hinj : Function.Injective f) :
    (List.ofFn f ++ [f 0]).tail.Nodup := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [List.ofFn_succ]
  simp only [List.cons_append, List.tail_cons, List.nodup_append]
  constructor
  · rw [List.nodup_ofFn]
    intro i j hij
    exact Fin.succ_injective m (hinj hij)
  · constructor
    · simp
    · intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      rw [List.mem_ofFn] at ha
      obtain ⟨i, hi⟩ := ha
      intro hai
      have hindex : i.succ = (0 : Fin (m + 1)) :=
        hinj (hi.trans hai)
      exact Fin.succ_ne_zero i hindex




theorem ons_dartEdgeSet_evenSubgraph_of_site_injective
    {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k ↦ (v k).1))
    (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2) :
    ons_dartEdgeSet v ∈
      StatMech.Ising.evenSubgraphs (onsTorusGraph L) := by
  let site : Fin n → ZMod L × ZMod L := fun k ↦ (v (-k)).1
  let edge : Fin n → Sym2 (ZMod L × ZMod L) :=
    fun k ↦ ons_portEdge L (v (-k))
  let closed := List.ofFn site ++ [site 0]
  have hsiteInj : Function.Injective site := by
    intro i j hij
    have hneg : -i = -j := hsite hij
    simpa using congrArg Neg.neg hneg
  have hstepSite (k : Fin n) :
      site (k + 1) = ons_dirStep L (v (-k)).2 (site k) := by
    have h := hvalid (-(k + 1))
    have hidx : -(k + 1) + 1 = -k := by abel
    rw [hidx] at h
    simpa [site] using h
  have hadj (k : Fin n) :
      (onsTorusGraph L).Adj (site k) (site (k + 1)) := by
    rw [hstepSite]
    have h := ons_portEdge_mem_edgeFinset L (v (-k))
    rw [SimpleGraph.mem_edgeFinset] at h
    change (onsTorusGraph L).Adj (v (-k)).1
      (ons_dirStep L (v (-k)).2 (v (-k)).1) at h
    simpa [site] using h
  have hchain : List.IsChain (onsTorusGraph L).Adj closed := by
    exact isChain_closed_ofFn site hadj
  have hclosed : closed ≠ [] := by simp [closed, NeZero.ne n]
  let p0 := SimpleGraph.Walk.ofSupport closed hclosed hchain
  have hhead : closed.head hclosed = site 0 := by
    have hneFn : List.ofFn site ≠ [] := by simp [NeZero.ne n]
    change (List.ofFn site ++ [site 0]).head hclosed = site 0
    rw [List.head_append]
    simp [List.isEmpty_eq_false_iff.mpr hneFn, List.head_ofFn hneFn]
  have hlast : closed.getLast hclosed = site 0 := by simp [closed]
  let p : (onsTorusGraph L).Walk (site 0) (site 0) :=
    p0.copy hhead hlast
  have hsupport : p.support = closed := by
    simp [p, p0]
  have hedgeStep (k : Fin n) :
      s(site k, site (k + 1)) = edge k := by
    rw [hstepSite]
    rfl
  have hedges : p.edges = List.ofFn edge := by
    rw [SimpleGraph.Walk.edges_eq_zipWith_support, hsupport]
    rw [zipWith_closed_ofFn]
    apply congrArg List.ofFn
    funext k
    exact hedgeStep k
  have hedgeInj : Function.Injective edge := by
    intro i j hij
    have hneg := (ons_portEdge_loop_injective v hvalid hsite hnu) hij
    simpa using congrArg Neg.neg hneg
  have hpcycle : p.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_def]
    refine ⟨?_, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isTrail_def, hedges, List.nodup_ofFn]
      exact hedgeInj
    · intro hpnil
      have hlen : (List.ofFn edge).length = 0 := by
        rw [← hedges, hpnil]
        rfl
      simp only [List.length_ofFn] at hlen
      exact (NeZero.ne n) hlen
    · rw [hsupport]
      exact closed_ofFn_tail_nodup site hsiteInj
  have heven := ons_cycle_edges_evenSubgraph (onsTorusGraph L) p hpcycle
  rw [hedges] at heven
  have hedgeSet : (List.ofFn edge).toFinset = ons_dartEdgeSet v := by
    ext e
    simp only [List.mem_toFinset, List.mem_ofFn, ons_dartEdgeSet,
      Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨-k, ?_⟩
      simpa [edge] using hk
    · rintro ⟨k, hk⟩
      refine ⟨-k, ?_⟩
      simpa [edge] using hk
  rwa [hedgeSet] at heven




theorem ons_simpleLoop_horizontal_winding_eq_zero_or_odd
    {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k ↦ (v k).1))
    (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
    (mx : ℤ)
    (hmx : (∑ k, ons_dirExponentX (v k).2) = (L : ℤ) * mx)
    (hmy : (∑ k, ons_dirExponentY (v k).2) = 0) :
    mx = 0 ∨ Odd mx := by
  by_cases hmx0 : mx = 0
  · exact Or.inl hmx0
  · right
    have hF := ons_dartEdgeSet_evenSubgraph_of_site_injective
      v hvalid hsite hnu
    apply Int.not_even_iff_odd.mp
    intro heven
    have hmyScaled : (∑ k, ons_dirExponentY (v k).2) =
        (L : ℤ) * 0 := by simpa using hmy
    have hhom := ons_evenHomology_dartEdgeSet_eq_windingParity
      v hvalid hsite hnu mx 0 hmx hmyScaled
    have hparity : ons_windingParity mx 0 = 0 := by
      apply Prod.ext
      · simp [ons_windingParity, ons_intParity, heven]
      · simp [ons_windingParity, ons_intParity]
    have hzeroHomology : ons_evenHomology L (ons_dartEdgeSet v) = 0 := by
      rw [hhom, hparity]
    have hxzero := (ons_simpleLoop_zeroHomology_winding_eq_zero
      v hvalid hsite hnu hF hzeroHomology).1
    rw [hmx] at hxzero
    have hL : (L : ℤ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (lt_trans (by decide : 0 < 2)
        (Fact.out : 2 < L)))
    exact hmx0 ((mul_eq_zero.mp hxzero).resolve_left hL)



theorem ons_simpleLoop_horizontal_winding_odd_of_ne_zero
    {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k ↦ (v k).1))
    (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
    (mx : ℤ)
    (hmx : (∑ k, ons_dirExponentX (v k).2) = (L : ℤ) * mx)
    (hmy : (∑ k, ons_dirExponentY (v k).2) = 0)
    (hmx0 : mx ≠ 0) :
    Odd mx := by
  exact (ons_simpleLoop_horizontal_winding_eq_zero_or_odd
    v hvalid hsite hnu mx hmx hmy).resolve_left hmx0

end StatMech.Onsager
