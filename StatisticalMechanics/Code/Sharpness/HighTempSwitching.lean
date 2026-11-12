/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Sharpness.HighTempSources

open Finset
open scoped symmDiff

namespace StatMech
namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem hasOddBoundary_iff_srcP (F : Finset (Sym2 V)) (A : Finset V) :
    HasOddBoundary F A ↔ srcP F = A := by
  constructor
  · intro h
    ext v
    rw [mem_srcP]
    simpa [incCount, degP] using h v
  · intro h v
    rw [← h, mem_srcP]
    simp [incCount, degP]


theorem hasOddBoundary_symmDiff {F H : Finset (Sym2 V)}
    {A B : Finset V} (hF : HasOddBoundary F A)
    (hH : HasOddBoundary H B) :
    HasOddBoundary (F ∆ H) (A ∆ B) := by
  rw [hasOddBoundary_iff_srcP, srcP_symmDiff,
    (hasOddBoundary_iff_srcP F A).mp hF,
    (hasOddBoundary_iff_srcP H B).mp hH]


theorem mem_symmDiff_singleton_iff {α : Type*} [DecidableEq α]
    (S : Finset α) (a x : α) :
    x ∈ S ∆ {a} ↔ (x ∈ S ↔ x ≠ a) := by
  simp only [Finset.mem_symmDiff, Finset.mem_singleton]
  tauto



theorem card_pair_symmDiff_singleton {α : Type*} [DecidableEq α]
    (F H : Finset α) {e : α} (he : e ∈ F ∆ H) :
    (F ∆ {e}).card + (H ∆ {e}).card = F.card + H.card := by
  simp only [Finset.mem_symmDiff] at he
  by_cases heF : e ∈ F
  · have heH : e ∉ H := by tauto
    rw [show F ∆ {e} = F.erase e by
        ext x
        rw [mem_symmDiff_singleton_iff]
        by_cases hxe : x = e
        · subst x; simp [heF]
        · simp [hxe],
      show H ∆ {e} = insert e H by
        ext x
        rw [mem_symmDiff_singleton_iff]
        by_cases hxe : x = e
        · subst x; simp [heH]
        · simp [hxe],
      card_erase_of_mem heF, card_insert_of_notMem heH]
    have hFpos : 0 < F.card := card_pos.mpr ⟨e, heF⟩
    omega
  · have heH : e ∈ H := by tauto
    rw [show F ∆ {e} = insert e F by
        ext x
        rw [mem_symmDiff_singleton_iff]
        by_cases hxe : x = e
        · subst x; simp [heF]
        · simp [hxe],
      show H ∆ {e} = H.erase e by
        ext x
        rw [mem_symmDiff_singleton_iff]
        by_cases hxe : x = e
        · subst x; simp [heH]
        · simp [hxe],
      card_insert_of_notMem heF, card_erase_of_mem heH]
    have hHpos : 0 < H.card := card_pos.mpr ⟨e, heH⟩
    omega



theorem card_pair_symmDiff_eq {α : Type*} [DecidableEq α]
    (F H Q : Finset α) (hQ : Q ⊆ F ∆ H) :
    (F ∆ Q).card + (H ∆ Q).card = F.card + H.card := by
  induction Q using Finset.induction_on generalizing F H with
  | empty =>
      have hF : F ∆ (∅ : Finset α) = F := by
        ext x
        simp [Finset.mem_symmDiff]
      have hH : H ∆ (∅ : Finset α) = H := by
        ext x
        simp [Finset.mem_symmDiff]
      rw [hF, hH]
  | @insert e Q heQ ih =>
      have heFH : e ∈ F ∆ H := hQ (by simp)
      have hpair : (F ∆ {e}) ∆ (H ∆ {e}) = F ∆ H := by
        ext x
        by_cases hxe : x = e
        · subst x
          simp only [Finset.mem_symmDiff, Finset.mem_singleton]
          tauto
        · simp only [Finset.mem_symmDiff, Finset.mem_singleton]
          simp only [hxe, false_iff, iff_false]
          tauto
      have hQsub : Q ⊆ (F ∆ {e}) ∆ (H ∆ {e}) := by
        intro x hx
        rw [hpair]
        exact hQ (Finset.mem_insert_of_mem hx)
      have hstep := card_pair_symmDiff_singleton F H heFH
      have hrest := ih (F := F ∆ {e}) (H := H ∆ {e}) hQsub
      have hFin : F ∆ insert e Q = (F ∆ {e}) ∆ Q := by
        ext x
        simp only [Finset.mem_symmDiff, Finset.mem_insert,
          Finset.mem_singleton]
        by_cases hxe : x = e
        · subst x
          simp [heQ]
        · by_cases hxQ : x ∈ Q <;> simp [hxe, hxQ] <;> tauto
      have hHin : H ∆ insert e Q = (H ∆ {e}) ∆ Q := by
        ext x
        simp only [Finset.mem_symmDiff, Finset.mem_insert,
          Finset.mem_singleton]
        by_cases hxe : x = e
        · subst x
          simp [heQ]
        · by_cases hxQ : x ∈ Q <;> simp [hxe, hxQ] <;> tauto
      rw [hFin, hHin]
      exact hrest.trans hstep





def sourcePair (a b : V) : Finset V := ({a} : Finset V) ∆ {b}

@[simp]
theorem sourcePair_self (a : V) : sourcePair a a = ∅ := by
  simp [sourcePair]

theorem sourcePair_eq_pair {a b : V} (hab : a ≠ b) :
    sourcePair a b = {a, b} := by
  ext v
  simp only [sourcePair, Finset.mem_symmDiff, Finset.mem_singleton,
    Finset.mem_insert]
  constructor
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact Or.inl ⟨rfl, hab⟩
    · exact Or.inr ⟨rfl, hab.symm⟩


theorem sourcePair_chain (a b c d : V) :
    sourcePair a b ∆ sourcePair b c ∆ sourcePair c d = sourcePair a d := by
  ext v
  simp only [sourcePair, Finset.mem_symmDiff, Finset.mem_singleton]
  tauto



theorem hasOddBoundary_path_edges {K : SimpleGraph V} {a b : V}
    (p : K.Walk a b) (hp : p.IsPath) :
    HasOddBoundary p.edges.toFinset (sourcePair a b) := by
  intro v
  have hdeg : incCount p.edges.toFinset v = walkDeg p v := by
    unfold incCount walkDeg
    have hfilter :
        p.edges.toFinset.filter (fun e => v ∈ e) =
          (p.edges.filter (fun e => decide (v ∈ e))).toFinset := by
      ext e
      simp
    rw [hfilter]
    exact List.toFinset_card_of_nodup (hp.edges_nodup.filter _)
  rw [hdeg, walkDeg_odd_iff p hp v]
  simp only [sourcePair, Finset.mem_symmDiff, Finset.mem_singleton]
  constructor
  · rintro ⟨rfl | rfl, hab⟩
    · exact Or.inl ⟨rfl, hab⟩
    · exact Or.inr ⟨rfl, hab.symm⟩
  · rintro (⟨hva, hvb⟩ | ⟨hvb, hva⟩)
    · exact ⟨Or.inl hva, fun hab => hvb (hva.trans hab)⟩
    · exact ⟨Or.inr hvb, fun hab => hva (hvb.trans hab.symm)⟩



private theorem walk_edge_getElem {K : SimpleGraph V} {a b : V}
    (p : K.Walk a b) (i : ℕ) (hi : i < p.length) :
    p.edges[i]'(by rw [SimpleGraph.Walk.length_edges]; exact hi) =
      s(p.getVert i, p.getVert (i + 1)) := by
  induction p generalizing i with
  | nil => simp at hi
  | cons hadj q ih =>
      cases i with
      | zero =>
          simp only [SimpleGraph.Walk.edges_cons, List.getElem_cons_zero,
            SimpleGraph.Walk.getVert_zero]
          congr 1
          rw [SimpleGraph.Walk.getVert_cons_succ,
            SimpleGraph.Walk.getVert_zero]
      | succ n =>
          simp only [SimpleGraph.Walk.edges_cons, List.getElem_cons_succ]
          rw [SimpleGraph.Walk.length_cons] at hi
          rw [ih n (by omega), SimpleGraph.Walk.getVert_cons_succ,
            SimpleGraph.Walk.getVert_cons_succ]





theorem sourcePair_symmDiff_firstExit
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F H : Finset (Sym2 V)) {o z : V}
    (hFsub : F ⊆ G.edgeFinset) (hHsub : H ⊆ G.edgeFinset)
    (hoz : o ≠ z) (hF : HasOddBoundary F (sourcePair o z))
    (hH : HasOddBoundary H ∅) (S : Finset V) (ho : o ∈ S) (hz : z ∉ S) :
    ∃ x ∈ S, ∃ y ∉ S, ∃ Q : Finset (Sym2 V),
      Q ⊆ F ∆ H ∧ HasOddBoundary Q (sourcePair o x) ∧
        s(x, y) ∉ Q ∧ s(x, y) ∈ F ∆ H := by
  have hUsub : F ∆ H ⊆ G.edgeFinset := by
    intro e he
    simp only [Finset.mem_symmDiff] at he
    rcases he with ⟨heF, _⟩ | ⟨heH, _⟩
    · exact hFsub heF
    · exact hHsub heH
  have hU0 := hasOddBoundary_symmDiff hF hH
  have hU : HasOddBoundary (F ∆ H) (sourcePair o z) := by
    convert hU0 using 1
    ext v
    simp only [sourcePair, Finset.mem_symmDiff, Finset.mem_singleton]
    tauto
  have hUpair : HasOddBoundary (F ∆ H) {o, z} := by
    rw [← sourcePair_eq_pair hoz]
    exact hU
  let p := (hasOddBoundary_backbone G (F ∆ H) hUsub hoz hUpair).some
  obtain ⟨k, hk1, hkle, hx, hy, _, hodd, _, _⟩ :=
    backbone_firstExit G p S ho hz
  let x := p.1.getVert (k - 1)
  let y := p.1.getVert k
  let Q := (p.1.take (k - 1)).edges.toFinset
  have hQbd : HasOddBoundary Q (sourcePair o x) := by
    exact hasOddBoundary_path_edges (p.1.take (k - 1)) (p.2.take (k - 1))
  have hQsub : Q ⊆ F ∆ H := by
    intro e he
    have heTake : e ∈ (p.1.take (k - 1)).edges := by
      exact List.mem_toFinset.mp he
    have hePath : e ∈ p.1.edges := by
      rw [SimpleGraph.Walk.edges_take] at heTake
      exact List.mem_of_mem_take heTake
    have heOdd := isBackbonePath_edge_odd G p hePath
    by_contra heU
    simp [edgeIndicatorCurrent, heU] at heOdd
  have heQ : s(x, y) ∉ Q := by
    intro he
    have heTake : s(x, y) ∈ List.take (k - 1) p.1.edges := by
      rw [← SimpleGraph.Walk.edges_take]
      exact List.mem_toFinset.mp he
    have hlenE : k - 1 < p.1.edges.length := by
      rw [SimpleGraph.Walk.length_edges]
      omega
    have hedge :
        s(x, y) = p.1.edges[k - 1]'hlenE := by
      have h := walk_edge_getElem p.1 (k - 1) (by omega)
      rw [show k - 1 + 1 = k by omega] at h
      exact h.symm
    have heDrop : s(x, y) ∈ List.drop (k - 1) p.1.edges := by
      rw [List.drop_eq_getElem_cons hlenE, ← hedge]
      exact List.mem_cons_self
    exact List.disjoint_take_drop p.2.edges_nodup (le_refl (k - 1)) heTake heDrop
  have heU : s(x, y) ∈ F ∆ H := by
    by_contra he
    simp [x, y, edgeIndicatorCurrent, he] at hodd
  exact ⟨x, hx, y, hy, Q, hQsub, hQbd, heQ, heU⟩


theorem erase_eq_symmDiff_singleton {α : Type*} [DecidableEq α]
    (F : Finset α) {e : α} (he : e ∈ F) :
    F.erase e = F ∆ {e} := by
  ext x
  rw [mem_symmDiff_singleton_iff]
  by_cases hxe : x = e
  · subst x
    simp [he]
  · simp [hxe]



theorem card_switch_erase_exit {α : Type*} [DecidableEq α]
    (F H Q : Finset α) {e : α} (hQ : Q ⊆ F ∆ H)
    (heF : e ∈ F) (heQ : e ∉ Q) :
    (H ∆ Q).card + ((F ∆ Q).erase e).card + 1 = F.card + H.card := by
  have heToggle : e ∈ F ∆ Q := by
    simp only [Finset.mem_symmDiff]
    exact Or.inl ⟨heF, heQ⟩
  have hcard := card_pair_symmDiff_eq F H Q hQ
  have herase := card_erase_of_mem heToggle
  have hpos : 0 < (F ∆ Q).card := card_pos.mpr ⟨e, heToggle⟩
  omega


theorem hasOddBoundary_singleton_sourcePair {x y : V} (hxy : x ≠ y) :
    HasOddBoundary ({s(x, y)} : Finset (Sym2 V)) (sourcePair x y) := by
  rw [hasOddBoundary_iff_srcP, sourcePair_eq_pair hxy]
  exact srcP_singleton s(x, y) x y rfl hxy






theorem hasOddBoundary_switch_erase_exit
    {F H Q : Finset (Sym2 V)} {o x y z : V}
    (hF : HasOddBoundary F (sourcePair o z))
    (hH : HasOddBoundary H ∅)
    (hQ : HasOddBoundary Q (sourcePair o x))
    (hxy : x ≠ y) (heF : s(x, y) ∈ F) (heQ : s(x, y) ∉ Q) :
    HasOddBoundary (H ∆ Q) (sourcePair o x) ∧
      HasOddBoundary ((F ∆ Q).erase s(x, y)) (sourcePair y z) := by
  have hleft := hasOddBoundary_symmDiff hH hQ
  have heToggle : s(x, y) ∈ F ∆ Q := by
    simp only [Finset.mem_symmDiff]
    exact Or.inl ⟨heF, heQ⟩
  have hright0 := hasOddBoundary_symmDiff hF hQ
  have hedge := hasOddBoundary_singleton_sourcePair (V := V) hxy
  have hright1 := hasOddBoundary_symmDiff hright0 hedge
  constructor
  · have hempty : (∅ : Finset V) ∆ sourcePair o x = sourcePair o x := by
      ext v
      simp [Finset.mem_symmDiff]
    rw [hempty] at hleft
    exact hleft
  · rw [erase_eq_symmDiff_singleton (F ∆ Q) heToggle]
    convert hright1 using 1
    ext v
    simp only [sourcePair, Finset.mem_symmDiff, Finset.mem_singleton]
    tauto





structure HighTempFirstExit (K : Finset (Sym2 V)) (o z : V)
    (S : Finset V) where
  x : V
  y : V
  Q : Finset (Sym2 V)
  x_mem : x ∈ S
  y_notMem : y ∉ S
  Q_subset : Q ⊆ K
  Q_inside : ∀ e ∈ Q, edgeInside S e
  Q_sources : HasOddBoundary Q (sourcePair o x)
  exit_mem : s(x, y) ∈ K
  exit_notMem : s(x, y) ∉ Q
  ne : x ≠ y



theorem exists_highTempFirstExit (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Finset (Sym2 V)) (hK : K ⊆ G.edgeFinset) {o z : V}
    (hbd : HasOddBoundary K (sourcePair o z)) (S : Finset V)
    (ho : o ∈ S) (hz : z ∉ S) :
    Nonempty (HighTempFirstExit K o z S) := by
  have hoz : o ≠ z := fun h => hz (h ▸ ho)
  have hbd' : HasOddBoundary K {o, z} := by
    rwa [sourcePair_eq_pair hoz] at hbd
  let p := (hasOddBoundary_backbone G K hK hoz hbd').some
  obtain ⟨k, hk1, hkle, hx, hy, _heG, hodd, _hpos, hprev⟩ :=
    backbone_firstExit G p S ho hz
  let x := p.1.getVert (k - 1)
  let y := p.1.getVert k
  let qwalk := p.1.take (k - 1)
  let Q := qwalk.edges.toFinset
  have hQsub : Q ⊆ K := by
    intro e he
    have heList : e ∈ qwalk.edges := by simpa [Q] using he
    have hePath : e ∈ p.1.edges := by
      change e ∈ (p.1.take (k - 1)).edges at heList
      rw [SimpleGraph.Walk.edges_take] at heList
      exact List.take_subset _ _ heList
    have heOdd := isBackbonePath_edge_odd G p hePath
    by_contra heK
    simp [edgeIndicatorCurrent, heK] at heOdd
  have hQinside : ∀ e ∈ Q, edgeInside S e := by
    intro e he v hv
    have heList : e ∈ qwalk.edges := by simpa [Q] using he
    have hvSupp : v ∈ qwalk.support := qwalk.mem_support_of_mem_edges heList hv
    change v ∈ (p.1.take (k - 1)).support at hvSupp
    rw [SimpleGraph.Walk.take_support_eq_support_take_succ,
      List.mem_take_iff_getElem] at hvSupp
    obtain ⟨j, hj, hvj⟩ := hvSupp
    have hjk : j < k := by
      have : j < k - 1 + 1 := hj.trans_le (Nat.min_le_left _ _)
      omega
    have hjlen : j ≤ p.1.length := hjk.le.trans hkle
    have hget : p.1.getVert j = v := by
      rw [p.1.getVert_eq_support_getElem hjlen]
      exact hvj
    exact hget ▸ hprev j hjk
  have hQsrc : HasOddBoundary Q (sourcePair o x) := by
    have hpath : qwalk.IsPath := p.2.take (k - 1)
    simpa only [Q, qwalk, x] using hasOddBoundary_path_edges qwalk hpath
  have hexitK : s(x, y) ∈ K := by
    by_contra heK
    simp [x, y, edgeIndicatorCurrent, heK] at hodd
  have hexitQ : s(x, y) ∉ Q := by
    intro heQ
    have heTake : s(x, y) ∈ List.take (k - 1) p.1.edges := by
      have : s(x, y) ∈ (p.1.take (k - 1)).edges := by
        simpa [Q, qwalk] using heQ
      rwa [SimpleGraph.Walk.edges_take] at this
    have hi : k - 1 < p.1.length := by omega
    have hedgeEq : p.1.edges[k - 1]'(by simpa using hi) = s(x, y) := by
      simpa only [x, y, show k - 1 + 1 = k by omega] using
        walk_edge_getElem p.1 (k - 1) hi
    have heDrop : s(x, y) ∈ List.drop (k - 1) p.1.edges := by
      rw [List.drop_eq_getElem_cons (by simpa using hi), hedgeEq]
      simp
    exact (List.disjoint_take_drop p.2.isTrail.edges_nodup (le_refl (k - 1)))
      heTake heDrop
  refine ⟨⟨x, y, Q, hx, hy, hQsub, hQinside, hQsrc,
    hexitK, hexitQ, ?_⟩⟩
  exact (SimpleGraph.mem_edgeFinset.mp (hK hexitK)).ne



noncomputable def highTempFirstExit (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Finset (Sym2 V)) (hK : K ⊆ G.edgeFinset) {o z : V}
    (hbd : HasOddBoundary K (sourcePair o z)) (S : Finset V)
    (ho : o ∈ S) (hz : z ∉ S) : HighTempFirstExit K o z S :=
  (exists_highTempFirstExit G K hK hbd S ho hz).some



theorem highTempFirstExit_Q_congr (G : SimpleGraph V) [DecidableRel G.Adj]
    {K L : Finset (Sym2 V)} (hKL : K = L)
    (hK : K ⊆ G.edgeFinset) (hL : L ⊆ G.edgeFinset) {o z : V}
    (hbdK : HasOddBoundary K (sourcePair o z))
    (hbdL : HasOddBoundary L (sourcePair o z)) (S : Finset V)
    (ho : o ∈ S) (hz : z ∉ S) :
    (highTempFirstExit G K hK hbdK S ho hz).Q =
      (highTempFirstExit G L hL hbdL S ho hz).Q := by
  subst L
  rfl





theorem prod_pair_symmDiff_eq {α : Type*} [DecidableEq α]
    (t : α → ℝ) (F H Q : Finset α) (hQ : Q ⊆ F ∆ H) :
    (∏ e ∈ F ∆ Q, t e) * (∏ e ∈ H ∆ Q, t e) =
      (∏ e ∈ F, t e) * (∏ e ∈ H, t e) := by
  induction Q using Finset.induction_on generalizing F H with
  | empty =>
      have hF : F ∆ (∅ : Finset α) = F := by
        ext x
        simp only [Finset.mem_symmDiff, Finset.notMem_empty, not_false_eq_true,
          and_true, false_and, or_false]
      have hH : H ∆ (∅ : Finset α) = H := by
        ext x
        simp only [Finset.mem_symmDiff, Finset.notMem_empty, not_false_eq_true,
          and_true, false_and, or_false]
      rw [hF, hH]
  | @insert e Q heQ ih =>
      have heFH : e ∈ F ∆ H := hQ (by simp)
      have hpair : (F ∆ {e}) ∆ (H ∆ {e}) = F ∆ H := by
        ext x
        simp only [Finset.mem_symmDiff, Finset.mem_singleton]
        tauto
      have hQsub : Q ⊆ (F ∆ {e}) ∆ (H ∆ {e}) := by
        intro x hx
        rw [hpair]
        exact hQ (Finset.mem_insert_of_mem hx)
      have hrest := ih (F := F ∆ {e}) (H := H ∆ {e}) hQsub
      have hFin : F ∆ insert e Q = (F ∆ {e}) ∆ Q := by
        ext x
        simp only [Finset.mem_symmDiff, Finset.mem_insert,
          Finset.mem_singleton]
        by_cases hxe : x = e
        · subst x
          simp [heQ]
        · by_cases hxQ : x ∈ Q <;> simp [hxe, hxQ] <;> tauto
      have hHin : H ∆ insert e Q = (H ∆ {e}) ∆ Q := by
        ext x
        simp only [Finset.mem_symmDiff, Finset.mem_insert,
          Finset.mem_singleton]
        by_cases hxe : x = e
        · subst x
          simp [heQ]
        · by_cases hxQ : x ∈ Q <;> simp [hxe, hxQ] <;> tauto
      rw [hFin, hHin, hrest]
      rcases (Finset.mem_symmDiff.mp heFH) with ⟨heF, heH⟩ | ⟨heH, heF⟩
      · have hFs : F ∆ {e} = F.erase e := by
          ext x
          rw [mem_symmDiff_singleton_iff]
          by_cases hxe : x = e <;> simp [hxe, heF]
        have hHs : H ∆ {e} = insert e H := by
          ext x
          rw [mem_symmDiff_singleton_iff]
          by_cases hxe : x = e <;> simp [hxe, heH]
        rw [hFs, hHs, Finset.prod_insert heH,
          ← Finset.prod_erase_mul F t heF]
        ring
      · have hFs : F ∆ {e} = insert e F := by
          ext x
          rw [mem_symmDiff_singleton_iff]
          by_cases hxe : x = e <;> simp [hxe, heF]
        have hHs : H ∆ {e} = H.erase e := by
          ext x
          rw [mem_symmDiff_singleton_iff]
          by_cases hxe : x = e <;> simp [hxe, heH]
        rw [hFs, hHs, Finset.prod_insert heF,
          ← Finset.prod_erase_mul H t heH]
        ring


theorem prod_switch_erase_exit (t : Sym2 V → ℝ)
    (F H Q : Finset (Sym2 V)) {x y : V} (hQ : Q ⊆ F ∆ H)
    (heF : s(x, y) ∈ F) (heQ : s(x, y) ∉ Q) :
    (∏ e ∈ H ∆ Q, t e) * t s(x, y) *
        (∏ e ∈ (F ∆ Q).erase s(x, y), t e) =
      (∏ e ∈ F, t e) * (∏ e ∈ H, t e) := by
  have he : s(x, y) ∈ F ∆ Q := by
    exact Finset.mem_symmDiff.mpr (Or.inl ⟨heF, heQ⟩)
  have hprod := prod_pair_symmDiff_eq t F H Q hQ
  have herase := Finset.prod_erase_mul (F ∆ Q) t he
  rw [mul_comm (∏ e ∈ F ∆ Q, t e) (∏ e ∈ H ∆ Q, t e)] at hprod
  calc
    (∏ e ∈ H ∆ Q, t e) * t s(x, y) *
        (∏ e ∈ (F ∆ Q).erase s(x, y), t e) =
      (∏ e ∈ H ∆ Q, t e) *
        ((∏ e ∈ (F ∆ Q).erase s(x, y), t e) * t s(x, y)) := by ring
    _ = (∏ e ∈ H ∆ Q, t e) * (∏ e ∈ F ∆ Q, t e) := by rw [herase]
    _ = _ := hprod

end Sharpness
end StatMech
