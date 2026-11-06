/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

@[expose] public section

section
namespace MathlibExt.Combinatorics.SimpleGraph.DiracWanted

/-!
# Dirac's theorem

Hamiltonian cycle from minimum degree at least half the number of vertices.
-/

/-- Minimum degree at least 2 under the Dirac hypothesis with at least 3 vertices. -/
private theorem dirac_deg_ge_two {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hdeg : ∀ v : V, Fintype.card V ≤ 2 * G.degree v) (v : V) :
    2 ≤ G.degree v := by
  have h := hdeg v
  omega

/-- The Dirac degree hypothesis implies any two vertices are joined by a walk
of length at most 2 (hence the graph is preconnected). -/
private theorem dirac_preconnected {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v : V, Fintype.card V ≤ 2 * G.degree v) :
    G.Preconnected := by
  classical
  intro u v
  by_cases heq : u = v
  · subst heq
    exact SimpleGraph.Reachable.refl u
  · by_cases huv : G.Adj u v
    · exact huv.reachable
    · -- A common neighbour exists by counting.
      have hvU : v ∉ G.neighborFinset u := by
        rw [SimpleGraph.mem_neighborFinset]
        exact huv
      have huV : u ∉ G.neighborFinset v := by
        rw [SimpleGraph.mem_neighborFinset]
        exact fun h => huv h.symm
      have hsub : G.neighborFinset u ∪ G.neighborFinset v
          ⊆ ((Finset.univ.erase u).erase v) := by
        intro w hw
        rw [Finset.mem_erase, Finset.mem_erase]
        rcases Finset.mem_union.mp hw with h | h
        · rw [SimpleGraph.mem_neighborFinset] at h
          exact ⟨fun hv => huv (hv ▸ h), (G.ne_of_adj h).symm, Finset.mem_univ w⟩
        · rw [SimpleGraph.mem_neighborFinset] at h
          exact ⟨(G.ne_of_adj h).symm,
            fun hu => huv (hu ▸ h).symm, Finset.mem_univ w⟩
      have hcardU := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr
          ⟨Ne.symm heq, Finset.mem_univ v⟩),
        Finset.card_erase_of_mem (Finset.mem_univ u),
        Finset.card_univ] at hcardU
      have hdu := SimpleGraph.card_neighborFinset_eq_degree G u
      have hdv := SimpleGraph.card_neighborFinset_eq_degree G v
      have hsum := hdeg u
      have hsum2 := hdeg v
      have : Nontrivial V := ⟨u, v, heq⟩
      have hn2 : 2 ≤ Fintype.card V := by
        have h := Fintype.one_lt_card (α := V)
        omega
      have hinter : (G.neighborFinset u ∩ G.neighborFinset v).Nonempty := by
        rw [← Finset.card_pos]
        have hunion := Finset.card_union_add_card_inter
          (G.neighborFinset u) (G.neighborFinset v)
        omega
      obtain ⟨w, hw⟩ := hinter
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
        SimpleGraph.mem_neighborFinset] at hw
      exact hw.1.reachable.trans hw.2.symm.reachable

/-- Neighbours of the start of a longest path lie on the path. -/
private theorem dirac_mem_of_adj_left_of_maxpath {V : Type*}
    (G : SimpleGraph V)
    {a b : V} {P : G.Walk a b} (hP : P.IsPath)
    (hmax : ∀ (u' v' : V) (p' : G.Walk u' v'), p'.IsPath → p'.length ≤ P.length)
    {w : V} (h : G.Adj w a) : w ∈ P.support := by
  by_contra hw
  have hpath : (SimpleGraph.Walk.cons h P).IsPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff]
    exact ⟨hP, hw⟩
  have hle := hmax _ _ _ hpath
  rw [SimpleGraph.Walk.length_cons] at hle
  omega

/-- Neighbours of the end of a longest path lie on the path. -/
private theorem dirac_mem_of_adj_right_of_maxpath {V : Type*}
    (G : SimpleGraph V)
    {a b : V} {P : G.Walk a b} (hP : P.IsPath)
    (hmax : ∀ (u' v' : V) (p' : G.Walk u' v'), p'.IsPath → p'.length ≤ P.length)
    {w : V} (h : G.Adj b w) : w ∈ P.support := by
  by_contra hw
  have hpath : (P.concat h).IsPath := hP.concat hw h
  have hle := hmax _ _ _ hpath
  rw [SimpleGraph.Walk.length_concat] at hle
  omega

/-- A longest (maximal-length) path exists. -/
private theorem dirac_exists_maxpath {V : Type*} [Finite V]
    (G : SimpleGraph V) [Nonempty V] :
    ∃ (a b : V) (P : G.Walk a b) (_ : P.IsPath),
      ∀ (u' v' : V) (p' : G.Walk u' v'), p'.IsPath → p'.length ≤ P.length := by
  have : Finite G.edgeSet := by infer_instance
  exact SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G

/-- A longest path has length at least 2 (via a length-2 path from min-degree 2). -/
private theorem dirac_maxpath_ge_two {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hdeg : ∀ v : V, Fintype.card V ≤ 2 * G.degree v)
    {a b : V} {P : G.Walk a b}
    (hmax : ∀ (u' v' : V) (p' : G.Walk u' v'), p'.IsPath → p'.length ≤ P.length) :
    2 ≤ P.length := by
  classical
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  have hdx : 2 ≤ (G.neighborFinset x).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact dirac_deg_ge_two G hcard hdeg x
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < (G.neighborFinset x).card)
  have hxy : G.Adj x y := (SimpleGraph.mem_neighborFinset G x y).mp hy
  have hdy : 2 ≤ (G.neighborFinset y).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact dirac_deg_ge_two G hcard hdeg y
  have hmem : x ∈ G.neighborFinset y :=
    (SimpleGraph.mem_neighborFinset G y x).mpr hxy.symm
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem hmem]; omega :
    0 < ((G.neighborFinset y).erase x).card)
  rw [Finset.mem_erase] at hw
  obtain ⟨hwne, hwm⟩ := hw
  have hyw : G.Adj y w := (SimpleGraph.mem_neighborFinset G y w).mp hwm
  set Q := SimpleGraph.Walk.cons hxy
    (SimpleGraph.Walk.cons hyw SimpleGraph.Walk.nil) with hQ
  have hQpath : Q.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hQ]
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]
    have e1 : x ∉ [y, w] := by simp [G.ne_of_adj hxy, hwne.symm]
    have e2 : y ∉ [w] := by simp [G.ne_of_adj hyw]
    exact List.nodup_cons.mpr ⟨e1, List.nodup_cons.mpr ⟨e2, List.nodup_singleton w⟩⟩
  have hle := hmax _ _ _ hQpath
  have hQlen : Q.length = 2 := rfl
  omega

/-- Rotation index: along a longest path, some consecutive pair straddles the
endpoints (`a` reaches forward, `b` reaches backward). Proved by counting:
both neighbour-sets embed into `range length` disjointly. -/
private theorem dirac_rot_idx {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v : V, Fintype.card V ≤ 2 * G.degree v)
    {a b : V} {P : G.Walk a b} (hP : P.IsPath)
    (hmax : ∀ (u' v' : V) (p' : G.Walk u' v'), p'.IsPath → p'.length ≤ P.length) :
    ∃ j, j < P.length ∧ G.Adj a (P.getVert (j + 1)) ∧ G.Adj b (P.getVert j) := by
  classical
  have inj := hP.getVert_injOn
  have hmemA : ∀ w : V, G.Adj a w → w ∈ P.support := fun w h =>
    dirac_mem_of_adj_left_of_maxpath G hP hmax h.symm
  have hmemB : ∀ w : V, G.Adj b w → w ∈ P.support := fun w h =>
    dirac_mem_of_adj_right_of_maxpath G hP hmax h
  classical
  set l := P.length with hl
  set A := Finset.range l |>.filter (fun j => G.Adj a (P.getVert (j + 1))) with hA
  set B := Finset.range l |>.filter (fun j => G.Adj b (P.getVert j)) with hB
  have hinjA : Set.InjOn (fun j => P.getVert (j + 1)) (↑A) := by
    intro x hx y hy heq
    simp only [hA, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx hy
    have ex : x + 1 ≤ l := by omega
    have ey : y + 1 ≤ l := by omega
    have e := inj ex ey heq
    omega
  have hAcard : A.card = G.degree a := by
    have himg : G.neighborFinset a = A.image (fun j => P.getVert (j + 1)) := by
      ext w
      simp only [hA, SimpleGraph.mem_neighborFinset, Finset.mem_image,
        Finset.mem_filter, Finset.mem_range]
      constructor
      · intro hadj
        have hmem := hmemA w hadj
        rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hmem
        obtain ⟨k, hkvert, hkle⟩ := hmem
        have hk0 : k ≠ 0 := by
          intro hk0'
          have hwa : w = a := by rw [← hkvert, hk0',
            SimpleGraph.Walk.getVert_zero]
          exact (G.ne_of_adj hadj).symm hwa
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
        refine ⟨j, ⟨by omega, by rw [hkvert]; exact hadj⟩, hkvert⟩
      · rintro ⟨j, ⟨hjl, hadj⟩, rfl⟩
        exact hadj
    have h1 : A.card = (A.image (fun j => P.getVert (j + 1))).card :=
      (Finset.card_image_of_injOn hinjA).symm
    rw [h1, ← himg, SimpleGraph.card_neighborFinset_eq_degree]
  have hinjB : Set.InjOn (fun j => P.getVert j) (↑B) := by
    intro x hx y hy heq
    simp only [hB, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx hy
    have ex : x ≤ l := by omega
    have ey : y ≤ l := by omega
    exact inj ex ey heq
  have hBcard : B.card = G.degree b := by
    have himg : G.neighborFinset b = B.image (fun j => P.getVert j) := by
      ext w
      simp only [hB, SimpleGraph.mem_neighborFinset, Finset.mem_image,
        Finset.mem_filter, Finset.mem_range]
      constructor
      · intro hadj
        have hmem := hmemB w hadj
        rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hmem
        obtain ⟨k, hkvert, hkle⟩ := hmem
        have hkl : k ≠ l := by
          intro hkl'
          have hwb : w = b := by rw [← hkvert, hkl',
            SimpleGraph.Walk.getVert_length]
          exact (G.ne_of_adj hadj).symm hwb
        refine ⟨k, ⟨by omega, by rw [hkvert]; exact hadj⟩, hkvert⟩
      · rintro ⟨j, ⟨hjl, hadj⟩, rfl⟩
        exact hadj
    have h1 : B.card = (B.image (fun j => P.getVert j)).card :=
      (Finset.card_image_of_injOn hinjB).symm
    rw [h1, ← himg, SimpleGraph.card_neighborFinset_eq_degree]
  by_contra hcon
  have hdis : Disjoint A B := by
    rw [Finset.disjoint_left]
    rintro x hxA hxB
    simp only [hA, hB, Finset.mem_filter, Finset.mem_range] at hxA hxB
    obtain ⟨hxAl, hxAadj⟩ := hxA
    obtain ⟨hxBl, hxBadj⟩ := hxB
    exact hcon ⟨x, hxAl, hxAadj, hxBadj⟩
  have hsub : A ∪ B ⊆ Finset.range l :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hle := Finset.card_le_card hsub
  rw [Finset.card_range,
    Finset.card_union_of_disjoint hdis] at hle
  have hda := hdeg a
  have hdb := hdeg b
  have hsupp : P.length + 1 ≤ Fintype.card V := by
    have h1 := hP.support_nodup.length_le_card
    rwa [SimpleGraph.Walk.length_support] at h1
  omega

/-- The rotation cycle: a longest path closes up to a cycle through exactly the
same vertices. The cycle goes along the path to `xⱼ`, jumps to the end `b`,
runs the rest of the path backwards to `xⱼ₊₁`, and jumps back to `a`. -/
private theorem dirac_cycle_of_maxpath {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v : V, Fintype.card V ≤ 2 * G.degree v)
    {a b : V} {P : G.Walk a b} (hP : P.IsPath)
    (hmax : ∀ (u' v' : V) (p' : G.Walk u' v'), p'.IsPath → p'.length ≤ P.length)
    (hl2 : 2 ≤ P.length) :
    ∃ C : G.Walk a a, C.IsCycle ∧ C.length = P.length + 1 ∧
      (∀ w, w ∈ C.support ↔ w ∈ P.support) := by
  classical
  obtain ⟨j, hjl, hadjA, hadjB⟩ := dirac_rot_idx G hdeg hP hmax
  have h1 : G.Adj (P.getVert j) b := hadjB.symm
  have h2 : G.Adj (P.getVert (j + 1)) a := hadjA.symm
  set T := P.take j with hT
  set E1 := h1.toWalk with hE1
  set A := T.append E1 with hA
  set D := P.drop (j + 1) with hD
  set R := D.reverse with hR
  set E2 := h2.toWalk with hE2
  set B := R.append E2 with hB
  set C := A.append B with hC
  have hjl1 : j + 1 ≤ P.length := hjl
  -- Length facts.
  have hE1l : E1.length = 1 := h1.length_toWalk
  have hE2l : E2.length = 1 := h2.length_toWalk
  have hTl : T.length = j := by
    rw [hT, SimpleGraph.Walk.take_length, Nat.min_eq_left (le_of_lt hjl)]
  have hDlen : D.length = P.length - (j + 1) := by
    rw [hD, SimpleGraph.Walk.drop_length]
  have hRl : R.length = D.length := by
    rw [hR]; exact SimpleGraph.Walk.length_reverse D
  have hAl : A.length = j + 1 := by
    rw [hA, SimpleGraph.Walk.length_append, hTl, hE1l]
  have hBl : B.length = D.length + 1 := by
    rw [hB, SimpleGraph.Walk.length_append, hE2l, hRl]
  have hClen : C.length = P.length + 1 := by
    rw [hC, SimpleGraph.Walk.length_append, hAl, hBl, hDlen]
    omega
  have inj := hP.getVert_injOn
  -- Endpoint values of the single-edge walks.
  have hE1src : E1.getVert 0 = P.getVert j := SimpleGraph.Walk.getVert_zero E1
  have hE1end : E1.getVert 1 = b := by
    have h := SimpleGraph.Walk.getVert_length E1
    rwa [hE1l] at h
  have hE2src : E2.getVert 0 = P.getVert (j + 1) := SimpleGraph.Walk.getVert_zero E2
  have hE2end : E2.getVert 1 = a := by
    have h := SimpleGraph.Walk.getVert_length E2
    rwa [hE2l] at h
  have hPa : P.getVert 0 = a := SimpleGraph.Walk.getVert_zero P
  have hPb : P.getVert P.length = b := SimpleGraph.Walk.getVert_length P
  -- Branch equations for `getVert` along the cycle.
  have hB1 : ∀ m, m ≤ j → C.getVert m = P.getVert m := by
    intro m hm
    have hmA : m < A.length := by rw [hAl]; omega
    rw [hC, SimpleGraph.Walk.getVert_append, ite_eq_left hmA]
    by_cases hmT : m < T.length
    · rw [hA, SimpleGraph.Walk.getVert_append, ite_eq_left hmT, hT,
        SimpleGraph.Walk.take_getVert]
      congr 1
      omega
    · have hmj : m = j := by rw [hTl] at hmT; omega
      have hnT : ¬ j < T.length := by rw [hTl]; omega
      rw [hA, SimpleGraph.Walk.getVert_append, hmj, ite_eq_right hnT]
      have hz : j - T.length = 0 := by rw [hTl]; omega
      rw [hz, hE1src]
  have hB2 : C.getVert (j + 1) = P.getVert P.length := by
    have hnA : ¬ j + 1 < A.length := by rw [hAl]; omega
    rw [hC, SimpleGraph.Walk.getVert_append, ite_eq_right hnA]
    have hz : j + 1 - A.length = 0 := by rw [hAl]; omega
    rw [hz, SimpleGraph.Walk.getVert_zero, hPb]
  have hB3 : ∀ m, j + 2 ≤ m → m ≤ P.length →
      C.getVert m = P.getVert (P.length - (m - (j + 1))) := by
    intro m hmlo hmhi
    have hnA : ¬ m < A.length := by rw [hAl]; omega
    rw [hC, SimpleGraph.Walk.getVert_append, ite_eq_right hnA]
    set k := m - A.length with hk
    have hkm : k = m - (j + 1) := by rw [hk, hAl]
    have hkD : k ≤ D.length := by rw [hkm, hDlen]; omega
    by_cases hkR : k < R.length
    · have hpos : k < R.length := hkR
      rw [hB, SimpleGraph.Walk.getVert_append, ite_eq_left hpos]
      have e1 : R.getVert k = D.getVert (D.length - k) :=
        SimpleGraph.Walk.getVert_reverse D k
      have e2 : D.getVert (D.length - k) = P.getVert ((j + 1) + (D.length - k)) := by
        rw [hD]; exact SimpleGraph.Walk.drop_getVert P (j + 1) (D.length - k)
      rw [e1, e2]
      congr 1
      rw [hDlen] at *
      omega
    · have hkE : k = R.length := by omega
      have hneg : ¬ k < R.length := by rw [hkE]; exact lt_irrefl _
      rw [hB, SimpleGraph.Walk.getVert_append, ite_eq_right hneg]
      have hk0 : k - R.length = 0 := by omega
      rw [hk0, hE2src]
      congr 1
      omega
  have hB4 : C.getVert (P.length + 1) = P.getVert 0 := by
    rw [← hClen, SimpleGraph.Walk.getVert_length, SimpleGraph.Walk.getVert_zero]
  -- Every index maps into the path, with its `k`-form and branch condition recorded.
  have hphi : ∀ m, 1 ≤ m → m ≤ P.length + 1 → ∃ k, k ≤ P.length ∧
      C.getVert m = P.getVert k ∧
      ((k = m ∧ m ≤ j) ∨ (k = P.length ∧ m = j + 1) ∨
        (k = P.length - (m - (j + 1)) ∧ j + 2 ≤ m ∧ m ≤ P.length) ∨
        (k = 0 ∧ m = P.length + 1)) := by
    intro m hmlo hmhi
    by_cases h1' : m ≤ j
    · exact ⟨m, by omega, hB1 m h1', Or.inl ⟨rfl, h1'⟩⟩
    · by_cases h2' : m = j + 1
      · subst h2'
        exact ⟨P.length, le_refl _, hB2, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
      · by_cases h3 : m ≤ P.length
        · refine ⟨P.length - (m - (j + 1)), Nat.sub_le _ _, hB3 m (by omega) h3,
            Or.inr (Or.inr (Or.inl ⟨rfl, by omega, h3⟩))⟩
        · have hm4 : m = P.length + 1 := by omega
          subst hm4
          exact ⟨0, Nat.zero_le _, hB4, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
  -- `getVert` is injective on `1 .. length+1`.
  have hinjC : Set.InjOn C.getVert {m | 1 ≤ m ∧ m ≤ P.length + 1} := by
    intro m1 hm1 m2 hm2 heq
    simp only [Set.mem_ofPred_eq] at hm1 hm2
    obtain ⟨k1, kb1, e1, hk1⟩ := hphi m1 hm1.1 hm1.2
    obtain ⟨k2, kb2, e2, hk2⟩ := hphi m2 hm2.1 hm2.2
    rw [e1, e2] at heq
    have e := inj kb1 kb2 heq
    rcases hk1 with ⟨rfl, h1c⟩ | ⟨rfl, h2c⟩ | ⟨rfl, h3c1, h3c2⟩ | ⟨rfl, h4c⟩ <;>
      rcases hk2 with ⟨rfl, h5c⟩ | ⟨rfl, h6c⟩ | ⟨rfl, h7c1, h7c2⟩ | ⟨rfl, h8c⟩
    all_goals omega
  -- The cycle has the same support as the path.
  have hsup : ∀ w, w ∈ C.support ↔ w ∈ P.support := by
    intro w
    constructor
    · intro hw
      rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hw
      obtain ⟨n, hnvert, hnle⟩ := hw
      rw [hClen] at hnle
      by_cases hn0 : n = 0
      · subst hn0
        rw [SimpleGraph.Walk.getVert_zero] at hnvert
        subst hnvert
        exact SimpleGraph.Walk.start_mem_support P
      · obtain ⟨k, kb, e, -⟩ := hphi n (by omega) hnle
        rw [← hnvert, e]
        exact SimpleGraph.Walk.getVert_mem_support P k
    · intro hw
      rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hw
      obtain ⟨n, hnvert, hnle⟩ := hw
      by_cases hn0 : n = 0
      · subst hn0
        rw [SimpleGraph.Walk.getVert_zero] at hnvert
        subst hnvert
        have hmem := SimpleGraph.Walk.getVert_mem_support C 0
        rwa [SimpleGraph.Walk.getVert_zero] at hmem
      · by_cases hnl : n = P.length
        · subst hnl
          rw [← hnvert, ← hB2]
          exact SimpleGraph.Walk.getVert_mem_support C (j + 1)
        · by_cases hnj : n ≤ j
          · rw [← hnvert, ← hB1 n hnj]
            exact SimpleGraph.Walk.getVert_mem_support C n
          · -- `j + 1 ≤ n ≤ length - 1`: reach back via `hB3` at `m = length`.
            have hnm : j + 1 ≤ n ∧ n ≤ P.length - 1 := by omega
            have e3 := hB3 P.length (by omega) (le_refl _)
            have hform : P.length - (P.length - (j + 1)) = j + 1 := by
              rw [Nat.sub_sub_self hjl1]
            rw [hform] at e3
            -- `e3 : C.getVert length = P.getVert (j+1)`; combine as needed
            by_cases hnj1 : n = j + 1
            · subst hnj1
              rw [← hnvert, ← e3]
              exact SimpleGraph.Walk.getVert_mem_support C P.length
            · set m := (j + 1) + (P.length - n) with hmdef
              have hm1 : j + 2 ≤ m := by rw [hmdef]; omega
              have hm2 : m ≤ P.length := by rw [hmdef]; omega
              have em := hB3 m hm1 hm2
              have hform2 : P.length - (m - (j + 1)) = n := by rw [hmdef]; omega
              rw [hform2] at em
              rw [← hnvert, ← em]
              exact SimpleGraph.Walk.getVert_mem_support C m
  -- Assemble the cycle.
  have hcyc : C.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
    refine ⟨?_, by rw [hClen]; omega⟩
    have htaillen : C.tail.length = P.length := by
      rw [SimpleGraph.Walk.tail, SimpleGraph.Walk.drop_length, hClen]
      omega
    rw [← SimpleGraph.Walk.IsPath.getVert_injOn_iff]
    intro m1 hm1 m2 hm2 heq
    simp only [Set.mem_ofPred_eq] at hm1 hm2
    simp only [SimpleGraph.Walk.getVert_tail] at heq
    obtain ⟨k1, kb1, e1, hk1⟩ := hphi (m1 + 1) (by omega) (by omega)
    obtain ⟨k2, kb2, e2, hk2⟩ := hphi (m2 + 1) (by omega) (by omega)
    rw [e1, e2] at heq
    have e := inj kb1 kb2 heq
    rcases hk1 with ⟨rfl, h1c⟩ | ⟨rfl, h2c⟩ | ⟨rfl, h3c1, h3c2⟩ | ⟨rfl, h4c⟩ <;>
      rcases hk2 with ⟨rfl, h5c⟩ | ⟨rfl, h6c⟩ | ⟨rfl, h7c1, h7c2⟩ | ⟨rfl, h8c⟩
    all_goals omega
  exact ⟨C, hcyc, hClen, hsup⟩

/-- The longest path spans every vertex: otherwise, rotating the cycle at the
first point of contact with an outside vertex yields a longer path. -/
private theorem dirac_spanning {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v : V, Fintype.card V ≤ 2 * G.degree v)
    {a b : V} {P : G.Walk a b}
    (hmax : ∀ (u' v' : V) (p' : G.Walk u' v'), p'.IsPath → p'.length ≤ P.length)
    {C : G.Walk a a} (hC : C.IsCycle)
    (hsup : ∀ w, w ∈ C.support ↔ w ∈ P.support)
    (hlenC : C.length = P.length + 1) :
    ∀ w, w ∈ P.support := by
  classical
  have hpre := dirac_preconnected G hdeg
  intro w
  by_contra hw
  obtain ⟨Q, -⟩ := (hpre w a).exists_isPath
  have haP : a ∈ P.support :=
    (hsup a).mp (SimpleGraph.Walk.start_mem_support C)
  classical
  have hex : ∃ n, Q.getVert n ∈ P.support ∧ n ≤ Q.length :=
    ⟨Q.length, by rw [SimpleGraph.Walk.getVert_length]; exact haP, le_refl _⟩
  have hkspec := Nat.find_spec hex
  have hkmin : ∀ m, (Q.getVert m ∈ P.support ∧ m ≤ Q.length) → Nat.find hex ≤ m := by
    intro m hm
    exact Nat.find_min' hex hm
  set k := Nat.find hex with hkdef
  obtain ⟨hkmem, hkle⟩ := hkspec
  have hk0 : k ≠ 0 := by
    intro hk0'
    rw [hk0'] at hkmem
    rw [SimpleGraph.Walk.getVert_zero] at hkmem
    exact hw hkmem
  have hmin : Q.getVert (k - 1) ∉ P.support := by
    intro hcon
    have h1 : k ≤ k - 1 := hkmin (k - 1) ⟨hcon, by omega⟩
    omega
  have hadj : G.Adj (Q.getVert (k - 1)) (Q.getVert k) := by
    have hlt : k - 1 < Q.length := by omega
    have h := Q.adj_getVert_succ hlt
    rwa [Nat.sub_add_cancel (show 1 ≤ k by omega)] at h
  have hz'C : Q.getVert k ∈ C.support := (hsup _).mpr hkmem
  have hC'cyc := SimpleGraph.Walk.IsCycle.rotate hz'C hC
  set C' := C.rotate _ hz'C with hC'def
  set Dd := C'.dropLast with hDddef
  have hdrop : Dd.IsPath := hC'cyc.isPath_dropLast
  have hzC' : Q.getVert (k - 1) ∉ C'.support := by
    rw [SimpleGraph.Walk.mem_support_rotate_iff]
    intro hcon
    exact hmin ((hsup _).mp hcon)
  have hsub : Dd.support ⊆ C'.support := by
    rw [hDddef]
    exact (SimpleGraph.Walk.isSubwalk_take C' (C'.length - 1)).support_subset
  have hDpath : (SimpleGraph.Walk.cons hadj Dd).IsPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff]
    refine ⟨hdrop, ?_⟩
    intro hcon
    exact hzC' (hsub hcon)
  have hle := hmax _ _ _ hDpath
  have hDlen : (SimpleGraph.Walk.cons hadj Dd).length = P.length + 1 := by
    have h1 : (SimpleGraph.Walk.cons hadj Dd).length = Dd.length + 1 :=
      SimpleGraph.Walk.length_cons _ _
    have h2 : Dd.length = C'.length - 1 := by
      rw [hDddef]; exact SimpleGraph.Walk.length_dropLast C'
    have h3 : C'.length = C.length := by
      rw [hC'def]; exact SimpleGraph.Walk.length_rotate C _ hz'C
    omega
  omega

/--
**Dirac's theorem.** Let $G$ be a finite simple graph with $n \ge 3$ vertices in which every
vertex has degree at least $n/2$. Then $G$ is Hamiltonian, that is, it has a cycle that visits
every vertex exactly once.

Proves `Wanted` entry `dirac`.

Source: G. A. Dirac, Some Theorems on Abstract Graphs, Proc. London Math. Soc. s3-2 (1952), 69–81,
DOI 10.1112/plms/s3-2.1.69.
-/
theorem dirac {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hdeg : ∀ v : V, Fintype.card V ≤ 2 * G.degree v) :
    G.IsHamiltonian := by
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨a, b, P, hP, hmax⟩ := dirac_exists_maxpath G
  have hl2 := dirac_maxpath_ge_two G hcard hdeg hmax
  obtain ⟨C, hcyc, hlenC, hsup⟩ := dirac_cycle_of_maxpath G hdeg hP hmax hl2
  have hspan := dirac_spanning G hdeg hmax hcyc hsup hlenC
  have hcardV : Fintype.card V = P.length + 1 := by
    have h1 := hP.support_nodup.length_le_card
    rw [SimpleGraph.Walk.length_support] at h1
    have hsub : Finset.univ ⊆ P.support.toFinset := by
      intro w _
      rw [List.mem_toFinset]
      exact hspan w
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_univ, List.toFinset_card_of_nodup hP.support_nodup,
      SimpleGraph.Walk.length_support] at h2
    omega
  intro hne1
  refine ⟨a, C, ?_⟩
  rw [SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
  exact ⟨hcyc, by omega⟩

end MathlibExt.Combinatorics.SimpleGraph.DiracWanted
