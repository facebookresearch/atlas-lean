/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.BoxSurfaceVolume
import Code.Lattice.Clusters
import Code.Percolation.BurtonKeane
import Code.Percolation.BurtonKeaneUniqueness
import Code.Percolation.TrifurcationCount
import Code.Percolation.BurtonKeaneClose
import Code.Percolation.ForestLeafCountClose
import Code.Percolation.SingleLeafHallClose
import Code.Percolation.BoundaryPruningClose
import Code.Percolation.BKSpanningTreeClose
import Code.Percolation.OpenSpanningForestClose

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}












def spc_OnBPath {V : Type*} (T : SimpleGraph V) (B : Set V) (v : V) : Prop :=
  ∃ b₁ b₂ : V, b₁ ∈ B ∧ b₂ ∈ B ∧ b₁ ≠ b₂ ∧ ∃ p : T.Walk b₁ b₂, p.IsPath ∧ v ∈ p.support




theorem spc_survivor_has_neighbor {V : Type*} (T : SimpleGraph V) (B : Set V)
    (v : V) (h : spc_OnBPath T B v) : ∃ w, T.Adj v w ∧ spc_OnBPath T B w := by
  obtain ⟨b₁, b₂, hb₁, hb₂, hne, p, hp, hmem⟩ := h
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hmem
  obtain ⟨i, hvi, hile⟩ := hmem
  have hlen : 0 < p.length := by
    rcases Nat.eq_zero_or_pos p.length with h0 | h0
    · exact absurd (p.eq_of_length_eq_zero h0) hne
    · exact h0
  by_cases hi : i < p.length
  · exact ⟨p.getVert (i + 1), hvi ▸ p.adj_getVert_succ hi,
      ⟨b₁, b₂, hb₁, hb₂, hne, p, hp, p.getVert_mem_support _⟩⟩
  · have hieq : i = p.length := le_antisymm hile (not_lt.mp hi)
    refine ⟨p.getVert (p.length - 1), ?_,
      ⟨b₁, b₂, hb₁, hb₂, hne, p, hp, p.getVert_mem_support _⟩⟩
    have hadj := p.adj_getVert_succ (i := p.length - 1) (by omega)
    rw [Nat.sub_add_cancel hlen] at hadj
    rw [← hvi, hieq]; exact hadj.symm





theorem spc_interior_two_neighbors {V : Type*} (T : SimpleGraph V) (B : Set V)
    (v : V) (hv : spc_OnBPath T B v) (hvB : v ∉ B) :
    ∃ w₁ w₂ : V, w₁ ≠ w₂ ∧ T.Adj v w₁ ∧ T.Adj v w₂ ∧
      spc_OnBPath T B w₁ ∧ spc_OnBPath T B w₂ := by
  obtain ⟨b₁, b₂, hb₁, hb₂, hne, p, hp, hmem⟩ := hv
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hmem
  obtain ⟨i, hvi, hile⟩ := hmem
  have hvb1 : v ≠ b₁ := fun h => hvB (h ▸ hb₁)
  have hvb2 : v ≠ b₂ := fun h => hvB (h ▸ hb₂)
  have hi0 : i ≠ 0 := by intro h; subst h; rw [p.getVert_zero] at hvi; exact hvb1 hvi.symm
  have hilen : i ≠ p.length := by
    intro h; subst h; rw [p.getVert_length] at hvi; exact hvb2 hvi.symm
  have hipos : 0 < i := Nat.pos_of_ne_zero hi0
  have hilt : i < p.length := lt_of_le_of_ne hile hilen
  refine ⟨p.getVert (i - 1), p.getVert (i + 1), ?_, ?_, ?_, ?_, ?_⟩
  · intro hcontra
    have := hp.getVert_injOn (x₁ := i - 1) (x₂ := i + 1)
      (by simp only [Set.mem_setOf_eq]; omega) (by simp only [Set.mem_setOf_eq]; omega) hcontra
    omega
  · rw [← hvi]
    have hadj := p.adj_getVert_succ (i := i - 1) (by omega)
    rw [Nat.sub_add_cancel hipos] at hadj; exact hadj.symm
  · rw [← hvi]; exact p.adj_getVert_succ hilt
  · exact ⟨b₁, b₂, hb₁, hb₂, hne, p, hp, p.getVert_mem_support _⟩
  · exact ⟨b₁, b₂, hb₁, hb₂, hne, p, hp, p.getVert_mem_support _⟩







section Degrees
variable {W : Type*} [Fintype W] [DecidableEq W] (F : SimpleGraph W) [DecidableRel F.Adj]

omit [DecidableEq W] in

theorem spc_deg_ge_one (v w : W) (h : F.Adj v w) : 1 ≤ F.degree v := by
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, F.degree_pos_iff_exists_adj]; exact ⟨w, h⟩

set_option linter.unusedDecidableInType false in

theorem spc_deg_ge_two (v w₁ w₂ : W) (hne : w₁ ≠ w₂) (h1 : F.Adj v w₁) (h2 : F.Adj v w₂) :
    2 ≤ F.degree v := by
  rw [← F.card_neighborFinset_eq_degree]
  have hsub : ({w₁, w₂} : Finset W) ⊆ F.neighborFinset v := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> rw [mem_neighborFinset] <;> assumption
  calc (2 : ℕ) = ({w₁, w₂} : Finset W).card := (Finset.card_pair hne).symm
    _ ≤ _ := Finset.card_le_card hsub

set_option linter.unusedDecidableInType false in

theorem spc_deg_ge_three (v w₁ w₂ w₃ : W) (h12 : w₁ ≠ w₂) (h13 : w₁ ≠ w₃) (h23 : w₂ ≠ w₃)
    (h1 : F.Adj v w₁) (h2 : F.Adj v w₂) (h3 : F.Adj v w₃) : 3 ≤ F.degree v := by
  rw [← F.card_neighborFinset_eq_degree]
  have hsub : ({w₁, w₂, w₃} : Finset W) ⊆ F.neighborFinset v := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> rw [mem_neighborFinset] <;> assumption
  calc (3 : ℕ) = ({w₁, w₂, w₃} : Finset W).card := by
        rw [Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_pair h23]
    _ ≤ _ := Finset.card_le_card hsub

end Degrees











theorem spc_map_acyclic {V V' : Type*} {G : SimpleGraph V} (hac : G.IsAcyclic) (f : V ↪ V') :
    (SimpleGraph.map f G).IsAcyclic := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · have hbot : SimpleGraph.map f G = ⊥ := by
      ext x y; rw [SimpleGraph.map_adj]; simp only [bot_adj, iff_false]
      rintro ⟨a, _, _, _, _⟩; exact isEmptyElim a
    rw [hbot]; exact isAcyclic_bot
  obtain ⟨g, hg⟩ : ∃ g : V' → V, ∀ a, g (f a) = a :=
    ⟨Function.invFun f, Function.leftInverse_invFun f.injective⟩
  set gHom : (SimpleGraph.map f G) →g G :=
    ⟨g, by intro x y hxy; rw [SimpleGraph.map_adj] at hxy
           obtain ⟨a, b, hab, rfl, rfl⟩ := hxy; rw [hg, hg]; exact hab⟩ with hgHom
  have hgHom_apply : ∀ w, gHom w = g w := fun _ => rfl
  intro u c hc
  have hlen : 0 < c.length := by have := hc.three_le_length; omega
  
  have hsupp_mem : ∀ w ∈ c.support, ∃ a, f a = w := by
    intro w hw
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hw
    obtain ⟨i, hi, hil⟩ := hw
    rcases Nat.lt_or_ge i c.length with hlt | hge
    · have hadj := c.adj_getVert_succ hlt
      rw [SimpleGraph.map_adj] at hadj; obtain ⟨a, b, hab, h1, h2⟩ := hadj
      exact ⟨a, h1.trans hi⟩
    · have hieq : i = c.length := le_antisymm hil hge
      have hadj := c.adj_getVert_succ (i := c.length - 1) (by omega)
      rw [SimpleGraph.map_adj] at hadj; obtain ⟨a, b, hab, h1, h2⟩ := hadj
      refine ⟨b, ?_⟩; rw [h2, ← hi, hieq]; congr 1; omega
  
  have hginj : ∀ x ∈ c.support, ∀ y ∈ c.support, g x = g y → x = y := by
    intro x hx y hy hxy
    obtain ⟨ax, rfl⟩ := hsupp_mem x hx
    obtain ⟨ay, rfl⟩ := hsupp_mem y hy
    rw [hg, hg] at hxy; rw [hxy]
  
  refine hac (c.map gHom) ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
  · rw [SimpleGraph.Walk.edges_map]
    refine List.Nodup.map_on ?_ hc.edges_nodup
    intro e1 he1 e2 he2 heq
    induction e1 with
    | _ p q =>
      induction e2 with
      | _ r s =>
        simp only [Sym2.map_mk, Sym2.eq_iff] at heq
        have hp := c.fst_mem_support_of_mem_edges he1
        have hq := c.snd_mem_support_of_mem_edges he1
        have hr := c.fst_mem_support_of_mem_edges he2
        have hs := c.snd_mem_support_of_mem_edges he2
        rw [Sym2.eq_iff]
        rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨hginj p hp r hr h1, hginj q hq s hs h2⟩
        · exact Or.inr ⟨hginj p hp s hs h1, hginj q hq r hr h2⟩
  · intro hnil
    have hl := SimpleGraph.Walk.length_map gHom c
    rw [hnil] at hl; simp only [SimpleGraph.Walk.length_nil] at hl; omega
  · rw [SimpleGraph.Walk.support_map]
    have htail : (List.map (⇑gHom) c.support).tail = List.map (⇑gHom) c.support.tail := by
      cases c.support <;> simp
    rw [htail]
    refine List.Nodup.map_on ?_ hc.support_nodup
    intro x hx y hy
    simp only [hgHom_apply]
    exact fun h => hginj x (List.mem_of_mem_tail hx) y (List.mem_of_mem_tail hy) h



















open Classical in




def spc_SpanForestArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (Vall : Finset (Site d)) (T : SimpleGraph (Site d)) (_ : DecidableRel T.Adj)
    (B : Set (Site d)) (m : Site d → Fin 3 → Site d),
    T.IsAcyclic ∧
    (∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v) ∧
    (∀ u v, T.Adj u v → u ∈ Vall) ∧
    (B ⊆ vertexBoundary d n) ∧
    (∃ v, spc_OnBPath T B v) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      spc_OnBPath T B x ∧
      ((m x 0 ≠ m x 1 ∧ m x 0 ≠ m x 2 ∧ m x 1 ≠ m x 2) ∧
       (∀ i, T.Adj x (m x i) ∧ spc_OnBPath T B (m x i)) ∧
       (¬ Connected d (removeSite x ω) (m x 0) (m x 1) ∧
        ¬ Connected d (removeSite x ω) (m x 0) (m x 2) ∧
        ¬ Connected d (removeSite x ω) (m x 1) (m x 2))))

open Classical in















theorem spc_peeledBoxForest_of_spanForestArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : spc_SpanForestArms ω n) : osf_PeeledBoxForest ω n := by
  classical
  obtain ⟨Vall, T, hTdec, B, m, hTac, hTopen, hTsupp, hBbd, hRne, hData⟩ := h
  
  have hRfin : {v | spc_OnBPath T B v}.Finite := by
    apply Set.Finite.subset (Vall.finite_toSet)
    intro v hv
    obtain ⟨w, hadj, _⟩ := spc_survivor_has_neighbor T B v hv
    exact hTsupp v w hadj
  set Vset : Finset (Site d) := hRfin.toFinset with hVset
  have hmemVset : ∀ v, v ∈ Vset ↔ spc_OnBPath T B v := by
    intro v; rw [hVset, Set.Finite.mem_toFinset]; rfl
  have hVne : Nonempty (↥Vset) := by
    obtain ⟨v, hv⟩ := hRne; exact ⟨⟨v, (hmemVset v).mpr hv⟩⟩
  set F₀ : SimpleGraph (↥Vset) := T.comap (fun (u : ↥Vset) => (u : Site d)) with hF₀
  haveI hF₀dec : DecidableRel F₀.Adj := fun a b => by rw [hF₀, comap_adj]; infer_instance
  have hF₀adj : ∀ u v : ↥Vset, F₀.Adj u v ↔ T.Adj (u : Site d) (v : Site d) := by
    intro u v; rw [hF₀, comap_adj]
  have hF₀ac : F₀.IsAcyclic :=
    hTac.comap ⟨(fun (u : ↥Vset) => (u : Site d)), fun {a b} h => h⟩ (fun a b h => Subtype.ext h)
  have hlift : ∀ v, spc_OnBPath T B v → v ∈ Vset := fun v hv => (hmemVset v).mpr hv
  
  let dflt : ↥Vset := hVne.some
  set vx : Site d → ↥Vset := fun x =>
    if hx : spc_OnBPath T B x then ⟨x, hlift x hx⟩ else dflt with hvxdef
  set bb : Site d → Fin 3 → ↥Vset := fun x i =>
    if hx : spc_OnBPath T B (m x i) then ⟨m x i, hlift _ hx⟩ else dflt with hbbdef
  refine osf_peeledBoxForest_of_acyclic ω n Vset hVne F₀ hF₀ac vx bb ?_ ?_ ?_ ?_
  · 
    intro u v huv
    rw [hF₀adj] at huv; exact hTopen _ _ huv
  · 
    intro v
    have hvR : spc_OnBPath T B (v : Site d) := (hmemVset (v : Site d)).mp v.2
    obtain ⟨w, hadjw, hwR⟩ := spc_survivor_has_neighbor T B (v : Site d) hvR
    exact spc_deg_ge_one F₀ v ⟨w, hlift w hwR⟩ (by rw [hF₀adj]; exact hadjw)
  · 
    intro x hxbox htri
    obtain ⟨hxR, hmne, hmadj, hmsep⟩ := hData x hxbox htri
    have hvxval : (vx x : Site d) = x := by simp only [hvxdef, dif_pos hxR]
    refine ⟨hvxval, ?_, ?_⟩
    · intro i
      have hmi := hmadj i
      have hbbval : (bb x i : Site d) = m x i := by simp only [hbbdef, dif_pos hmi.2]
      refine ⟨?_, ?_⟩
      · refine Adj.reachable ?_
        rw [hF₀adj, hvxval, hbbval]; exact hmi.1
      · intro hh
        have hval : (bb x i : Site d) = (vx x : Site d) :=
          congrArg (fun (u : ↥Vset) => (u : Site d)) hh
        rw [hbbval, hvxval] at hval
        exact (T.ne_of_adj hmi.1) hval.symm
    · have h0 : (bb x 0 : Site d) = m x 0 := by simp only [hbbdef, dif_pos (hmadj 0).2]
      have h1 : (bb x 1 : Site d) = m x 1 := by simp only [hbbdef, dif_pos (hmadj 1).2]
      have h2 : (bb x 2 : Site d) = m x 2 := by simp only [hbbdef, dif_pos (hmadj 2).2]
      rw [h0, h1, h2]; exact hmsep
  · 
    intro v hv
    have hvR : spc_OnBPath T B (v : Site d) := (hmemVset (v : Site d)).mp v.2
    by_cases hvB : (v : Site d) ∈ B
    · exact hBbd hvB
    · exfalso
      obtain ⟨w₁, w₂, hw12, ha1, ha2, hr1, hr2⟩ :=
        spc_interior_two_neighbors T B (v : Site d) hvR hvB
      have hdeg2 : 2 ≤ F₀.degree v :=
        spc_deg_ge_two F₀ v ⟨w₁, hlift w₁ hr1⟩ ⟨w₂, hlift w₂ hr2⟩
          (fun hh => hw12 (Subtype.ext_iff.mp hh))
          (by rw [hF₀adj]; exact ha1) (by rw [hF₀adj]; exact ha2)
      omega



theorem spc_boxOpenForest_of_spanForestArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : spc_SpanForestArms ω n) : bst_BoxOpenForest ω n :=
  osf_boxOpenForest_of_peeled ω n (spc_peeledBoxForest_of_spanForestArms ω n h)


theorem spc_Tcount_le_boundary_of_spanForestArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : spc_SpanForestArms ω n) : Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bst_Tcount_le_boundary_of_boxOpenForest ω n (spc_boxOpenForest_of_spanForestArms ω n h)









open Classical in



theorem spc_spanForestArms_of_boundary_edge (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {b₁ b₂ : Site d} (hb1 : b₁ ∈ vertexBoundary d n) (hb2 : b₂ ∈ vertexBoundary d n)
    (hbne : b₁ ≠ b₂) (hopen : (openSubgraph d ω).Adj b₁ b₂)
    (hnotrif : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    spc_SpanForestArms ω n := by
  classical
  set T : SimpleGraph (Site d) := SimpleGraph.fromEdgeSet {s(b₁, b₂)} with hT
  have hTb : T.Adj b₁ b₂ := by rw [hT, fromEdgeSet_adj]; exact ⟨by simp, hbne⟩
  have hTac : T.IsAcyclic := by
    rw [hT, isAcyclic_iff_forall_adj_isBridge]
    intro u v huv
    rw [fromEdgeSet_adj] at huv
    obtain ⟨hmem, hne⟩ := huv
    simp only [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
    rw [isBridge_iff]
    refine ⟨by rw [fromEdgeSet_adj]; exact ⟨by simp [hmem], hne⟩, ?_⟩
    intro hreach
    obtain ⟨w⟩ := hreach
    have hbot : ((SimpleGraph.fromEdgeSet {s(b₁, b₂)}).deleteEdges {s(u, v)}) = ⊥ := by
      ext a b
      rw [deleteEdges_adj]
      simp only [fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff, bot_adj, iff_false, not_and]
      rintro ⟨hab, habne⟩ hnab
      apply hnab
      rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
        subst_vars <;> tauto
    rw [hbot] at w
    exact hne (w.eq_of_length_eq_zero
      (by cases w with | nil => rfl | cons h _ => exact absurd h (by simp)))
  set B : Set (Site d) := {b₁, b₂} with hB
  set p : T.Walk b₁ b₂ := Walk.cons hTb Walk.nil with hp
  have hpp : p.IsPath := by
    rw [hp, SimpleGraph.Walk.isPath_def]
    change List.Nodup [b₁, b₂]
    simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, List.nodup_nil, and_true]
    exact ⟨hbne, by trivial⟩
  have honB1 : spc_OnBPath T B b₁ :=
    ⟨b₁, b₂, by simp [hB], by simp [hB], hbne, p, hpp, by simp [hp]⟩
  refine ⟨{b₁, b₂}, T, by rw [hT]; infer_instance, B, fun _ _ => b₁, hTac, ?_, ?_, ?_,
    ⟨b₁, honB1⟩, ?_⟩
  · intro u v huv
    rw [hT, fromEdgeSet_adj] at huv
    obtain ⟨hmem, hne⟩ := huv
    simp only [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hopen
    · exact hopen.symm
  · intro u v huv
    rw [hT, fromEdgeSet_adj] at huv
    obtain ⟨hmem, hne⟩ := huv
    simp only [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · rw [hB]; intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;> assumption
  · intro x hxbox htri; exact absurd htri (hnotrif x hxbox)












open Classical in



theorem spc_spanForestArms_star (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x : Site d} (a : Fin 3 → Site d)
    (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x)
    (hadj : ∀ i, (openSubgraph d ω).Adj x (a i))
    (habdry : ∀ i, a i ∈ vertexBoundary d n)
    (hxne : ∀ i, a i ≠ x)
    (hainj : Function.Injective a)
    (hsep : ¬ Connected d (removeSite x ω) (a 0) (a 1) ∧
            ¬ Connected d (removeSite x ω) (a 0) (a 2) ∧
            ¬ Connected d (removeSite x ω) (a 1) (a 2)) :
    spc_SpanForestArms ω n := by
  classical
  set lab : Fin 4 → Site d := fun v => match v with
    | 0 => x | 1 => a 0 | 2 => a 1 | 3 => a 2 with hlab
  have hlabinj : Function.Injective lab := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp only [hlab] at huv <;>
      first
        | rfl
        | (exact absurd huv (hxne 0).symm) | (exact absurd huv (hxne 1).symm)
        | (exact absurd huv (hxne 2).symm) | (exact absurd huv.symm (hxne 0).symm)
        | (exact absurd huv.symm (hxne 1).symm) | (exact absurd huv.symm (hxne 2).symm)
        | (exact absurd (hainj huv) (by decide))
  set emb : Fin 4 ↪ Site d := ⟨lab, hlabinj⟩ with hemb
  set T : SimpleGraph (Site d) := SimpleGraph.map emb Flc2Witness.starG with hT
  have hTac : T.IsAcyclic := spc_map_acyclic Flc2Witness.starG_isTree.isAcyclic emb
  have hTadj : ∀ i j : Fin 4, T.Adj (lab i) (lab j) ↔ Flc2Witness.starG.Adj i j := by
    intro i j; rw [hT, SimpleGraph.map_adj]
    constructor
    · rintro ⟨p, q, hpq, h1, h2⟩; exact (hlabinj h1) ▸ (hlabinj h2) ▸ hpq
    · intro h; exact ⟨i, j, h, rfl, rfl⟩
  have hstar : ∀ i : Fin 3, Flc2Witness.starG.Adj 0 i.succ := by
    intro i; rw [Flc2Witness.starG, fromRel_adj]
    refine ⟨(Fin.succ_ne_zero i).symm, ?_⟩
    left; rw [Flc2Witness.starE]; left; exact ⟨rfl, Fin.succ_ne_zero i⟩
  have hlabsucc : ∀ i : Fin 3, lab i.succ = a i := by intro i; fin_cases i <;> rfl
  have hTxai : ∀ i : Fin 3, T.Adj x (a i) := by
    intro i
    have := (hTadj 0 i.succ).mpr (hstar i)
    rwa [show lab 0 = x from rfl, hlabsucc i] at this
  set B : Set (Site d) := {a 0, a 1, a 2} with hB
  have hai_in_B : ∀ i : Fin 3, a i ∈ B := by intro i; fin_cases i <;> simp [hB]
  
  have hpathij : ∀ i j : Fin 3, i ≠ j →
      ∃ p : T.Walk (a i) (a j), p.IsPath ∧ x ∈ p.support ∧ a i ∈ p.support ∧ a j ∈ p.support := by
    intro i j hij
    refine ⟨Walk.cons (hTxai i).symm (Walk.cons (hTxai j) Walk.nil), ?_, by simp, by simp, by simp⟩
    rw [SimpleGraph.Walk.isPath_def]
    change List.Nodup [a i, x, a j]
    have haij : a i ≠ a j := fun h => hij (hainj h)
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false,
      not_or, and_true]
    exact ⟨⟨hxne i, haij⟩, (hxne j).symm, not_false⟩
  have honB_path : ∀ i j : Fin 3, i ≠ j → ∀ v, (v = a i ∨ v = x ∨ v = a j) →
      spc_OnBPath T B v := by
    intro i j hij v hv
    obtain ⟨p, hp, hxs, his, hjs⟩ := hpathij i j hij
    refine ⟨a i, a j, hai_in_B i, hai_in_B j, fun h => hij (hainj h), p, hp, ?_⟩
    rcases hv with rfl | rfl | rfl
    · exact his
    · exact hxs
    · exact hjs
  have honB_x : spc_OnBPath T B x := honB_path 0 1 (by decide) x (Or.inr (Or.inl rfl))
  have honB_ai : ∀ i : Fin 3, spc_OnBPath T B (a i) := by
    intro i
    fin_cases i
    · exact honB_path 0 1 (by decide) (a 0) (Or.inl rfl)
    · exact honB_path 1 0 (by decide) (a 1) (Or.inl rfl)
    · exact honB_path 2 0 (by decide) (a 2) (Or.inl rfl)
  refine ⟨{x, a 0, a 1, a 2}, T, by rw [hT]; infer_instance, B, fun _ => a, hTac, ?_, ?_, ?_,
    ⟨x, honB_x⟩, ?_⟩
  · 
    intro u v huv
    rw [hT, SimpleGraph.map_adj] at huv
    obtain ⟨p, q, hpq, rfl, rfl⟩ := huv
    rw [Flc2Witness.starG, fromRel_adj] at hpq
    obtain ⟨hpqne, hor⟩ := hpq
    change (openSubgraph d ω).Adj (lab p) (lab q)
    fin_cases p <;> fin_cases q <;> simp only [hlab] <;>
      first
        | (exfalso; revert hor; simp only [Flc2Witness.starE]; decide)
        | exact hadj 0 | exact hadj 1 | exact hadj 2
        | exact (hadj 0).symm | exact (hadj 1).symm | exact (hadj 2).symm
  · 
    intro u v huv
    rw [hT, SimpleGraph.map_adj] at huv
    obtain ⟨p, q, hpq, rfl, rfl⟩ := huv
    fin_cases p <;>
      simp only [Finset.mem_insert, Finset.mem_singleton,
        show (emb : Fin 4 → Site d) = lab from rfl] <;>
      first
        | (left; rfl) | (right; left; rfl) | (right; right; left; rfl) | (right; right; right; rfl)
  · 
    rw [hB]; intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact habdry 0
    · exact habdry 1
    · exact habdry 2
  · 
    intro y hybox htri
    have hyx : y = x := hsingle y hybox htri; subst hyx
    refine ⟨honB_x, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · exact fun h => (by decide : (0 : Fin 3) ≠ 1) (hainj h)
    · exact fun h => (by decide : (0 : Fin 3) ≠ 2) (hainj h)
    · exact fun h => (by decide : (1 : Fin 3) ≠ 2) (hainj h)
    · intro i; exact ⟨hTxai i, honB_ai i⟩
    · exact hsep

end Percolation

end StatMech
