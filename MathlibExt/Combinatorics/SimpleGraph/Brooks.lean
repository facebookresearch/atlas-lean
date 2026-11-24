/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

@[expose] public section

section
namespace MathlibExt.Combinatorics.SimpleGraph.BrooksWanted

/-!
# Brooks' theorem
-/

open Finset

private def IsProperOn {V : Type*} {k : ℕ} (G : SimpleGraph V) (f : V → Fin k) (W : Finset V) :
    Prop :=
  ∀ a ∈ W, ∀ b ∈ W, G.Adj a b → f a ≠ f b

/-- `LinkedOn G W` means every nontrivial cut of `W` is crossed by an edge. -/
private def LinkedOn {V : Type*} (G : SimpleGraph V) (W : Finset V) : Prop :=
  ∀ S : Finset V, S ⊆ W → S.Nonempty →
    (∃ t ∈ W, t ∉ S) → ∃ s ∈ S, ∃ t ∈ W, t ∉ S ∧ G.Adj s t

private theorem exists_extend_coloring_of_forall_exists_low {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (P U : Finset V) (hdisj : Disjoint P U) (c : V → Fin k)
    (hproper : IsProperOn G c P)
    (H : ∀ T : Finset V, T ⊆ U → T.Nonempty →
      ∃ v ∈ T, #((G.neighborFinset v ∩ P).image c) + #(G.neighborFinset v ∩ T) < k) :
    ∃ f : V → Fin k, (∀ x ∈ P, f x = c x) ∧ IsProperOn G f (P ∪ U) := by
  induction U using Finset.strongInduction generalizing P c with
  | _ U ih =>
    by_cases hU : U = ∅
    · subst hU
      exact ⟨c, fun _ _ => rfl, by simpa using hproper⟩
    · have hUne : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hU
      obtain ⟨v, hvU, hbound⟩ := H U Finset.Subset.rfl hUne
      have herv_sub : U.erase v ⊂ U :=
        Finset.erase_ssubset hvU
      have hdisj' : Disjoint P (U.erase v) :=
        Disjoint.mono_right (Finset.erase_subset _ _) hdisj
      have H' : ∀ T : Finset V, T ⊆ U.erase v → T.Nonempty →
          ∃ w ∈ T, #((G.neighborFinset w ∩ P).image c) + #(G.neighborFinset w ∩ T) < k := by
        intro T hT hTne
        obtain ⟨w, hwT, hw⟩ := H T (Finset.Subset.trans hT (Finset.erase_subset _ _)) hTne
        exact ⟨w, hwT, hw⟩
      obtain ⟨f', hf'eq, hf'proper⟩ := ih (U.erase v) herv_sub P hdisj' c hproper H'
      have hvN : v ∉ G.neighborFinset v := by
        rw [SimpleGraph.mem_neighborFinset]
        exact SimpleGraph.irrefl G
      have hvP : v ∉ P := by
        exact (Finset.disjoint_right.mp hdisj) hvU
      set F : Finset (Fin k) := (G.neighborFinset v ∩ (P ∪ U.erase v)).image f' with hF
      have hFbound : #F < k := by
        have hsub : G.neighborFinset v ∩ (P ∪ U.erase v) ⊆
            (G.neighborFinset v ∩ P) ∪ (G.neighborFinset v ∩ U.erase v) := by
          intro x hx
          simp only [Finset.mem_inter, Finset.mem_union] at hx ⊢
          obtain ⟨hxN, hxPU⟩ := hx
          rcases hxPU with hP | hUe
          · exact Or.inl ⟨hxN, hP⟩
          · exact Or.inr ⟨hxN, hUe⟩
        have hcard1 : #((G.neighborFinset v ∩ (P ∪ U.erase v)).image f') ≤
            #((G.neighborFinset v ∩ P).image f') +
                #((G.neighborFinset v ∩ U.erase v).image f') := by
          calc #((G.neighborFinset v ∩ (P ∪ U.erase v)).image f')
              ≤ #(((G.neighborFinset v ∩ P) ∪ (G.neighborFinset v ∩ U.erase v)).image f') :=
                Finset.card_le_card (Finset.image_subset_image hsub)
            _ ≤ #((G.neighborFinset v ∩ P).image f') +
                #((G.neighborFinset v ∩ U.erase v).image f') := by
                rw [Finset.image_union]
                exact Finset.card_union_le _ _
        have himgP : (G.neighborFinset v ∩ P).image f' = (G.neighborFinset v ∩ P).image c := by
          apply Finset.image_congr
          intro x hx
          exact hf'eq x (Finset.mem_inter.mp hx).2
        have hinter : G.neighborFinset v ∩ U.erase v = G.neighborFinset v ∩ U := by
          ext x
          simp only [Finset.mem_inter, Finset.mem_erase]
          constructor
          · rintro ⟨hxN, _, hxU⟩
            exact ⟨hxN, hxU⟩
          · rintro ⟨hxN, hxU⟩
            refine ⟨hxN, ?_, hxU⟩
            intro hxveq
            subst hxveq
            exact absurd hxN hvN
        rw [himgP, hinter] at hcard1
        have hcard2 : #((G.neighborFinset v ∩ U).image f') ≤ #(G.neighborFinset v ∩ U) :=
          Finset.card_image_le
        rw [hF]
        omega
      have huniv : #(Finset.univ : Finset (Fin k)) = k := by
        rw [Finset.card_univ, Fintype.card_fin]
      obtain ⟨a, _, haF⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := F) (t := Finset.univ)
          (by omega)
      refine ⟨Function.update f' v a, ?_, ?_⟩
      · intro x hxP
        have hxnev : x ≠ v := by
          intro hxv
          subst hxv
          exact absurd hxP hvP
        exact ((Function.update_of_ne hxnev a f').trans (hf'eq x hxP))
      · intro x hxPU y hyPU hadj
        simp only [Finset.mem_union] at hxPU hyPU
        by_cases hxv : x = v
        · -- x = v
          rw [hxv] at hadj ⊢
          by_cases hyv : y = v
          · rw [hyv] at hadj
            exact absurd hadj (SimpleGraph.irrefl G)
          · -- x = v, y ≠ v
            have hfx : (Function.update f' v a) v = a := Function.update_self v a f'
            have hfy : (Function.update f' v a) y = f' y := Function.update_of_ne hyv a f'
            rw [hfx, hfy]
            intro heq
            apply haF
            rw [hF, Finset.mem_image]
            have hyN : y ∈ G.neighborFinset v := by
              simp only [SimpleGraph.mem_neighborFinset]
              exact hadj
            have hymem : y ∈ P ∪ U.erase v := by
              rcases hyPU with hP | hUmem
              · exact Finset.mem_union_left _ hP
              · have : y ∈ U.erase v := Finset.mem_erase.mpr ⟨hyv, hUmem⟩
                exact Finset.mem_union_right _ this
            exact ⟨y, Finset.mem_inter.mpr ⟨hyN, hymem⟩, heq.symm⟩
        · -- x ≠ v
          by_cases hyv : y = v
          · rw [hyv] at hadj ⊢
            have hfx : (Function.update f' v a) x = f' x := Function.update_of_ne hxv a f'
            have hfy : (Function.update f' v a) v = a := Function.update_self v a f'
            rw [hfx, hfy]
            intro heq
            apply haF
            rw [hF, Finset.mem_image]
            have hxN : x ∈ G.neighborFinset v := by
              simp only [SimpleGraph.mem_neighborFinset]
              exact hadj.symm
            have hxmem : x ∈ P ∪ U.erase v := by
              rcases hxPU with hP | hUmem
              · exact Finset.mem_union_left _ hP
              · have : x ∈ U.erase v := Finset.mem_erase.mpr ⟨hxv, hUmem⟩
                exact Finset.mem_union_right _ this
            exact ⟨x, Finset.mem_inter.mpr ⟨hxN, hxmem⟩, heq⟩
          · have hfx : (Function.update f' v a) x = f' x := Function.update_of_ne hxv a f'
            have hfy : (Function.update f' v a) y = f' y := Function.update_of_ne hyv a f'
            rw [hfx, hfy]
            have hx' : x ∈ P ∪ U.erase v := by
              rcases hxPU with hP | hUmem
              · exact Finset.mem_union_left _ hP
              · have : x ∈ U.erase v := Finset.mem_erase.mpr ⟨hxv, hUmem⟩
                exact Finset.mem_union_right _ this
            have hy' : y ∈ P ∪ U.erase v := by
              rcases hyPU with hP | hUmem
              · exact Finset.mem_union_left _ hP
              · have : y ∈ U.erase v := Finset.mem_erase.mpr ⟨hyv, hUmem⟩
                exact Finset.mem_union_right _ this
            exact hf'proper x hx' y hy' hadj

private theorem linkedOn_univ_of_connected {V : Type*} [Fintype V]
    (G : SimpleGraph V)
    (hconn : G.Connected) : LinkedOn G Finset.univ := by
  classical
  intro S hS hne hcomp
  obtain ⟨s0, hs0⟩ := hne
  obtain ⟨t0, _, ht0⟩ := hcomp
  obtain ⟨p⟩ := hconn.preconnected s0 t0
  obtain ⟨d, hdarts, hd1, hd2⟩ :=
    SimpleGraph.Walk.exists_boundary_dart p (↑S : Set V) hs0 ht0
  have hadj : G.Adj d.toProd.1 d.toProd.2 := d.adj
  have h1 : d.toProd.1 ∈ S := hd1
  have h2 : d.toProd.2 ∉ S := hd2
  have h2U : d.toProd.2 ∈ (Finset.univ : Finset V) := Finset.mem_univ _
  exact ⟨d.toProd.1, h1, d.toProd.2, h2U, h2, hadj⟩

private theorem exists_adj_adj_not_adj_of_linkedOn {V : Type*} [Fintype V]
    (G : SimpleGraph V)
    (hL : LinkedOn G Finset.univ) {a b : V} (hne : a ≠ b) (hnadj : ¬G.Adj a b) :
    ∃ s t : V, G.Adj a s ∧ G.Adj s t ∧ t ≠ a ∧ ¬G.Adj a t := by
  classical
  set T : Finset V := insert a (G.neighborFinset a) with hT
  have hbT : b ∉ T := by
    simp only [hT, Finset.mem_insert, SimpleGraph.mem_neighborFinset]
    rintro (rfl | h)
    · exact hne rfl
    · exact hnadj h
  have hTsub : T ⊆ Finset.univ := Finset.subset_univ _
  have hTne : T.Nonempty := ⟨a, Finset.mem_insert_self a _⟩
  have hcomp : ∃ t ∈ (Finset.univ : Finset V), t ∉ T := ⟨b, Finset.mem_univ b, hbT⟩
  obtain ⟨s, hsT, t, _, htT, hadj⟩ := hL T hTsub hTne hcomp
  simp only [hT, Finset.mem_insert, SimpleGraph.mem_neighborFinset] at hsT
  have htT' : t ≠ a ∧ ¬G.Adj a t := by
    simp only [hT, Finset.mem_insert, SimpleGraph.mem_neighborFinset] at htT
    push Not at htT
    exact htT
  obtain ⟨htne, htN⟩ := htT'
  rcases hsT with rfl | hsN
  · exact absurd hadj htN
  · exact ⟨s, t, hsN, hadj, htne, htN⟩

private theorem exists_properOn_of_linkedOn_univ {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : 0 < k) (hL : LinkedOn G Finset.univ)
    (hdeg : ∀ v, G.degree v ≤ k) (U : Finset V)
    (hU : U ≠ Finset.univ ∨ ∃ r, G.degree r < k) :
    ∃ f : V → Fin k, IsProperOn G f U := by
  classical
  -- apply N2 with P = ∅
  have hdisj : Disjoint (∅ : Finset V) U := by simp
  have hproper : IsProperOn G (fun _ => (⟨0, hk⟩ : Fin k)) (∅ : Finset V) := by
    intro a ha
    simp at ha
  have H : ∀ T : Finset V, T ⊆ U → T.Nonempty →
      ∃ v ∈ T, #(((G.neighborFinset v ∩ ∅).image (fun _ => (⟨0, hk⟩ : Fin k)))) +
        #(G.neighborFinset v ∩ T) < k := by
    intro T hTU hTne
    have him0 : ∀ v : V, #(((G.neighborFinset v ∩ ∅).image (fun _ => (⟨0, hk⟩ : Fin k)))) = 0 := by
      intro v
      rw [Finset.inter_empty, Finset.image_empty, Finset.card_empty]
    by_cases hT : T = Finset.univ
    · -- T = univ: use low-degree vertex
      have hUuniv : U = Finset.univ :=
        Subset.antisymm (Finset.subset_univ _) (hT ▸ hTU)
      rcases hU with hne | hex
      · exact absurd hUuniv hne
      · obtain ⟨r, hr⟩ := hex
        have hrT : r ∈ T := hT.symm ▸ Finset.mem_univ r
        refine ⟨r, hrT, ?_⟩
        rw [him0]
        have hinter : G.neighborFinset r ∩ T = G.neighborFinset r := by
          rw [hT, Finset.inter_univ]
        rw [hinter, SimpleGraph.card_neighborFinset_eq_degree]
        omega
    · -- T ≠ univ: crossing edge gives strict subset
      have hTsub : T ⊂ Finset.univ :=
        Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hT⟩
      obtain ⟨t, htU, htT⟩ := Finset.exists_of_ssubset hTsub
      obtain ⟨s, hsT, u, _, huT, hadj⟩ := hL T (Finset.subset_univ _) hTne ⟨t, htU, htT⟩
      refine ⟨s, hsT, ?_⟩
      rw [him0]
      -- N(s) ∩ T ⊂ N(s)
      have hmem : u ∈ G.neighborFinset s := by
        rw [SimpleGraph.mem_neighborFinset]
        exact hadj
      have hssub : G.neighborFinset s ∩ T ⊂ G.neighborFinset s := by
        apply Finset.ssubset_iff_subset_ne.mpr
        constructor
        · exact Finset.inter_subset_left
        · intro heq
          apply huT
          have : u ∈ G.neighborFinset s ∩ T := heq.symm ▸ hmem
          exact (Finset.mem_inter.mp this).2
      have hlt : #(G.neighborFinset s ∩ T) < #(G.neighborFinset s) :=
        Finset.card_lt_card hssub
      rw [SimpleGraph.card_neighborFinset_eq_degree] at hlt
      have hle := hdeg s
      omega
  obtain ⟨f, _, hf⟩ := exists_extend_coloring_of_forall_exists_low G k ∅ U hdisj _ hproper H
  rw [Finset.empty_union] at hf
  exact ⟨f, hf⟩

private theorem exists_coloring_of_cut_vertex {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : 0 < k) (hL : LinkedOn G Finset.univ)
    (hdeg : ∀ v, G.degree v ≤ k) (z : V) (S : Finset V)
    (hSsub : S ⊆ Finset.univ.erase z) (hSne : S.Nonempty)
    (hcomp : ∃ t ∈ Finset.univ.erase z, t ∉ S)
    (hnoedge : ∀ s ∈ S, ∀ t ∈ Finset.univ.erase z, t ∉ S → ¬G.Adj s t) :
    ∃ f : V → Fin k, IsProperOn G f Finset.univ := by
  classical
  -- z ∉ S
  have hzS : z ∉ S := by
    intro hz
    have hz' : z ∈ Finset.univ.erase z := hSsub hz
    simp [Finset.mem_erase] at hz'
  -- A and B are proper subsets
  set A : Finset V := insert z S with hA
  set B : Finset V := Finset.univ \ S with hB
  have hAne : A ≠ Finset.univ := by
    obtain ⟨t, htE, htS⟩ := hcomp
    intro hcon
    apply htS
    have htU : t ∈ (Finset.univ : Finset V) := Finset.mem_univ t
    rw [← hcon] at htU
    simp only [hA, mem_insert] at htU
    rcases htU with rfl | hmem
    · simp [Finset.mem_erase] at htE
    · exact hmem
  have hBne : B ≠ Finset.univ := by
    obtain ⟨s0, hs0⟩ := hSne
    intro hcon
    have hs0U : s0 ∈ (Finset.univ : Finset V) := Finset.mem_univ s0
    have hs0B : s0 ∈ B := hcon ▸ hs0U
    simp only [hB, mem_sdiff, mem_univ, true_and] at hs0B
    exact hs0B hs0
  obtain ⟨f1, hf1⟩ := exists_properOn_of_linkedOn_univ G k hk hL hdeg A (Or.inl hAne)
  obtain ⟨f2, hf2⟩ := exists_properOn_of_linkedOn_univ G k hk hL hdeg B (Or.inl hBne)
  -- swap colors at z
  let σ := Equiv.swap (f2 z) (f1 z)
  have hσ : σ (f2 z) = f1 z := Equiv.swap_apply_left _ _
  have hσinj := Equiv.injective σ
  -- combined coloring
  refine ⟨fun v => if v ∈ S then f1 v else σ (f2 v), ?_⟩
  intro a _ b _ hadj
  by_cases haS : a ∈ S <;> by_cases hbS : b ∈ S
  · -- both in S: use f1
    have hfa : (if a ∈ S then f1 a else σ (f2 a)) = f1 a := by simp [haS]
    have hfb : (if b ∈ S then f1 b else σ (f2 b)) = f1 b := by simp [hbS]
    change (if a ∈ S then f1 a else σ (f2 a)) ≠ (if b ∈ S then f1 b else σ (f2 b))
    rw [hfa, hfb]
    have haA : a ∈ A := Finset.mem_insert_of_mem haS
    have hbA : b ∈ A := Finset.mem_insert_of_mem hbS
    exact hf1 a haA b hbA hadj
  · -- a ∈ S, b ∉ S: force b = z
    by_cases hbz : b = z
    · have hfa : (if a ∈ S then f1 a else σ (f2 a)) = f1 a := by simp [haS]
      have hfb : (if b ∈ S then f1 b else σ (f2 b)) = σ (f2 b) := by simp [hbS]
      change (if a ∈ S then f1 a else σ (f2 a)) ≠ (if b ∈ S then f1 b else σ (f2 b))
      rw [hfa, hfb, hbz, hσ]
      have haA : a ∈ A := Finset.mem_insert_of_mem haS
      have hzA : z ∈ A := Finset.mem_insert_self z S
      have hadj' : G.Adj a z := hbz ▸ hadj
      exact hf1 a haA z hzA hadj'
    · exfalso
      have hbE : b ∈ Finset.univ.erase z := Finset.mem_erase.mpr ⟨hbz, Finset.mem_univ b⟩
      exact hnoedge a haS b hbE hbS hadj
  · -- a ∉ S, b ∈ S: force a = z
    by_cases haz : a = z
    · have hfa : (if a ∈ S then f1 a else σ (f2 a)) = σ (f2 a) := by simp [haS]
      have hfb : (if b ∈ S then f1 b else σ (f2 b)) = f1 b := by simp [hbS]
      change (if a ∈ S then f1 a else σ (f2 a)) ≠ (if b ∈ S then f1 b else σ (f2 b))
      rw [hfa, hfb, haz, hσ]
      have hbA : b ∈ A := Finset.mem_insert_of_mem hbS
      have hzA : z ∈ A := Finset.mem_insert_self z S
      have hadj' : G.Adj z b := haz ▸ hadj
      exact hf1 z hzA b hbA hadj'
    · exfalso
      have haE : a ∈ Finset.univ.erase z := Finset.mem_erase.mpr ⟨haz, Finset.mem_univ a⟩
      exact hnoedge b hbS a haE haS hadj.symm
  · -- neither in S: use f2 and injectivity
    have hfa : (if a ∈ S then f1 a else σ (f2 a)) = σ (f2 a) := by simp [haS]
    have hfb : (if b ∈ S then f1 b else σ (f2 b)) = σ (f2 b) := by simp [hbS]
    change (if a ∈ S then f1 a else σ (f2 a)) ≠ (if b ∈ S then f1 b else σ (f2 b))
    rw [hfa, hfb]
    have haB : a ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, haS⟩
    have hbB : b ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ b, hbS⟩
    have hne : f2 a ≠ f2 b := hf2 a haB b hbB hadj
    exact fun h => hne (hσinj h)

private theorem exists_adj_of_closed_piece {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    {x y : V} {D : Finset V} (hxy : x ≠ y)
    (hDne : D.Nonempty) (hxD : x ∉ D) (hyD : y ∉ D)
    (hclosed : ∀ d ∈ D, ∀ z : V, G.Adj d z → z ∈ D ∨ z = x ∨ z = y)
    (hL : LinkedOn G (Finset.univ.erase y)) :
    ∃ d ∈ D, G.Adj x d := by
  classical
  have hDsub : D ⊆ Finset.univ.erase y := by
    intro d hd
    exact Finset.mem_erase.mpr ⟨fun h => hyD (h ▸ hd), Finset.mem_univ d⟩
  have hxE : x ∈ Finset.univ.erase y :=
    Finset.mem_erase.mpr ⟨hxy, Finset.mem_univ x⟩
  obtain ⟨d, hdD, t, htE, htD, hadj⟩ := hL D hDsub hDne ⟨x, hxE, hxD⟩
  have htne : t ≠ y := (Finset.mem_erase.mp htE).1
  rcases hclosed d hdD t hadj with hTD | rfl | rfl
  · exact absurd hTD htD
  · exact ⟨d, hdD, hadj.symm⟩
  · exact absurd rfl htne

private theorem subset_of_cut_avoiding {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    {x y u : V} {D : Finset V} (hxy : x ≠ y)
    (_hxD : x ∉ D) (_hyD : y ∉ D)
    (hclosed : ∀ d ∈ D, ∀ z : V, G.Adj d z → z ∈ D ∨ z = x ∨ z = y)
    (huD : u ∈ D)
    (hLx : LinkedOn G (Finset.univ.erase x))
    (S : Finset V) (hSsub : S ⊆ Finset.univ \ {x, u}) (hyS : y ∉ S)
    (hnoedge : ∀ s ∈ S, ∀ t ∈ (Finset.univ \ {x, u}) \ S, ¬ G.Adj s t) :
    S ⊆ D := by
  classical
  by_contra hcon
  obtain ⟨s0, hs0S, hs0D⟩ := Finset.not_subset.mp hcon
  set S' : Finset V := S.filter (· ∉ D) with hS'
  have hs0S' : s0 ∈ S' := Finset.mem_filter.mpr ⟨hs0S, hs0D⟩
  have hS'ne : S'.Nonempty := ⟨s0, hs0S'⟩
  have hS'S : S' ⊆ S := Finset.filter_subset _ _
  have hS'sub : S' ⊆ Finset.univ.erase x := by
    intro s hs
    have hsS : s ∈ S := hS'S hs
    have hsx : s ≠ x := by
      intro h
      have hsW : s ∈ Finset.univ \ {x, u} := hSsub hsS
      rw [h] at hsW
      simp at hsW
    exact Finset.mem_erase.mpr ⟨hsx, Finset.mem_univ s⟩
  have hyS' : ∃ t ∈ Finset.univ.erase x, t ∉ S' := by
    have hyx : y ≠ x := fun h => hxy h.symm
    have hyE : y ∈ Finset.univ.erase x := Finset.mem_erase.mpr ⟨hyx, Finset.mem_univ y⟩
    refine ⟨y, hyE, ?_⟩
    intro hy
    have hyS0 : y ∈ S := hS'S hy
    exact hyS hyS0
  obtain ⟨s, hsS', t, htE, htS', hadj⟩ := hLx S' hS'sub hS'ne hyS'
  have hsS : s ∈ S := hS'S hsS'
  have hsD : s ∉ D := (Finset.mem_filter.mp hsS').2
  have htne_x : t ≠ x := (Finset.mem_erase.mp htE).1
  by_cases htD : t ∈ D
  · have hmem : G.Adj t s := hadj.symm
    rcases hclosed t htD s hmem with hSD | hSx | hSy
    · exact hsD hSD
    · have hsW : s ∈ Finset.univ \ {x, u} := hSsub hsS
      rw [hSx] at hsW
      simp at hsW
    · rw [hSy] at hsS
      exact hyS hsS
  · have htS : t ∉ S := by
      intro ht
      have : t ∈ S' := Finset.mem_filter.mpr ⟨ht, htD⟩
      exact htS' this
    have htu : t ≠ u := by
      intro htu
      subst htu
      exact htD huD
    have htW : t ∈ Finset.univ \ {x, u} := by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, not_or]
      exact ⟨htne_x, htu⟩
    have htC : t ∈ (Finset.univ \ {x, u}) \ S := Finset.mem_sdiff.mpr ⟨htW, htS⟩
    exact hnoedge s hsS t htC hadj

private theorem exists_coloring_of_lovasz_triple {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hdeg : ∀ v, G.degree v ≤ k)
    {v u w : V} (hvu : G.Adj v u) (hvw : G.Adj v w) (huw_ne : u ≠ w)
    (hnadj : ¬ G.Adj u w)
    (hL : LinkedOn G (Finset.univ \ {u, w})) :
    ∃ f : V → Fin k, IsProperOn G f Finset.univ := by
  classical
  have huN : u ∈ G.neighborFinset v := by
    rw [SimpleGraph.mem_neighborFinset]; exact hvu
  have hwN : w ∈ G.neighborFinset v := by
    rw [SimpleGraph.mem_neighborFinset]; exact hvw
  have hPsub : ({u, w} : Finset V) ⊆ G.neighborFinset v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact huN
    · exact hwN
  have hpair : ({u, w} : Finset V).card = 2 := Finset.card_pair huw_ne
  have h2le : 2 ≤ G.degree v := by
    have h := Finset.card_le_card hPsub
    rw [hpair, SimpleGraph.card_neighborFinset_eq_degree] at h
    exact h
  have hk2 : 2 ≤ k := le_trans h2le (hdeg v)
  have hk0 : 0 < k := by omega
  set P : Finset V := {u, w} with hP
  set c : V → Fin k := fun _ => ⟨0, hk0⟩ with hc
  have hproper : IsProperOn G c P := by
    intro a ha b hb hadj
    simp only [hP, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd hadj (SimpleGraph.irrefl G)
    · exact absurd hadj hnadj
    · exact absurd hadj.symm hnadj
    · exact absurd hadj (SimpleGraph.irrefl G)
  set U : Finset V := Finset.univ \ {u, w} with hU
  have hdisj : Disjoint P U := by
    rw [hP, hU]
    exact Finset.disjoint_sdiff
  have hunion : P ∪ U = Finset.univ := by
    rw [hP, hU]
    exact Finset.union_sdiff_of_subset (Finset.subset_univ _)
  have hPUemp : Disjoint P U := hdisj
  have H : ∀ T : Finset V, T ⊆ U → T.Nonempty →
      ∃ s ∈ T, #((G.neighborFinset s ∩ P).image c) + #(G.neighborFinset s ∩ T) < k := by
    intro T hTU hTne
    have hTU' : ∀ x ∈ T, x ∉ P := by
      intro x hxT hxP
      have hxU : x ∈ U := hTU hxT
      exact (Finset.disjoint_left.mp hPUemp) hxP hxU
    by_cases hvT : v ∈ T
    · refine ⟨v, hvT, ?_⟩
      have himg : #((G.neighborFinset v ∩ P).image c) ≤ 1 := by
        have hsub1 : (G.neighborFinset v ∩ P).image c ⊆ ({⟨0, hk0⟩} : Finset (Fin k)) := by
          intro y hy
          obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
          exact Finset.mem_singleton_self _
        have h := Finset.card_le_card hsub1
        rwa [Finset.card_singleton] at h
      have hd : Disjoint (G.neighborFinset v ∩ T) P := by
        rw [Finset.disjoint_left]
        intro x hxT hxP
        exact hTU' x (Finset.mem_inter.mp hxT).2 hxP
      have hunion_sub : (G.neighborFinset v ∩ T) ∪ P ⊆ G.neighborFinset v := by
        intro x hx
        simp only [Finset.mem_union, Finset.mem_inter] at hx
        rcases hx with ⟨hxN, _⟩ | hxP
        · exact hxN
        · exact hPsub hxP
      have hcard := Finset.card_le_card hunion_sub
      rw [Finset.card_union_of_disjoint hd, hP, hpair,
        SimpleGraph.card_neighborFinset_eq_degree] at hcard
      have hle := hdeg v
      omega
    · have hvU : v ∈ U := by
        rw [hU]
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hvu.ne, hvw.ne⟩
      have hTeq : T ≠ U := by
        intro hcon
        subst hcon
        exact hvT hvU
      have hss : T ⊂ U := Finset.ssubset_iff_subset_ne.mpr ⟨hTU, hTeq⟩
      obtain ⟨t0, ht0U, ht0T⟩ := Finset.exists_of_ssubset hss
      obtain ⟨s, hsT, t2, ht2U, ht2T, hadj⟩ := hL T hTU hTne ⟨t0, ht0U, ht0T⟩
      refine ⟨s, hsT, ?_⟩
      have himg_le : #((G.neighborFinset s ∩ P).image c) ≤ #(G.neighborFinset s ∩ P) :=
        Finset.card_image_le
      have ht2N : t2 ∈ G.neighborFinset s := by
        rw [SimpleGraph.mem_neighborFinset]; exact hadj
      have d12 : Disjoint (G.neighborFinset s ∩ P) (G.neighborFinset s ∩ T) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        have hxP : x ∈ P := (Finset.mem_inter.mp hx1).2
        have hxT : x ∈ T := (Finset.mem_inter.mp hx2).2
        exact hTU' x hxT hxP
      have d13 : Disjoint (G.neighborFinset s ∩ P) ({t2} : Finset V) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        have hxP : x ∈ P := (Finset.mem_inter.mp hx1).2
        have hxt : x = t2 := Finset.mem_singleton.mp hx2
        have ht2U' : t2 ∈ U := ht2U
        rw [← hxt] at ht2U'
        exact (Finset.disjoint_left.mp hPUemp) hxP ht2U'
      have d23 : Disjoint (G.neighborFinset s ∩ T) ({t2} : Finset V) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        have hxT : x ∈ T := (Finset.mem_inter.mp hx1).2
        have hxt : x = t2 := Finset.mem_singleton.mp hx2
        rw [hxt] at hxT
        exact ht2T hxT
      have hunion_sub : ((G.neighborFinset s ∩ P) ∪ (G.neighborFinset s ∩ T)) ∪ ({t2} : Finset V)
          ⊆ G.neighborFinset s := by
        intro x hx
        simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_singleton] at hx
        rcases hx with (⟨hxN, _⟩ | ⟨hxN, _⟩) | rfl
        · exact hxN
        · exact hxN
        · exact ht2N
      have hcard := Finset.card_le_card hunion_sub
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨d13, d23⟩),
        Finset.card_union_of_disjoint d12, Finset.card_singleton,
        SimpleGraph.card_neighborFinset_eq_degree] at hcard
      have hle := hdeg s
      omega
  obtain ⟨f, _, hf⟩ := exists_extend_coloring_of_forall_exists_low G k P U hdisj c hproper H
  rw [hunion] at hf
  exact ⟨f, hf⟩

private theorem linkedOn_compl_pair_of_nonseparating {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    {v y u w : V} (hvy : v ≠ y)
    {S R : Finset V} (hSsub : S ⊆ Finset.univ \ {v, y})
    (hR : R = (Finset.univ \ {v, y}) \ S)
    (hnoedge : ∀ s ∈ S, ∀ t ∈ R, ¬ G.Adj s t)
    (huS : u ∈ S) (hwR : w ∈ R)
    (hLvu : LinkedOn G (Finset.univ \ {v, u}))
    (hLvw : LinkedOn G (Finset.univ \ {v, w}))
    {n0 : V} (hn0 : G.Adj v n0) (hn0u : n0 ≠ u) (hn0w : n0 ≠ w) :
    LinkedOn G (Finset.univ \ {u, w}) := by
  classical
  set W : Finset V := Finset.univ \ {u, w} with hW
  have hu_ne : u ≠ v ∧ u ≠ y := by
    have h2 := (Finset.mem_sdiff.mp (hSsub huS)).2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h2
    exact h2
  have hw_whole : w ∈ Finset.univ \ {v, y} := by
    rw [hR] at hwR
    exact (Finset.mem_sdiff.mp hwR).1
  have hw_ne : w ≠ v ∧ w ≠ y := by
    have h2 := (Finset.mem_sdiff.mp hw_whole).2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h2
    exact h2
  have huw : u ≠ w := by
    intro h
    rw [h] at huS
    rw [hR] at hwR
    exact (Finset.mem_sdiff.mp hwR).2 huS
  have hyu : y ≠ u := hu_ne.2.symm
  have hyw : y ≠ w := hw_ne.2.symm
  have hyv : y ≠ v := hvy.symm
  have hvu : v ≠ u := hu_ne.1.symm
  have hvw : v ≠ w := hw_ne.1.symm
  have hyW : y ∈ W := by
    rw [hW]
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hyu, hyw⟩
  have hyVU : y ∈ Finset.univ \ {v, u} := by
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hyv, hyu⟩
  have hyVW : y ∈ Finset.univ \ {v, w} := by
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hyv, hyw⟩
  have hSRunion : S ∪ R = Finset.univ \ {v, y} := by
    rw [hR]
    exact Finset.union_sdiff_of_subset hSsub
  have side_S : ∀ z ∈ W, z ∈ S → ∀ T : Finset V, T ⊆ W → T.Nonempty →
      z ∈ T → y ∉ T → ∃ s ∈ T, ∃ t ∈ W, t ∉ T ∧ G.Adj s t := by
    intro z hzW hzS T hTW hTne hzT hyT
    have hTSsub : T ∩ S ⊆ Finset.univ \ {v, u} := by
      intro x hx
      obtain ⟨hxT, hxS⟩ := Finset.mem_inter.mp hx
      have hxW : x ∈ W := hTW hxT
      have hxv : x ≠ v := by
        have h := hSsub hxS
        have h2 := (Finset.mem_sdiff.mp h).2
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h2
        exact h2.1
      have hxu : x ≠ u := by
        rw [hW] at hxW
        have h2 := (Finset.mem_sdiff.mp hxW).2
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h2
        exact h2.1
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hxv, hxu⟩
    have hTSne : (T ∩ S).Nonempty := ⟨z, Finset.mem_inter.mpr ⟨hzT, hzS⟩⟩
    have hcompTS : ∃ t ∈ Finset.univ \ {v, u}, t ∉ T ∩ S := by
      refine ⟨y, hyVU, ?_⟩
      intro h
      exact hyT (Finset.mem_inter.mp h).1
    obtain ⟨s, hsTS, t, htVU, htTS, hadj⟩ := hLvu (T ∩ S) hTSsub hTSne hcompTS
    have hsT : s ∈ T := (Finset.mem_inter.mp hsTS).1
    have hsS : s ∈ S := (Finset.mem_inter.mp hsTS).2
    have htR : t ∉ R := fun ht => hnoedge s hsS t ht hadj
    have htne : t ≠ v ∧ t ≠ u := by
      have h := (Finset.mem_sdiff.mp htVU).2
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
      exact h
    by_cases hty : t = y
    · refine ⟨s, hsT, y, hyW, hyT, hty ▸ hadj⟩
    · have htwhole : t ∈ Finset.univ \ {v, y} := by
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ t, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨htne.1, hty⟩
      have htS : t ∈ S := by
        by_contra hcon
        exact htR (by rw [hR]; exact Finset.mem_sdiff.mpr ⟨htwhole, hcon⟩)
      have htT : t ∉ T := fun h => htTS (Finset.mem_inter.mpr ⟨h, htS⟩)
      have htw : t ≠ w := fun h => htR (h ▸ hwR)
      have htW : t ∈ W := by
        rw [hW]
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ t, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨htne.2, htw⟩
      exact ⟨s, hsT, t, htW, htT, hadj⟩
  have side_R : ∀ z ∈ W, z ∈ R → ∀ T : Finset V, T ⊆ W → T.Nonempty →
      z ∈ T → y ∉ T → ∃ s ∈ T, ∃ t ∈ W, t ∉ T ∧ G.Adj s t := by
    intro z hzW hzR T hTW hTne hzT hyT
    have hTRsub : T ∩ R ⊆ Finset.univ \ {v, w} := by
      intro x hx
      obtain ⟨hxT, hxR⟩ := Finset.mem_inter.mp hx
      have hxW : x ∈ W := hTW hxT
      have hxv : x ≠ v := by
        have h : x ∈ Finset.univ \ {v, y} := by
          rw [hR] at hxR
          exact (Finset.mem_sdiff.mp hxR).1
        have h2 := (Finset.mem_sdiff.mp h).2
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h2
        exact h2.1
      have hxw : x ≠ w := by
        rw [hW] at hxW
        have h2 := (Finset.mem_sdiff.mp hxW).2
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h2
        exact h2.2
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hxv, hxw⟩
    have hTRne : (T ∩ R).Nonempty := ⟨z, Finset.mem_inter.mpr ⟨hzT, hzR⟩⟩
    have hcompTR : ∃ t ∈ Finset.univ \ {v, w}, t ∉ T ∩ R := by
      refine ⟨y, hyVW, ?_⟩
      intro h
      exact hyT (Finset.mem_inter.mp h).1
    obtain ⟨s, hsTR, t, htVW, htTR, hadj⟩ := hLvw (T ∩ R) hTRsub hTRne hcompTR
    have hsT : s ∈ T := (Finset.mem_inter.mp hsTR).1
    have hsR : s ∈ R := (Finset.mem_inter.mp hsTR).2
    have htS : t ∉ S := fun ht => hnoedge t ht s hsR hadj.symm
    have htne : t ≠ v ∧ t ≠ w := by
      have h := (Finset.mem_sdiff.mp htVW).2
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
      exact h
    by_cases hty : t = y
    · refine ⟨s, hsT, y, hyW, hyT, hty ▸ hadj⟩
    · have htwhole : t ∈ Finset.univ \ {v, y} := by
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ t, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨htne.1, hty⟩
      have htR : t ∈ R := by
        have hmem : t ∈ S ∪ R := by rw [hSRunion]; exact htwhole
        simp only [Finset.mem_union] at hmem
        rcases hmem with h | h
        · exact absurd h htS
        · exact h
      have htT : t ∉ T := fun h => htTR (Finset.mem_inter.mpr ⟨h, htR⟩)
      have htu : t ≠ u := fun h => htS (h ▸ huS)
      have htW : t ∈ W := by
        rw [hW]
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ t, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨htu, htne.2⟩
      exact ⟨s, hsT, t, htW, htT, hadj⟩
  have main : ∀ T : Finset V, T ⊆ W → T.Nonempty → (∃ t ∈ W, t ∉ T) → y ∉ T →
      ∃ s ∈ T, ∃ t ∈ W, t ∉ T ∧ G.Adj s t := by
    intro T hTW hTne hcomp hyT
    have hn0W : n0 ∈ W := by
      rw [hW]
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ n0, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hn0u, hn0w⟩
    have hn0v : n0 ≠ v := fun h => hn0.ne (h ▸ rfl)
    by_cases hvT : v ∈ T
    · by_cases hTeq : T = {v}
      · have hn0T : n0 ∉ T := by rw [hTeq]; simp [hn0v]
        have hvT' : v ∈ T := by rw [hTeq]; exact Finset.mem_singleton_self v
        exact ⟨v, hvT', n0, hn0W, hn0T, hn0⟩
      · have hex : ∃ z ∈ T, z ≠ v := by
          by_contra hcon
          have hsub : T ⊆ {v} := by
            intro z hz
            simp only [Finset.mem_singleton]
            by_contra hzv
            exact hcon ⟨z, hz, hzv⟩
          have hsup : ({v} : Finset V) ⊆ T := by
            intro x hx
            simp only [Finset.mem_singleton] at hx
            rw [hx]
            exact hvT
          exact hTeq (Finset.Subset.antisymm hsub hsup)
        obtain ⟨z, hzT, hzv⟩ := hex
        have hzW : z ∈ W := hTW hzT
        have hzwhole : z ∈ Finset.univ \ {v, y} := by
          refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, ?_⟩
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          refine ⟨hzv, ?_⟩
          intro hzy
          rw [hzy] at hzT
          exact hyT hzT
        have hmem : z ∈ S ∪ R := by rw [hSRunion]; exact hzwhole
        simp only [Finset.mem_union] at hmem
        rcases hmem with hzS | hzR
        · exact side_S z hzW hzS T hTW hTne hzT hyT
        · exact side_R z hzW hzR T hTW hTne hzT hyT
    · obtain ⟨z, hzT⟩ := hTne
      have hzv : z ≠ v := fun h => hvT (h ▸ hzT)
      have hzW : z ∈ W := hTW hzT
      have hzwhole : z ∈ Finset.univ \ {v, y} := by
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨hzv, ?_⟩
        intro hzy
        rw [hzy] at hzT
        exact hyT hzT
      have hmem : z ∈ S ∪ R := by rw [hSRunion]; exact hzwhole
      simp only [Finset.mem_union] at hmem
      rcases hmem with hzS | hzR
      · exact side_S z hzW hzS T hTW ⟨z, hzT⟩ hzT hyT
      · exact side_R z hzW hzR T hTW ⟨z, hzT⟩ hzT hyT
  intro T hTW hTne hcomp
  by_cases hyT : y ∈ T
  · obtain ⟨t0, ht0W, ht0T⟩ := hcomp
    have hWTsub : W \ T ⊆ W := Finset.sdiff_subset
    have hWTne : (W \ T).Nonempty := ⟨t0, Finset.mem_sdiff.mpr ⟨ht0W, ht0T⟩⟩
    have hyWT : y ∉ W \ T := fun h => (Finset.mem_sdiff.mp h).2 hyT
    obtain ⟨s, hsWT, t, htW, htt, hadj⟩ :=
      main (W \ T) hWTsub hWTne ⟨y, hyW, hyWT⟩ hyWT
    have hsW : s ∈ W := (Finset.mem_sdiff.mp hsWT).1
    have hsT : s ∉ T := (Finset.mem_sdiff.mp hsWT).2
    have htT : t ∈ T := by
      by_contra hcon
      exact htt (Finset.mem_sdiff.mpr ⟨htW, hcon⟩)
    exact ⟨t, htT, s, hsW, hsT, hadj.symm⟩
  · exact main T hTW hTne hcomp hyT

private theorem exists_nonseparating_neighbor {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (h2conn : ∀ z, LinkedOn G (Finset.univ.erase z))
    {x y : V} {D : Finset V} (hxy : x ≠ y)
    (hDne : D.Nonempty) (hxD : x ∉ D) (hyD : y ∉ D)
    (hclosed : ∀ d ∈ D, ∀ z : V, G.Adj d z → z ∈ D ∨ z = x ∨ z = y) :
    ∃ u ∈ D, G.Adj x u ∧ LinkedOn G (Finset.univ \ {x, u}) := by
  classical
  suffices H : ∀ n, ∀ (y : V) (D : Finset V), #D ≤ n → x ≠ y → D.Nonempty →
      x ∉ D → y ∉ D →
      (∀ d ∈ D, ∀ z : V, G.Adj d z → z ∈ D ∨ z = x ∨ z = y) →
      ∃ u ∈ D, G.Adj x u ∧ LinkedOn G (Finset.univ \ {x, u}) by
    exact H (#D) y D le_rfl hxy hDne hxD hyD hclosed
  intro n
  induction n with
  | zero =>
    intro y D hle _hxy hDne _hxD _hyD _hclosed
    have hpos : 0 < #D := Finset.card_pos.mpr hDne
    omega
  | succ n ih =>
    intro y D hle hxy hDne hxD hyD hclosed
    obtain ⟨u, huD, hxu⟩ :=
      exists_adj_of_closed_piece G hxy hDne hxD hyD hclosed (h2conn y)
    by_cases hL : LinkedOn G (Finset.univ \ {x, u})
    · exact ⟨u, huD, hxu, hL⟩
    · simp only [LinkedOn, not_forall, not_exists] at hL
      push Not at hL
      obtain ⟨S, hSsub, hSne, hcomp, hno⟩ := hL
      have huy : u ≠ y := fun h => hyD (h ▸ huD)
      have hyu : y ≠ u := huy.symm
      have hyW : y ∈ Finset.univ \ {x, u} := by
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hxy.symm, hyu⟩
      have huW : u ∉ Finset.univ \ {x, u} := by simp
      have hxW : x ∉ Finset.univ \ {x, u} := by simp
      have huS : u ∉ S := fun h => huW (hSsub h)
      have hxS : x ∉ S := fun h => hxW (hSsub h)
      have hno' : ∀ s ∈ S, ∀ t ∈ (Finset.univ \ {x, u}) \ S, ¬ G.Adj s t := by
        intro s hs t ht
        obtain ⟨htW, htS⟩ := Finset.mem_sdiff.mp ht
        exact hno s hs t htW htS
      have hxu_ne : x ≠ u := by
        intro h
        rw [← h] at huD
        exact hxD huD
      by_cases hyS : y ∈ S
      · set W : Finset V := Finset.univ \ {x, u} with hW
        obtain ⟨t0, ht0W, ht0S⟩ := hcomp
        have hWTne : (W \ S).Nonempty := ⟨t0, Finset.mem_sdiff.mpr ⟨ht0W, ht0S⟩⟩
        have hWTsub : W \ S ⊆ W := Finset.sdiff_subset
        have hyWT : y ∉ W \ S := fun h => (Finset.mem_sdiff.mp h).2 hyS
        have hxWT : x ∉ W \ S := fun h => hxW (by rw [hW] at h ⊢; exact hWTsub h)
        have hnoB : ∀ s ∈ W \ S, ∀ t ∈ W \ (W \ S), ¬ G.Adj s t := by
          intro s hs t ht hadj
          have hsS : s ∉ S := (Finset.mem_sdiff.mp hs).2
          have hsW : s ∈ W := (Finset.mem_sdiff.mp hs).1
          have htW : t ∈ W := (Finset.mem_sdiff.mp ht).1
          have htS : t ∈ S := by
            by_contra hcon
            exact (Finset.mem_sdiff.mp ht).2 (Finset.mem_sdiff.mpr ⟨htW, hcon⟩)
          have hsW' : s ∈ Finset.univ \ {x, u} := by rwa [hW] at hsW
          have htW' : t ∈ Finset.univ \ {x, u} := by rwa [hW] at htW
          exact (hno t htS s hsW' hsS) hadj.symm
        have hsubD : W \ S ⊆ D := by
          have h := subset_of_cut_avoiding G hxy hxD hyD hclosed huD (h2conn x)
            (W \ S) (by rwa [hW] at hWTsub ⊢) hyWT
            (by rwa [hW] at hnoB ⊢)
          exact h
        have huWT : u ∉ W \ S := fun h => huW (by rw [hW] at h ⊢; exact hWTsub h)
        have hssub : W \ S ⊂ D :=
          Finset.ssubset_iff_subset_ne.mpr ⟨hsubD, fun h => huWT (h.symm ▸ huD)⟩
        have hcard : #(W \ S) < #(D) := Finset.card_lt_card hssub
        have hle' : #(W \ S) ≤ n := by omega
        have hclosedB : ∀ d ∈ W \ S, ∀ z : V,
            G.Adj d z → z ∈ W \ S ∨ z = x ∨ z = u := by
          intro d hd z hadj
          by_cases hz : z ∈ W \ S
          · exact Or.inl hz
          · by_cases hzx : z = x
            · exact Or.inr (Or.inl hzx)
            · by_cases hzu : z = u
              · exact Or.inr (Or.inr hzu)
              · exfalso
                by_cases hzW : z ∈ W
                · have hzC : z ∈ W \ (W \ S) := Finset.mem_sdiff.mpr ⟨hzW, hz⟩
                  exact (hnoB d hd z hzC) hadj
                · have hzmem : z ∈ ({x, u} : Finset V) := by
                    by_contra hcon
                    have hzW' : z ∈ W := by
                      rw [hW]
                      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hcon⟩
                    exact hzW hzW'
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hzmem
                  rcases hzmem with h | h
                  · exact absurd h hzx
                  · exact absurd h hzu
        obtain ⟨u', hu', hxu', hL'⟩ := ih u (W \ S) hle' hxu_ne hWTne hxWT huWT hclosedB
        exact ⟨u', hsubD hu', hxu', hL'⟩
      · have hsubD : S ⊆ D :=
          subset_of_cut_avoiding G hxy hxD hyD hclosed huD (h2conn x)
            S hSsub hyS hno'
        have hssub : S ⊂ D :=
          Finset.ssubset_iff_subset_ne.mpr ⟨hsubD, fun h => huS (h.symm ▸ huD)⟩
        have hcard : #(S) < #(D) := Finset.card_lt_card hssub
        have hle' : #(S) ≤ n := by omega
        have hclosedS : ∀ d ∈ S, ∀ z : V,
            G.Adj d z → z ∈ S ∨ z = x ∨ z = u := by
          intro d hd z hadj
          by_cases hzS : z ∈ S
          · exact Or.inl hzS
          · by_cases hzx : z = x
            · exact Or.inr (Or.inl hzx)
            · by_cases hzu : z = u
              · exact Or.inr (Or.inr hzu)
              · exfalso
                have hzW : z ∈ Finset.univ \ {x, u} := by
                  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, ?_⟩
                  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                  exact ⟨hzx, hzu⟩
                have hzC : z ∈ (Finset.univ \ {x, u}) \ S :=
                  Finset.mem_sdiff.mpr ⟨hzW, hzS⟩
                exact (hno d hd z hzW hzS) hadj
        obtain ⟨u', hu', hxu', hL'⟩ := ih u S hle' hxu_ne hSne hxS huS hclosedS
        exact ⟨u', hsubD hu', hxu', hL'⟩

private theorem exists_lovasz_triple {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hL : LinkedOn G Finset.univ)
    (h2conn : ∀ z, LinkedOn G (Finset.univ.erase z))
    {a b : V} (hne : a ≠ b) (hnadj : ¬ G.Adj a b)
    (hdeg : 3 ≤ G.degree a) :
    ∃ v u w, G.Adj v u ∧ G.Adj v w ∧ u ≠ w ∧ ¬ G.Adj u w ∧
      LinkedOn G (Finset.univ \ {u, w}) := by
  classical
  by_cases hyes : ∀ y, y ≠ a → LinkedOn G (Finset.univ \ {a, y})
  · obtain ⟨s, t, has, hst, htne, hnt⟩ :=
      exists_adj_adj_not_adj_of_linkedOn G hL hne hnadj
    refine ⟨s, a, t, has.symm, hst, htne.symm, hnt, hyes t htne⟩
  · simp only [not_forall] at hyes
    obtain ⟨y, hyne, hyL⟩ := hyes
    simp only [LinkedOn, not_forall, not_exists] at hyL
    push Not at hyL
    obtain ⟨S, hSsub, hSne, hcomp, hno⟩ := hyL
    set W : Finset V := Finset.univ \ {a, y} with hW
    have haW : a ∉ W := by rw [hW]; simp
    have hyW : y ∉ W := by rw [hW]; simp
    have hSsub' : S ⊆ Finset.univ \ {a, y} := by rw [← hW]; exact hSsub
    have haS : a ∉ S := fun h => haW (by rw [hW]; exact hSsub' h)
    have hyS : y ∉ S := fun h => hyW (by rw [hW]; exact hSsub' h)
    have hRne : (W \ S).Nonempty := by
      obtain ⟨t, htW, htS⟩ := hcomp
      exact ⟨t, Finset.mem_sdiff.mpr ⟨htW, htS⟩⟩
    have hRsub : W \ S ⊆ W := Finset.sdiff_subset
    have haR : a ∉ W \ S := fun h => haW (hRsub h)
    have hyR : y ∉ W \ S := fun h => hyW (hRsub h)
    have hnoR : ∀ s ∈ S, ∀ t ∈ W \ S, ¬ G.Adj s t := by
      intro s hs t ht hadj
      have htW : t ∈ W := (Finset.mem_sdiff.mp ht).1
      have htS : t ∉ S := (Finset.mem_sdiff.mp ht).2
      have htW' : t ∈ Finset.univ \ {a, y} := by rwa [hW] at htW
      exact (hno s hs t htW' htS) hadj
    have hclosedS : ∀ d ∈ S, ∀ z : V, G.Adj d z → z ∈ S ∨ z = a ∨ z = y := by
      intro d hd z hadj
      by_cases hzS : z ∈ S
      · exact Or.inl hzS
      · by_cases hza : z = a
        · exact Or.inr (Or.inl hza)
        · by_cases hzy : z = y
          · exact Or.inr (Or.inr hzy)
          · exfalso
            by_cases hzW : z ∈ W
            · have hzC : z ∈ W \ S := Finset.mem_sdiff.mpr ⟨hzW, hzS⟩
              exact (hnoR d hd z hzC) hadj
            · have hzmem : z ∈ ({a, y} : Finset V) := by
                by_contra hcon
                have hzW' : z ∈ W := by
                  rw [hW]
                  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hcon⟩
                exact hzW hzW'
              simp only [Finset.mem_insert, Finset.mem_singleton] at hzmem
              rcases hzmem with h | h
              · exact absurd h hza
              · exact absurd h hzy
    have hclosedR : ∀ d ∈ W \ S, ∀ z : V, G.Adj d z → z ∈ W \ S ∨ z = a ∨ z = y := by
      intro d hd z hadj
      have hdW : d ∈ W := hRsub hd
      have hdS : d ∉ S := (Finset.mem_sdiff.mp hd).2
      by_cases hzR : z ∈ W \ S
      · exact Or.inl hzR
      · by_cases hza : z = a
        · exact Or.inr (Or.inl hza)
        · by_cases hzy : z = y
          · exact Or.inr (Or.inr hzy)
          · exfalso
            by_cases hzW : z ∈ W
            · have hzS : z ∈ S := by
                by_contra hcon
                exact hzR (Finset.mem_sdiff.mpr ⟨hzW, hcon⟩)
              have hzW' : z ∈ Finset.univ \ {a, y} := by rwa [hW] at hzW
              have hdW' : d ∈ Finset.univ \ {a, y} := by rwa [hW] at hdW
              exact (hno z hzS d hdW' hdS) hadj.symm
            · have hzmem : z ∈ ({a, y} : Finset V) := by
                by_contra hcon
                have hzW' : z ∈ W := by
                  rw [hW]
                  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hcon⟩
                exact hzW hzW'
              simp only [Finset.mem_insert, Finset.mem_singleton] at hzmem
              rcases hzmem with h | h
              · exact absurd h hza
              · exact absurd h hzy
    obtain ⟨u, huS, hau, hLau⟩ :=
      exists_nonseparating_neighbor G h2conn hyne.symm hSne haS hyS hclosedS
    obtain ⟨w, hwR, haw, hLaw⟩ :=
      exists_nonseparating_neighbor G h2conn hyne.symm hRne haR hyR hclosedR
    have huw : u ≠ w := by
      intro h
      rw [h] at huS
      exact (Finset.mem_sdiff.mp hwR).2 huS
    have hnadj_uw : ¬ G.Adj u w := by
      intro hadj
      have hwW : w ∈ W := hRsub hwR
      have hwS : w ∉ S := (Finset.mem_sdiff.mp hwR).2
      have hwW' : w ∈ Finset.univ \ {a, y} := by rwa [hW] at hwW
      exact (hno u huS w hwW' hwS) hadj
    have hlt : (({u, w} : Finset V).card) < #(G.neighborFinset a) := by
      rw [Finset.card_pair huw, SimpleGraph.card_neighborFinset_eq_degree]
      omega
    obtain ⟨n0, hn0N, hn0P⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have hn0 : G.Adj a n0 := by rwa [SimpleGraph.mem_neighborFinset] at hn0N
    have hn0ne : n0 ≠ u ∧ n0 ≠ w := by
      have h := hn0P
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
      exact h
    have hnoedge : ∀ s ∈ S, ∀ t ∈ W \ S, ¬ G.Adj s t := hnoR
    have hR' : W \ S = (Finset.univ \ {a, y}) \ S := by rw [hW]
    have hLuw : LinkedOn G (Finset.univ \ {u, w}) :=
      linkedOn_compl_pair_of_nonseparating G hyne.symm hSsub' hR' hnoedge huS hwR
        hLau hLaw hn0 hn0ne.1 hn0ne.2
    exact ⟨a, u, w, hau, haw, huw, hnadj_uw, hLuw⟩

private theorem exists_coloring_of_three_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : 3 ≤ k) (hL : LinkedOn G Finset.univ)
    (hdeg : ∀ v, G.degree v ≤ k)
    {a b : V} (hne : a ≠ b) (hnadj : ¬ G.Adj a b) :
    ∃ f : V → Fin k, IsProperOn G f Finset.univ := by
  classical
  by_cases hlow : ∃ r, G.degree r < k
  · obtain ⟨f, hf⟩ :=
      exists_properOn_of_linkedOn_univ G k (by omega) hL hdeg Finset.univ (Or.inr hlow)
    exact ⟨f, hf⟩
  · simp only [not_exists] at hlow
    have hdeg_eq : ∀ v, G.degree v = k :=
      fun v => le_antisymm (hdeg v) (not_lt.mp (hlow v))
    by_cases h2 : ∀ z, LinkedOn G (Finset.univ.erase z)
    · obtain ⟨v, u, w, hvu, hvw, huw, hnadj_uw, hLuw⟩ :=
        exists_lovasz_triple G hL h2 hne hnadj (by rw [hdeg_eq a]; exact hk)
      exact exists_coloring_of_lovasz_triple G k hdeg hvu hvw huw hnadj_uw hLuw
    · simp only [not_forall] at h2
      obtain ⟨z, hz⟩ := h2
      simp only [LinkedOn, not_forall, not_exists] at hz
      push Not at hz
      obtain ⟨S, hSsub, hSne, hcomp, hno⟩ := hz
      exact exists_coloring_of_cut_vertex G k (by omega) hL hdeg z S hSsub hSne hcomp hno

private theorem exists_cycle_length_card_of_two_regular {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hdeg2 : ∀ v, G.degree v = 2) :
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ c.length = Fintype.card V := by
  classical
  have hex : ∃ (u : V) (c : G.Walk u u), c.IsCycle := by
    by_cases hAc : G.IsAcyclic
    · have htree : G.IsTree := SimpleGraph.IsTree.mk hconn hAc
      have hcard := SimpleGraph.IsTree.card_edgeFinset htree
      have hsum := SimpleGraph.sum_degrees_eq_twice_card_edges G
      have hsum2 : (∑ v : V, G.degree v) = 2 * Fintype.card V := by
        simp only [hdeg2]
        simp [Finset.sum_const, Finset.card_univ, mul_comm]
      omega
    · simp only [SimpleGraph.IsAcyclic, not_forall, not_not] at hAc
      obtain ⟨v, c, hc⟩ := hAc
      exact ⟨v, c, hc⟩
  obtain ⟨u, c, hc⟩ := hex
  obtain ⟨v', h, t, rfl⟩ : ∃ (v' : V) (h : G.Adj u v') (t : G.Walk v' u),
      c = SimpleGraph.Walk.cons h t := by
    cases c with
    | nil =>
      exfalso
      exact (SimpleGraph.Walk.IsCycle.not_nil hc) SimpleGraph.Walk.nil_nil
    | cons h t =>
      exact ⟨_, h, t, rfl⟩
  have hclosure : ∀ x ∈ (SimpleGraph.Walk.cons h t).support.toFinset, ∀ y : V,
      G.Adj x y → y ∈ (SimpleGraph.Walk.cons h t).support.toFinset := by
    intro x hx y hadj
    have hx' : x ∈ (SimpleGraph.Walk.cons h t).support := List.mem_toFinset.mp hx
    have h1 : ((SimpleGraph.Walk.cons h t).toSubgraph.neighborSet x).ncard = 2 :=
      SimpleGraph.Walk.IsCycle.ncard_neighborSet_toSubgraph_eq_two hc hx'
    have h2 : (G.neighborSet x).ncard = 2 := by
      rw [← SimpleGraph.coe_neighborFinset, Set.ncard_coe_finset,
        SimpleGraph.card_neighborFinset_eq_degree]
      exact hdeg2 x
    have hsub : (SimpleGraph.Walk.cons h t).toSubgraph.neighborSet x ⊆ G.neighborSet x :=
      SimpleGraph.Subgraph.neighborSet_subset _ _
    have heq : (SimpleGraph.Walk.cons h t).toSubgraph.neighborSet x = G.neighborSet x :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [h1, h2])
    have hy : y ∈ (SimpleGraph.Walk.cons h t).toSubgraph.neighborSet x := by
      rw [heq]
      exact (SimpleGraph.mem_neighborSet G x y).mpr hadj
    have hadj' : (SimpleGraph.Walk.cons h t).toSubgraph.Adj x y :=
      (SimpleGraph.Subgraph.mem_neighborSet _ _ _).mp hy
    have hmem : y ∈ (SimpleGraph.Walk.cons h t).support :=
      SimpleGraph.Walk.mem_support_of_adj_toSubgraph hadj'.symm
    exact List.mem_toFinset.mpr hmem
  have hTeq : (SimpleGraph.Walk.cons h t).support.toFinset = Finset.univ := by
    by_contra hne
    have hss : (SimpleGraph.Walk.cons h t).support.toFinset ⊂ Finset.univ :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hne⟩
    obtain ⟨z, hzU, hzT⟩ := Finset.exists_of_ssubset hss
    have hTne : (SimpleGraph.Walk.cons h t).support.toFinset.Nonempty :=
      ⟨u, List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support _)⟩
    have hLconn := linkedOn_univ_of_connected G hconn
    obtain ⟨s, hsT, z', hz'U, hz'T, hadj⟩ :=
      hLconn _ (Finset.subset_univ _) hTne ⟨z, hzU, hzT⟩
    exact hz'T (hclosure s hsT z' hadj)
  have hall : ∀ w : V, w ∈ (SimpleGraph.Walk.cons h t).support := by
    intro w
    have hw : w ∈ (SimpleGraph.Walk.cons h t).support.toFinset := hTeq ▸ Finset.mem_univ w
    exact List.mem_toFinset.mp hw
  have hnil := SimpleGraph.Walk.IsCycle.not_nil hc
  have htsup : (SimpleGraph.Walk.cons h t).tail.support =
      ((SimpleGraph.Walk.cons h t).support).tail :=
    SimpleGraph.Walk.support_tail_of_not_nil _ hnil
  have hpath : ((SimpleGraph.Walk.cons h t).tail).IsPath :=
    SimpleGraph.Walk.IsCycle.isPath_tail hc
  have hsup_cons : (SimpleGraph.Walk.cons h t).support = u :: t.support :=
    SimpleGraph.Walk.support_cons h t
  have hall_tail : ∀ w : V, w ∈ ((SimpleGraph.Walk.cons h t).tail).support := by
    intro w
    rw [htsup, hsup_cons, List.tail_cons]
    have hw : w ∈ u :: t.support := by rw [← hsup_cons]; exact hall w
    simp only [List.mem_cons] at hw
    rcases hw with rfl | h
    · exact SimpleGraph.Walk.end_mem_support t
    · exact h
  have hham : ((SimpleGraph.Walk.cons h t).tail).IsHamiltonian :=
    (SimpleGraph.Walk.IsPath.isHamiltonian_iff hpath).mpr hall_tail
  have hhcyc : (SimpleGraph.Walk.cons h t).IsHamiltonianCycle :=
    SimpleGraph.Walk.isHamiltonianCycle_isCycle_and_isHamiltonian_tail.mpr ⟨hc, hham⟩
  have hlen : (SimpleGraph.Walk.cons h t).length = Fintype.card V :=
    SimpleGraph.Walk.IsHamiltonianCycle.length_eq hhcyc
  exact ⟨u, SimpleGraph.Walk.cons h t, hc, hlen⟩

private theorem nonempty_iso_cycleGraph_of_two_regular {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hdeg2 : ∀ v, G.degree v = 2) :
    Nonempty (G ≃g SimpleGraph.cycleGraph (Fintype.card V)) := by
  classical
  obtain ⟨u, c, hc, hlen⟩ := exists_cycle_length_card_of_two_regular G hconn hdeg2
  have hltV : 2 < Fintype.card V := by
    have h := SimpleGraph.degree_lt_card_verts (G := G) u
    rwa [hdeg2 u] at h
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card V = m + 3 := ⟨Fintype.card V - 3, by omega⟩
  rw [hm]
  rw [hm] at hlen
  have hcont := (SimpleGraph.cycleGraph_isContained_iff (by omega : 2 < m + 3)).mpr
    ⟨u, c, hc, hlen⟩
  obtain ⟨φ⟩ := hcont
  set f : Fin (m + 3) → V := ⇑φ.toHom with hf
  have hinj : Function.Injective f := SimpleGraph.Copy.injective φ
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [Fintype.card_fin]
    exact hm.symm
  have hrev : ∀ i j, G.Adj (f i) (f j) → (SimpleGraph.cycleGraph (m + 3)).Adj i j := by
    intro i j hadj
    have h2a : #(G.neighborFinset (f i)) = 2 := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      exact hdeg2 _
    have h2b : #(((SimpleGraph.cycleGraph (m + 3)).neighborFinset i).image f) = 2 := by
      rw [Finset.card_image_of_injective _ hinj,
        SimpleGraph.card_neighborFinset_eq_degree,
        SimpleGraph.cycleGraph_degree_three_le]
    have hsub : ((SimpleGraph.cycleGraph (m + 3)).neighborFinset i).image f ⊆
        G.neighborFinset (f i) := by
      intro x hx
      obtain ⟨k, hkN, rfl⟩ := Finset.mem_image.mp hx
      have hadj' : G.Adj (f i) (f k) := φ.toHom.map_adj
        ((SimpleGraph.mem_neighborFinset _ _ _).mp hkN)
      exact (SimpleGraph.mem_neighborFinset _ _ _).mpr hadj'
    have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
    have hjN : f j ∈ G.neighborFinset (f i) :=
      (SimpleGraph.mem_neighborFinset _ _ _).mpr hadj
    rw [← heq] at hjN
    obtain ⟨k, hkN, hfkj⟩ := Finset.mem_image.mp hjN
    have hkj : k = j := hinj hfkj
    rw [hkj] at hkN
    exact (SimpleGraph.mem_neighborFinset _ _ _).mp hkN
  have hforward : ∀ i j, (SimpleGraph.cycleGraph (m + 3)).Adj i j → G.Adj (f i) (f j) :=
    fun i j h => φ.toHom.map_adj h
  let e := Equiv.ofBijective f hbij
  have hiso : SimpleGraph.cycleGraph (m + 3) ≃g G :=
    { toEquiv := e, map_rel_iff' := fun {i j} => ⟨hrev i j, hforward i j⟩ }
  exact ⟨hiso.symm⟩

/--
**Brooks' theorem.** Let $G$ be a finite connected simple graph and let $\Delta$ be its maximum
degree: every vertex of $G$ has degree at most $\Delta$ and some vertex has degree exactly $\Delta$.
If $G$ is not complete and is not isomorphic to a cycle graph on an odd number of vertices, then $G$
has a proper vertex coloring with $\Delta$ colors.

Proves `Wanted` entry `brooks`.

Source: R. L. Brooks, On colouring the nodes of a network, Proc. Camb. Philos. Soc. 37 (1941), DOI
10.1017/S030500410002168X.
-/
theorem brooks {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (Δ : ℕ) (hconn : G.Connected)
    (hΔ : ∀ v, G.degree v ≤ Δ)
    (hΔatt : ∃ v, G.degree v = Δ)
    (hcomp : ¬Nonempty (G ≃g (⊤ : SimpleGraph V)))
    (hodd : ∀ (n : ℕ), Odd n → ¬Nonempty (G ≃g SimpleGraph.cycleGraph n)) :
    ∃ f : V → Fin Δ, ∀ ⦃v w : V⦄, G.Adj v w → f v ≠ f w := by
  classical
  have _ := hΔatt
  -- connectivity as LinkedOn (N1)
  have hL : LinkedOn G Finset.univ :=
    linkedOn_univ_of_connected G hconn
  -- a non-edge exists (else G = ⊤, contradicting hcomp)
  have hex : ∃ a b : V, a ≠ b ∧ ¬G.Adj a b := by
    by_contra h
    push Not at h
    have htop : G = ⊤ := by
      ext a b
      simp only [SimpleGraph.top_adj]
      constructor
      · intro hab
        exact SimpleGraph.ne_of_adj G hab
      · intro hne
        by_cases hab : G.Adj a b
        · exact hab
        · exact absurd (h a b hne) hab
    exact hcomp ⟨htop ▸ SimpleGraph.Iso.refl⟩
  -- Assembly: Δ ≤ 1 impossible (N5); Δ = 2 by low vertex (N3) or 2-regular
  -- classification (N14) with parity; Δ ≥ 3 by N12.
  by_cases hD : Δ ≤ 1
  · -- N5 gives a vertex of degree ≥ 2, contradicting hΔ.
    obtain ⟨a, b, hne, hnadj⟩ := hex
    obtain ⟨s, t, has, hst, htne, _hnt⟩ :=
      exists_adj_adj_not_adj_of_linkedOn G hL hne hnadj
    have hat_ne : a ≠ t := fun h => htne h.symm
    have hpair : ({a, t} : Finset V).card = 2 := Finset.card_pair hat_ne
    have haN : a ∈ G.neighborFinset s := by
      rw [SimpleGraph.mem_neighborFinset]; exact has.symm
    have htN : t ∈ G.neighborFinset s := by
      rw [SimpleGraph.mem_neighborFinset]; exact hst
    have hsub : ({a, t} : Finset V) ⊆ G.neighborFinset s := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact haN
      · exact htN
    have h2 : 2 ≤ G.degree s := by
      have h := Finset.card_le_card hsub
      rw [hpair, SimpleGraph.card_neighborFinset_eq_degree] at h
      exact h
    have hle := hΔ s
    omega
  · by_cases hD2 : Δ = 2
    · subst hD2
      by_cases hlow : ∃ r, G.degree r < 2
      · obtain ⟨f, hf⟩ :=
          exists_properOn_of_linkedOn_univ G 2 (by omega) hL hΔ Finset.univ (Or.inr hlow)
        exact ⟨f, fun v w hadj => hf v (Finset.mem_univ v) w (Finset.mem_univ w) hadj⟩
      · -- All degrees = 2: 2-regular classification (N14), then parity.
        have hdeg2 : ∀ v, G.degree v = 2 := by
          intro v
          have hle := hΔ v
          have hnge : ¬ G.degree v < 2 := fun h => hlow ⟨v, h⟩
          omega
        obtain ⟨e⟩ := nonempty_iso_cycleGraph_of_two_regular G hconn hdeg2
        rcases Nat.even_or_odd (Fintype.card V) with heven | hoddN
        · -- even cycle: bipartite coloring transported along e
          have hbip : (SimpleGraph.cycleGraph (Fintype.card V)).IsBipartite :=
            SimpleGraph.IsBipartite.cycleGraph_of_even heven
          obtain ⟨C⟩ := hbip
          refine ⟨fun v => C (e v), fun v w hadj => ?_⟩
          have hadj' : (SimpleGraph.cycleGraph (Fintype.card V)).Adj (e v) (e w) :=
            (SimpleGraph.Iso.map_adj_iff e).mpr hadj
          exact C.valid hadj'
        · exact absurd ⟨e⟩ (hodd _ hoddN)
    · -- Δ ≥ 3 via N12.
      have hk3 : 3 ≤ Δ := by omega
      obtain ⟨a, b, hne, hnadj⟩ := hex
      obtain ⟨f, hf⟩ := exists_coloring_of_three_le G Δ hk3 hL hΔ hne hnadj
      exact ⟨f, fun v w hadj => hf v (Finset.mem_univ v) w (Finset.mem_univ w) hadj⟩

end MathlibExt.Combinatorics.SimpleGraph.BrooksWanted
end
