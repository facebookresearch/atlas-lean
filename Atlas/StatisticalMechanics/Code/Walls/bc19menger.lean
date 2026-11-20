/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































import Code.Walls.bc18mengerhard

namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} {k : ℕ}










structure bc19_AFan (G : SimpleGraph V) (A S R : Set V) (k : ℕ) where
  
  a : Fin k → V
  
  c : Fin k → V
  
  q : ∀ i, G.Walk (a i) (c i)
  ha : ∀ i, a i ∈ A
  hc : ∀ i, c i ∈ S
  hq : ∀ i, (q i).IsPath
  
  hmeet : ∀ i, ∀ z ∈ (q i).support, z ∈ S → z = c i
  
  hreg : ∀ i, ∀ z ∈ (q i).support, z ∈ R
  
  hdisj : ∀ ⦃i j⦄, i ≠ j → ∀ ⦃z⦄, z ∈ (q i).support → z ∉ (q j).support

omit [DecidableEq V] in

theorem bc19_AFan_c_inj {A S R : Set V} (F : bc19_AFan G A S R k) :
    Function.Injective F.c := by
  intro i j hij
  by_contra hne
  have hi : F.c i ∈ (F.q i).support := (F.q i).end_mem_support
  have hj : F.c j ∈ (F.q j).support := (F.q j).end_mem_support
  have hj' : F.c i ∈ (F.q j).support := by rw [hij]; exact hj
  exact F.hdisj hne hi hj'

omit [DecidableEq V] in

theorem bc19_AFan_c_cover [Fintype V] {A S R : Set V} (hS : S.ncard = k)
    (F : bc19_AFan G A S R k) : ∀ s ∈ S, ∃ i, F.c i = s := by
  have hinj := bc19_AFan_c_inj F
  set T := Set.range F.c with hT
  have hTsub : T ⊆ S := by rintro _ ⟨i, rfl⟩; exact F.hc i
  have hTcard : T.ncard = k := by
    rw [hT, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hTeq : T = S := Set.eq_of_subset_of_ncard_le hTsub (by rw [hTcard, hS]) (Set.toFinite S)
  intro s hs
  rw [← hTeq] at hs; obtain ⟨i, hi⟩ := hs; exact ⟨i, hi⟩









noncomputable def bc19_AFan_of_family {A S R : Set V}
    (F : bc16_DisjointPathFamily G A S (Fin k))
    (hreg : ∀ i, ∀ z ∈ (F.p i).support, z ∈ R) :
    bc19_AFan G A S R k := by
  have hhit : ∀ i, ∃ z ∈ (F.p i).support, z ∈ S :=
    fun i => ⟨F.b i, (F.p i).end_mem_support, F.hb i⟩
  choose c q hqpath hcS hqsub hqmeet using fun i => bc18_firstHitPath (F.p i) (hhit i)
  exact {
    a := F.a
    c := c
    q := q
    ha := F.ha
    hc := hcS
    hq := hqpath
    hmeet := hqmeet
    hreg := fun i z hz => hreg i z (hqsub i hz)
    hdisj := by
      intro i j hij z hzi hzj
      exact F.hdisj hij (hqsub i hzi) (hqsub j hzj) }








noncomputable def bc19_match [Fintype V] {A B S RA RB : Set V} (hS : S.ncard = k)
    (FA : bc19_AFan G A S RA k) (FB : bc19_AFan G B S RB k) : Fin k → Fin k :=
  fun i => (bc19_AFan_c_cover hS FB (FA.c i) (FA.hc i)).choose

theorem bc19_match_spec [Fintype V] {A B S RA RB : Set V} (hS : S.ncard = k)
    (FA : bc19_AFan G A S RA k) (FB : bc19_AFan G B S RB k) (i : Fin k) :
    FB.c (bc19_match hS FA FB i) = FA.c i :=
  (bc19_AFan_c_cover hS FB (FA.c i) (FA.hc i)).choose_spec

theorem bc19_match_inj [Fintype V] {A B S RA RB : Set V} (hS : S.ncard = k)
    (FA : bc19_AFan G A S RA k) (FB : bc19_AFan G B S RB k) :
    Function.Injective (bc19_match hS FA FB) := by
  intro i j hij
  have h1 := bc19_match_spec hS FA FB i
  have h2 := bc19_match_spec hS FA FB j
  rw [hij] at h1
  exact bc19_AFan_c_inj FA (h1.symm.trans h2)





noncomputable def bc19_gluedPath [Fintype V] {A B S RA RB : Set V} (hS : S.ncard = k)
    (FA : bc19_AFan G A S RA k) (FB : bc19_AFan G B S RB k) (i : Fin k) :
    G.Walk (FA.a i) (FB.a (bc19_match hS FA FB i)) :=
  (FA.q i).append ((FB.q (bc19_match hS FA FB i)).reverse.copy (bc19_match_spec hS FA FB i) rfl)

theorem bc19_Bhalf_support [Fintype V] {A B S RA RB : Set V} (hS : S.ncard = k)
    (FA : bc19_AFan G A S RA k) (FB : bc19_AFan G B S RB k) (i : Fin k) :
    ((FB.q (bc19_match hS FA FB i)).reverse.copy (bc19_match_spec hS FA FB i) rfl).support
      = (FB.q (bc19_match hS FA FB i)).support.reverse := by
  rw [Walk.support_copy, Walk.support_reverse]

theorem bc19_gluedPath_support_mem [Fintype V] {A B S RA RB : Set V} (hS : S.ncard = k)
    (FA : bc19_AFan G A S RA k) (FB : bc19_AFan G B S RB k) (i : Fin k) {z : V} :
    z ∈ (bc19_gluedPath hS FA FB i).support ↔
      z ∈ (FA.q i).support ∨ z ∈ (FB.q (bc19_match hS FA FB i)).support := by
  rw [bc19_gluedPath, Walk.mem_support_append_iff, bc19_Bhalf_support, List.mem_reverse]

theorem bc19_gluedPath_isPath [Fintype V] {A B S RA RB : Set V} (hS : S.ncard = k)
    (hRR : RA ∩ RB ⊆ S)
    (FA : bc19_AFan G A S RA k) (FB : bc19_AFan G B S RB k) (i : Fin k) :
    (bc19_gluedPath hS FA FB i).IsPath := by
  rw [bc19_gluedPath]
  apply bc18_appendPath_of_inter (FA.hq i)
  · rw [Walk.isPath_copy]; exact (Walk.isPath_reverse_iff _).2 (FB.hq _)
  · intro z hzA hzB
    rw [bc19_Bhalf_support, List.mem_reverse] at hzB
    exact FA.hmeet i z hzA (hRR ⟨FA.hreg i z hzA, FB.hreg _ z hzB⟩)




theorem bc19_cross_eq [Fintype V] {A B S RA RB : Set V} (hS : S.ncard = k)
    (hRR : RA ∩ RB ⊆ S)
    (FA : bc19_AFan G A S RA k) (FB : bc19_AFan G B S RB k) {i j : Fin k} {z : V}
    (hzA : z ∈ (FA.q i).support) (hzB : z ∈ (FB.q (bc19_match hS FA FB j)).support) :
    FA.c i = FA.c j := by
  have hvS : z ∈ S := hRR ⟨FA.hreg i z hzA, FB.hreg _ z hzB⟩
  have h1 : z = FA.c i := FA.hmeet i z hzA hvS
  have h2 : z = FB.c (bc19_match hS FA FB j) := FB.hmeet _ z hzB hvS
  rw [bc19_match_spec hS FA FB j] at h2
  rw [← h1, ← h2]





noncomputable def bc19_glueFans [Fintype V] {A B S RA RB : Set V} (hS : S.ncard = k)
    (hRR : RA ∩ RB ⊆ S)
    (FA : bc19_AFan G A S RA k) (FB : bc19_AFan G B S RB k) :
    bc16_DisjointPathFamily G A B (Fin k) where
  a := FA.a
  b := fun i => FB.a (bc19_match hS FA FB i)
  p := bc19_gluedPath hS FA FB
  ha := FA.ha
  hb := fun i => FB.ha (bc19_match hS FA FB i)
  hp := bc19_gluedPath_isPath hS hRR FA FB
  hdisj := by
    intro i j hij z hzi hzj
    rw [bc19_gluedPath_support_mem] at hzi hzj
    rcases hzi with hiA | hiB <;> rcases hzj with hjA | hjB
    · exact FA.hdisj hij hiA hjA
    · exact hij (bc19_AFan_c_inj FA (bc19_cross_eq hS hRR FA FB hiA hjB))
    · exact hij (bc19_AFan_c_inj FA (bc19_cross_eq hS hRR FA FB hjA hiB)).symm
    · exact FB.hdisj ((bc19_match_inj hS FA FB).ne hij) hiB hjB










theorem bc19_aFan_extract [Fintype V] {A B S : Set V}
    (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard)
    (hSsep : bc16_IsSeparator G A B S)
    (hH : bc17_HardDir (bc17_restr G (bc18_AReach G A S)) A S) :
    Nonempty (bc19_AFan G A S (bc18_AReach G A S) k) := by
  have F := (bc18_aside_fan hmin hSsep hH).some
  set RA := bc18_AReach G A S with hRA
  have hregF : ∀ i, ∀ z ∈ (F.p i).support, z ∈ RA := fun i z hz =>
    bc17_restr_support_subset G RA (bc18_subset_AReach G A S (F.ha i)) (F.p i) z hz
  set F' := bc17_familyMapLe (bc17_restr_le G RA) F with hF'
  have hregF' : ∀ i, ∀ z ∈ (F'.p i).support, z ∈ RA := by
    intro i z hz
    rw [hF'] at hz; simp only [bc17_familyMapLe] at hz
    rw [Walk.support_mapLe_eq_support] at hz; exact hregF i z hz
  exact ⟨bc19_AFan_of_family F' hregF'⟩



theorem bc19_trivFan [Fintype V] {B S : Set V} (hS : S.ncard = k) (hSB : S ⊆ B) :
    Nonempty (bc19_AFan G B S S k) := by
  obtain ⟨f, hinj, hf⟩ := bc17_exists_finInj_of_le_ncard (Set.toFinite S) (le_of_eq hS.symm)
  exact ⟨{
    a := f
    c := f
    q := fun _ => Walk.nil
    ha := fun i => hSB (hf i)
    hc := hf
    hq := fun _ => Walk.IsPath.nil
    hmeet := by
      intro i z hz _
      rw [Walk.support_nil, List.mem_singleton] at hz; exact hz
    hreg := by
      intro i z hz
      rw [Walk.support_nil, List.mem_singleton] at hz; exact hz ▸ hf i
    hdisj := by
      intro i j hij z hzi hzj
      rw [Walk.support_nil, List.mem_singleton] at hzi hzj
      exact hij (hinj (hzi.symm.trans hzj)) }⟩









omit [DecidableEq V] in

theorem bc19_lastEdge {a s : V} (Q : G.Walk a s) (hne : a ≠ s) :
    ∃ u, G.Adj u s ∧ u ∈ Q.support := by
  induction Q with
  | nil => exact absurd rfl hne
  | @cons a b s hadj t ih =>
      by_cases hbs : b = s
      · subst hbs; exact ⟨a, hadj, Walk.start_mem_support _⟩
      · obtain ⟨u, hu, hut⟩ := ih hbs
        exact ⟨u, hu, by rw [Walk.support_cons]; exact List.mem_cons.2 (Or.inr hut)⟩

omit [DecidableEq V] in


theorem bc19_essential [Fintype V] {A B S : Set V} {s : V}
    (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard)
    (hScard : S.ncard = k) (hsS : s ∈ S) :
    ¬ bc16_IsSeparator G A B (S \ {s}) := by
  intro hsep
  have hle := hmin _ hsep
  have : (S \ {s}).ncard < S.ncard :=
    Set.ncard_lt_ncard ⟨Set.diff_subset, fun h => (h hsS).2 rfl⟩ (Set.toFinite S)
  rw [hScard] at this; omega





theorem bc19_Bside_strict_of_notSubsetA [Fintype V] {A B S : Set V}
    (hSsep : bc16_IsSeparator G A B S)
    (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard)
    (hScard : S.ncard = k)
    (hnsub : ¬ S ⊆ A) :
    (bc17_restr G (bc18_AReach G B S)).edgeSet.ncard < G.edgeSet.ncard := by
  obtain ⟨s, hsS, hsA⟩ : ∃ s ∈ S, s ∉ A := by
    by_contra hc; push Not at hc; exact hnsub (fun s hs => hc s hs)
  have hess := bc19_essential hmin hScard hsS
  obtain ⟨a, ha, Q0, hQ0⟩ := bc18_mem_AReach_of_essential hSsep hess
  set Q := Q0.bypass with hQdef
  have hQpath : Q.IsPath := Q0.bypass_isPath
  have hQmeet : ∀ z ∈ Q.support, z ∈ S → z = s := fun z hz => hQ0 z (Q0.support_bypass_subset hz)
  have hane : a ≠ s := fun h => hsA (h ▸ ha)
  obtain ⟨u, hAdj, huQ⟩ := bc19_lastEdge Q hane
  have huS : u ∉ S := fun huS => hAdj.ne (hQmeet u huQ huS)
  have huRA : u ∈ bc18_AReach G A S := bc18_mem_AReach_of_mem_support ha hQpath hQmeet huQ
  have huRB : u ∉ bc18_AReach G B S := fun huRB =>
    huS (bc18_AReach_inter_subset hSsep ⟨huRA, huRB⟩)
  exact bc17_restr_edgeSet_ncard_lt G (bc18_AReach G B S) (x := s) (y := u) hAdj.symm huRB




theorem bc19_Aside_strict_of_notSubsetB [Fintype V] {A B S : Set V}
    (hSsep : bc16_IsSeparator G A B S)
    (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard)
    (hScard : S.ncard = k)
    (hnsub : ¬ S ⊆ B) :
    (bc17_restr G (bc18_AReach G A S)).edgeSet.ncard < G.edgeSet.ncard :=
  bc19_Bside_strict_of_notSubsetA (bc16_separator_symm hSsep)
    (fun C hC => hmin C (bc16_separator_symm hC)) hScard hnsub










def bc19_reindex {A B : Set V} {ι κ : Type*} (E : κ ≃ ι)
    (F : bc16_DisjointPathFamily G A B ι) : bc16_DisjointPathFamily G A B κ where
  a := fun i => F.a (E i)
  b := fun i => F.b (E i)
  p := fun i => F.p (E i)
  ha := fun i => F.ha (E i)
  hb := fun i => F.hb (E i)
  hp := fun i => F.hp (E i)
  hdisj := by
    intro i j hij z hzi hzj
    exact F.hdisj (fun h => hij (E.injective h)) hzi hzj



def bc19_directSum {A B Y : Set V} {x y : V} {m : ℕ}
    (hxy : G.Adj x y) (f : Fin m → V) (hf : ∀ i, f i ∈ Y)
    (hinj : Function.Injective f)
    (hxY : x ∉ Y) (hyY : y ∉ Y)
    (hxA : x ∈ A) (hyB : y ∈ B) (hYA : Y ⊆ A) (hYB : Y ⊆ B) :
    bc16_DisjointPathFamily G A B (Sum (Fin m) Unit) where
  a := Sum.elim f (fun _ => x)
  b := Sum.elim f (fun _ => y)
  p := fun i => match i with
    | Sum.inl j => (Walk.nil : G.Walk (f j) (f j))
    | Sum.inr _ => Walk.cons hxy Walk.nil
  ha := by rintro (j | _); exacts [hYA (hf j), hxA]
  hb := by rintro (j | _); exacts [hYB (hf j), hyB]
  hp := by rintro (j | _); exacts [Walk.IsPath.nil, Walk.IsPath.of_adj hxy]
  hdisj := by
    rintro (i | _) (j | _) hij z hzi hzj <;> simp only at hzi hzj
    · have h1 := Walk.mem_support_nil_iff.mp hzi
      have h2 := Walk.mem_support_nil_iff.mp hzj
      exact hij (by rw [Sum.inl.injEq]; exact hinj (h1.symm.trans h2))
    · have h1 := Walk.mem_support_nil_iff.mp hzi
      rw [Sum.elim_inl] at h1
      simp only [Walk.support_cons, Walk.support_nil, Sum.elim_inr, List.mem_cons,
        List.not_mem_nil, or_false] at hzj
      rcases hzj with h | h
      · exact hxY (by rw [← h, h1]; exact hf i)
      · exact hyY (by rw [← h, h1]; exact hf i)
    · have h2 := Walk.mem_support_nil_iff.mp hzj
      rw [Sum.elim_inl] at h2
      simp only [Walk.support_cons, Walk.support_nil, Sum.elim_inr, List.mem_cons,
        List.not_mem_nil, or_false] at hzi
      rcases hzi with h | h
      · exact hxY (by rw [← h, h2]; exact hf j)
      · exact hyY (by rw [← h, h2]; exact hf j)
    · exact hij rfl


noncomputable def bc19_sumEquiv (m : ℕ) : (Sum (Fin m) Unit) ≃ Fin (m + 1) :=
  Fintype.equivFinOfCardEq (by simp)




theorem bc19_directSolution [Fintype V] {A B Y : Set V} {x y : V}
    (hxy : G.Adj x y) (hxY : x ∉ Y) (hyY : y ∉ Y)
    (hxA : x ∈ A) (hyB : y ∈ B) (hYA : Y ⊆ A) (hYB : Y ⊆ B)
    (hk : Y.ncard + 1 = k) :
    Nonempty (bc16_DisjointPathFamily G A B (Fin k)) := by
  obtain ⟨f, hinj, hf⟩ := bc17_exists_finInj_of_le_ncard (Set.toFinite Y) (le_refl Y.ncard)
  have F := bc19_directSum hxy f hf hinj hxY hyY hxA hyB hYA hYB
  refine ⟨bc19_reindex ?_ F⟩
  rw [← hk]; exact (bc19_sumEquiv Y.ncard).symm









theorem bc19_Y_sep_of_xyA {A B Y : Set V} {x y : V}
    (hxY : x ∉ Y) (hyY : y ∉ Y) (hxA : x ∈ A) (hyA : y ∈ A)
    (hYsep : bc16_IsSeparator (G.deleteEdges {s(x, y)}) A B Y) :
    bc16_IsSeparator G A B Y := by
  by_contra hnot
  rw [bc16_IsSeparator] at hnot
  push Not at hnot
  obtain ⟨a₀, ha₀, b₀, hb₀, R₀, hR₀⟩ := hnot
  have ha₀Y : a₀ ∉ Y := fun h => hR₀ a₀ h R₀.start_mem_support
  have hR₀restr : (bc17_restr G {v | v ∉ Y}).Reachable a₀ b₀ :=
    ⟨bc18_walkToRestrCompl R₀ (fun w hw hwY => hR₀ w hwY hw)⟩
  rcases hR₀restr with ⟨R₀'⟩
  rcases bc18_splitAtEdge (x := x) (y := y) R₀' with hkeep | ⟨_, h2⟩ | ⟨_, h2⟩
  · rw [bc18_restr_compl_deleteEdges] at hkeep
    exact bc18_contra_of_reachable hYsep ha₀ hb₀ ha₀Y hkeep
  · rw [bc18_restr_compl_deleteEdges] at h2
    exact bc18_contra_of_reachable hYsep hyA hb₀ hyY h2
  · rw [bc18_restr_compl_deleteEdges] at h2
    exact bc18_contra_of_reachable hYsep hxA hb₀ hxY h2












theorem bc19_subset_AReach_of_min [Fintype V] {A B S : Set V}
    (hSsep : bc16_IsSeparator G A B S)
    (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard)
    (hScard : S.ncard = k) : S ⊆ bc18_AReach G A S :=
  fun s hsS => bc18_mem_AReach_of_essential hSsep (bc19_essential hmin hScard hsS)




theorem bc19_getAFan [Fintype V] {N : ℕ} {A B S : Set V}
    (IH : ∀ (G' : SimpleGraph V), G'.edgeSet.ncard < N → ∀ (A' B' : Set V), bc17_HardDir G' A' B')
    (hltN : (bc17_restr G (bc18_AReach G A S)).edgeSet.ncard < G.edgeSet.ncard →
            (bc17_restr G (bc18_AReach G A S)).edgeSet.ncard < N)
    (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard)
    (hSsep : bc16_IsSeparator G A B S) (hScard : S.ncard = k)
    (hcase : S ⊆ A ∨ ¬ S ⊆ B) :
    ∃ RA : Set V, RA ⊆ bc18_AReach G A S ∧ Nonempty (bc19_AFan G A S RA k) := by
  by_cases hSA : S ⊆ A
  · exact ⟨S, bc19_subset_AReach_of_min hSsep hmin hScard, bc19_trivFan (B := A) hScard hSA⟩
  · have hSB : ¬ S ⊆ B := hcase.resolve_left hSA
    exact ⟨bc18_AReach G A S, le_refl _,
      bc19_aFan_extract hmin hSsep
        (IH _ (hltN (bc19_Aside_strict_of_notSubsetB hSsep hmin hScard hSB)) A S)⟩




theorem bc19_routeS [Fintype V] {N : ℕ} {A B S : Set V}
    (IH : ∀ (G' : SimpleGraph V), G'.edgeSet.ncard < N → ∀ (A' B' : Set V), bc17_HardDir G' A' B')
    (hltA : (bc17_restr G (bc18_AReach G A S)).edgeSet.ncard < G.edgeSet.ncard →
            (bc17_restr G (bc18_AReach G A S)).edgeSet.ncard < N)
    (hltB : (bc17_restr G (bc18_AReach G B S)).edgeSet.ncard < G.edgeSet.ncard →
            (bc17_restr G (bc18_AReach G B S)).edgeSet.ncard < N)
    (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard)
    (hSsep : bc16_IsSeparator G A B S) (hScard : S.ncard = k)
    (hcA : S ⊆ A ∨ ¬ S ⊆ B) (hcB : S ⊆ B ∨ ¬ S ⊆ A) :
    Nonempty (bc16_DisjointPathFamily G A B (Fin k)) := by
  obtain ⟨RA, hRA, FA⟩ := bc19_getAFan IH hltA hmin hSsep hScard hcA
  obtain ⟨RB, hRB, FB⟩ := bc19_getAFan (A := B) (B := A) IH hltB
    (fun C hC => hmin C (bc16_separator_symm hC)) (bc16_separator_symm hSsep) hScard hcB
  exact ⟨bc19_glueFans hScard
    (fun z ⟨hzA, hzB⟩ => bc18_AReach_inter_subset hSsep ⟨hRA hzA, hRB hzB⟩) FA.some FB.some⟩





theorem bc19_hardDir_aux [Fintype V] (N : ℕ) :
    ∀ (G : SimpleGraph V), G.edgeSet.ncard < N → ∀ (A B : Set V), bc17_HardDir G A B := by
  induction N with
  | zero => intro G hlt; exact absurd hlt (by omega)
  | succ N IH =>
    intro G hlt A B k hmin
    by_cases hbot : G = ⊥
    · subst hbot; exact bc17_hard_bot A B hmin
    · have hne : G.edgeSet.ncard ≠ 0 := by
        intro h0; apply hbot
        rw [← edgeSet_eq_empty, ← Set.ncard_eq_zero (Set.toFinite _)]; exact h0
      obtain ⟨x, y, hxy⟩ : ∃ x y, G.Adj x y := by
        by_contra hc; push Not at hc
        apply hne; rw [Set.ncard_eq_zero (Set.toFinite _)]
        ext e; obtain ⟨u, v⟩ := e
        simp only [mem_edgeSet, Set.mem_empty_iff_false, iff_false]; exact hc u v
      have hdel_lt : (G.deleteEdges {s(x, y)}).edgeSet.ncard < N := by
        have := bc17_edgeSet_ncard_lt_of_deleteEdge (G := G) hxy; omega
      rcases bc17_deleteEdge_dichotomy hxy hmin with hC1 | hC2
      · 
        exact bc17_hardDir_step_case1 (IH _ hdel_lt A B) hC1
      · 
        obtain ⟨Y, hYsep, hYlt, hxY, hyY, hSxsep, hSysep⟩ := hC2
        have hYnotG : ¬ bc16_IsSeparator G A B Y :=
          fun hG => absurd (hmin Y hG) (by omega)
        have hSxcard : (insert x Y).ncard = k := by
          have hge := hmin _ hSxsep
          rw [Set.ncard_insert_of_notMem hxY (Set.toFinite Y)] at hge ⊢; omega
        have hSycard : (insert y Y).ncard = k := by
          have hge := hmin _ hSysep
          rw [Set.ncard_insert_of_notMem hyY (Set.toFinite Y)] at hge ⊢; omega
        have hYcard1 : Y.ncard + 1 = k := by
          have := hmin _ hSxsep
          rw [Set.ncard_insert_of_notMem hxY (Set.toFinite Y)] at this; omega
        have mkLtA : ∀ S : Set V,
            (bc17_restr G (bc18_AReach G A S)).edgeSet.ncard < G.edgeSet.ncard →
            (bc17_restr G (bc18_AReach G A S)).edgeSet.ncard < N := fun S h => by omega
        have mkLtB : ∀ S : Set V,
            (bc17_restr G (bc18_AReach G B S)).edgeSet.ncard < G.edgeSet.ncard →
            (bc17_restr G (bc18_AReach G B S)).edgeSet.ncard < N := fun S h => by omega
        have hnotxyA : ¬ (x ∈ A ∧ y ∈ A) := fun ⟨hxA, hyA⟩ =>
          hYnotG (bc19_Y_sep_of_xyA hxY hyY hxA hyA hYsep)
        have hnotxyB : ¬ (x ∈ B ∧ y ∈ B) := fun ⟨hxB, hyB⟩ =>
          hYnotG (bc16_separator_symm
            (bc19_Y_sep_of_xyA (B := A) hxY hyY hxB hyB (bc16_separator_symm hYsep)))
        by_cases hSxA : insert x Y ⊆ A <;> by_cases hSxB : insert x Y ⊆ B
        · exact bc19_routeS IH (mkLtA _) (mkLtB _) hmin hSxsep hSxcard
            (Or.inl hSxA) (Or.inl hSxB)
        · by_cases hSyA : insert y Y ⊆ A <;> by_cases hSyB : insert y Y ⊆ B
          · exact bc19_routeS IH (mkLtA _) (mkLtB _) hmin hSysep hSycard
              (Or.inl hSyA) (Or.inl hSyB)
          · exact absurd ⟨hSxA (Set.mem_insert _ _), hSyA (Set.mem_insert _ _)⟩ hnotxyA
          · refine bc19_directSolution hxy hxY hyY
              (hSxA (Set.mem_insert _ _)) (hSyB (Set.mem_insert _ _))
              (fun z hz => hSxA (Set.mem_insert_of_mem _ hz))
              (fun z hz => hSyB (Set.mem_insert_of_mem _ hz)) hYcard1
          · exact bc19_routeS IH (mkLtA _) (mkLtB _) hmin hSysep hSycard
              (Or.inr hSyB) (Or.inr hSyA)
        · by_cases hSyA : insert y Y ⊆ A <;> by_cases hSyB : insert y Y ⊆ B
          · exact bc19_routeS IH (mkLtA _) (mkLtB _) hmin hSysep hSycard
              (Or.inl hSyA) (Or.inl hSyB)
          · refine bc19_directSolution hxy.symm hyY hxY
              (hSyA (Set.mem_insert _ _)) (hSxB (Set.mem_insert _ _))
              (fun z hz => hSyA (Set.mem_insert_of_mem _ hz))
              (fun z hz => hSxB (Set.mem_insert_of_mem _ hz)) hYcard1
          · exact absurd ⟨hSxB (Set.mem_insert _ _), hSyB (Set.mem_insert _ _)⟩ hnotxyB
          · exact bc19_routeS IH (mkLtA _) (mkLtB _) hmin hSysep hSycard
              (Or.inr hSyB) (Or.inr hSyA)
        · exact bc19_routeS IH (mkLtA _) (mkLtB _) hmin hSxsep hSxcard
            (Or.inr hSxB) (Or.inr hSxA)





theorem bc19_hardDir_all [Fintype V] (G : SimpleGraph V) (A B : Set V) :
    bc17_HardDir G A B :=
  bc19_hardDir_aux (G.edgeSet.ncard + 1) G (by omega) A B





theorem bc19_menger_minmax [Fintype V] (G : SimpleGraph V) (A B : Set V) {k : ℕ}
    (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard) :
    ∃ F : bc16_DisjointPathFamily G A B (Fin k),
      ∀ C, bc16_IsSeparator G A B C → Fintype.card (Fin k) ≤ C.ncard := by
  obtain ⟨F⟩ := bc19_hardDir_all G A B k hmin
  exact ⟨F, fun C hC => by simpa using hmin C hC⟩

end StatMech.Walls
