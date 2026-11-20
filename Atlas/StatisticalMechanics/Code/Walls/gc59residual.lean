/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































































import Mathlib
import Code.Walls.gc58cyclespace

open Finset BigOperators SimpleGraph
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK connK_symm sources_symmDiff mem_sources
  path_exists exists_conn_set adjStep degK)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]






theorem gc59_reroute_step (ends : ι → Sym2 W) (G : Finset ι) (i : ι) {p q : W}
    (hi : i ∈ G) (hpq : ends i = s(p, q)) (hconn : connK ends (G \ {i}) p q)
    {a b : W} (hab : connK ends G a b) :
    connK ends (G \ {i}) a b :=
  gc55_reroute ends G i hi hpq hconn hab















def gc59_Peelable (ends : ι → Sym2 W) : Finset ι → List ι → Prop
  | _, [] => True
  | G, (i :: rest) =>
      i ∈ G ∧ (∃ p q : W, ends i = s(p, q) ∧ connK ends (G \ {i}) p q)
        ∧ gc59_Peelable ends (G \ {i}) rest


def gc59_removeList : Finset ι → List ι → Finset ι
  | G, [] => G
  | G, (i :: rest) => gc59_removeList (G \ {i}) rest




theorem gc59_connK_of_peelable (ends : ι → Sym2 W) {a b : W} :
    ∀ (ds : List ι) (G : Finset ι), gc59_Peelable ends G ds → connK ends G a b →
      connK ends (gc59_removeList G ds) a b := by
  intro ds
  induction ds with
  | nil => intro G _ hab; simpa [gc59_removeList] using hab
  | cons i rest ih =>
    intro G hpeel hab
    obtain ⟨hiG, ⟨p, q, hpq, hconn⟩, hrest⟩ := hpeel
    have hstep : connK ends (G \ {i}) a b :=
      gc59_reroute_step ends G i hiG hpq hconn hab
    simpa [gc59_removeList] using ih (G \ {i}) hrest hstep


theorem gc59_removeList_eq_sdiff (G : Finset ι) (ds : List ι) :
    gc59_removeList G ds = G \ ds.toFinset := by
  induction ds generalizing G with
  | nil => simp [gc59_removeList]
  | cons i rest ih =>
    rw [gc59_removeList, ih]
    ext j
    simp only [Finset.mem_sdiff, List.toFinset_cons, Finset.mem_insert, Finset.mem_singleton,
      List.mem_toFinset]
    tauto




theorem gc59_connK_of_peelable_sdiff (ends : ι → Sym2 W) {a b : W} (G : Finset ι) (ds : List ι)
    (hpeel : gc59_Peelable ends G ds) (hab : connK ends G a b) :
    connK ends (G \ ds.toFinset) a b := by
  rw [← gc59_removeList_eq_sdiff]
  exact gc59_connK_of_peelable ends ds G hpeel hab


theorem gc59_sdiff_inter (G D : Finset ι) : G \ (D ∩ G) = G \ D := by
  ext j
  simp only [Finset.mem_sdiff, Finset.mem_inter]
  tauto





theorem gc59_gate_survives_of_peeling (ends : ι → Sym2 W) {K L D : Finset ι} {x g : W}
    {ds : List ι} (hds : ds.toFinset = D ∩ (K ∪ L))
    (hpeel : gc59_Peelable ends (K ∪ L) ds) (hgate : connK ends (K ∪ L) x g) :
    connK ends ((K ∪ L) \ D) x g := by
  have := gc59_connK_of_peelable_sdiff ends (K ∪ L) ds hpeel hgate
  rw [hds, gc59_sdiff_inter] at this
  exact this















def gc59_RerouteConnector (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W) : Prop :=
    ∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W)
      ∧ ∀ L ∈ gc51_LblockSet ends K o x g,
          ∃ ds : List ι, ds.toFinset = D ∩ (K ∪ L)
            ∧ gc59_Peelable ends (K ∪ L) ds ∧ connK ends (K ∪ L) x g






theorem gc59_disjointConnector_of_reroute (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    (h : gc59_RerouteConnector ends K o x y g) :
    gc57_DisjointConnector ends K o x y g := by
  obtain ⟨D, hDV, hDsrc, hpeel⟩ := h
  refine ⟨D, hDV, hDsrc, ?_⟩
  intro L hL
  obtain ⟨ds, hds, hPeel, hgate⟩ := hpeel L hL
  have hconn : connK ends ((K ∪ L) \ D) x g :=
    gc59_gate_survives_of_peeling ends hds hPeel hgate
  refine ⟨(K ∪ L) \ D, Finset.sdiff_subset, ?_, hconn⟩
  rw [Finset.disjoint_left]
  intro i hi hiD
  exact (Finset.mem_sdiff.1 hi).2 hiD




















theorem gc59_disjointConnector_full (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W}
    (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg' : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hKsrc : sources ends K = ({o, x} : Finset W))
    (hcov :
      (connK ends K x g)
      ∨ (∃ i, i ∈ univ \ K ∧ ends i = s(y, g))
      ∨ (∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W)
            ∧ ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D)
      ∨ gc59_RerouteConnector ends K o x y g) :
    gc57_DisjointConnector ends K o x y g := by
  rcases hcov with hxg | hyge | hdisj | hreroute
  · exact gc58_disjointConnector_tricho ends hnd K hoy hog hxy hxg' hyg huniv hKsrc (Or.inl hxg)
  · exact gc58_disjointConnector_tricho ends hnd K hoy hog hxy hxg' hyg huniv hKsrc (Or.inr (Or.inl hyge))
  · exact gc58_disjointConnector_tricho ends hnd K hoy hog hxy hxg' hyg huniv hKsrc (Or.inr (Or.inr hdisj))
  · exact gc59_disjointConnector_of_reroute ends K hreroute






theorem gc59_countIneq_of_cover (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg' : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hcov : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
      (connK ends K x g)
      ∨ (∃ i, i ∈ univ \ K ∧ ends i = s(y, g))
      ∨ (∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W)
            ∧ ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D)
      ∨ gc59_RerouteConnector ends K o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g := by
  apply gc57_countIneq_of_disjointConnector ends hnd hox hoy hog hxy hxg' hyg huniv
  intro K hK
  have hKsrc : sources ends K = ({o, x} : Finset W) := by
    simpa [Finset.mem_filter, Finset.mem_powerset] using hK
  exact gc59_disjointConnector_full ends hnd K hoy hog hxy hxg' hyg huniv hKsrc (hcov K hK)

end Abstract

open Classical


















noncomputable def gc59_witnessEnds : Fin 5 → Sym2 (Fin 4) :=
  ![s(0, 1), s(0, 2), s(0, 3), s(0, 3), s(0, 3)]


theorem gc59_witnessEnds_univ_sources :
    sources gc59_witnessEnds (univ : Finset (Fin 5)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by decide


theorem gc59_witnessEnds_K_sources :
    sources gc59_witnessEnds ({0} : Finset (Fin 5)) = ({0, 1} : Finset (Fin 4)) := by decide


theorem gc59_witnessEnds_D_sources :
    sources gc59_witnessEnds ({1, 2} : Finset (Fin 5)) = ({2, 3} : Finset (Fin 4)) := by decide


theorem gc59_witnessEnds_loopless : ∀ i : Fin 5, ¬ (gc59_witnessEnds i).IsDiag := by decide



theorem gc59_witness_conn_23 :
    connK gc59_witnessEnds (({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) 1 3 :=
  (Relation.ReflTransGen.single (b := (0 : Fin 4)) ⟨0, by decide, by decide, by decide, by decide⟩).tail
    ⟨2, by decide, by decide, by decide, by decide⟩


theorem gc59_witness_conn_24 :
    connK gc59_witnessEnds (({0} : Finset (Fin 5)) ∪ ({2, 4} : Finset (Fin 5))) 1 3 :=
  (Relation.ReflTransGen.single (b := (0 : Fin 4)) ⟨0, by decide, by decide, by decide, by decide⟩).tail
    ⟨2, by decide, by decide, by decide, by decide⟩


theorem gc59_witness_conn_34 :
    connK gc59_witnessEnds (({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) 1 3 :=
  (Relation.ReflTransGen.single (b := (0 : Fin 4)) ⟨0, by decide, by decide, by decide, by decide⟩).tail
    ⟨3, by decide, by decide, by decide, by decide⟩




theorem gc59_witness_LblockSet :
    gc51_LblockSet gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 3
      = ({{2, 3}, {2, 4}, {3, 4}} : Finset (Finset (Fin 5))) := by
  rw [gc51_LblockSet]
  have hV : (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) = ({1, 2, 3, 4} : Finset (Fin 5)) := by
    decide
  rw [hV]
  have hset : ({1, 2, 3, 4} : Finset (Fin 5)).powerset.filter
      (fun L => sources gc59_witnessEnds L = (∅ : Finset (Fin 4)))
      = ({∅, {2, 3}, {2, 4}, {3, 4}} : Finset (Finset (Fin 5))) := by decide
  rw [show ({1, 2, 3, 4} : Finset (Fin 5)).powerset.filter
        (fun L => sources gc59_witnessEnds L = (∅ : Finset (Fin 4))
          ∧ connK gc59_witnessEnds (({0} : Finset (Fin 5)) ∪ L) 1 3)
      = (({1, 2, 3, 4} : Finset (Fin 5)).powerset.filter
          (fun L => sources gc59_witnessEnds L = (∅ : Finset (Fin 4)))).filter
            (fun L => connK gc59_witnessEnds (({0} : Finset (Fin 5)) ∪ L) 1 3) from by
    rw [Finset.filter_filter]]
  rw [hset]
  
  have hne : ¬ connK gc59_witnessEnds (({0} : Finset (Fin 5)) ∪ (∅ : Finset (Fin 5))) 1 3 := by
    rw [Finset.union_empty]
    intro h
    
    have inv : ∀ w : Fin 4, connK gc59_witnessEnds ({0} : Finset (Fin 5)) 1 w → (w = 0 ∨ w = 1) := by
      intro w hw
      induction hw with
      | refl => decide
      | @tail b c _ hstep ih =>
        obtain ⟨i, hi, hbi, hci, hbc⟩ := hstep
        rcases ih with rfl | rfl <;> (fin_cases hi <;> revert hbc hbi hci <;> revert c <;> decide)
    rcases inv 3 h with h3 | h3 <;> exact absurd h3 (by decide)
  
  ext L
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hLmem, hconn⟩
    rcases hLmem with rfl | rfl | rfl | rfl
    · exact absurd hconn hne
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨by simp, gc59_witness_conn_23⟩
    · exact ⟨by simp, gc59_witness_conn_24⟩
    · exact ⟨by simp, gc59_witness_conn_34⟩



theorem gc59_witness_reconn_23 :
    connK gc59_witnessEnds ((({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) \ {2}) 0 3 := by
  have h : (({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) \ ({2} : Finset (Fin 5))
      = ({0, 3} : Finset (Fin 5)) := by decide
  rw [h]
  exact Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩



theorem gc59_witness_reconn_24 :
    connK gc59_witnessEnds ((({0} : Finset (Fin 5)) ∪ ({2, 4} : Finset (Fin 5))) \ {2}) 0 3 := by
  have h : (({0} : Finset (Fin 5)) ∪ ({2, 4} : Finset (Fin 5))) \ ({2} : Finset (Fin 5))
      = ({0, 4} : Finset (Fin 5)) := by decide
  rw [h]
  exact Relation.ReflTransGen.single ⟨4, by decide, by decide, by decide, by decide⟩








theorem gc59_witness_rerouteConnector :
    gc59_RerouteConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
  refine ⟨({1, 2} : Finset (Fin 5)), ?_, gc59_witnessEnds_D_sources, ?_⟩
  · rw [show (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) = ({1, 2, 3, 4} : Finset (Fin 5)) from by decide]
    decide
  · intro L hL
    rw [gc59_witness_LblockSet] at hL
    simp only [Finset.mem_insert, Finset.mem_singleton] at hL
    rcases hL with rfl | rfl | rfl
    · 
      refine ⟨[2], by decide, ⟨by decide, ⟨0, 3, by decide, gc59_witness_reconn_23⟩, trivial⟩,
        gc59_witness_conn_23⟩
    · 
      refine ⟨[2], by decide, ⟨by decide, ⟨0, 3, by decide, gc59_witness_reconn_24⟩, trivial⟩,
        gc59_witness_conn_24⟩
    · 
      refine ⟨[], by decide, trivial, gc59_witness_conn_34⟩



theorem gc59_witness_disjointConnector :
    gc57_DisjointConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  gc59_disjointConnector_of_reroute gc59_witnessEnds _ gc59_witness_rerouteConnector


























theorem gc59_status :
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (a b : W) (G : Finset ι) (ds : List ι),
        gc59_Peelable ends G ds → connK ends G a b → connK ends (G \ ds.toFinset) a b)
    ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W),
        gc59_RerouteConnector ends K o x y g → gc57_DisjointConnector ends K o x y g)
    ∧ gc59_RerouteConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3
    ∧ gc57_DisjointConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  ⟨fun ends a b G ds hp hab => gc59_connK_of_peelable_sdiff ends G ds hp hab,
    fun ends K o x y g h => gc59_disjointConnector_of_reroute ends K h,
    gc59_witness_rerouteConnector, gc59_witness_disjointConnector⟩

end StatMech.Walls
