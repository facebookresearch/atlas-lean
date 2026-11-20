/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































import Mathlib
import Code.Walls.menger_core

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
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK connK_symm adjStep degK compOf
  sources_symmDiff mem_sources path_exists exists_conn_set)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]






def mngg_IsConnector (ends : ι → Sym2 W) (G : Finset ι) (a b : W) (P : Finset ι) : Prop :=
  P ⊆ G ∧ sources ends P = ({a, b} : Finset W)


theorem mngg_connK_of_isConnector (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {G : Finset ι} {a b : W} (hab : a ≠ b) {P : Finset ι}
    (hP : mngg_IsConnector ends G a b P) : connK ends P a b :=
  mng_connK_of_sources ends hnd P hab hP.2



def mngg_DisjointFamily (ends : ι → Sym2 W) (G : Finset ι) (a b : W) {j : ℕ}
    (P : Fin j → Finset ι) : Prop :=
  (∀ i, mngg_IsConnector ends G a b (P i)) ∧
    (∀ i i', i ≠ i' → Disjoint (P i) (P i'))


def mngg_familyUnion {j : ℕ} (P : Fin j → Finset ι) : Finset ι :=
  Finset.univ.biUnion (fun i => P i)

@[simp] theorem mngg_mem_familyUnion {j : ℕ} {P : Fin j → Finset ι} {x : ι} :
    x ∈ mngg_familyUnion P ↔ ∃ i, x ∈ P i := by
  simp [mngg_familyUnion]


theorem mngg_familyUnion_subset {ends : ι → Sym2 W} {G : Finset ι} {a b : W} {j : ℕ}
    {P : Fin j → Finset ι} (hP : mngg_DisjointFamily ends G a b P) :
    mngg_familyUnion P ⊆ G := by
  intro x hx
  rw [mngg_mem_familyUnion] at hx
  obtain ⟨i, hi⟩ := hx
  exact (hP.1 i).1 hi





def mngg_RelConn (ends : ι → Sym2 W) (G : Finset ι) (a b : W) (k : ℕ) : Prop :=
  ∀ (j : ℕ), j < k → ∀ (P : Fin j → Finset ι), mngg_DisjointFamily ends G a b P →
    connK ends (G \ mngg_familyUnion P) a b



theorem mngg_RelConn_of_le {ends : ι → Sym2 W} {G : Finset ι} {a b : W} {k k' : ℕ}
    (hkk' : k ≤ k') (h : mngg_RelConn ends G a b k') : mngg_RelConn ends G a b k :=
  fun j hj P hP => h j (lt_of_lt_of_le hj hkk') P hP












theorem mngg_augment (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {G : Finset ι} {a b : W} (hab : a ≠ b) {j : ℕ} {P : Fin j → Finset ι}
    (hP : mngg_DisjointFamily ends G a b P)
    (hres : connK ends (G \ mngg_familyUnion P) a b) :
    ∃ Q : Fin (j + 1) → Finset ι, mngg_DisjointFamily ends G a b Q ∧
      (∀ i : Fin j, Q i.castSucc = P i) ∧ Q (Fin.last j) ⊆ G \ mngg_familyUnion P := by
  
  obtain ⟨Q₀, hQ₀sub, hQ₀src⟩ := exists_conn_set ends (G \ mngg_familyUnion P) hres hab
  
  have hQ₀src' : sources ends Q₀ = ({a, b} : Finset W) := by
    rw [hQ₀src]
  
  have hQ₀G : Q₀ ⊆ G := fun x hx => (Finset.mem_sdiff.1 (hQ₀sub hx)).1
  
  have hQ₀disjU : Disjoint Q₀ (mngg_familyUnion P) := by
    rw [Finset.disjoint_left]
    intro x hx
    exact (Finset.mem_sdiff.1 (hQ₀sub hx)).2
  refine ⟨Fin.snoc P Q₀, ⟨?_, ?_⟩, ?_, ?_⟩
  · 
    intro i
    refine Fin.lastCases ?_ ?_ i
    · rw [Fin.snoc_last]; exact ⟨hQ₀G, hQ₀src'⟩
    · intro i'; rw [Fin.snoc_castSucc]; exact hP.1 i'
  · 
    intro i i'
    refine Fin.lastCases ?_ ?_ i
    · 
      refine Fin.lastCases ?_ ?_ i'
      · intro hne; exact absurd rfl hne
      · intro i'' _
        rw [Fin.snoc_last, Fin.snoc_castSucc]
        refine Finset.disjoint_of_subset_right ?_ hQ₀disjU
        intro x hx; rw [mngg_mem_familyUnion]; exact ⟨i'', hx⟩
    · intro i''
      refine Fin.lastCases ?_ ?_ i'
      · intro _
        rw [Fin.snoc_last, Fin.snoc_castSucc]
        refine Finset.disjoint_of_subset_left ?_ hQ₀disjU.symm
        intro x hx; rw [mngg_mem_familyUnion]; exact ⟨i'', hx⟩
      · intro i''' hne
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        refine hP.2 i'' i''' ?_
        intro h; exact hne (by rw [h])
  · intro i; rw [Fin.snoc_castSucc]
  · rw [Fin.snoc_last]; exact hQ₀sub











theorem mngg_edgeMenger_family (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {G : Finset ι} {a b : W} (hab : a ≠ b) (k : ℕ)
    (hconn : mngg_RelConn ends G a b k) :
    ∃ P : Fin k → Finset ι, mngg_DisjointFamily ends G a b P := by
  induction k with
  | zero =>
    exact ⟨Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0⟩⟩
  | succ n ih =>
    
    obtain ⟨P, hP⟩ := ih (mngg_RelConn_of_le (Nat.le_succ n) hconn)
    
    have hres : connK ends (G \ mngg_familyUnion P) a b :=
      hconn n (Nat.lt_succ_self n) P hP
    
    obtain ⟨Q, hQ, _, _⟩ := mngg_augment ends hnd hab hP hres
    exact ⟨Q, hQ⟩




theorem mngg_edgeMenger (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {G : Finset ι} {a b : W} (hab : a ≠ b) (k : ℕ)
    (hconn : mngg_RelConn ends G a b k) :
    ∃ P : Fin k → Finset ι,
      (∀ i, P i ⊆ G) ∧
      (∀ i, sources ends (P i) = ({a, b} : Finset W)) ∧
      (∀ i, connK ends (P i) a b) ∧
      (∀ i i', i ≠ i' → Disjoint (P i) (P i')) := by
  obtain ⟨P, hconn', hdisj⟩ := mngg_edgeMenger_family ends hnd hab k hconn
  refine ⟨P, fun i => (hconn' i).1, fun i => (hconn' i).2, ?_, hdisj⟩
  intro i
  exact mngg_connK_of_isConnector ends hnd hab (hconn' i)











def mngg_IsCut (ends : ι → Sym2 W) (G : Finset ι) (a b : W) (C : Finset ι) : Prop :=
  C ⊆ G ∧ ¬ connK ends (G \ C) a b




theorem mngg_cut_meets_connector (ends : ι → Sym2 W) {G : Finset ι} {a b : W} {C P : Finset ι}
    (hC : mngg_IsCut ends G a b C) (hPG : P ⊆ G) (hPconn : connK ends P a b) :
    (P ∩ C).Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty, ← Finset.disjoint_iff_inter_eq_empty] at hempty
  exact hC.2 (mng_connK_of_disjoint ends hPG hempty hPconn)





theorem mngg_card_cut_ge (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {G : Finset ι} {a b : W} (hab : a ≠ b) {k : ℕ} {P : Fin k → Finset ι}
    (hP : mngg_DisjointFamily ends G a b P) {C : Finset ι} (hC : mngg_IsCut ends G a b C) :
    k ≤ #C := by
  
  have hmeet : ∀ i, ((P i) ∩ C).Nonempty := fun i =>
    mngg_cut_meets_connector ends hC (hP.1 i).1
      (mngg_connK_of_isConnector ends hnd hab (hP.1 i))
  choose e he using hmeet
  have heC : ∀ i, e i ∈ C := fun i => (Finset.mem_inter.1 (he i)).2
  have heP : ∀ i, e i ∈ P i := fun i => (Finset.mem_inter.1 (he i)).1
  
  have hinj : Function.Injective e := by
    intro i i' h
    by_contra hne
    exact (Finset.disjoint_left.1 (hP.2 i i' hne)) (heP i) (h ▸ heP i')
  
  have hle := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin k))) (t := C) e
    (fun i _ => heC i) (fun i _ i' _ h => hinj h)
  simpa using hle






theorem mngg_three_disjoint_connectors (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {G : Finset ι} {a b : W} (hab : a ≠ b) (hconn : mngg_RelConn ends G a b 3) :
    ∃ P₁ P₂ P₃ : Finset ι,
      P₁ ⊆ G ∧ P₂ ⊆ G ∧ P₃ ⊆ G ∧
      Disjoint P₁ P₂ ∧ Disjoint P₁ P₃ ∧ Disjoint P₂ P₃ ∧
      sources ends P₁ = ({a, b} : Finset W) ∧
      sources ends P₂ = ({a, b} : Finset W) ∧
      sources ends P₃ = ({a, b} : Finset W) ∧
      connK ends P₁ a b ∧ connK ends P₂ a b ∧ connK ends P₃ a b := by
  obtain ⟨P, hsub, hsrc, hck, hdisj⟩ := mngg_edgeMenger ends hnd hab 3 hconn
  refine ⟨P 0, P 1, P 2, hsub 0, hsub 1, hsub 2, ?_, ?_, ?_,
    hsrc 0, hsrc 1, hsrc 2, hck 0, hck 1, hck 2⟩
  · exact hdisj 0 1 (by decide)
  · exact hdisj 0 2 (by decide)
  · exact hdisj 1 2 (by decide)






theorem mngg_maxflow_mincut (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {G : Finset ι} {a b : W} (hab : a ≠ b) (k : ℕ)
    (hconn : mngg_RelConn ends G a b k) :
    (∃ P : Fin k → Finset ι, mngg_DisjointFamily ends G a b P) ∧
    (∀ C : Finset ι, mngg_IsCut ends G a b C → k ≤ #C) := by
  obtain ⟨P, hP⟩ := mngg_edgeMenger_family ends hnd hab k hconn
  exact ⟨⟨P, hP⟩, fun C hC => mngg_card_cut_ge ends hnd hab hP hC⟩
















theorem mngg_disjoint_connectors_of_cut (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {G : Finset ι} {x g : W} (hne : x ≠ g) (k : ℕ)
    (hconn : mngg_RelConn ends G x g (k + 1)) :
    ∃ (P₀ : Finset ι) (P : Fin k → Finset ι),
      P₀ ⊆ G ∧ connK ends P₀ x g ∧ (∀ i, P i ⊆ G) ∧ (∀ i, connK ends (P i) x g) ∧
      (∀ i, Disjoint P₀ (P i)) ∧ (∀ i i', i ≠ i' → Disjoint (P i) (P i')) ∧
      (∀ D : Finset ι, D ⊆ mngg_familyUnion P → connK ends (G \ D) x g) := by
  obtain ⟨Q, hsub, hsrc, hck, hdisj⟩ := mngg_edgeMenger ends hnd hne (k + 1) hconn
  
  refine ⟨Q (Fin.last k), fun i => Q i.castSucc,
    hsub _, hck _, fun i => hsub _, fun i => hck _, ?_, ?_, ?_⟩
  · 
    intro i
    exact hdisj (Fin.last k) i.castSucc (by
      intro h; exact absurd h.symm (Fin.castSucc_lt_last i).ne)
  · 
    intro i i' hii'
    exact hdisj i.castSucc i'.castSucc (by
      intro h; exact hii' (Fin.castSucc_injective _ h))
  · 
    intro D hD
    have hP₀U : Disjoint (Q (Fin.last k)) (mngg_familyUnion (fun i => Q i.castSucc)) := by
      rw [Finset.disjoint_left]
      intro y hy hyU
      rw [mngg_mem_familyUnion] at hyU
      obtain ⟨i, hi⟩ := hyU
      exact (Finset.disjoint_left.1
        (hdisj (Fin.last k) i.castSucc (by
          intro h; exact absurd h.symm (Fin.castSucc_lt_last i).ne))) hy hi
    have hP₀D : Disjoint (Q (Fin.last k)) D :=
      Finset.disjoint_of_subset_right hD hP₀U
    exact mng_connK_of_disjoint ends (hsub _) hP₀D (hck _)

end Abstract









open Classical







noncomputable def mngg_theta : Fin 6 → Sym2 (Fin 5) :=
  ![s(0, 4), s(0, 1), s(1, 4), s(0, 2), s(2, 3), s(3, 4)]


theorem mngg_theta_loopless : ∀ i : Fin 6, ¬ (mngg_theta i).IsDiag := by decide


theorem mngg_theta_P1_sources :
    sources mngg_theta ({0} : Finset (Fin 6)) = ({0, 4} : Finset (Fin 5)) := by decide


theorem mngg_theta_P2_sources :
    sources mngg_theta ({1, 2} : Finset (Fin 6)) = ({0, 4} : Finset (Fin 5)) := by decide


theorem mngg_theta_P3_sources :
    sources mngg_theta ({3, 4, 5} : Finset (Fin 6)) = ({0, 4} : Finset (Fin 5)) := by decide


theorem mngg_theta_disjoint :
    Disjoint ({0} : Finset (Fin 6)) ({1, 2} : Finset (Fin 6)) ∧
    Disjoint ({0} : Finset (Fin 6)) ({3, 4, 5} : Finset (Fin 6)) ∧
    Disjoint ({1, 2} : Finset (Fin 6)) ({3, 4, 5} : Finset (Fin 6)) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide


theorem mngg_theta_P1_conn : connK mngg_theta ({0} : Finset (Fin 6)) 0 4 :=
  Relation.ReflTransGen.single (b := (4 : Fin 5))
    ⟨0, by decide, by decide, by decide, by decide⟩


theorem mngg_theta_P2_conn : connK mngg_theta ({1, 2} : Finset (Fin 6)) 0 4 :=
  (Relation.ReflTransGen.single (b := (1 : Fin 5))
      ⟨1, by decide, by decide, by decide, by decide⟩).trans
    (Relation.ReflTransGen.single (b := (4 : Fin 5))
      ⟨2, by decide, by decide, by decide, by decide⟩)


theorem mngg_theta_P3_conn : connK mngg_theta ({3, 4, 5} : Finset (Fin 6)) 0 4 :=
  (Relation.ReflTransGen.single (b := (2 : Fin 5))
      ⟨3, by decide, by decide, by decide, by decide⟩).trans
    ((Relation.ReflTransGen.single (b := (3 : Fin 5))
        ⟨4, by decide, by decide, by decide, by decide⟩).trans
      (Relation.ReflTransGen.single (b := (4 : Fin 5))
        ⟨5, by decide, by decide, by decide, by decide⟩))





theorem mngg_test_theta_three_disjoint :
    ∃ P₁ P₂ P₃ : Finset (Fin 6),
      P₁ ⊆ (univ : Finset (Fin 6)) ∧ P₂ ⊆ (univ : Finset (Fin 6)) ∧ P₃ ⊆ (univ : Finset (Fin 6)) ∧
      Disjoint P₁ P₂ ∧ Disjoint P₁ P₃ ∧ Disjoint P₂ P₃ ∧
      sources mngg_theta P₁ = ({0, 4} : Finset (Fin 5)) ∧
      sources mngg_theta P₂ = ({0, 4} : Finset (Fin 5)) ∧
      sources mngg_theta P₃ = ({0, 4} : Finset (Fin 5)) ∧
      connK mngg_theta P₁ 0 4 ∧ connK mngg_theta P₂ 0 4 ∧ connK mngg_theta P₃ 0 4 :=
  ⟨{0}, {1, 2}, {3, 4, 5}, Finset.subset_univ _, Finset.subset_univ _, Finset.subset_univ _,
    mngg_theta_disjoint.1, mngg_theta_disjoint.2.1, mngg_theta_disjoint.2.2,
    mngg_theta_P1_sources, mngg_theta_P2_sources, mngg_theta_P3_sources,
    mngg_theta_P1_conn, mngg_theta_P2_conn, mngg_theta_P3_conn⟩









theorem mngg_test_residual_conn :
    connK mngg_theta ((univ : Finset (Fin 6)) \ ({0, 1, 2} : Finset (Fin 6))) 0 4 := by
  have hsub : ({3, 4, 5} : Finset (Fin 6)) ⊆ (univ : Finset (Fin 6)) \ ({0, 1, 2} : Finset (Fin 6)) := by
    decide
  exact mng_connK_mono mngg_theta hsub mngg_theta_P3_conn






noncomputable def mngg_theta_cut : Finset (Fin 6) := {0, 1, 3}


theorem mngg_test_cut_disconnects :
    ¬ connK mngg_theta ((univ : Finset (Fin 6)) \ mngg_theta_cut) 0 4 := by
  intro h
  have inv : ∀ w : Fin 5,
      connK mngg_theta ((univ : Finset (Fin 6)) \ mngg_theta_cut) 0 w → w = 0 := by
    intro w hw
    induction hw with
    | refl => rfl
    | @tail c d _ hstep ih =>
      obtain ⟨i, hi, hc, hd, hcd⟩ := hstep
      
      simp only [mngg_theta_cut, Finset.mem_sdiff, Finset.mem_univ, true_and] at hi
      subst ih
      fin_cases i <;> simp_all [mngg_theta]
  exact absurd (inv 4 h) (by decide)




theorem mngg_test_maxflow_eq_mincut :
    mngg_IsCut mngg_theta (univ : Finset (Fin 6)) 0 4 mngg_theta_cut ∧
    #mngg_theta_cut = 3 := by
  refine ⟨⟨by decide, mngg_test_cut_disconnects⟩, by decide⟩









noncomputable def mngg_sq : Fin 4 → Sym2 (Fin 4) := ![s(0, 1), s(1, 2), s(2, 3), s(3, 0)]



noncomputable def mngg_sq_cut : Finset (Fin 4) := {0, 3}

theorem mngg_sq_cut_disconnects :
    ¬ connK mngg_sq ((univ : Finset (Fin 4)) \ mngg_sq_cut) 0 2 := by
  intro h
  have inv : ∀ w : Fin 4,
      connK mngg_sq ((univ : Finset (Fin 4)) \ mngg_sq_cut) 0 w → w = 0 := by
    intro w hw
    induction hw with
    | refl => rfl
    | @tail c d _ hstep ih =>
      obtain ⟨i, hi, hc, hd, hcd⟩ := hstep
      revert hc hd hcd ih
      fin_cases i <;> simp_all [mngg_sq, mngg_sq_cut]
  exact absurd (inv 2 h) (by decide)





theorem mngg_test_square_not_three :
    mngg_IsCut mngg_sq (univ : Finset (Fin 4)) 0 2 mngg_sq_cut ∧
    #mngg_sq_cut = 2 ∧
    (∀ (P : Fin 3 → Finset (Fin 4)),
      mngg_DisjointFamily mngg_sq (univ : Finset (Fin 4)) 0 2 P → False) := by
  have hcut : mngg_IsCut mngg_sq (univ : Finset (Fin 4)) 0 2 mngg_sq_cut :=
    ⟨by decide, mngg_sq_cut_disconnects⟩
  have hloop : ∀ i : Fin 4, ¬ (mngg_sq i).IsDiag := by decide
  refine ⟨hcut, by decide, ?_⟩
  intro P hP
  have : (3 : ℕ) ≤ #mngg_sq_cut :=
    mngg_card_cut_ge mngg_sq hloop (by decide) hP hcut
  rw [show #mngg_sq_cut = 2 from by decide] at this
  omega






theorem mngg_status :
    
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
      {G : Finset ι} {a b : W} (hab : a ≠ b) (k : ℕ) (hconn : mngg_RelConn ends G a b k),
      ∃ P : Fin k → Finset ι, mngg_DisjointFamily ends G a b P) ∧
    
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
      {G : Finset ι} {a b : W} (hab : a ≠ b) {k : ℕ} {P : Fin k → Finset ι}
      (hP : mngg_DisjointFamily ends G a b P) {C : Finset ι} (hC : mngg_IsCut ends G a b C),
      k ≤ #C) ∧
    
    (∃ P₁ P₂ P₃ : Finset (Fin 6),
      Disjoint P₁ P₂ ∧ Disjoint P₁ P₃ ∧ Disjoint P₂ P₃ ∧
      connK mngg_theta P₁ 0 4 ∧ connK mngg_theta P₂ 0 4 ∧ connK mngg_theta P₃ 0 4) ∧
    
    (∀ (P : Fin 3 → Finset (Fin 4)),
      mngg_DisjointFamily mngg_sq (univ : Finset (Fin 4)) 0 2 P → False) := by
  refine ⟨?_, ?_, ?_, mngg_test_square_not_three.2.2⟩
  · intro ι W _ _ _ _ ends hnd G a b hab k hconn
    exact mngg_edgeMenger_family ends hnd hab k hconn
  · intro ι W _ _ _ _ ends hnd G a b hab k P hP C hC
    exact mngg_card_cut_ge ends hnd hab hP hC
  · exact ⟨{0}, {1, 2}, {3, 4, 5}, mngg_theta_disjoint.1, mngg_theta_disjoint.2.1,
      mngg_theta_disjoint.2.2, mngg_theta_P1_conn, mngg_theta_P2_conn, mngg_theta_P3_conn⟩

end StatMech.Walls
