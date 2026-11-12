/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamFourColorBalancedCore










open Finset
open scoped symmDiff

namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent


def threeGateCounterEnds : Fin 15 -> Sym2 (Fin 6)
  | 0 => s(0, 1)
  | 1 => s(0, 2)
  | 2 => s(0, 3)
  | 3 => s(0, 4)
  | 4 => s(0, 5)
  | 5 => s(1, 2)
  | 6 => s(1, 3)
  | 7 => s(1, 4)
  | 8 => s(1, 5)
  | 9 => s(2, 3)
  | 10 => s(2, 4)
  | 11 => s(2, 5)
  | 12 => s(3, 4)
  | 13 => s(3, 5)
  | 14 => s(4, 5)

def threeGateCounterSupport : Finset (Fin 15) :=
  {0, 1, 4, 5, 7, 8, 9, 10, 11, 12, 14}

def threeGateCounterK : Finset (Fin 15) := {0, 9, 11, 12, 14}

def threeGateCounterS : Finset (Fin 15) := {4, 8, 9, 10, 12}

def threeGateCounterN : Finset (Fin 15) := {1, 9, 11, 12, 14}

def threeGateCounterA : Finset (Fin 15) := {0, 1, 4, 8, 9, 10, 12}


def ThreeGateCounterGated (E : Finset (Fin 15)) : Prop :=
  ¬ connK threeGateCounterEnds E 1 3 ∧
    ¬ connK threeGateCounterEnds (threeGateCounterSupport \ E) 1 3

private theorem not_connK_of_closed_vertex_set
    {I W : Type*} [DecidableEq I] [DecidableEq W]
    {ends : I -> Sym2 W} {E : Finset I} {C : Finset W} {u v : W}
    (hu : u ∈ C) (hv : v ∉ C)
    (hclosed : ∀ i ∈ E, ∀ a ∈ ends i, a ∈ C ->
      ∀ b ∈ ends i, b ∈ C) :
    ¬ connK ends E u v := by
  intro huv
  apply hv
  have hmem : ∀ x, connK ends E u x -> x ∈ C := by
    intro x hux
    induction hux with
    | refl => exact hu
    | tail hab hstep ih =>
        rcases hstep with ⟨i, hi, ha, hb, -⟩
        exact hclosed i hi _ ha ih _ hb
  exact hmem v huv

private theorem threeGateCounter_closed
    (E : Finset (Fin 15)) (C : Finset (Fin 6))
    (hEC : (E = threeGateCounterK ∧ C = {0, 1}) ∨
      (E = threeGateCounterS ∧ C = {0, 1, 5}) ∨
      (E = threeGateCounterN ∧ C = {1})) :
    ∀ i ∈ E, ∀ a ∈ threeGateCounterEnds i, a ∈ C ->
      ∀ b ∈ threeGateCounterEnds i, b ∈ C := by
  rcases hEC with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    intro i hi a ha haC b hb <;>
    fin_cases i <;>
    simp [threeGateCounterK, threeGateCounterS, threeGateCounterN,
      threeGateCounterEnds] at hi ha haC hb ⊢ <;> aesop

private theorem threeGateCounter_complement_closed
    (E : Finset (Fin 15))
    (hE : E = threeGateCounterK ∨
      E = threeGateCounterS ∨ E = threeGateCounterN) :
    ∀ i ∈ threeGateCounterSupport \ E,
      ∀ a ∈ threeGateCounterEnds i, a ∈ ({0, 1, 2, 4, 5} : Finset (Fin 6)) ->
      ∀ b ∈ threeGateCounterEnds i, b ∈ ({0, 1, 2, 4, 5} : Finset (Fin 6)) := by
  rcases hE with rfl | rfl | rfl <;>
    intro i hi a ha haC b hb <;>
    fin_cases i <;>
    simp [threeGateCounterSupport, threeGateCounterK,
      threeGateCounterS, threeGateCounterN,
      threeGateCounterEnds] at hi ha haC hb ⊢ <;> aesop

theorem threeGateCounter_boundaries :
    sources threeGateCounterEnds threeGateCounterSupport = {0, 2} /\
      sources threeGateCounterEnds threeGateCounterK = {0, 1} /\
      sources threeGateCounterEnds threeGateCounterS = {0, 1} /\
      sources threeGateCounterEnds threeGateCounterN = {0, 2} /\
      sources threeGateCounterEnds threeGateCounterA = {0, 2} := by
  decide

theorem threeGateCounter_threefold :
    threeGateCounterK ∆ threeGateCounterS ∆ threeGateCounterN =
      threeGateCounterA := by
  decide

private theorem threeGateCounter_complement_not_conn
    (E : Finset (Fin 15))
    (hE : E = threeGateCounterK ∨
      E = threeGateCounterS ∨ E = threeGateCounterN) :
    ¬ connK threeGateCounterEnds (threeGateCounterSupport \ E) 1 3 := by
  apply not_connK_of_closed_vertex_set
    (C := ({0, 1, 2, 4, 5} : Finset (Fin 6)))
  · simp
  · simp
  · exact threeGateCounter_complement_closed E hE

theorem threeGateCounter_K_gated :
    ThreeGateCounterGated threeGateCounterK := by
  constructor
  · apply not_connK_of_closed_vertex_set
      (C := ({0, 1} : Finset (Fin 6))) (by simp) (by simp)
    exact threeGateCounter_closed _ _ (Or.inl ⟨rfl, rfl⟩)
  · exact threeGateCounter_complement_not_conn _ (Or.inl rfl)

theorem threeGateCounter_S_gated :
    ThreeGateCounterGated threeGateCounterS := by
  constructor
  · apply not_connK_of_closed_vertex_set
      (C := ({0, 1, 5} : Finset (Fin 6))) (by simp) (by simp)
    exact threeGateCounter_closed _ _ (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact threeGateCounter_complement_not_conn _ (Or.inr (Or.inl rfl))

theorem threeGateCounter_N_gated :
    ThreeGateCounterGated threeGateCounterN := by
  constructor
  · apply not_connK_of_closed_vertex_set
      (C := ({1} : Finset (Fin 6))) (by simp) (by simp)
    exact threeGateCounter_closed _ _ (Or.inr (Or.inr ⟨rfl, rfl⟩))
  · exact threeGateCounter_complement_not_conn _ (Or.inr (Or.inr rfl))

private theorem threeGateCounter_A_conn :
    connK threeGateCounterEnds threeGateCounterA 1 3 := by
  have h15 : connK threeGateCounterEnds threeGateCounterA 1 5 :=
    Relation.ReflTransGen.single ⟨8, by simp [threeGateCounterA],
      by simp [threeGateCounterEnds], by simp [threeGateCounterEnds], by decide⟩
  have h50 : adjStep threeGateCounterEnds threeGateCounterA 5 0 :=
    ⟨4, by simp [threeGateCounterA], by simp [threeGateCounterEnds],
      by simp [threeGateCounterEnds], by decide⟩
  have h02 : adjStep threeGateCounterEnds threeGateCounterA 0 2 :=
    ⟨1, by simp [threeGateCounterA], by simp [threeGateCounterEnds],
      by simp [threeGateCounterEnds], by decide⟩
  have h23 : adjStep threeGateCounterEnds threeGateCounterA 2 3 :=
    ⟨9, by simp [threeGateCounterA], by simp [threeGateCounterEnds],
      by simp [threeGateCounterEnds], by decide⟩
  exact ((h15.tail h50).tail h02).tail h23


theorem threeGate_boundaryOnly_closure_false :
    sources threeGateCounterEnds threeGateCounterSupport = {0, 2} ∧
      sources threeGateCounterEnds threeGateCounterK = {0, 1} ∧
      sources threeGateCounterEnds threeGateCounterS = {0, 1} ∧
      sources threeGateCounterEnds threeGateCounterN = {0, 2} ∧
      threeGateCounterK ∆ threeGateCounterS ∆ threeGateCounterN =
        threeGateCounterA ∧
      ThreeGateCounterGated threeGateCounterK ∧
      ThreeGateCounterGated threeGateCounterS ∧
      ThreeGateCounterGated threeGateCounterN ∧
      ¬ ThreeGateCounterGated threeGateCounterA := by
  refine ⟨threeGateCounter_boundaries.1,
    threeGateCounter_boundaries.2.1,
    threeGateCounter_boundaries.2.2.1,
    threeGateCounter_boundaries.2.2.2.1,
    threeGateCounter_threefold,
    threeGateCounter_K_gated,
    threeGateCounter_S_gated,
    threeGateCounter_N_gated, ?_⟩
  intro hA
  exact hA.1 threeGateCounter_A_conn




def canonicalGateCounterEnds : Fin 21 -> Sym2 (Fin 7)
  | 0 => s(0, 1)
  | 1 => s(0, 2)
  | 2 => s(0, 3)
  | 3 => s(0, 4)
  | 4 => s(0, 5)
  | 5 => s(0, 6)
  | 6 => s(1, 2)
  | 7 => s(1, 3)
  | 8 => s(1, 4)
  | 9 => s(1, 5)
  | 10 => s(1, 6)
  | 11 => s(2, 3)
  | 12 => s(2, 4)
  | 13 => s(2, 5)
  | 14 => s(2, 6)
  | 15 => s(3, 4)
  | 16 => s(3, 5)
  | 17 => s(3, 6)
  | 18 => s(4, 5)
  | 19 => s(4, 6)
  | 20 => s(5, 6)
  | _ => s(5, 6)

def canonicalGateCounterSupport : Finset (Fin 21) :=
  {0, 2, 5, 6, 13, 14, 15, 16, 17, 18, 20}

def canonicalGateCounterK : Finset (Fin 21) := {0, 13, 14, 20}

def canonicalGateCounterL : Finset (Fin 21) :=
  {2, 5, 6, 15, 16, 17, 18}

def canonicalGateCounterA : Finset (Fin 21) :=
  {0, 6, 13, 14, 15, 16, 18, 20}

def canonicalGateCounterB : Finset (Fin 21) := {2, 5, 17}

def canonicalGateCounterS : Finset (Fin 21) :=
  {0, 13, 14, 15, 16, 18, 20}

def canonicalGateCounterR : Finset (Fin 21) := {2, 5, 6, 17}

def canonicalGateCounterC0 : Finset (Fin 21) := {0, 13, 14, 20}

def canonicalGateCounterC1 : Finset (Fin 21) := ∅

def canonicalGateCounterC2 : Finset (Fin 21) := {6, 15, 16, 18}

def canonicalGateCounterC3 : Finset (Fin 21) := {2, 5, 17}

def canonicalGateCounterTransfer : Finset (Fin 21) := {6}

def CanonicalGateCounterGated (E : Finset (Fin 21)) : Prop :=
  ¬ connK canonicalGateCounterEnds E 1 3 ∧
    ¬ connK canonicalGateCounterEnds (canonicalGateCounterSupport \ E) 1 3

private theorem canonicalGateCounter_closed
    (E : Finset (Fin 21)) (C : Finset (Fin 7))
    (hEC :
      ((E = canonicalGateCounterK ∨ E = canonicalGateCounterS) ∧ C = {0, 1}) ∨
      ((E = canonicalGateCounterL ∨ E = canonicalGateCounterR) ∧ C = {1, 2})) :
    ∀ i ∈ E, ∀ a ∈ canonicalGateCounterEnds i, a ∈ C ->
      ∀ b ∈ canonicalGateCounterEnds i, b ∈ C := by
  rcases hEC with ⟨hE, rfl⟩ | ⟨hE, rfl⟩ <;>
    rcases hE with rfl | rfl <;>
    intro i hi a ha haC b hb <;>
    fin_cases i <;>
    simp [canonicalGateCounterK, canonicalGateCounterL,
      canonicalGateCounterS, canonicalGateCounterR,
      canonicalGateCounterEnds] at hi ha haC hb ⊢ <;> aesop

private theorem canonicalGateCounter_not_conn
    (E : Finset (Fin 21)) (C : Finset (Fin 7))
    (hEC :
      ((E = canonicalGateCounterK ∨ E = canonicalGateCounterS) ∧ C = {0, 1}) ∨
      ((E = canonicalGateCounterL ∨ E = canonicalGateCounterR) ∧ C = {1, 2})) :
    ¬ connK canonicalGateCounterEnds E 1 3 := by
  apply not_connK_of_closed_vertex_set (C := C)
  · rcases hEC with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
  · rcases hEC with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
  · exact canonicalGateCounter_closed E C hEC

theorem canonicalGateCounter_rows_partition :
    canonicalGateCounterSupport \ canonicalGateCounterK = canonicalGateCounterL ∧
      canonicalGateCounterSupport \ canonicalGateCounterA = canonicalGateCounterB ∧
      canonicalGateCounterSupport \ canonicalGateCounterS = canonicalGateCounterR := by
  decide

theorem canonicalGateCounter_cells :
    canonicalGateCounterK ∩ canonicalGateCounterA = canonicalGateCounterC0 ∧
      canonicalGateCounterK ∩ canonicalGateCounterB = canonicalGateCounterC1 ∧
      canonicalGateCounterL ∩ canonicalGateCounterA = canonicalGateCounterC2 ∧
      canonicalGateCounterL ∩ canonicalGateCounterB = canonicalGateCounterC3 := by
  decide

theorem canonicalGateCounter_cell_sources :
    sources canonicalGateCounterEnds canonicalGateCounterC0 = {0, 1} ∧
      sources canonicalGateCounterEnds canonicalGateCounterC1 = ∅ ∧
      sources canonicalGateCounterEnds canonicalGateCounterC2 = {1, 2} ∧
      sources canonicalGateCounterEnds canonicalGateCounterC3 = ∅ := by
  decide

private theorem canonicalGateCounter_K_no_incident_three :
    ∀ i ∈ canonicalGateCounterK,
      (3 : Fin 7) ∉ canonicalGateCounterEnds i := by
  intro i hi
  fin_cases i <;>
    simp [canonicalGateCounterK, canonicalGateCounterEnds] at hi ⊢

private theorem edgeComponent_subset_support_generic
    {I W : Type*} [DecidableEq I] [Fintype W] [DecidableEq W]
    (ends : I -> Sym2 W) (E : Finset I) (u : W) :
    edgeComponent ends E u ⊆ E := by
  classical
  intro i hi
  rw [edgeComponent, Finset.mem_filter] at hi
  exact hi.1

private theorem edgeComponent_endpoint_conn_generic
    {I W : Type*} [DecidableEq I] [Fintype W] [DecidableEq W]
    (ends : I -> Sym2 W) (E : Finset I) (u : W)
    {i : I} (hi : i ∈ edgeComponent ends E u)
    {x : W} (hx : x ∈ ends i) :
    connK ends E u x := by
  classical
  rw [edgeComponent, Finset.mem_filter] at hi
  exact hi.2 x hx

theorem canonicalGateCounter_K_zeroComponent :
    edgeComponent canonicalGateCounterEnds canonicalGateCounterK 3 = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  let x := (canonicalGateCounterEnds i).out.1
  have hx : x ∈ canonicalGateCounterEnds i :=
    Sym2.out_fst_mem (canonicalGateCounterEnds i)
  have h3x : (3 : Fin 7) ≠ x := by
    intro h
    have h3mem : (3 : Fin 7) ∈ canonicalGateCounterEnds i := by
      rw [h]
      exact hx
    exact canonicalGateCounter_K_no_incident_three i
      (edgeComponent_subset_support_generic _ _ _ hi) h3mem
  exact (not_connK_of_no_incident h3x
    canonicalGateCounter_K_no_incident_three)
      (edgeComponent_endpoint_conn_generic _ _ _ hi hx)

private theorem canonicalGateCounter_L_closed :
    ∀ i ∈ canonicalGateCounterL,
      ∀ a ∈ canonicalGateCounterEnds i, a ∈ ({1, 2} : Finset (Fin 7)) ->
      ∀ b ∈ canonicalGateCounterEnds i, b ∈ ({1, 2} : Finset (Fin 7)) := by
  exact canonicalGateCounter_closed _ _
    (Or.inr ⟨Or.inl rfl, rfl⟩)

private theorem canonicalGateCounter_L_not_conn_outside
    {x : Fin 7} (hx : x ∉ ({1, 2} : Finset (Fin 7))) :
    ¬ connK canonicalGateCounterEnds canonicalGateCounterL 1 x := by
  apply not_connK_of_closed_vertex_set
    (C := ({1, 2} : Finset (Fin 7))) (by simp) hx
  exact canonicalGateCounter_L_closed

private theorem canonicalGateCounter_L_edge_outside_of_ne_six
    (i : Fin 21) (hi : i ∈ canonicalGateCounterL) (hne : i ≠ 6) :
    ∃ x ∈ canonicalGateCounterEnds i,
      x ∉ ({1, 2} : Finset (Fin 7)) := by
  fin_cases i <;>
    simp [canonicalGateCounterL, canonicalGateCounterEnds] at hi hne ⊢

theorem canonicalGateCounter_L_kComponent :
    edgeComponent canonicalGateCounterEnds canonicalGateCounterL 1 = {6} := by
  classical
  apply Finset.Subset.antisymm
  · intro i hi
    by_cases h : i = 6
    · simp [h]
    · obtain ⟨x, hx, hxout⟩ :=
        canonicalGateCounter_L_edge_outside_of_ne_six i
          (by
            exact edgeComponent_subset_support_generic _ _ _ hi) h
      exfalso
      apply canonicalGateCounter_L_not_conn_outside hxout
      exact edgeComponent_endpoint_conn_generic _ _ _ hi hx
  · intro i hi
    have hi6 : i = 6 := by simpa using hi
    subst i
    exact mem_edgeComponent_of_endpoint
      (by simp [canonicalGateCounterL])
      (by simp [canonicalGateCounterEnds])

theorem canonicalGateCounter_transfer_is_canonical :
    edgeComponent canonicalGateCounterEnds canonicalGateCounterK 3 ∪
        edgeComponent canonicalGateCounterEnds canonicalGateCounterL 1 =
      canonicalGateCounterTransfer := by
  rw [canonicalGateCounter_K_zeroComponent,
    canonicalGateCounter_L_kComponent]
  rfl

theorem canonicalGateCounter_transfer_rows :
    canonicalGateCounterA ∆ canonicalGateCounterTransfer =
        canonicalGateCounterS ∧
      canonicalGateCounterB ∆ canonicalGateCounterTransfer =
        canonicalGateCounterR := by
  decide

theorem canonicalGateCounter_KL_gated :
    CanonicalGateCounterGated canonicalGateCounterK := by
  rw [CanonicalGateCounterGated, canonicalGateCounter_rows_partition.1]
  exact ⟨canonicalGateCounter_not_conn _ _
      (Or.inl ⟨Or.inl rfl, rfl⟩),
    canonicalGateCounter_not_conn _ _
      (Or.inr ⟨Or.inl rfl, rfl⟩)⟩

theorem canonicalGateCounter_SR_gated :
    CanonicalGateCounterGated canonicalGateCounterS := by
  rw [CanonicalGateCounterGated, canonicalGateCounter_rows_partition.2.2]
  exact ⟨canonicalGateCounter_not_conn _ _
      (Or.inl ⟨Or.inr rfl, rfl⟩),
    canonicalGateCounter_not_conn _ _
      (Or.inr ⟨Or.inr rfl, rfl⟩)⟩

private theorem canonicalGateCounter_A_conn :
    connK canonicalGateCounterEnds canonicalGateCounterA 1 3 := by
  have h12 : connK canonicalGateCounterEnds canonicalGateCounterA 1 2 :=
    Relation.ReflTransGen.single ⟨6, by simp [canonicalGateCounterA],
      by simp [canonicalGateCounterEnds], by simp [canonicalGateCounterEnds], by decide⟩
  have h25 : adjStep canonicalGateCounterEnds canonicalGateCounterA 2 5 :=
    ⟨13, by simp [canonicalGateCounterA], by simp [canonicalGateCounterEnds],
      by simp [canonicalGateCounterEnds], by decide⟩
  have h53 : adjStep canonicalGateCounterEnds canonicalGateCounterA 5 3 :=
    ⟨16, by simp [canonicalGateCounterA], by simp [canonicalGateCounterEnds],
      by simp [canonicalGateCounterEnds], by decide⟩
  exact (h12.tail h25).tail h53



theorem canonicalGate_cellStrengthening_not_sufficient :
    canonicalGateCounterK ∩ canonicalGateCounterA = canonicalGateCounterC0 ∧
      canonicalGateCounterK ∩ canonicalGateCounterB = canonicalGateCounterC1 ∧
      canonicalGateCounterL ∩ canonicalGateCounterA = canonicalGateCounterC2 ∧
      canonicalGateCounterL ∩ canonicalGateCounterB = canonicalGateCounterC3 ∧
      sources canonicalGateCounterEnds canonicalGateCounterC0 = {0, 1} ∧
      sources canonicalGateCounterEnds canonicalGateCounterC1 = ∅ ∧
      sources canonicalGateCounterEnds canonicalGateCounterC2 = {1, 2} ∧
      sources canonicalGateCounterEnds canonicalGateCounterC3 = ∅ ∧
      (edgeComponent canonicalGateCounterEnds canonicalGateCounterK 3 ∪
          edgeComponent canonicalGateCounterEnds canonicalGateCounterL 1 =
        canonicalGateCounterTransfer) ∧
      canonicalGateCounterA ∆ canonicalGateCounterTransfer =
        canonicalGateCounterS ∧
      canonicalGateCounterB ∆ canonicalGateCounterTransfer =
        canonicalGateCounterR ∧
      CanonicalGateCounterGated canonicalGateCounterK ∧
      CanonicalGateCounterGated canonicalGateCounterS ∧
      ¬ CanonicalGateCounterGated canonicalGateCounterA := by
  refine ⟨canonicalGateCounter_cells.1,
    canonicalGateCounter_cells.2.1,
    canonicalGateCounter_cells.2.2.1,
    canonicalGateCounter_cells.2.2.2,
    canonicalGateCounter_cell_sources.1,
    canonicalGateCounter_cell_sources.2.1,
    canonicalGateCounter_cell_sources.2.2.1,
    canonicalGateCounter_cell_sources.2.2.2,
    canonicalGateCounter_transfer_is_canonical,
    canonicalGateCounter_transfer_rows.1,
    canonicalGateCounter_transfer_rows.2,
    canonicalGateCounter_KL_gated,
    canonicalGateCounter_SR_gated, ?_⟩
  intro hA
  exact hA.1 canonicalGateCounter_A_conn

end StatMech.GrahamGHS.FourColor
