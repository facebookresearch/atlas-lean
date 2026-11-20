/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









import Code.Sharpness.BackboneSupportLexParityBridge
import Code.Sharpness.BackboneSelectorCompatible

open Finset SimpleGraph
open scoped BigOperators

set_option maxHeartbeats 1600000

namespace StatMech.Sharpness


def shbK4Edge.code : shbK4Edge → Sym2 (Fin 4)
  | .e01 => s(0, 1)
  | .e02 => s(0, 2)
  | .e03 => s(0, 3)
  | .e12 => s(1, 2)
  | .e13 => s(1, 3)
  | .e23 => s(2, 3)

theorem shbK4Edge.code_injective : Function.Injective shbK4Edge.code := by
  decide


def shbK4Graph (E : Finset shbK4Edge) : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet (↑(E.image shbK4Edge.code) : Set (Sym2 (Fin 4)))

instance (E : Finset shbK4Edge) : DecidableRel (shbK4Graph E).Adj := by
  intro x y
  simp only [shbK4Graph, SimpleGraph.fromEdgeSet_adj]
  infer_instance

@[simp] theorem shbK4Graph_mem_edgeSet_iff
    (E : Finset shbK4Edge) (e : Sym2 (Fin 4)) :
    e ∈ (shbK4Graph E).edgeSet ↔ e ∈ E.image shbK4Edge.code := by
  rw [shbK4Graph, SimpleGraph.edgeSet_fromEdgeSet]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    rw [Finset.mem_image] at h
    obtain ⟨k, _, rfl⟩ := h
    cases k <;> decide

@[simp] theorem shbK4Graph_edgeFinset
    (E : Finset shbK4Edge) :
    (shbK4Graph E).edgeFinset = E.image shbK4Edge.code := by
  ext e
  simp [SimpleGraph.mem_edgeFinset]


noncomputable def shbK4GraphEdgeEquiv (E : Finset shbK4Edge) :
    ↑E ≃ ↑(shbK4Graph E).edgeFinset where
  toFun k := ⟨k.1.code, by
    rw [shbK4Graph_edgeFinset]
    exact Finset.mem_image.mpr ⟨k.1, k.2, rfl⟩⟩
  invFun e := ⟨Classical.choose (Finset.mem_image.mp (by
    simpa [shbK4Graph_edgeFinset] using e.2)),
    (Classical.choose_spec (Finset.mem_image.mp (by
      simpa [shbK4Graph_edgeFinset] using e.2))).1⟩
  left_inv k := by
    apply Subtype.ext
    exact shbK4Edge.code_injective
      (Classical.choose_spec (Finset.mem_image.mp (by
      simpa [shbK4Graph_edgeFinset] using
          ((⟨k.1.code, by
              rw [shbK4Graph_edgeFinset]
              exact Finset.mem_image.mpr ⟨k.1, k.2, rfl⟩⟩ :
            ↑(shbK4Graph E).edgeFinset)).2))).2
  right_inv e := by
    apply Subtype.ext
    exact (Classical.choose_spec (Finset.mem_image.mp (by
      simpa [shbK4Graph_edgeFinset] using e.2))).2


def shbK4DirectPath (E : Finset shbK4Edge)
    (h03 : shbK4Edge.e03 ∈ E) : (shbK4Graph E).Path (0 : Fin 4) 3 := by
  let w : (shbK4Graph E).Walk (0 : Fin 4) 3 :=
    SimpleGraph.Walk.cons (by
      rw [shbK4Graph, SimpleGraph.fromEdgeSet_adj]
      constructor
      · exact Finset.mem_image.mpr ⟨shbK4Edge.e03, h03, rfl⟩
      · decide)
      SimpleGraph.Walk.nil
  exact ⟨w, by simp [w]⟩

@[simp] theorem shbK4DirectPath_support
    (E : Finset shbK4Edge) (h03 : shbK4Edge.e03 ∈ E) :
    (shbK4DirectPath E h03).1.support = [(0 : Fin 4), 3] := by
  simp [shbK4DirectPath]


def shbK4OddSupport (E : Finset shbK4Edge) (n : Current (Fin 4)) :
    Finset shbK4Edge :=
  E.filter fun k ↦ Odd (n k.code)

@[simp] theorem shbK4Edge_mem_oddSupport
    (E : Finset shbK4Edge) (n : Current (Fin 4)) (k : shbK4Edge) :
    k ∈ shbK4OddSupport E n ↔ k ∈ E ∧ Odd (n k.code) := by
  simp [shbK4OddSupport]

theorem shbK4Edge_mem_code_iff_incident (k : shbK4Edge) (v : Fin 4) :
    v ∈ k.code ↔ k.Incident v := by
  fin_cases k <;> fin_cases v <;> decide

theorem shbK4_incidentFlux_eq
    (E : Finset shbK4Edge) (n : Current (Fin 4)) (v : Fin 4) :
    incidentFlux (shbK4Graph E) n v =
      ∑ k ∈ E.filter (fun k ↦ k.Incident v), n k.code := by
  unfold incidentFlux
  rw [shbK4Graph_edgeFinset]
  rw [Finset.sum_filter]
  rw [Finset.sum_filter]
  rw [Finset.sum_image shbK4Edge.code_injective.injOn]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [shbK4Edge_mem_code_iff_incident]



theorem shbK4_sources_eq_boundary
    (E : Finset shbK4Edge) (n : Current (Fin 4)) :
    sources (shbK4Graph E) n = shbK4Boundary (shbK4OddSupport E n) := by
  ext v
  rw [mem_sources]
  unfold shbK4Boundary
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [shbK4_incidentFlux_eq]
  rw [Finset.odd_sum_iff_odd_card_odd]
  have hfilter :
      (E.filter (fun k ↦ k.Incident v)).filter (fun k ↦ Odd (n k.code)) =
        (shbK4OddSupport E n).filter (fun k ↦ k.Incident v) := by
    ext k
    simp [shbK4OddSupport, and_left_comm, and_assoc, and_comm]
  rw [hfilter]


def shbK4PathSupported {E : Finset shbK4Edge}
    (A : Finset shbK4Edge) {x y : Fin 4}
    (p : (shbK4Graph E).Path x y) : Prop :=
  ∀ e ∈ p.1.edges, e ∈ A.image shbK4Edge.code

instance {E A : Finset shbK4Edge} {x y : Fin 4}
    (p : (shbK4Graph E).Path x y) : Decidable (shbK4PathSupported A p) := by
  unfold shbK4PathSupported
  infer_instance

@[simp] private theorem shbK4Edge_code_mem_image_iff
    (A : Finset shbK4Edge) (k : shbK4Edge) :
    k.code ∈ A.image shbK4Edge.code ↔ k ∈ A := by
  constructor
  · intro h
    obtain ⟨k', hk', hcode⟩ := Finset.mem_image.mp h
    simpa [shbK4Edge.code_injective hcode] using hk'
  · exact fun hk ↦ Finset.mem_image.mpr ⟨k, hk, rfl⟩

@[simp] private theorem shbK4Edge_forall_eq_code_mem_image_iff
    (A : Finset shbK4Edge) (k : shbK4Edge) :
    (∀ e : Sym2 (Fin 4), e = k.code →
      e ∈ A.image shbK4Edge.code) ↔ k ∈ A := by
  constructor
  · intro h
    exact (shbK4Edge_code_mem_image_iff A k).mp (h k.code rfl)
  · intro hk e he
    subst e
    exact (shbK4Edge_code_mem_image_iff A k).mpr hk

private theorem shbK4_support_lt_direct_classification (l : List (Fin 4))
    (hnodup : l.Nodup) (hfirst : l.head? = some 0)
    (hlast : l.getLast? = some 3) (hlt : l < [(0 : Fin 4), 3]) :
    l = [0, 1, 2, 3] ∨ l = [0, 1, 3] ∨
      l = [0, 2, 1, 3] ∨ l = [0, 2, 3] := by
  rcases l with _ | ⟨a, l⟩
  · simp at hfirst
  simp only [List.head?_cons, Option.some.injEq] at hfirst
  subst a
  rcases l with _ | ⟨b, l⟩
  · simp at hlast
  have hlen : l.length ≤ 2 := by
    have hcard := hnodup.length_le_card
    simp at hcard
    omega
  rcases l with _ | ⟨c, l⟩
  · fin_cases b <;> simp_all
  rcases l with _ | ⟨d, l⟩
  · fin_cases b <;> fin_cases c <;> simp_all
  have : l = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp_all
  subst l
  fin_cases b <;> fin_cases c <;> fin_cases d <;> simp_all

private theorem shbK4PathSupported_0123_iff
    {E A : Finset shbK4Edge} (p : (shbK4Graph E).Path 0 3)
    (hp : p.1.support = [(0 : Fin 4), 1, 2, 3]) :
    shbK4PathSupported A p ↔
      ({shbK4Edge.e01, shbK4Edge.e12, shbK4Edge.e23} :
        Finset shbK4Edge) ⊆ A := by
  have hedges : p.1.edges =
      [shbK4Edge.e01.code, shbK4Edge.e12.code, shbK4Edge.e23.code] := by
    rw [SimpleGraph.Walk.edges_eq_zipWith_support, hp]
    decide
  unfold shbK4PathSupported
  rw [hedges]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    shbK4Edge_code_mem_image_iff, shbK4Edge_forall_eq_code_mem_image_iff,
    Finset.insert_subset_iff, Finset.singleton_subset_iff]

private theorem shbK4PathSupported_013_iff
    {E A : Finset shbK4Edge} (p : (shbK4Graph E).Path 0 3)
    (hp : p.1.support = [(0 : Fin 4), 1, 3]) :
    shbK4PathSupported A p ↔
      ({shbK4Edge.e01, shbK4Edge.e13} : Finset shbK4Edge) ⊆ A := by
  have hedges : p.1.edges =
      [shbK4Edge.e01.code, shbK4Edge.e13.code] := by
    rw [SimpleGraph.Walk.edges_eq_zipWith_support, hp]
    decide
  unfold shbK4PathSupported
  rw [hedges]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    shbK4Edge_code_mem_image_iff, shbK4Edge_forall_eq_code_mem_image_iff,
    Finset.insert_subset_iff, Finset.singleton_subset_iff]

private theorem shbK4PathSupported_0213_iff
    {E A : Finset shbK4Edge} (p : (shbK4Graph E).Path 0 3)
    (hp : p.1.support = [(0 : Fin 4), 2, 1, 3]) :
    shbK4PathSupported A p ↔
      ({shbK4Edge.e02, shbK4Edge.e12, shbK4Edge.e13} :
        Finset shbK4Edge) ⊆ A := by
  have hedges : p.1.edges =
      [shbK4Edge.e02.code, shbK4Edge.e12.code, shbK4Edge.e13.code] := by
    rw [SimpleGraph.Walk.edges_eq_zipWith_support, hp]
    decide
  unfold shbK4PathSupported
  rw [hedges]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    shbK4Edge_code_mem_image_iff, shbK4Edge_forall_eq_code_mem_image_iff,
    Finset.insert_subset_iff, Finset.singleton_subset_iff]

private theorem shbK4PathSupported_023_iff
    {E A : Finset shbK4Edge} (p : (shbK4Graph E).Path 0 3)
    (hp : p.1.support = [(0 : Fin 4), 2, 3]) :
    shbK4PathSupported A p ↔
      ({shbK4Edge.e02, shbK4Edge.e23} : Finset shbK4Edge) ⊆ A := by
  have hedges : p.1.edges =
      [shbK4Edge.e02.code, shbK4Edge.e23.code] := by
    rw [SimpleGraph.Walk.edges_eq_zipWith_support, hp]
    decide
  unfold shbK4PathSupported
  rw [hedges]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    shbK4Edge_code_mem_image_iff, shbK4Edge_forall_eq_code_mem_image_iff,
    Finset.insert_subset_iff, Finset.singleton_subset_iff]

private theorem shbK4DirectPath_supported_iff
    (E A : Finset shbK4Edge) (h03 : shbK4Edge.e03 ∈ E) :
    shbK4PathSupported A (shbK4DirectPath E h03) ↔
      shbK4Edge.e03 ∈ A := by
  have hedges : (shbK4DirectPath E h03).1.edges =
      [shbK4Edge.e03.code] := by
    rw [SimpleGraph.Walk.edges_eq_zipWith_support,
      shbK4DirectPath_support]
    decide
  unfold shbK4PathSupported
  rw [hedges]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq,
    shbK4Edge_code_mem_image_iff]

private theorem shbK4Graph_adj_of_edge
    (E : Finset shbK4Edge) (k : shbK4Edge) (hk : k ∈ E)
    {x y : Fin 4} (hcode : k.code = s(x, y)) (hne : x ≠ y) :
    (shbK4Graph E).Adj x y := by
  rw [shbK4Graph, SimpleGraph.fromEdgeSet_adj]
  exact ⟨Finset.mem_image.mpr ⟨k, hk, hcode⟩, hne⟩

private def shbK4Path0123 (E : Finset shbK4Edge)
    (h01 : shbK4Edge.e01 ∈ E) (h12 : shbK4Edge.e12 ∈ E)
    (h23 : shbK4Edge.e23 ∈ E) : (shbK4Graph E).Path 0 3 := by
  let w : (shbK4Graph E).Walk (0 : Fin 4) 3 :=
    SimpleGraph.Walk.cons
      (shbK4Graph_adj_of_edge E shbK4Edge.e01 h01
        (x := (0 : Fin 4)) (y := 1) (by decide) (by decide))
      (SimpleGraph.Walk.cons
        (shbK4Graph_adj_of_edge E shbK4Edge.e12 h12
          (x := (1 : Fin 4)) (y := 2) (by decide) (by decide))
        (SimpleGraph.Walk.cons
          (shbK4Graph_adj_of_edge E shbK4Edge.e23 h23
            (x := (2 : Fin 4)) (y := 3) (by decide) (by decide))
          SimpleGraph.Walk.nil))
  exact ⟨w, by simp [w]⟩

@[simp] private theorem shbK4Path0123_support
    (E : Finset shbK4Edge) (h01 : shbK4Edge.e01 ∈ E)
    (h12 : shbK4Edge.e12 ∈ E) (h23 : shbK4Edge.e23 ∈ E) :
    (shbK4Path0123 E h01 h12 h23).1.support = [(0 : Fin 4), 1, 2, 3] := by
  simp [shbK4Path0123]

private def shbK4Path013 (E : Finset shbK4Edge)
    (h01 : shbK4Edge.e01 ∈ E) (h13 : shbK4Edge.e13 ∈ E) :
    (shbK4Graph E).Path 0 3 := by
  let w : (shbK4Graph E).Walk (0 : Fin 4) 3 :=
    SimpleGraph.Walk.cons
      (shbK4Graph_adj_of_edge E shbK4Edge.e01 h01
        (x := (0 : Fin 4)) (y := 1) (by decide) (by decide))
      (SimpleGraph.Walk.cons
        (shbK4Graph_adj_of_edge E shbK4Edge.e13 h13
          (x := (1 : Fin 4)) (y := 3) (by decide) (by decide))
        SimpleGraph.Walk.nil)
  exact ⟨w, by simp [w]⟩

@[simp] private theorem shbK4Path013_support
    (E : Finset shbK4Edge) (h01 : shbK4Edge.e01 ∈ E)
    (h13 : shbK4Edge.e13 ∈ E) :
    (shbK4Path013 E h01 h13).1.support = [(0 : Fin 4), 1, 3] := by
  simp [shbK4Path013]

private def shbK4Path0213 (E : Finset shbK4Edge)
    (h02 : shbK4Edge.e02 ∈ E) (h12 : shbK4Edge.e12 ∈ E)
    (h13 : shbK4Edge.e13 ∈ E) : (shbK4Graph E).Path 0 3 := by
  let w : (shbK4Graph E).Walk (0 : Fin 4) 3 :=
    SimpleGraph.Walk.cons
      (shbK4Graph_adj_of_edge E shbK4Edge.e02 h02
        (x := (0 : Fin 4)) (y := 2) (by decide) (by decide))
      (SimpleGraph.Walk.cons
        (shbK4Graph_adj_of_edge E shbK4Edge.e12 h12
          (x := (2 : Fin 4)) (y := 1) (by decide) (by decide))
        (SimpleGraph.Walk.cons
          (shbK4Graph_adj_of_edge E shbK4Edge.e13 h13
            (x := (1 : Fin 4)) (y := 3) (by decide) (by decide))
          SimpleGraph.Walk.nil))
  exact ⟨w, by simp [w]⟩

@[simp] private theorem shbK4Path0213_support
    (E : Finset shbK4Edge) (h02 : shbK4Edge.e02 ∈ E)
    (h12 : shbK4Edge.e12 ∈ E) (h13 : shbK4Edge.e13 ∈ E) :
    (shbK4Path0213 E h02 h12 h13).1.support = [(0 : Fin 4), 2, 1, 3] := by
  simp [shbK4Path0213]

private def shbK4Path023 (E : Finset shbK4Edge)
    (h02 : shbK4Edge.e02 ∈ E) (h23 : shbK4Edge.e23 ∈ E) :
    (shbK4Graph E).Path 0 3 := by
  let w : (shbK4Graph E).Walk (0 : Fin 4) 3 :=
    SimpleGraph.Walk.cons
      (shbK4Graph_adj_of_edge E shbK4Edge.e02 h02
        (x := (0 : Fin 4)) (y := 2) (by decide) (by decide))
      (SimpleGraph.Walk.cons
        (shbK4Graph_adj_of_edge E shbK4Edge.e23 h23
          (x := (2 : Fin 4)) (y := 3) (by decide) (by decide))
        SimpleGraph.Walk.nil)
  exact ⟨w, by simp [w]⟩

@[simp] private theorem shbK4Path023_support
    (E : Finset shbK4Edge) (h02 : shbK4Edge.e02 ∈ E)
    (h23 : shbK4Edge.e23 ∈ E) :
    (shbK4Path023 E h02 h23).1.support = [(0 : Fin 4), 2, 3] := by
  simp [shbK4Path023]

theorem shbK4_isBackboneOf_iff_pathSupported
    (E : Finset shbK4Edge) (n : Current (Fin 4)) {x y : Fin 4}
    (p : (shbK4Graph E).Path x y) :
    shb_IsBackboneOf (shbK4Graph E) n x y p ↔
      shbK4PathSupported (shbK4OddSupport E n) p := by
  constructor
  · intro hp e he
    have heG := p.1.edges_subset_edgeSet he
    rw [shbK4Graph_mem_edgeSet_iff] at heG
    obtain ⟨k, hkE, hcode⟩ := Finset.mem_image.mp heG
    apply Finset.mem_image.mpr
    refine ⟨k, ?_, hcode⟩
    apply Finset.mem_filter.mpr
    refine ⟨hkE, ?_⟩
    rw [hcode]
    exact hp e he
  · intro hp e he
    obtain ⟨k, hkA, hcode⟩ := Finset.mem_image.mp (hp e he)
    rw [← hcode]
    exact (Finset.mem_filter.mp hkA).2


theorem shbK4_selectsDirect03_iff_realized_minimal
    (E A : Finset shbK4Edge) (h03 : shbK4Edge.e03 ∈ E) (hAE : A ⊆ E) :
    shbK4SelectsDirect03 A ↔
      shbK4Boundary A = {0, 3} ∧
        shbK4PathSupported A (shbK4DirectPath E h03) ∧
        ∀ q : (shbK4Graph E).Path (0 : Fin 4) 3,
          q.1.support < (shbK4DirectPath E h03).1.support →
            ¬ shbK4PathSupported A q := by
  constructor
  · intro hselect
    unfold shbK4SelectsDirect03 at hselect
    rcases hselect with ⟨hboundary, h03A, h013, h0123, h0213, h023⟩
    refine ⟨hboundary, (shbK4DirectPath_supported_iff E A h03).2 h03A, ?_⟩
    intro q hlt hsupported
    rw [shbK4DirectPath_support] at hlt
    have hfirst : q.1.support.head? = some 0 := by
      rw [← q.1.cons_tail_support]
      rfl
    have hlast : q.1.support.getLast? = some 3 := by
      rw [List.getLast?_eq_getLast_of_ne_nil q.1.support_ne_nil,
        q.1.getLast_support]
    rcases shbK4_support_lt_direct_classification q.1.support
        q.2.support_nodup hfirst hlast hlt with hq | hq | hq | hq
    · exact h0123 ((shbK4PathSupported_0123_iff q hq).1 hsupported)
    · exact h013 ((shbK4PathSupported_013_iff q hq).1 hsupported)
    · exact h0213 ((shbK4PathSupported_0213_iff q hq).1 hsupported)
    · exact h023 ((shbK4PathSupported_023_iff q hq).1 hsupported)
  · rintro ⟨hboundary, hsupported, hminimal⟩
    unfold shbK4SelectsDirect03
    refine ⟨hboundary, (shbK4DirectPath_supported_iff E A h03).1 hsupported,
      ?_, ?_, ?_, ?_⟩
    · intro hsubset
      have h01A : shbK4Edge.e01 ∈ A := hsubset (by simp)
      have h13A : shbK4Edge.e13 ∈ A := hsubset (by simp)
      let q := shbK4Path013 E (hAE h01A) (hAE h13A)
      apply hminimal q
      · simp [q]
        decide
      · exact (shbK4PathSupported_013_iff q (by simp [q])).2 hsubset
    · intro hsubset
      have h01A : shbK4Edge.e01 ∈ A := hsubset (by simp)
      have h12A : shbK4Edge.e12 ∈ A := hsubset (by simp)
      have h23A : shbK4Edge.e23 ∈ A := hsubset (by simp)
      let q := shbK4Path0123 E (hAE h01A) (hAE h12A) (hAE h23A)
      apply hminimal q
      · simp [q]
        decide
      · exact (shbK4PathSupported_0123_iff q (by simp [q])).2 hsubset
    · intro hsubset
      have h02A : shbK4Edge.e02 ∈ A := hsubset (by simp)
      have h12A : shbK4Edge.e12 ∈ A := hsubset (by simp)
      have h13A : shbK4Edge.e13 ∈ A := hsubset (by simp)
      let q := shbK4Path0213 E (hAE h02A) (hAE h12A) (hAE h13A)
      apply hminimal q
      · simp [q]
        decide
      · exact (shbK4PathSupported_0213_iff q (by simp [q])).2 hsubset
    · intro hsubset
      have h02A : shbK4Edge.e02 ∈ A := hsubset (by simp)
      have h23A : shbK4Edge.e23 ∈ A := hsubset (by simp)
      let q := shbK4Path023 E (hAE h02A) (hAE h23A)
      apply hminimal q
      · simp [q]
        decide
      · exact (shbK4PathSupported_023_iff q (by simp [q])).2 hsubset



theorem shb_backboneSelectSupport_eq_some_iff
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : Current V) (x y : V) (p : G.Path x y) :
    shb_backboneSelectSupport G n x y = some p ↔
      shb_IsBackboneOf G n x y p ∧
        ∀ q : G.Path x y, q.1.support < p.1.support →
          ¬ shb_IsBackboneOf G n x y q := by
  letI : LinearOrder (G.Path x y) := shb_supportPathOrder G x y
  constructor
  · intro hsel
    unfold shb_backboneSelectSupport at hsel
    split at hsel
    · rename_i hne
      have hmin : (shb_backboneSet G n x y).min' hne = p :=
        Option.some.inj hsel
      have hp : p ∈ shb_backboneSet G n x y := by
        rw [← hmin]
        exact Finset.min'_mem _ _
      refine ⟨(shb_mem_backboneSet G n x y p).mp hp, ?_⟩
      intro q hqp hq
      have hqmem : q ∈ shb_backboneSet G n x y :=
        (shb_mem_backboneSet G n x y q).mpr hq
      have hle : (shb_backboneSet G n x y).min' hne ≤ q :=
        Finset.min'_le _ _ hqmem
      rw [hmin] at hle
      exact (not_lt_of_ge hle) hqp
    · simp at hsel
  · rintro ⟨hp, hbefore⟩
    have hpmem : p ∈ shb_backboneSet G n x y :=
      (shb_mem_backboneSet G n x y p).mpr hp
    have hne : (shb_backboneSet G n x y).Nonempty := ⟨p, hpmem⟩
    unfold shb_backboneSelectSupport
    rw [dif_pos hne]
    apply congrArg some
    apply le_antisymm
    · exact Finset.min'_le _ _ hpmem
    · apply not_lt.mp
      intro hlt
      exact hbefore _ hlt
        ((shb_mem_backboneSet G n x y _).mp (Finset.min'_mem _ _))



theorem shbK4_source_selector_fiber_iff
    (E : Finset shbK4Edge) (h03 : shbK4Edge.e03 ∈ E)
    (n : Current (Fin 4)) :
    (sources (shbK4Graph E) n = {(0 : Fin 4), 3} ∧
        shb_backboneSelectSupport (shbK4Graph E) n 0 3 =
          some (shbK4DirectPath E h03)) ↔
      shbK4SelectsDirect03 (shbK4OddSupport E n) := by
  rw [shbK4_selectsDirect03_iff_realized_minimal E
    (shbK4OddSupport E n) h03 (Finset.filter_subset _ _)]
  rw [shb_backboneSelectSupport_eq_some_iff]
  rw [shbK4_sources_eq_boundary]
  simp_rw [shbK4_isBackboneOf_iff_pathSupported]



theorem shbK4Graph_mono {E F : Finset shbK4Edge} (hEF : E ⊆ F) :
    shbK4Graph E ≤ shbK4Graph F := by
  intro x y hxy
  rw [shbK4Graph, SimpleGraph.fromEdgeSet_adj] at hxy ⊢
  refine ⟨?_, hxy.2⟩
  obtain ⟨k, hkE, hk⟩ := Finset.mem_image.mp hxy.1
  exact Finset.mem_image.mpr ⟨k, hEF hkE, hk⟩

theorem shbK4H_subset_shbK4G : shbK4H ⊆ shbK4G := by
  exact Finset.ssubset_iff_subset_ne.mp shbK4H_ssubset_shbK4G |>.1


theorem shbK4DirectPath_mapLe :
    shb_pathMapLe (shbK4Graph_mono shbK4H_subset_shbK4G)
        (shbK4DirectPath shbK4H (by decide)) =
      shbK4DirectPath shbK4G (by decide) := by
  apply Subtype.ext
  apply SimpleGraph.Walk.support_injective
  simp only [shb_pathMapLe, SimpleGraph.Walk.support_mapLe_eq_support,
    shbK4DirectPath_support]



theorem shbK4_ofEdgeFun_source_selector_fiber_iff
    (E : Finset shbK4Edge) (h03 : shbK4Edge.e03 ∈ E)
    (m : (shbK4Graph E).edgeFinset → ℕ) :
    (sources (shbK4Graph E) (ofEdgeFun (shbK4Graph E) m) =
          {(0 : Fin 4), 3} ∧
        shb_backboneSelectSupport (shbK4Graph E)
            (ofEdgeFun (shbK4Graph E) m) 0 3 =
          some (shbK4DirectPath E h03)) ↔
      shbK4SelectsDirect03
        (shbK4OddSupport E (ofEdgeFun (shbK4Graph E) m)) :=
  shbK4_source_selector_fiber_iff E h03 _


theorem shbK4_weight_ofEdgeFun_one
    (E : Finset shbK4Edge) (x : ℝ)
    (m : (shbK4Graph E).edgeFinset → ℕ) :
    weight (shbK4Graph E) x (fun _ ↦ 1)
        (ofEdgeFun (shbK4Graph E) m) =
      ∏ k : ↑E,
        x ^ (m (shbK4GraphEdgeEquiv E k)) /
          (m (shbK4GraphEdgeEquiv E k)).factorial := by
  rw [weight_ofEdgeFun]
  simp only [mul_one]
  exact (Equiv.prod_comp (shbK4GraphEdgeEquiv E)
    (fun e : (shbK4Graph E).edgeFinset ↦
      x ^ (m e) / (m e).factorial)).symm

end StatMech.Sharpness
