/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.Z2GaugeSubsystem
import Code.FrontierA.Z2GaugeCubicalWilson
import Code.FrontierA.Z2GaugeRectangularThermodynamic
import Code.FrontierA.RectangularBlockTiling










open scoped BigOperators symmDiff
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false
set_option linter.flexible false

namespace StatMech.FrontierA

noncomputable section
local instance z2GaugeCubicalGluingPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {E P : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]

theorem gaugeSurfaceBoundary_union_of_disjoint
    (incidence : P → Finset E) {A B : Finset P} (hAB : Disjoint A B) :
    gaugeSurfaceBoundary incidence (A ∪ B) =
      gaugeSurfaceBoundary incidence A ∆ gaugeSurfaceBoundary incidence B := by
  ext e
  rw [mem_gaugeSurfaceBoundary]
  rw [mem_symmDiff, mem_gaugeSurfaceBoundary, mem_gaugeSurfaceBoundary]
  have hcount : plaquetteIncidenceCount incidence (A ∪ B) e =
      plaquetteIncidenceCount incidence A e + plaquetteIncidenceCount incidence B e := by
    unfold plaquetteIncidenceCount
    rw [Finset.sum_union hAB]
  rw [hcount, Nat.even_add]
  tauto

variable {Esmall Ebig Psmall Pbig : Type*}
  [Fintype Esmall] [DecidableEq Esmall] [Fintype Ebig] [DecidableEq Ebig]
  [Fintype Psmall] [DecidableEq Psmall] [Fintype Pbig] [DecidableEq Pbig]

theorem plaquetteIncidenceCount_map_apply
    (incidenceSmall : Psmall → Finset Esmall)
    (incidenceBig : Pbig → Finset Ebig)
    (eEmb : Esmall ↪ Ebig) (pEmb : Psmall ↪ Pbig)
    (hinc : ∀ p, incidenceBig (pEmb p) = (incidenceSmall p).map eEmb)
    (A : Finset Psmall) (e : Esmall) :
    plaquetteIncidenceCount incidenceBig (A.map pEmb) (eEmb e) =
      plaquetteIncidenceCount incidenceSmall A e := by
  unfold plaquetteIncidenceCount
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro p hp
  rw [hinc]
  simp

theorem plaquetteIncidenceCount_map_apply_of_not_mem_range
    (incidenceSmall : Psmall → Finset Esmall)
    (incidenceBig : Pbig → Finset Ebig)
    (eEmb : Esmall ↪ Ebig) (pEmb : Psmall ↪ Pbig)
    (hinc : ∀ p, incidenceBig (pEmb p) = (incidenceSmall p).map eEmb)
    (A : Finset Psmall) {e : Ebig} (he : e ∉ Set.range eEmb) :
    plaquetteIncidenceCount incidenceBig (A.map pEmb) e = 0 := by
  unfold plaquetteIncidenceCount
  apply Finset.sum_eq_zero
  intro q hq
  rw [Finset.mem_map] at hq
  obtain ⟨p, hp, rfl⟩ := hq
  rw [hinc]
  have hnot : ¬∃ x ∈ incidenceSmall p, eEmb x = e :=
    fun ⟨x, _, hxe⟩ => he ⟨x, hxe⟩
  simp [Finset.mem_map, hnot]

theorem gaugeSurfaceBoundary_map
    (incidenceSmall : Psmall → Finset Esmall)
    (incidenceBig : Pbig → Finset Ebig)
    (eEmb : Esmall ↪ Ebig) (pEmb : Psmall ↪ Pbig)
    (hinc : ∀ p, incidenceBig (pEmb p) = (incidenceSmall p).map eEmb)
    (A : Finset Psmall) :
    gaugeSurfaceBoundary incidenceBig (A.map pEmb) =
      (gaugeSurfaceBoundary incidenceSmall A).map eEmb := by
  ext e
  by_cases he : e ∈ Set.range eEmb
  · obtain ⟨e', rfl⟩ := he
    rw [mem_gaugeSurfaceBoundary, plaquetteIncidenceCount_map_apply
      incidenceSmall incidenceBig eEmb pEmb hinc]
    simp [mem_gaugeSurfaceBoundary]
  · rw [mem_gaugeSurfaceBoundary,
      plaquetteIncidenceCount_map_apply_of_not_mem_range incidenceSmall
        incidenceBig eEmb pEmb hinc A he]
    have hnotmap : e ∉ (gaugeSurfaceBoundary incidenceSmall A).map eEmb := by
      intro hmem
      rw [Finset.mem_map] at hmem
      obtain ⟨e', _, heq⟩ := hmem
      exact he ⟨e', heq⟩
    simp [hnotmap]


def finOffsetEmbedding {n N : Nat} (offset : Nat) (h : offset + n ≤ N) :
    Fin n ↪ Fin N :=
  (Fin.natAddEmb offset).trans (Fin.castLEEmb h)

@[simp] theorem finOffsetEmbedding_val {n N : Nat} (offset : Nat)
    (h : offset + n ≤ N) (i : Fin n) :
    (finOffsetEmbedding offset h i).val = offset + i.val := rfl

@[simp] theorem finOffsetEmbedding_castSucc {n N : Nat} (offset : Nat)
    (h : offset + n ≤ N) (i : Fin n) :
    finOffsetEmbedding offset (by omega : offset + (n + 1) ≤ N + 1) i.castSucc =
      (finOffsetEmbedding offset h i).castSucc := by
  apply Fin.ext
  rfl

@[simp] theorem finOffsetEmbedding_succ {n N : Nat} (offset : Nat)
    (h : offset + n ≤ N) (i : Fin n) :
    finOffsetEmbedding offset (by omega : offset + (n + 1) ≤ N + 1) i.succ =
      (finOffsetEmbedding offset h i).succ := by
  apply Fin.ext
  rfl

@[simp] theorem finOffsetEmbedding_castSucc' {n N : Nat} (offset : Nat)
    (h : offset + (n + 1) ≤ N + 1) (i : Fin n) :
    finOffsetEmbedding offset h i.castSucc =
      (finOffsetEmbedding offset (by omega) i).castSucc := by
  apply Fin.ext
  rfl

@[simp] theorem finOffsetEmbedding_succ' {n N : Nat} (offset : Nat)
    (h : offset + (n + 1) ≤ N + 1) (i : Fin n) :
    finOffsetEmbedding offset h i.succ =
      (finOffsetEmbedding offset (by omega) i).succ := by
  apply Fin.ext
  rfl

def cubicalEdgeChart {a b c A B C : Nat} (ox oy oz : Nat)
    (hx : ox + a ≤ A) (hy : oy + b ≤ B) (hz : oz + c ≤ C) :
    CubicalEdge a b c ↪ CubicalEdge A B C where
  toFun
    | .x i j k => .x (finOffsetEmbedding ox hx i)
        (finOffsetEmbedding oy (by omega) j)
        (finOffsetEmbedding oz (by omega) k)
    | .y i j k => .y (finOffsetEmbedding ox (by omega) i)
        (finOffsetEmbedding oy hy j)
        (finOffsetEmbedding oz (by omega) k)
    | .z i j k => .z (finOffsetEmbedding ox (by omega) i)
        (finOffsetEmbedding oy (by omega) j)
        (finOffsetEmbedding oz hz k)
  inj' := by
    intro e f hef
    cases e <;> cases f <;>
      simp only [CubicalEdge.x.injEq, CubicalEdge.y.injEq,
        CubicalEdge.z.injEq, reduceCtorEq] at hef ⊢ <;>
      simp_all [finOffsetEmbedding]

def cubicalPlaquetteChart {a b c A B C : Nat} (ox oy oz : Nat)
    (hx : ox + a ≤ A) (hy : oy + b ≤ B) (hz : oz + c ≤ C) :
    CubicalPlaquette a b c ↪ CubicalPlaquette A B C where
  toFun
    | .xy i j k => .xy (finOffsetEmbedding ox hx i)
        (finOffsetEmbedding oy hy j)
        (finOffsetEmbedding oz (by omega) k)
    | .xz i j k => .xz (finOffsetEmbedding ox hx i)
        (finOffsetEmbedding oy (by omega) j)
        (finOffsetEmbedding oz hz k)
    | .yz i j k => .yz (finOffsetEmbedding ox (by omega) i)
        (finOffsetEmbedding oy hy j)
        (finOffsetEmbedding oz hz k)
  inj' := by
    intro p q hpq
    cases p <;> cases q <;>
      simp only [CubicalPlaquette.xy.injEq, CubicalPlaquette.xz.injEq,
        CubicalPlaquette.yz.injEq, reduceCtorEq] at hpq ⊢ <;>
      simp_all [finOffsetEmbedding]

theorem cubicalPlaquetteIncidence_chart {a b c A B C : Nat}
    (ox oy oz : Nat) (hx : ox + a ≤ A) (hy : oy + b ≤ B)
    (hz : oz + c ≤ C) (p : CubicalPlaquette a b c) :
    cubicalPlaquetteIncidence
        (cubicalPlaquetteChart ox oy oz hx hy hz p) =
      (cubicalPlaquetteIncidence p).map
        (cubicalEdgeChart ox oy oz hx hy hz) := by
  cases p <;>
    simp [cubicalPlaquetteIncidence, cubicalPlaquetteChart,
      cubicalEdgeChart]



theorem cubicalXYWilsonExpectation_le_chart {a b c A B C : Nat}
    (ox oy oz : Nat) (hx : ox + a ≤ A) (hy : oy + b ≤ B)
    (hz : oz + c ≤ C) {beta : Real} (hbeta : 0 ≤ beta)
    (z : Fin (c + 1)) :
    gaugeWilsonExpectation cubicalPlaquetteIncidence
        (fun _ : CubicalPlaquette a b c => beta) (cubicalXYLoop z) ≤
      gaugeWilsonExpectation cubicalPlaquetteIncidence
        (fun _ : CubicalPlaquette A B C => beta)
        ((cubicalXYLoop z).map (cubicalEdgeChart ox oy oz hx hy hz)) := by
  let eEmb := cubicalEdgeChart ox oy oz hx hy hz
  let pEmb := cubicalPlaquetteChart ox oy oz hx hy hz
  let Ksmall := fun _ : CubicalPlaquette a b c => beta
  have hzero : ∀ p, 0 ≤ extendGaugeCoupling pEmb Ksmall p := by
    intro p
    unfold extendGaugeCoupling
    cases (embeddingSplitEquiv pEmb).symm p with
    | inl q => exact hbeta
    | inr q => exact le_rfl
  have hle : ∀ p, extendGaugeCoupling pEmb Ksmall p ≤ beta := by
    intro p
    unfold extendGaugeCoupling
    cases (embeddingSplitEquiv pEmb).symm p with
    | inl q => exact le_rfl
    | inr q => exact hbeta
  calc
    gaugeWilsonExpectation cubicalPlaquetteIncidence Ksmall (cubicalXYLoop z) =
        gaugeWilsonExpectation cubicalPlaquetteIncidence
          (extendGaugeCoupling pEmb Ksmall) ((cubicalXYLoop z).map eEmb) :=
      (gaugeWilsonExpectation_extendGaugeCoupling
        cubicalPlaquetteIncidence cubicalPlaquetteIncidence eEmb pEmb
        (cubicalPlaquetteIncidence_chart ox oy oz hx hy hz) Ksmall
        (cubicalXYLoop z)).symm
    _ ≤ gaugeWilsonExpectation cubicalPlaquetteIncidence
          (fun _ : CubicalPlaquette A B C => beta)
          ((cubicalXYLoop z).map eEmb) :=
      gaugeWilsonExpectation_mono_coupling cubicalPlaquetteIncidence
        (extendGaugeCoupling pEmb Ksmall) (fun _ => beta) hzero hle _

theorem cubicalXYSheet_horizontal_union (m l n c₁ c₂ C : Nat)
    (hc₁ : c₁ ≤ C) (hc₂ : c₂ ≤ C) :
    (cubicalXYSheet (a := m) (b := n) (c := c₁) (0 : Fin (c₁ + 1))).map
          (cubicalPlaquetteChart 0 0 0 (by omega) (by omega) (by omega)) ∪
      (cubicalXYSheet (a := l) (b := n) (c := c₂) (0 : Fin (c₂ + 1))).map
          (cubicalPlaquetteChart m 0 0 (by omega) (by omega) (by omega)) =
        cubicalXYSheet (a := m + l) (b := n) (c := C) (0 : Fin (C + 1)) := by
  ext p
  cases p with
  | xy i j k =>
      simp [cubicalXYSheet, cubicalPlaquetteChart, finOffsetEmbedding]
      constructor
      · rintro (⟨_, _, hk⟩ | ⟨_, _, hk⟩) <;> exact hk
      · intro hk
        by_cases hi : i.val < m
        · left
          refine ⟨⟨⟨i.val, hi⟩, ?_⟩, ⟨⟨j.val, j.isLt⟩, ?_⟩, hk⟩
          · apply Fin.ext
            simp [finOffsetEmbedding]
          · apply Fin.ext
            simp [finOffsetEmbedding]
        · right
          have hil : i.val - m < l := by omega
          refine ⟨⟨⟨i.val - m, hil⟩, ?_⟩, ⟨⟨j.val, j.isLt⟩, ?_⟩, hk⟩
          · apply Fin.ext
            simp [finOffsetEmbedding]
            omega
          · apply Fin.ext
            simp [finOffsetEmbedding]
  | xz i j k => simp [cubicalXYSheet, cubicalPlaquetteChart]
  | yz i j k => simp [cubicalXYSheet, cubicalPlaquetteChart]

theorem cubicalXYSheet_horizontal_disjoint (m l n c₁ c₂ C : Nat)
    (hc₁ : c₁ ≤ C) (hc₂ : c₂ ≤ C) :
    Disjoint
      ((cubicalXYSheet (a := m) (b := n) (c := c₁) (0 : Fin (c₁ + 1))).map
        (cubicalPlaquetteChart (A := m + l) (B := n) (C := C)
          0 0 0 (by omega) (by omega) (by omega)))
      ((cubicalXYSheet (a := l) (b := n) (c := c₂) (0 : Fin (c₂ + 1))).map
        (cubicalPlaquetteChart (A := m + l) (B := n) (C := C)
          m 0 0 (by omega) (by omega) (by omega))) := by
  rw [Finset.disjoint_left]
  intro p hp₁ hp₂
  cases p with
  | xy i j k =>
      simp [cubicalXYSheet, cubicalPlaquetteChart, finOffsetEmbedding] at hp₁ hp₂
      obtain ⟨⟨x₁, _⟩, hx₁⟩ := hp₁.1
      obtain ⟨⟨x₂, _⟩, hx₂⟩ := hp₂.1
      have hv₁ := congrArg Fin.val hx₁
      have hv₂ := congrArg Fin.val hx₂
      simp at hv₁ hv₂
      omega
  | xz i j k => simp [cubicalXYSheet, cubicalPlaquetteChart] at hp₁
  | yz i j k => simp [cubicalXYSheet, cubicalPlaquetteChart] at hp₁

theorem cubicalXYLoop_horizontal_symmDiff (m l n c₁ c₂ C : Nat)
    (hc₁ : c₁ ≤ C) (hc₂ : c₂ ≤ C) :
    (cubicalXYLoop (a := m) (b := n) (c := c₁) (0 : Fin (c₁ + 1))).map
          (cubicalEdgeChart (A := m + l) (B := n) (C := C)
            0 0 0 (by omega) (by omega) (by omega)) ∆
      (cubicalXYLoop (a := l) (b := n) (c := c₂) (0 : Fin (c₂ + 1))).map
          (cubicalEdgeChart (A := m + l) (B := n) (C := C)
            m 0 0 (by omega) (by omega) (by omega)) =
        cubicalXYLoop (a := m + l) (b := n) (c := C) (0 : Fin (C + 1)) := by
  let P₁ := cubicalPlaquetteChart (a := m) (b := n) (c := c₁)
    (A := m + l) (B := n) (C := C)
    0 0 0 (by omega) (by omega) (by omega)
  let P₂ := cubicalPlaquetteChart (a := l) (b := n) (c := c₂)
    (A := m + l) (B := n) (C := C)
    m 0 0 (by omega) (by omega) (by omega)
  let E₁ := cubicalEdgeChart (a := m) (b := n) (c := c₁)
    (A := m + l) (B := n) (C := C)
    0 0 0 (by omega) (by omega) (by omega)
  let E₂ := cubicalEdgeChart (a := l) (b := n) (c := c₂)
    (A := m + l) (B := n) (C := C)
    m 0 0 (by omega) (by omega) (by omega)
  let S₁ := (cubicalXYSheet (a := m) (b := n) (c := c₁)
    (0 : Fin (c₁ + 1))).map P₁
  let S₂ := (cubicalXYSheet (a := l) (b := n) (c := c₂)
    (0 : Fin (c₂ + 1))).map P₂
  change (gaugeSurfaceBoundary cubicalPlaquetteIncidence
      (cubicalXYSheet (0 : Fin (c₁ + 1)))).map E₁ ∆
    (gaugeSurfaceBoundary cubicalPlaquetteIncidence
      (cubicalXYSheet (0 : Fin (c₂ + 1)))).map E₂ = _
  rw [← gaugeSurfaceBoundary_map cubicalPlaquetteIncidence
      cubicalPlaquetteIncidence E₁ P₁
      (cubicalPlaquetteIncidence_chart 0 0 0 _ _ _),
    ← gaugeSurfaceBoundary_map cubicalPlaquetteIncidence
      cubicalPlaquetteIncidence E₂ P₂
      (cubicalPlaquetteIncidence_chart m 0 0 _ _ _)]
  change gaugeSurfaceBoundary cubicalPlaquetteIncidence S₁ ∆
    gaugeSurfaceBoundary cubicalPlaquetteIncidence S₂ = _
  rw [← gaugeSurfaceBoundary_union_of_disjoint cubicalPlaquetteIncidence
    (cubicalXYSheet_horizontal_disjoint m l n c₁ c₂ C hc₁ hc₂)]
  have hunion : S₁ ∪ S₂ =
      cubicalXYSheet (a := m + l) (b := n) (c := C) (0 : Fin (C + 1)) :=
    cubicalXYSheet_horizontal_union m l n c₁ c₂ C hc₁ hc₂
  rw [hunion]
  rfl

theorem cubicalXYSheet_vertical_union (m n k c₁ c₂ C : Nat)
    (hc₁ : c₁ ≤ C) (hc₂ : c₂ ≤ C) :
    (cubicalXYSheet (a := m) (b := n) (c := c₁) (0 : Fin (c₁ + 1))).map
          (cubicalPlaquetteChart 0 0 0 (by omega) (by omega) (by omega)) ∪
      (cubicalXYSheet (a := m) (b := k) (c := c₂) (0 : Fin (c₂ + 1))).map
          (cubicalPlaquetteChart 0 n 0 (by omega) (by omega) (by omega)) =
        cubicalXYSheet (a := m) (b := n + k) (c := C) (0 : Fin (C + 1)) := by
  ext p
  cases p with
  | xy i j z =>
      simp [cubicalXYSheet, cubicalPlaquetteChart, finOffsetEmbedding]
      constructor
      · rintro (⟨_, _, hz⟩ | ⟨_, _, hz⟩) <;> exact hz
      · intro hz
        by_cases hj : j.val < n
        · left
          refine ⟨⟨⟨i.val, i.isLt⟩, ?_⟩, ⟨⟨j.val, hj⟩, ?_⟩, hz⟩
          · apply Fin.ext
            simp
          · apply Fin.ext
            simp
        · right
          have hjk : j.val - n < k := by omega
          refine ⟨⟨⟨i.val, i.isLt⟩, ?_⟩, ⟨⟨j.val - n, hjk⟩, ?_⟩, hz⟩
          · apply Fin.ext
            simp
          · apply Fin.ext
            simp
            omega
  | xz i j z => simp [cubicalXYSheet, cubicalPlaquetteChart]
  | yz i j z => simp [cubicalXYSheet, cubicalPlaquetteChart]

theorem cubicalXYSheet_vertical_disjoint (m n k c₁ c₂ C : Nat)
    (hc₁ : c₁ ≤ C) (hc₂ : c₂ ≤ C) :
    Disjoint
      ((cubicalXYSheet (a := m) (b := n) (c := c₁) (0 : Fin (c₁ + 1))).map
        (cubicalPlaquetteChart (A := m) (B := n + k) (C := C)
          0 0 0 (by omega) (by omega) (by omega)))
      ((cubicalXYSheet (a := m) (b := k) (c := c₂) (0 : Fin (c₂ + 1))).map
        (cubicalPlaquetteChart (A := m) (B := n + k) (C := C)
          0 n 0 (by omega) (by omega) (by omega))) := by
  rw [Finset.disjoint_left]
  intro p hp₁ hp₂
  cases p with
  | xy i j z =>
      simp [cubicalXYSheet, cubicalPlaquetteChart, finOffsetEmbedding] at hp₁ hp₂
      obtain ⟨⟨y₁, _⟩, hy₁⟩ := hp₁.2.1
      obtain ⟨⟨y₂, _⟩, hy₂⟩ := hp₂.2.1
      have hv₁ := congrArg Fin.val hy₁
      have hv₂ := congrArg Fin.val hy₂
      simp at hv₁ hv₂
      omega
  | xz i j z => simp [cubicalXYSheet, cubicalPlaquetteChart] at hp₁
  | yz i j z => simp [cubicalXYSheet, cubicalPlaquetteChart] at hp₁

theorem cubicalXYLoop_vertical_symmDiff (m n k c₁ c₂ C : Nat)
    (hc₁ : c₁ ≤ C) (hc₂ : c₂ ≤ C) :
    (cubicalXYLoop (a := m) (b := n) (c := c₁) (0 : Fin (c₁ + 1))).map
          (cubicalEdgeChart (A := m) (B := n + k) (C := C)
            0 0 0 (by omega) (by omega) (by omega)) ∆
      (cubicalXYLoop (a := m) (b := k) (c := c₂) (0 : Fin (c₂ + 1))).map
          (cubicalEdgeChart (A := m) (B := n + k) (C := C)
            0 n 0 (by omega) (by omega) (by omega)) =
        cubicalXYLoop (a := m) (b := n + k) (c := C) (0 : Fin (C + 1)) := by
  let P₁ := cubicalPlaquetteChart (a := m) (b := n) (c := c₁)
    (A := m) (B := n + k) (C := C) 0 0 0 (by omega) (by omega) (by omega)
  let P₂ := cubicalPlaquetteChart (a := m) (b := k) (c := c₂)
    (A := m) (B := n + k) (C := C) 0 n 0 (by omega) (by omega) (by omega)
  let E₁ := cubicalEdgeChart (a := m) (b := n) (c := c₁)
    (A := m) (B := n + k) (C := C) 0 0 0 (by omega) (by omega) (by omega)
  let E₂ := cubicalEdgeChart (a := m) (b := k) (c := c₂)
    (A := m) (B := n + k) (C := C) 0 n 0 (by omega) (by omega) (by omega)
  let S₁ := (cubicalXYSheet (a := m) (b := n) (c := c₁)
    (0 : Fin (c₁ + 1))).map P₁
  let S₂ := (cubicalXYSheet (a := m) (b := k) (c := c₂)
    (0 : Fin (c₂ + 1))).map P₂
  change (gaugeSurfaceBoundary cubicalPlaquetteIncidence
      (cubicalXYSheet (0 : Fin (c₁ + 1)))).map E₁ ∆
    (gaugeSurfaceBoundary cubicalPlaquetteIncidence
      (cubicalXYSheet (0 : Fin (c₂ + 1)))).map E₂ = _
  rw [← gaugeSurfaceBoundary_map cubicalPlaquetteIncidence
      cubicalPlaquetteIncidence E₁ P₁
      (cubicalPlaquetteIncidence_chart 0 0 0 _ _ _),
    ← gaugeSurfaceBoundary_map cubicalPlaquetteIncidence
      cubicalPlaquetteIncidence E₂ P₂
      (cubicalPlaquetteIncidence_chart 0 n 0 _ _ _)]
  change gaugeSurfaceBoundary cubicalPlaquetteIncidence S₁ ∆
    gaugeSurfaceBoundary cubicalPlaquetteIncidence S₂ = _
  rw [← gaugeSurfaceBoundary_union_of_disjoint cubicalPlaquetteIncidence
    (cubicalXYSheet_vertical_disjoint m n k c₁ c₂ C hc₁ hc₂)]
  have hunion : S₁ ∪ S₂ =
      cubicalXYSheet (a := m) (b := n + k) (c := C) (0 : Fin (C + 1)) :=
    cubicalXYSheet_vertical_union m n k c₁ c₂ C hc₁ hc₂
  rw [hunion]
  rfl



def cubicalRectangularWilsonExpectation (beta : Real) (m n : Nat) : Real :=
  gaugeWilsonExpectation
    (cubicalPlaquetteIncidence (a := m) (b := n) (c := max m n))
    (fun _ : CubicalPlaquette m n (max m n) => beta)
    (cubicalXYLoop (a := m) (b := n) (c := max m n)
      (0 : Fin (max m n + 1)))

theorem cubicalRectangularWilsonExpectation_mul_le_horizontal
    {beta : Real} (hbeta : 0 < beta) (m l n : Nat) :
    cubicalRectangularWilsonExpectation beta m n *
        cubicalRectangularWilsonExpectation beta l n ≤
      cubicalRectangularWilsonExpectation beta (m + l) n := by
  let c₁ := max m n
  let c₂ := max l n
  let C := max (m + l) n
  have hc₁ : c₁ ≤ C := by
    dsimp [c₁, C]
    apply max_le
    · exact le_trans (by omega) (Nat.le_max_left _ _)
    · exact Nat.le_max_right _ _
  have hc₂ : c₂ ≤ C := by
    dsimp [c₂, C]
    apply max_le
    · exact le_trans (by omega) (Nat.le_max_left _ _)
    · exact Nat.le_max_right _ _
  let E₁ := cubicalEdgeChart (a := m) (b := n) (c := c₁)
    (A := m + l) (B := n) (C := C) 0 0 0 (by omega) (by omega) (by omega)
  let E₂ := cubicalEdgeChart (a := l) (b := n) (c := c₂)
    (A := m + l) (B := n) (C := C) m 0 0 (by omega) (by omega) (by omega)
  let L₁ := (cubicalXYLoop (a := m) (b := n) (c := c₁)
    (0 : Fin (c₁ + 1))).map E₁
  let L₂ := (cubicalXYLoop (a := l) (b := n) (c := c₂)
    (0 : Fin (c₂ + 1))).map E₂
  have hleft : cubicalRectangularWilsonExpectation beta m n ≤
      gaugeWilsonExpectation cubicalPlaquetteIncidence
        (fun _ : CubicalPlaquette (m + l) n C => beta) L₁ := by
    simpa [cubicalRectangularWilsonExpectation, c₁, C, E₁, L₁] using
      (cubicalXYWilsonExpectation_le_chart (a := m) (b := n) (c := c₁)
        (A := m + l) (B := n) (C := C) 0 0 0
        (by omega) (by omega) (by omega) hbeta.le (0 : Fin (c₁ + 1)))
  have hright : cubicalRectangularWilsonExpectation beta l n ≤
      gaugeWilsonExpectation cubicalPlaquetteIncidence
        (fun _ : CubicalPlaquette (m + l) n C => beta) L₂ := by
    simpa [cubicalRectangularWilsonExpectation, c₂, C, E₂, L₂] using
      (cubicalXYWilsonExpectation_le_chart (a := l) (b := n) (c := c₂)
        (A := m + l) (B := n) (C := C) m 0 0
        (by omega) (by omega) (by omega) hbeta.le (0 : Fin (c₂ + 1)))
  have hsmall₂ : 0 ≤ cubicalRectangularWilsonExpectation beta l n :=
    (gaugeWilsonExpectation_mem_Icc cubicalPlaquetteIncidence
      (fun _ : CubicalPlaquette l n (max l n) => beta) (fun _ => hbeta)
      (cubicalXYLoop (0 : Fin (max l n + 1)))).1
  have hcommon₁ : 0 ≤ gaugeWilsonExpectation cubicalPlaquetteIncidence
      (fun _ : CubicalPlaquette (m + l) n C => beta) L₁ :=
    (gaugeWilsonExpectation_mem_Icc cubicalPlaquetteIncidence
      (fun _ : CubicalPlaquette (m + l) n C => beta) (fun _ => hbeta) L₁).1
  have hproduct : cubicalRectangularWilsonExpectation beta m n *
      cubicalRectangularWilsonExpectation beta l n ≤
      gaugeWilsonExpectation cubicalPlaquetteIncidence
          (fun _ : CubicalPlaquette (m + l) n C => beta) L₁ *
        gaugeWilsonExpectation cubicalPlaquetteIncidence
          (fun _ : CubicalPlaquette (m + l) n C => beta) L₂ :=
    mul_le_mul hleft hright hsmall₂ hcommon₁
  have hgks := gaugeWilsonExpectation_mul_le_symmDiff
    cubicalPlaquetteIncidence
    (fun _ : CubicalPlaquette (m + l) n C => beta) (fun _ => hbeta.le) L₁ L₂
  have hloops : L₁ ∆ L₂ =
      cubicalXYLoop (a := m + l) (b := n) (c := C) (0 : Fin (C + 1)) := by
    simpa [c₁, c₂, C, E₁, E₂, L₁, L₂] using
      cubicalXYLoop_horizontal_symmDiff m l n c₁ c₂ C hc₁ hc₂
  rw [hloops] at hgks
  exact hproduct.trans (by
    simpa [cubicalRectangularWilsonExpectation, C] using hgks)

theorem cubicalRectangularWilsonExpectation_mul_le_vertical
    {beta : Real} (hbeta : 0 < beta) (m n k : Nat) :
    cubicalRectangularWilsonExpectation beta m n *
        cubicalRectangularWilsonExpectation beta m k ≤
      cubicalRectangularWilsonExpectation beta m (n + k) := by
  let c₁ := max m n
  let c₂ := max m k
  let C := max m (n + k)
  have hc₁ : c₁ ≤ C := by
    dsimp [c₁, C]
    apply max_le
    · exact Nat.le_max_left _ _
    · exact le_trans (by omega) (Nat.le_max_right _ _)
  have hc₂ : c₂ ≤ C := by
    dsimp [c₂, C]
    apply max_le
    · exact Nat.le_max_left _ _
    · exact le_trans (by omega) (Nat.le_max_right _ _)
  let E₁ := cubicalEdgeChart (a := m) (b := n) (c := c₁)
    (A := m) (B := n + k) (C := C) 0 0 0 (by omega) (by omega) (by omega)
  let E₂ := cubicalEdgeChart (a := m) (b := k) (c := c₂)
    (A := m) (B := n + k) (C := C) 0 n 0 (by omega) (by omega) (by omega)
  let L₁ := (cubicalXYLoop (a := m) (b := n) (c := c₁)
    (0 : Fin (c₁ + 1))).map E₁
  let L₂ := (cubicalXYLoop (a := m) (b := k) (c := c₂)
    (0 : Fin (c₂ + 1))).map E₂
  have hfirst : cubicalRectangularWilsonExpectation beta m n ≤
      gaugeWilsonExpectation cubicalPlaquetteIncidence
        (fun _ : CubicalPlaquette m (n + k) C => beta) L₁ := by
    simpa [cubicalRectangularWilsonExpectation, c₁, C, E₁, L₁] using
      (cubicalXYWilsonExpectation_le_chart (a := m) (b := n) (c := c₁)
        (A := m) (B := n + k) (C := C) 0 0 0
        (by omega) (by omega) (by omega) hbeta.le (0 : Fin (c₁ + 1)))
  have hsecond : cubicalRectangularWilsonExpectation beta m k ≤
      gaugeWilsonExpectation cubicalPlaquetteIncidence
        (fun _ : CubicalPlaquette m (n + k) C => beta) L₂ := by
    simpa [cubicalRectangularWilsonExpectation, c₂, C, E₂, L₂] using
      (cubicalXYWilsonExpectation_le_chart (a := m) (b := k) (c := c₂)
        (A := m) (B := n + k) (C := C) 0 n 0
        (by omega) (by omega) (by omega) hbeta.le (0 : Fin (c₂ + 1)))
  have hsmall₂ : 0 ≤ cubicalRectangularWilsonExpectation beta m k :=
    (gaugeWilsonExpectation_mem_Icc cubicalPlaquetteIncidence
      (fun _ : CubicalPlaquette m k (max m k) => beta) (fun _ => hbeta)
      (cubicalXYLoop (0 : Fin (max m k + 1)))).1
  have hcommon₁ : 0 ≤ gaugeWilsonExpectation cubicalPlaquetteIncidence
      (fun _ : CubicalPlaquette m (n + k) C => beta) L₁ :=
    (gaugeWilsonExpectation_mem_Icc cubicalPlaquetteIncidence
      (fun _ : CubicalPlaquette m (n + k) C => beta) (fun _ => hbeta) L₁).1
  have hproduct : cubicalRectangularWilsonExpectation beta m n *
      cubicalRectangularWilsonExpectation beta m k ≤
      gaugeWilsonExpectation cubicalPlaquetteIncidence
          (fun _ : CubicalPlaquette m (n + k) C => beta) L₁ *
        gaugeWilsonExpectation cubicalPlaquetteIncidence
          (fun _ : CubicalPlaquette m (n + k) C => beta) L₂ :=
    mul_le_mul hfirst hsecond hsmall₂ hcommon₁
  have hgks := gaugeWilsonExpectation_mul_le_symmDiff
    cubicalPlaquetteIncidence
    (fun _ : CubicalPlaquette m (n + k) C => beta) (fun _ => hbeta.le) L₁ L₂
  have hloops : L₁ ∆ L₂ =
      cubicalXYLoop (a := m) (b := n + k) (c := C) (0 : Fin (C + 1)) := by
    simpa [c₁, c₂, C, E₁, E₂, L₁, L₂] using
      cubicalXYLoop_vertical_symmDiff m n k c₁ c₂ C hc₁ hc₂
  rw [hloops] at hgks
  exact hproduct.trans (by
    simpa [cubicalRectangularWilsonExpectation, C] using hgks)

@[simp] theorem gaugeWilsonExpectation_empty
    {E P : Type*} [Fintype E] [DecidableEq E]
    [Fintype P] [DecidableEq P]
    (incidence : P → Finset E) (K : P → Real) :
    gaugeWilsonExpectation incidence K ∅ = 1 := by
  unfold gaugeWilsonExpectation gaugeWilsonNumerator wilsonSpin
  simp only [Finset.prod_empty, one_mul]
  exact div_self (gaugePartition_pos incidence K).ne'

@[simp] theorem cubicalRectangularWilsonExpectation_zero_left
    (beta : Real) (n : Nat) :
    cubicalRectangularWilsonExpectation beta 0 n = 1 := by
  have hsheet : cubicalXYSheet (a := 0) (b := n) (c := max 0 n)
      (0 : Fin (max 0 n + 1)) = ∅ := by
    simp [cubicalXYSheet]
  have hloop : cubicalXYLoop (a := 0) (b := n) (c := max 0 n)
      (0 : Fin (max 0 n + 1)) = ∅ := by
    unfold cubicalXYLoop
    rw [hsheet]
    simp [gaugeSurfaceBoundary]
  simp [cubicalRectangularWilsonExpectation, hloop]

@[simp] theorem cubicalRectangularWilsonExpectation_zero_right
    (beta : Real) (m : Nat) :
    cubicalRectangularWilsonExpectation beta m 0 = 1 := by
  have hsheet : cubicalXYSheet (a := m) (b := 0) (c := max m 0)
      (0 : Fin (max m 0 + 1)) = ∅ := by
    simp [cubicalXYSheet]
  have hloop : cubicalXYLoop (a := m) (b := 0) (c := max m 0)
      (0 : Fin (max m 0 + 1)) = ∅ := by
    unfold cubicalXYLoop
    rw [hsheet]
    simp [gaugeSurfaceBoundary]
  simp [cubicalRectangularWilsonExpectation, hloop]

theorem cubicalRectangularWilsonExpectation_pos
    {beta : Real} (hbeta : 0 < beta) (m n : Nat) :
    0 < cubicalRectangularWilsonExpectation beta m n := by
  unfold cubicalRectangularWilsonExpectation
  apply (gaugeWilsonExpectation_pos_iff_exists_boundary
    cubicalPlaquetteIncidence
    (fun _ : CubicalPlaquette m n (max m n) => beta) (fun _ => hbeta)
    (cubicalXYLoop (0 : Fin (max m n + 1)))).mpr
  exact ⟨cubicalXYSheet (0 : Fin (max m n + 1)),
    cubicalXYSheet_hasWilsonBoundary (0 : Fin (max m n + 1))⟩

theorem cubicalRectangularWilsonFreeEnergy_eq_neg_log_expectation
    (beta : Real) (m n : Nat) :
    cubicalRectangularWilsonFreeEnergy beta m n =
      -Real.log (cubicalRectangularWilsonExpectation beta m n) := rfl

theorem cubicalRectangularWilsonFreeEnergy_horizontal_subadditive
    {beta : Real} (hbeta : 0 < beta) :
    HorizontallySubadditive (cubicalRectangularWilsonFreeEnergy beta) := by
  intro n m l
  have hm := cubicalRectangularWilsonExpectation_pos hbeta m n
  have hl := cubicalRectangularWilsonExpectation_pos hbeta l n
  have hprod := cubicalRectangularWilsonExpectation_mul_le_horizontal
    hbeta m l n
  have hlog := Real.log_le_log (mul_pos hm hl) hprod
  rw [Real.log_mul hm.ne' hl.ne'] at hlog
  simp only [cubicalRectangularWilsonFreeEnergy_eq_neg_log_expectation]
  linarith

theorem cubicalRectangularWilsonFreeEnergy_vertical_subadditive
    {beta : Real} (hbeta : 0 < beta) :
    VerticallySubadditive (cubicalRectangularWilsonFreeEnergy beta) := by
  intro m n k
  have hn := cubicalRectangularWilsonExpectation_pos hbeta m n
  have hk := cubicalRectangularWilsonExpectation_pos hbeta m k
  have hprod := cubicalRectangularWilsonExpectation_mul_le_vertical
    hbeta m n k
  have hlog := Real.log_le_log (mul_pos hn hk) hprod
  rw [Real.log_mul hn.ne' hk.ne'] at hlog
  simp only [cubicalRectangularWilsonFreeEnergy_eq_neg_log_expectation]
  linarith

theorem cubicalRectangularWilsonFreeEnergy_separatelySubadditive
    {beta : Real} (hbeta : 0 < beta) :
    SeparatelySubadditive (cubicalRectangularWilsonFreeEnergy beta) :=
  ⟨cubicalRectangularWilsonFreeEnergy_horizontal_subadditive hbeta,
    cubicalRectangularWilsonFreeEnergy_vertical_subadditive hbeta⟩

@[simp] theorem cubicalRectangularWilsonFreeEnergy_zero_left
    (beta : Real) (n : Nat) :
    cubicalRectangularWilsonFreeEnergy beta 0 n = 0 := by
  rw [cubicalRectangularWilsonFreeEnergy_eq_neg_log_expectation,
    cubicalRectangularWilsonExpectation_zero_left]
  norm_num

@[simp] theorem cubicalRectangularWilsonFreeEnergy_zero_right
    (beta : Real) (m : Nat) :
    cubicalRectangularWilsonFreeEnergy beta m 0 = 0 := by
  rw [cubicalRectangularWilsonFreeEnergy_eq_neg_log_expectation,
    cubicalRectangularWilsonExpectation_zero_right]
  norm_num

theorem cubicalRectangularWilsonFreeEnergy_hasAreaBound
    {beta : Real} (hbeta : 0 < beta) :
    HasRectangularAreaBound (cubicalRectangularWilsonFreeEnergy beta) := by
  refine ⟨2 * gaugeDualCoupling beta,
    mul_nonneg (by norm_num) (gaugeDualCoupling_pos hbeta).le, ?_⟩
  intro m n
  by_cases hm : m = 0
  · subst m
    simp
  by_cases hn : n = 0
  · subst n
    simp
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hc : 0 < max m n := hmpos.trans_le (Nat.le_max_left m n)
  have hbound := cubicalXYWilsonFreeEnergy_le_area_mul_dualCoupling
    hmpos hnpos hc (0 : Fin (max m n + 1)) beta hbeta
  calc
    cubicalRectangularWilsonFreeEnergy beta m n ≤
        2 * (m * n : Nat) * gaugeDualCoupling beta := by
      simpa [cubicalRectangularWilsonFreeEnergy] using hbound
    _ = (2 * gaugeDualCoupling beta) * (m : Real) * (n : Real) := by
      push_cast
      ring



theorem cubicalRectangularWilsonFreeEnergy_hasBlockGluing
    {beta : Real} (hbeta : 0 < beta) :
    HasRectangularBlockGluing (cubicalRectangularWilsonFreeEnergy beta) :=
  hasRectangularBlockGluing_of_separatelySubadditive_areaBound
    (cubicalRectangularWilsonFreeEnergy_nonneg hbeta)
    (cubicalRectangularWilsonFreeEnergy_separatelySubadditive hbeta)
    (cubicalRectangularWilsonFreeEnergy_hasAreaBound hbeta)


theorem cubicalSquareWilsonDensity_tendsto_rectangularSurfaceRate_unconditional
    {beta : Real} (hbeta : 0 < beta) :
    Filter.Tendsto (cubicalSquareWilsonDensity beta) Filter.atTop
      (nhds (rectangularSurfaceRate
        (cubicalRectangularWilsonFreeEnergy beta))) :=
  cubicalSquareWilsonDensity_tendsto_rectangularSurfaceRate hbeta
    (cubicalRectangularWilsonFreeEnergy_hasBlockGluing hbeta)


theorem cubicalSquareDisorderDensity_tendsto_rectangularSurfaceRate_unconditional
    {beta : Real} (hbeta : 0 < beta) :
    Filter.Tendsto (cubicalSquareDisorderDensity beta) Filter.atTop
      (nhds (rectangularSurfaceRate
        (cubicalRectangularWilsonFreeEnergy beta))) :=
  cubicalSquareDisorderDensity_tendsto_rectangularSurfaceRate hbeta
    (cubicalRectangularWilsonFreeEnergy_hasBlockGluing hbeta)

end
end StatMech.FrontierA
