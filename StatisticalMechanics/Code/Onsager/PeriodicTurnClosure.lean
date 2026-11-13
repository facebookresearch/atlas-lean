/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.GeneralUmlaufsatz
import Code.Onsager.TorusPeriodicLift










namespace StatMech.Onsager

open BigOperators
open StatMech.Onsager.BaseCase

def ons_pathDisplacement : List (Fin 4) → ℤ × ℤ
  | [] => 0
  | d :: ds => stepOf d + ons_pathDisplacement ds

def ons_pathVertices : List (Fin 4) → List (ℤ × ℤ)
  | [] => [0]
  | d :: ds => 0 :: (ons_pathVertices ds).map (stepOf d + ·)

def ons_openTurnSum : List (Fin 4) → ℤ
  | [] => 0
  | [_] => 0
  | d :: e :: ds =>
      ons_turnPow d e + ons_openTurnSum (e :: ds)

def ons_cyclicTurnSum : List (Fin 4) → ℤ
  | [] => 0
  | d :: ds =>
      ons_openTurnSum (d :: ds) +
        ons_turnPow (d :: ds).getLast! d

@[simp] theorem ons_pathDisplacement_nil :
    ons_pathDisplacement [] = 0 := rfl

@[simp] theorem ons_pathDisplacement_cons (d : Fin 4) (ds : List (Fin 4)) :
    ons_pathDisplacement (d :: ds) =
      stepOf d + ons_pathDisplacement ds := rfl

@[simp] theorem ons_pathVertices_nil :
    ons_pathVertices [] = [0] := rfl

@[simp] theorem ons_pathVertices_cons (d : Fin 4) (ds : List (Fin 4)) :
    ons_pathVertices (d :: ds) =
      0 :: (ons_pathVertices ds).map (stepOf d + ·) := rfl

theorem ons_pathDisplacement_append (l r : List (Fin 4)) :
    ons_pathDisplacement (l ++ r) =
      ons_pathDisplacement l + ons_pathDisplacement r := by
  induction l with
  | nil => simp
  | cons d ds ih =>
      simp only [List.cons_append, ons_pathDisplacement_cons, ih]
      abel

@[simp] theorem ons_pathVertices_length (l : List (Fin 4)) :
    (ons_pathVertices l).length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons d ds ih => simp [ih]

@[simp] theorem ons_pathVertices_head (l : List (Fin 4)) :
    (ons_pathVertices l).head? = some 0 := by
  cases l <;> rfl

theorem ons_pathVertices_getLast (l : List (Fin 4)) :
    (ons_pathVertices l).getLast? = some (ons_pathDisplacement l) := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
      simp only [ons_pathVertices_cons, List.getLast?_cons,
        List.getLast?_map, ih,
        Option.map_some, ons_pathDisplacement_cons]
      simp

theorem ons_pathVertices_append (l r : List (Fin 4)) :
    ons_pathVertices (l ++ r) =
      (ons_pathVertices l).dropLast ++
        (ons_pathVertices r).map (ons_pathDisplacement l + ·) := by
  induction l with
  | nil => simp
  | cons d ds ih =>
      have hmap :
          (ons_pathVertices ds).map (stepOf d + ·) ≠ [] := by
        intro h
        have hlen := congrArg List.length h
        rw [List.length_map, ons_pathVertices_length] at hlen
        simp at hlen
      simp only [List.cons_append, ons_pathVertices_cons, ih,
        List.map_append, List.map_map,
        List.dropLast_cons_of_ne_nil hmap,
        ← List.map_dropLast, ons_pathDisplacement_cons]
      congr 2
      apply List.map_congr_left
      intro z hz
      simp only [Function.comp_apply]
      abel

theorem ons_pathVertices_append_dropLast
    (l r : List (Fin 4)) :
    (ons_pathVertices (l ++ r)).dropLast =
      (ons_pathVertices l).dropLast ++
        (ons_pathVertices r).dropLast.map
          (ons_pathDisplacement l + ·) := by
  rw [ons_pathVertices_append]
  have hne :
      (ons_pathVertices r).map (ons_pathDisplacement l + ·) ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    rw [List.length_map, ons_pathVertices_length] at hlen
    simp at hlen
  rw [List.dropLast_append_of_ne_nil hne, ← List.map_dropLast]

theorem ons_mem_pathVertices_append_dropLast_iff
    (l r : List (Fin 4)) (z : ℤ × ℤ) :
    z ∈ (ons_pathVertices (l ++ r)).dropLast ↔
      z ∈ (ons_pathVertices l).dropLast ∨
        ∃ w ∈ (ons_pathVertices r).dropLast,
          z = ons_pathDisplacement l + w := by
  rw [ons_pathVertices_append_dropLast, List.mem_append, List.mem_map]
  constructor
  · rintro (hz | ⟨w, hw, rfl⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨w, hw, rfl⟩
  · rintro (hz | ⟨w, hw, rfl⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨w, hw, rfl⟩

@[simp] theorem ons_openTurnSum_nil : ons_openTurnSum [] = 0 := rfl

@[simp] theorem ons_openTurnSum_singleton (d : Fin 4) :
    ons_openTurnSum [d] = 0 := rfl

theorem ons_openTurnSum_cons_cons
    (d e : Fin 4) (ds : List (Fin 4)) :
    ons_openTurnSum (d :: e :: ds) =
      ons_turnPow d e + ons_openTurnSum (e :: ds) := rfl

theorem ons_openTurnSum_append
    (l r : List (Fin 4)) (hl : l ≠ []) (hr : r ≠ []) :
    ons_openTurnSum (l ++ r) =
      ons_openTurnSum l +
        ons_turnPow l.getLast! r.head! + ons_openTurnSum r := by
  induction l with
  | nil => exact (hl rfl).elim
  | cons d ds ih =>
      cases ds with
      | nil =>
          obtain ⟨e, es, rfl⟩ := List.exists_cons_of_ne_nil hr
          simp [ons_openTurnSum]
      | cons e es =>
          have htail : e :: es ≠ [] := by simp
          change ons_turnPow d e +
              ons_openTurnSum ((e :: es) ++ r) = _
          rw [ih htail, ons_openTurnSum_cons_cons]
          simp [List.getLast!]
          abel

theorem ons_openTurnSum_replicate (n : ℕ) (d : Fin 4) :
    ons_openTurnSum (List.replicate n d) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      cases n with
      | zero => rfl
      | succ n =>
          simp only [List.replicate_succ, ons_openTurnSum_cons_cons,
            ons_turnPow]
          norm_num
          simpa only [List.replicate_succ] using ih

@[simp] theorem ons_getLast_replicate_succ
    (n : ℕ) (d : Fin 4) :
    (List.replicate (n + 1) d).getLast! = d := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ]
      simp [List.getLast!]

@[simp] theorem ons_getLast?_replicate_succ_getD
    (n : ℕ) (d : Fin 4) :
    (List.replicate (n + 1) d).getLast?.getD 0 = d := by
  rw [List.getLast?_replicate]
  simp

@[simp] theorem ons_head_replicate_succ
    (n : ℕ) (d : Fin 4) :
    (List.replicate (n + 1) d).head! = d := by
  rw [List.replicate_succ]
  rfl

theorem ons_pathDisplacement_replicate (n : ℕ) (d : Fin 4) :
    ons_pathDisplacement (List.replicate n d) = n • stepOf d := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, ons_pathDisplacement_cons, ih]
      rw [add_comm]
      exact (succ_nsmul (stepOf d) n).symm

theorem ons_pathVertices_replicate (n : ℕ) (d : Fin 4) :
    ons_pathVertices (List.replicate n d) =
      (List.range (n + 1)).map (fun k ↦ k • stepOf d) := by
  induction n with
  | zero => simp [ons_pathVertices]
  | succ n ih =>
      rw [List.replicate_succ, ons_pathVertices_cons, ih]
      conv_rhs => rw [show n + 1 + 1 = (n + 1) + 1 by rfl,
        List.range_succ_eq_map]
      simp only [List.map_map, List.map_cons, zero_nsmul,
        List.cons.injEq, true_and]
      apply List.map_congr_left
      intro k hk
      simp only [Function.comp_apply]
      rw [succ_nsmul]
      abel

theorem ons_mem_pathVertices_replicate_iff
    (n : ℕ) (d : Fin 4) (z : ℤ × ℤ) :
    z ∈ ons_pathVertices (List.replicate n d) ↔
      ∃ k : ℕ, k ≤ n ∧ z = k • stepOf d := by
  rw [ons_pathVertices_replicate, List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, Nat.le_of_lt_succ (List.mem_range.mp hk), rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, List.mem_range.mpr (Nat.lt_succ_iff.mpr hk), rfl⟩

theorem ons_pathVertices_replicate_dropLast
    (n : ℕ) (d : Fin 4) :
    (ons_pathVertices (List.replicate n d)).dropLast =
      (List.range n).map (fun k ↦ k • stepOf d) := by
  rw [ons_pathVertices_replicate, List.range_succ,
    List.map_append, List.dropLast_append_of_ne_nil (by simp)]
  simp

theorem ons_map_pathVertices_replicate_dropLast
    {X : Type*} (f : (ℤ × ℤ) → X) (n : ℕ) (d : Fin 4) :
    (List.map f (ons_pathVertices (List.replicate n d))).dropLast =
      (List.range n).map (fun k ↦ f (k • stepOf d)) := by
  rw [← List.map_dropLast, ons_pathVertices_replicate_dropLast,
    List.map_map]
  simp [Function.comp_def]

theorem ons_mem_pathVertices_replicate_dropLast_iff
    (n : ℕ) (d : Fin 4) (z : ℤ × ℤ) :
    z ∈ (ons_pathVertices (List.replicate n d)).dropLast ↔
      ∃ k : ℕ, k < n ∧ z = k • stepOf d := by
  rw [ons_pathVertices_replicate_dropLast, List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, List.mem_range.mp hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, List.mem_range.mpr hk, rfl⟩

def ons_outsideConnector (dx dy top : ℤ) : List (Fin 4) :=
  [0] ++
    List.replicate (top - dy).toNat 1 ++
    List.replicate (dx + 2).toNat 2 ++
    List.replicate top.toNat 3 ++ [0]

theorem ons_outsideConnector_ne_nil (dx dy top : ℤ) :
    ons_outsideConnector dx dy top ≠ [] := by
  simp [ons_outsideConnector]

@[simp] theorem ons_outsideConnector_head
    (dx dy top : ℤ) :
    (ons_outsideConnector dx dy top).head! = 0 := by
  simp [ons_outsideConnector]

@[simp] theorem ons_outsideConnector_getLast
    (dx dy top : ℤ) :
    (ons_outsideConnector dx dy top).getLast! = 0 := by
  simp [ons_outsideConnector, List.getLast!]

theorem ons_outsideConnector_displacement
    (dx dy top : ℤ) (hdx : 0 < dx) (hdy : dy < top)
    (htop : 0 < top) :
    ons_pathDisplacement (ons_outsideConnector dx dy top) = (-dx, -dy) := by
  have hu : 0 ≤ top - dy := by omega
  have hw : 0 ≤ dx + 2 := by omega
  have hv : 0 ≤ top := by omega
  simp only [ons_outsideConnector, ons_pathDisplacement_append,
    ons_pathDisplacement_replicate, ons_pathDisplacement_cons,
    ons_pathDisplacement_nil]
  simp [stepOf, Prod.smul_mk, nsmul_eq_mul,
    Int.toNat_of_nonneg hu, Int.toNat_of_nonneg hw,
    Int.toNat_of_nonneg hv]
  constructor <;> ring

theorem ons_openTurnSum_five_blocks
    (a b c d e : Fin 4) (na nb nc nd ne : ℕ) :
    ons_openTurnSum
        (List.replicate (na + 1) a ++
          List.replicate (nb + 1) b ++
          List.replicate (nc + 1) c ++
          List.replicate (nd + 1) d ++
          List.replicate (ne + 1) e) =
      ons_turnPow a b + ons_turnPow b c +
        ons_turnPow c d + ons_turnPow d e := by
  let A := List.replicate (na + 1) a
  let B := List.replicate (nb + 1) b
  let C := List.replicate (nc + 1) c
  let D := List.replicate (nd + 1) d
  let E := List.replicate (ne + 1) e
  have hA : A ≠ [] := by simp [A]
  have hB : B ≠ [] := by simp [B]
  have hC : C ≠ [] := by simp [C]
  have hD : D ≠ [] := by simp [D]
  have hE : E ≠ [] := by simp [E]
  change ons_openTurnSum (A ++ B ++ C ++ D ++ E) = _
  simp only [List.append_assoc]
  rw [ons_openTurnSum_append A (B ++ (C ++ (D ++ E))) hA (by simp [hB]),
    ons_openTurnSum_append B (C ++ (D ++ E)) hB (by simp [hC]),
    ons_openTurnSum_append C (D ++ E) hC (by simp [hD]),
    ons_openTurnSum_append D E hD hE]
  simp [A, B, C, D, E, ons_openTurnSum_replicate]
  abel

theorem ons_outsideConnector_openTurnSum
    (dx dy top : ℤ) (hdx : 0 < dx) (hdy : dy < top)
    (htop : 0 < top) :
    ons_openTurnSum (ons_outsideConnector dx dy top) = 4 := by
  have hu : 0 < (top - dy).toNat := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have := Int.toNat_eq_zero.mp hzero
    omega
  have hw : 0 < (dx + 2).toNat := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have := Int.toNat_eq_zero.mp hzero
    omega
  have hv : 0 < top.toNat := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have := Int.toNat_eq_zero.mp hzero
    omega
  obtain ⟨u, hu'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hu)
  obtain ⟨w, hw'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hw)
  obtain ⟨v, hv'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hv)
  rw [show ons_outsideConnector dx dy top =
      List.replicate (0 + 1) 0 ++
        List.replicate (u + 1) 1 ++
        List.replicate (w + 1) 2 ++
        List.replicate (v + 1) 3 ++
        List.replicate (0 + 1) 0 by
      simp [ons_outsideConnector, hu', hw', hv']]
  rw [ons_openTurnSum_five_blocks]
  decide

theorem ons_mem_outsideConnector_vertices_dropLast
    (dx dy top : ℤ) (hdx : 0 < dx) (hdy : dy < top)
    (htop : 0 < top) (z : ℤ × ℤ)
    (hz : z ∈ (ons_pathVertices
      (ons_outsideConnector dx dy top)).dropLast) :
    z = 0 ∨
      (∃ k : ℕ, k < (top - dy).toNat ∧ z = (1, (k : ℤ))) ∨
      (∃ k : ℕ, k < (dx + 2).toNat ∧
        z = (1 - (k : ℤ), top - dy)) ∨
      (∃ k : ℕ, k < top.toNat ∧
        z = (-dx - 1, top - dy - (k : ℤ))) ∨
      z = (-dx - 1, -dy) := by
  let B := List.replicate (top - dy).toNat (1 : Fin 4)
  let C := List.replicate (dx + 2).toNat (2 : Fin 4)
  let D := List.replicate top.toNat (3 : Fin 4)
  have hu : 0 ≤ top - dy := by omega
  have hw : 0 ≤ dx + 2 := by omega
  have hv : 0 ≤ top := by omega
  have hshape : ons_outsideConnector dx dy top =
      [0] ++ (B ++ (C ++ (D ++ [0]))) := by
    simp [ons_outsideConnector, B, C, D, List.append_assoc]
  rw [hshape] at hz
  rcases (ons_mem_pathVertices_append_dropLast_iff
      [0] (B ++ (C ++ (D ++ [0]))) z).mp hz with hstart | ⟨z₁, hz₁, ez₁⟩
  · left
    simpa [ons_pathVertices] using hstart
  rcases (ons_mem_pathVertices_append_dropLast_iff
      B (C ++ (D ++ [0])) z₁).mp hz₁ with hright | ⟨z₂, hz₂, ez₂⟩
  · right; left
    obtain ⟨k, hk, hkz⟩ :=
      (ons_mem_pathVertices_replicate_dropLast_iff
        (top - dy).toNat 1 z₁).mp (by simpa [B] using hright)
    refine ⟨k, hk, ?_⟩
    rw [ez₁, hkz]
    simp [ons_pathDisplacement, stepOf, Prod.smul_mk]
  rcases (ons_mem_pathVertices_append_dropLast_iff
      C (D ++ [0]) z₂).mp hz₂ with htopEdge | ⟨z₃, hz₃, ez₃⟩
  · right; right; left
    obtain ⟨k, hk, hkz⟩ :=
      (ons_mem_pathVertices_replicate_dropLast_iff
        (dx + 2).toNat 2 z₂).mp (by simpa [C] using htopEdge)
    refine ⟨k, hk, ?_⟩
    rw [ez₁, ez₂, hkz,
      show ons_pathDisplacement B =
          (top - dy).toNat • stepOf 1 by
        simp [B, ons_pathDisplacement_replicate]]
    simp [ons_pathDisplacement, stepOf, Prod.smul_mk,
      Int.toNat_of_nonneg hu]
    ring
  rcases (ons_mem_pathVertices_append_dropLast_iff
      D [0] z₃).mp hz₃ with hleft | ⟨z₄, hz₄, ez₄⟩
  · right; right; right; left
    obtain ⟨k, hk, hkz⟩ :=
      (ons_mem_pathVertices_replicate_dropLast_iff
        top.toNat 3 z₃).mp (by simpa [D] using hleft)
    refine ⟨k, hk, ?_⟩
    rw [ez₁, ez₂, ez₃, hkz,
      show ons_pathDisplacement B =
          (top - dy).toNat • stepOf 1 by
        simp [B, ons_pathDisplacement_replicate],
      show ons_pathDisplacement C =
          (dx + 2).toNat • stepOf 2 by
        simp [C, ons_pathDisplacement_replicate]]
    simp [ons_pathDisplacement, stepOf, Prod.smul_mk,
      Int.toNat_of_nonneg hu, Int.toNat_of_nonneg hw]
    constructor <;> ring
  · right; right; right; right
    have hz₄zero : z₄ = 0 := by
      simpa [ons_pathVertices] using hz₄
    rw [ez₁, ez₂, ez₃, ez₄, hz₄zero,
      show ons_pathDisplacement B =
          (top - dy).toNat • stepOf 1 by
        simp [B, ons_pathDisplacement_replicate],
      show ons_pathDisplacement C =
          (dx + 2).toNat • stepOf 2 by
        simp [C, ons_pathDisplacement_replicate],
      show ons_pathDisplacement D = top.toNat • stepOf 3 by
        simp [D, ons_pathDisplacement_replicate]]
    simp [ons_pathDisplacement, stepOf, Prod.smul_mk,
      Int.toNat_of_nonneg hu, Int.toNat_of_nonneg hw,
      Int.toNat_of_nonneg hv]
    constructor <;> ring

def ons_outsideConnectorVertexList (dx dy top : ℤ) :
    List (ℤ × ℤ) :=
  [0] ++
    (List.range (top - dy).toNat).map
      (fun k ↦ (1, (k : ℤ))) ++
    (List.range (dx + 2).toNat).map
      (fun k ↦ (1 - (k : ℤ), top - dy)) ++
    (List.range top.toNat).map
      (fun k ↦ (-dx - 1, top - dy - (k : ℤ))) ++
    [(-dx - 1, -dy)]

theorem ons_outsideConnector_vertices_dropLast_eq
    (dx dy top : ℤ) (hdx : 0 < dx) (hdy : dy < top)
    (htop : 0 < top) :
    (ons_pathVertices (ons_outsideConnector dx dy top)).dropLast =
      ons_outsideConnectorVertexList dx dy top := by
  let B := List.replicate (top - dy).toNat (1 : Fin 4)
  let C := List.replicate (dx + 2).toNat (2 : Fin 4)
  let D := List.replicate top.toNat (3 : Fin 4)
  have hu : 0 ≤ top - dy := by omega
  have hw : 0 ≤ dx + 2 := by omega
  have hv : 0 ≤ top := by omega
  have hshape : ons_outsideConnector dx dy top =
      [0] ++ (B ++ (C ++ (D ++ [0]))) := by
    simp [ons_outsideConnector, B, C, D, List.append_assoc]
  rw [hshape,
    ons_pathVertices_append_dropLast [0] (B ++ (C ++ (D ++ [0]))),
    ons_pathVertices_append_dropLast B (C ++ (D ++ [0])),
    ons_pathVertices_append_dropLast C (D ++ [0]),
    ons_pathVertices_append_dropLast D [0],
    ons_pathVertices_replicate_dropLast]
  simp only [List.map_append, List.map_map, Function.comp_apply]
  simp [B, C, D, ons_outsideConnectorVertexList,
    ons_pathDisplacement_replicate, ons_pathDisplacement,
    stepOf, Prod.smul_mk, Int.toNat_of_nonneg hu,
    Int.toNat_of_nonneg hw, Int.toNat_of_nonneg hv]
  repeat' first
    | apply congrArg₂ List.append <;> try rfl
    | apply List.map_congr_left
      intro k hk
      apply Prod.ext <;> simp <;> ring
  all_goals
    first
    | rw [← List.map_eq_flatMap, List.map_map]
      apply List.map_congr_left
      intro k hk
      apply Prod.ext <;>
        simp [Function.comp_def, stepOf, Prod.smul_mk] <;> ring
    | rw [ons_map_pathVertices_replicate_dropLast,
          ← List.map_eq_flatMap, List.map_map]
      apply List.map_congr_left
      intro k hk
      apply Prod.ext <;>
        simp [Function.comp_def, stepOf, Prod.smul_mk] <;> ring
    | congr 2 <;> ring

theorem ons_outsideConnectorVertexList_nodup
    (dx dy top : ℤ) (hdx : 0 < dx) (hdy : dy < top)
    (htop : 0 < top) :
    (ons_outsideConnectorVertexList dx dy top).Nodup := by
  simp [ons_outsideConnectorVertexList, List.nodup_append]
  repeat' apply And.intro
  all_goals
    first
    | omega
    | intro h
      have hx := congrArg (fun z : ℤ × ℤ ↦ z.1) h
      simp at hx
      omega
    | rw [← List.map_eq_flatMap, List.map_map]
      apply List.Nodup.map (by
        intro a b hab
        simp only [Function.comp_apply, Prod.mk.injEq] at hab
        omega)
      exact List.nodup_range

theorem ons_outsideConnector_vertices_dropLast_nodup
    (dx dy top : ℤ) (hdx : 0 < dx) (hdy : dy < top)
    (htop : 0 < top) :
    (ons_pathVertices (ons_outsideConnector dx dy top)).dropLast.Nodup := by
  rw [ons_outsideConnector_vertices_dropLast_eq dx dy top hdx hdy htop]
  exact ons_outsideConnectorVertexList_nodup dx dy top hdx hdy htop

theorem ons_pathDisplacement_not_mem_dropLast_of_vertices_nodup
    (l : List (Fin 4)) (hnodup : (ons_pathVertices l).Nodup) :
    ons_pathDisplacement l ∉ (ons_pathVertices l).dropLast := by
  have hne : ons_pathVertices l ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
  have hlast : (ons_pathVertices l).getLast hne =
      ons_pathDisplacement l := by
    have h := ons_pathVertices_getLast l
    rw [List.getLast?_eq_getLast hne] at h
    exact Option.some.inj h
  rw [← List.dropLast_append_getLast hne] at hnodup
  have hdisj := (List.nodup_append.mp hnodup).2.2
  intro hmem
  exact hdisj (ons_pathDisplacement l) hmem
    ((ons_pathVertices l).getLast hne) (by simp) hlast.symm

theorem ons_outsideConnector_shift_disjoint
    (l : List (Fin 4)) (dx dy top : ℤ)
    (hdx : 0 < dx) (hdy : dy < top) (htop : 0 < top)
    (hdisp : ons_pathDisplacement l = (dx, dy))
    (hnodup : (ons_pathVertices l).Nodup)
    (hxmin : ∀ z ∈ (ons_pathVertices l).dropLast, 0 ≤ z.1)
    (hxmax : ∀ z ∈ (ons_pathVertices l).dropLast, z.1 ≤ dx)
    (hymax : ∀ z ∈ (ons_pathVertices l).dropLast, z.2 < top) :
    ∀ z ∈ (ons_pathVertices l).dropLast,
      ∀ w ∈ (ons_pathVertices
        (ons_outsideConnector dx dy top)).dropLast,
        z ≠ ons_pathDisplacement l + w := by
  intro z hz w hw heq
  have hend : (dx, dy) ∉ (ons_pathVertices l).dropLast := by
    simpa [hdisp] using
      ons_pathDisplacement_not_mem_dropLast_of_vertices_nodup l hnodup
  rcases ons_mem_outsideConnector_vertices_dropLast
      dx dy top hdx hdy htop w hw with
    rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ |
      ⟨k, hk, rfl⟩ | rfl
  · have hzeq : z = (dx, dy) := by simpa [hdisp] using heq
    exact hend (hzeq ▸ hz)
  · have hx := congrArg Prod.fst heq
    have := hxmax z hz
    simp [hdisp] at hx
    omega
  · have hy := congrArg Prod.snd heq
    have := hymax z hz
    have hk' : (k : ℤ) < dx + 2 := by
      simpa [Int.toNat_of_nonneg (show 0 ≤ dx + 2 by omega)] using hk
    simp [hdisp] at hy
    omega
  · have hx := congrArg Prod.fst heq
    have := hxmin z hz
    simp [hdisp] at hx
    omega
  · have hx := congrArg Prod.fst heq
    have := hxmin z hz
    simp [hdisp] at hx
    omega

theorem ons_boundingClosure_vertices_dropLast_nodup
    (l : List (Fin 4)) (dx dy top : ℤ)
    (hdx : 0 < dx) (hdy : dy < top) (htop : 0 < top)
    (hdisp : ons_pathDisplacement l = (dx, dy))
    (hnodup : (ons_pathVertices l).Nodup)
    (hxmin : ∀ z ∈ (ons_pathVertices l).dropLast, 0 ≤ z.1)
    (hxmax : ∀ z ∈ (ons_pathVertices l).dropLast, z.1 ≤ dx)
    (hymax : ∀ z ∈ (ons_pathVertices l).dropLast, z.2 < top) :
    (ons_pathVertices
      (l ++ ons_outsideConnector dx dy top)).dropLast.Nodup := by
  rw [ons_pathVertices_append_dropLast]
  have hleft : (ons_pathVertices l).dropLast.Nodup :=
    List.Nodup.sublist (List.dropLast_sublist _) hnodup
  have hright :
      ((ons_pathVertices
        (ons_outsideConnector dx dy top)).dropLast.map
          (ons_pathDisplacement l + ·)).Nodup :=
    (ons_outsideConnector_vertices_dropLast_nodup
      dx dy top hdx hdy htop).map (add_right_injective _)
  apply List.Nodup.append hleft hright
  rw [List.disjoint_iff_ne]
  intro z hz b hb
  rw [List.mem_map] at hb
  obtain ⟨w, hw, rfl⟩ := hb
  exact ons_outsideConnector_shift_disjoint l dx dy top hdx hdy htop
    hdisp hnodup hxmin hxmax hymax z hz w hw

theorem ons_pos_succ_eq_head_add_pos_tail
    {n : ℕ} [NeZero n] (d : Fin (n + 1) → Fin 4) (i : Fin n) :
    pos d i.succ =
      stepOf (d 0) + pos (fun j : Fin n ↦ d j.succ) i := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  induction i using Fin.induction with
  | zero =>
      rw [ons_pos_succ_cast d 0]
      simp [pos]
  | succ i ih =>
      rw [ons_pos_succ_cast d i.succ]
      have hi : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
      rw [hi, ih, ons_pos_succ_cast (fun j ↦ d j.succ) i]
      abel

theorem ons_pathVertices_dropLast_eq_ofFn_pos
    (l : List (Fin 4)) [NeZero l.length] :
    (ons_pathVertices l).dropLast =
      List.ofFn (pos (fun i : Fin l.length ↦ l.get i)) := by
  have hl : l ≠ [] := by
    intro h
    subst l
    exact NeZero.ne 0 rfl
  obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil hl
  cases ds with
  | nil =>
      simp [ons_pathVertices, List.ofFn_succ, pos]
  | cons e es =>
      letI : NeZero (e :: es).length := ⟨by simp⟩
      have ih := ons_pathVertices_dropLast_eq_ofFn_pos (e :: es)
      have hmap :
          (ons_pathVertices (e :: es)).map (stepOf d + ·) ≠ [] := by
        simp
      rw [ons_pathVertices_cons,
        List.dropLast_cons_of_ne_nil hmap, ← List.map_dropLast, ih]
      conv_rhs => rw [List.ofFn_succ]
      change 0 :: _ = pos (fun i : Fin (d :: e :: es).length ↦
        (d :: e :: es).get i) 0 :: _
      rw [show pos (fun i : Fin (d :: e :: es).length ↦
        (d :: e :: es).get i) 0 = 0 by simp [pos]]
      congr 1
      rw [List.map_ofFn]
      congr 1
      funext i
      exact (ons_pos_succ_eq_head_add_pos_tail
        (fun j : Fin ((e :: es).length + 1) ↦
          (d :: e :: es).get j) i).symm

theorem ons_pos_get_injective_of_vertices_dropLast_nodup
    (l : List (Fin 4)) [NeZero l.length]
    (hnodup : (ons_pathVertices l).dropLast.Nodup) :
    Function.Injective (pos (fun i : Fin l.length ↦ l.get i)) := by
  rw [ons_pathVertices_dropLast_eq_ofFn_pos] at hnodup
  exact List.nodup_ofFn.mp hnodup

theorem ons_pathDisplacement_eq_sum_map (l : List (Fin 4)) :
    ons_pathDisplacement l = (l.map stepOf).sum := by
  induction l with
  | nil => rfl
  | cons d ds ih => simp [ih]

theorem ons_pathDisplacement_ofFn {n : ℕ} (d : Fin n → Fin 4) :
    ons_pathDisplacement (List.ofFn d) = ∑ i, stepOf (d i) := by
  rw [ons_pathDisplacement_eq_sum_map, List.map_ofFn,
    List.sum_ofFn]
  simp [Function.comp_def]

theorem ons_openTurnSum_ofFn {n : ℕ} (d : Fin (n + 1) → Fin 4) :
    ons_openTurnSum (List.ofFn d) =
      ∑ i : Fin n, ons_turnPow (d i.castSucc) (d i.succ) := by
  induction n with
  | zero => simp [List.ofFn_succ]
  | succ n ih =>
      rw [List.ofFn_succ]
      set g : Fin (n + 1) → Fin 4 := fun i ↦ d i.succ with hg
      have hgcons : List.ofFn g =
          g 0 :: List.ofFn (fun i : Fin n ↦ g i.succ) := by
        rw [List.ofFn_succ]
      rw [hgcons, ons_openTurnSum_cons_cons, ← hgcons, ih g,
        Fin.sum_univ_succ]
      simp only [hg, Fin.castSucc_zero, Fin.succ_castSucc]

theorem ons_getLast!_ofFn {X : Type*} [Inhabited X]
    {n : ℕ} (f : Fin (n + 1) → X) :
    (List.ofFn f).getLast! = f (Fin.last n) := by
  cases n with
  | zero => simp [List.ofFn_succ, List.getLast!]
  | succ n =>
      rw [List.ofFn_succ]
      dsimp only [List.getLast!]
      rw [List.getLast_cons (by simp)]
      rw [List.getLast_ofFn (by simp)]
      congr 1

theorem ons_cyclicTurnSum_ofFn {n : ℕ} (d : Fin (n + 1) → Fin 4) :
    ons_cyclicTurnSum (List.ofFn d) =
      ∑ i, ons_turnPow (d i) (d (i + 1)) := by
  rw [show ons_cyclicTurnSum (List.ofFn d) =
      ons_openTurnSum (List.ofFn d) +
        ons_turnPow (List.ofFn d).getLast! (d 0) by
    simp only [List.ofFn_succ]
    rfl]
  rw [ons_openTurnSum_ofFn, Fin.sum_univ_castSucc,
    ons_getLast!_ofFn]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    congr 1
    apply Fin.ext
    simp
  · rw [Fin.last_add_one]

theorem ons_cyclicTurnSum_ofFn' {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) :
    ons_cyclicTurnSum (List.ofFn d) =
      ∑ i, ons_turnPow (d i) (d (i + 1)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact ons_cyclicTurnSum_ofFn d

theorem ons_cyclicTurnSum_eq_four_or_neg_four_of_list
    (l : List (Fin 4)) [NeZero l.length]
    (hclosed : ons_pathDisplacement l = 0)
    (hsimple : (ons_pathVertices l).dropLast.Nodup)
    (hlen : 3 ≤ l.length)
    (hnu : ∀ i : Fin l.length, l.get (i + 1) ≠ l.get i + 2) :
    ons_cyclicTurnSum l = 4 ∨ ons_cyclicTurnSum l = -4 := by
  let d : Fin l.length → Fin 4 := fun i ↦ l.get i
  have hsum : ∑ i, stepOf (d i) = 0 := by
    rw [← ons_pathDisplacement_ofFn, List.ofFn_get]
    exact hclosed
  have hinj : Function.Injective (pos d) :=
    ons_pos_get_injective_of_vertices_dropLast_nodup l hsimple
  have hturn :=
    GeneralUmlaufsatz.turnSum_eq_four_or_neg_four
      d hsum hinj hlen hnu
  rw [← ons_cyclicTurnSum_ofFn', List.ofFn_get] at hturn
  exact hturn

theorem ons_stepOf_add_two (w : Fin 4) :
    stepOf (w + 2) = -stepOf w := by
  fin_cases w <;> rfl

theorem ons_nonUturn_of_pos_injective
    {n : ℕ} [NeZero n] (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0)
    (hinj : Function.Injective (pos d)) (hn : 3 ≤ n) :
    ∀ i, d (i + 1) ≠ d i + 2 := by
  intro i hdir
  have heq : pos d (i + 1 + 1) = pos d i := by
    rw [NoDoubleWind.pos_succ d hclosed (i + 1),
      NoDoubleWind.pos_succ d hclosed i, hdir, ons_stepOf_add_two]
    exact add_neg_cancel_right _ _
  have hidx := hinj heq
  have htwo : (2 : Fin n) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    change 2 % n = 0 at hv
    rw [Nat.mod_eq_of_lt hn] at hv
    omega
  apply htwo
  calc
    (2 : Fin n) = 1 + 1 := by
      apply Fin.ext
      simp [Fin.val_add, Nat.mod_eq_of_lt hn]
    _ = -i + (i + 1 + 1) := by abel
    _ = -i + i := by rw [hidx]
    _ = 0 := neg_add_cancel i

theorem ons_cyclicTurnSum_eq_four_or_neg_four_of_simple_list
    (l : List (Fin 4)) [NeZero l.length]
    (hclosed : ons_pathDisplacement l = 0)
    (hsimple : (ons_pathVertices l).dropLast.Nodup)
    (hlen : 3 ≤ l.length) :
    ons_cyclicTurnSum l = 4 ∨ ons_cyclicTurnSum l = -4 := by
  let d : Fin l.length → Fin 4 := fun i ↦ l.get i
  have hsum : ∑ i, stepOf (d i) = 0 := by
    rw [← ons_pathDisplacement_ofFn, List.ofFn_get]
    exact hclosed
  have hinj : Function.Injective (pos d) :=
    ons_pos_get_injective_of_vertices_dropLast_nodup l hsimple
  exact ons_cyclicTurnSum_eq_four_or_neg_four_of_list l hclosed
    hsimple hlen (ons_nonUturn_of_pos_injective d hsum hinj hlen)

theorem ons_boundingClosure_turnSum_eq_four_or_neg_four
    (l : List (Fin 4)) (dx dy top : ℤ)
    (hdx : 0 < dx) (hdy : dy < top) (htop : 0 < top)
    (hdisp : ons_pathDisplacement l = (dx, dy))
    (hnodup : (ons_pathVertices l).Nodup)
    (hxmin : ∀ z ∈ (ons_pathVertices l).dropLast, 0 ≤ z.1)
    (hxmax : ∀ z ∈ (ons_pathVertices l).dropLast, z.1 ≤ dx)
    (hymax : ∀ z ∈ (ons_pathVertices l).dropLast, z.2 < top) :
    ons_cyclicTurnSum (l ++ ons_outsideConnector dx dy top) = 4 ∨
      ons_cyclicTurnSum (l ++ ons_outsideConnector dx dy top) = -4 := by
  let c := ons_outsideConnector dx dy top
  letI : NeZero (l ++ c).length := ⟨by simp [c, ons_outsideConnector]⟩
  have hclosed : ons_pathDisplacement (l ++ c) = 0 := by
    rw [ons_pathDisplacement_append,
      ons_outsideConnector_displacement dx dy top hdx hdy htop,
      hdisp]
    ext <;> simp
  have hsimple : (ons_pathVertices (l ++ c)).dropLast.Nodup := by
    exact ons_boundingClosure_vertices_dropLast_nodup l dx dy top
      hdx hdy htop hdisp hnodup hxmin hxmax hymax
  have hlen : 3 ≤ (l ++ c).length := by
    have hv0 : top.toNat ≠ 0 := by
      intro h
      have := Int.toNat_eq_zero.mp h
      omega
    have hv : 1 ≤ top.toNat := Nat.one_le_iff_ne_zero.mpr hv0
    simp [c, ons_outsideConnector]
    omega
  exact ons_cyclicTurnSum_eq_four_or_neg_four_of_simple_list
    (l ++ c) hclosed hsimple hlen

theorem ons_getLast!_eq_getLast {X : Type*} [Inhabited X]
    (l : List X) (h : l ≠ []) :
    l.getLast! = l.getLast h := by
  cases l with
  | nil => exact (h rfl).elim
  | cons a as => rfl

theorem ons_boundingClosure_cyclicTurnSum
    (l : List (Fin 4)) (hl : l ≠ [])
    (dx dy top : ℤ) (hdx : 0 < dx) (hdy : dy < top)
    (htop : 0 < top) :
    ons_cyclicTurnSum (l ++ ons_outsideConnector dx dy top) =
      ons_openTurnSum l + ons_turnPow l.getLast! 0 + 4 +
        ons_turnPow 0 l.head! := by
  let c := ons_outsideConnector dx dy top
  have hc : c ≠ [] := ons_outsideConnector_ne_nil dx dy top
  rw [show ons_cyclicTurnSum (l ++ c) =
      ons_openTurnSum (l ++ c) +
        ons_turnPow (l ++ c).getLast! (l ++ c).head! by
    obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil hl
    rfl]
  rw [ons_openTurnSum_append l c hl hc,
    ons_outsideConnector_openTurnSum dx dy top hdx hdy htop]
  have hlast : (l ++ c).getLast! = 0 := by
    have happ : l ++ c ≠ [] := List.append_ne_nil_of_right_ne_nil l hc
    have heq : (l ++ c).getLast happ = c.getLast hc := by
      rw [List.getLast_append]
      simp [hc]
    rw [ons_getLast!_eq_getLast (l ++ c) happ]
    rw [heq]
    rw [← ons_getLast!_eq_getLast c hc]
    exact ons_outsideConnector_getLast dx dy top
  have hhead : (l ++ c).head! = l.head! := by simp [hl]
  have hchead : c.head! = 0 := by
    simpa only [c] using ons_outsideConnector_head dx dy top
  rw [hlast, hhead, hchead]

theorem ons_three_values_force_step_zero
    (a t : ℤ)
    (h0 : a = 4 ∨ a = -4)
    (h1 : a + t = 4 ∨ a + t = -4)
    (h2 : a + 2 * t = 4 ∨ a + 2 * t = -4) :
    t = 0 := by
  rcases h0 with h0 | h0 <;>
    rcases h1 with h1 | h1 <;>
      rcases h2 with h2 | h2 <;> omega

def ons_periodStateList (n r : ℕ) : List (ℕ × Fin n) :=
  List.ofFn (fun i : Fin n ↦ (r, i))

def ons_allPeriodStates (n N : ℕ) : List (ℕ × Fin n) :=
  (List.range (N + 1)).flatMap (ons_periodStateList n)

def ons_periodicArcStates {n : ℕ} (N : ℕ)
    (imin imax : Fin n) : List (ℕ × Fin n) :=
  ((ons_allPeriodStates n N).drop imin.val).take
    (N * n + imax.val + 1 - imin.val)

theorem ons_periodStateList_nodup (n r : ℕ) :
    (ons_periodStateList n r).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j hij
  exact Prod.mk.inj hij |>.2

theorem ons_mem_allPeriodStates_fst_le
    (n N : ℕ) (z : ℕ × Fin n)
    (hz : z ∈ ons_allPeriodStates n N) :
    z.1 ≤ N := by
  rw [ons_allPeriodStates, List.mem_flatMap] at hz
  obtain ⟨r, hr, hz⟩ := hz
  rw [ons_periodStateList, List.mem_ofFn] at hz
  obtain ⟨i, rfl⟩ := hz
  exact Nat.le_of_lt_succ (List.mem_range.mp hr)

theorem ons_allPeriodStates_nodup (n N : ℕ) :
    (ons_allPeriodStates n N).Nodup := by
  induction N with
  | zero =>
      simpa [ons_allPeriodStates] using ons_periodStateList_nodup n 0
  | succ N ih =>
      rw [ons_allPeriodStates, List.range_succ,
        List.flatMap_append]
      simp only [List.flatMap_singleton]
      apply List.Nodup.append (by simpa [ons_allPeriodStates] using ih)
        (ons_periodStateList_nodup n (N + 1))
      rw [List.disjoint_iff_ne]
      intro a ha b hb hab
      have ha' : a.1 ≤ N :=
        ons_mem_allPeriodStates_fst_le n N a (by
          simpa [ons_allPeriodStates] using ha)
      rw [ons_periodStateList, List.mem_ofFn] at hb
      obtain ⟨i, rfl⟩ := hb
      have := congrArg Prod.fst hab
      simp at this
      omega

@[simp] theorem ons_periodStateList_length (n r : ℕ) :
    (ons_periodStateList n r).length = n := by
  simp [ons_periodStateList]

@[simp] theorem ons_allPeriodStates_length (n N : ℕ) :
    (ons_allPeriodStates n N).length = (N + 1) * n := by
  simp [ons_allPeriodStates, List.length_flatMap]

theorem ons_periodicArcStates_nodup {n : ℕ}
    (N : ℕ) (imin imax : Fin n) :
    (ons_periodicArcStates N imin imax).Nodup := by
  apply List.Nodup.sublist
    ((List.take_sublist _ _).trans (List.drop_sublist _ _))
  exact ons_allPeriodStates_nodup n N

@[simp] theorem ons_periodicArcStates_length {n : ℕ}
    (N : ℕ) (hN : 1 ≤ N) (imin imax : Fin n) :
    (ons_periodicArcStates N imin imax).length =
      N * n + imax.val + 1 - imin.val := by
  rw [ons_periodicArcStates, List.length_take, List.length_drop,
    ons_allPeriodStates_length]
  rw [Nat.min_eq_left]
  rw [Nat.add_mul]
  omega

theorem ons_mem_periodicArcStates_fst_le {n : ℕ}
    (N : ℕ) (imin imax : Fin n) (z : ℕ × Fin n)
    (hz : z ∈ ons_periodicArcStates N imin imax) :
    z.1 ≤ N := by
  apply ons_mem_allPeriodStates_fst_le n N z
  exact List.Sublist.mem hz
    ((List.take_sublist _ _).trans (List.drop_sublist _ _))

def ons_periodStateCoord {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (z : ℕ × Fin n) : ℤ × ℤ :=
  pos d z.2 + z.1 • ons_pathDisplacement (List.ofFn d)

theorem ons_periodStateList_isChain {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (r : ℕ) :
    List.IsChain
      (fun a b ↦ ons_periodStateCoord d b =
        ons_periodStateCoord d a + stepOf (d a.2))
      (ons_periodStateList n r) := by
  rw [ons_periodStateList, List.isChain_ofFn]
  intro i hi
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  let j : Fin m := ⟨i, by omega⟩
  have hjc : (j.castSucc : Fin (m + 1)) = ⟨i, by omega⟩ := Fin.ext rfl
  have hjs : (j.succ : Fin (m + 1)) = ⟨i + 1, hi⟩ := Fin.ext rfl
  simp only [ons_periodStateCoord]
  rw [← hjc, ← hjs, ons_pos_succ_cast]
  abel

theorem ons_periodState_boundary {m : ℕ}
    (d : Fin (m + 1) → Fin 4) (r : ℕ) :
    ons_periodStateCoord d (r + 1, 0) =
      ons_periodStateCoord d (r, Fin.last m) +
        stepOf (d (Fin.last m)) := by
  simp only [ons_periodStateCoord]
  rw [NoDoubleWind.pos_zero, zero_add]
  have hlast := ons_pos_last_add_step d
  rw [← ons_pathDisplacement_ofFn d] at hlast
  rw [succ_nsmul]
  rw [← hlast]
  abel

@[simp] theorem ons_periodStateList_head? {n : ℕ} [NeZero n]
    (r : ℕ) :
    (ons_periodStateList n r).head? = some (r, (0 : Fin n)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  simp [ons_periodStateList, List.ofFn_succ]

def ons_lastFin (n : ℕ) [NeZero n] : Fin n :=
  ⟨n - 1, Nat.sub_lt (Nat.pos_of_ne_zero (NeZero.ne n)) (by omega)⟩

@[simp] theorem ons_periodStateList_getLast? {n : ℕ} [NeZero n]
    (r : ℕ) :
    (ons_periodStateList n r).getLast? =
      some (r, ons_lastFin n) := by
  change (List.ofFn (fun i : Fin n ↦ (r, i))).getLast? = _
  rw [List.getLast?_eq_some_getLast (by
    simpa using (NeZero.ne n))]
  rw [List.getLast_ofFn (by
    simpa using (NeZero.ne n))]
  congr 2

@[simp] theorem ons_allPeriodStates_getLast? {n : ℕ} [NeZero n]
    (N : ℕ) :
    (ons_allPeriodStates n N).getLast? =
      some (N, ons_lastFin n) := by
  rw [ons_allPeriodStates, List.range_succ, List.flatMap_append]
  simp

theorem ons_allPeriodStates_isChain {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (N : ℕ) :
    List.IsChain
      (fun a b ↦ ons_periodStateCoord d b =
        ons_periodStateCoord d a + stepOf (d a.2))
      (ons_allPeriodStates n N) := by
  induction N with
  | zero =>
      simpa [ons_allPeriodStates] using ons_periodStateList_isChain d 0
  | succ N ih =>
      rw [ons_allPeriodStates, List.range_succ,
        List.flatMap_append]
      simp only [List.flatMap_singleton]
      apply List.IsChain.append
        (by simpa [ons_allPeriodStates] using ih)
        (ons_periodStateList_isChain d (N + 1))
      intro a ha b hb
      have ha' : a = (N, ons_lastFin n) := by
        change a ∈ (ons_allPeriodStates n N).getLast? at ha
        have := ha
        rw [ons_allPeriodStates_getLast?] at this
        symm
        simpa using this
      have hb' : b = (N + 1, (0 : Fin n)) := by
        change b ∈ (ons_periodStateList n (N + 1)).head? at hb
        have := hb
        rw [ons_periodStateList_head?] at this
        symm
        simpa using this
      rw [ha', hb']
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
      change ons_periodStateCoord d (N + 1, 0) =
        ons_periodStateCoord d (N, Fin.last m) +
          stepOf (d (Fin.last m))
      exact ons_periodState_boundary d N

theorem ons_periodicArcStates_isChain {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (N : ℕ) (imin imax : Fin n) :
    List.IsChain
      (fun a b ↦ ons_periodStateCoord d b =
        ons_periodStateCoord d a + stepOf (d a.2))
      (ons_periodicArcStates N imin imax) := by
  exact (ons_allPeriodStates_isChain d N).drop imin.val |>.take _

@[simp] theorem ons_periodicArcStates_head? {n : ℕ} [NeZero n]
    (N : ℕ) (hN : 1 ≤ N) (imin imax : Fin n) :
    (ons_periodicArcStates N imin imax).head? = some (0, imin) := by
  have hcount : N * n + imax.val + 1 - imin.val ≠ 0 := by
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have hmul : n ≤ N * n := by
      exact Nat.le_mul_of_pos_left n (by omega)
    omega
  rw [ons_periodicArcStates, List.head?_take, if_neg hcount,
    List.head?_drop, ons_allPeriodStates, List.range_succ_eq_map]
  simp only [List.flatMap_cons, ons_periodStateList_length]
  rw [List.getElem?_append_left (by simpa using imin.isLt)]
  rw [ons_periodStateList, List.getElem?_ofFn, dif_pos imin.isLt]

@[simp] theorem ons_periodicArcStates_getLast? {n : ℕ} [NeZero n]
    (N : ℕ) (hN : 1 ≤ N) (imin imax : Fin n) :
    (ons_periodicArcStates N imin imax).getLast? =
      some (N, imax) := by
  let count := N * n + imax.val + 1 - imin.val
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hmul : n ≤ N * n := Nat.le_mul_of_pos_left n (by omega)
  have hcount : count ≠ 0 := by
    dsimp [count]
    omega
  rw [ons_periodicArcStates, List.getLast?_take, if_neg hcount,
    List.getElem?_drop]
  have hidx : imin.val + (count - 1) = N * n + imax.val := by
    dsimp [count]
    omega
  rw [hidx, ons_allPeriodStates, List.range_succ,
    List.flatMap_append]
  simp only [List.flatMap_singleton]
  rw [List.getElem?_append_right (by
    simp [List.length_flatMap])]
  simp [ons_periodStateList, List.getElem?_ofFn, imax.isLt]

def ons_periodicArcDirections {n : ℕ}
    (d : Fin n → Fin 4) (N : ℕ) (imin imax : Fin n) :
    List (Fin 4) :=
  (ons_periodicArcStates N imin imax).dropLast.map
    (fun z ↦ d z.2)

theorem ons_pathVertices_map_dropLast_of_chain
    {X : Type*} [Inhabited X]
    (coord : X → ℤ × ℤ) (dir : X → Fin 4)
    (s : List X) (hs : s ≠ [])
    (hchain : List.IsChain
      (fun a b ↦ coord b = coord a + stepOf (dir a)) s) :
    ons_pathVertices (s.dropLast.map dir) =
      s.map (fun x ↦ coord x - coord s.head!) := by
  induction s with
  | nil => exact (hs rfl).elim
  | cons a as ih =>
      cases as with
      | nil => simp [ons_pathVertices, List.head!]
      | cons b bs =>
          have hc := List.isChain_cons_cons.mp hchain
          have ih' := ih (by simp) hc.2
          rw [List.dropLast_cons_of_ne_nil (by simp), List.map_cons,
            ons_pathVertices_cons, ih']
          simp only [List.map_cons, List.cons.injEq, List.head!,
            sub_self, true_and]
          constructor
          · rw [hc.1]
            abel
          · rw [List.map_map]
            apply List.map_congr_left
            intro x hx
            simp only [Function.comp_apply]
            rw [hc.1]
            abel

theorem ons_periodicArc_pathVertices {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (N : ℕ) (hN : 1 ≤ N)
    (imin imax : Fin n) :
    ons_pathVertices (ons_periodicArcDirections d N imin imax) =
      (ons_periodicArcStates N imin imax).map
        (fun z ↦ ons_periodStateCoord d z -
          ons_periodStateCoord d (0, imin)) := by
  rw [ons_periodicArcDirections]
  have hs : ons_periodicArcStates N imin imax ≠ [] := by
    intro h
    have hh := ons_periodicArcStates_head? N hN imin imax
    rw [h] at hh
    simp at hh
  have h := ons_pathVertices_map_dropLast_of_chain
    (ons_periodStateCoord d) (fun z ↦ d z.2)
    (ons_periodicArcStates N imin imax) hs
    (ons_periodicArcStates_isChain d N imin imax)
  rw [show (ons_periodicArcStates N imin imax).head! = (0, imin) by
    have hh := ons_periodicArcStates_head? N hN imin imax
    cases hs' : ons_periodicArcStates N imin imax with
    | nil => simp [hs'] at hh
    | cons a as => simpa [hs'] using hh] at h
  exact h

theorem ons_periodicArc_pathVertices_nodup {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (N : ℕ) (hN : 1 ≤ N)
    (imin imax : Fin n)
    (hinj : Function.Injective (ons_periodStateCoord d)) :
    (ons_pathVertices
      (ons_periodicArcDirections d N imin imax)).Nodup := by
  rw [ons_periodicArc_pathVertices d N hN imin imax]
  apply List.Nodup.map (by
    intro a b hab
    apply hinj
    apply sub_left_injective
    exact hab)
  exact ons_periodicArcStates_nodup N imin imax

theorem ons_periodicArc_displacement {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (N : ℕ) (hN : 1 ≤ N)
    (imin imax : Fin n) :
    ons_pathDisplacement (ons_periodicArcDirections d N imin imax) =
      ons_periodStateCoord d (N, imax) -
        ons_periodStateCoord d (0, imin) := by
  have hlast := ons_pathVertices_getLast
    (ons_periodicArcDirections d N imin imax)
  rw [ons_periodicArc_pathVertices d N hN imin imax,
    List.getLast?_map, ons_periodicArcStates_getLast? N hN] at hlast
  exact Option.some.inj hlast.symm

theorem ons_periodicArc_xmin {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (N : ℕ) (hN : 1 ≤ N)
    (imin imax : Fin n)
    (hmin : ∀ i, (pos d imin).1 ≤ (pos d i).1)
    (hD : 0 < (ons_pathDisplacement (List.ofFn d)).1) :
    ∀ z ∈ (ons_pathVertices
      (ons_periodicArcDirections d N imin imax)).dropLast,
      0 ≤ z.1 := by
  intro z hz
  have hz' : z ∈ ons_pathVertices
      (ons_periodicArcDirections d N imin imax) :=
    List.mem_of_mem_dropLast hz
  rw [ons_periodicArc_pathVertices d N hN imin imax,
    List.mem_map] at hz'
  obtain ⟨s, hs, rfl⟩ := hz'
  have hp := hmin s.2
  simp [ons_periodStateCoord, Prod.smul_mk]
  nlinarith [Nat.zero_le s.1]

theorem ons_periodicArc_xmax {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (N : ℕ) (hN : 1 ≤ N)
    (imin imax : Fin n)
    (hmax : ∀ i, (pos d i).1 ≤ (pos d imax).1)
    (hD : 0 < (ons_pathDisplacement (List.ofFn d)).1) :
    ∀ z ∈ (ons_pathVertices
      (ons_periodicArcDirections d N imin imax)).dropLast,
      z.1 ≤
        (ons_periodStateCoord d (N, imax) -
          ons_periodStateCoord d (0, imin)).1 := by
  intro z hz
  have hz' : z ∈ ons_pathVertices
      (ons_periodicArcDirections d N imin imax) :=
    List.mem_of_mem_dropLast hz
  rw [ons_periodicArc_pathVertices d N hN imin imax,
    List.mem_map] at hz'
  obtain ⟨s, hs, rfl⟩ := hz'
  have hp := hmax s.2
  have hr := ons_mem_periodicArcStates_fst_le N imin imax s hs
  simp [ons_periodStateCoord, Prod.smul_mk]
  nlinarith

theorem ons_exists_path_top (l : List (Fin 4)) (dy : ℤ) :
    ∃ top : ℤ, 0 < top ∧ dy < top ∧
      ∀ z ∈ (ons_pathVertices l).dropLast, z.2 < top := by
  let ys := ((ons_pathVertices l).dropLast.map
    (fun z ↦ z.2.natAbs)).sum
  let top : ℤ := (dy.natAbs + ys + 1 : ℕ)
  refine ⟨top, ?_, ?_, ?_⟩
  · simp [top]
    positivity
  · have hdy : dy ≤ (dy.natAbs : ℤ) := Int.le_natAbs
    simp only [top, Nat.cast_add, Nat.cast_one]
    have hys : (0 : ℤ) ≤ ys := by positivity
    omega
  · intro z hz
    have hmem : z.2.natAbs ∈
        (ons_pathVertices l).dropLast.map (fun w ↦ w.2.natAbs) :=
      List.mem_map.mpr ⟨z, hz, rfl⟩
    have hleNat : z.2.natAbs ≤ ys :=
      List.le_sum_of_mem hmem
    have hle : z.2 ≤ (z.2.natAbs : ℤ) := Int.le_natAbs
    have hcast : (z.2.natAbs : ℤ) ≤ ys := by exact_mod_cast hleNat
    simp only [top, Nat.cast_add, Nat.cast_one]
    have hdy0 : (0 : ℤ) ≤ dy.natAbs := by positivity
    omega

theorem ons_periodicArc_adjustedTurn_eq_four_or_neg_four
    {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (N : ℕ) (hN : 1 ≤ N)
    (imin imax : Fin n)
    (hinj : Function.Injective (ons_periodStateCoord d))
    (hmin : ∀ i, (pos d imin).1 ≤ (pos d i).1)
    (hmax : ∀ i, (pos d i).1 ≤ (pos d imax).1)
    (hD : 0 < (ons_pathDisplacement (List.ofFn d)).1) :
    let l := ons_periodicArcDirections d N imin imax
    ons_openTurnSum l + ons_turnPow l.getLast! 0 + 4 +
        ons_turnPow 0 l.head! = 4 ∨
      ons_openTurnSum l + ons_turnPow l.getLast! 0 + 4 +
        ons_turnPow 0 l.head! = -4 := by
  let l := ons_periodicArcDirections d N imin imax
  let delta := ons_periodStateCoord d (N, imax) -
    ons_periodStateCoord d (0, imin)
  have hdx : 0 < delta.1 := by
    have hp := hmin imax
    have hmul : 0 < (N : ℤ) *
        (ons_pathDisplacement (List.ofFn d)).1 := by
      positivity
    simp [delta, ons_periodStateCoord, Prod.smul_mk]
    nlinarith
  have hdisp : ons_pathDisplacement l = delta := by
    exact ons_periodicArc_displacement d N hN imin imax
  have hnodup : (ons_pathVertices l).Nodup :=
    ons_periodicArc_pathVertices_nodup d N hN imin imax hinj
  have hxmin := ons_periodicArc_xmin d N hN imin imax hmin hD
  have hxmax := ons_periodicArc_xmax d N hN imin imax hmax hD
  obtain ⟨top, htop, hdy, hymax⟩ := ons_exists_path_top l delta.2
  have hturn := ons_boundingClosure_turnSum_eq_four_or_neg_four
    l delta.1 delta.2 top hdx hdy htop hdisp hnodup hxmin hxmax hymax
  have hln : l ≠ [] := by
    intro hl
    have hslen := ons_periodicArcStates_length N hN imin imax
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have hmul : n ≤ N * n := Nat.le_mul_of_pos_left n (by omega)
    have hdirlen := congrArg List.length hl
    simp [l, ons_periodicArcDirections] at hdirlen
    omega
  rw [ons_boundingClosure_cyclicTurnSum l hln
    delta.1 delta.2 top hdx hdy htop] at hturn
  exact hturn

def ons_directionPeriods {n : ℕ}
    (d : Fin n → Fin 4) (N : ℕ) : List (Fin 4) :=
  (List.range N).flatMap (fun _ ↦ List.ofFn d)

theorem ons_allPeriodStates_map_direction {n : ℕ}
    (d : Fin n → Fin 4) (N : ℕ) :
    (ons_allPeriodStates n N).map (fun z ↦ d z.2) =
      ons_directionPeriods d (N + 1) := by
  simp [ons_allPeriodStates, ons_periodStateList,
    ons_directionPeriods, List.map_flatMap, List.map_ofFn]
  apply List.flatMap_congr
  intro r hr
  congr 1

theorem ons_dropLast_take_of_pos_le {X : Type*}
    (l : List X) (k : ℕ) (hk : 0 < k) (hle : k ≤ l.length) :
    (l.take k).dropLast = l.take (k - 1) := by
  rw [List.dropLast_eq_take, List.length_take, Nat.min_eq_left hle,
    List.take_take]
  rw [Nat.min_eq_left]
  omega

theorem ons_periodicArcDirections_eq_slice {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (N : ℕ) (hN : 1 ≤ N)
    (imin imax : Fin n) :
    ons_periodicArcDirections d N imin imax =
      ((ons_directionPeriods d (N + 1)).drop imin.val).take
        (N * n + imax.val - imin.val) := by
  let count := N * n + imax.val + 1 - imin.val
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hmul : n ≤ N * n := Nat.le_mul_of_pos_left n (by omega)
  have hcount : 0 < count := by
    dsimp [count]
    omega
  have hle : count ≤
      ((ons_directionPeriods d (N + 1)).drop imin.val).length := by
    rw [List.length_drop]
    simp [ons_directionPeriods, List.length_flatMap]
    rw [Nat.add_mul]
    dsimp [count]
    omega
  rw [ons_periodicArcDirections, ons_periodicArcStates,
    List.map_dropLast, List.map_take, List.map_drop,
    ons_allPeriodStates_map_direction,
    ons_dropLast_take_of_pos_le _ count hcount hle]
  congr 1
  dsimp [count]
  omega

@[simp] theorem ons_directionPeriods_length {n : ℕ}
    (d : Fin n → Fin 4) (N : ℕ) :
    (ons_directionPeriods d N).length = N * n := by
  simp [ons_directionPeriods, List.length_flatMap]

theorem ons_directionPeriods_succ {n : ℕ}
    (d : Fin n → Fin 4) (N : ℕ) :
    ons_directionPeriods d (N + 1) =
      ons_directionPeriods d N ++ List.ofFn d := by
  simp [ons_directionPeriods, List.range_succ, List.flatMap_append]

theorem ons_directionPeriods_append_comm {n : ℕ}
    (d : Fin n → Fin 4) (N : ℕ) :
    ons_directionPeriods d N ++ List.ofFn d =
      List.ofFn d ++ ons_directionPeriods d N := by
  induction N with
  | zero => simp [ons_directionPeriods]
  | succ N ih =>
      rw [show N + 1 = N + 1 by rfl, ons_directionPeriods_succ]
      rw [← List.append_assoc, ih, List.append_assoc]

theorem ons_directionPeriods_succ_left {n : ℕ}
    (d : Fin n → Fin 4) (N : ℕ) :
    ons_directionPeriods d (N + 1) =
      List.ofFn d ++ ons_directionPeriods d N := by
  rw [ons_directionPeriods_succ,
    ons_directionPeriods_append_comm]

theorem ons_periodicArcDirections_eq_blocks {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (N : ℕ) (hN : 1 ≤ N)
    (imin imax : Fin n) :
    ons_periodicArcDirections d N imin imax =
      (List.ofFn d).drop imin.val ++
        ons_directionPeriods d (N - 1) ++
        (List.ofFn d).take imax.val := by
  rw [ons_periodicArcDirections_eq_slice d N hN,
    ons_directionPeriods_succ_left]
  rw [List.drop_append, List.take_append]
  simp only [List.length_ofFn]
  have hdrop : imin.val - n = 0 := by omega
  rw [hdrop, List.drop_zero]
  have hfirst :
      ((List.ofFn d).drop imin.val).take
          (N * n + imax.val - imin.val) =
        (List.ofFn d).drop imin.val := by
    apply (List.take_eq_self_iff _).mpr
    rw [List.length_drop, List.length_ofFn]
    have hmul : n ≤ N * n := Nat.le_mul_of_pos_left n (by omega)
    omega
  rw [hfirst]
  rw [List.length_drop, List.length_ofFn]
  have hNsplit : N = (N - 1) + 1 := by omega
  have hmulEq : N * n = (N - 1) * n + n := by
    rw [hNsplit, Nat.add_mul]
    simp
  have hrem : N * n + imax.val - imin.val - (n - imin.val) =
      (N - 1) * n + imax.val := by
    rw [hmulEq]
    omega
  rw [hrem]
  conv_lhs =>
    rhs
    rw [hNsplit, ons_directionPeriods_succ]
  rw [List.take_append]
  simp only [ons_directionPeriods_length]
  have htakePeriods :
      (ons_directionPeriods d (N - 1)).take
          ((N - 1) * n + imax.val) =
        ons_directionPeriods d (N - 1) := by
    apply (List.take_eq_self_iff _).mpr
    simp
  have hnorm : N - 1 + 1 - 1 = N - 1 := by omega
  rw [hnorm]
  rw [htakePeriods]
  rw [Nat.add_sub_cancel_left]
  exact (List.append_assoc _ _ _).symm

theorem ons_getLast!_append_of_right_ne_nil {X : Type*} [Inhabited X]
    (l r : List X) (hr : r ≠ []) :
    (l ++ r).getLast! = r.getLast! := by
  have hlr : l ++ r ≠ [] := List.append_ne_nil_of_right_ne_nil l hr
  rw [ons_getLast!_eq_getLast (l ++ r) hlr,
    ons_getLast!_eq_getLast r hr]
  rw [List.getLast_append]
  simp [hr]

theorem ons_openTurnSum_insert_cycle
    (A D P : List (Fin 4)) (hA : A ≠ []) (hD : D ≠ [])
    (hlast : A.getLast! = D.getLast!)
    (hhead : P ≠ [] → P.head! = D.head!) :
    ons_openTurnSum (A ++ D ++ P) =
      ons_openTurnSum (A ++ P) + ons_cyclicTurnSum D := by
  have hAD : A ++ D ≠ [] := List.append_ne_nil_of_right_ne_nil A hD
  have hcyc : ons_cyclicTurnSum D =
      ons_openTurnSum D + ons_turnPow D.getLast! D.head! := by
    obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil hD
    rfl
  by_cases hP : P = []
  · subst P
    simp only [List.append_nil]
    rw [ons_openTurnSum_append A D hA hD, hcyc, hlast]
    abel
  · rw [ons_openTurnSum_append (A ++ D) P hAD hP,
      ons_openTurnSum_append A D hA hD,
      ons_openTurnSum_append A P hA hP,
      ons_getLast!_append_of_right_ne_nil A D hD,
      hhead hP, hcyc, hlast]
    abel

theorem ons_adjustedTurn_insert_cycle
    (A D P : List (Fin 4)) (hA : A ≠ []) (hD : D ≠ [])
    (hlast : A.getLast! = D.getLast!)
    (hhead : P ≠ [] → P.head! = D.head!) :
    let old := A ++ P
    let new := A ++ D ++ P
    ons_openTurnSum new + ons_turnPow new.getLast! 0 + 4 +
        ons_turnPow 0 new.head! =
      ons_openTurnSum old + ons_turnPow old.getLast! 0 + 4 +
        ons_turnPow 0 old.head! + ons_cyclicTurnSum D := by
  dsimp
  rw [ons_openTurnSum_insert_cycle A D P hA hD hlast hhead]
  have hheadOld : (A ++ P).head! = A.head! := by simp [hA]
  have hheadNew : (A ++ D ++ P).head! = A.head! := by simp [hA]
  rw [hheadOld, hheadNew]
  by_cases hP : P = []
  · subst P
    simp only [List.append_nil]
    rw [ons_getLast!_append_of_right_ne_nil A D hD, hlast]
    abel
  · rw [ons_getLast!_append_of_right_ne_nil A P hP,
      ons_getLast!_append_of_right_ne_nil (A ++ D) P hP]
    abel

theorem ons_ofFn_ne_nil {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) : List.ofFn d ≠ [] := by
  intro h
  have := congrArg List.length h
  simp at this
  exact NeZero.ne n this

theorem ons_drop_ofFn_ne_nil {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (i : Fin n) :
    (List.ofFn d).drop i.val ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [List.length_drop, List.length_ofFn] at this
  simp at this
  omega

theorem ons_drop_ofFn_getLast! {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (i : Fin n) :
    ((List.ofFn d).drop i.val).getLast! = (List.ofFn d).getLast! := by
  have hdrop := ons_drop_ofFn_ne_nil d i
  have hsplit := List.take_append_drop i.val (List.ofFn d)
  calc
    ((List.ofFn d).drop i.val).getLast! =
        ((List.ofFn d).take i.val ++
          (List.ofFn d).drop i.val).getLast! :=
      (ons_getLast!_append_of_right_ne_nil
        ((List.ofFn d).take i.val) ((List.ofFn d).drop i.val) hdrop).symm
    _ = (List.ofFn d).getLast! := congrArg List.getLast! hsplit

theorem ons_directionPeriods_getLast! {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (N : ℕ) (hN : 1 ≤ N) :
    (ons_directionPeriods d N).getLast! = (List.ofFn d).getLast! := by
  have hsplit : N = (N - 1) + 1 := by omega
  rw [hsplit, ons_directionPeriods_succ]
  exact ons_getLast!_append_of_right_ne_nil
    (ons_directionPeriods d (N - 1)) (List.ofFn d)
    (ons_ofFn_ne_nil d)

theorem ons_arcInitialBlock_getLast! {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (N : ℕ) (hN : 1 ≤ N)
    (imin : Fin n) :
    ((List.ofFn d).drop imin.val ++
      ons_directionPeriods d (N - 1)).getLast! =
        (List.ofFn d).getLast! := by
  by_cases hzero : N - 1 = 0
  · rw [hzero]
    change (((List.ofFn d).drop imin.val) ++ []).getLast! = _
    rw [List.append_nil]
    exact ons_drop_ofFn_getLast! d imin
  · have hpos : 1 ≤ N - 1 := Nat.one_le_iff_ne_zero.mpr hzero
    have hperiods : ons_directionPeriods d (N - 1) ≠ [] := by
      intro h
      have hlen := congrArg List.length h
      rw [ons_directionPeriods_length] at hlen
      simp at hlen
      rcases hlen with hleft | hright
      · exact hzero hleft
      · exact NeZero.ne n hright
    rw [ons_getLast!_append_of_right_ne_nil
      ((List.ofFn d).drop imin.val)
      (ons_directionPeriods d (N - 1)) hperiods]
    exact ons_directionPeriods_getLast! d (N - 1) hpos

theorem ons_head!_eq_head {X : Type*} [Inhabited X]
    (l : List X) (h : l ≠ []) :
    l.head! = l.head h := by
  cases l with
  | nil => exact (h rfl).elim
  | cons a as => rfl

theorem ons_take_ofFn_head! {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (i : Fin n)
    (h : (List.ofFn d).take i.val ≠ []) :
    ((List.ofFn d).take i.val).head! = (List.ofFn d).head! := by
  have hfull := ons_ofFn_ne_nil d
  rw [ons_head!_eq_head ((List.ofFn d).take i.val) h,
    ons_head!_eq_head (List.ofFn d) hfull]
  exact List.head_take h

theorem ons_periodicArc_adjustedTurn_succ {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (N : ℕ) (hN : 1 ≤ N)
    (imin imax : Fin n) :
    let old := ons_periodicArcDirections d N imin imax
    let new := ons_periodicArcDirections d (N + 1) imin imax
    ons_openTurnSum new + ons_turnPow new.getLast! 0 + 4 +
        ons_turnPow 0 new.head! =
      ons_openTurnSum old + ons_turnPow old.getLast! 0 + 4 +
        ons_turnPow 0 old.head! +
          ons_cyclicTurnSum (List.ofFn d) := by
  let S := (List.ofFn d).drop imin.val
  let M := ons_directionPeriods d (N - 1)
  let D := List.ofFn d
  let P := (List.ofFn d).take imax.val
  let A := S ++ M
  have hA : A ≠ [] := by
    exact List.append_ne_nil_of_left_ne_nil
      (ons_drop_ofFn_ne_nil d imin) M
  have hD : D ≠ [] := ons_ofFn_ne_nil d
  have hlast : A.getLast! = D.getLast! := by
    exact ons_arcInitialBlock_getLast! d N hN imin
  have hhead : P ≠ [] → P.head! = D.head! := by
    intro hP
    exact ons_take_ofFn_head! d imax hP
  have hinsert := ons_adjustedTurn_insert_cycle A D P hA hD hlast hhead
  dsimp only
  rw [ons_periodicArcDirections_eq_blocks d N hN,
    ons_periodicArcDirections_eq_blocks d (N + 1) (by omega)]
  have hsplit : N = (N - 1) + 1 := by omega
  have hper : ons_directionPeriods d N =
      ons_directionPeriods d (N - 1) ++ List.ofFn d := by
    conv_lhs => rw [hsplit]
    exact ons_directionPeriods_succ d (N - 1)
  have hsuccsub : N + 1 - 1 = N := by omega
  rw [hsuccsub, hper]
  simpa only [S, M, D, P, A, List.append_assoc] using hinsert

theorem ons_periodicSimple_cyclicTurnSum_eq_zero
    {n : ℕ} [NeZero n] (d : Fin n → Fin 4)
    (hinj : Function.Injective (ons_periodStateCoord d))
    (hD : 0 < (ons_pathDisplacement (List.ofFn d)).1) :
    ons_cyclicTurnSum (List.ofFn d) = 0 := by
  obtain ⟨imin, -, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun i : Fin n ↦ (pos d i).1) Finset.univ_nonempty
  obtain ⟨imax, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin n ↦ (pos d i).1) Finset.univ_nonempty
  have hmin' : ∀ i, (pos d imin).1 ≤ (pos d i).1 := by
    intro i
    exact hmin i (Finset.mem_univ i)
  have hmax' : ∀ i, (pos d i).1 ≤ (pos d imax).1 := by
    intro i
    exact hmax i (Finset.mem_univ i)
  let adj (N : ℕ) : ℤ :=
    let l := ons_periodicArcDirections d N imin imax
    ons_openTurnSum l + ons_turnPow l.getLast! 0 + 4 +
      ons_turnPow 0 l.head!
  have h1 : adj 1 = 4 ∨ adj 1 = -4 := by
    simpa [adj] using ons_periodicArc_adjustedTurn_eq_four_or_neg_four
      d 1 (by omega) imin imax hinj hmin' hmax' hD
  have h2 : adj 2 = 4 ∨ adj 2 = -4 := by
    simpa [adj] using ons_periodicArc_adjustedTurn_eq_four_or_neg_four
      d 2 (by omega) imin imax hinj hmin' hmax' hD
  have h3 : adj 3 = 4 ∨ adj 3 = -4 := by
    simpa [adj] using ons_periodicArc_adjustedTurn_eq_four_or_neg_four
      d 3 (by omega) imin imax hinj hmin' hmax' hD
  have h12 : adj 2 = adj 1 + ons_cyclicTurnSum (List.ofFn d) := by
    simpa [adj] using ons_periodicArc_adjustedTurn_succ
      d 1 (by omega) imin imax
  have h23 : adj 3 = adj 2 + ons_cyclicTurnSum (List.ofFn d) := by
    simpa [adj] using ons_periodicArc_adjustedTurn_succ
      d 2 (by omega) imin imax
  rw [h12] at h2
  have h13 : adj 3 = adj 1 +
      2 * ons_cyclicTurnSum (List.ofFn d) := by
    rw [h23, h12]
    ring
  rw [h13] at h3
  exact ons_three_values_force_step_zero
    (adj 1) (ons_cyclicTurnSum (List.ofFn d)) h1 h2 h3

def ons_rotatePoint (c : Fin 4) (p : ℤ × ℤ) : ℤ × ℤ :=
  match c.val with
  | 0 => p
  | 1 => (-p.2, p.1)
  | 2 => (-p.1, -p.2)
  | _ => (p.2, -p.1)

theorem ons_rotatePoint_add (c : Fin 4) (p q : ℤ × ℤ) :
    ons_rotatePoint c (p + q) =
      ons_rotatePoint c p + ons_rotatePoint c q := by
  fin_cases c <;> apply Prod.ext <;> simp [ons_rotatePoint] <;> ring

theorem ons_rotatePoint_nsmul (c : Fin 4) (k : ℕ) (p : ℤ × ℤ) :
    ons_rotatePoint c (k • p) = k • ons_rotatePoint c p := by
  induction k with
  | zero => fin_cases c <;> simp [ons_rotatePoint]
  | succ k ih => rw [succ_nsmul, succ_nsmul, ons_rotatePoint_add, ih]

theorem ons_rotatePoint_injective (c : Fin 4) :
    Function.Injective (ons_rotatePoint c) := by
  intro p q h
  fin_cases c <;>
    have hfst := congrArg Prod.fst h <;>
    have hsnd := congrArg Prod.snd h <;>
    apply Prod.ext <;>
    simp [ons_rotatePoint] at hfst hsnd ⊢ <;> omega

theorem ons_stepOf_add_direction (c d : Fin 4) :
    stepOf (d + c) = ons_rotatePoint c (stepOf d) := by
  fin_cases c <;> fin_cases d <;> rfl

theorem ons_pathDisplacement_map_add
    (c : Fin 4) (l : List (Fin 4)) :
    ons_pathDisplacement (l.map (fun d ↦ d + c)) =
      ons_rotatePoint c (ons_pathDisplacement l) := by
  induction l with
  | nil => fin_cases c <;> rfl
  | cons d ds ih =>
      simp only [List.map_cons, ons_pathDisplacement_cons, ih,
        ons_stepOf_add_direction, ons_rotatePoint_add]

theorem ons_pos_add_direction {n : ℕ} [NeZero n]
    (c : Fin 4) (d : Fin n → Fin 4) (i : Fin n) :
    pos (fun j ↦ d j + c) i = ons_rotatePoint c (pos d i) := by
  unfold pos
  induction (Finset.univ.filter (fun x ↦ x < i)) using Finset.induction with
  | empty => fin_cases c <;> rfl
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ih,
        ons_stepOf_add_direction, ons_rotatePoint_add]

theorem ons_periodStateCoord_add_direction
    {n : ℕ} [NeZero n]
    (c : Fin 4) (d : Fin n → Fin 4) (z : ℕ × Fin n) :
    ons_periodStateCoord (fun i ↦ d i + c) z =
      ons_rotatePoint c (ons_periodStateCoord d z) := by
  have hlist : List.ofFn (fun i ↦ d i + c) =
      (List.ofFn d).map (fun e ↦ e + c) := by
    rw [List.map_ofFn]
    congr 1
  have hdisp : ons_pathDisplacement (List.ofFn (fun i ↦ d i + c)) =
      ons_rotatePoint c (ons_pathDisplacement (List.ofFn d)) := by
    rw [hlist, ons_pathDisplacement_map_add]
  rw [ons_periodStateCoord, ons_periodStateCoord,
    ons_pos_add_direction, hdisp, ← ons_rotatePoint_nsmul,
    ← ons_rotatePoint_add]

theorem ons_turnPow_add_both (a b c : Fin 4) :
    ons_turnPow (a + c) (b + c) = ons_turnPow a b := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

theorem ons_cyclicTurnSum_ofFn_add_direction
    {n : ℕ} [NeZero n] (c : Fin 4) (d : Fin n → Fin 4) :
    ons_cyclicTurnSum (List.ofFn (fun i ↦ d i + c)) =
      ons_cyclicTurnSum (List.ofFn d) := by
  rw [ons_cyclicTurnSum_ofFn', ons_cyclicTurnSum_ofFn']
  apply Finset.sum_congr rfl
  intro i hi
  exact ons_turnPow_add_both (d i) (d (i + 1)) c

theorem ons_periodicSimple_cyclicTurnSum_eq_zero_of_nonzero
    {n : ℕ} [NeZero n] (d : Fin n → Fin 4)
    (hinj : Function.Injective (ons_periodStateCoord d))
    (hne : (ons_pathDisplacement (List.ofFn d)).1 ≠ 0 ∨
      (ons_pathDisplacement (List.ofFn d)).2 ≠ 0) :
    ons_cyclicTurnSum (List.ofFn d) = 0 := by
  let D := ons_pathDisplacement (List.ofFn d)
  change D.1 ≠ 0 ∨ D.2 ≠ 0 at hne
  let solve (c : Fin 4)
      (hpos : 0 < (ons_rotatePoint c D).1) :
      ons_cyclicTurnSum (List.ofFn d) = 0 := by
    let dr : Fin n → Fin 4 := fun i ↦ d i + c
    have hcoord : ∀ z, ons_periodStateCoord dr z =
        ons_rotatePoint c (ons_periodStateCoord d z) :=
      ons_periodStateCoord_add_direction c d
    have hinjr : Function.Injective (ons_periodStateCoord dr) := by
      intro x y hxy
      apply hinj
      apply ons_rotatePoint_injective c
      rw [← hcoord x, ← hcoord y]
      exact hxy
    have hDr : 0 < (ons_pathDisplacement (List.ofFn dr)).1 := by
      rw [show List.ofFn dr = (List.ofFn d).map (fun e ↦ e + c) by
        rw [List.map_ofFn]
        congr 1]
      rw [ons_pathDisplacement_map_add]
      exact hpos
    have hz := ons_periodicSimple_cyclicTurnSum_eq_zero dr hinjr hDr
    rw [ons_cyclicTurnSum_ofFn_add_direction c d] at hz
    exact hz
  by_cases hx0 : D.1 = 0
  · have hy : D.2 ≠ 0 := hne.resolve_left (not_ne_iff.mpr hx0)
    by_cases hyp : 0 < D.2
    · exact solve 3 (by simpa [ons_rotatePoint] using hyp)
    · exact solve 1 (by
        have : D.2 < 0 := lt_of_le_of_ne (le_of_not_gt hyp) hy
        simpa [ons_rotatePoint] using neg_pos.mpr this)
  · by_cases hxp : 0 < D.1
    · exact solve 0 (by simpa [ons_rotatePoint] using hxp)
    · exact solve 2 (by
        have : D.1 < 0 := lt_of_le_of_ne (le_of_not_gt hxp) hx0
        simpa [ons_rotatePoint] using neg_pos.mpr this)

theorem ons_liftDir_periodStateCoord_eq_periodicLiftVertex
    {L n : ℕ} [NeZero n]
    (v : Fin n → ons_Dart L) (mx my : ℤ)
    (hmx : (∑ k, ons_dirExponentX (v k).2) = (L : ℤ) * mx)
    (hmy : (∑ k, ons_dirExponentY (v k).2) = (L : ℤ) * my)
    (z : ℕ × Fin n) :
    ons_periodStateCoord (ons_liftDir v) z =
      ons_periodicLiftVertex v mx my (z.1 : ℤ) z.2 := by
  rw [ons_periodStateCoord, ons_periodicLiftVertex]
  have hdisp : ons_pathDisplacement (List.ofFn (ons_liftDir v)) =
      ons_windingTranslation L mx my := by
    rw [ons_pathDisplacement_ofFn]
    exact ons_liftDir_totalStep_eq_windingTranslation v mx my hmx hmy
  rw [hdisp]
  unfold ons_windingTranslation
  apply Prod.ext <;> simp [Prod.smul_mk] <;> ring

theorem ons_liftDir_periodStateCoord_injective
    {L n : ℕ} [NeZero L] [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k ↦ (v k).1))
    (mx my : ℤ) (hne : mx ≠ 0 ∨ my ≠ 0)
    (hmx : (∑ k, ons_dirExponentX (v k).2) = (L : ℤ) * mx)
    (hmy : (∑ k, ons_dirExponentY (v k).2) = (L : ℤ) * my) :
    Function.Injective (ons_periodStateCoord (ons_liftDir v)) := by
  intro x y hxy
  have hp : ons_periodicLiftVertex v mx my (x.1 : ℤ) x.2 =
      ons_periodicLiftVertex v mx my (y.1 : ℤ) y.2 := by
    rw [← ons_liftDir_periodStateCoord_eq_periodicLiftVertex
      v mx my hmx hmy x,
      ← ons_liftDir_periodStateCoord_eq_periodicLiftVertex
      v mx my hmx hmy y]
    exact hxy
  have hpair : ((x.1 : ℤ), x.2) = ((y.1 : ℤ), y.2) :=
    (ons_periodicLiftVertex_injective
      v hvalid hsite mx my hne) hp
  apply Prod.ext
  · exact Int.ofNat_inj.mp
      (congrArg (fun z : ℤ × Fin n ↦ z.1) hpair)
  · exact congrArg (fun z : ℤ × Fin n ↦ z.2) hpair

theorem ons_liftDir_displacement_nonzero
    {L n : ℕ} [NeZero L] [NeZero n]
    (v : Fin n → ons_Dart L) (mx my : ℤ)
    (hne : mx ≠ 0 ∨ my ≠ 0)
    (hmx : (∑ k, ons_dirExponentX (v k).2) = (L : ℤ) * mx)
    (hmy : (∑ k, ons_dirExponentY (v k).2) = (L : ℤ) * my) :
    (ons_pathDisplacement (List.ofFn (ons_liftDir v))).1 ≠ 0 ∨
      (ons_pathDisplacement (List.ofFn (ons_liftDir v))).2 ≠ 0 := by
  rw [ons_pathDisplacement_ofFn,
    ons_liftDir_totalStep_eq_windingTranslation v mx my hmx hmy]
  unfold ons_windingTranslation
  have hL : (L : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne L
  rcases hne with hx | hy
  · left
    exact mul_ne_zero hL hx
  · right
    exact mul_ne_zero hL hy

theorem ons_noncontractible_liftDir_cyclicTurnSum_eq_zero
    {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k ↦ (v k).1))
    (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
    (hhom : ons_evenHomology L (ons_dartEdgeSet v) ≠ 0) :
    ons_cyclicTurnSum (List.ofFn (ons_liftDir v)) = 0 := by
  obtain ⟨mx, my, hmx, hmy, hne, -⟩ :=
    ons_simpleLoop_nonzeroHomology_periodicLift
      v hvalid hsite hnu hhom
  apply ons_periodicSimple_cyclicTurnSum_eq_zero_of_nonzero
    (ons_liftDir v)
    (ons_liftDir_periodStateCoord_injective
      v hvalid hsite mx my hne hmx hmy)
    (ons_liftDir_displacement_nonzero v mx my hne hmx hmy)

theorem ons_noncontractible_turnProduct_eq_one
    {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (omega : ℂ) (homega : omega ≠ 0)
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k ↦ (v k).1))
    (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
    (hhom : ons_evenHomology L (ons_dartEdgeSet v) ≠ 0) :
    ∏ k, ons_turnW omega (v (k + 1)).2 (v k).2 = 1 := by
  rw [ons_liftDir_turnProduct omega v]
  calc
    (∏ k, ons_turnW omega (ons_liftDir v k)
        (ons_liftDir v (k + 1))) =
        ∏ k, omega ^ ons_turnPow (ons_liftDir v k)
          (ons_liftDir v (k + 1)) := by
      apply Finset.prod_congr rfl
      intro k hk
      exact ons_turnW_eq_zpow omega _ _
        (ons_liftDir_nonUturn v hnu k)
    _ = omega ^ (∑ k, ons_turnPow (ons_liftDir v k)
          (ons_liftDir v (k + 1))) :=
      ons_prod_zpow omega homega _ _
    _ = 1 := by
      have hz := ons_noncontractible_liftDir_cyclicTurnSum_eq_zero
        v hvalid hsite hnu hhom
      rw [ons_cyclicTurnSum_ofFn'] at hz
      rw [hz]
      simp

theorem ons_decExpanded_turnProduct_eq_one_of_nonzeroHomology
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d)
    (hhom : ons_evenHomology L (ons_walkOriginalEdges q) ≠ 0) :
    letI : NeZero (ons_decExpandedDartList L q).length :=
      ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
    ∏ k, ons_turnW ons_turnRoot
        (ons_decExpandedKWLoop L q hq (k + 1)).2
        (ons_decExpandedKWLoop L q hq k).2 = 1 := by
  letI : Fact (2 < 8 * L) := ⟨by
    have := (Fact.out : 2 < L)
    omega⟩
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  have hroot : ons_turnRoot ≠ 0 := by
    intro h
    have hs := ons_turnRoot_sq
    rw [h] at hs
    have hs' : (0 : ℂ) = Complex.I := by simpa using hs
    exact Complex.I_ne_zero hs'.symm
  have hrefined : ons_evenHomology (8 * L)
      (ons_dartEdgeSet (ons_decExpandedKWLoop L q hq)) ≠ 0 := by
    rw [ons_decExpandedKWLoop_edgeSet L q hq]
    rw [ons_decEmbedWalk_evenHomology_eq L q hq hsnd]
    exact hhom
  exact ons_noncontractible_turnProduct_eq_one
    ons_turnRoot hroot (ons_decExpandedKWLoop L q hq)
    (ons_decExpandedKWLoop_valid L q hq)
    (ons_decExpandedKWLoop_site_injective L q hq)
    (ons_decExpandedKWLoop_nonUturn L q hq) hrefined

end StatMech.Onsager
