/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusSectors
import Code.FrontierA.SurfaceKacWardTwist










open scoped BigOperators

namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager



noncomputable def triangularTorusSurfaceEdgeClass (L : Nat) :
    Sym2 (ZMod L × ZMod L) → SurfaceHomology 1 :=
  fun edge =>
    (fun _ => if triangularTorusXSeamEdge L edge then 1 else 0,
      fun _ => if triangularTorusYSeamEdge L edge then 1 else 0)

private theorem not_triangularTorusXSeamEdge_diag
    (L : Nat) [Fact (2 < L)] (v : ZMod L × ZMod L) :
    ¬triangularTorusXSeamEdge L s(v, v) := by
  have hne : (1 : ZMod L) ≠ 0 := by
    letI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
    exact one_ne_zero
  have hnod (a b : ZMod L)
      (hdiag : s(v, v) = s(((0 : ZMod L), a), (-1, b))) : False := by
    rw [Sym2.eq_iff] at hdiag
    rcases hdiag with h | h
    · apply hne
      have hz : (0 : ZMod L) = -1 :=
        (congrArg Prod.fst h.1).symm.trans (congrArg Prod.fst h.2)
      simpa using congrArg (fun z : ZMod L => z + 1) hz
    · apply hne
      have hz : (0 : ZMod L) = -1 :=
        (congrArg Prod.fst h.2).symm.trans (congrArg Prod.fst h.1)
      simpa using congrArg (fun z : ZMod L => z + 1) hz
  rintro (⟨y, hy⟩ | ⟨y, hy⟩)
  · exact hnod y y hy
  · exact hnod y (y - 1) hy

private theorem not_triangularTorusYSeamEdge_diag
    (L : Nat) [Fact (2 < L)] (v : ZMod L × ZMod L) :
    ¬triangularTorusYSeamEdge L s(v, v) := by
  have hne : (1 : ZMod L) ≠ 0 := by
    letI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
    exact one_ne_zero
  have hnod (a b : ZMod L)
      (hdiag : s(v, v) = s((a, (0 : ZMod L)), (b, -1))) : False := by
    rw [Sym2.eq_iff] at hdiag
    rcases hdiag with h | h
    · apply hne
      have hz : (0 : ZMod L) = -1 :=
        (congrArg Prod.snd h.1).symm.trans (congrArg Prod.snd h.2)
      simpa using congrArg (fun z : ZMod L => z + 1) hz
    · apply hne
      have hz : (0 : ZMod L) = -1 :=
        (congrArg Prod.snd h.2).symm.trans (congrArg Prod.snd h.1)
      simpa using congrArg (fun z : ZMod L => z + 1) hz
  rintro (⟨x, hx⟩ | ⟨x, hx⟩)
  · exact hnod x x hx
  · exact hnod x (x - 1) hx



@[simp] theorem triangularTorusSurfaceEdgeClass_diag
    (L : Nat) [Fact (2 < L)] (v : ZMod L × ZMod L) :
    triangularTorusSurfaceEdgeClass L s(v, v) = 0 := by
  apply Prod.ext
  · funext i
    fin_cases i
    simp [triangularTorusSurfaceEdgeClass,
      not_triangularTorusXSeamEdge_diag L v]
  · funext i
    fin_cases i
    simp [triangularTorusSurfaceEdgeClass,
      not_triangularTorusYSeamEdge_diag L v]

private theorem fin2_sum_indicator_eq_card_filter_mod
    {α : Type*} [DecidableEq α] (F : Finset α) (P : α → Prop)
    [DecidablePred P] :
    (∑ x ∈ F, if P x then (1 : Fin 2) else 0) =
      ⟨(F.filter P).card % 2, Nat.mod_lt _ (by decide)⟩ := by
  induction F using Finset.induction_on with
  | empty => simp
  | @insert x F hx ih =>
      by_cases hP : P x
      · simp only [Finset.sum_insert hx, Finset.filter_insert, hP,
          ↓reduceIte, ih]
        apply Fin.ext
        simp [Fin.val_add, Nat.add_mod, hx]
        omega
      · simp [Finset.sum_insert hx, Finset.filter_insert, hP, ih]



theorem triangularTorus_surfaceSubgraphHomology_eq
    (L : Nat) (F : Finset (Sym2 (ZMod L × ZMod L))) :
    surfaceSubgraphHomology (triangularTorusSurfaceEdgeClass L) F =
      (fun _ => (triangularTorusEvenHomology L F).1,
        fun _ => (triangularTorusEvenHomology L F).2) := by
  classical
  apply Prod.ext
  · funext i
    fin_cases i
    simp only [surfaceSubgraphHomology, Prod.fst_sum, Finset.sum_apply,
      triangularTorusSurfaceEdgeClass]
    change (∑ edge ∈ F,
      if triangularTorusXSeamEdge L edge then (1 : Fin 2) else 0) = _
    rw [fin2_sum_indicator_eq_card_filter_mod]
    rfl
  · funext i
    fin_cases i
    simp only [surfaceSubgraphHomology, Prod.snd_sum, Finset.sum_apply,
      triangularTorusSurfaceEdgeClass]
    change (∑ edge ∈ F,
      if triangularTorusYSeamEdge L edge then (1 : Fin 2) else 0) = _
    rw [fin2_sum_indicator_eq_card_filter_mod]
    rfl



def triangularTorusSurfaceSpin (a b : Fin 2) : SurfaceSpinStructure 1 :=
  (fun _ => 1 + a, fun _ => 1 + b)



theorem triangularTorus_surfaceParitySign_eq_spinCharacter
    (a b : Fin 2) (h : Fin 2 × Fin 2) :
    surfaceParitySign
        (surfaceQuadraticParity (triangularTorusSurfaceSpin a b)
          (fun _ => h.1, fun _ => h.2)) =
      ons_spinCharacter a b h := by
  rcases h with ⟨x, y⟩
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;>
    norm_num [surfaceParitySign, surfaceQuadraticParity,
      triangularTorusSurfaceSpin, ons_spinCharacter, Fin.sum_univ_one,
      Fin.val_add]




theorem triangularTorus_surfaceQuadraticEvenPolynomial_eq
    (L : Nat) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → Complex) (a b : Fin 2) :
    surfaceQuadraticEvenPolynomial (triangularTorusGraph L)
        (triangularTorusSurfaceEdgeClass L)
        (triangularTorusSurfaceSpin a b) weight =
      triangularTorusWeightedSpinCharacterSum L weight a b := by
  classical
  unfold surfaceQuadraticEvenPolynomial
    triangularTorusWeightedSpinCharacterSum evenSubgraphs
  apply Finset.sum_congr rfl
  intro F hF
  rw [triangularTorus_surfaceSubgraphHomology_eq,
    triangularTorus_surfaceParitySign_eq_spinCharacter]

end StatMech.FrontierA
