/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Sharpness.ABInfiniteGhost
import Code.FK.TranslationCofinal

open Filter MeasureTheory Set SimpleGraph Topology
open scoped BigOperators

namespace StatMech
namespace Sharpness

open ConfigSpace
open StatMech.Lattice



noncomputable def ablBoxFinset (d n : Nat) : Finset (Site d) :=
  (box_finite d n).toFinset

@[simp] theorem mem_ablBoxFinset {d n : Nat} {x : Site d} :
    x ∈ ablBoxFinset d n ↔ x ∈ box d n := by
  simp [ablBoxFinset]

theorem zero_mem_ablBoxFinset (d n : Nat) :
    (0 : Site d) ∈ ablBoxFinset d n := by
  rw [mem_ablBoxFinset, mem_box]
  intro i
  simp

theorem ablBoxFinset_mono (d : Nat) : Monotone (ablBoxFinset d) := by
  intro m n hmn x hx
  rw [mem_ablBoxFinset] at hx ⊢
  exact box_mono d hmn hx

theorem ablGhostWindow_mono (d : Nat) :
    Monotone (fun n => abigGhostWindow (ablBoxFinset d n)) := by
  intro m n hmn z hz
  simp only [abigGhostWindow, Finset.mem_union, Finset.mem_image,
    Finset.mem_singleton] at hz ⊢
  rcases hz with ⟨x, hx, rfl⟩ | rfl
  · exact Or.inl ⟨x, ablBoxFinset_mono d hmn hx, rfl⟩
  · exact Or.inr rfl



theorem ablGhostWindow_cover (d : Nat) (F : Finset (Option (Site d))) :
    ∃ n, F ⊆ abigGhostWindow (ablBoxFinset d n) := by
  classical
  let radius : Site d → Nat := fun x =>
    Finset.univ.sup (fun i : Fin d => (x i).natAbs)
  let n : Nat := F.sup (fun z => z.elim 0 radius)
  refine ⟨n, ?_⟩
  intro z hz
  rcases z with _ | x
  · simp [abigGhostWindow]
  · have hrn : radius x ≤ n := by
      exact Finset.le_sup (s := F) (f := fun z => z.elim 0 radius) hz
    have hxbox : x ∈ box d n := by
      rw [mem_box]
      intro i
      exact (Finset.le_sup (s := Finset.univ)
        (f := fun j : Fin d => (x j).natAbs) (Finset.mem_univ i)).trans hrn
    rw [abigGhostWindow, Finset.mem_union]
    exact Or.inl (Finset.mem_image.mpr
      ⟨x, mem_ablBoxFinset.mpr hxbox, rfl⟩)


theorem abl_row_comp_translate {d : Nat} (J : Sym2 (Site d) → Real)
    (hJinv : ∀ x u v,
      J s(FK.fktc_translate x u, FK.fktc_translate x v) = J s(u, v))
    (x : Site d) :
    (fun y => if (hypercubicLattice d).Adj x y then J s(x, y) else 0) ∘
        FK.fktc_translate x =
      fun y => if (hypercubicLattice d).Adj (0 : Site d) y
        then J s(0, y) else 0 := by
  funext y
  simp only [Function.comp_apply]
  have hx0 : FK.fktc_translate x (0 : Site d) = x := by
    funext i
    simp [FK.fktc_translate_apply]
  by_cases h : (hypercubicLattice d).Adj (0 : Site d) y
  · have h' : (hypercubicLattice d).Adj x (FK.fktc_translate x y) := by
      simpa only [hx0] using
        (FK.fktc_translate_adj x (0 : Site d) y).mpr h
    rw [if_pos h, if_pos h']
    simpa only [hx0] using hJinv x (0 : Site d) y
  · have h' : ¬ (hypercubicLattice d).Adj x (FK.fktc_translate x y) := by
      intro hxy
      apply h
      have hxy' : (hypercubicLattice d).Adj
          (FK.fktc_translate x (0 : Site d)) (FK.fktc_translate x y) := by
        simpa only [hx0] using hxy
      exact (FK.fktc_translate_adj x (0 : Site d) y).mp hxy'
    rw [if_neg h, if_neg h']


theorem abl_row_summable {d : Nat} (J : Sym2 (Site d) → Real)
    (hJinv : ∀ x u v,
      J s(FK.fktc_translate x u, FK.fktc_translate x v) = J s(u, v))
    (hsum0 : Summable (fun y =>
      if (hypercubicLattice d).Adj (0 : Site d) y then J s(0, y) else 0))
    (x : Site d) :
    Summable (fun y =>
      if (hypercubicLattice d).Adj x y then J s(x, y) else 0) := by
  apply (FK.fktc_translate x).summable_iff.mp
  simpa only [abl_row_comp_translate J hJinv x] using hsum0


theorem abl_row_tsum_eq {d : Nat} (J : Sym2 (Site d) → Real)
    (hJinv : ∀ x u v,
      J s(FK.fktc_translate x u, FK.fktc_translate x v) = J s(u, v))
    (x : Site d) :
    (∑' y, if (hypercubicLattice d).Adj x y then J s(x, y) else 0) =
      ∑' y, if (hypercubicLattice d).Adj (0 : Site d) y
        then J s(0, y) else 0 := by
  calc
    _ = ∑' y, if (hypercubicLattice d).Adj x (FK.fktc_translate x y)
          then J s(x, FK.fktc_translate x y) else 0 :=
        (Equiv.tsum_eq (FK.fktc_translate x)
          (fun y => if (hypercubicLattice d).Adj x y then J s(x, y) else 0)).symm
    _ = _ := by
      apply tsum_congr
      intro y
      exact congrFun (abl_row_comp_translate J hJinv x) y









theorem abl_aizenmanBarsky_hypercubic_unconditional {d : Nat}
    (J : Sym2 (Site d) → Real)
    (hJ : ∀ e, 0 ≤ J e)
    (hJsupport : ∀ x y, ¬ (hypercubicLattice d).Adj x y → J s(x, y) = 0)
    (hJinv : ∀ x u v,
      J s(FK.fktc_translate x u, FK.fktc_translate x v) = J s(u, v))
    (hsum0 : Summable (fun y =>
      if (hypercubicLattice d).Adj (0 : Site d) y then J s(0, y) else 0)) :
    AizenmanBarskyInequalityPhysical
      (abigMag (hypercubicLattice d) J (0 : Site d))
      (∑' y, if (hypercubicLattice d).Adj (0 : Site d) y
        then J s(0, y) else 0) := by
  let J0 : Real := ∑' y, if (hypercubicLattice d).Adj (0 : Site d) y
    then J s(0, y) else 0
  apply abig_aizenmanBarskyPhysical_of_tsum_transitive_unconditional
    (hypercubicLattice d) J (0 : Site d) J0
    (move := FK.fktc_translate) (S := ablBoxFinset d)
  · apply tsum_nonneg
    intro y
    split_ifs
    · exact hJ _
    · exact le_rfl
  · exact hJ
  · exact hJsupport
  · exact abl_row_summable J hJinv hsum0
  · intro x
    exact le_of_eq (abl_row_tsum_eq J hJinv x)
  · intro x
    funext i
    simp [FK.fktc_translate_apply]
  · exact FK.fktc_translate_adj
  · exact hJinv
  · exact zero_mem_ablBoxFinset d
  · exact ablGhostWindow_mono d
  · exact ablGhostWindow_cover d



theorem abl_origin_row_tsum_eq {d : Nat} (J : Sym2 (Site d) → Real)
    (hJsupport : ∀ x y, ¬ (hypercubicLattice d).Adj x y → J s(x, y) = 0) :
    (∑' y, if (hypercubicLattice d).Adj (0 : Site d) y
        then J s(0, y) else 0) =
      ∑' y, J s((0 : Site d), y) := by
  apply tsum_congr
  intro y
  by_cases h : (hypercubicLattice d).Adj (0 : Site d) y
  · rw [if_pos h]
  · rw [if_neg h, hJsupport 0 y h]


theorem abl_aizenmanBarsky_hypercubic {d : Nat}
    (J : Sym2 (Site d) → Real)
    (hJ : ∀ e, 0 ≤ J e)
    (hJsupport : ∀ x y, ¬ (hypercubicLattice d).Adj x y → J s(x, y) = 0)
    (hJinv : ∀ x u v,
      J s(FK.fktc_translate x u, FK.fktc_translate x v) = J s(u, v))
    (hsum0 : Summable (fun y => J s((0 : Site d), y))) :
    AizenmanBarskyInequalityPhysical
      (abigMag (hypercubicLattice d) J (0 : Site d))
      (∑' y, J s((0 : Site d), y)) := by
  have hmasked : Summable (fun y =>
      if (hypercubicLattice d).Adj (0 : Site d) y
        then J s(0, y) else 0) := by
    apply hsum0.congr
    intro y
    by_cases h : (hypercubicLattice d).Adj (0 : Site d) y
    · rw [if_pos h]
    · rw [if_neg h, hJsupport 0 y h]
  have h := abl_aizenmanBarsky_hypercubic_unconditional
    J hJ hJsupport hJinv hmasked
  rwa [abl_origin_row_tsum_eq J hJsupport] at h

end Sharpness
end StatMech
