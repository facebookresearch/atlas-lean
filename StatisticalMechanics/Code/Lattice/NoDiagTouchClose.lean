/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.Clusters
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.ContourLinksExits
import Code.Lattice.Umlaufsatz
import Code.Lattice.UmlaufsatzSingleCycle
import Code.Lattice.NoPinchDual
import Code.Lattice.NoPinchMatching
import Code.Lattice.Wall1EmbeddingRetry

open SimpleGraph Function Set

namespace StatMech

namespace Lattice










def ndt_product (A B : Set ℤ) : Set (Site 2) := {x | x 0 ∈ A ∧ x 1 ∈ B}





theorem ndt_kingSaturated_product (A B : Set ℤ) : npm_KingSaturated (ndt_product A B) := by
  intro f
  simp only [ndt_product, Set.mem_setOf_eq, npd_P00, npd_P11, npd_P10, npd_P01,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  exact ⟨fun h00 h11 => Or.inl ⟨h11.1, h00.2⟩, fun h10 h01 => Or.inl ⟨h01.1, h10.2⟩⟩


theorem ndt_box_eq_product (n : ℕ) :
    box 2 n = ndt_product {t : ℤ | t.natAbs ≤ n} {t : ℤ | t.natAbs ≤ n} := by
  ext x
  simp only [box, ndt_product, Set.mem_setOf_eq]
  refine ⟨fun h => ⟨h 0, h 1⟩, fun ⟨h0, h1⟩ i => ?_⟩
  fin_cases i
  · exact h0
  · exact h1




theorem ndt_kingSaturated_box (n : ℕ) : npm_KingSaturated (box 2 n) := by
  rw [ndt_box_eq_product]; exact ndt_kingSaturated_product _ _




def ndt_sublevel (φ ψ : ℤ → ℤ) (c : ℤ) : Set (Site 2) := {x | φ (x 0) + ψ (x 1) ≤ c}






theorem ndt_kingSaturated_sublevel (φ ψ : ℤ → ℤ) (c : ℤ) :
    npm_KingSaturated (ndt_sublevel φ ψ c) := by
  intro f
  simp only [ndt_sublevel, Set.mem_setOf_eq, npd_P00, npd_P11, npd_P10, npd_P01,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  refine ⟨fun h00 h11 => ?_, fun h10 h01 => ?_⟩
  · by_cases hh : φ (f 0 + 1) + ψ (f 1) ≤ c
    · exact Or.inl hh
    · exact Or.inr (by omega)
  · by_cases hh : φ (f 0) + ψ (f 1) ≤ c
    · exact Or.inl hh
    · exact Or.inr (by omega)


















inductive ndt_StarHullMem (K : Set (Site 2)) : Site 2 → Prop
  | base {x : Site 2} (h : x ∈ K) : ndt_StarHullMem K x
  | fillBL {f : Site 2} (h00 : ndt_StarHullMem K (npd_P00 f))
      (h11 : ndt_StarHullMem K (npd_P11 f)) : ndt_StarHullMem K (npd_P10 f)
  | fillTL {f : Site 2} (h10 : ndt_StarHullMem K (npd_P10 f))
      (h01 : ndt_StarHullMem K (npd_P01 f)) : ndt_StarHullMem K (npd_P00 f)


def ndt_StarHull (K : Set (Site 2)) : Set (Site 2) := {x | ndt_StarHullMem K x}


theorem ndt_subset_starHull (K : Set (Site 2)) : K ⊆ ndt_StarHull K :=
  fun _ h => ndt_StarHullMem.base h







theorem ndt_kingSaturated_starHull (K : Set (Site 2)) : npm_KingSaturated (ndt_StarHull K) := by
  intro f
  exact ⟨fun h00 h11 => Or.inl (ndt_StarHullMem.fillBL h00 h11),
         fun h10 h01 => Or.inl (ndt_StarHullMem.fillTL h10 h01)⟩







theorem ndt_noDiagTouch (K : Set (Site 2)) : npd_NoDiagTouch (ndt_StarHull K) :=
  npm_noDiagTouch_of_kingSaturated (ndt_kingSaturated_starHull K)









theorem ndt_starHull_empty : ndt_StarHull (∅ : Set (Site 2)) = ∅ := by
  ext x
  simp only [ndt_StarHull, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hx
  induction hx with
  | base h => exact h
  | fillBL _ _ ih00 _ => exact ih00
  | fillTL h10 _ ih10 _ => exact ih10


def ndt_FillClosed (S : Set (Site 2)) : Prop :=
  (∀ f, npd_P00 f ∈ S → npd_P11 f ∈ S → npd_P10 f ∈ S) ∧
  (∀ f, npd_P10 f ∈ S → npd_P01 f ∈ S → npd_P00 f ∈ S)





theorem ndt_starHull_subset_of_fillClosed {K S : Set (Site 2)} (hKS : K ⊆ S)
    (hS : ndt_FillClosed S) : ndt_StarHull K ⊆ S := by
  intro x hx
  induction hx with
  | base h => exact hKS h
  | @fillBL f _ _ ih00 ih11 => exact hS.1 f ih00 ih11
  | @fillTL f _ _ ih10 ih01 => exact hS.2 f ih10 ih01


theorem ndt_fillClosed_product (A B : Set ℤ) : ndt_FillClosed (ndt_product A B) := by
  refine ⟨fun f h00 h11 => ?_, fun f h10 h01 => ?_⟩
  · simp only [ndt_product, Set.mem_setOf_eq, npd_P00, npd_P11, npd_P10,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at *
    exact ⟨h11.1, h00.2⟩
  · simp only [ndt_product, Set.mem_setOf_eq, npd_P10, npd_P01, npd_P00,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at *
    exact ⟨h01.1, h10.2⟩





theorem ndt_starHull_product (A B : Set ℤ) :
    ndt_StarHull (ndt_product A B) = ndt_product A B :=
  Set.Subset.antisymm
    (ndt_starHull_subset_of_fillClosed (le_refl _) (ndt_fillClosed_product A B))
    (ndt_subset_starHull _)



theorem ndt_starHull_box (n : ℕ) : ndt_StarHull (box 2 n) = box 2 n := by
  rw [ndt_box_eq_product, ndt_starHull_product]














theorem ndt_faceMultiplicityOne (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    usc_FaceMultiplicityOne (ndt_StarHull K) a :=
  emb_faceMultiplicityOne_of_kingSaturated (ndt_StarHull K) a (ndt_kingSaturated_starHull K)




theorem ndt_orbitFaceNoPinch (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    OrbitFaceNoPinch (ndt_StarHull K) a :=
  npm_orbitFaceNoPinch (ndt_StarHull K) a (ndt_kingSaturated_starHull K)







theorem ndt_orbit_isCycle (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hp : 3 ≤ dartOrbitPeriod (ndt_StarHull K) a) :
    ((dartOrbitFaceWalk (ndt_StarHull K) a.1 a.2 (dartOrbitPeriod (ndt_StarHull K) a)).copy rfl
      (by rw [orbit_iterate_period_eq (ndt_StarHull K) a])).IsCycle :=
  emb_orbit_isCycle_of_kingSaturated (ndt_StarHull K) a hp (ndt_kingSaturated_starHull K)









theorem ndt_box_noDiagTouch (n : ℕ) : npd_NoDiagTouch (box 2 n) :=
  npm_noDiagTouch_of_kingSaturated (ndt_kingSaturated_box n)



theorem ndt_box_faceMultiplicityOne (n : ℕ)
    (a : {e : Dart // IsBoundaryDart (box 2 n) e}) :
    usc_FaceMultiplicityOne (box 2 n) a :=
  emb_faceMultiplicityOne_of_kingSaturated (box 2 n) a (ndt_kingSaturated_box n)




theorem ndt_box_orbit_isCycle (n : ℕ)
    (a : {e : Dart // IsBoundaryDart (box 2 n) e})
    (hp : 3 ≤ dartOrbitPeriod (box 2 n) a) :
    ((dartOrbitFaceWalk (box 2 n) a.1 a.2 (dartOrbitPeriod (box 2 n) a)).copy rfl
      (by rw [orbit_iterate_period_eq (box 2 n) a])).IsCycle :=
  emb_orbit_isCycle_of_kingSaturated (box 2 n) a hp (ndt_kingSaturated_box n)







































end Lattice

end StatMech
