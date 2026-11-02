/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Sphere.SecondInter

namespace MetaMathlibExt

open scoped EuclideanSpace

@[expose] public section

private noncomputable local instance : Module.Oriented ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2) :=
  ⟨Module.Basis.orientation <| PiLp.basisFun 2 _ _⟩

private theorem miquel_aux_span_symm (P Q : EuclideanSpace ℝ (Fin 2)) :
    affineSpan ℝ ({P, Q} : Set (EuclideanSpace ℝ (Fin 2))) =
      affineSpan ℝ ({Q, P} : Set (EuclideanSpace ℝ (Fin 2))) :=
  AffineSubspace.affineSpan_pair_comm

private theorem miquel_aux_swap_mem {X P Q : EuclideanSpace ℝ (Fin 2)}
    (h : X ∈ affineSpan ℝ ({P, Q} : Set (EuclideanSpace ℝ (Fin 2)))) :
    X ∈ affineSpan ℝ ({Q, P} : Set (EuclideanSpace ℝ (Fin 2))) := by
  rwa [miquel_aux_span_symm] at h

private theorem miquel_aux_reorder {X Y Z X' Y' Z' : EuclideanSpace ℝ (Fin 2)}
    (e : ({X, Y, Z} : Set (EuclideanSpace ℝ (Fin 2))) = {X', Y', Z'})
    (h : Collinear ℝ ({X, Y, Z} : Set (EuclideanSpace ℝ (Fin 2)))) :
    Collinear ℝ ({X', Y', Z'} : Set (EuclideanSpace ℝ (Fin 2))) := by
  rwa [e] at h

private theorem miquel_aux_inter {P Q R X : EuclideanSpace ℝ (Fin 2)}
    (hABC : ¬ Collinear ℝ ({P, Q, R} : Set (EuclideanSpace ℝ (Fin 2))))
    (h1 : X ∈ affineSpan ℝ ({Q, R} : Set (EuclideanSpace ℝ (Fin 2))))
    (h2 : X ∈ affineSpan ℝ ({R, P} : Set (EuclideanSpace ℝ (Fin 2)))) :
    X = R := by
  by_contra hXR
  have hQRX : Collinear ℝ ({X, Q, R} : Set (EuclideanSpace ℝ (Fin 2))) :=
    collinear_insert_of_mem_affineSpan_pair h1
  have hRPX : Collinear ℝ ({X, R, P} : Set (EuclideanSpace ℝ (Fin 2))) :=
    collinear_insert_of_mem_affineSpan_pair h2
  have hQ : Q ∈ affineSpan ℝ ({R, X} : Set (EuclideanSpace ℝ (Fin 2))) :=
    hQRX.mem_affineSpan_of_mem_of_ne
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      (Set.mem_insert _ _)
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) (Ne.symm hXR)
  have hP : P ∈ affineSpan ℝ ({R, X} : Set (EuclideanSpace ℝ (Fin 2))) :=
    hRPX.mem_affineSpan_of_mem_of_ne (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      (Set.mem_insert _ _)
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      (Ne.symm hXR)
  have hQRX' : Collinear ℝ ({Q, R, X} : Set (EuclideanSpace ℝ (Fin 2))) :=
    (collinear_insert_iff_of_mem_affineSpan hQ).mpr (collinear_pair ℝ _ _)
  have hPmem : P ∈ affineSpan ℝ (insert Q ({R, X} : Set (EuclideanSpace ℝ (Fin 2)))) :=
    Set.mem_of_mem_of_subset hP
      (SetLike.coe_subset_coe.mpr (affineSpan_mono ℝ (Set.subset_insert Q {R, X})))
  have hPQRX : Collinear ℝ (insert P (insert Q ({R, X} : Set (EuclideanSpace ℝ (Fin 2))))) :=
    (collinear_insert_iff_of_mem_affineSpan hPmem).mpr hQRX'
  have hsub : ({P, Q, R} : Set (EuclideanSpace ℝ (Fin 2))) ⊆
      insert P (insert Q ({R, X} : Set (EuclideanSpace ℝ (Fin 2)))) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
    tauto
  exact hABC (Collinear.subset hsub hPQRX)

private theorem miquel_aux_noncoll {P Q R X Y : EuclideanSpace ℝ (Fin 2)}
    (hABC : ¬ Collinear ℝ ({P, Q, R} : Set (EuclideanSpace ℝ (Fin 2))))
    (hX : X ∈ affineSpan ℝ ({Q, R} : Set (EuclideanSpace ℝ (Fin 2))))
    (hY : Y ∈ affineSpan ℝ ({R, P} : Set (EuclideanSpace ℝ (Fin 2))))
    (hXR : X ≠ R) (hYR : Y ≠ R) :
    ¬ Collinear ℝ ({R, X, Y} : Set (EuclideanSpace ℝ (Fin 2))) := by
  intro hC
  have hXRY : X ∈ affineSpan ℝ ({R, Y} : Set (EuclideanSpace ℝ (Fin 2))) :=
    hC.mem_affineSpan_of_mem_of_ne (Set.mem_insert _ _)
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) (Ne.symm hYR)
  have hsubYX : ({R, Y} : Set (EuclideanSpace ℝ (Fin 2))) ⊆
      ↑(affineSpan ℝ ({R, P} : Set (EuclideanSpace ℝ (Fin 2)))) :=
    Set.insert_subset_iff.mpr
      ⟨left_mem_affineSpan_pair _ _ _, Set.singleton_subset_iff.mpr hY⟩
  have hle : affineSpan ℝ ({R, Y} : Set (EuclideanSpace ℝ (Fin 2))) ≤
      affineSpan ℝ ({R, P} : Set (EuclideanSpace ℝ (Fin 2))) :=
    affineSpan_le.mpr hsubYX
  have hXRP : X ∈ affineSpan ℝ ({R, P} : Set (EuclideanSpace ℝ (Fin 2))) :=
    Set.mem_of_mem_of_subset hXRY (SetLike.coe_subset_coe.mpr hle)
  exact hXR (miquel_aux_inter hABC hX hXRP)

private theorem miquel_aux_trisum {X Y Z : EuclideanSpace ℝ (Fin 2)}
    (hXY : X ≠ Y) (hYZ : Y ≠ Z) (hZX : Z ≠ X) :
    (2 : ℤ) • EuclideanGeometry.oangle X Y Z + (2 : ℤ) • EuclideanGeometry.oangle Y Z X +
      (2 : ℤ) • EuclideanGeometry.oangle Z X Y = 0 := by
  have hp : X -ᵥ Y ≠ 0 := vsub_ne_zero.mpr hXY
  have hq : Y -ᵥ Z ≠ 0 := vsub_ne_zero.mpr hYZ
  have hr : Z -ᵥ X ≠ 0 := vsub_ne_zero.mpr hZX
  have e1 : EuclideanGeometry.oangle X Y Z =
      Module.Oriented.positiveOrientation.oangle (X -ᵥ Y) (Z -ᵥ Y) := rfl
  have e2 : EuclideanGeometry.oangle Y Z X =
      Module.Oriented.positiveOrientation.oangle (Y -ᵥ Z) (X -ᵥ Z) := rfl
  have e3 : EuclideanGeometry.oangle Z X Y =
      Module.Oriented.positiveOrientation.oangle (Z -ᵥ X) (Y -ᵥ X) := rfl
  rw [e1, e2, e3, ← neg_vsub_eq_vsub_rev Y Z, ← neg_vsub_eq_vsub_rev Z X,
    ← neg_vsub_eq_vsub_rev X Y, Orientation.two_zsmul_oangle_neg_right _ _ _,
    Orientation.two_zsmul_oangle_neg_right _ _ _, Orientation.two_zsmul_oangle_neg_right _ _ _]
  have hadd : Module.Oriented.positiveOrientation.oangle (X -ᵥ Y) (Y -ᵥ Z) +
        Module.Oriented.positiveOrientation.oangle (Y -ᵥ Z) (Z -ᵥ X) =
      Module.Oriented.positiveOrientation.oangle (X -ᵥ Y) (Z -ᵥ X) :=
    Orientation.oangle_add _ hp hq hr
  have hadd2 : Module.Oriented.positiveOrientation.oangle (X -ᵥ Y) (Z -ᵥ X) +
        Module.Oriented.positiveOrientation.oangle (Z -ᵥ X) (X -ᵥ Y) =
      Module.Oriented.positiveOrientation.oangle (X -ᵥ Y) (X -ᵥ Y) :=
    Orientation.oangle_add _ hp hr hp
  have hself : Module.Oriented.positiveOrientation.oangle (X -ᵥ Y) (X -ᵥ Y) = 0 :=
    Orientation.oangle_self _ _
  calc (2 : ℤ) • Module.Oriented.positiveOrientation.oangle (X -ᵥ Y) (Y -ᵥ Z) +
          (2 : ℤ) • Module.Oriented.positiveOrientation.oangle (Y -ᵥ Z) (Z -ᵥ X) +
        (2 : ℤ) • Module.Oriented.positiveOrientation.oangle (Z -ᵥ X) (X -ᵥ Y)
        = (2 : ℤ) • (Module.Oriented.positiveOrientation.oangle (X -ᵥ Y) (Y -ᵥ Z) +
            Module.Oriented.positiveOrientation.oangle (Y -ᵥ Z) (Z -ᵥ X) +
          Module.Oriented.positiveOrientation.oangle (Z -ᵥ X) (X -ᵥ Y)) := by
        simp only [smul_add]
      _ = (2 : ℤ) • (Module.Oriented.positiveOrientation.oangle (X -ᵥ Y) (Z -ᵥ X) +
          Module.Oriented.positiveOrientation.oangle (Z -ᵥ X) (X -ᵥ Y)) := by
        rw [hadd]
      _ = (2 : ℤ) • Module.Oriented.positiveOrientation.oangle (X -ᵥ Y) (X -ᵥ Y) := by
        rw [hadd2]
      _ = 0 := by rw [hself, smul_zero]

private theorem miquel_aux_line_angle {A B C A' B' C' : EuclideanSpace ℝ (Fin 2)}
    (h1 : affineSpan ℝ ({A, B} : Set (EuclideanSpace ℝ (Fin 2))) =
      affineSpan ℝ ({A', B'} : Set (EuclideanSpace ℝ (Fin 2))))
    (h2 : affineSpan ℝ ({C, B} : Set (EuclideanSpace ℝ (Fin 2))) =
      affineSpan ℝ ({C', B'} : Set (EuclideanSpace ℝ (Fin 2)))) :
    (2 : ℤ) • EuclideanGeometry.oangle A B C =
      (2 : ℤ) • EuclideanGeometry.oangle A' B' C' := by
  refine EuclideanGeometry.two_zsmul_oangle_of_parallel ?_ ?_
  · rw [h1]; exact AffineSubspace.Parallel.refl _
  · rw [h2]; exact AffineSubspace.Parallel.refl _

private theorem miquel_aux_coll2 {X Y Z : EuclideanSpace ℝ (Fin 2)}
    (h : Collinear ℝ ({X, Y, Z} : Set (EuclideanSpace ℝ (Fin 2)))) :
    (2 : ℤ) • EuclideanGeometry.oangle X Y Z = 0 := by
  rw [Real.Angle.two_zsmul_eq_zero_iff]
  exact EuclideanGeometry.oangle_eq_zero_or_eq_pi_iff_collinear.mpr h

/-- **Miquel's theorem.** Let $A$, $B$, $C$ be non-collinear points of the Euclidean plane
$\mathbb{R}^2$, and let $D$, $E$, $F$ be points on the lines $BC$, $CA$, $AB$ respectively with
$D \ne B$, $D \ne C$, $E \ne C$, $E \ne A$, $F \ne A$ and $F \ne B$. If $A$, $E$, $F$ lie on the
circle with center $O_1$ and radius $r_1$, $B$, $F$, $D$ lie on the circle with center $O_2$ and
radius $r_2$, and $C$, $D$, $E$ lie on the circle with center $O_3$ and radius $r_3$, then these
three circles have a common point.

Source: https://en.wikipedia.org/wiki/Miquel%27s_theorem (statement miquel-theorem-s1).
Proves `Wanted` entry `miquel_theorem`.
-/
theorem miquel_theorem (A B C D E F : EuclideanSpace ℝ (Fin 2))
    (hTri : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    (hD : D ∈ affineSpan ℝ ({B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    (hE : E ∈ affineSpan ℝ ({C, A} : Set (EuclideanSpace ℝ (Fin 2))))
    (hF : F ∈ affineSpan ℝ ({A, B} : Set (EuclideanSpace ℝ (Fin 2))))
    (hDB : D ≠ B) (hDC : D ≠ C)
    (hEC : E ≠ C) (hEA : E ≠ A)
    (hFA : F ≠ A) (hFB : F ≠ B)
    (O1 O2 O3 : EuclideanSpace ℝ (Fin 2)) (r1 r2 r3 : ℝ)
    (hAEF : A ∈ Metric.sphere O1 r1 ∧ E ∈ Metric.sphere O1 r1 ∧ F ∈ Metric.sphere O1 r1)
    (hBFD : B ∈ Metric.sphere O2 r2 ∧ F ∈ Metric.sphere O2 r2 ∧ D ∈ Metric.sphere O2 r2)
    (hCDE : C ∈ Metric.sphere O3 r3 ∧ D ∈ Metric.sphere O3 r3 ∧ E ∈ Metric.sphere O3 r3) :
    ∃ M, M ∈ Metric.sphere O1 r1 ∧ M ∈ Metric.sphere O2 r2 ∧ M ∈ Metric.sphere O3 r3 := by
  have hAB : A ≠ B := ne₁₂_of_not_collinear hTri
  have hAC : A ≠ C := ne₁₃_of_not_collinear hTri
  have hBC : B ≠ C := ne₂₃_of_not_collinear hTri
  have eCAB : ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) = {C, A, B} := by
    ext y
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have eBCA : ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) = {B, C, A} := by
    ext y
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hCAB : ¬ Collinear ℝ ({C, A, B} : Set (EuclideanSpace ℝ (Fin 2))) := eCAB ▸ hTri
  have hBCA : ¬ Collinear ℝ ({B, C, A} : Set (EuclideanSpace ℝ (Fin 2))) := eBCA ▸ hTri
  have hDE : D ≠ E := by
    intro h
    subst h
    exact hDC (miquel_aux_inter hTri hD hE)
  have hED : E ≠ D := Ne.symm hDE
  have hDF : D ≠ F := by
    intro h
    subst h
    exact hDB (miquel_aux_inter hCAB hF hD)
  have hEF : E ≠ F := by
    intro h
    subst h
    exact hEA (miquel_aux_inter hBCA hE hF)
  have hncCDE : ¬ Collinear ℝ ({C, D, E} : Set (EuclideanSpace ℝ (Fin 2))) :=
    miquel_aux_noncoll hTri hD hE hDC hEC
  have hncAEF : ¬ Collinear ℝ ({A, E, F} : Set (EuclideanSpace ℝ (Fin 2))) :=
    miquel_aux_noncoll hBCA hE hF hEA hFA
  have hncBFD : ¬ Collinear ℝ ({B, F, D} : Set (EuclideanSpace ℝ (Fin 2))) :=
    miquel_aux_noncoll hCAB hF hD hFB hDB
  have hA1 : A ∈ (⟨O1, r1⟩ : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))) :=
    hAEF.1
  have hE1 : E ∈ (⟨O1, r1⟩ : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))) :=
    hAEF.2.1
  have hF1 : F ∈ (⟨O1, r1⟩ : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))) :=
    hAEF.2.2
  have hB2 : B ∈ (⟨O2, r2⟩ : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))) :=
    hBFD.1
  have hF2 : F ∈ (⟨O2, r2⟩ : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))) :=
    hBFD.2.1
  have hD2 : D ∈ (⟨O2, r2⟩ : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))) :=
    hBFD.2.2
  have hC3 : C ∈ (⟨O3, r3⟩ : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))) :=
    hCDE.1
  have hD3 : D ∈ (⟨O3, r3⟩ : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))) :=
    hCDE.2.1
  have hE3 : E ∈ (⟨O3, r3⟩ : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))) :=
    hCDE.2.2
  -- line identities used in both cases
  have hDCB : D ∈ affineSpan ℝ ({C, B} : Set (EuclideanSpace ℝ (Fin 2))) :=
    miquel_aux_swap_mem hD
  have L1 : affineSpan ℝ ({D, B} : Set (EuclideanSpace ℝ (Fin 2))) =
      affineSpan ℝ ({C, B} : Set (EuclideanSpace ℝ (Fin 2))) :=
    affineSpan_pair_eq_of_left_mem_of_ne hDCB hDB
  have Laii : affineSpan ℝ ({F, B} : Set (EuclideanSpace ℝ (Fin 2))) =
      affineSpan ℝ ({A, B} : Set (EuclideanSpace ℝ (Fin 2))) :=
    affineSpan_pair_eq_of_left_mem_of_ne hF hFB
  have Lbi : affineSpan ℝ ({F, A} : Set (EuclideanSpace ℝ (Fin 2))) =
      affineSpan ℝ ({B, A} : Set (EuclideanSpace ℝ (Fin 2))) :=
    affineSpan_pair_eq_of_left_mem_of_ne (miquel_aux_swap_mem hF) hFA
  have L4 : affineSpan ℝ ({A, E} : Set (EuclideanSpace ℝ (Fin 2))) =
      affineSpan ℝ ({A, C} : Set (EuclideanSpace ℝ (Fin 2))) :=
    affineSpan_pair_eq_of_right_mem_of_ne (miquel_aux_swap_mem hE) hEA
  have L4' : affineSpan ℝ ({E, A} : Set (EuclideanSpace ℝ (Fin 2))) =
      affineSpan ℝ ({C, A} : Set (EuclideanSpace ℝ (Fin 2))) :=
    (miquel_aux_span_symm E A).trans (L4.trans (miquel_aux_span_symm A C))
  have L5 : affineSpan ℝ ({D, C} : Set (EuclideanSpace ℝ (Fin 2))) =
      affineSpan ℝ ({B, C} : Set (EuclideanSpace ℝ (Fin 2))) :=
    affineSpan_pair_eq_of_left_mem_of_ne hD hDC
  have L6 : affineSpan ℝ ({E, C} : Set (EuclideanSpace ℝ (Fin 2))) =
      affineSpan ℝ ({A, C} : Set (EuclideanSpace ℝ (Fin 2))) :=
    affineSpan_pair_eq_of_left_mem_of_ne (miquel_aux_swap_mem hE) hEC
  have triABC := miquel_aux_trisum hBC.symm hAB.symm hAC
  have triAFE := miquel_aux_trisum hEF.symm hEA hFA.symm
  have triBFD := miquel_aux_trisum hDF.symm hDB hFB.symm
  by_cases hO : O1 = O2
  · have hr : r1 = r2 := by
      have e1 : dist F O1 = r1 := Metric.mem_sphere.mp hAEF.2.2
      have e2 : dist F O2 = r2 := Metric.mem_sphere.mp hBFD.2.1
      rw [hO] at e1
      exact e1.symm.trans e2
    have hss : (⟨O1, r1⟩ : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))) =
        ⟨O2, r2⟩ := by
      rw [hO, hr]
    have hDs1 : D ∈ (⟨O1, r1⟩ : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))) := by
      rw [hss]
      exact hD2
    exact ⟨D, hDs1, hBFD.2.2, hCDE.2.1⟩
  · have hO12 : O1 ≠ O2 := hO
    have hw : O1 -ᵥ O2 ≠ 0 := vsub_ne_zero.mpr hO12
    set d : EuclideanSpace ℝ (Fin 2) :=
      Orientation.rotation Module.Oriented.positiveOrientation (Real.pi / 2 : ℝ)
        (O1 -ᵥ O2) with hddef
    have hdw : inner ℝ (O1 -ᵥ O2) d = 0 :=
      Orientation.inner_rotation_pi_div_two_right _ _
    have hd_ne : d ≠ 0 := by
      intro h
      apply hw
      exact (Orientation.rotation Module.Oriented.positiveOrientation
        (Real.pi / 2 : ℝ)).injective (h.trans (map_zero _).symm)
    set M : EuclideanSpace ℝ (Fin 2) :=
      (⟨O1, r1⟩ : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))).secondInter
        F d with hMdef
    have hMs1 : M ∈ (⟨O1, r1⟩ : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))) :=
      (EuclideanGeometry.Sphere.secondInter_mem d).mpr hF1
    have hMM : M =
        (⟨O2, r2⟩ : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))).secondInter
          F d := by
      have h := EuclideanGeometry.Sphere.secondInter_vsub_secondInter
        (⟨O1, r1⟩ : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2)))
        (⟨O2, r2⟩ : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))) F d
      have h0 : inner ℝ d (O1 -ᵥ O2) = 0 := by
        rw [real_inner_comm]
        exact hdw
      rw [h0, mul_zero, zero_div, zero_smul] at h
      exact vsub_eq_zero_iff_eq.mp h
    have hMs2 : M ∈ (⟨O2, r2⟩ : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))) := by
      rw [hMM]
      exact (EuclideanGeometry.Sphere.secondInter_mem d).mpr hF2
    by_cases hMF : M = F
    · -- tangent case: M = F, show F lies on the third circle
      have hMF' : (⟨O1, r1⟩ :
          EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))).secondInter F d = F :=
        hMF
      have ht0 : inner ℝ d (F -ᵥ O1) = 0 := by
        have h := EuclideanGeometry.Sphere.secondInter_eq_self_iff.mp hMF'
        rwa [EuclideanGeometry.Sphere.mk_center] at h
      have ht02 : inner ℝ d (F -ᵥ O2) = 0 := by
        have e : F -ᵥ O2 = (F -ᵥ O1) + (O1 -ᵥ O2) :=
          (vsub_add_vsub_cancel F O1 O2).symm
        rw [e, inner_add_right, ht0,
          show inner ℝ d (O1 -ᵥ O2) = 0 by rw [real_inner_comm]; exact hdw, add_zero]
      set Q : EuclideanSpace ℝ (Fin 2) := d +ᵥ F with hQdef
      have hQv : Q -ᵥ F = d := vadd_vsub _ _
      have hQF : Q ≠ F := by
        intro h
        apply hd_ne
        rw [← hQv, h, vsub_self]
      have htan1 : (⟨O1, r1⟩ :
          EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))).IsTangentAt F
          (affineSpan ℝ ({F, Q} : Set (EuclideanSpace ℝ (Fin 2)))) := by
        refine EuclideanGeometry.Sphere.IsTangentAt.mk hF1
          (left_mem_affineSpan_pair _ _ _) ?_
        intro x hx
        rw [EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_left]
        have hx' : (x -ᵥ F) +ᵥ F ∈
            affineSpan ℝ ({F, Q} : Set (EuclideanSpace ℝ (Fin 2))) := by
          rw [vsub_vadd]
          exact hx
        obtain ⟨r, hr⟩ := vadd_left_mem_affineSpan_pair.mp hx'
        rw [hQv] at hr
        rw [← hr, inner_smul_left, EuclideanGeometry.Sphere.mk_center, ht0, mul_zero]
      have htan2 : (⟨O2, r2⟩ :
          EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))).IsTangentAt F
          (affineSpan ℝ ({F, Q} : Set (EuclideanSpace ℝ (Fin 2)))) := by
        refine EuclideanGeometry.Sphere.IsTangentAt.mk hF2
          (left_mem_affineSpan_pair _ _ _) ?_
        intro x hx
        rw [EuclideanGeometry.Sphere.mem_orthRadius_iff_inner_left]
        have hx' : (x -ᵥ F) +ᵥ F ∈
            affineSpan ℝ ({F, Q} : Set (EuclideanSpace ℝ (Fin 2))) := by
          rw [vsub_vadd]
          exact hx
        obtain ⟨r, hr⟩ := vadd_left_mem_affineSpan_pair.mp hx'
        rw [hQv] at hr
        rw [← hr, inner_smul_left, EuclideanGeometry.Sphere.mk_center, ht02, mul_zero]
      have T1 : (2 : ℤ) • EuclideanGeometry.oangle Q F A =
          (2 : ℤ) • EuclideanGeometry.oangle F E A :=
        EuclideanGeometry.Sphere.two_zsmul_oangle_tangent_eq hF1 hA1 hE1 htan1 hQF
          hEF hEA hFA.symm
      have T2 : (2 : ℤ) • EuclideanGeometry.oangle Q F B =
          (2 : ℤ) • EuclideanGeometry.oangle F D B :=
        EuclideanGeometry.Sphere.two_zsmul_oangle_tangent_eq hF2 hB2 hD2 htan2 hQF
          hDF hDB hFB.symm
      have hFAFB : affineSpan ℝ ({A, F} : Set (EuclideanSpace ℝ (Fin 2))) =
          affineSpan ℝ ({B, F} : Set (EuclideanSpace ℝ (Fin 2))) :=
        (miquel_aux_span_symm A F).trans
          (Lbi.trans ((miquel_aux_span_symm B A).trans (Laii.symm.trans
            (miquel_aux_span_symm F B))))
      have hS1 : (2 : ℤ) • EuclideanGeometry.oangle Q F A =
          (2 : ℤ) • EuclideanGeometry.oangle Q F B :=
        miquel_aux_line_angle rfl hFAFB
      have hS1' : (2 : ℤ) • EuclideanGeometry.oangle F E A =
          (2 : ℤ) • EuclideanGeometry.oangle F D B := T1.symm.trans (hS1.trans T2)
      have sa_t : (2 : ℤ) • EuclideanGeometry.oangle D B F =
          (2 : ℤ) • EuclideanGeometry.oangle C B A :=
        miquel_aux_line_angle L1 Laii
      have sb_t : (2 : ℤ) • EuclideanGeometry.oangle E A F =
          (2 : ℤ) • EuclideanGeometry.oangle C A B :=
        miquel_aux_line_angle L4' Lbi
      have sc_t : (2 : ℤ) • EuclideanGeometry.oangle D C E =
          (2 : ℤ) • EuclideanGeometry.oangle B C A :=
        miquel_aux_line_angle L5 L6
      have eBFA : ({F, A, B} : Set (EuclideanSpace ℝ (Fin 2))) = {B, F, A} := by
        ext y
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · intro h
          rcases h with h | h | h
          · rw [h]; simp
          · rw [h]; simp
          · rw [h]; simp
        · intro h
          rcases h with h | h | h
          · rw [h]; simp
          · rw [h]; simp
          · rw [h]; simp
      have hBFAcol : Collinear ℝ ({F, A, B} : Set (EuclideanSpace ℝ (Fin 2))) :=
        collinear_insert_of_mem_affineSpan_pair hF
      have zBFA : (2 : ℤ) • EuclideanGeometry.oangle B F A = 0 :=
        miquel_aux_coll2 (miquel_aux_reorder eBFA hBFAcol)
      have ad_a : EuclideanGeometry.oangle D F B + EuclideanGeometry.oangle B F E =
          EuclideanGeometry.oangle D F E :=
        EuclideanGeometry.oangle_add hDF hFB.symm hEF
      have ad_b : EuclideanGeometry.oangle B F A + EuclideanGeometry.oangle A F E =
          EuclideanGeometry.oangle B F E :=
        EuclideanGeometry.oangle_add hFB.symm hFA.symm hEF
      have key : (2 : ℤ) • EuclideanGeometry.oangle D F E =
          (2 : ℤ) • EuclideanGeometry.oangle D C E := by
        have e1 : (2 : ℤ) • EuclideanGeometry.oangle D F E =
            (2 : ℤ) • EuclideanGeometry.oangle D F B +
              (2 : ℤ) • EuclideanGeometry.oangle B F E := by
          rw [← ad_a, smul_add]
        have e2 : (2 : ℤ) • EuclideanGeometry.oangle B F E =
            (2 : ℤ) • EuclideanGeometry.oangle A F E := by
          have eb : (2 : ℤ) • EuclideanGeometry.oangle B F E =
              (2 : ℤ) • EuclideanGeometry.oangle B F A +
                (2 : ℤ) • EuclideanGeometry.oangle A F E := by
            rw [← ad_b, smul_add]
          rw [eb, zBFA, zero_add]
        have e3 : (2 : ℤ) • EuclideanGeometry.oangle D F B =
            -((2 : ℤ) • EuclideanGeometry.oangle B F D) :=
          eq_neg_iff_add_eq_zero.mpr (by
            have h := EuclideanGeometry.oangle_add_oangle_rev D F B
            rw [← smul_add, h, smul_zero])
        rw [e1, e2, e3]
        have rAFE : (2 : ℤ) • EuclideanGeometry.oangle A F E =
            -((2 : ℤ) • EuclideanGeometry.oangle F E A +
              (2 : ℤ) • EuclideanGeometry.oangle E A F) :=
          eq_neg_iff_add_eq_zero.mpr (by rw [← triAFE]; abel)
        have rBFD : (2 : ℤ) • EuclideanGeometry.oangle B F D =
            -((2 : ℤ) • EuclideanGeometry.oangle F D B +
              (2 : ℤ) • EuclideanGeometry.oangle D B F) :=
          eq_neg_iff_add_eq_zero.mpr (by rw [← triBFD]; abel)
        rw [rAFE, rBFD, neg_neg, sa_t, sb_t, sc_t, ← hS1']
        have rBAC : (2 : ℤ) • EuclideanGeometry.oangle B A C =
            -((2 : ℤ) • EuclideanGeometry.oangle C A B) :=
          eq_neg_iff_add_eq_zero.mpr (by
            have h := EuclideanGeometry.oangle_add_oangle_rev B A C
            rw [← smul_add, h, smul_zero])
        have rACB : (2 : ℤ) • EuclideanGeometry.oangle A C B =
            -((2 : ℤ) • EuclideanGeometry.oangle B C A) :=
          eq_neg_iff_add_eq_zero.mpr (by
            have h := EuclideanGeometry.oangle_add_oangle_rev A C B
            rw [← smul_add, h, smul_zero])
        rw [rBAC, rACB] at triABC
        have hfin : ((2 : ℤ) • EuclideanGeometry.oangle F E A +
              (2 : ℤ) • EuclideanGeometry.oangle C B A) +
              (-((2 : ℤ) • EuclideanGeometry.oangle F E A +
                (2 : ℤ) • EuclideanGeometry.oangle C A B)) -
              (2 : ℤ) • EuclideanGeometry.oangle B C A = 0 := by
          rw [← triABC]
          abel
        exact sub_eq_zero.mp hfin
      have hconc :=
        EuclideanGeometry.concyclic_or_collinear_of_two_zsmul_oangle_eq key
      rcases hconc with hcon | hcol
      · obtain ⟨c, r, hcr⟩ := EuclideanGeometry.cospherical_def _ |>.mp hcon.1
        have hCs' : C ∈ (⟨c, r⟩ :
            EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))) :=
          EuclideanGeometry.mem_sphere.mpr
            (hcr C (Set.mem_insert_of_mem _
              (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
        have hDs' : D ∈ (⟨c, r⟩ :
            EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))) :=
          EuclideanGeometry.mem_sphere.mpr (hcr D (Set.mem_insert _ _))
        have hEs' : E ∈ (⟨c, r⟩ :
            EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))) :=
          EuclideanGeometry.mem_sphere.mpr
            (hcr E (Set.mem_insert_of_mem _
              (Set.mem_insert_of_mem _
                (Set.mem_insert_of_mem _ (Set.mem_singleton _)))))
        have hFs' : F ∈ (⟨c, r⟩ :
            EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))) :=
          EuclideanGeometry.mem_sphere.mpr
            (hcr F (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
        by_cases hs : (⟨c, r⟩ : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))) =
            ⟨O3, r3⟩
        · have hFs3 : F ∈ (⟨O3, r3⟩ :
              EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))) := by
            rw [← hs]
            exact hFs'
          exact ⟨F, hAEF.2.2, hBFD.2.1, hFs3⟩
        · have hE := EuclideanGeometry.eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two
            Fact.out hs hDC.symm hCs' hDs' hEs' hC3 hD3 hE3
          rcases hE with h | h
          · exact absurd h hEC
          · exact absurd h hED
      · have hsub : ({C, D, E} : Set (EuclideanSpace ℝ (Fin 2))) ⊆ {D, F, C, E} := by
          intro y hy
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl | rfl
          · exact Set.mem_insert_of_mem _
              (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
          · exact Set.mem_insert _ _
          · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
              (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
        exact (hncCDE (Collinear.subset hsub hcol)).elim
    · -- transverse case
      by_cases hMD : M = D
      · refine ⟨D, ?_, hBFD.2.2, hCDE.2.1⟩
        rw [← hMD]
        exact hMs1
      · by_cases hME : M = E
        · refine ⟨E, hE1, ?_, hCDE.2.2⟩
          rw [← hME]
          exact hMs2
        · have cDMBF : EuclideanGeometry.Cospherical
              ({D, M, B, F} : Set (EuclideanSpace ℝ (Fin 2))) :=
            EuclideanGeometry.cospherical_iff_exists_sphere.mpr
              ⟨⟨O2, r2⟩, by
                intro x hx
                simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
                rcases hx with rfl | rfl | rfl | rfl
                · exact hD2
                · exact hMs2
                · exact hB2
                · exact hF2⟩
          have cFMAE : EuclideanGeometry.Cospherical
              ({F, M, A, E} : Set (EuclideanSpace ℝ (Fin 2))) :=
            EuclideanGeometry.cospherical_iff_exists_sphere.mpr
              ⟨⟨O1, r1⟩, by
                intro x hx
                simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
                rcases hx with rfl | rfl | rfl | rfl
                · exact hF1
                · exact hMs1
                · exact hA1
                · exact hE1⟩
          have e1 : (2 : ℤ) • EuclideanGeometry.oangle D M F =
              (2 : ℤ) • EuclideanGeometry.oangle D B F :=
            EuclideanGeometry.Cospherical.two_zsmul_oangle_eq cDMBF hMD hMF hDB.symm
              hFB.symm
          have e2 : (2 : ℤ) • EuclideanGeometry.oangle F M E =
              (2 : ℤ) • EuclideanGeometry.oangle F A E :=
            EuclideanGeometry.Cospherical.two_zsmul_oangle_eq cFMAE hMF hME hFA.symm
              hEA.symm
          have e3 : (2 : ℤ) • EuclideanGeometry.oangle D M E =
              (2 : ℤ) • EuclideanGeometry.oangle D M F +
                (2 : ℤ) • EuclideanGeometry.oangle F M E := by
            rw [← EuclideanGeometry.oangle_add (Ne.symm hMD) (Ne.symm hMF) (Ne.symm hME),
              smul_add]
          have sa : (2 : ℤ) • EuclideanGeometry.oangle D B F =
              (2 : ℤ) • EuclideanGeometry.oangle C B A :=
            calc (2 : ℤ) • EuclideanGeometry.oangle D B F
                = (2 : ℤ) • EuclideanGeometry.oangle C B F :=
                  miquel_aux_line_angle L1 rfl
              _ = (2 : ℤ) • EuclideanGeometry.oangle C B A :=
                  miquel_aux_line_angle rfl Laii
          have sb : (2 : ℤ) • EuclideanGeometry.oangle F A E =
              (2 : ℤ) • EuclideanGeometry.oangle B A C :=
            calc (2 : ℤ) • EuclideanGeometry.oangle F A E
                = (2 : ℤ) • EuclideanGeometry.oangle B A E :=
                  miquel_aux_line_angle Lbi rfl
              _ = (2 : ℤ) • EuclideanGeometry.oangle B A C :=
                  miquel_aux_line_angle rfl L4'
          have sc : (2 : ℤ) • EuclideanGeometry.oangle D C E =
              (2 : ℤ) • EuclideanGeometry.oangle B C A :=
            miquel_aux_line_angle L5 L6
          have key : (2 : ℤ) • EuclideanGeometry.oangle D M E =
              (2 : ℤ) • EuclideanGeometry.oangle D C E := by
            rw [e3, e1, e2, sa, sb, sc]
            have rBAC : (2 : ℤ) • EuclideanGeometry.oangle B A C =
                -((2 : ℤ) • EuclideanGeometry.oangle C A B) :=
              eq_neg_iff_add_eq_zero.mpr (by
                have h := EuclideanGeometry.oangle_add_oangle_rev B A C
                rw [← smul_add, h, smul_zero])
            have rACB : (2 : ℤ) • EuclideanGeometry.oangle A C B =
                -((2 : ℤ) • EuclideanGeometry.oangle B C A) :=
              eq_neg_iff_add_eq_zero.mpr (by
                have h := EuclideanGeometry.oangle_add_oangle_rev A C B
                rw [← smul_add, h, smul_zero])
            rw [rBAC, rACB] at triABC
            rw [rBAC]
            have hfin : ((2 : ℤ) • EuclideanGeometry.oangle C B A +
                  (-((2 : ℤ) • EuclideanGeometry.oangle C A B))) -
                (2 : ℤ) • EuclideanGeometry.oangle B C A = 0 := by
              rw [← triABC]
              abel
            exact sub_eq_zero.mp hfin
          have hconc :=
            EuclideanGeometry.concyclic_or_collinear_of_two_zsmul_oangle_eq key
          rcases hconc with hcon | hcol
          · obtain ⟨c, r, hcr⟩ := EuclideanGeometry.cospherical_def _ |>.mp hcon.1
            have hCs' : C ∈ (⟨c, r⟩ :
                EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))) :=
              EuclideanGeometry.mem_sphere.mpr
                (hcr C (Set.mem_insert_of_mem _
                  (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
            have hDs' : D ∈ (⟨c, r⟩ :
                EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))) :=
              EuclideanGeometry.mem_sphere.mpr (hcr D (Set.mem_insert _ _))
            have hEs' : E ∈ (⟨c, r⟩ :
                EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))) :=
              EuclideanGeometry.mem_sphere.mpr
                (hcr E (Set.mem_insert_of_mem _
                  (Set.mem_insert_of_mem _
                    (Set.mem_insert_of_mem _ (Set.mem_singleton _)))))
            have hMs' : M ∈ (⟨c, r⟩ :
                EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))) :=
              EuclideanGeometry.mem_sphere.mpr
                (hcr M (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
            by_cases hs : (⟨c, r⟩ :
                EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))) = ⟨O3, r3⟩
            · have hMs3 : M ∈ (⟨O3, r3⟩ :
                  EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2))) := by
                rw [← hs]
                exact hMs'
              exact ⟨M, hMs1, hMs2, hMs3⟩
            · have hE := EuclideanGeometry.eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two
                Fact.out hs hDC.symm hCs' hDs' hEs' hC3 hD3 hE3
              rcases hE with h | h
              · exact absurd h hEC
              · exact absurd h hED
          · have hsub : ({C, D, E} : Set (EuclideanSpace ℝ (Fin 2))) ⊆ {D, M, C, E} := by
              intro y hy
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
              rcases hy with rfl | rfl | rfl
              · exact Set.mem_insert_of_mem _
                  (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
              · exact Set.mem_insert _ _
              · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
                  (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
            exact (hncCDE (Collinear.subset hsub hcol)).elim

end

end MetaMathlibExt
