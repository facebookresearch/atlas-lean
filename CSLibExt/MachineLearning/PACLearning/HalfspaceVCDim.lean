/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.MachineLearning.PACLearning.VCDimension
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Insert
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Radon
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! # VC dimension of affine halfspaces

The class of affine halfspaces in `ℝᵈ` has VC dimension `d + 1`.

## Main statements

- `halfspaceClass_shatters`: the origin plus the standard basis vectors are shattered.
- `halfspaceClass_not_shatters`: no set of `d + 2` points is shattered.
- `halfspaceClass_vcDim`: the VC dimension is exactly `d + 1`.

The upper bound goes through Radon's theorem (`Convex.radon_partition`): the convex
hulls of the two sides of a Radon partition sit inside complementary halfspaces, so an
affine functional separating them cannot exist at a common point.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Cslib.MachineLearning.PACLearning

/-- The concept class of affine halfspaces in `ℝᵈ`: each concept decides the strict
positive side `0 < ⟪w, x⟫ + b` of an affine functional. -/
noncomputable def halfspaceClass (d : ℕ) :
    ConceptClass (EuclideanSpace ℝ (Fin d)) Bool :=
  {c | ∃ (w : EuclideanSpace ℝ (Fin d)) (b : ℝ),
    c = fun x => decide (0 < ⟪w, x⟫_ℝ + b)}

open scoped Classical in
/-- Lower-bound witness: the origin together with the standard basis vectors. -/
noncomputable def halfspaceWitness (d : ℕ) :
    Finset (EuclideanSpace ℝ (Fin d)) :=
  insert 0 (Finset.image (fun i : Fin d => EuclideanSpace.single i (1 : ℝ))
    Finset.univ)

open scoped Classical in
/-- The witness set has `d + 1` points. -/
theorem halfspaceWitness_card (d : ℕ) : (halfspaceWitness d).card = d + 1 := by
  have h0 : (0 : EuclideanSpace ℝ (Fin d)) ∉
      Finset.image (fun i : Fin d => EuclideanSpace.single i (1 : ℝ))
        Finset.univ := by
    intro hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨j, _, hj⟩ := hmem
    have h2 := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x j) hj
    simp at h2
  have hinj : Function.Injective
      (fun i : Fin d => EuclideanSpace.single i (1 : ℝ)) := by
    intro i j h
    by_contra hne
    have hji : j ≠ i := Ne.symm hne
    have h2 := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x j) h
    simp [hji] at h2
  rw [halfspaceWitness, Finset.card_insert_of_notMem h0,
    Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- The witness set is shattered: given target values, set the bias from the value at
the origin and each weight coordinate from the value at the matching basis vector. -/
theorem halfspaceClass_shatters (d : ℕ) :
    SetShatters (halfspaceClass d) ↑(halfspaceWitness d) := by
  classical
  intro W' hW'
  set b : ℝ := if (0 : EuclideanSpace ℝ (Fin d)) ∈ W' then 1 else -1 with hb
  set w : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun i =>
    (if EuclideanSpace.single i (1 : ℝ) ∈ W' then (1 : ℝ) else -1) - b) with hw
  have hwj : ∀ j : Fin d, w j =
      (if EuclideanSpace.single j (1 : ℝ) ∈ W' then (1 : ℝ) else -1) - b :=
    fun j => rfl
  have h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ W' ↔ 0 < ⟪w, 0⟫_ℝ + b := by
    rw [inner_zero_right, zero_add]
    by_cases h : (0 : EuclideanSpace ℝ (Fin d)) ∈ W' <;> simp [hb, h]
  have h1 : ∀ j : Fin d, EuclideanSpace.single j (1 : ℝ) ∈ W' ↔
      0 < ⟪w, EuclideanSpace.single j (1 : ℝ)⟫_ℝ + b := by
    intro j
    rw [EuclideanSpace.inner_single_right, RCLike.conj_to_real, hwj j]
    by_cases h : EuclideanSpace.single j (1 : ℝ) ∈ W' <;> simp [h]
  refine ⟨fun x => decide (0 < ⟪w, x⟫_ℝ + b), ⟨w, b, rfl⟩, ?_⟩
  rw [halfspaceWitness]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
    decide_eq_true_eq, Finset.mem_coe, Finset.mem_insert, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hpos, rfl | ⟨j, rfl⟩⟩
    · exact h0.mpr hpos
    · exact (h1 j).mpr hpos
  · intro hx
    have hxmem := hW' hx
    simp only [halfspaceWitness, Finset.mem_coe, Finset.mem_insert,
      Finset.mem_image, Finset.mem_univ, true_and] at hxmem
    rcases hxmem with rfl | ⟨j, rfl⟩
    · exact ⟨h0.mp hx, Or.inl rfl⟩
    · exact ⟨(h1 j).mp hx, Or.inr ⟨j, rfl⟩⟩

/-- An affine functional maps a convex combination to the combination of values. -/
private theorem halfspace_affine_eval (d : ℕ) (w : EuclideanSpace ℝ (Fin d))
    (b : ℝ) (x y : EuclideanSpace ℝ (Fin d)) (u v : ℝ) (huv : u + v = 1) :
    u * ⟪w, x⟫_ℝ + v * ⟪w, y⟫_ℝ + b
      = u * (⟪w, x⟫_ℝ + b) + v * (⟪w, y⟫_ℝ + b) := by
  linear_combination (-b) * huv

/-- No set of `d + 2` points is shattered. The points are affinely dependent, so a
Radon partition has intersecting convex hulls; an affine functional positive on one
side and nonpositive on the other is impossible at a common point. -/
theorem halfspaceClass_not_shatters (d : ℕ)
    (s : Finset (EuclideanSpace ℝ (Fin d))) (hs : s.card = d + 2) :
    ¬ SetShatters (halfspaceClass d) ↑s := by
  intro hshat
  have hcard : Fintype.card ↥s = d + 2 := by rw [Fintype.card_coe, hs]
  have hdep : ¬ AffineIndependent ℝ ((↑) : ↥s → EuclideanSpace ℝ (Fin d)) := by
    rw [← finrank_vectorSpan_le_iff_not_affineIndependent ℝ _ hcard]
    calc Module.finrank ℝ
            (vectorSpan ℝ (Set.range ((↑) : ↥s → EuclideanSpace ℝ (Fin d))))
          ≤ Module.finrank ℝ (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :=
            Submodule.finrank_mono le_top
        _ = d := by rw [finrank_top, finrank_euclideanSpace_fin]
  obtain ⟨I, hI⟩ := Convex.radon_partition hdep
  obtain ⟨p, hp⟩ := hI
  rw [Set.mem_inter_iff] at hp
  obtain ⟨hpI, hpIc⟩ := hp
  have hsub : ((↑) : ↥s → EuclideanSpace ℝ (Fin d)) '' I ⊆ ↑s := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := hx
    exact Finset.mem_coe.mpr y.property
  obtain ⟨c, hc, hc_eq⟩ :=
    hshat (((↑) : ↥s → EuclideanSpace ℝ (Fin d)) '' I) hsub
  obtain ⟨w, b, rfl⟩ := hc
  have hpos : ∀ y : ↥s, (y : EuclideanSpace ℝ (Fin d)) ∈
      ((↑) : ↥s → EuclideanSpace ℝ (Fin d)) '' I → 0 < ⟪w, y⟫_ℝ + b := by
    intro y hy
    have hmem : (y : EuclideanSpace ℝ (Fin d)) ∈
        (fun x => decide (0 < ⟪w, x⟫_ℝ + b)) ⁻¹' {true} ∩ ↑s := by
      rw [hc_eq]
      exact hy
    simp only [Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff] at hmem
    exact of_decide_eq_true hmem.1
  have hneg : ∀ y : ↥s, (y : EuclideanSpace ℝ (Fin d)) ∈
      ((↑) : ↥s → EuclideanSpace ℝ (Fin d)) '' Iᶜ → ⟪w, y⟫_ℝ + b ≤ 0 := by
    intro y hy
    have hyW : (y : EuclideanSpace ℝ (Fin d)) ∈ (↑s : Set _) :=
      Finset.mem_coe.mpr y.property
    have hynot : (y : EuclideanSpace ℝ (Fin d)) ∉
        ((↑) : ↥s → EuclideanSpace ℝ (Fin d)) '' I := by
      rintro ⟨z, hzI, hzy⟩
      obtain ⟨z', hz'I, hzy'⟩ := hy
      have hzz : z' = z := Subtype.coe_injective (hzy'.trans hzy.symm)
      rw [hzz] at hz'I
      exact hz'I hzI
    have hcon : (y : EuclideanSpace ℝ (Fin d)) ∉
        (fun x => decide (0 < ⟪w, x⟫_ℝ + b)) ⁻¹' {true} ∩ ↑s := by
      rw [hc_eq]
      exact hynot
    simp only [Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff] at hcon
    have h1 : decide (0 < ⟪w, (y : EuclideanSpace ℝ (Fin d))⟫_ℝ + b) ≠ true :=
      fun hh => hcon ⟨hh, hyW⟩
    have hneg1 : ¬ (0 < ⟪w, (y : EuclideanSpace ℝ (Fin d))⟫_ℝ + b) :=
      fun hh => h1 (by simpa using hh)
    exact not_lt.mp hneg1
  have hconv1 : Convex ℝ
      {x : EuclideanSpace ℝ (Fin d) | 0 < ⟪w, x⟫_ℝ + b} := by
    rw [convex_iff_forall_pos]
    intro x hx y hy u v hu hv huv
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [inner_add_right, inner_smul_right, inner_smul_right,
      halfspace_affine_eval d w b x y u v huv]
    exact add_pos (mul_pos hu hx) (mul_pos hv hy)
  have hconv2 : Convex ℝ
      {x : EuclideanSpace ℝ (Fin d) | ⟪w, x⟫_ℝ + b ≤ 0} := by
    rw [convex_iff_forall_pos]
    intro x hx y hy u v hu hv huv
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [inner_add_right, inner_smul_right, inner_smul_right,
      halfspace_affine_eval d w b x y u v huv]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hu.le hx)
      (mul_nonpos_of_nonneg_of_nonpos hv.le hy)
  have hsub1 : ((↑) : ↥s → EuclideanSpace ℝ (Fin d)) '' I ⊆
      {x : EuclideanSpace ℝ (Fin d) | 0 < ⟪w, x⟫_ℝ + b} := by
    intro x hx
    obtain ⟨y, hyI, rfl⟩ := hx
    exact hpos y ⟨y, hyI, rfl⟩
  have hsub2 : ((↑) : ↥s → EuclideanSpace ℝ (Fin d)) '' Iᶜ ⊆
      {x : EuclideanSpace ℝ (Fin d) | ⟪w, x⟫_ℝ + b ≤ 0} := by
    intro x hx
    obtain ⟨y, hyI, rfl⟩ := hx
    exact hneg y ⟨y, hyI, rfl⟩
  have h1 : 0 < ⟪w, p⟫_ℝ + b := convexHull_min hsub1 hconv1 hpI
  have h2 : ⟪w, p⟫_ℝ + b ≤ 0 := convexHull_min hsub2 hconv2 hpIc
  exact not_lt_of_ge h2 h1

/-- Any shattered finite set has at most `d + 1` points. -/
theorem halfspaceClass_card_le_of_shatters (d : ℕ)
    {W : Finset (EuclideanSpace ℝ (Fin d))}
    (hW : SetShatters (halfspaceClass d) ↑W) :
    W.card ≤ d + 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨t, htsub, htcard⟩ :=
    Finset.exists_subset_card_eq (show d + 2 ≤ W.card by omega)
  exact halfspaceClass_not_shatters d t htcard
    (hW.subset (Finset.coe_subset.mpr htsub))

/-- Affine halfspaces have finite VC dimension. -/
theorem halfspaceClass_hasFiniteVCDim (d : ℕ) :
    HasFiniteVCDim (halfspaceClass d) := by
  rw [hasFiniteVCDim_iff]
  exact ⟨d + 1, fun W hW => halfspaceClass_card_le_of_shatters d hW⟩

/-- The VC dimension of affine halfspaces in `ℝᵈ` is `d + 1`. -/
theorem halfspaceClass_vcDim (d : ℕ) : vcDim (halfspaceClass d) = d + 1 := by
  have hlower_mem : d + 1 ∈ {n : ℕ | ∃ W : Finset (EuclideanSpace ℝ (Fin d)),
      W.card = n ∧ SetShatters (halfspaceClass d) ↑W} :=
    ⟨halfspaceWitness d, halfspaceWitness_card d, halfspaceClass_shatters d⟩
  have hbdd : BddAbove {n : ℕ | ∃ W : Finset (EuclideanSpace ℝ (Fin d)),
      W.card = n ∧ SetShatters (halfspaceClass d) ↑W} :=
    halfspaceClass_hasFiniteVCDim d
  have hne : {n : ℕ | ∃ W : Finset (EuclideanSpace ℝ (Fin d)),
      W.card = n ∧ SetShatters (halfspaceClass d) ↑W}.Nonempty :=
    ⟨d + 1, hlower_mem⟩
  have hle : ∀ n ∈ {n : ℕ | ∃ W : Finset (EuclideanSpace ℝ (Fin d)),
      W.card = n ∧ SetShatters (halfspaceClass d) ↑W}, n ≤ d + 1 := by
    intro n hn
    obtain ⟨W, hWc, hW⟩ := hn
    rw [← hWc]
    exact halfspaceClass_card_le_of_shatters d hW
  exact le_antisymm (csSup_le hne hle) (le_csSup hbdd hlower_mem)

end Cslib.MachineLearning.PACLearning
