/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_LatticeTreeOrbital.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

open scoped Matrix

namespace LT.LatticeTree

section Helpers

variable {α : Type*} [CommRing α]

theorem mulVec_single_one (M : Matrix (Fin 2) (Fin 2) α) (j : Fin 2) :
    M *ᵥ (Pi.single j 1) = fun i => M i j := by
  funext i
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, Finset.sum_ite_eq']

theorem diagonal_mulVec (d v : Fin 2 → α) :
    Matrix.diagonal d *ᵥ v = fun i => d i * v i := by
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, ite_mul, Finset.sum_ite_eq]

end Helpers

variable (R : Type*) [CommRing R]
variable (K : Type*) [Field K] [Algebra R K]

def stdLattice : Submodule R (Fin 2 → K) where
  carrier := {v | ∀ i, IsLocalization.IsInteger R (v i)}
  add_mem' := fun hv hw i => IsLocalization.isInteger_add (hv i) (hw i)
  zero_mem' := fun _ => IsLocalization.isInteger_zero
  smul_mem' := fun r v hv i => by
    rw [Pi.smul_apply]
    exact IsLocalization.isInteger_smul (hv i)

theorem mem_stdLattice {v : Fin 2 → K} :
    v ∈ stdLattice R K ↔ ∀ i, IsLocalization.IsInteger R (v i) := Iff.rfl

attribute [local simp] mem_stdLattice
theorem single_one_mem_stdLattice (j : Fin 2) :
    (Pi.single j 1 : Fin 2 → K) ∈ stdLattice R K := by
  intro i
  rcases eq_or_ne i j with rfl | h
  · rw [Pi.single_eq_same]
    exact IsLocalization.isInteger_one
  · rw [Pi.single_eq_of_ne h]
    exact IsLocalization.isInteger_zero

theorem stdLattice_eq_span :
    stdLattice R K = Submodule.span R (Set.range fun j => (Pi.single j 1 : Fin 2 → K)) := by
  apply le_antisymm
  · intro v hv
    choose w hw using hv
    have hv' : v = w 0 • (Pi.single 0 1 : Fin 2 → K) + w 1 • (Pi.single 1 1 : Fin 2 → K) := by
      funext i
      have h0 : algebraMap R K (w 0) = v 0 := hw 0
      have h1 : algebraMap R K (w 1) = v 1 := hw 1
      fin_cases i <;>
        simp [Algebra.smul_def, ← h0, ← h1]
    rw [hv']
    exact add_mem
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact single_one_mem_stdLattice R K j

theorem stdLattice_fg : (stdLattice R K).FG := by
  rw [Submodule.fg_def]
  exact ⟨Set.range fun j => (Pi.single j 1 : Fin 2 → K), Set.finite_range _,
    (stdLattice_eq_span R K).symm⟩

theorem stdLattice_span_top :
    Submodule.span K ((stdLattice R K : Set (Fin 2 → K))) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun K (Fin 2)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact Submodule.subset_span (by
    simpa only [Pi.basisFun_apply, SetLike.mem_coe] using single_one_mem_stdLattice R K j)

variable {R K}

def mulVecLinR (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    (Fin 2 → K) →ₗ[R] (Fin 2 → K) where
  toFun v := (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v
  map_add' v w := Matrix.mulVec_add _ v w
  map_smul' r v := by
    rw [RingHom.id_apply]
    exact Matrix.mulVec_smul _ r v

@[simp] theorem mulVecLinR_apply (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Fin 2 → K) :
    mulVecLinR (R := R) g v = (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v := rfl

def latticeMap (g : Matrix.GeneralLinearGroup (Fin 2) K) (L : Submodule R (Fin 2 → K)) :
    Submodule R (Fin 2 → K) :=
  L.map (mulVecLinR g)

theorem mem_latticeMap {g : Matrix.GeneralLinearGroup (Fin 2) K}
    {L : Submodule R (Fin 2 → K)} {v : Fin 2 → K} :
    v ∈ latticeMap g L ↔ ∃ w ∈ L, (g : Matrix (Fin 2) (Fin 2) K) *ᵥ w = v :=
  Submodule.mem_map

theorem mulVec_mem_latticeMap {g : Matrix.GeneralLinearGroup (Fin 2) K}
    {L : Submodule R (Fin 2 → K)} {w : Fin 2 → K} (hw : w ∈ L) :
    (g : Matrix (Fin 2) (Fin 2) K) *ᵥ w ∈ latticeMap g L :=
  ⟨w, hw, rfl⟩

theorem mulVecLinR_mul (g h : Matrix.GeneralLinearGroup (Fin 2) K) :
    mulVecLinR (R := R) (g * h) = (mulVecLinR g).comp (mulVecLinR h) :=
  LinearMap.ext fun v => by
    rw [LinearMap.comp_apply, mulVecLinR_apply, mulVecLinR_apply, mulVecLinR_apply,
      Matrix.mulVec_mulVec, Units.val_mul]

theorem latticeMap_one (L : Submodule R (Fin 2 → K)) : latticeMap 1 L = L := by
  have h : ∀ v : Fin 2 → K, mulVecLinR (R := R) 1 v = v := fun v => by
    rw [mulVecLinR_apply, Units.val_one, Matrix.one_mulVec]
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [show mulVecLinR (R := R) 1 w = w from h w]
    exact hw
  · intro hv
    exact ⟨v, hv, h v⟩

attribute [local simp] latticeMap_one
theorem latticeMap_mul (g h : Matrix.GeneralLinearGroup (Fin 2) K)
    (L : Submodule R (Fin 2 → K)) :
    latticeMap (g * h) L = latticeMap g (latticeMap h L) := by
  unfold latticeMap
  rw [mulVecLinR_mul, Submodule.map_comp]

theorem latticeMap_inv_latticeMap (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (L : Submodule R (Fin 2 → K)) :
    latticeMap g⁻¹ (latticeMap g L) = L := by
  rw [← latticeMap_mul, inv_mul_cancel, latticeMap_one]

theorem latticeMap_latticeMap_inv (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (L : Submodule R (Fin 2 → K)) :
    latticeMap g (latticeMap g⁻¹ L) = L := by
  rw [← latticeMap_mul, mul_inv_cancel, latticeMap_one]

theorem latticeMap_injective (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    Function.Injective (latticeMap (R := R) g) :=
  Function.LeftInverse.injective (latticeMap_inv_latticeMap g)

theorem latticeMap_mono (g : Matrix.GeneralLinearGroup (Fin 2) K)
    {L L' : Submodule R (Fin 2 → K)} (h : L ≤ L') : latticeMap g L ≤ latticeMap g L' :=
  Submodule.map_mono h

theorem le_of_latticeMap_le (g : Matrix.GeneralLinearGroup (Fin 2) K)
    {L L' : Submodule R (Fin 2 → K)} (h : latticeMap g L ≤ latticeMap g L') : L ≤ L' := by
  have := latticeMap_mono g⁻¹ h
  rwa [latticeMap_inv_latticeMap, latticeMap_inv_latticeMap] at this

theorem latticeMap_lt_latticeMap_iff (g : Matrix.GeneralLinearGroup (Fin 2) K)
    {L L' : Submodule R (Fin 2 → K)} : latticeMap g L < latticeMap g L' ↔ L < L' := by
  constructor
  · intro h
    exact lt_of_le_of_ne (le_of_latticeMap_le g h.1) (fun hEq => h.ne (by rw [hEq]))
  · intro h
    exact lt_of_le_of_ne (latticeMap_mono g h.1)
      (fun hEq => h.ne (latticeMap_injective g hEq))

/-- The standard lattice is a `Submodule.IsLattice` for any `R`-algebra `K`: if `algebraMap R K`
is injective, its `R`-rank is the `K`-dimension `2` of its span, and otherwise no nonempty subset
of `K²` is `R`-linearly independent. -/
theorem isLattice_stdLattice : Submodule.IsLattice K (stdLattice R K) := by
  by_cases h : Function.Injective (algebraMap R K)
  · have : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).mpr h
    have : Nontrivial R := (algebraMap R K).domain_nontrivial
    have hli : LinearIndependent R fun j : Fin 2 => (Pi.single j 1 : Fin 2 → K) :=
      (Pi.linearIndependent_single_one (Fin 2) K).restrict_scalars' R
    refine (Submodule.IsLattice.iff_fg_and_finrank_span_eq_finrank K _).mpr
      ⟨stdLattice_fg R K, ?_⟩
    rw [stdLattice_span_top R K, finrank_top, Module.finrank_fin_fun K, stdLattice_eq_span R K,
      finrank_span_eq_card hli, Fintype.card_fin]
  · obtain ⟨r, r', hrr', hne⟩ := Function.not_injective_iff.mp h
    refine ⟨stdLattice_fg R K, fun s _ hs => ?_⟩
    rcases s.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · exact linearIndepOn_empty K id
    · refine absurd (LinearIndependent.smul_left_injective hs ⟨v, hv⟩ ?_) hne
      change r • v = r' • v
      rw [← algebraMap_smul K r v, ← algebraMap_smul K r' v, hrr']

theorem isFullLattice_stdLattice : Submodule.IsFullLattice K (stdLattice R K) where
  toIsLattice := isLattice_stdLattice
  span_eq_top := stdLattice_span_top R K

theorem IsFullLattice.map {L : Submodule R (Fin 2 → K)} (hL : Submodule.IsFullLattice K L)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) : Submodule.IsFullLattice K (latticeMap g L) where
  fg := (Submodule.IsLattice.fg K L).map _
  linearIndepOn s hs hli := by
    have hgg : ∀ v : Fin 2 → K, (g : Matrix (Fin 2) (Fin 2) K) *ᵥ
        (((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = v :=
      fun v => by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec]
    have hgg' : ∀ v : Fin 2 → K,
        ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
          ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = v :=
      fun v => by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]
    have hsub : mulVecLinR (R := R) g⁻¹ '' s ⊆ L := by
      rintro _ ⟨v, hv, rfl⟩
      obtain ⟨w, hw, rfl⟩ := mem_latticeMap.mp (hs hv)
      rwa [mulVecLinR_apply, hgg']
    have hK := Submodule.IsLattice.linearIndepOn (A := K) _ hsub (hli.image (by
      rw [LinearMap.ker_eq_bot.mpr fun v w hvw => by rw [← hgg v, ← hgg w]; exact congrArg _ hvw]
      exact disjoint_bot_right))
    have := hK.image (f := Matrix.mulVecLin (g : Matrix (Fin 2) (Fin 2) K)) (by
      rw [LinearMap.ker_eq_bot.mpr fun v w hvw => by
        rw [← hgg' v, ← hgg' w]; exact congrArg _ hvw]
      exact disjoint_bot_right)
    rwa [Set.image_image, Set.image_congr fun v _ => by
      rw [Matrix.mulVecLin_apply, mulVecLinR_apply, hgg], Set.image_id'] at this
  span_eq_top := by
    rw [eq_top_iff]
    intro v _
    have hv : v = (g : Matrix (Fin 2) (Fin 2) K) *ᵥ
        (((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [hv]
    have hw : ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v ∈
        Submodule.span K (L : Set (Fin 2 → K)) := hL.span_eq_top ▸ Submodule.mem_top
    refine Submodule.span_induction
      (p := fun w _ => (g : Matrix (Fin 2) (Fin 2) K) *ᵥ w ∈
        Submodule.span K ((latticeMap g L : Set (Fin 2 → K)))) ?_ ?_ ?_ ?_ hw
    · intro x hx
      exact Submodule.subset_span (mulVec_mem_latticeMap hx)
    · simp only [Matrix.mulVec_zero]
      exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      simp only [Matrix.mulVec_add]
      exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      simp only [Matrix.mulVec_smul]
      exact Submodule.smul_mem _ c hx

theorem isInteger_apply_of_mem_range {g : Matrix.GeneralLinearGroup (Fin 2) K}
    (hg : g ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range)
    (i j : Fin 2) : IsLocalization.IsInteger R ((g : Matrix (Fin 2) (Fin 2) K) i j) := by
  obtain ⟨h, rfl⟩ := hg
  exact ⟨h i j, (Matrix.GeneralLinearGroup.map_apply (algebraMap R K) i j h).symm⟩

theorem latticeMap_le_stdLattice_of_isInteger {g : Matrix.GeneralLinearGroup (Fin 2) K}
    (hg : ∀ i j, IsLocalization.IsInteger R ((g : Matrix (Fin 2) (Fin 2) K) i j)) :
    latticeMap g (stdLattice R K) ≤ stdLattice R K := by
  rintro _ ⟨w, hw, rfl⟩
  intro i
  show IsLocalization.IsInteger R (((g : Matrix (Fin 2) (Fin 2) K) *ᵥ w) i)
  have hcoord : ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ w) i =
      (g : Matrix (Fin 2) (Fin 2) K) i 0 * w 0 +
        (g : Matrix (Fin 2) (Fin 2) K) i 1 * w 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hcoord]
  exact IsLocalization.isInteger_add
    (IsLocalization.isInteger_mul (hg i 0) (hw 0))
    (IsLocalization.isInteger_mul (hg i 1) (hw 1))

def scalarGL (c : Kˣ) : Matrix.GeneralLinearGroup (Fin 2) K :=
  ⟨(c : K) • 1, ((c⁻¹ : Kˣ) : K) • 1, by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Units.mul_inv,
        one_smul], by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Units.inv_mul,
        one_smul]⟩

@[simp] theorem scalarGL_coe (c : Kˣ) :
    ((scalarGL c : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (c : K) • 1 := rfl

theorem scalarGL_mulVec (c : Kˣ) (v : Fin 2 → K) :
    ((scalarGL c : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v =
      (c : K) • v := by
  rw [scalarGL_coe, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem scalarGL_mul (c c' : Kˣ) :
    (scalarGL (c * c') : Matrix.GeneralLinearGroup (Fin 2) K) = scalarGL c * scalarGL c' := by
  ext1
  rw [Units.val_mul, scalarGL_coe, scalarGL_coe, scalarGL_coe, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, smul_smul, Units.val_mul]

theorem scalarGL_one : (scalarGL (1 : Kˣ) : Matrix.GeneralLinearGroup (Fin 2) K) = 1 := by
  ext1
  rw [scalarGL_coe, Units.val_one, one_smul, Units.val_one]

theorem scalarGL_mul_comm (c : Kˣ) (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    scalarGL c * g = g * scalarGL c := by
  ext1
  rw [Units.val_mul, Units.val_mul, scalarGL_coe, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one]

theorem mem_latticeMap_scalarGL {c : Kˣ} {L : Submodule R (Fin 2 → K)} {v : Fin 2 → K} :
    v ∈ latticeMap (scalarGL c) L ↔ ∃ w ∈ L, (c : K) • w = v := by
  rw [mem_latticeMap]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, (scalarGL_mulVec c w).symm⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, scalarGL_mulVec c w⟩

def diagSnd (x : Kˣ) : Matrix.GeneralLinearGroup (Fin 2) K :=
  ⟨Matrix.diagonal ![1, (x : K)], Matrix.diagonal ![1, ((x⁻¹ : Kˣ) : K)], by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp, by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp⟩

@[simp] theorem diagSnd_coe (x : Kˣ) :
    ((diagSnd x : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal ![1, (x : K)] := rfl

theorem diagSnd_mulVec (x : Kˣ) (v : Fin 2 → K) :
    ((diagSnd x : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v =
      ![v 0, (x : K) * v 1] := by
  rw [diagSnd_coe, diagonal_mulVec]
  funext i
  fin_cases i <;> simp

theorem mem_latticeMap_diagSnd_stdLattice {x : Kˣ} {v : Fin 2 → K} :
    v ∈ latticeMap (diagSnd x) (stdLattice R K) ↔
      IsLocalization.IsInteger R (v 0) ∧
        ∃ w : K, IsLocalization.IsInteger R w ∧ (x : K) * w = v 1 := by
  rw [mem_latticeMap]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [diagSnd_mulVec]
    exact ⟨by simpa using hw 0, w 1, hw 1, by simp⟩
  · rintro ⟨h0, w1, hw1, hw1'⟩
    refine ⟨![v 0, w1], ?_, ?_⟩
    · intro i
      fin_cases i
      · simpa using h0
      · simpa using hw1
    · rw [diagSnd_mulVec]
      funext i
      fin_cases i <;> simp [hw1']

theorem single_zero_one_mem_latticeMap_diagSnd (x : Kˣ) :
    (Pi.single 0 1 : Fin 2 → K) ∈ latticeMap (diagSnd x) (stdLattice R K) := by
  rw [mem_latticeMap_diagSnd_stdLattice]
  refine ⟨by rw [Pi.single_eq_same]; exact IsLocalization.isInteger_one,
    0, IsLocalization.isInteger_zero, ?_⟩
  rw [mul_zero, Pi.single_eq_of_ne]
  decide

def Homothetic (L L' : Submodule R (Fin 2 → K)) : Prop :=
  ∃ c : Kˣ, latticeMap (scalarGL c) L = L'

theorem Homothetic.refl (L : Submodule R (Fin 2 → K)) : Homothetic L L :=
  ⟨1, by rw [scalarGL_one, latticeMap_one]⟩

theorem Homothetic.symm {L L' : Submodule R (Fin 2 → K)} (h : Homothetic L L') :
    Homothetic L' L := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨c⁻¹, by
    rw [← latticeMap_mul, ← scalarGL_mul, inv_mul_cancel, scalarGL_one, latticeMap_one]⟩

theorem Homothetic.trans {L L' L'' : Submodule R (Fin 2 → K)}
    (h : Homothetic L L') (h' : Homothetic L' L'') : Homothetic L L'' := by
  obtain ⟨c, rfl⟩ := h
  obtain ⟨c', rfl⟩ := h'
  exact ⟨c' * c, by rw [scalarGL_mul, latticeMap_mul]⟩

theorem IsFullLattice.of_homothetic {L L' : Submodule R (Fin 2 → K)}
    (hL : Submodule.IsFullLattice K L) (h : Homothetic L L') : Submodule.IsFullLattice K L' := by
  obtain ⟨c, rfl⟩ := h
  exact IsFullLattice.map hL _

variable (R K) in

def FullLattice : Type _ := {L : Submodule R (Fin 2 → K) // Submodule.IsFullLattice K L}


end LT.LatticeTree
