/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Henderson's rules for the inverse numerator relationship matrix

For a pedigree of `n` animals ordered so that parents precede their offspring, the numerator
relationship matrix `A` is given by the tabular method: `A` is symmetric,
`A_jj = 1 + A_sd / 2` when both parents `s` and `d` of `j` are known (and `1` otherwise), and
`A_ij = (A_is + A_id) / 2` for `i < j`, where a missing parent contributes `0`. Henderson
(1976) observed that `A = T D Tᵀ` with `T = (I - P)⁻¹` unit lower triangular, where `P` has
entries `1/2` at the known parents of each animal (the parent-average recursion of breeding
values), and `D` diagonal with `D_i = 1/2 - (F_s + F_d)/4` when both parents are known,
`3/4 - F_p/4` when one parent `p` is known and `1` when none is, `F_k = A_{s_k d_k} / 2` being
the inbreeding coefficient. Hence `A⁻¹ = (I - P)ᵀ D⁻¹ (I - P)`, which is assembled from the
pedigree by local additions: for each animal `i`, add `D_i⁻¹ cᵢ cᵢᵀ` with
`cᵢ = eᵢ - ½ e_s - ½ e_d` (the `+1`, `-1/2`, `+1/4` multiples of `D_i⁻¹` over each
parent–offspring triple).

This module proves the local-addition formula for `A⁻¹`: every entry of a tabular matrix lies
in `[0, 2)`, so every Mendelian variance is positive; `(I - P) A (I - P)ᵀ` equals the diagonal
matrix of Mendelian variances; hence `A` is invertible with
`A⁻¹ = ∑ᵢ D_i⁻¹ cᵢ cᵢᵀ`.

## References

* C. R. Henderson, "A simple method for computing the inverse of a numerator relationship
  matrix used in prediction of breeding values", Biometrics 32 (1976) 69–83; the `L D Lᵀ`
  form as presented in course notes on Henderson's rules (secondary source; the primary was
  not read locally).
-/

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.HendersonInverseWanted

open Matrix

/-- A pedigree of `n` animals: each animal has an optional sire and an optional dam, every known
parent precedes its offspring in the ordering, and the two known parents of an animal are
distinct animals. -/
structure Pedigree (n : ℕ) where
  /-- The sire of each animal, if known. -/
  sire : Fin n → Option (Fin n)
  /-- The dam of each animal, if known. -/
  dam : Fin n → Option (Fin n)
  sire_lt : ∀ i s, sire i = some s → s < i
  dam_lt : ∀ i d, dam i = some d → d < i
  sire_ne_dam : ∀ i s d, sire i = some s → dam i = some d → s ≠ d

namespace Pedigree

/-- The entry `A_ip` for a parent `p` of an animal, or `0` when the parent is unknown. -/
def parentEntry {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : Option (Fin n) → ℝ
  | none => 0
  | some p => A i p

/-- The inbreeding coefficient of animal `k` read from a relationship matrix `A`: half the
relationship between its parents, or `0` when a parent is unknown. -/
noncomputable def inbreeding {n : ℕ} (ped : Pedigree n) (A : Matrix (Fin n) (Fin n) ℝ)
    (k : Fin n) : ℝ :=
  match ped.sire k, ped.dam k with
  | some s, some d => A s d / 2
  | _, _ => 0

/-- `A` is the **numerator relationship matrix** of the pedigree: it satisfies the tabular
method, i.e. it is symmetric, `A_jj = 1 + F_j`, and `A_ij = (A_is + A_id) / 2` for `i < j`. -/
def IsTabular {n : ℕ} (ped : Pedigree n) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A.IsSymm ∧ (∀ j, A j j = 1 + ped.inbreeding A j) ∧
    ∀ i j, i < j → A i j = (parentEntry A i (ped.sire j) + parentEntry A i (ped.dam j)) / 2

/-- Henderson's diagonal entry `D_i`, the Mendelian sampling variance of animal `i` relative to
the additive variance: `1/2 - (F_s + F_d)/4`, `3/4 - F_p/4` or `1` according as two, one or no
parents are known. -/
noncomputable def mendelianVar {n : ℕ} (ped : Pedigree n) (A : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) : ℝ :=
  match ped.sire i, ped.dam i with
  | some s, some d => 1 / 2 - (ped.inbreeding A s + ped.inbreeding A d) / 4
  | some s, none => 3 / 4 - ped.inbreeding A s / 4
  | none, some d => 3 / 4 - ped.inbreeding A d / 4
  | none, none => 1

/-- The parent-average matrix `P`: entry `1/2` at each known parent of each animal. -/
noncomputable def parentMatrix {n : ℕ} (ped : Pedigree n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    (if ped.sire i = some j then 1 / 2 else 0) +
      (if ped.dam i = some j then 1 / 2 else 0)

/-- Row `i` of `I - P`: `eᵢ - ½ e_s - ½ e_d` over the known parents `s`, `d` of animal `i`. -/
noncomputable def hendersonVec {n : ℕ} (ped : Pedigree n) (i : Fin n) : Fin n → ℝ :=
  (1 - ped.parentMatrix) i

/-- A known parent contributes the relationship entry. -/
private theorem parentEntry_some {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i p : Fin n) :
    parentEntry A i (some p) = A i p :=
  rfl

/-- An unknown parent contributes `0`. -/
private theorem parentEntry_none {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    parentEntry A i none = 0 :=
  rfl

/-- The inbreeding coefficient when both parents are known. -/
private theorem inbreeding_some_some {n : ℕ} (ped : Pedigree n)
    (A : Matrix (Fin n) (Fin n) ℝ) (k s d : Fin n) (hs : ped.sire k = some s)
    (hd : ped.dam k = some d) : ped.inbreeding A k = A s d / 2 := by
  unfold inbreeding
  rw [hs, hd]

/-- The inbreeding coefficient is `0` when the sire is unknown. -/
private theorem inbreeding_of_sire_none {n : ℕ} (ped : Pedigree n)
    (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) (hs : ped.sire k = none) :
    ped.inbreeding A k = 0 := by
  unfold inbreeding
  rw [hs]

/-- The inbreeding coefficient is `0` when the dam is unknown. -/
private theorem inbreeding_of_dam_none {n : ℕ} (ped : Pedigree n)
    (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) (hd : ped.dam k = none) :
    ped.inbreeding A k = 0 := by
  unfold inbreeding
  rw [hd]
  cases h : ped.sire k <;> rfl

/-- The Mendelian variance when both parents are known. -/
private theorem mendelianVar_some_some {n : ℕ} (ped : Pedigree n)
    (A : Matrix (Fin n) (Fin n) ℝ) (i s d : Fin n) (hs : ped.sire i = some s)
    (hd : ped.dam i = some d) :
    ped.mendelianVar A i = 1 / 2 - (ped.inbreeding A s + ped.inbreeding A d) / 4 := by
  unfold mendelianVar
  rw [hs, hd]

/-- The Mendelian variance when only the sire is known. -/
private theorem mendelianVar_some_none {n : ℕ} (ped : Pedigree n)
    (A : Matrix (Fin n) (Fin n) ℝ) (i s : Fin n) (hs : ped.sire i = some s)
    (hd : ped.dam i = none) :
    ped.mendelianVar A i = 3 / 4 - ped.inbreeding A s / 4 := by
  unfold mendelianVar
  rw [hs, hd]

/-- The Mendelian variance when only the dam is known. -/
private theorem mendelianVar_none_some {n : ℕ} (ped : Pedigree n)
    (A : Matrix (Fin n) (Fin n) ℝ) (i d : Fin n) (hs : ped.sire i = none)
    (hd : ped.dam i = some d) :
    ped.mendelianVar A i = 3 / 4 - ped.inbreeding A d / 4 := by
  unfold mendelianVar
  rw [hs, hd]

/-- The Mendelian variance when no parent is known. -/
private theorem mendelianVar_none_none {n : ℕ} (ped : Pedigree n)
    (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (hs : ped.sire i = none)
    (hd : ped.dam i = none) : ped.mendelianVar A i = 1 := by
  unfold mendelianVar
  rw [hs, hd]

/-- Entries of a symmetric matrix read the same in either order. -/
private theorem symm_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (h : A.IsSymm)
    (i j : Fin n) : A i j = A j i :=
  (h.apply i j).symm

/-- Every entry of a tabular matrix with indices at most `m` lies in `[0, 2)`. -/
private theorem entry_bounds_aux {n : ℕ} (ped : Pedigree n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : ped.IsTabular A) (m : ℕ) (i j : Fin n)
    (hi : i.val ≤ m) (hj : j.val ≤ m) : 0 ≤ A i j ∧ A i j < 2 := by
  obtain ⟨hsymm, hdiag, hoff⟩ := hA
  induction m generalizing i j with
  | zero =>
    have hi0 : i.val = 0 := by omega
    have hj0 : j.val = 0 := by omega
    have hij : i = j := Fin.ext_iff.mpr (by omega)
    subst hij
    have hs : ped.sire i = none := by
      cases h : ped.sire i
      case none => rfl
      case some s =>
        have hlt := ped.sire_lt i s h
        omega
    have hii : A i i = 1 := by
      rw [hdiag i, inbreeding_of_sire_none _ _ _ hs]
      norm_num
    rw [hii]
    norm_num
  | succ m ih =>
    have hlt : ∀ a b : Fin n, a.val < b.val → b.val ≤ m + 1 → 0 ≤ A a b ∧ A a b < 2 := by
      intro a b hab hb
      have hAab : A a b =
          (parentEntry A a (ped.sire b) + parentEntry A a (ped.dam b)) / 2 :=
        hoff a b hab
      have h1 : 0 ≤ parentEntry A a (ped.sire b) ∧ parentEntry A a (ped.sire b) < 2 := by
        cases hs : ped.sire b
        case none =>
          rw [parentEntry_none]
          norm_num
        case some s =>
          rw [parentEntry_some]
          have hsb : s < b := ped.sire_lt b s hs
          exact ih a s (by omega) (by omega)
      have h2 : 0 ≤ parentEntry A a (ped.dam b) ∧ parentEntry A a (ped.dam b) < 2 := by
        cases hd : ped.dam b
        case none =>
          rw [parentEntry_none]
          norm_num
        case some d =>
          rw [parentEntry_some]
          have hdb : d < b := ped.dam_lt b d hd
          exact ih a d (by omega) (by omega)
      obtain ⟨h1lo, h1hi⟩ := h1
      obtain ⟨h2lo, h2hi⟩ := h2
      rw [hAab]
      constructor <;> linarith
    rcases lt_trichotomy i.val j.val with h | h | h
    · exact hlt i j h hj
    · have hij : i = j := Fin.ext_iff.mpr h
      subst hij
      have hF : 0 ≤ ped.inbreeding A i ∧ ped.inbreeding A i < 1 := by
        cases hsi : ped.sire i
        case none =>
          rw [inbreeding_of_sire_none _ _ _ hsi]
          norm_num
        case some s =>
          cases hdi : ped.dam i
          case none =>
            rw [inbreeding_of_dam_none _ _ _ hdi]
            norm_num
          case some d =>
            rw [inbreeding_some_some _ _ _ _ _ hsi hdi]
            have hsi' : s < i := ped.sire_lt i s hsi
            have hdi' : d < i := ped.dam_lt i d hdi
            have hsd := ih s d (by omega) (by omega)
            obtain ⟨hlo, hhi⟩ := hsd
            constructor <;> linarith
      have hdiag_i : A i i = 1 + ped.inbreeding A i := hdiag i
      obtain ⟨flo, fhi⟩ := hF
      rw [hdiag_i]
      constructor <;> linarith
    · rw [symm_apply A hsymm]
      exact hlt j i h hi

/-- Every entry of a tabular matrix lies in `[0, 2)`. -/
private theorem entry_bounds {n : ℕ} (ped : Pedigree n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ped.IsTabular A) (i j : Fin n) : 0 ≤ A i j ∧ A i j < 2 :=
  entry_bounds_aux ped A hA n i j (by omega) (by omega)

/-- Every inbreeding coefficient lies in `[0, 1)`. -/
private theorem inbreeding_bounds {n : ℕ} (ped : Pedigree n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : ped.IsTabular A) (k : Fin n) :
    0 ≤ ped.inbreeding A k ∧ ped.inbreeding A k < 1 := by
  cases hs : ped.sire k
  case none =>
    rw [inbreeding_of_sire_none _ _ _ hs]
    norm_num
  case some s =>
    cases hd : ped.dam k
    case none =>
      rw [inbreeding_of_dam_none _ _ _ hd]
      norm_num
    case some d =>
      rw [inbreeding_some_some _ _ _ _ _ hs hd]
      obtain ⟨hlo, hhi⟩ := entry_bounds ped A hA s d
      constructor <;> linarith

/-- Every Mendelian variance is positive. -/
private theorem mendelianVar_pos {n : ℕ} (ped : Pedigree n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : ped.IsTabular A) (i : Fin n) :
    0 < ped.mendelianVar A i := by
  cases hs : ped.sire i
  case none =>
    cases hd : ped.dam i
    case none =>
      rw [mendelianVar_none_none _ _ _ hs hd]
      norm_num
    case some d =>
      rw [mendelianVar_none_some _ _ _ _ hs hd]
      obtain ⟨flo, fhi⟩ := inbreeding_bounds ped A hA d
      linarith
  case some s =>
    cases hd : ped.dam i
    case none =>
      rw [mendelianVar_some_none _ _ _ _ hs hd]
      obtain ⟨flo, fhi⟩ := inbreeding_bounds ped A hA s
      linarith
    case some d =>
      rw [mendelianVar_some_some _ _ _ _ _ hs hd]
      obtain ⟨flos, fhis⟩ := inbreeding_bounds ped A hA s
      obtain ⟨flod, fhid⟩ := inbreeding_bounds ped A hA d
      linarith

/-- A row of `M` summed against a row of the parent matrix is the parent average. -/
private theorem sum_mul_parentMatrix {n : ℕ} (ped : Pedigree n)
    (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ∑ l, M i l * ped.parentMatrix j l =
      (parentEntry M i (ped.sire j) + parentEntry M i (ped.dam j)) / 2 := by
  cases hs : ped.sire j
  case none =>
    cases hd : ped.dam j
    case none =>
      rw [parentEntry_none]
      have h0 : ∀ l, M i l * ped.parentMatrix j l = 0 := by
        intro l
        unfold parentMatrix
        rw [hs, hd]
        simp
      simp [h0]
    case some d =>
      rw [parentEntry_none, parentEntry_some]
      have hPl : ∀ l, M i l * ped.parentMatrix j l =
          (if d = l then M i l * (1/2) else 0) := by
        intro l
        unfold parentMatrix
        rw [hs, hd]
        by_cases h : d = l <;> simp [h]
      simp only [hPl, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      ring
  case some s =>
    cases hd : ped.dam j
    case none =>
      rw [parentEntry_some, parentEntry_none]
      have hPl : ∀ l, M i l * ped.parentMatrix j l =
          (if s = l then M i l * (1/2) else 0) := by
        intro l
        unfold parentMatrix
        rw [hs, hd]
        by_cases h : s = l <;> simp [h]
      simp only [hPl, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      ring
    case some d =>
      rw [parentEntry_some, parentEntry_some]
      have hPl : ∀ l, M i l * ped.parentMatrix j l =
          (if s = l then M i l * (1/2) else 0) +
            (if d = l then M i l * (1/2) else 0) := by
        intro l
        unfold parentMatrix
        rw [hs, hd]
        by_cases h1 : s = l <;> by_cases h2 : d = l <;> simp [h1, h2, mul_add]
      simp only [hPl, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      ring

/-- Right multiplication by `(I - P)ᵀ` subtracts the parent average. -/
private theorem mul_Lt {n : ℕ} (ped : Pedigree n) (M : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) :
    (M * (1 - ped.parentMatrix : Matrix (Fin n) (Fin n) ℝ)ᵀ) i j =
      M i j - (parentEntry M i (ped.sire j) + parentEntry M i (ped.dam j)) / 2 := by
  have hsub : ∀ l, M i l * ((1 - ped.parentMatrix)ᵀ l j) =
      M i l * (((if j = l then (1:ℝ) else 0) - ped.parentMatrix j l)) := by
    intro l
    rw [Matrix.transpose_apply, Matrix.sub_apply, Matrix.one_apply]
  have hdirac : ∀ l, M i l * (if j = l then (1:ℝ) else 0) =
      (if j = l then M i l else 0) := by
    intro l
    by_cases h : j = l <;> simp [h]
  rw [Matrix.mul_apply]
  simp only [hsub, mul_sub, Finset.sum_sub_distrib, hdirac, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  rw [sum_mul_parentMatrix]

/-- A column of `M` summed against a row of the parent matrix, both parents known. -/
private theorem sum_parentMatrix_mul_some_some {n : ℕ} (ped : Pedigree n)
    (M : Matrix (Fin n) (Fin n) ℝ) (i j s d : Fin n) (hs : ped.sire i = some s)
    (hd : ped.dam i = some d) :
    ∑ k, ped.parentMatrix i k * M k j = (M s j + M d j) / 2 := by
  have hP : ∀ k, ped.parentMatrix i k * M k j =
      (if s = k then (1/2 : ℝ) * M k j else 0) +
        (if d = k then (1/2 : ℝ) * M k j else 0) := by
    intro k
    unfold parentMatrix
    rw [hs, hd]
    by_cases h1 : s = k <;> by_cases h2 : d = k <;> simp [h1, h2, add_mul]
  simp only [hP, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- A column of `M` summed against a row of the parent matrix, only the sire known. -/
private theorem sum_parentMatrix_mul_some_none {n : ℕ} (ped : Pedigree n)
    (M : Matrix (Fin n) (Fin n) ℝ) (i j s : Fin n) (hs : ped.sire i = some s)
    (hd : ped.dam i = none) :
    ∑ k, ped.parentMatrix i k * M k j = M s j / 2 := by
  have hP : ∀ k, ped.parentMatrix i k * M k j =
      (if s = k then (1/2 : ℝ) * M k j else 0) := by
    intro k
    unfold parentMatrix
    rw [hs, hd]
    by_cases h : s = k <;> simp [h]
  simp only [hP, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- A column of `M` summed against a row of the parent matrix, only the dam known. -/
private theorem sum_parentMatrix_mul_none_some {n : ℕ} (ped : Pedigree n)
    (M : Matrix (Fin n) (Fin n) ℝ) (i j d : Fin n) (hs : ped.sire i = none)
    (hd : ped.dam i = some d) :
    ∑ k, ped.parentMatrix i k * M k j = M d j / 2 := by
  have hP : ∀ k, ped.parentMatrix i k * M k j =
      (if d = k then (1/2 : ℝ) * M k j else 0) := by
    intro k
    unfold parentMatrix
    rw [hs, hd]
    by_cases h : d = k <;> simp [h]
  simp only [hP, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- A column of `M` summed against a row of the parent matrix, no parent known. -/
private theorem sum_parentMatrix_mul_none_none {n : ℕ} (ped : Pedigree n)
    (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (hs : ped.sire i = none)
    (hd : ped.dam i = none) :
    ∑ k, ped.parentMatrix i k * M k j = 0 := by
  have h0 : ∀ k, ped.parentMatrix i k * M k j = 0 := by
    intro k
    unfold parentMatrix
    rw [hs, hd]
    simp
  simp [h0]

/-- Left multiplication by `I - P`, both parents known. -/
private theorem L_mul_some_some {n : ℕ} (ped : Pedigree n)
    (M : Matrix (Fin n) (Fin n) ℝ) (i j s d : Fin n) (hs : ped.sire i = some s)
    (hd : ped.dam i = some d) :
    ((1 - ped.parentMatrix) * M) i j = M i j - (M s j + M d j) / 2 := by
  have hsub : ∀ k, ((1 - ped.parentMatrix) i k) * M k j =
      (((if i = k then (1:ℝ) else 0) - ped.parentMatrix i k) * M k j) := by
    intro k
    rw [Matrix.sub_apply, Matrix.one_apply]
  have hdirac : ∀ k, (if i = k then (1:ℝ) else 0) * M k j =
      (if i = k then M k j else 0) := by
    intro k
    by_cases h : i = k <;> simp [h]
  rw [Matrix.mul_apply]
  simp only [hsub, sub_mul, Finset.sum_sub_distrib, hdirac, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  rw [sum_parentMatrix_mul_some_some _ _ _ _ _ _ hs hd]

/-- Left multiplication by `I - P`, only the sire known. -/
private theorem L_mul_some_none {n : ℕ} (ped : Pedigree n)
    (M : Matrix (Fin n) (Fin n) ℝ) (i j s : Fin n) (hs : ped.sire i = some s)
    (hd : ped.dam i = none) :
    ((1 - ped.parentMatrix) * M) i j = M i j - M s j / 2 := by
  have hsub : ∀ k, ((1 - ped.parentMatrix) i k) * M k j =
      (((if i = k then (1:ℝ) else 0) - ped.parentMatrix i k) * M k j) := by
    intro k
    rw [Matrix.sub_apply, Matrix.one_apply]
  have hdirac : ∀ k, (if i = k then (1:ℝ) else 0) * M k j =
      (if i = k then M k j else 0) := by
    intro k
    by_cases h : i = k <;> simp [h]
  rw [Matrix.mul_apply]
  simp only [hsub, sub_mul, Finset.sum_sub_distrib, hdirac, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  rw [sum_parentMatrix_mul_some_none _ _ _ _ _ hs hd]

/-- Left multiplication by `I - P`, only the dam known. -/
private theorem L_mul_none_some {n : ℕ} (ped : Pedigree n)
    (M : Matrix (Fin n) (Fin n) ℝ) (i j d : Fin n) (hs : ped.sire i = none)
    (hd : ped.dam i = some d) :
    ((1 - ped.parentMatrix) * M) i j = M i j - M d j / 2 := by
  have hsub : ∀ k, ((1 - ped.parentMatrix) i k) * M k j =
      (((if i = k then (1:ℝ) else 0) - ped.parentMatrix i k) * M k j) := by
    intro k
    rw [Matrix.sub_apply, Matrix.one_apply]
  have hdirac : ∀ k, (if i = k then (1:ℝ) else 0) * M k j =
      (if i = k then M k j else 0) := by
    intro k
    by_cases h : i = k <;> simp [h]
  rw [Matrix.mul_apply]
  simp only [hsub, sub_mul, Finset.sum_sub_distrib, hdirac, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  rw [sum_parentMatrix_mul_none_some _ _ _ _ _ hs hd]

/-- Left multiplication by `I - P`, no parent known. -/
private theorem L_mul_none_none {n : ℕ} (ped : Pedigree n)
    (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (hs : ped.sire i = none)
    (hd : ped.dam i = none) :
    ((1 - ped.parentMatrix) * M) i j = M i j := by
  have hsub : ∀ k, ((1 - ped.parentMatrix) i k) * M k j =
      (((if i = k then (1:ℝ) else 0) - ped.parentMatrix i k) * M k j) := by
    intro k
    rw [Matrix.sub_apply, Matrix.one_apply]
  have hdirac : ∀ k, (if i = k then (1:ℝ) else 0) * M k j =
      (if i = k then M k j else 0) := by
    intro k
    by_cases h : i = k <;> simp [h]
  rw [Matrix.mul_apply]
  simp only [hsub, sub_mul, Finset.sum_sub_distrib, hdirac, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  rw [sum_parentMatrix_mul_none_none _ _ _ _ hs hd, sub_zero]

/-- Entries of `A (I - P)ᵀ` vanish above the diagonal. -/
private theorem ALt_offdiag {n : ℕ} (ped : Pedigree n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ped.IsTabular A) (a b : Fin n) (hab : a < b) :
    (A * (1 - ped.parentMatrix : Matrix (Fin n) (Fin n) ℝ)ᵀ) a b = 0 := by
  obtain ⟨hsymm, hdiag, hoff⟩ := hA
  rw [mul_Lt, hoff a b hab]
  ring

/-- Entries of `(I - P) A (I - P)ᵀ` vanish above the diagonal. -/
private theorem LALt_apply_offdiag {n : ℕ} (ped : Pedigree n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : ped.IsTabular A) (i j : Fin n) (hij : i < j) :
    ((1 - ped.parentMatrix) *
        (A * (1 - ped.parentMatrix : Matrix (Fin n) (Fin n) ℝ)ᵀ)) i j = 0 := by
  cases hs : ped.sire i
  case none =>
    cases hd : ped.dam i
    case none =>
      rw [L_mul_none_none _ _ _ _ hs hd]
      exact ALt_offdiag ped A hA i j hij
    case some d =>
      rw [L_mul_none_some _ _ _ _ _ hs hd]
      have h1 := ALt_offdiag ped A hA i j hij
      have h2 := ALt_offdiag ped A hA d j (lt_trans (ped.dam_lt i d hd) hij)
      rw [h1, h2]
      norm_num
  case some s =>
    cases hd : ped.dam i
    case none =>
      rw [L_mul_some_none _ _ _ _ _ hs hd]
      have h1 := ALt_offdiag ped A hA i j hij
      have h2 := ALt_offdiag ped A hA s j (lt_trans (ped.sire_lt i s hs) hij)
      rw [h1, h2]
      norm_num
    case some d =>
      rw [L_mul_some_some _ _ _ _ _ _ hs hd]
      have h1 := ALt_offdiag ped A hA i j hij
      have h2 := ALt_offdiag ped A hA s j (lt_trans (ped.sire_lt i s hs) hij)
      have h3 := ALt_offdiag ped A hA d j (lt_trans (ped.dam_lt i d hd) hij)
      rw [h1, h2, h3]
      norm_num

/-- Diagonal entries of `(I - P) A (I - P)ᵀ` are the Mendelian variances. -/
private theorem LALt_apply_diag {n : ℕ} (ped : Pedigree n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : ped.IsTabular A) (i : Fin n) :
    ((1 - ped.parentMatrix) *
        (A * (1 - ped.parentMatrix : Matrix (Fin n) (Fin n) ℝ)ᵀ)) i i =
      ped.mendelianVar A i := by
  have hsymm : A.IsSymm := hA.1
  have hdiag : ∀ j, A j j = 1 + ped.inbreeding A j := hA.2.1
  have hoff : ∀ i j, i < j →
      A i j = (parentEntry A i (ped.sire j) + parentEntry A i (ped.dam j)) / 2 := hA.2.2
  cases hs : ped.sire i
  case none =>
    cases hd : ped.dam i
    case none =>
      rw [L_mul_none_none _ _ _ _ hs hd, mendelianVar_none_none _ _ _ hs hd,
        mul_Lt, hs, hd, parentEntry_none]
      have hdiag_i : A i i = 1 + ped.inbreeding A i := hdiag i
      rw [inbreeding_of_sire_none _ _ _ hs] at hdiag_i
      rw [hdiag_i]
      norm_num
    case some d =>
      rw [L_mul_none_some _ _ _ _ _ hs hd, mendelianVar_none_some _ _ _ _ hs hd]
      have hdi : d < i := ped.dam_lt i d hd
      have hz := ALt_offdiag ped A hA d i hdi
      rw [hz, mul_Lt, hs, hd, parentEntry_none, parentEntry_some]
      have hsym := symm_apply A hsymm i d
      have hhoff := hoff d i hdi
      rw [hs, hd, parentEntry_none, parentEntry_some] at hhoff
      have hdiag_i := hdiag i
      rw [inbreeding_of_sire_none _ _ _ hs] at hdiag_i
      have hdiag_d := hdiag d
      linarith
  case some s =>
    cases hd : ped.dam i
    case none =>
      rw [L_mul_some_none _ _ _ _ _ hs hd, mendelianVar_some_none _ _ _ _ hs hd]
      have hsi : s < i := ped.sire_lt i s hs
      have hz := ALt_offdiag ped A hA s i hsi
      rw [hz, mul_Lt, hs, hd, parentEntry_some, parentEntry_none]
      have hsym := symm_apply A hsymm i s
      have hhoff := hoff s i hsi
      rw [hs, hd, parentEntry_some, parentEntry_none] at hhoff
      have hdiag_i := hdiag i
      rw [inbreeding_of_dam_none _ _ _ hd] at hdiag_i
      have hdiag_s := hdiag s
      linarith
    case some d =>
      rw [L_mul_some_some _ _ _ _ _ _ hs hd, mendelianVar_some_some _ _ _ _ _ hs hd]
      have hsi : s < i := ped.sire_lt i s hs
      have hdi : d < i := ped.dam_lt i d hd
      have hzs := ALt_offdiag ped A hA s i hsi
      have hzd := ALt_offdiag ped A hA d i hdi
      rw [hzs, hzd, mul_Lt, hs, hd, parentEntry_some, parentEntry_some]
      have hsym_s := symm_apply A hsymm i s
      have hsym_d := symm_apply A hsymm i d
      have hhoff_s := hoff s i hsi
      have hhoff_d := hoff d i hdi
      rw [hs, hd, parentEntry_some, parentEntry_some] at hhoff_s
      rw [hs, hd, parentEntry_some, parentEntry_some] at hhoff_d
      have hdiag_i := hdiag i
      have hdiag_s := hdiag s
      have hdiag_d := hdiag d
      rw [inbreeding_some_some _ _ _ _ _ hs hd] at hdiag_i
      have hsym_sd := symm_apply A hsymm d s
      linarith

/-- Transposing `(I - P) * (A * (I - P)ᵀ)`. -/
private theorem LALt_symm {n : ℕ} (ped : Pedigree n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ped.IsTabular A) :
    ((1 - ped.parentMatrix) *
          (A * (1 - ped.parentMatrix : Matrix (Fin n) (Fin n) ℝ)ᵀ))ᵀ =
        (1 - ped.parentMatrix) * A *
          (1 - ped.parentMatrix : Matrix (Fin n) (Fin n) ℝ)ᵀ := by
  obtain ⟨hsymm, hdiag, hoff⟩ := hA
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hsymm.eq]

/-- Entries of `(I - P) A (I - P)ᵀ`: Mendelian variances on the diagonal, `0` elsewhere. -/
private theorem LALt_entry {n : ℕ} (ped : Pedigree n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ped.IsTabular A) (i j : Fin n) :
    ((1 - ped.parentMatrix) * A *
        (1 - ped.parentMatrix : Matrix (Fin n) (Fin n) ℝ)ᵀ) i j =
      if i = j then ped.mendelianVar A i else 0 := by
  rw [Matrix.mul_assoc]
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl]
    exact LALt_apply_diag ped A hA i
  · rw [ite_eq_right hij]
    rcases lt_trichotomy i.val j.val with h | h | h
    · exact LALt_apply_offdiag ped A hA i j h
    · exact absurd (Fin.ext_iff.mpr h) hij
    · have e1 : ((1 - ped.parentMatrix) *
            (A * (1 - ped.parentMatrix : Matrix (Fin n) (Fin n) ℝ)ᵀ)) i j =
          (((1 - ped.parentMatrix) *
              (A * (1 - ped.parentMatrix : Matrix (Fin n) (Fin n) ℝ)ᵀ))ᵀ) j i :=
        (Matrix.transpose_apply _ j i).symm
      rw [e1, LALt_symm ped A hA, Matrix.mul_assoc]
      exact LALt_apply_offdiag ped A hA j i h

/-- `(I - P) A (I - P)ᵀ` is the diagonal matrix of Mendelian variances. -/
private theorem LALt_eq_diagonal {n : ℕ} (ped : Pedigree n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : ped.IsTabular A) :
    ((1 - ped.parentMatrix) * A *
        (1 - ped.parentMatrix : Matrix (Fin n) (Fin n) ℝ)ᵀ) =
      Matrix.diagonal (ped.mendelianVar A) := by
  ext i j
  rw [LALt_entry ped A hA i j]
  by_cases hij : i = j <;> simp [hij]

/-- `I - P` is lower triangular. -/
private theorem L_isLowerTriangular {n : ℕ} (ped : Pedigree n) :
    (1 - ped.parentMatrix).IsLowerTriangular := by
  intro i j h
  have hij : i < j := h
  have hs0 : ped.sire i ≠ some j := fun h' => (not_lt_of_gt (ped.sire_lt i j h')) hij
  have hd0 : ped.dam i ≠ some j := fun h' => (not_lt_of_gt (ped.dam_lt i j h')) hij
  have hne : i ≠ j := ne_of_lt hij
  rw [Matrix.sub_apply, Matrix.one_apply, ite_eq_right hne]
  unfold parentMatrix
  rw [ite_eq_right hs0, ite_eq_right hd0]
  norm_num

/-- `I - P` has ones on the diagonal. -/
private theorem L_diag {n : ℕ} (ped : Pedigree n) (i : Fin n) :
    (1 - ped.parentMatrix) i i = 1 := by
  have hs0 : ped.sire i ≠ some i := fun h' => lt_irrefl _ (ped.sire_lt i i h')
  have hd0 : ped.dam i ≠ some i := fun h' => lt_irrefl _ (ped.dam_lt i i h')
  rw [Matrix.sub_apply, Matrix.one_apply, ite_eq_left rfl]
  unfold parentMatrix
  rw [ite_eq_right hs0, ite_eq_right hd0]
  norm_num

/-- `I - P` has determinant one. -/
private theorem det_L {n : ℕ} (ped : Pedigree n) :
    (1 - ped.parentMatrix : Matrix (Fin n) (Fin n) ℝ).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (L_isLowerTriangular ped)]
  simp only [L_diag ped, Finset.prod_const_one]

/-- The inverse of a diagonal matrix with nonzero entries. -/
private theorem diag_inv {n : ℕ} (D : Fin n → ℝ) (hD : ∀ i, D i ≠ 0) :
    (Matrix.diagonal D)⁻¹ = Matrix.diagonal fun i => (D i)⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal]
  have h1 : (fun i => (D i)⁻¹ * D i) = fun _ => (1:ℝ) :=
    funext fun i => inv_mul_cancel₀ (hD i)
  rw [h1, Matrix.diagonal_one]

/-- `(I - P)ᵀ D (I - P)` as a sum of rank-one matrices. -/
private theorem LtDinvL_eq_sum {n : ℕ} (ped : Pedigree n) (D : Fin n → ℝ) :
    (1 - ped.parentMatrix : Matrix (Fin n) (Fin n) ℝ)ᵀ * Matrix.diagonal D *
        (1 - ped.parentMatrix) =
      ∑ i, D i • Matrix.vecMulVec ((1 - ped.parentMatrix) i) ((1 - ped.parentMatrix) i) := by
  ext j k
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.diagonal_mul, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- **Henderson's rules for `A⁻¹`** (Henderson 1976): if `A` is the numerator relationship matrix
of a pedigree with parents before offspring, then `A` is invertible and
`A⁻¹ = ∑ᵢ D_i⁻¹ cᵢ cᵢᵀ` with `cᵢ = eᵢ - ½ e_s - ½ e_d`, i.e. `A⁻¹ = (I - P)ᵀ D⁻¹ (I - P)` is
assembled by local additions over parent–offspring triples.

Source: Henderson (1976). -/
public theorem inv_eq_sum {n : ℕ} (ped : Pedigree n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ped.IsTabular A) :
    IsUnit A.det ∧
      A⁻¹ = ∑ i, (ped.mendelianVar A i)⁻¹ • vecMulVec (ped.hendersonVec i) (ped.hendersonVec i)
    := by
  have hDne : ∀ i, ped.mendelianVar A i ≠ 0 :=
    fun i => ne_of_gt (mendelianVar_pos ped A hA i)
  have hLALt := LALt_eq_diagonal ped A hA
  have hdetL : (1 - ped.parentMatrix : Matrix (Fin n) (Fin n) ℝ).det = 1 := det_L ped
  have huL : IsUnit (1 - ped.parentMatrix : Matrix (Fin n) (Fin n) ℝ).det := by
    rw [hdetL]
    exact isUnit_one
  have huLt : IsUnit (1 - ped.parentMatrix : Matrix (Fin n) (Fin n) ℝ)ᵀ.det := by
    rw [Matrix.det_transpose, hdetL]
    exact isUnit_one
  have huD : IsUnit (Matrix.diagonal (ped.mendelianVar A)).det := by
    apply isUnit_iff_ne_zero.mpr
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hDne i)
  have hAeq : A = (1 - ped.parentMatrix : Matrix (Fin n) (Fin n) ℝ)⁻¹ *
      Matrix.diagonal (ped.mendelianVar A) *
        ((1 - ped.parentMatrix : Matrix (Fin n) (Fin n) ℝ)ᵀ)⁻¹ := by
    have h1 : (1 - ped.parentMatrix : Matrix (Fin n) (Fin n) ℝ)⁻¹ *
        ((1 - ped.parentMatrix) * A *
          (1 - ped.parentMatrix : Matrix (Fin n) (Fin n) ℝ)ᵀ) *
        ((1 - ped.parentMatrix : Matrix (Fin n) (Fin n) ℝ)ᵀ)⁻¹ = A := by
      simp only [Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv _ huLt, Matrix.mul_one, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ huL, Matrix.one_mul]
    rw [hLALt] at h1
    exact h1.symm
  have hAB : A * ((1 - ped.parentMatrix : Matrix (Fin n) (Fin n) ℝ)ᵀ *
      (Matrix.diagonal (ped.mendelianVar A))⁻¹ * (1 - ped.parentMatrix)) = 1 := by
    nth_rewrite 1 [hAeq]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((1 - ped.parentMatrix : Matrix (Fin n) (Fin n) ℝ)ᵀ)⁻¹,
      Matrix.nonsing_inv_mul _ huLt, Matrix.one_mul,
      ← Matrix.mul_assoc _ (Matrix.diagonal (ped.mendelianVar A))⁻¹,
      Matrix.mul_nonsing_inv _ huD, Matrix.one_mul,
      Matrix.nonsing_inv_mul _ huL]
  have hAinv : A⁻¹ = (1 - ped.parentMatrix : Matrix (Fin n) (Fin n) ℝ)ᵀ *
      (Matrix.diagonal (ped.mendelianVar A))⁻¹ * (1 - ped.parentMatrix) :=
    Matrix.inv_eq_right_inv hAB
  have hunit : IsUnit A.det := by
    have hdet : A.det * ((1 - ped.parentMatrix : Matrix (Fin n) (Fin n) ℝ)ᵀ *
        (Matrix.diagonal (ped.mendelianVar A))⁻¹ * (1 - ped.parentMatrix)).det = 1 := by
      rw [← Matrix.det_mul, hAB, Matrix.det_one]
    have hne : A.det ≠ 0 := by
      intro h
      rw [h, zero_mul] at hdet
      exact zero_ne_one hdet
    exact isUnit_iff_ne_zero.mpr hne
  have hsum : (1 - ped.parentMatrix : Matrix (Fin n) (Fin n) ℝ)ᵀ *
      (Matrix.diagonal (ped.mendelianVar A))⁻¹ * (1 - ped.parentMatrix) =
      ∑ i, (ped.mendelianVar A i)⁻¹ •
        Matrix.vecMulVec ((1 - ped.parentMatrix) i) ((1 - ped.parentMatrix) i) := by
    rw [diag_inv _ hDne]
    exact LtDinvL_eq_sum ped (fun i => (ped.mendelianVar A i)⁻¹)
  refine ⟨hunit, ?_⟩
  have hfold : ∀ i, ped.hendersonVec i = (1 - ped.parentMatrix) i := fun i => rfl
  simp only [hfold]
  rw [hAinv, hsum]

end Pedigree

end WantedExt.Biology.StatisticalGenetics.HendersonInverseWanted
