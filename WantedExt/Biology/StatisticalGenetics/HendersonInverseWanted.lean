/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
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

Recorded here: the `T D Tᵀ` factorization with positive `D`, and the local-addition formula for
`A⁻¹`, for every pedigree with distinct known parents that precede their offspring. The
algorithmic cost and the computation of the inbreeding coefficients are not formalized.

Sources: C. R. Henderson, "A simple method for computing the inverse of a numerator relationship
matrix used in prediction of breeding values", Biometrics 32 (1976) 69–83; the `L D Lᵀ` form as
presented in course notes on Henderson's rules (secondary source; the primary was not read
locally).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

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

variable {n : ℕ} (ped : Pedigree n)

/-- The entry `A_ip` for a parent `p` of an animal, or `0` when the parent is unknown. -/
def parentEntry (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : Option (Fin n) → ℝ
  | none => 0
  | some p => A i p

/-- The inbreeding coefficient of animal `k` read from a relationship matrix `A`: half the
relationship between its parents, or `0` when a parent is unknown. -/
noncomputable def inbreeding (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) : ℝ :=
  match ped.sire k, ped.dam k with
  | some s, some d => A s d / 2
  | _, _ => 0

/-- `A` is the **numerator relationship matrix** of the pedigree: it satisfies the tabular
method, i.e. it is symmetric, `A_jj = 1 + F_j`, and `A_ij = (A_is + A_id) / 2` for `i < j`. -/
def IsTabular (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A.IsSymm ∧ (∀ j, A j j = 1 + ped.inbreeding A j) ∧
    ∀ i j, i < j → A i j = (parentEntry A i (ped.sire j) + parentEntry A i (ped.dam j)) / 2

/-- Henderson's diagonal entry `D_i`, the Mendelian sampling variance of animal `i` relative to
the additive variance: `1/2 - (F_s + F_d)/4`, `3/4 - F_p/4` or `1` according as two, one or no
parents are known. -/
noncomputable def mendelianVar (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ :=
  match ped.sire i, ped.dam i with
  | some s, some d => 1 / 2 - (ped.inbreeding A s + ped.inbreeding A d) / 4
  | some s, none => 3 / 4 - ped.inbreeding A s / 4
  | none, some d => 3 / 4 - ped.inbreeding A d / 4
  | none, none => 1

/-- The parent-average matrix `P`: entry `1/2` at each known parent of each animal. -/
noncomputable def parentMatrix : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  (if ped.sire i = some j then 1 / 2 else 0) + (if ped.dam i = some j then 1 / 2 else 0)

/-- Row `i` of `I - P`: `eᵢ - ½ e_s - ½ e_d` over the known parents `s`, `d` of animal `i`. -/
noncomputable def hendersonVec (i : Fin n) : Fin n → ℝ := (1 - ped.parentMatrix) i

/-- **Henderson's `T D Tᵀ` factorization** (Henderson 1976): if `A` is the numerator
relationship matrix of a pedigree with parents before offspring, then every Mendelian sampling
variance `D_i` is positive and `A = (I - P)⁻¹ D ((I - P)⁻¹)ᵀ`.

Source: Henderson (1976). -/
public theorem_wanted eq_ldl (A : Matrix (Fin n) (Fin n) ℝ) (hA : ped.IsTabular A) :
    (∀ i, 0 < ped.mendelianVar A i) ∧
      A = (1 - ped.parentMatrix)⁻¹ * diagonal (ped.mendelianVar A) *
        ((1 - ped.parentMatrix)⁻¹)ᵀ

/-- **Henderson's rules for `A⁻¹`** (Henderson 1976): if `A` is the numerator relationship matrix
of a pedigree with parents before offspring, then `A` is invertible and
`A⁻¹ = ∑ᵢ D_i⁻¹ cᵢ cᵢᵀ` with `cᵢ = eᵢ - ½ e_s - ½ e_d`, i.e. `A⁻¹ = (I - P)ᵀ D⁻¹ (I - P)` is
assembled by local additions over parent–offspring triples.

Source: Henderson (1976). -/
public theorem_wanted inv_eq_sum (A : Matrix (Fin n) (Fin n) ℝ) (hA : ped.IsTabular A) :
    IsUnit A.det ∧
      A⁻¹ = ∑ i, (ped.mendelianVar A i)⁻¹ • vecMulVec (ped.hendersonVec i) (ped.hendersonVec i)

end Pedigree

end WantedExt.Biology.StatisticalGenetics.HendersonInverseWanted
