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

Recorded here: the `T D Tᵀ` factorization with positive `D`, for every pedigree with distinct
known parents that precede their offspring. The local-addition formula for `A⁻¹`, for the same
pedigrees, is proved in `Domains.Biology.StatisticalGenetics.HendersonInverseInvEqSum`. The
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
public import Domains.Biology.StatisticalGenetics.HendersonInverseInvEqSum

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.HendersonInverseWanted

open Matrix

namespace Pedigree

variable {n : ℕ} (ped : Pedigree n)

/-- **Henderson's `T D Tᵀ` factorization** (Henderson 1976): if `A` is the numerator
relationship matrix of a pedigree with parents before offspring, then every Mendelian sampling
variance `D_i` is positive and `A = (I - P)⁻¹ D ((I - P)⁻¹)ᵀ`.

Source: Henderson (1976). -/
public theorem_wanted eq_ldl (A : Matrix (Fin n) (Fin n) ℝ) (hA : ped.IsTabular A) :
    (∀ i, 0 < ped.mendelianVar A i) ∧
      A = (1 - ped.parentMatrix)⁻¹ * diagonal (ped.mendelianVar A) *
        ((1 - ped.parentMatrix)⁻¹)ᵀ

end Pedigree

end WantedExt.Biology.StatisticalGenetics.HendersonInverseWanted
