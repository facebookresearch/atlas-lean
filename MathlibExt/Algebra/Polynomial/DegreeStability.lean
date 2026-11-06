/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.L1Norm

/-!
# Degree stability under small l1-perturbations

Monic polynomials within `l1Norm`-distance one of each other have equal
natural degree. This is the degree half of a root-continuity statement; the
root-matching half (producing an `IsClosestConjugate` pair) is not proved here.
-/

@[expose] public section

namespace Polynomial

variable {K : Type*} [Ring K] [Nontrivial K]

/-- **Monic polynomials close in L1 norm have the same degree.** Let $K$ be a nontrivial ring
and $v$ a real-valued absolute value on $K$. If $f, g \in K[x]$ are monic and the L1 norm of
$f - g$ with respect to $v$ is strictly less than $1$, then $f$ and $g$ have the same degree. -/
theorem natDegree_eq_of_monic_of_l1Norm_sub_lt_one (v : AbsoluteValue K ℝ)
    {f g : Polynomial K} (hf : f.Monic) (hg : g.Monic)
    (h : l1Norm v (f - g) < 1) : f.natDegree = g.natDegree := by
  apply le_antisymm
  · by_contra hle
    push Not at hle
    have hg0 : g.coeff f.natDegree = 0 := coeff_eq_zero_of_natDegree_lt hle
    have hcoeff : (f - g).coeff f.natDegree = 1 := by
      rw [coeff_sub, hf.coeff_natDegree, hg0, sub_zero]
    have hmem : f.natDegree ∈ (f - g).support :=
      mem_support_iff.mpr (by rw [hcoeff]; exact one_ne_zero)
    have hbound := Finset.single_le_sum (s := (f - g).support)
      (f := fun i => v ((f - g).coeff i)) (fun i _ => v.nonneg _) hmem
    rw [l1Norm_def] at h
    simpa [hcoeff] using hbound.trans_lt h
  · by_contra hle
    push Not at hle
    have hf0 : f.coeff g.natDegree = 0 := coeff_eq_zero_of_natDegree_lt hle
    have hcoeff : (f - g).coeff g.natDegree = -1 := by
      rw [coeff_sub, hf0, hg.coeff_natDegree, zero_sub]
    have hmem : g.natDegree ∈ (f - g).support :=
      mem_support_iff.mpr (by rw [hcoeff]; exact neg_ne_zero.mpr one_ne_zero)
    have hbound := Finset.single_le_sum (s := (f - g).support)
      (f := fun i => v ((f - g).coeff i)) (fun i _ => v.nonneg _) hmem
    rw [l1Norm_def] at h
    simpa [hcoeff] using hbound.trans_lt h

end Polynomial
