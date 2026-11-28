/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.Data.Matrix.Basic

/-!
# Common-denominator form of proper rational matrices

A rational matrix is proper when every entry has numerator degree at most
denominator degree (`RatFunc.intDegree ≤ 0`). Every proper rational
matrix `G` over a field `𝕜` splits as `G = D + N / d` with a constant
matrix `D` (the value at infinity), a polynomial matrix `N`, and one
common monic denominator `d` whose degree strictly exceeds every entry
degree of `N`; the construction takes `d` to be the product of the
monic entry denominators (`RatFunc.denom` is normalized to be monic)
and divides. This is the
standard first step from a proper transfer matrix toward a state-space
realization; no realization is constructed here. The common denominator
is not claimed minimal (it need not be the lcm of the entry
denominators).

Provenance: the classical proper-rational-matrix normal form.
-/

open Polynomial Matrix

@[expose] public section

namespace ControlTheory

namespace RatMatrix

/-- A rational matrix is proper when every entry has numerator degree at
most denominator degree (`RatFunc.intDegree ≤ 0`; the zero entry counts as
proper, with `intDegree 0 = 0`). -/
def IsProper {𝕜 : Type*} [Field 𝕜] {p m : Type*}
    (G : Matrix p m (RatFunc 𝕜)) : Prop :=
  ∀ i j, (G i j).intDegree ≤ 0

/-- Common-denominator form of a proper rational matrix: every proper
rational matrix `G` with finitely many rows and columns splits as `G = D + N / d` with a
constant matrix `D`, a polynomial matrix
`N`, and a single common monic denominator `d` whose degree strictly
exceeds the degree of every entry of `N` (polynomial `degree`, so the
zero polynomial, of degree `⊥`, is allowed in `N` even when `d = 1`). -/
theorem exists_commonDenom {𝕜 : Type*} [Field 𝕜] {p m : Type*}
    [Fintype p] [Fintype m]
    (G : Matrix p m (RatFunc 𝕜)) (hG : IsProper G) :
    ∃ (D : Matrix p m 𝕜) (N : Matrix p m 𝕜[X]) (d : 𝕜[X]),
      d.Monic ∧ (∀ i j, (N i j).degree < d.degree) ∧
        ∀ i j, G i j = algebraMap 𝕜 (RatFunc 𝕜) (D i j)
          + algebraMap 𝕜[X] (RatFunc 𝕜) (N i j) / algebraMap 𝕜[X] (RatFunc 𝕜) d := by
  set d : 𝕜[X] := ∏ i, ∏ j, (G i j).denom with hd
  have hdM : d.Monic := by
    rw [hd]
    exact monic_prod_of_monic Finset.univ (fun i => ∏ j, (G i j).denom)
      (fun i _ => monic_prod_of_monic Finset.univ (fun j => (G i j).denom)
        (fun j _ => RatFunc.monic_denom (G i j)))
  have hd0 : d ≠ 0 := hdM.ne_zero
  have hdvd : ∀ i j, (G i j).denom ∣ d := by
    intro i j
    rw [hd]
    exact dvd_trans
      (Finset.dvd_prod_of_mem (fun k => (G i k).denom) (Finset.mem_univ j))
      (Finset.dvd_prod_of_mem (fun k => ∏ l, (G k l).denom) (Finset.mem_univ i))
  have hdvd' : ∀ i j, ∃ e, d = (G i j).denom * e := hdvd
  choose e he using hdvd'
  refine ⟨Matrix.of (fun i j => (((G i j).num * e i j) / d).coeff 0),
    Matrix.of (fun i j => ((G i j).num * e i j) % d), d, hdM, ?_, ?_⟩
  · intro i j
    simp only [Matrix.of_apply]
    show (((G i j).num * e i j) % d).degree < d.degree
    exact degree_mod_lt _ hd0
  · intro i j
    simp only [Matrix.of_apply]
    have he0 : e i j ≠ 0 := by
      intro h
      apply hd0
      rw [he i j, h, mul_zero]
    have hproper0 := hG i j
    simp only [RatFunc.intDegree] at hproper0
    have hproper : (G i j).num.natDegree ≤ (G i j).denom.natDegree := by omega
    have hdnat : d.natDegree = (G i j).denom.natDegree + (e i j).natDegree := by
      rw [he i j]
      exact natDegree_mul (RatFunc.denom_ne_zero (G i j)) he0
    have hPnat : ((G i j).num * e i j).natDegree ≤ d.natDegree := by
      by_cases hn0 : (G i j).num = 0
      · have hP0 : (G i j).num * e i j = 0 := by rw [hn0, zero_mul]
        rw [hP0, natDegree_zero]
        exact Nat.zero_le _
      · have hPm : ((G i j).num * e i j).natDegree
            = (G i j).num.natDegree + (e i j).natDegree :=
          natDegree_mul hn0 he0
        omega
    have hNdeg : (((G i j).num * e i j) % d).degree < d.degree :=
      degree_mod_lt _ hd0
    have hNnat : (((G i j).num * e i j) % d).natDegree ≤ d.natDegree := by
      by_cases hN0 : ((G i j).num * e i j) % d = 0
      · rw [hN0, natDegree_zero]
        exact Nat.zero_le _
      · exact le_of_lt (natDegree_lt_natDegree hN0 hNdeg)
    have hdam : d * (((G i j).num * e i j) / d)
        = ((G i j).num * e i j) - ((G i j).num * e i j) % d := by
      have h := EuclideanDomain.div_add_mod ((G i j).num * e i j) d
      calc d * (((G i j).num * e i j) / d)
          = (d * (((G i j).num * e i j) / d) + ((G i j).num * e i j) % d)
            - ((G i j).num * e i j) % d := by rw [add_sub_cancel_right]
        _ = ((G i j).num * e i j) - ((G i j).num * e i j) % d := by rw [h]
    have hsub : (d * (((G i j).num * e i j) / d)).natDegree ≤ d.natDegree := by
      rw [hdam, sub_eq_add_neg]
      have h2 := natDegree_add_le ((G i j).num * e i j)
        (-(((G i j).num * e i j) % d))
      rw [natDegree_neg] at h2
      omega
    have hqnat : (((G i j).num * e i j) / d).natDegree ≤ 0 := by
      by_cases hq0 : ((G i j).num * e i j) / d = 0
      · rw [hq0, natDegree_zero]
      · have hmul := natDegree_mul hd0 hq0
        omega
    have hqC : ((G i j).num * e i j) / d
        = C ((((G i j).num * e i j) / d).coeff 0) :=
      eq_C_of_natDegree_le_zero hqnat
    have hdA : algebraMap 𝕜[X] (RatFunc 𝕜) d ≠ 0 :=
      RatFunc.algebraMap_ne_zero hd0
    have heA : algebraMap 𝕜[X] (RatFunc 𝕜) (e i j) ≠ 0 :=
      RatFunc.algebraMap_ne_zero he0
    have hsA : algebraMap 𝕜[X] (RatFunc 𝕜) (G i j).denom ≠ 0 :=
      RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero (G i j))
    have hAP : algebraMap 𝕜[X] (RatFunc 𝕜) ((G i j).num * e i j)
        = algebraMap 𝕜[X] (RatFunc 𝕜) d
          * algebraMap 𝕜[X] (RatFunc 𝕜) (((G i j).num * e i j) / d)
          + algebraMap 𝕜[X] (RatFunc 𝕜) (((G i j).num * e i j) % d) := by
      have h := congrArg (algebraMap 𝕜[X] (RatFunc 𝕜))
        (EuclideanDomain.div_add_mod ((G i j).num * e i j) d)
      simp only [map_add, map_mul] at h ⊢
      exact h.symm
    have hcancel : algebraMap 𝕜[X] (RatFunc 𝕜) d
          * algebraMap 𝕜[X] (RatFunc 𝕜) (((G i j).num * e i j) / d)
          / algebraMap 𝕜[X] (RatFunc 𝕜) d
        = algebraMap 𝕜[X] (RatFunc 𝕜) (((G i j).num * e i j) / d) := by
      rw [div_eq_iff hdA]
      ring
    have hdiv : algebraMap 𝕜[X] (RatFunc 𝕜) ((G i j).num * e i j)
          / algebraMap 𝕜[X] (RatFunc 𝕜) d
        = algebraMap 𝕜[X] (RatFunc 𝕜) (((G i j).num * e i j) / d)
          + algebraMap 𝕜[X] (RatFunc 𝕜) (((G i j).num * e i j) % d)
          / algebraMap 𝕜[X] (RatFunc 𝕜) d := by
      rw [hAP, add_div, hcancel]
    have hfrac : algebraMap 𝕜[X] (RatFunc 𝕜) ((G i j).num * e i j)
          / algebraMap 𝕜[X] (RatFunc 𝕜) d
        = algebraMap 𝕜[X] (RatFunc 𝕜) (G i j).num
          / algebraMap 𝕜[X] (RatFunc 𝕜) (G i j).denom := by
      rw [he i j]
      simp only [map_mul]
      rw [div_eq_div_iff (mul_ne_zero hsA heA) hsA]
      ring
    have hC : algebraMap 𝕜[X] (RatFunc 𝕜) (((G i j).num * e i j) / d)
        = algebraMap 𝕜 (RatFunc 𝕜) ((((G i j).num * e i j) / d).coeff 0) := by
      conv_lhs => rw [hqC]
      rw [RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C]
    exact calc G i j
        = algebraMap 𝕜[X] (RatFunc 𝕜) (G i j).num
          / algebraMap 𝕜[X] (RatFunc 𝕜) (G i j).denom :=
          (RatFunc.num_div_denom (G i j)).symm
      _ = algebraMap 𝕜[X] (RatFunc 𝕜) ((G i j).num * e i j)
          / algebraMap 𝕜[X] (RatFunc 𝕜) d := hfrac.symm
      _ = algebraMap 𝕜[X] (RatFunc 𝕜) (((G i j).num * e i j) / d)
          + algebraMap 𝕜[X] (RatFunc 𝕜) (((G i j).num * e i j) % d)
          / algebraMap 𝕜[X] (RatFunc 𝕜) d := hdiv
      _ = algebraMap 𝕜 (RatFunc 𝕜) ((((G i j).num * e i j) / d).coeff 0)
          + algebraMap 𝕜[X] (RatFunc 𝕜) (((G i j).num * e i j) % d)
          / algebraMap 𝕜[X] (RatFunc 𝕜) d := by rw [hC]

end RatMatrix

end ControlTheory
