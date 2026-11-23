/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.AizenmanSignDominance

/-!
# Inclusion–exclusion for the random-current GHS gap

The GHS gap of a sourced current decomposed by the connectivity of three sites.

## i. Overview

For a current with source set `A` and distinct sites `o, x, y`, the GHS gap is `mass(A) - mass(A ∆
{x, y}) - mass(A ∆ {o, y}) - mass(A ∆ {o, x})`, where `mass(S)` sums a weight over sub-currents with
sources `S`. It is nonnegative unless all three pairs are connected, and equals `-2 mass(A)` when
they are. Summing over currents, the total gap is nonnegative under the domination condition `2 ·
mass(all connected) ≤ mass(none connected)`.

Several hypotheses in this file are *domination conditions* (`2 · mass(all connected) ≤ mass(none
connected)`); `ahd_hdom_refutable` shows that such a condition fails on a triangle, so the results
conditional on it are not unconditional proofs of the GHS inequality. The unconditional GHS
inequality is in `GHSLebowitz`.

## ii. Key results

- `StatMech.Ising.aie_allConn` : all three pairs are connected
- `StatMech.Ising.aie_gap` : the GHS gap of a current
- `StatMech.Ising.aie_per_super_nonneg_not_all` : the gap is nonnegative unless all pairs connect
- `StatMech.Ising.aie_gap_allConn` : the gap is `-2 mass` when all pairs connect
- `StatMech.Ising.aie_inclusion_exclusion` : the total gap is nonnegative under domination
- `StatMech.Ising.aie_ghs_distinct_site` : the conditional distinct-site GHS bound

## iii. Table of contents

- A. Connectivity of three sites
- B. Masses and the GHS gap
- C. Inclusion–exclusion over currents

## iv. References

- M. Aizenman, *Geometric analysis of φ⁴ fields and Ising models. Parts I and II*, Comm. Math. Phys.
  86 (1982) 1–48
- R. B. Griffiths, C. A. Hurst and S. Sherman, *Concavity of magnetization of an Ising ferromagnet
  in a positive external field*, J. Math. Phys. 11 (1970) 790–795
-/

@[expose] public section

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical


namespace StatMech

namespace Sharpness

namespace RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]

lemma aie_conn_trans_xy (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hoy : connK ends m o y) (hox : connK ends m o x) : connK ends m x y :=
  Relation.ReflTransGen.trans (connK_symm ends m hox) hoy

lemma aie_conn_trans_ox (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hxy : connK ends m x y) (hoy : connK ends m o y) : connK ends m o x :=
  Relation.ReflTransGen.trans hoy (connK_symm ends m hxy)

omit [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι] in
lemma aie_conn_trans_oy (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hxy : connK ends m x y) (hox : connK ends m o x) : connK ends m o y :=
  Relation.ReflTransGen.trans hox hxy

/-! ## A. Connectivity of three sites -/

/-- The current `m` connects each of the pairs `{x, y}`, `{o, y}`, `{o, x}`. -/
def aie_allConn (ends : ι → Sym2 V) (m : Finset ι) (o x y : V) : Prop :=
  connK ends m x y ∧ connK ends m o y ∧ connK ends m o x

/-- The current `m` connects none of the pairs `{x, y}`, `{o, y}`, `{o, x}`. -/
def aie_noneConn (ends : ι → Sym2 V) (m : Finset ι) (o x y : V) : Prop :=
  ¬ connK ends m x y ∧ ¬ connK ends m o y ∧ ¬ connK ends m o x

omit [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι] in
lemma aie_noneConn_not_allConn (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (h : aie_noneConn ends m o x y) : ¬ aie_allConn ends m o x y := by
  rintro ⟨h1, _, _⟩; exact h.1 h1

lemma aie_backbone_trichotomy (ends : ι → Sym2 V) (m : Finset ι) (o x y : V) :
    asd_ghsBackboneFactor ends m o x y = 1
    ∨ asd_ghsBackboneFactor ends m o x y = 0
    ∨ asd_ghsBackboneFactor ends m o x y = -2 := by
  unfold asd_ghsBackboneFactor
  by_cases hxy : connK ends m x y <;> by_cases hoy : connK ends m o y <;>
    by_cases hox : connK ends m o x
  · right; right; rw [ite_eq_left hxy, ite_eq_left hoy, ite_eq_left hox]; norm_num
  · exact absurd (aie_conn_trans_ox ends m hxy hoy) hox
  · exact absurd (aie_conn_trans_oy ends m hxy hox) hoy
  · right; left; rw [ite_eq_left hxy, ite_eq_right hoy, ite_eq_right hox]; norm_num
  · exact absurd (aie_conn_trans_xy ends m hoy hox) hxy
  · right; left; rw [ite_eq_right hxy, ite_eq_left hoy, ite_eq_right hox]; norm_num
  · right; left; rw [ite_eq_right hxy, ite_eq_right hoy, ite_eq_left hox]; norm_num
  · left; rw [ite_eq_right hxy, ite_eq_right hoy, ite_eq_right hox]; norm_num

omit [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι] in
lemma aie_backbone_value_none (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (h : aie_noneConn ends m o x y) : asd_ghsBackboneFactor ends m o x y = 1 :=
  asd_ghsBackboneFactor_noConn ends m h.1 h.2.1 h.2.2

omit [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι] in
lemma aie_backbone_value_all (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (h : aie_allConn ends m o x y) : asd_ghsBackboneFactor ends m o x y = -2 :=
  asd_ghsBackboneFactor_allConn ends m h.1 h.2.1 h.2.2

lemma aie_backbone_value_one (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hnotall : ¬ aie_allConn ends m o x y) (hnotnone : ¬ aie_noneConn ends m o x y) :
    asd_ghsBackboneFactor ends m o x y = 0 := by
  unfold asd_ghsBackboneFactor
  simp only [aie_allConn, aie_noneConn] at hnotall hnotnone
  by_cases hxy : connK ends m x y <;> by_cases hoy : connK ends m o y <;>
    by_cases hox : connK ends m o x
  · exact absurd ⟨hxy, hoy, hox⟩ hnotall
  · exact absurd (aie_conn_trans_ox ends m hxy hoy) hox
  · exact absurd (aie_conn_trans_oy ends m hxy hox) hoy
  · rw [ite_eq_left hxy, ite_eq_right hoy, ite_eq_right hox]; norm_num
  · exact absurd (aie_conn_trans_xy ends m hoy hox) hxy
  · rw [ite_eq_right hxy, ite_eq_left hoy, ite_eq_right hox]; norm_num
  · rw [ite_eq_right hxy, ite_eq_right hoy, ite_eq_left hox]; norm_num
  · exact absurd ⟨hxy, hoy, hox⟩ hnotnone

lemma aie_backbone_factor_nonneg_not_all (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hnotall : ¬ aie_allConn ends m o x y) : 0 ≤ asd_ghsBackboneFactor ends m o x y := by
  by_cases hnone : aie_noneConn ends m o x y
  · rw [aie_backbone_value_none ends m hnone]; norm_num
  · rw [aie_backbone_value_one ends m hnotall hnone]

/-! ## B. Masses and the GHS gap -/

/-- The total weight `∑ φ(K)` of the sub-currents `K ⊆ m` with source set `S`. -/
noncomputable def aie_mass (ends : ι → Sym2 V) (m : Finset ι) (φ : Finset ι → ℝ) (S : Finset V) :
    ℝ :=
  ∑ K ∈ m.powerset.filter (fun K => sources ends K = S), φ K

/-- The GHS gap `mass(A) - mass(A ∆ {x, y}) - mass(A ∆ {o, y}) - mass(A ∆ {o, x})`. -/
noncomputable def aie_gap (ends : ι → Sym2 V) (m : Finset ι) (φ : Finset ι → ℝ) (A : Finset V)
    (o x y : V) : ℝ :=
  aie_mass ends m φ A - aie_mass ends m φ (A ∆ {x, y})
    - aie_mass ends m φ (A ∆ {o, y}) - aie_mass ends m φ (A ∆ {o, x})

omit [DecidableEq ι] [Fintype ι] in
lemma aie_mass_nonneg (ends : ι → Sym2 V) (m : Finset ι) (φ : Finset ι → ℝ)
    (hφnn : ∀ K, 0 ≤ φ K) (S : Finset V) : 0 ≤ aie_mass ends m φ S :=
  Finset.sum_nonneg (fun K _ => hφnn K)

lemma aie_gap_eq (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) :
    aie_gap ends m φ A o x y = aie_mass ends m φ A * asd_ghsBackboneFactor ends m o x y := by
  unfold aie_gap aie_mass asd_ghsBackboneFactor
  exact asd_ghsSigned_eq ends m hnd A hm hox hoy hxy φ hφ

lemma aie_per_super_nonneg_not_all (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφnn : ∀ K, 0 ≤ φ K) (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hnotall : ¬ aie_allConn ends m o x y) :
    0 ≤ aie_gap ends m φ A o x y := by
  rw [aie_gap_eq ends m hnd A hm hox hoy hxy φ hφ]
  exact mul_nonneg (aie_mass_nonneg ends m φ hφnn A)
    (aie_backbone_factor_nonneg_not_all ends m hnotall)

lemma aie_gap_allConn (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) (hall : aie_allConn ends m o x y) :
    aie_gap ends m φ A o x y = -2 * aie_mass ends m φ A := by
  rw [aie_gap_eq ends m hnd A hm hox hoy hxy φ hφ, aie_backbone_value_all ends m hall]; ring

lemma aie_gap_noneConn (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) (hnone : aie_noneConn ends m o x y) :
    aie_gap ends m φ A o x y = aie_mass ends m φ A := by
  rw [aie_gap_eq ends m hnd A hm hox hoy hxy φ hφ, aie_backbone_value_none ends m hnone]; ring

lemma aie_gap_exactlyOne (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hnotall : ¬ aie_allConn ends m o x y) (hnotnone : ¬ aie_noneConn ends m o x y) :
    aie_gap ends m φ A o x y = 0 := by
  rw [aie_gap_eq ends m hnd A hm hox hoy hxy φ hφ,
      aie_backbone_value_one ends m hnotall hnotnone]; ring

omit [DecidableEq ι] [Fintype ι] in
lemma aie_inclusion_exclusion_split (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (A : Finset V) (o x y : V) (Φ : Finset ι → Finset ι → ℝ) :
    ∑ m ∈ M, aie_gap ends m (Φ m) A o x y
      = (∑ m ∈ M, aie_mass ends m (Φ m) A)
        - (∑ m ∈ M, aie_mass ends m (Φ m) (A ∆ {x, y}))
        - (∑ m ∈ M, aie_mass ends m (Φ m) (A ∆ {o, y}))
        - (∑ m ∈ M, aie_mass ends m (Φ m) (A ∆ {o, x})) := by
  unfold aie_gap
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]

lemma aie_inclusion_exclusion_decomp (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K) :
    ∑ m ∈ M, aie_gap ends m (Φ m) A o x y
      = (∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A)
        - 2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A) := by

  rw [← Finset.sum_filter_add_sum_filter_not M (fun m => aie_allConn ends m o x y)
    (fun m => aie_gap ends m (Φ m) A o x y)]

  have hall : ∑ m ∈ M.filter (fun m => aie_allConn ends m o x y),
        aie_gap ends m (Φ m) A o x y
      = -2 * ∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m hmem => ?_)
    rw [Finset.mem_filter] at hmem
    exact aie_gap_allConn ends m (hnd m hmem.1) A (hm m hmem.1) hox hoy hxy (Φ m)
      (hΦ m hmem.1) hmem.2

  have hrest : ∑ m ∈ M.filter (fun m => ¬ aie_allConn ends m o x y),
        aie_gap ends m (Φ m) A o x y
      = ∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A := by
    rw [← Finset.sum_filter_add_sum_filter_not (M.filter (fun m => ¬ aie_allConn ends m o x y))
      (fun m => aie_noneConn ends m o x y) (fun m => aie_gap ends m (Φ m) A o x y)]

    have hfilt : (M.filter (fun m => ¬ aie_allConn ends m o x y)).filter
        (fun m => aie_noneConn ends m o x y) = M.filter (fun m => aie_noneConn ends m o x y) := by
      ext m
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hm0, _⟩, hn⟩; exact ⟨hm0, hn⟩
      · rintro ⟨hm0, hn⟩
        exact ⟨⟨hm0, aie_noneConn_not_allConn ends m hn⟩, hn⟩
    have h1 : ∑ m ∈ (M.filter (fun m => ¬ aie_allConn ends m o x y)).filter
          (fun m => aie_noneConn ends m o x y), aie_gap ends m (Φ m) A o x y
        = ∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A := by
      rw [hfilt]
      refine Finset.sum_congr rfl (fun m hmem => ?_)
      rw [Finset.mem_filter] at hmem
      exact aie_gap_noneConn ends m (hnd m hmem.1) A (hm m hmem.1) hox hoy hxy (Φ m)
        (hΦ m hmem.1) hmem.2

    have h2 : ∑ m ∈ (M.filter (fun m => ¬ aie_allConn ends m o x y)).filter
          (fun m => ¬ aie_noneConn ends m o x y), aie_gap ends m (Φ m) A o x y = 0 := by
      refine Finset.sum_eq_zero (fun m hmem => ?_)
      simp only [Finset.mem_filter] at hmem
      exact aie_gap_exactlyOne ends m (hnd m hmem.1.1) A (hm m hmem.1.1) hox hoy hxy (Φ m)
        (hΦ m hmem.1.1) hmem.1.2 hmem.2
    rw [h1, h2, add_zero]
  rw [hall, hrest]; ring

/-! ## C. Inclusion–exclusion over currents -/

lemma aie_inclusion_exclusion (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K)
    (hdom : 2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A)
      ≤ ∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A) :
    0 ≤ ∑ m ∈ M, aie_gap ends m (Φ m) A o x y := by
  rw [aie_inclusion_exclusion_decomp ends M hnd A hm hox hoy hxy Φ hΦ]
  linarith

lemma aie_ghs_distinct_site (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K)
    (hdom : 2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A)
      ≤ ∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A) :
    (∑ m ∈ M, aie_mass ends m (Φ m) (A ∆ {x, y}))
      + (∑ m ∈ M, aie_mass ends m (Φ m) (A ∆ {o, y}))
      + (∑ m ∈ M, aie_mass ends m (Φ m) (A ∆ {o, x}))
      ≤ ∑ m ∈ M, aie_mass ends m (Φ m) A := by
  have hge : 0 ≤ ∑ m ∈ M, aie_gap ends m (Φ m) A o x y :=
    aie_inclusion_exclusion ends M hnd A hm hox hoy hxy Φ hΦ hdom
  rw [aie_inclusion_exclusion_split ends M A o x y Φ] at hge
  linarith

end RandomCurrent

end Sharpness

end StatMech
