/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import PhyslibExt.CondensedMatter.IsingModel.TwoReplica
public import PhyslibExt.CondensedMatter.IsingModel.TwoReplicaWeighted
public import PhyslibExt.CondensedMatter.IsingModel.BackboneExists
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.RandomCurrent
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.TwoReplica
public import PhyslibExt.CondensedMatter.IsingModel.AizenmanSignDominance

/-!
# Three-point inclusion–exclusion for split current weights

The weighted mass of sub-currents with prescribed sources, its behaviour under switching, and a
three-point (GHS-type) inequality conditional on coherence and domination hypotheses.

## i. Overview

For a current `m` and a source set `S`, `hnw_mass m S` is the weighted sum `∑_K w(K) w(m - K)` over
sub-currents `K ≤ m` with sources `S`. For three distinct sites `o, x, y`, the gap
`hnw_gap = mass(A) - mass(A ∆ {x,y}) - mass(A ∆ {o,y}) - mass(A ∆ {o,x})` equals `-2 · mass(A)` when
all three pairs are joined by odd edges (switching lemma), `mass(A)` when no pair is joined by
positive edges, and `0` in the mixed cases provided odd and positive connectivity agree for the
three pairs (`hnw_coherent`). Summing over a set `M` of currents gives an inclusion–exclusion
identity, and hence the three-point inequality
`mass(A ∆ {x,y}) + mass(A ∆ {o,y}) + mass(A ∆ {o,x}) ≤ mass(A)` summed over `M`.

Headline fidelity:
- `hnw_inclusion_exclusion_decomp` is conditional on `hcoh : ∀ m ∈ M, hnw_coherent G m o x y`
  (odd-edge and positive-edge connectivity agree for each of the three pairs), besides the
  loopless-graph hypothesis `hnd` and the source hypothesis `hm`.
- `hnw_closure_of_hdom` and `hnw_ghs_distinct_site_of_hdom` are conditional on `hcoh` and on the
  domination inequality `hdom` (twice the all-connected mass is at most the none-connected mass).
  Neither hypothesis is derived in the library. They are satisfiable (for example by `M = ∅`), so
  the statements are not vacuous, but no nontrivial family satisfying them is constructed.
- `hnw_mass_eq_weight_mul_count`, `hnw_addBackbone_sources` and `hnw_addBackbone_weight` are
  unconditional.
- The backbone chain rule (P2) does not appear.

## ii. Key results

- `StatMech.Ising.hnw_mass`, `StatMech.Ising.hnw_gap` : split mass and three-point gap
- `StatMech.Ising.hnw_allConn`, `StatMech.Ising.hnw_noneConn`, `StatMech.Ising.hnw_coherent` :
  connectivity patterns of three sites
- `StatMech.Ising.hnw_inclusion_exclusion_decomp` : the inclusion–exclusion identity
- `StatMech.Ising.hnw_ghs_distinct_site_of_hdom` : the three-point inequality
- `StatMech.Ising.hnw_addBackbone_weight` : weight of a current with a backbone added

## iii. Table of contents

- A. Split mass and three-point gap
- B. Gap in each connectivity pattern
- C. Inclusion–exclusion and the three-point inequality
- D. Adding a backbone

## iv. References

- M. Aizenman, "Geometric analysis of φ⁴ fields and Ising models", Comm. Math. Phys. 86 (1982) 1–48
- R. B. Griffiths, C. A. Hurst, S. Sherman, "Concavity of magnetization of an Ising ferromagnet in
  a positive external field", J. Math. Phys. 11 (1970) 790–795
-/

@[expose] public section

open Finset
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false

namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. Split mass and three-point gap -/

/-- The split mass `∑_K w(K) w(m - K)` over sub-currents `K ≤ m` with sources `S`. -/
noncomputable def hnw_mass (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) (S : Finset V) : ℝ :=
  splitWeightedSum G β J m 1 S

/-- The three-point gap `mass(A) - mass(A ∆ {x,y}) - mass(A ∆ {o,y}) - mass(A ∆ {o,x})`. -/
noncomputable def hnw_gap (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) (A : Finset V)
    (o x y : V) : ℝ :=
  hnw_mass G β J m A - hnw_mass G β J m (A ∆ {x, y})
    - hnw_mass G β J m (A ∆ {o, y}) - hnw_mass G β J m (A ∆ {o, x})

/-- The split mass is nonnegative for nonnegative `β` and couplings. -/
lemma hnw_mass_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (m : Current V) (S : Finset V) : 0 ≤ hnw_mass G β J m S :=
  asd_splitWeightedSum_nonneg G β J hβ hJ m 1 (by norm_num) S

/-! ## B. Gap in each connectivity pattern -/

/-- All three pairs among `o, x, y` are joined by odd edges of `m`. -/
def hnw_allConn (m : Current V) (o x y : V) : Prop :=
  connP (oddEdges G.edgeFinset m) x y ∧ connP (oddEdges G.edgeFinset m) o y
    ∧ connP (oddEdges G.edgeFinset m) o x

/-- No pair among `o, x, y` is joined by positive edges of `m`. -/
def hnw_noneConn (m : Current V) (o x y : V) : Prop :=
  ¬ connP (posEdges G.edgeFinset m) x y ∧ ¬ connP (posEdges G.edgeFinset m) o y
    ∧ ¬ connP (posEdges G.edgeFinset m) o x

omit [DecidableEq V] in
/-- The patterns `hnw_noneConn` and `hnw_allConn` are exclusive. -/
lemma hnw_noneConn_not_allConn (m : Current V) {o x y : V}
    (h : hnw_noneConn G m o x y) : ¬ hnw_allConn G m o x y := by
  rintro ⟨hxy, _, _⟩
  exact h.1 (connOdd_imp_connPos G.edgeFinset m hxy)

/-- Switching lemma for the split mass. -/
lemma hnw_switching (β : ℝ) (J : Sym2 V → ℝ) (m : Current V)
    {u v : V} (huv : u ≠ v) (hconn : connP (oddEdges G.edgeFinset m) u v) (A : Finset V) :
    hnw_mass G β J m (A ∆ {u, v}) = hnw_mass G β J m A :=
  ising_switching_weighted G β J m huv hconn 1 A

/-- The split mass with sources `A ∆ {u, v}` vanishes when `u` and `v` are not joined by positive
edges. -/
lemma hnw_mass_vanish (β : ℝ) (J : Sym2 V → ℝ) (m : Current V)
    (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (A : Finset V) (hm : Sharpness.sources G m = A)
    {u v : V} (huv : u ≠ v) (hdisc : ¬ connP (posEdges G.edgeFinset m) u v) :
    hnw_mass G β J m (A ∆ {u, v}) = 0 :=
  ising_switching_weighted_vanishing G β J m hnd A hm huv hdisc 1

omit [DecidableEq V] in
/-- Odd-edge connectivity of `o` to `x` and to `y` gives `x` to `y`. -/
lemma hnw_conn_trans_xy (m : Current V) {o x y : V}
    (hoy : connP (oddEdges G.edgeFinset m) o y) (hox : connP (oddEdges G.edgeFinset m) o x) :
    connP (oddEdges G.edgeFinset m) x y :=
  Relation.ReflTransGen.trans (connP_symm _ hox) hoy

omit [DecidableEq V] in
/-- Odd-edge connectivity of `x` to `y` and of `o` to `y` gives `o` to `x`. -/
lemma hnw_conn_trans_ox (m : Current V) {o x y : V}
    (hxy : connP (oddEdges G.edgeFinset m) x y) (hoy : connP (oddEdges G.edgeFinset m) o y) :
    connP (oddEdges G.edgeFinset m) o x :=
  Relation.ReflTransGen.trans hoy (connP_symm _ hxy)

omit [DecidableEq V] in
/-- Odd-edge connectivity of `x` to `y` and of `o` to `x` gives `o` to `y`. -/
lemma hnw_conn_trans_oy (m : Current V) {o x y : V}
    (hxy : connP (oddEdges G.edgeFinset m) x y) (hox : connP (oddEdges G.edgeFinset m) o x) :
    connP (oddEdges G.edgeFinset m) o y :=
  Relation.ReflTransGen.trans hox hxy

/-- In the all-connected pattern the gap is `-2 · mass(A)`. -/
lemma hnw_gap_allConn (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) (A : Finset V)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hall : hnw_allConn G m o x y) :
    hnw_gap G β J m A o x y = -2 * hnw_mass G β J m A := by
  obtain ⟨hxy', hoy', hox'⟩ := hall
  unfold hnw_gap
  rw [hnw_switching G β J m hxy hxy' A, hnw_switching G β J m hoy hoy' A,
      hnw_switching G β J m hox hox' A]
  ring

/-- In the none-connected pattern the gap is `mass(A)`. -/
lemma hnw_gap_noneConn (β : ℝ) (J : Sym2 V → ℝ) (m : Current V)
    (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (A : Finset V) (hm : Sharpness.sources G m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hnone : hnw_noneConn G m o x y) :
    hnw_gap G β J m A o x y = hnw_mass G β J m A := by
  obtain ⟨hxy', hoy', hox'⟩ := hnone
  unfold hnw_gap
  rw [hnw_mass_vanish G β J m hnd A hm hxy hxy',
      hnw_mass_vanish G β J m hnd A hm hoy hoy',
      hnw_mass_vanish G β J m hnd A hm hox hox']
  ring

/-- For each pair among `o, x, y`, connectivity through odd edges of `m` is equivalent to
connectivity through positive edges. -/
def hnw_coherent (m : Current V) (o x y : V) : Prop :=
  (connP (oddEdges G.edgeFinset m) x y ↔ connP (posEdges G.edgeFinset m) x y)
  ∧ (connP (oddEdges G.edgeFinset m) o y ↔ connP (posEdges G.edgeFinset m) o y)
  ∧ (connP (oddEdges G.edgeFinset m) o x ↔ connP (posEdges G.edgeFinset m) o x)

/-- Under `hnw_coherent`, the gap vanishes in the mixed patterns. -/
lemma hnw_gap_exactlyOne (β : ℝ) (J : Sym2 V → ℝ) (m : Current V)
    (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (A : Finset V) (hm : Sharpness.sources G m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hcoh : hnw_coherent G m o x y)
    (hnotall : ¬ hnw_allConn G m o x y) (hnotnone : ¬ hnw_noneConn G m o x y) :
    hnw_gap G β J m A o x y = 0 := by
  obtain ⟨cxy, coy, cox⟩ := hcoh
  unfold hnw_allConn at hnotall
  unfold hnw_noneConn at hnotnone
  unfold hnw_gap
  by_cases oxy : connP (oddEdges G.edgeFinset m) x y <;>
    by_cases ooy : connP (oddEdges G.edgeFinset m) o y <;>
    by_cases oox : connP (oddEdges G.edgeFinset m) o x
  · exact absurd ⟨oxy, ooy, oox⟩ hnotall
  · exact absurd (hnw_conn_trans_ox G m oxy ooy) oox
  · exact absurd (hnw_conn_trans_oy G m oxy oox) ooy
  · rw [hnw_switching G β J m hxy oxy A,
        hnw_mass_vanish G β J m hnd A hm hoy (fun h => ooy (coy.mpr h)),
        hnw_mass_vanish G β J m hnd A hm hox (fun h => oox (cox.mpr h))]
    ring
  · exact absurd (hnw_conn_trans_xy G m ooy oox) oxy
  · rw [hnw_switching G β J m hoy ooy A,
        hnw_mass_vanish G β J m hnd A hm hxy (fun h => oxy (cxy.mpr h)),
        hnw_mass_vanish G β J m hnd A hm hox (fun h => oox (cox.mpr h))]
    ring
  · rw [hnw_switching G β J m hox oox A,
        hnw_mass_vanish G β J m hnd A hm hxy (fun h => oxy (cxy.mpr h)),
        hnw_mass_vanish G β J m hnd A hm hoy (fun h => ooy (coy.mpr h))]
    ring
  · exact absurd ⟨fun h => oxy (cxy.mpr h), fun h => ooy (coy.mpr h),
      fun h => oox (cox.mpr h)⟩ hnotnone

/-! ## C. Inclusion–exclusion and the three-point inequality -/

open Classical in
/-- Inclusion–exclusion identity: summed over `M`, the gap equals the none-connected mass minus
twice the all-connected mass. Conditional on `hcoh`. -/
theorem hnw_inclusion_exclusion_decomp (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V))
    (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hcoh : ∀ m ∈ M, hnw_coherent G m o x y) :
    ∑ m ∈ M, hnw_gap G β J m A o x y
      = (∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m A)
        - 2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m A) := by
  rw [← Finset.sum_filter_add_sum_filter_not M (fun m => hnw_allConn G m o x y)
    (fun m => hnw_gap G β J m A o x y)]
  have hall : ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_gap G β J m A o x y
      = -2 * ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m A := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m hmem => ?_)
    rw [Finset.mem_filter] at hmem
    exact hnw_gap_allConn G β J m A hox hoy hxy hmem.2
  have hrest : ∑ m ∈ M.filter (fun m => ¬ hnw_allConn G m o x y), hnw_gap G β J m A o x y
      = ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m A := by
    rw [← Finset.sum_filter_add_sum_filter_not (M.filter (fun m => ¬ hnw_allConn G m o x y))
      (fun m => hnw_noneConn G m o x y) (fun m => hnw_gap G β J m A o x y)]
    have hfilt : (M.filter (fun m => ¬ hnw_allConn G m o x y)).filter
        (fun m => hnw_noneConn G m o x y) = M.filter (fun m => hnw_noneConn G m o x y) := by
      ext m
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hm0, _⟩, hn⟩; exact ⟨hm0, hn⟩
      · rintro ⟨hm0, hn⟩
        exact ⟨⟨hm0, hnw_noneConn_not_allConn G m hn⟩, hn⟩
    have h1 : ∑ m ∈ (M.filter (fun m => ¬ hnw_allConn G m o x y)).filter
          (fun m => hnw_noneConn G m o x y), hnw_gap G β J m A o x y
        = ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m A := by
      rw [hfilt]
      refine Finset.sum_congr rfl (fun m hmem => ?_)
      rw [Finset.mem_filter] at hmem
      exact hnw_gap_noneConn G β J m (hnd m hmem.1) A (hm m hmem.1) hox hoy hxy hmem.2
    have h2 : ∑ m ∈ (M.filter (fun m => ¬ hnw_allConn G m o x y)).filter
          (fun m => ¬ hnw_noneConn G m o x y), hnw_gap G β J m A o x y = 0 := by
      refine Finset.sum_eq_zero (fun m hmem => ?_)
      simp only [Finset.mem_filter] at hmem
      exact hnw_gap_exactlyOne G β J m (hnd m hmem.1.1) A (hm m hmem.1.1) hox hoy hxy
        (hcoh m hmem.1.1) hmem.1.2 hmem.2
    rw [h1, h2, add_zero]
  rw [hall, hrest]; ring

open Classical in
/-- The summed gap is nonnegative, conditional on `hcoh` and the domination inequality `hdom`. -/
lemma hnw_closure_of_hdom (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V))
    (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hcoh : ∀ m ∈ M, hnw_coherent G m o x y)
    (hdom : 2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m A)
      ≤ ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m A) :
    0 ≤ ∑ m ∈ M, hnw_gap G β J m A o x y := by
  rw [hnw_inclusion_exclusion_decomp G β J M hnd A hm hox hoy hxy hcoh]
  linarith

open Classical in
/-- **Three-point inequality** (GHS type) for split masses, conditional on `hcoh` and `hdom`:
`∑ mass(A ∆ {x,y}) + ∑ mass(A ∆ {o,y}) + ∑ mass(A ∆ {o,x}) ≤ ∑ mass(A)` over `M`. -/
theorem hnw_ghs_distinct_site_of_hdom (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V))
    (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hcoh : ∀ m ∈ M, hnw_coherent G m o x y)
    (hdom : 2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m A)
      ≤ ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m A) :
    (∑ m ∈ M, hnw_mass G β J m (A ∆ {x, y}))
      + (∑ m ∈ M, hnw_mass G β J m (A ∆ {o, y}))
      + (∑ m ∈ M, hnw_mass G β J m (A ∆ {o, x}))
      ≤ ∑ m ∈ M, hnw_mass G β J m A := by
  have hge := hnw_closure_of_hdom G β J M hnd A hm hox hoy hxy hcoh hdom
  unfold hnw_gap at hge
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hge
  linarith

/-! ## D. Adding a backbone -/

/-- The split mass is `w(m)` times a weighted count of sub-currents with sources `A`. -/
lemma hnw_mass_eq_weight_mul_count (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) (A : Finset V) :
    hnw_mass G β J m A
      = Sharpness.weight G β J m
        * ∑ K : {K : Current V // ∀ e, K e ≤ m e},
            (if Sharpness.sources G K.1 = A
              then (∏ e ∈ G.edgeFinset, (Nat.choose (m e) (K.1 e) : ℝ)) else 0) := by
  unfold hnw_mass
  rw [ising_two_point_switching G β J m 1 A, one_mul]

/-- In the all-connected pattern the three shifted masses equal `mass(A)`. -/
lemma hnw_allMass_eq_paired (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) (A : Finset V)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hall : hnw_allConn G m o x y) :
    hnw_mass G β J m (A ∆ {x, y}) = hnw_mass G β J m A
      ∧ hnw_mass G β J m (A ∆ {o, y}) = hnw_mass G β J m A
      ∧ hnw_mass G β J m (A ∆ {o, x}) = hnw_mass G β J m A := by
  obtain ⟨hxy', hoy', hox'⟩ := hall
  exact ⟨hnw_switching G β J m hxy hxy' A, hnw_switching G β J m hoy hoy' A,
    hnw_switching G β J m hox hox' A⟩

/-- For nonnegative `β` and couplings, `2 · mass(A) ≤ 0` iff `mass(A) = 0`. -/
lemma hnw_two_mul_mass_nonpos_iff (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (m : Current V) (A : Finset V) :
    (2 * hnw_mass G β J m A ≤ 0) ↔ hnw_mass G β J m A = 0 := by
  have hnn := hnw_mass_nonneg G β J hβ hJ m A
  constructor
  · intro h; linarith
  · intro h; rw [h]; norm_num

/-- The sources of the indicator current of `P ⊆ E` are the odd-degree sites of `P`. -/
lemma hnw_sources_indicator (P : Finset (Sym2 V)) (hP : P ⊆ G.edgeFinset) :
    Sharpness.sources G (fun e => if e ∈ P then 1 else 0) = srcP P := by
  ext z
  simp only [Sharpness.mem_sources, mem_srcP]
  have key : Sharpness.incidentFlux G (fun e => if e ∈ P then 1 else 0) z = degP P z := by
    unfold Sharpness.incidentFlux
    rw [degP_as_sum G.edgeFinset P hP z]
  rw [key]

/-- Adding the indicator of `P` to a current changes its sources by `srcP P`. -/
lemma hnw_addBackbone_sources (m : Current V) (P : Finset (Sym2 V)) (hP : P ⊆ G.edgeFinset) :
    Sharpness.sources G (fun e => m e + (if e ∈ P then 1 else 0))
      = Sharpness.sources G m ∆ srcP P := by
  rw [show (fun e => m e + (if e ∈ P then 1 else 0))
      = fun e => m e + (fun e => if e ∈ P then 1 else 0) e from rfl,
      Sharpness.sources_add, hnw_sources_indicator G P hP]

/-- Weight of the current `m + 1_P`: `w(m) ∏_{e ∈ P} βJ_e / (m_e + 1)`. -/
theorem hnw_addBackbone_weight (β : ℝ) (J : Sym2 V → ℝ) (m : Current V)
    (P : Finset (Sym2 V)) :
    Sharpness.weight G β J (fun e => m e + (if e ∈ P then 1 else 0))
      = Sharpness.weight G β J m
        * ∏ e ∈ G.edgeFinset, (if e ∈ P then (β * J e) / (m e + 1) else 1) := by
  unfold Sharpness.weight
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  by_cases h : e ∈ P
  · simp only [ite_eq_left h]
    rw [pow_succ]
    have hfac : (Nat.factorial (m e + 1) : ℝ) = (m e + 1) * Nat.factorial (m e) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hfac]
    have hfacne : (Nat.factorial (m e) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    field_simp
  · simp only [ite_eq_right h, add_zero, mul_one]

end Ising

end StatMech
