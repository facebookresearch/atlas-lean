/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.LatticePointBoundaryCubes
public import MathlibExt.Geometry.LatticePointEnumerator

/-!
# Lattice-point error bound and eventual asymptotics (ATLAS N385, final stage)

Source: `Atlas/NumberTheoryI/code/AnalyticClassNumber.lean`, lines 609--713
at revision `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`.

This module is the final N385 stage: the reusable error bound (source
`lattice_count_error_bound`, lines 658--673) and the eventual asymptotic
(source `lattice_point_count_asymptotics`, lines 675--713). It completes
N385. It does not cover N386 (change of basis, source lines 715 onward).

Source-to-API map (all within lines 609--713 above):
- source `lattice_count_upper_sandwich` (lines 609--631) and
  `lattice_count_lower_sandwich` (lines 633--656) stay private here as
  `LatticePointAsymptotics.count_upper_le` and
  `LatticePointAsymptotics.count_lower_le`;
- the source per-chart set in `hFinBdry` is reused from
  `LipschitzImageCubeCount.integerCubeSet`, not duplicated;
- source `outerCubeSet_finite` is reused from
  `LatticePointCubeSandwich.finite_outerCubeSet`, not duplicated;
- source `cube_measure_sandwich` is reused from
  `LatticePointCubeSandwich.cube_measure_sandwich`, not duplicated;
- source `boundary_cubes_bound` is reused from
  `LatticePointBoundaryCubes.card_outer_le_card_inner_add_sum`,
  not duplicated;
- source `single_lipschitz_image_cube_count` is reused from
  `LipschitzImageCubeCount.exists_cubeCount_le_const_mul_pow`,
  not duplicated;
- source `lattice_count_error_bound` (lines 658--673) becomes
  `LatticePointAsymptotics.lattice_point_count_error_bound`, stated through
  the canonical `LatticePointEnumerator.latticeEnumerator`;
- source `lattice_point_count_asymptotics` (lines 675--713) becomes
  `LatticePointAsymptotics.lattice_point_count_asymptotics`, stated through
  the canonical `LatticePointEnumerator.latticeEnumerator`;
- the two elementary inclusions (scaled lattice-point indices lie in
  `outerCubeSet S t`; `innerCubeSet S t` lies in the scaled lattice-point
  indices) stay private;
- the raw integer subtype is bridged to the canonical
  `LatticePointEnumerator.latticePointSet` by
  `LatticePointAsymptotics.rawSubtypeEquivCanonicalPointSet`, with cardinal
  equality in `LatticePointAsymptotics.card_raw_eq_latticeEnumerator`.

The source hypotheses `hn : 0 < n`, `MeasurableSet S`, and
`volume S ≠ ⊤` are dropped: the reused APIs support dimension zero, and
boundedness already gives finite volume. The error bound generalizes the
chart domain from source `n - 1` to an independent `d`.
-/

@[expose] public section

open LatticePointBoundaryCubes LatticePointCubeSandwich LipschitzImageCubeCount
open scoped Pointwise

namespace LatticePointAsymptotics

/-- Scaled lattice-point indices are outer cube indices. -/
private theorem count_subset_outerCubeSet {n : ℕ} (S : Set (Fin n → ℝ))
    (t : ℝ) :
    {x : Fin n → ℤ | (fun i => (x i : ℝ) / t) ∈ S} ⊆ outerCubeSet S t := by
  intro x hx
  rw [mem_outerCubeSet_iff]
  refine ⟨fun i => (x i : ℝ), ?_, hx⟩
  rw [mem_integerUnitCube_iff]
  intro i
  exact ⟨le_refl _, lt_add_one _⟩

/-- Inner cube indices are scaled lattice-point indices. -/
private theorem innerCubeSet_subset_count {n : ℕ} (S : Set (Fin n → ℝ))
    (t : ℝ) :
    innerCubeSet S t ⊆
      {x : Fin n → ℤ | (fun i => (x i : ℝ) / t) ∈ S} := by
  intro v hv
  rw [mem_innerCubeSet_iff] at hv
  have hmem : (fun i => ((v i : ℤ) : ℝ)) ∈ integerUnitCube v :=
    mem_integerUnitCube_iff.mpr fun i => ⟨le_refl _, lt_add_one _⟩
  exact hv _ hmem

/-- Private real upper bound: the scaled count is at most volume plus charts. -/
private theorem count_upper_le {n d numMaps : ℕ} (S : Set (Fin n → ℝ))
    (hS : Bornology.IsBounded S)
    (maps : Fin numMaps → (↥(unitCube d) → (Fin n → ℝ)))
    (hCover : frontier S ⊆ ⋃ i, Set.range (maps i)) {t : ℝ} (ht : 0 < t)
    (hFinMaps : ∀ i, (integerCubeSet (maps i) t).Finite) :
    (Nat.card {x : Fin n → ℤ | (fun i => (x i : ℝ) / t) ∈ S} : ℝ) ≤
      (MeasureTheory.volume S).toReal * t ^ n +
        ∑ i, (Nat.card (integerCubeSet (maps i) t) : ℝ) := by
  have hfinOuter : (outerCubeSet S t).Finite := finite_outerCubeSet S hS ht
  have hSub : {x : Fin n → ℤ | (fun i => (x i : ℝ) / t) ∈ S} ⊆
      outerCubeSet S t :=
    count_subset_outerCubeSet S t
  have hCountR : (Nat.card {x : Fin n → ℤ | (fun i => (x i : ℝ) / t) ∈ S} : ℝ) ≤
      (Nat.card (outerCubeSet S t) : ℝ) := by
    have h := Set.ncard_le_ncard hSub hfinOuter
    simp only [← Nat.card_coe_set_eq] at h
    exact_mod_cast h
  have hCardR : (Nat.card (outerCubeSet S t) : ℝ) ≤
      (Nat.card (innerCubeSet S t) : ℝ) +
        ∑ i, (Nat.card (integerCubeSet (maps i) t) : ℝ) := by
    exact_mod_cast
      card_outer_le_card_inner_add_sum S maps hCover hfinOuter hFinMaps
  have hInnerLe : (Nat.card (innerCubeSet S t) : ℝ) ≤
      (MeasureTheory.volume S).toReal * t ^ n :=
    (cube_measure_sandwich S hS ht).1
  linarith

/-- Private real lower bound: volume is at most the scaled count plus charts. -/
private theorem count_lower_le {n d numMaps : ℕ} (S : Set (Fin n → ℝ))
    (hS : Bornology.IsBounded S)
    (maps : Fin numMaps → (↥(unitCube d) → (Fin n → ℝ)))
    (hCover : frontier S ⊆ ⋃ i, Set.range (maps i)) {t : ℝ} (ht : 0 < t)
    (hFinMaps : ∀ i, (integerCubeSet (maps i) t).Finite) :
    (MeasureTheory.volume S).toReal * t ^ n ≤
      (Nat.card {x : Fin n → ℤ | (fun i => (x i : ℝ) / t) ∈ S} : ℝ) +
        ∑ i, (Nat.card (integerCubeSet (maps i) t) : ℝ) := by
  have hfinOuter : (outerCubeSet S t).Finite := finite_outerCubeSet S hS ht
  have hfinCount : {x : Fin n → ℤ | (fun i => (x i : ℝ) / t) ∈ S}.Finite :=
    hfinOuter.subset (count_subset_outerCubeSet S t)
  have hInnerR : (Nat.card (innerCubeSet S t) : ℝ) ≤
      (Nat.card {x : Fin n → ℤ | (fun i => (x i : ℝ) / t) ∈ S} : ℝ) := by
    have h := Set.ncard_le_ncard (innerCubeSet_subset_count S t) hfinCount
    simp only [← Nat.card_coe_set_eq] at h
    exact_mod_cast h
  have hCardR : (Nat.card (outerCubeSet S t) : ℝ) ≤
      (Nat.card (innerCubeSet S t) : ℝ) +
        ∑ i, (Nat.card (integerCubeSet (maps i) t) : ℝ) := by
    exact_mod_cast
      card_outer_le_card_inner_add_sum S maps hCover hfinOuter hFinMaps
  have hVolLe : (MeasureTheory.volume S).toReal * t ^ n ≤
      (Nat.card (outerCubeSet S t) : ℝ) :=
    (cube_measure_sandwich S hS ht).2
  linarith

/-- **Integer points of a dilate.** Let $S \subseteq \mathbb{R}^n$ and $t > 0$. Viewing an
integer vector as a real vector gives a bijection from the set of $x \in \mathbb{Z}^n$ with
$x / t \in S$ onto the lattice point set $tS \cap \mathbb{Z}^n$. -/
noncomputable def rawSubtypeEquivCanonicalPointSet {n : ℕ}
    (S : Set (Fin n → ℝ)) {t : ℝ} (ht : 0 < t) :
    {x : Fin n → ℤ | (fun i => (x i : ℝ) / t) ∈ S} ≃
      ↥(LatticePointEnumerator.latticePointSet n S t) :=
  Equiv.ofBijective
    (fun x => ⟨fun i => ((x.val i : ℤ) : ℝ), by
      have htne : t ≠ 0 := ht.ne'
      have hmemDil : (fun i => ((x.val i : ℤ) : ℝ)) ∈ t • S :=
        ⟨(fun i => ((x.val i : ℤ) : ℝ) / t), x.property, by
          funext i
          simp only [Pi.smul_apply, smul_eq_mul]
          exact mul_div_cancel₀ _ htne⟩
      have hmemLat : (fun i => ((x.val i : ℤ) : ℝ)) ∈
          LatticePointEnumerator.stdLattice n := by
        show _ ∈ LatticePointEnumerator.stdLattice n
        rw [LatticePointEnumerator.mem_stdLattice_iff]
        exact fun i => ⟨x.val i, rfl⟩
      exact ⟨hmemDil, hmemLat⟩⟩)
    ⟨by
      intro a b hab
      apply Subtype.ext
      funext i
      have h := congrArg Subtype.val hab
      have hi : ((a.val i : ℤ) : ℝ) = ((b.val i : ℤ) : ℝ) := congrFun h i
      exact Int.cast_injective hi,
    by
      intro y
      obtain ⟨hmemDil, hmemLat⟩ := y.property
      have hInt' : ∀ i, ∃ z : ℤ, (z : ℝ) = y.val i := by
        show ∀ i, ∃ z : ℤ, (z : ℝ) = y.val i
        exact LatticePointEnumerator.mem_stdLattice_iff.mp hmemLat
      choose z hz using hInt'
      have htne : t ≠ 0 := ht.ne'
      obtain ⟨s, hsS, hsEq⟩ := hmemDil
      have hmem : (fun i => ((z i : ℤ) : ℝ) / t) ∈ S := by
        have hEq : (fun i => ((z i : ℤ) : ℝ) / t) = s := by
          funext i
          have hyi : y.val i = t * s i := by
            have h := congrFun hsEq i
            simp only [Pi.smul_apply, smul_eq_mul] at h
            rw [h]
          rw [hz i, hyi]
          field_simp
        rw [hEq]
        exact hsS
      refine ⟨⟨z, hmem⟩, ?_⟩
      apply Subtype.ext
      funext i
      change ((z i : ℤ) : ℝ) = y.val i
      exact hz i⟩

/-- **Integer count of a dilate.** Let $S \subseteq \mathbb{R}^n$ and $t > 0$. The number of
integer vectors $x \in \mathbb{Z}^n$ with $x / t \in S$ equals the lattice enumerator of $S$ at
$t$, the number of points of $\mathbb{Z}^n$ in the dilate $tS$; here an infinite set is counted
as $0$. -/
theorem card_raw_eq_latticeEnumerator {n : ℕ} (S : Set (Fin n → ℝ))
    {t : ℝ} (ht : 0 < t) :
    Nat.card {x : Fin n → ℤ | (fun i => (x i : ℝ) / t) ∈ S} =
      LatticePointEnumerator.latticeEnumerator n S t := by
  unfold LatticePointEnumerator.latticeEnumerator
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr (rawSubtypeEquivCanonicalPointSet S ht)

/-- **Lattice-point error bound from boundary charts.** Let $S \subseteq \mathbb{R}^n$ be
bounded, let $f_1, \dots, f_m$ be maps from the unit cube $[0,1]^d$ to $\mathbb{R}^n$ whose
ranges cover the boundary $\partial S$, and let $t > 0$. For each $i$, let $N_i(t)$ be the number
of $v \in \mathbb{Z}^n$ such that $t f_i(y)$ lies in the half-open cube $\prod_j [v_j, v_j + 1)$
for some $y \in [0,1]^d$, and assume each of these sets of $v$ is finite. Then the lattice
enumerator $L_S(t)$, the number of points of $\mathbb{Z}^n$ in $tS$, satisfies
$|L_S(t) - \operatorname{vol}(S)\, t^n| \le N_1(t) + \dots + N_m(t)$, where $\operatorname{vol}$
is Lebesgue (outer) measure. -/
theorem lattice_point_count_error_bound
    {n d numMaps : ℕ} (S : Set (Fin n → ℝ))
    (hS : Bornology.IsBounded S)
    (maps : Fin numMaps → (↥(unitCube d) → (Fin n → ℝ)))
    (hCover : frontier S ⊆ ⋃ i, Set.range (maps i))
    {t : ℝ} (ht : 0 < t)
    (hFinMaps : ∀ i, (integerCubeSet (maps i) t).Finite) :
    ‖(LatticePointEnumerator.latticeEnumerator n S t : ℝ) -
      (MeasureTheory.volume S).toReal * t ^ n‖ ≤
      ∑ i, (Nat.card (integerCubeSet (maps i) t) : ℝ) := by
  have hCard : (LatticePointEnumerator.latticeEnumerator n S t : ℝ) =
      (Nat.card {x : Fin n → ℤ | (fun i => (x i : ℝ) / t) ∈ S} : ℝ) := by
    rw [card_raw_eq_latticeEnumerator S ht]
  rw [hCard]
  have hUpper := count_upper_le S hS maps hCover ht hFinMaps
  have hLower := count_lower_le S hS maps hCover ht hFinMaps
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- **Lattice-point count of a dilate with boundary error.** Let $S \subseteq \mathbb{R}^n$ be
bounded, and suppose its boundary $\partial S$ is $(n-1)$-Lipschitz parametrizable: it is the
union of the ranges of finitely many Lipschitz maps from the unit cube $[0,1]^{n-1}$, where
$n - 1$ is read as $0$ when $n = 0$. Then there is a real constant $C$ such that for all
sufficiently large real $t$, the lattice enumerator $L_S(t)$, the number of points of
$\mathbb{Z}^n$ in $tS$, satisfies $|L_S(t) - \operatorname{vol}(S)\, t^n| \le C\, t^{n-1}$, where
$\operatorname{vol}$ is Lebesgue (outer) measure. -/
theorem lattice_point_count_asymptotics
    {n : ℕ} (S : Set (Fin n → ℝ))
    (hS : Bornology.IsBounded S)
    (hS_bdry : IsLipschitzParametrizable (n - 1) (frontier S)) :
    ∃ C : ℝ, ∀ᶠ t in Filter.atTop,
      ‖(LatticePointEnumerator.latticeEnumerator n S t : ℝ) -
        (MeasureTheory.volume S).toReal * t ^ n‖ ≤ C * t ^ (n - 1) := by
  obtain ⟨numMaps, maps, hLip, hEq⟩ := hS_bdry
  have hCover : frontier S ⊆ ⋃ i, Set.range (maps i) := hEq.le
  have cube_bounds : ∀ i : Fin numMaps, ∃ Ci : ℝ, 0 < Ci ∧ ∀ t : ℝ, 1 ≤ t →
      (Nat.card (integerCubeSet (maps i) t) : ℝ) ≤ Ci * t ^ (n - 1) := by
    intro i
    obtain ⟨Ki, hKi⟩ := hLip i
    exact exists_cubeCount_le_const_mul_pow (maps i) Ki hKi
  choose Cs _hCpos hCs using cube_bounds
  refine ⟨∑ i, Cs i, ?_⟩
  apply Filter.eventually_atTop.mpr
  refine ⟨1, fun t ht => ?_⟩
  have ht_pos : 0 < t := by linarith
  have hFinMaps : ∀ i, (integerCubeSet (maps i) t).Finite := by
    intro i
    obtain ⟨Ki, hKi⟩ := hLip i
    exact finite_integerCubeSet (maps i) Ki hKi t ht
  calc ‖(LatticePointEnumerator.latticeEnumerator n S t : ℝ) -
          (MeasureTheory.volume S).toReal * t ^ n‖
        ≤ ∑ i, (Nat.card (integerCubeSet (maps i) t) : ℝ) :=
          lattice_point_count_error_bound S hS maps hCover ht_pos hFinMaps
      _ ≤ ∑ i, Cs i * t ^ (n - 1) :=
          Finset.sum_le_sum fun i _ => hCs i t ht
      _ = (∑ i, Cs i) * t ^ (n - 1) := by rw [Finset.sum_mul]

end LatticePointAsymptotics
