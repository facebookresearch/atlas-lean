/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Bounded cubical measure sandwich (ATLAS N385, prerequisite Stage A only)

Source: [AnalyticClassNumber.lean (lines 313--464 at
  revision `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`)](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/AnalyticClassNumber.lean#L313-L464).

This module ports only the bounded cubical sandwich prerequisite: the half-open
integer unit cube, the outer and inner lattice-cube index sets, finiteness of
the outer set for bounded sets at positive scales, and the measure/cardinality
sandwich. It excludes the boundary estimate, the final asymptotic, and N386.

Declaration-to-source mapping (all within lines 313--464 above):
- `LatticePointCubeSandwich.integerUnitCube`: half-open integer unit cube.
- `LatticePointCubeSandwich.mem_integerUnitCube_iff`: unfolding lemma.
- `LatticePointCubeSandwich.outerCubeSet`: outer lattice-cube index set.
- `LatticePointCubeSandwich.mem_outerCubeSet_iff`: unfolding lemma.
- `LatticePointCubeSandwich.innerCubeSet`: inner lattice-cube index set.
- `LatticePointCubeSandwich.mem_innerCubeSet_iff`: unfolding lemma.
- `LatticePointCubeSandwich.innerCubeSet_subset_outerCubeSet`: inner indices are outer indices.
- `LatticePointCubeSandwich.finite_outerCubeSet`: finiteness of the outer set for
  bounded sets at positive scales.
- `LatticePointCubeSandwich.cube_measure_sandwich`: measure/cardinality sandwich.
-/

@[expose] public section

open MeasureTheory Set ENNReal Pointwise

namespace LatticePointCubeSandwich

/-- **Integer unit cube.** For $v \in \mathbb{Z}^n$, the integer unit cube at $v$ is the half-open
cube $Q_v = \prod_i [v_i, v_i + 1) \subseteq \mathbb{R}^n$, the set of $x \in \mathbb{R}^n$ with
$v_i \le x_i < v_i + 1$ for every coordinate $i$. -/
noncomputable def integerUnitCube {n : ℕ} (v : Fin n → ℤ) :
    Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun i => Set.Ico (v i : ℝ) ((v i : ℝ) + 1))

/-- **Membership in an integer unit cube.** For $v \in \mathbb{Z}^n$ and $x \in \mathbb{R}^n$, $x$
lies in the integer unit cube at $v$ if and only if $v_i \le x_i < v_i + 1$ for every
coordinate $i$. -/
@[simp] theorem mem_integerUnitCube_iff {n : ℕ} {v : Fin n → ℤ}
    {x : Fin n → ℝ} :
    x ∈ integerUnitCube v ↔ ∀ i, (v i : ℝ) ≤ x i ∧ x i < (v i : ℝ) + 1 := by
  simp only [integerUnitCube, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_Ico]

/-- **Outer cube set.** For a set $S \subseteq \mathbb{R}^n$ and a real number $t$, the outer cube
set of $S$ at scale $t$ is the set of $v \in \mathbb{Z}^n$ such that
$(x_1/t, \dots, x_n/t) \in S$ for some $x$ in the integer unit cube
$Q_v = \prod_i [v_i, v_i + 1)$. For $t > 0$ these are the $v$ with $Q_v$ meeting $tS$; for $t = 0$
the division is read as $x_i/0 = 0$. -/
def outerCubeSet {n : ℕ} (S : Set (Fin n → ℝ)) (t : ℝ) :
    Set (Fin n → ℤ) :=
  {v | ∃ x ∈ integerUnitCube v, (fun i => x i / t) ∈ S}

/-- **Membership in the outer cube set.** For $S \subseteq \mathbb{R}^n$, $t \in \mathbb{R}$ and
$v \in \mathbb{Z}^n$, $v$ belongs to the outer cube set of $S$ at scale $t$ if and only if
$(x_1/t, \dots, x_n/t) \in S$ for some $x$ in the integer unit cube at $v$. -/
@[simp] theorem mem_outerCubeSet_iff {n : ℕ} {S : Set (Fin n → ℝ)} {t : ℝ}
    {v : Fin n → ℤ} :
    v ∈ outerCubeSet S t ↔ ∃ x ∈ integerUnitCube v, (fun i => x i / t) ∈ S :=
  Iff.rfl

/-- **Inner cube set.** For a set $S \subseteq \mathbb{R}^n$ and a real number $t$, the inner cube
set of $S$ at scale $t$ is the set of $v \in \mathbb{Z}^n$ such that
$(x_1/t, \dots, x_n/t) \in S$ for every $x$ in the integer unit cube
$Q_v = \prod_i [v_i, v_i + 1)$. For $t > 0$ these are the $v$ with $Q_v \subseteq tS$; for $t = 0$
the division is read as $x_i/0 = 0$. -/
def innerCubeSet {n : ℕ} (S : Set (Fin n → ℝ)) (t : ℝ) :
    Set (Fin n → ℤ) :=
  {v | ∀ x ∈ integerUnitCube v, (fun i => x i / t) ∈ S}

/-- **Membership in the inner cube set.** For $S \subseteq \mathbb{R}^n$, $t \in \mathbb{R}$ and
$v \in \mathbb{Z}^n$, $v$ belongs to the inner cube set of $S$ at scale $t$ if and only if
$(x_1/t, \dots, x_n/t) \in S$ for every $x$ in the integer unit cube at $v$. -/
@[simp] theorem mem_innerCubeSet_iff {n : ℕ} {S : Set (Fin n → ℝ)} {t : ℝ}
    {v : Fin n → ℤ} :
    v ∈ innerCubeSet S t ↔ ∀ x ∈ integerUnitCube v, (fun i => x i / t) ∈ S :=
  Iff.rfl

/-- **Inner cube indices are outer cube indices.** For every set $S \subseteq \mathbb{R}^n$ and
every real $t$, the inner cube set of $S$ at scale $t$ is contained in the outer cube set of $S$
at scale $t$. -/
theorem innerCubeSet_subset_outerCubeSet {n : ℕ} (S : Set (Fin n → ℝ))
    (t : ℝ) : innerCubeSet S t ⊆ outerCubeSet S t := by
  intro v hv
  rw [mem_innerCubeSet_iff] at hv
  rw [mem_outerCubeSet_iff]
  have hmem : (fun i => ((v i : ℤ) : ℝ)) ∈ integerUnitCube v := by
    rw [mem_integerUnitCube_iff]
    intro i
    exact ⟨le_refl _, by linarith⟩
  exact ⟨_, hmem, hv _ hmem⟩

/-- **Finiteness of the outer cube set.** If $S \subseteq \mathbb{R}^n$ is bounded and $t > 0$,
then the outer cube set of $S$ at scale $t$, the set of $v \in \mathbb{Z}^n$ whose integer unit
cube $\prod_i [v_i, v_i + 1)$ meets $tS$, is finite. -/
theorem finite_outerCubeSet {n : ℕ} (S : Set (Fin n → ℝ))
    (hS : Bornology.IsBounded S) {t : ℝ} (ht : 0 < t) :
    (outerCubeSet S t).Finite := by
  rw [isBounded_iff_forall_norm_le] at hS
  obtain ⟨R, hR⟩ := hS
  set B := ⌈R * t + 1⌉ with hB_def
  apply Set.Finite.subset (Set.Finite.pi (fun _ => Set.finite_Icc (-B) B))
  intro v hv
  rw [mem_outerCubeSet_iff] at hv
  obtain ⟨x, hxv, hx_mem⟩ := hv
  rw [mem_integerUnitCube_iff] at hxv
  simp only [mem_univ_pi, mem_Icc]
  intro i
  have hxt : ‖(fun j => x j / t)‖ ≤ R := hR _ hx_mem
  have hxi_t : |x i / t| ≤ R :=
    (norm_le_pi_norm (fun j => x j / t) i).trans hxt
  have hxi : |x i| ≤ R * t := by
    rwa [abs_div, div_le_iff₀ (abs_pos.mpr ht.ne'), abs_of_pos ht] at hxi_t
  obtain ⟨hlo, _hhi⟩ := hxv i
  have hxi_hi : x i ≤ R * t := (abs_le.mp hxi).2
  constructor
  · suffices h : -B < v i + 1 by omega
    suffices h : ((-B : ℤ) : ℝ) < (((v i + 1 : ℤ)) : ℝ) by
      exact_mod_cast h
    push_cast
    calc (-(⌈R * t + 1⌉ : ℤ) : ℝ) ≤ -(R * t + 1) := by
            linarith [Int.le_ceil (R * t + 1)]
      _ < (v i : ℝ) + 1 := by linarith [neg_le_of_abs_le hxi]
  · suffices h : (v i : ℤ) < B + 1 by omega
    suffices h : (((v i : ℤ)) : ℝ) < (((B + 1 : ℤ)) : ℝ) by
      exact_mod_cast h
    push_cast
    calc (v i : ℝ) ≤ x i := hlo
      _ ≤ R * t := hxi_hi
      _ < R * t + 1 := by linarith
      _ ≤ (⌈R * t + 1⌉ : ℤ) := Int.le_ceil _
      _ < (⌈R * t + 1⌉ : ℤ) + 1 := by linarith

/-- **Cubical measure sandwich.** Let $S \subseteq \mathbb{R}^n$ be bounded, let $t > 0$, and let
$\mathrm{vol}(S)$ be the Lebesgue (outer) measure of $S$, which is finite. For
$v \in \mathbb{Z}^n$ let $Q_v = \prod_i [v_i, v_i + 1)$. Let $I$ be the inner cube set of $S$ at
scale $t$, the $v$ with $Q_v \subseteq tS$, and $O$ the outer cube set, the $v$ with $Q_v$
meeting $tS$. Then $|I| \le \mathrm{vol}(S)\, t^n \le |O|$. -/
theorem cube_measure_sandwich {n : ℕ} (S : Set (Fin n → ℝ))
    (hS : Bornology.IsBounded S) {t : ℝ} (ht : 0 < t) :
    (Nat.card (innerCubeSet S t) : ℝ) ≤ (volume S).toReal * t ^ n ∧
      (volume S).toReal * t ^ n ≤ (Nat.card (outerCubeSet S t) : ℝ) := by
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have hS_vol : volume S ≠ ⊤ := ne_of_lt hS.measure_lt_top
  have hfin_outer : (outerCubeSet S t).Finite :=
    finite_outerCubeSet S hS ht
  have inner_sub_outer : innerCubeSet S t ⊆ outerCubeSet S t :=
    innerCubeSet_subset_outerCubeSet S t
  have hfin_inner := hfin_outer.subset inner_sub_outer
  have vol_cube : ∀ v : Fin n → ℤ, volume (integerUnitCube v) = 1 := by
    intro v
    simp only [integerUnitCube, Real.volume_pi_Ico, add_sub_cancel_left]
    simp [ENNReal.ofReal_one]
  have meas_cube : ∀ v : Fin n → ℤ,
      MeasurableSet (integerUnitCube v) :=
    fun v => MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ico)
  have pd_all : Set.PairwiseDisjoint (Set.univ : Set (Fin n → ℤ))
      integerUnitCube := by
    intro v _ w _ hvw
    simp only [Function.onFun, Set.disjoint_left, mem_integerUnitCube_iff]
    intro x hxv hxw
    apply hvw
    funext i
    have hvi := (hxv i).1
    have hvi2 := (hxv i).2
    have hwi := (hxw i).1
    have hwi2 := (hxw i).2
    have : (v i : ℤ) = w i := by
      by_contra h
      rcases lt_or_gt_of_ne h with h' | h'
      · have : (v i : ℝ) + 1 ≤ (w i : ℝ) := by exact_mod_cast h'
        linarith
      · have : (w i : ℝ) + 1 ≤ (v i : ℝ) := by exact_mod_cast h'
        linarith
    exact_mod_cast this
  have vol_scaled : volume {x : Fin n → ℝ | (fun i => x i / t) ∈ S} =
      ENNReal.ofReal (t ^ n) * volume S := by
    have : {x : Fin n → ℝ | (fun i => x i / t) ∈ S} = t • S := by
      ext x
      simp only [mem_ofPred_eq, Set.mem_smul_set_iff_inv_smul_mem₀ ht_ne]
      suffices (fun i => x i / t) = t⁻¹ • x by rw [this]
      ext i
      simp [Pi.smul_apply, smul_eq_mul, inv_mul_eq_div]
    rw [this, Measure.addHaar_smul volume t S]
    congr 1
    rw [Module.finrank_pi_fintype]
    simp [Module.finrank_self, abs_of_pos (pow_pos ht n)]
  have measure_cubes : ∀ (T : Set (Fin n → ℤ)), T.Finite →
      volume (⋃ v ∈ T, integerUnitCube v) = (Nat.card T : ENNReal) := by
    intro T hT
    let _ : Fintype ↥T := hT.fintype
    rw [measure_biUnion hT.countable
      (fun i hi j hj hij => pd_all (mem_univ i) (mem_univ j) hij)
      (fun v _ => meas_cube v)]
    conv_lhs => arg 1; ext v; rw [vol_cube v.val]
    cases nonempty_fintype T
    simp [mul_one, Nat.card_eq_fintype_card]
  have h_left_ennreal : (Nat.card (innerCubeSet S t) : ENNReal) ≤
      ENNReal.ofReal (t ^ n) * volume S := by
    rw [← measure_cubes _ hfin_inner, ← vol_scaled]
    apply measure_mono
    intro x hx
    simp only [mem_iUnion, exists_prop] at hx
    obtain ⟨v, hv, hxv⟩ := hx
    exact (mem_innerCubeSet_iff.mp hv) x hxv
  have left_ineq :
      (Nat.card (innerCubeSet S t) : ℝ) ≤ (volume S).toReal * t ^ n := by
    have h := (ENNReal.toReal_le_toReal (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS_vol)).mpr h_left_ennreal
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ t ^ n),
      ENNReal.toReal_natCast] at h
    linarith
  have h_right_ennreal : ENNReal.ofReal (t ^ n) * volume S ≤
      (Nat.card (outerCubeSet S t) : ENNReal) := by
    rw [← vol_scaled, ← measure_cubes _ hfin_outer]
    apply measure_mono
    intro x hx
    simp only [mem_iUnion, exists_prop]
    exact ⟨fun i => ⌊x i⌋,
      mem_outerCubeSet_iff.mpr ⟨x,
        mem_integerUnitCube_iff.mpr (fun i =>
          ⟨Int.floor_le (x i), Int.lt_floor_add_one (x i)⟩), hx⟩,
      mem_integerUnitCube_iff.mpr (fun i =>
        ⟨Int.floor_le (x i), Int.lt_floor_add_one (x i)⟩)⟩
  have right_ineq :
      (volume S).toReal * t ^ n ≤ (Nat.card (outerCubeSet S t) : ℝ) := by
    have h := (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS_vol)
      (ENNReal.natCast_ne_top _)).mpr h_right_ennreal
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ t ^ n),
      ENNReal.toReal_natCast] at h
    linarith
  exact ⟨left_ineq, right_ineq⟩

end LatticePointCubeSandwich
