/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.MetricSpace.PiNat

/-!
# Connected metric groups need not be arcwise connected

The ternary solenoid refutes part (2) of Scottish Book Problem 160.
Its real winding is dense, but no path joins the identity to the constant sequence at `-1`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.ScottishBook160Part2Wanted

/-- **Connectedness in the sense of Hausdorff.** A topological space $G$ is connected in the
sense of Hausdorff when it is not the union of two disjoint nonempty closed subsets.

The empty space satisfies this condition. -/
def IsHausdorffConnected (G : Type*) [TopologicalSpace G] : Prop :=
  ¬ ∃ (A B : Set G), IsClosed A ∧ IsClosed B ∧ A.Nonempty ∧ B.Nonempty ∧
    Disjoint A B ∧ A ∪ B = Set.univ

/-- **Arcwise connected space.** A topological space $G$ is arcwise connected when for any two
points $x, y \in G$ there is a continuous map $\gamma \colon \mathbb{R} \to G$ with
$\gamma(0) = x$ and $\gamma(1) = y$.

Restricting $\gamma$ to $[0, 1]$ gives a path from $x$ to $y$, and every such path extends
to $\mathbb{R}$, so this says that any two points are joined by a path; the path need not be
injective. -/
def IsArcwiseConnected (G : Type*) [TopologicalSpace G] : Prop :=
  ∀ x y : G, ∃ γ : ℝ → G, Continuous γ ∧ γ 0 = x ∧ γ 1 = y

/-- **Claim of Scottish Book Problem 160, part (2).** The claim that every metric group $G$
(a group with a metric for which multiplication and inversion are continuous) that is
connected in the sense of Hausdorff is arcwise connected. -/
def ScottishBookProblem160Part2Claim : Prop :=
  ∀ (G : Type*) [MetricSpace G] [Group G] [IsTopologicalGroup G],
    IsHausdorffConnected G → IsArcwiseConnected G

open Set Filter Topology
open scoped unitInterval

-- The inverse limit of circles under cubing, with coordinatewise group operations.
private def solenoid : Subgroup (ℕ → Circle) where
  carrier := {x | ∀ n, x (n + 1) ^ 3 = x n}
  one_mem' := by simp
  mul_mem' {x y} hx hy n := by simp [Pi.mul_apply, mul_pow, hx n, hy n]
  inv_mem' {x} hx n := by simp [Pi.inv_apply, inv_pow, hx n]

private lemma coord_pow (x : solenoid) (n k : ℕ) :
    x.val (n + k) ^ (3 ^ k : ℕ) = x.val n := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_mul, Nat.add_succ, x.property (n + k), ih]

private noncomputable def winding (t : ℝ) : solenoid :=
  ⟨fun n ↦ Circle.exp (t / 3 ^ n), fun n ↦ by
    rw [← Circle.exp_natCast_mul]
    congr 1
    push_cast
    rw [pow_succ]
    field_simp⟩

private lemma continuous_winding : Continuous winding :=
  Continuous.subtype_mk (continuous_pi fun _ ↦ Circle.exp.continuous.comp
    (continuous_id.div_const _)) _

-- Matching the nth coordinate also matches every earlier coordinate.
private lemma denseRange_winding : DenseRange winding := by
  intro x
  let t (k : ℕ) := (3 : ℝ) ^ k * (x.val k : ℂ).arg
  refine mem_closure_of_tendsto (f := fun k ↦ winding (t k)) (b := atTop) ?_
    (Eventually.of_forall fun k ↦ mem_range_self (t k))
  apply tendsto_subtype_rng.mpr
  refine tendsto_pi_nhds.mpr fun n ↦ tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop n] with k hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  change x.val n = Circle.exp (_ / _)
  rw [← coord_pow x n j, ← Circle.exp_arg (x.val (n + j)), ← Circle.exp_natCast_mul]
  congr 1
  dsimp [t]
  push_cast
  rw [pow_add]
  field_simp

private noncomputable def antipode : solenoid :=
  ⟨fun _ ↦ -1, fun _ ↦ Circle.ext (by norm_num)⟩

-- Lift coordinate zero to an angle. Uniqueness for the power coverings then fixes
-- every coordinate of the path as the winding of that angle.
private lemma antipode_unreachable (γ : ℝ → solenoid) (hγ : Continuous γ) (h₀ : γ 0 = 1)
    (h₁ : γ 1 = antipode) : False := by
  let p (n : ℕ) : C(I, Circle) :=
    ⟨fun t ↦ (γ t).val n, (continuous_apply n).comp
      (continuous_subtype_val.comp (hγ.comp continuous_subtype_val))⟩
  have hp (n : ℕ) : p n 0 = 1 := by
    change (γ 0).val n = 1
    rw [h₀]
    rfl
  obtain ⟨a, ha, ha₀⟩ := Circle.isCoveringMap_exp.exists_path_lifts (p 0) 0
    ((hp 0).trans Circle.exp_zero.symm)
  have heq (n : ℕ) : (fun t : I ↦ (winding (a t)).val n) = p n := by
    refine (Circle.isQuotientCoveringMap_npow (3 ^ n)).isCoveringMap.eq_of_comp_eq
      ((continuous_apply n).comp (continuous_subtype_val.comp
        (continuous_winding.comp a.continuous))) (p n).continuous ?_ 0 ?_
    · funext t
      change (winding (a t)).val n ^ (3 ^ n : ℕ) = (γ t).val n ^ (3 ^ n : ℕ)
      have hw := coord_pow (winding (a t)) 0 n
      have hγt := coord_pow (γ t) 0 n
      simp only [Nat.zero_add] at hw hγt
      rw [hw, hγt]
      simpa [winding, p] using congrFun ha t
    · change Circle.exp (a 0 / 3 ^ n) = p n 0
      simp [ha₀, hp]
  have hend (n : ℕ) : Circle.exp (a 1 / 3 ^ n) = -1 := by
    have h := congrFun (heq n) 1
    change Circle.exp (a 1 / 3 ^ n) = (γ 1).val n at h
    rwa [h₁] at h
  have hlim : Tendsto (fun n : ℕ ↦ a 1 / (3 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have h := (Circle.exp.continuous.tendsto 0).comp hlim
  simp only [Function.comp_def, hend, Circle.exp_zero] at h
  exact Circle.neg_ne_self 1 (tendsto_nhds_unique tendsto_const_nhds h)

private lemma hausdorffConnected_of_preconnected (G : Type*) [TopologicalSpace G]
    [PreconnectedSpace G] : IsHausdorffConnected G := by
  rintro ⟨A, B, hA, hB, hAn, hBn, hd, hu⟩
  have h := isPreconnected_closed_iff.mp (isPreconnected_univ (α := G)) A B hA hB
    hu.ge (by simpa using hAn) (by simpa using hBn)
  simp [hd.inter_eq] at h

/--
**Connected metric groups need not be arcwise connected.** The claim of part (2) of Scottish
Book Problem 160 is false: there is a metric group $G$ (a group with a metric for which
multiplication and inversion are continuous) that is connected in the sense of Hausdorff but
not arcwise connected, that is, there are points $x, y \in G$ such that no continuous map
$\gamma \colon \mathbb{R} \to G$ has $\gamma(0) = x$ and $\gamma(1) = y$.

The $p$-adic solenoid, the inverse limit of circles under $z \mapsto z^p$, is such a group:
it is a compact connected metrizable topological group that is not path connected.

Source: Encyclopedia of Mathematics, "Solenoid" (inverse-limit
construction with `fᵢ (z) = z ^ nᵢ`, a topological group, a
one-dimensional continuum); E. Hewitt and K. A. Ross, Abstract Harmonic
Analysis I (1979), cited there; solenoids are compact metrizable
spaces that are connected but not path connected.
-/
theorem scottishBook160Part2_refuted : ¬ ScottishBookProblem160Part2Claim := by
  intro claim
  let : MetricSpace (ℕ → Circle) := PiCountable.metricSpace
  have : PreconnectedSpace solenoid := denseRange_winding.preconnectedSpace continuous_winding
  obtain ⟨γ, hγ, h₀, h₁⟩ := claim (ULift solenoid) (by
    have := Homeomorph.ulift.symm.surjective.denseRange.preconnectedSpace
      (continuous_uliftUp (X := solenoid))
    exact hausdorffConnected_of_preconnected _) (ULift.up 1) (ULift.up antipode)
  exact antipode_unreachable (ULift.down ∘ γ) (continuous_uliftDown.comp hγ)
    (congrArg ULift.down h₀) (congrArg ULift.down h₁)

end MathlibExt.GroupTheory.ScottishBook160Part2Wanted
