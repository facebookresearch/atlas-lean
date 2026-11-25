/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.TotalDualIntegrality
public import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# The Edmonds-Giles theorem

Every extreme point of a rational totally dual integral system with integral right-hand side
has integral coordinates.
-/

public section

namespace MathlibExt.Analysis.Convex.EdmondsGilesWanted

open MathlibExt.Analysis.Convex.TotalDualIntegrality Matrix
open Filter Topology

/-- A direction annihilated by every tight row at a vertex must vanish: small perturbations
in both directions preserve all the inequalities. -/
private theorem eq_zero_of_tight_rows {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {b : Fin m → ℝ} {x v : Fin n → ℝ}
    (hx : x ∈ Set.extremePoints ℝ {x | A *ᵥ x ≤ b})
    (hv : ∀ i, (A *ᵥ x) i = b i → (A *ᵥ v) i = 0) : v = 0 := by
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, A *ᵥ (x + t • v) ≤ b := by
    simp only [mulVec_add, mulVec_smul]
    apply eventually_all.mpr
    intro i
    by_cases hi : (A *ᵥ x) i = b i
    · exact Eventually.of_forall fun t ↦ by simp [Pi.add_apply, Pi.smul_apply, hv i hi, hi]
    · have hcont : Continuous fun t : ℝ ↦ (A *ᵥ x) i + t * (A *ᵥ v) i :=
        continuous_const.add (continuous_id.mul continuous_const)
      exact ((hcont.tendsto' 0 _ (by simp)).eventually_lt_const
        (lt_of_le_of_ne (hx.1 i) hi)).mono fun _ h ↦ h.le
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  have hd : dist (ε / 2) 0 < ε := by
    simpa [Real.dist_eq, abs_of_pos (half_pos hε)] using half_lt_self hε
  have hplus := hball hd
  have hminus := hball (y := -(ε / 2)) (by simpa [Real.dist_eq] using hd)
  rw [neg_smul, ← sub_eq_add_neg] at hminus
  let := invertibleOfNonzero (two_ne_zero : (2 : ℝ) ≠ 0)
  have heq := hx.2 hplus hminus (mem_openSegment_add_sub (𝕜 := ℝ) x ((ε / 2) • v))
  exact (smul_eq_zero.mp (add_eq_left.mp heq)).resolve_left (half_pos hε).ne'

/-- A rational row has an integral multiple whose multiplier meets any prescribed lower bound. -/
private theorem exists_integral_multiple {n : ℕ} (q : Fin n → ℚ) (r : ℝ) :
    ∃ d : ℕ, r ≤ d ∧ ∀ j, ∃ k : ℤ, (d : ℝ) * (q j : ℝ) = k := by
  let D := ∏ j, (q j).den
  have hD : 1 ≤ D := Finset.prod_pos fun j _ ↦ (q j).den_pos
  obtain ⟨N, hN⟩ := exists_nat_gt r
  refine ⟨N * D, hN.le.trans (by exact_mod_cast Nat.le_mul_of_pos_right N hD), ?_⟩
  intro j
  obtain ⟨k, hk⟩ : (q j).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  refine ⟨(N : ℤ) * k * (q j).num, ?_⟩
  rw [hk, Rat.cast_def]
  push_cast
  have hd : ((q j).den : ℝ) ≠ 0 := by exact_mod_cast (q j).den_ne_zero
  field_simp

/-- With integral right-hand side, an integral objective attaining its maximum at `x` has
integral value there. -/
private theorem integral_maximum {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {b : Fin m → ℝ} (hb : ∀ i, ∃ z : ℤ, b i = z) (hTDI : IsTDI A b)
    {x : Fin n → ℝ} (hx : A *ᵥ x ≤ b) (c : Fin n → ℤ)
    (hmax : ∀ w, A *ᵥ w ≤ b → (fun j ↦ (c j : ℝ)) ⬝ᵥ w ≤ (fun j ↦ (c j : ℝ)) ⬝ᵥ x) :
    ∃ z : ℤ, (fun j ↦ (c j : ℝ)) ⬝ᵥ x = z := by
  obtain ⟨y, hy, hdual, w, hw, hvalue⟩ := hTDI c ⟨x, hx⟩
    ⟨_, fun _ ⟨w, hw, heq⟩ ↦ heq.symm.trans_le (hmax w hw)⟩
  choose z hz using hb
  refine ⟨z ⬝ᵥ y, ?_⟩
  have hcast : b ⬝ᵥ (fun i ↦ (y i : ℝ)) = ((z ⬝ᵥ y : ℤ) : ℝ) := by
    simp [dotProduct, hz]
  rw [← hcast]
  apply le_antisymm _ (hvalue.trans_le (hmax w hw))
  rw [← hdual, mulVec_transpose, ← dotProduct_mulVec, dotProduct_comm b]
  exact dotProduct_le_dotProduct_of_nonneg_left hx fun i ↦ Int.cast_nonneg (hy i)

/-- **Edmonds-Giles theorem.** If `A x ≤ b` is a TDI system with rational `A` and integral `b`,
then every extreme point of the polyhedron `{x : A x ≤ b}` is integral (Goemans, MIT 18.438,
Lecture 6, 2009, Theorem 2, where "integral" means that all extreme points are integral). -/
theorem extremePoints_integral_of_isTDI {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (hA : ∀ i j, ∃ q : ℚ, A i j = q) (hb : ∀ i, ∃ z : ℤ, b i = z)
    (hTDI : IsTDI A b) :
    ∀ x ∈ Set.extremePoints ℝ {x : Fin n → ℝ | A *ᵥ x ≤ b}, ∀ j, ∃ z : ℤ, x j = z := by
  classical
  intro x hx j
  let I := {i : Fin m // (A *ᵥ x) i = b i}
  let B : Matrix I (Fin n) ℝ := fun i ↦ A i.val
  -- The tight rows span the objective space, so they generate the coordinate objective.
  have hinj : Function.Injective B.mulVec := by
    apply (LinearMap.ker_eq_bot (f := B.mulVecLin)).mp
    apply ker_mulVecLin_eq_bot_iff.mpr
    intro v hv
    exact eq_zero_of_tight_rows hx fun i hi ↦ congrFun hv (⟨i, hi⟩ : I)
  obtain ⟨u, hu⟩ := (mulVec_injective_iff.mp hinj).vecMul_surjective (Pi.single j 1)
  change u ᵥ* B = Pi.single j 1 at hu
  -- Add integral multiples of the tight rows until every coefficient is nonnegative.
  choose q hq using hA
  choose d hd k hk using fun i : I ↦ exists_integral_multiple (q i.val) (-u i)
  let a : I → ℝ := fun i ↦ d i
  let c : Fin n → ℤ := fun l ↦ ∑ i, k i l
  have hc : a ᵥ* B = fun l ↦ (c l : ℝ) := by
    funext l
    change ∑ i : I, (d i : ℝ) * A i.val l = ((∑ i : I, k i l : ℤ) : ℝ)
    simp only [hq, hk, Int.cast_sum]
  let e : Fin n → ℤ := Pi.single j 1
  have he : (fun l ↦ (e l : ℝ)) = Pi.single j 1 := by
    ext l
    by_cases hl : l = j <;> simp [e, hl]
  have hce : (a + u) ᵥ* B = fun l ↦ ((c + e) l : ℝ) := by
    rw [add_vecMul, hc, hu, ← he]
    ext l
    simp
  -- Both objectives attain their maxima at x, where every row of B is tight.
  have integral (v : I → ℝ) (hv : 0 ≤ v) (f : Fin n → ℤ)
      (hf : v ᵥ* B = fun l ↦ (f l : ℝ)) : ∃ z : ℤ, (fun l ↦ (f l : ℝ)) ⬝ᵥ x = z := by
    apply integral_maximum hb hTDI hx.1 f
    intro w hw
    rw [← hf, ← dotProduct_mulVec, ← dotProduct_mulVec]
    exact dotProduct_le_dotProduct_of_nonneg_left (fun i ↦ (hw i.val).trans_eq i.prop.symm) hv
  obtain ⟨z, hz⟩ := integral a (fun i ↦ Nat.cast_nonneg (d i)) c hc
  obtain ⟨z', hz'⟩ := integral (a + u) (fun i ↦ by
    change 0 ≤ (d i : ℝ) + u i
    linarith [hd i]) (c + e) hce
  have hadd : (fun l ↦ ((c + e) l : ℝ)) = (fun l ↦ (c l : ℝ)) + (fun l ↦ (e l : ℝ)) := by
    ext l
    simp
  rw [hadd, add_dotProduct, hz, he, single_dotProduct, one_mul] at hz'
  exact ⟨z' - z, by push_cast; linarith⟩

end MathlibExt.Analysis.Convex.EdmondsGilesWanted
