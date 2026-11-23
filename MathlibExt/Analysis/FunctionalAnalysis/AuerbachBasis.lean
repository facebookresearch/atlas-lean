/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Auerbach bases in finite-dimensional normed spaces

An *Auerbach basis* of a finite-dimensional normed space `E` is a basis
whose vectors all have norm `1` and whose coordinate functionals all have
operator norm `1`. Auerbach's theorem (H. Auerbach, 1930) says that every
finite-dimensional normed space has one; see e.g. F. Albiac and
N. J. Kalton, *Topics in Banach Space Theory*, Springer, 2016.

The proof is the classical determinant-maximization argument. Fix a
background basis `b₀` and maximize `‖b₀.det x‖` over the compact set of
tuples `x` with every `‖x i‖ ≤ 1`. The maximum is nonzero (the normalized
background basis is a competitor), so the maximizer `x*` is a basis. If
some `‖x* i‖ < 1`, rescaling that one vector to norm `1` strictly
increases the determinant, contradicting maximality; hence every
`‖x* i‖ = 1`. Finally, for any `y`, replacing the `j`-th vector of `x*`
by the rescaled `y` does not increase the determinant, and the
determinant of the replaced tuple equals `b.coord j y * b₀.det x*` by
`Module.Basis.det_smul_mk_coord_eq_det_update`, which gives
`‖b.coord j y‖ ≤ ‖y‖`.

This is a companion to the Hamel-basis and dual-space material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/` (in particular the
Hahn–Banach material, which is how coordinate functionals are usually
produced). It is not one of the 72 v1 targets, and it is not in the
pinned Mathlib or in base MathlibExt.

## Main declarations

* `coordCLM` — the `i`-th coordinate functional of a basis, as a
  continuous linear map.
* `IsAuerbachBasis` — a basis of unit vectors whose coordinate
  functionals all have operator norm `1`.
* `exists_auerbach_basis` — Auerbach's theorem: every
  finite-dimensional normed space over `𝕜` (with `𝕜 = ℝ` or `𝕜 = ℂ`)
  has an Auerbach basis indexed by `Fin (Module.finrank 𝕜 E)`.
-/

open Set Filter Topology Metric

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.AuerbachBasis

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The `i`-th coordinate functional of a basis, as a continuous linear map.
In finite dimensions every linear map is continuous, so this is just the
coordinate functional bundled with its continuity. -/
noncomputable def coordCLM {ι : Type*} [FiniteDimensional 𝕜 E] (b : Module.Basis ι 𝕜 E) (i : ι) :
    E →L[𝕜] 𝕜 :=
  ⟨b.coord i, (b.coord i).continuous_of_finiteDimensional⟩

@[simp]
theorem coordCLM_apply {ι : Type*} [FiniteDimensional 𝕜 E] (b : Module.Basis ι 𝕜 E) (i : ι) (y : E) :
    coordCLM b i y = b.coord i y :=
  rfl

/-- If the `i`-th coordinate functional is bounded by the norm, its operator
norm is at most `1`. -/
theorem norm_coordCLM_le_one {ι : Type*} [FiniteDimensional 𝕜 E] (b : Module.Basis ι 𝕜 E) (i : ι)
    (h : ∀ y : E, ‖b.coord i y‖ ≤ ‖y‖) : ‖coordCLM b i‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) ?_
  intro y
  simpa using h y

/-- If the `i`-th basis vector has norm `1` and the `i`-th coordinate
functional is bounded by the norm, its operator norm is exactly `1`: it
attains `1` at the `i`-th basis vector. -/
theorem norm_coordCLM_eq_one {ι : Type*} [FiniteDimensional 𝕜 E] (b : Module.Basis ι 𝕜 E) (i : ι)
    (hb : ‖b i‖ = 1) (h : ∀ y : E, ‖b.coord i y‖ ≤ ‖y‖) : ‖coordCLM b i‖ = 1 := by
  apply le_antisymm (norm_coordCLM_le_one b i h)
  have h1 : ‖b.coord i (b i)‖ = 1 := by simp
  calc (1 : ℝ) = ‖b.coord i (b i)‖ := h1.symm
    _ ≤ ‖coordCLM b i‖ * ‖b i‖ := by
      simpa [coordCLM_apply] using ContinuousLinearMap.le_opNorm (coordCLM b i) (b i)
    _ = ‖coordCLM b i‖ := by rw [hb, mul_one]

/-- An *Auerbach basis* is a basis of unit vectors whose coordinate
functionals all have operator norm `1`. -/
def IsAuerbachBasis {ι : Type*} [FiniteDimensional 𝕜 E] (b : Module.Basis ι 𝕜 E) : Prop :=
  (∀ i, ‖b i‖ = 1) ∧ ∀ i, ‖coordCLM b i‖ = 1

/-- **Auerbach's theorem**: every finite-dimensional normed space over `𝕜`
has an Auerbach basis, indexed by `Fin (Module.finrank 𝕜 E)`. -/
theorem exists_auerbach_basis [FiniteDimensional 𝕜 E] :
    ∃ b : Module.Basis (Fin (Module.finrank 𝕜 E)) 𝕜 E, IsAuerbachBasis b := by
  classical
  set n := Module.finrank 𝕜 E with hn
  set b₀ : Module.Basis (Fin n) 𝕜 E := Module.finBasis 𝕜 E with hb₀
  have : ProperSpace E := FiniteDimensional.proper_rclike 𝕜 E
  -- The compact set of tuples with every component in the closed unit ball.
  set S : Set (Fin n → E) := Set.pi Set.univ fun _ => Metric.closedBall 0 1 with hS
  have hScompact : IsCompact S := isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have hSmem : ∀ {x : Fin n → E}, x ∈ S → ∀ i, ‖x i‖ ≤ 1 := by
    intro x hx i
    have hi := hx i (mem_univ i)
    simpa [Metric.mem_closedBall, dist_eq_norm] using hi
  have hSof : ∀ {x : Fin n → E}, (∀ i, ‖x i‖ ≤ 1) → x ∈ S := by
    intro x hx i _
    apply Metric.mem_closedBall.mpr
    simpa [dist_eq_norm] using hx i
  -- The determinant is continuous in the tuple.
  have hdet_cont : Continuous fun x : Fin n → E => b₀.det x := by
    have h1 : Continuous fun x : Fin n → E => b₀.toMatrix x := b₀.continuous_toMatrix
    have h2 : Continuous fun M : Matrix (Fin n) (Fin n) 𝕜 => M.det := by
      have hEq : (fun M : Matrix (Fin n) (Fin n) 𝕜 => M.det)
          = fun M => ∑ σ : Equiv.Perm (Fin n),
            (Equiv.Perm.sign σ : 𝕜) * ∏ i, M (σ i) i := by
        funext M
        simp [Matrix.det_apply, Units.smul_def]
      rw [hEq]
      refine continuous_finsetSum _ fun σ _ => Continuous.mul continuous_const ?_
      exact continuous_finsetProd _ fun i _ =>
        (continuous_apply i).comp (continuous_apply (σ i))
    have h3 : (fun x : Fin n → E => b₀.det x)
        = (fun M : Matrix (Fin n) (Fin n) 𝕜 => M.det) ∘ (fun x : Fin n → E => b₀.toMatrix x) := by
      funext x
      exact (b₀.det_apply x).symm
    rw [h3]
    exact h2.comp h1
  have hFcont : Continuous fun x : Fin n → E => ‖b₀.det x‖ := hdet_cont.norm
  -- The normalized background basis is a competitor with nonzero determinant.
  have hb₀ne : ∀ i, b₀ i ≠ 0 := fun i => b₀.ne_zero i
  have hcpos : ∀ i, 0 < ‖b₀ i‖ := fun i => norm_pos_iff.mpr (hb₀ne i)
  set w : Fin n → 𝕜ˣ := fun i =>
    Units.mk0 ((‖b₀ i‖ : 𝕜)⁻¹) (by
      have h : ((‖b₀ i‖ : 𝕜)) ≠ 0 := by exact_mod_cast ne_of_gt (hcpos i)
      exact inv_ne_zero h) with hw
  have hwval : ∀ i, (w i : 𝕜) = (‖b₀ i‖ : 𝕜)⁻¹ := fun i => rfl
  set x₀ : Fin n → E := ⇑(b₀.unitsSMul w) with hx₀
  have hx₀mem : x₀ ∈ S := by
    apply hSof
    intro i
    rw [hx₀, Module.Basis.unitsSMul_apply]
    show ‖(w i : 𝕜) • b₀ i‖ ≤ 1
    rw [hwval, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos (hcpos i),
      inv_mul_cancel₀ (ne_of_gt (hcpos i))]
  have hx₀det : b₀.det x₀ ≠ 0 := by
    rw [hx₀, b₀.det_unitsSMul_self]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => Units.ne_zero _
  -- Maximize `‖det‖` over `S`.
  obtain ⟨xstar, hxstarS, hxstarMax⟩ := hScompact.exists_isMaxOn ⟨x₀, hx₀mem⟩ hFcont.continuousOn
  have hD : 0 < ‖b₀.det xstar‖ := by
    have h0 : 0 < ‖b₀.det x₀‖ := norm_pos_iff.mpr hx₀det
    exact lt_of_lt_of_le h0 (hxstarMax hx₀mem)
  have hdet_ne : b₀.det xstar ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hD)
  -- The maximizer is a basis.
  have hunit : IsUnit (b₀.det xstar) := isUnit_iff_ne_zero.mpr hdet_ne
  obtain ⟨hli, hspan⟩ := (Module.Basis.is_basis_iff_det b₀).mpr hunit
  -- Every component of the maximizer has norm exactly `1`.
  have hnorm1 : ∀ i, ‖xstar i‖ = 1 := by
    intro i
    have hle : ‖xstar i‖ ≤ 1 := hSmem hxstarS i
    by_cases hc : ‖xstar i‖ = 0
    · exfalso
      apply hdet_ne
      have h0 : xstar i = 0 := norm_eq_zero.mp hc
      exact b₀.det.map_coord_zero i h0
    · have hcpos' : 0 < ‖xstar i‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hc)
      set c : ℝ := ‖xstar i‖ with hcdef
      set y : Fin n → E := Function.update xstar i ((c⁻¹ : 𝕜) • xstar i) with hydef
      have hyS : y ∈ S := by
        apply hSof
        intro j
        by_cases hji : j = i
        · subst hji
          rw [hydef, Function.update_self]
          rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hcpos',
            inv_mul_cancel₀ (ne_of_gt hcpos')]
        · rw [hydef, Function.update_of_ne hji]
          exact hSmem hxstarS j
      have hdet_y : b₀.det y = (c⁻¹ : 𝕜) • b₀.det xstar := by
        rw [hydef, b₀.det.map_update_smul, Function.update_eq_self]
      have hnorm_y : ‖b₀.det y‖ = c⁻¹ * ‖b₀.det xstar‖ := by
        rw [hdet_y, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hcpos']
      have hmax : ‖b₀.det y‖ ≤ ‖b₀.det xstar‖ := hxstarMax hyS
      have hcinv : c⁻¹ ≤ 1 := by
        rw [hnorm_y] at hmax
        have h' : c⁻¹ * ‖b₀.det xstar‖ ≤ 1 * ‖b₀.det xstar‖ := by simpa using hmax
        exact le_of_mul_le_mul_right h' hD
      have hc1 : 1 ≤ c := by
        have h := inv_anti₀ (inv_pos.mpr hcpos') hcinv
        simpa using h
      exact le_antisymm hle hc1
  -- The coordinate functionals are bounded by the norm.
  have hcoord : ∀ j, ∀ y : E, ‖(Module.Basis.mk hli hspan.ge).coord j y‖ ≤ ‖y‖ := by
    intro j y
    by_cases hy0 : y = 0
    · simp only [hy0, map_zero, norm_zero, le_refl]
    · have hd : 0 < ‖y‖ := norm_pos_iff.mpr hy0
      set d : ℝ := ‖y‖ with hddef
      set y' : E := (d⁻¹ : 𝕜) • y with hy'def
      have hy'norm : ‖y'‖ = 1 := by
        rw [hy'def, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hd,
          inv_mul_cancel₀ (ne_of_gt hd)]
      set z : Fin n → E := Function.update xstar j y' with hzdef
      have hzS : z ∈ S := by
        apply hSof
        intro k
        by_cases hkj : k = j
        · subst hkj
          rw [hzdef, Function.update_self]
          exact le_of_eq hy'norm
        · rw [hzdef, Function.update_of_ne hkj]
          exact hSmem hxstarS k
      have hdet_z : b₀.det z = b₀.det xstar * (Module.Basis.mk hli hspan.ge).coord j y' := by
        have h := b₀.det_smul_mk_coord_eq_det_update hli hspan.ge j
        have h2 := LinearMap.congr_fun h y'
        rw [LinearMap.smul_apply, smul_eq_mul, MultilinearMap.toLinearMap_apply] at h2
        rw [hzdef]
        exact h2.symm
      have hnorm' : ‖(Module.Basis.mk hli hspan.ge).coord j y'‖ ≤ 1 := by
        have hle : ‖b₀.det z‖ ≤ ‖b₀.det xstar‖ := hxstarMax hzS
        rw [hdet_z, norm_mul] at hle
        have h' : ‖b₀.det xstar‖ * ‖(Module.Basis.mk hli hspan.ge).coord j y'‖
            ≤ ‖b₀.det xstar‖ * 1 := by simpa using hle
        exact le_of_mul_le_mul_left h' hD
      have hy_eq : y = (d : 𝕜) • y' := by
        rw [hy'def, smul_smul,
          mul_inv_cancel₀ (by exact_mod_cast ne_of_gt hd : (d : 𝕜) ≠ 0), one_smul]
      rw [hy_eq, map_smul, norm_smul, RCLike.norm_ofReal, abs_of_pos hd]
      calc d * ‖(Module.Basis.mk hli hspan.ge).coord j y'‖ ≤ d * 1 :=
            mul_le_mul_of_nonneg_left hnorm' (le_of_lt hd)
        _ = d := mul_one d
  refine ⟨Module.Basis.mk hli hspan.ge, ?_, ?_⟩
  · intro i
    have hbi : (Module.Basis.mk hli hspan.ge) i = xstar i := by simp
    rw [hbi]
    exact hnorm1 i
  · intro i
    exact norm_coordCLM_eq_one _ i (by
      have hbi : (Module.Basis.mk hli hspan.ge) i = xstar i := by simp
      rw [hbi]
      exact hnorm1 i) (hcoord i)

end MathlibExt.Analysis.FunctionalAnalysis.AuerbachBasis
