/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Rate laws

Extent-rate convention, integrated rate laws (orders 0, 1, 2), half-life
characterization, rate-constant units, and a pseudo-first-order error bound.
-/

@[expose] public section

namespace Chemistry.Kinetics

/-! ## Extent-rate convention -/

/-- Extent rate `v = (1 / V) dξ/dt`: the single rate convention used here. -/
noncomputable def extentRate (V : ℝ) (ξ : ℝ → ℝ) (t : ℝ) : ℝ := (1 / V) * deriv ξ t

/-- Concentration from extent at constant volume: `c = c₀ + ν ξ / V`. -/
noncomputable def concOfExtent (c₀ ν V : ℝ) (ξ : ℝ → ℝ) (t : ℝ) : ℝ := c₀ + ν * ξ t / V

/-- Concentration rate from the extent rate: `dc/dt = ν v`. -/
theorem hasDerivAt_concOfExtent (c₀ ν V : ℝ) (ξ : ℝ → ℝ) (t : ℝ)
    (hξ : DifferentiableAt ℝ ξ t) :
    HasDerivAt (concOfExtent c₀ ν V ξ) (ν * extentRate V ξ t) t := by
  have hbase : HasDerivAt (fun s : ℝ => (ν / V) * ξ s) _ t :=
    hξ.hasDerivAt.const_mul (ν / V)
  have hadd : HasDerivAt (fun s : ℝ => c₀ + (ν / V) * ξ s) _ t :=
    hbase.const_add c₀
  have heq : (fun s : ℝ => c₀ + ν * ξ s / V) = (fun s : ℝ => c₀ + (ν / V) * ξ s) := by
    funext s
    ring
  have hchain : HasDerivAt (fun s : ℝ => c₀ + ν * ξ s / V) _ t :=
    hadd.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq heq)
  have hderiv : deriv (fun s : ℝ => c₀ + ν * ξ s / V) t
      = ν * ((1 / V) * deriv ξ t) := by
    rw [hchain.deriv]; ring
  have hfinal := hchain.differentiableAt.hasDerivAt
  rw [hderiv] at hfinal
  show HasDerivAt (fun s : ℝ => c₀ + ν * ξ s / V) (ν * ((1 / V) * deriv ξ t)) t
  exact hfinal

/-- `deriv` form of `hasDerivAt_concOfExtent`. -/
theorem deriv_concOfExtent (c₀ ν V : ℝ) (ξ : ℝ → ℝ) (t : ℝ)
    (hξ : DifferentiableAt ℝ ξ t) :
    deriv (concOfExtent c₀ ν V ξ) t = ν * extentRate V ξ t :=
  (hasDerivAt_concOfExtent c₀ ν V ξ t hξ).deriv

/-- Zero-order ODE from the convention: `v = k`, `ν = -1`. -/
theorem rateLaw_zero_ode (A ξ : ℝ → ℝ) (A0 k V t : ℝ)
    (hA : ∀ s, A s = concOfExtent A0 (-1) V ξ s)
    (hξ : DifferentiableAt ℝ ξ t)
    (hrate : extentRate V ξ t = k) :
    HasDerivAt A (-k) t := by
  have hAfun : A = concOfExtent A0 (-1) V ξ := funext hA
  have hbase := hasDerivAt_concOfExtent A0 (-1) V ξ t hξ
  rw [← hAfun] at hbase
  rw [hrate] at hbase
  have hval : (-1) * k = -k := by ring
  rw [hval] at hbase
  exact hbase

/-- First-order ODE from the convention: `v = k[A]`, `ν = -1`. -/
theorem rateLaw_first_ode (A ξ : ℝ → ℝ) (A0 k V t : ℝ)
    (hA : ∀ s, A s = concOfExtent A0 (-1) V ξ s)
    (hξ : DifferentiableAt ℝ ξ t)
    (hrate : extentRate V ξ t = k * A t) :
    HasDerivAt A (-k * A t) t := by
  have hAfun : A = concOfExtent A0 (-1) V ξ := funext hA
  have hbase := hasDerivAt_concOfExtent A0 (-1) V ξ t hξ
  rw [← hAfun] at hbase
  rw [hrate] at hbase
  have hval : (-1) * (k * A t) = -k * A t := by ring
  rw [hval] at hbase
  exact hbase

/-- Second-order `2A → P` ODE: `v = k[A]²`, `ν = -2`. -/
theorem rateLaw_secondAA_ode (A ξ : ℝ → ℝ) (A0 k V t : ℝ)
    (hA : ∀ s, A s = concOfExtent A0 (-2) V ξ s)
    (hξ : DifferentiableAt ℝ ξ t)
    (hrate : extentRate V ξ t = k * (A t)^2) :
    HasDerivAt A (-(2 * k) * (A t)^2) t := by
  have hAfun : A = concOfExtent A0 (-2) V ξ := funext hA
  have hbase := hasDerivAt_concOfExtent A0 (-2) V ξ t hξ
  rw [← hAfun] at hbase
  rw [hrate] at hbase
  have hval : (-2) * (k * (A t)^2) = -(2 * k) * (A t)^2 := by ring
  rw [hval] at hbase
  exact hbase

/-- Second-order `A + B` ODEs: `v = k[A][B]`, `ν = -1` for both. -/
theorem rateLaw_secondAB_ode (A B ξ : ℝ → ℝ) (A0 B0 k V t : ℝ)
    (hA : ∀ s, A s = concOfExtent A0 (-1) V ξ s)
    (hB : ∀ s, B s = concOfExtent B0 (-1) V ξ s)
    (hξ : DifferentiableAt ℝ ξ t)
    (hrate : extentRate V ξ t = k * A t * B t) :
    HasDerivAt A (-k * A t * B t) t ∧ HasDerivAt B (-k * A t * B t) t := by
  have hval : (-1) * (k * A t * B t) = -k * A t * B t := by ring
  constructor
  · have hAfun : A = concOfExtent A0 (-1) V ξ := funext hA
    have hbase := hasDerivAt_concOfExtent A0 (-1) V ξ t hξ
    rw [← hAfun] at hbase
    rw [hrate] at hbase
    rw [hval] at hbase
    exact hbase
  · have hBfun : B = concOfExtent B0 (-1) V ξ := funext hB
    have hbase := hasDerivAt_concOfExtent B0 (-1) V ξ t hξ
    rw [← hBfun] at hbase
    rw [hrate] at hbase
    rw [hval] at hbase
    exact hbase

/-! ## Solution uniqueness helper -/

/-- A function with zero derivative on `t ≥ 0` is determined by its value at `0`. -/
theorem eq_of_hasDerivAt_zero (g : ℝ → ℝ)
    (hg : ∀ t : ℝ, 0 ≤ t → HasDerivAt g 0 t) (hg0 : g 0 = 0)
    (t : ℝ) (ht : 0 ≤ t) : g t = 0 := by
  rcases eq_or_lt_of_le ht with rfl | hlt
  · exact hg0
  · have hderiv : ∀ x ∈ Set.Ioo 0 t, HasDerivAt g 0 x :=
      fun x hx => hg x (le_of_lt (Set.mem_Ioo.mp hx).1)
    have hcont : ContinuousOn g (Set.Icc 0 t) :=
      fun x hx => ((hg x (Set.mem_Icc.mp hx).1).continuousAt).continuousWithinAt
    obtain ⟨c, -, hc⟩ := exists_hasDerivAt_eq_slope g (fun _ => 0) hlt hcont hderiv
    have hc' : (0:ℝ) = (g t - g 0) / (t - 0) := hc
    rw [hg0] at hc'
    simp only [sub_zero] at hc'
    have hne : t ≠ 0 := ne_of_gt hlt
    have hsplit := div_eq_zero_iff.mp hc'.symm
    rcases hsplit with h | h
    · exact h
    · exact absurd h hne

/-! ## Order 0 -/

/-- Zero-order integrated law (before depletion): `[A]₀ - kt`. -/
def zeroOrderSol (A0 k : ℝ) (t : ℝ) : ℝ := A0 - k * t

/-- The zero-order solution has constant derivative `-k`. -/
theorem hasDerivAt_zeroOrderSol (A0 k t : ℝ) :
    HasDerivAt (zeroOrderSol A0 k) (-k) t := by
  have hchain : HasDerivAt (fun s : ℝ => A0 - k * s) _ t :=
    (hasDerivAt_const t A0).sub ((hasDerivAt_id' t).const_mul k)
  have hderiv : deriv (fun s : ℝ => A0 - k * s) t = -k := by
    rw [hchain.deriv]; ring
  have hfinal := hchain.differentiableAt.hasDerivAt
  rw [hderiv] at hfinal
  show HasDerivAt (fun s : ℝ => A0 - k * s) (-k) t
  exact hfinal

/-- Uniqueness for the zero-order ODE `f' = -k` on `t ≥ 0`. -/
theorem zeroOrderSol_unique (A0 k : ℝ) (g : ℝ → ℝ)
    (hg : ∀ t : ℝ, 0 ≤ t → HasDerivAt g (-k) t) (hg0 : g 0 = A0)
    (t : ℝ) (ht : 0 ≤ t) : g t = zeroOrderSol A0 k t := by
  have hh : ∀ s : ℝ, 0 ≤ s →
      HasDerivAt (fun s : ℝ => g s - zeroOrderSol A0 k s) 0 s := by
    intro s hs
    have hchain : HasDerivAt (fun s : ℝ => g s - zeroOrderSol A0 k s) _ s :=
      (hg s hs).sub (hasDerivAt_zeroOrderSol A0 k s)
    have hderiv : deriv (fun s : ℝ => g s - zeroOrderSol A0 k s) s = 0 := by
      rw [hchain.deriv]; ring
    have hfinal := hchain.differentiableAt.hasDerivAt
    rw [hderiv] at hfinal
    exact hfinal
  have h0 : (fun s : ℝ => g s - zeroOrderSol A0 k s) 0 = 0 := by
    simp only [hg0, zeroOrderSol, mul_zero, sub_zero, sub_self]
  have heq := eq_of_hasDerivAt_zero _ hh h0 t ht
  have heq' : g t - zeroOrderSol A0 k t = 0 := heq
  linarith

/-- The zero-order solution starts at `[A]₀`. -/
theorem zeroOrderSol_zero (A0 k : ℝ) : zeroOrderSol A0 k 0 = A0 := by
  simp [zeroOrderSol]

/-- Zero-order depletion time `[A]₀ / k`. -/
noncomputable def depletionTime (A0 k : ℝ) : ℝ := A0 / k

/-- Physical zero-order concentration, piecewise at depletion. -/
def zeroOrderConc (A0 k : ℝ) (t : ℝ) : ℝ := max (A0 - k * t) 0

/-- Before depletion the physical concentration tracks `A₀ - kt`. -/
theorem zeroOrderConc_before (A0 k t : ℝ) (hk : 0 < k)
    (ht : t ≤ depletionTime A0 k) : zeroOrderConc A0 k t = A0 - k * t := by
  have ht' : t ≤ A0 / k := ht
  have hkne : k ≠ 0 := ne_of_gt hk
  have hle : (0:ℝ) ≤ A0 - k * t := by
    have hkt : k * t ≤ k * (A0 / k) := mul_le_mul_of_nonneg_left ht' (le_of_lt hk)
    have hkA0 : k * (A0 / k) = A0 := by field_simp
    linarith
  show max (A0 - k * t) 0 = A0 - k * t
  exact max_eq_left hle

/-- After depletion the physical concentration is zero. -/
theorem zeroOrderConc_after (A0 k t : ℝ) (hk : 0 < k)
    (ht : depletionTime A0 k ≤ t) : zeroOrderConc A0 k t = 0 := by
  have ht' : A0 / k ≤ t := ht
  have hkne : k ≠ 0 := ne_of_gt hk
  have hle : A0 - k * t ≤ 0 := by
    have hkt : k * (A0 / k) ≤ k * t := mul_le_mul_of_nonneg_left ht' (le_of_lt hk)
    have hkA0 : k * (A0 / k) = A0 := by field_simp
    linarith
  show max (A0 - k * t) 0 = 0
  exact max_eq_right hle

/-- Zero-order half-life: `[A]₀ / (2k)`. -/
theorem zeroOrderSol_halfLife (A0 k : ℝ) (hk : 0 < k) (hA0 : 0 < A0) :
    zeroOrderSol A0 k (A0 / (2 * k)) = A0 / 2 := by
  have h2kne : (2:ℝ) * k ≠ 0 := ne_of_gt (by positivity)
  show A0 - k * (A0 / (2 * k)) = A0 / 2
  field_simp; ring

/-- The zero-order half-life time is unique. -/
theorem zeroOrderSol_halfLife_unique (A0 k t : ℝ) (hk : 0 < k) (_hA0 : 0 < A0)
    (h : zeroOrderSol A0 k t = A0 / 2) : t = A0 / (2 * k) := by
  have h2kpos : (0:ℝ) < 2 * k := by positivity
  rw [eq_div_iff (ne_of_gt h2kpos)]
  simp only [zeroOrderSol] at h
  linarith

/-! ## Order 1 -/

/-- First-order integrated law: `[A]₀ exp(-kt)`. -/
noncomputable def firstOrderSol (A0 k : ℝ) (t : ℝ) : ℝ := A0 * Real.exp (-k * t)

/-- The first-order solution starts at `[A]₀`. -/
theorem firstOrderSol_zero (A0 k : ℝ) : firstOrderSol A0 k 0 = A0 := by
  simp [firstOrderSol]

/-- The first-order solution stays positive. -/
theorem firstOrderSol_pos (A0 k t : ℝ) (hA0 : 0 < A0) :
    0 < firstOrderSol A0 k t := by
  show 0 < A0 * Real.exp (-k * t)
  exact mul_pos hA0 (Real.exp_pos _)

/-- The first-order solution satisfies `f' = -k f`. -/
theorem hasDerivAt_firstOrderSol (A0 k t : ℝ) :
    HasDerivAt (firstOrderSol A0 k) (-k * firstOrderSol A0 k t) t := by
  have hchain : HasDerivAt (fun s : ℝ => A0 * Real.exp (-k * s)) _ t :=
    (((hasDerivAt_id' t).const_mul (-k)).exp).const_mul A0
  have hderiv : deriv (fun s : ℝ => A0 * Real.exp (-k * s)) t
      = -k * (A0 * Real.exp (-k * t)) := by
    rw [hchain.deriv]; ring
  have hfinal := hchain.differentiableAt.hasDerivAt
  rw [hderiv] at hfinal
  show HasDerivAt (fun s : ℝ => A0 * Real.exp (-k * s))
    (-k * (A0 * Real.exp (-k * t))) t
  exact hfinal

/-- Uniqueness for `f' = -k f` on `t ≥ 0`, via the integrating factor. -/
theorem firstOrderSol_unique (A0 k : ℝ) (g : ℝ → ℝ)
    (hg : ∀ t : ℝ, 0 ≤ t → HasDerivAt g (-k * g t) t) (hg0 : g 0 = A0)
    (t : ℝ) (ht : 0 ≤ t) : g t = firstOrderSol A0 k t := by
  have hh : ∀ s : ℝ, 0 ≤ s →
      HasDerivAt (fun s : ℝ => g s * Real.exp (k * s) - A0) 0 s := by
    intro s hs
    have hchain : HasDerivAt (fun s : ℝ => g s * Real.exp (k * s) - A0) _ s :=
      ((hg s hs).mul (((hasDerivAt_id' s).const_mul k).exp)).sub
        (hasDerivAt_const s A0)
    have hderiv : deriv (fun s : ℝ => g s * Real.exp (k * s) - A0) s = 0 := by
      rw [hchain.deriv]; ring
    have hfinal := hchain.differentiableAt.hasDerivAt
    rw [hderiv] at hfinal
    exact hfinal
  have h0 : (fun s : ℝ => g s * Real.exp (k * s) - A0) 0 = 0 := by
    simp [hg0]
  have heq := eq_of_hasDerivAt_zero _ hh h0 t ht
  have heq' : g t * Real.exp (k * t) - A0 = 0 := heq
  have hmul : g t * Real.exp (k * t) = A0 := by linarith
  have hEne : Real.exp (k * t) ≠ 0 := Real.exp_ne_zero _
  have h1 : g t = A0 / Real.exp (k * t) := by
    rw [eq_div_iff hEne]
    exact hmul
  have h2 : (Real.exp (k * t))⁻¹ = Real.exp (-k * t) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have hconcl : g t = A0 * Real.exp (-k * t) := by
    rw [h1, div_eq_mul_inv, h2]
  show g t = A0 * Real.exp (-k * t)
  exact hconcl

/-- First-order half-life: `ln 2 / k`. -/
theorem firstOrderSol_halfLife (A0 k : ℝ) (hk : 0 < k) (_hA0 : 0 < A0) :
    firstOrderSol A0 k (Real.log 2 / k) = A0 / 2 := by
  have hkne : k ≠ 0 := ne_of_gt hk
  have hexp : -k * (Real.log 2 / k) = -Real.log 2 := by field_simp
  have he2 : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    norm_num
  show A0 * Real.exp (-k * (Real.log 2 / k)) = A0 / 2
  rw [hexp, he2]
  ring

/-- The first-order half-life time is unique. -/
theorem firstOrderSol_halfLife_unique (A0 k t : ℝ) (hk : 0 < k) (hA0 : 0 < A0)
    (h : firstOrderSol A0 k t = A0 / 2) : t = Real.log 2 / k := by
  have hA0ne : A0 ≠ 0 := ne_of_gt hA0
  have hkne : k ≠ 0 := ne_of_gt hk
  simp only [firstOrderSol] at h
  have h' : A0 * Real.exp (-k * t) = A0 * (1 / 2) := by linarith
  have hE : Real.exp (-k * t) = 1 / 2 := mul_left_cancel₀ hA0ne h'
  have hlog := congrArg Real.log hE
  rw [Real.log_exp] at hlog
  have h12 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
  rw [h12] at hlog
  rw [eq_div_iff hkne]
  linarith

/-! ## Order 2: general single-reactant law and A+A -/

/-- Uniqueness for `f' = -c f²` with `c > 0`, via the reciprocal transform. -/
theorem secondOrderGen_unique (A0 c : ℝ) (g : ℝ → ℝ) (hc : 0 < c) (hA0 : 0 < A0)
    (hg : ∀ t : ℝ, 0 ≤ t → HasDerivAt g (-c * (g t)^2) t)
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 < g t) (hg0 : g 0 = A0)
    (t : ℝ) (ht : 0 ≤ t) : g t = A0 / (1 + c * A0 * t) := by
  have hA0ne : A0 ≠ 0 := ne_of_gt hA0
  have hw : ∀ s : ℝ, 0 ≤ s → HasDerivAt (fun s : ℝ => (g s)⁻¹) c s := by
    intro s hs
    have hchain : HasDerivAt (fun s : ℝ => (g s)⁻¹) _ s :=
      (hg s hs).inv (ne_of_gt (hpos s hs))
    have hderiv : deriv (fun s : ℝ => (g s)⁻¹) s = c := by
      rw [hchain.deriv]
      have hne : g s ≠ 0 := ne_of_gt (hpos s hs)
      have hne2 : (g s)^2 ≠ 0 := pow_ne_zero 2 hne
      field_simp
    have hfinal := hchain.differentiableAt.hasDerivAt
    rw [hderiv] at hfinal
    exact hfinal
  have haff : ∀ s : ℝ, HasDerivAt (fun s : ℝ => 1 / A0 + c * s) c s := by
    intro s
    simpa using ((hasDerivAt_id' s).const_mul c).const_add (1 / A0)
  have hh : ∀ s : ℝ, 0 ≤ s →
      HasDerivAt (fun s : ℝ => (g s)⁻¹ - (1 / A0 + c * s)) 0 s := by
    intro s hs
    have hchain : HasDerivAt (fun s : ℝ => (g s)⁻¹ - (1 / A0 + c * s)) _ s :=
      (hw s hs).sub (haff s)
    have hderiv : deriv (fun s : ℝ => (g s)⁻¹ - (1 / A0 + c * s)) s = 0 := by
      rw [hchain.deriv]; ring
    have hfinal := hchain.differentiableAt.hasDerivAt
    rw [hderiv] at hfinal
    exact hfinal
  have h0 : (fun s : ℝ => (g s)⁻¹ - (1 / A0 + c * s)) 0 = 0 := by
    simp only [hg0, mul_zero, add_zero, one_div, sub_self]
  have heq := eq_of_hasDerivAt_zero _ hh h0 t ht
  have heq' : (g t)⁻¹ - (1 / A0 + c * t) = 0 := heq
  have hw_eq : (g t)⁻¹ = 1 / A0 + c * t := by linarith
  have hgt : g t ≠ 0 := ne_of_gt (hpos t ht)
  have h1A0 : (0:ℝ) < 1 / A0 := one_div_pos.mpr hA0
  have hct : (0:ℝ) ≤ c * t := mul_nonneg (le_of_lt hc) ht
  have hden : (1:ℝ) / A0 + c * t ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg h1A0 hct)
  have hden2 : (1:ℝ) + c * A0 * t ≠ 0 := ne_of_gt (by positivity)
  have h1 : g t * (1 / A0 + c * t) = 1 := by
    rw [← hw_eq]
    exact mul_inv_cancel₀ hgt
  have h2 : g t = 1 / (1 / A0 + c * t) := by
    rw [eq_div_iff hden]
    exact h1
  have h3 : (1:ℝ) / (1 / A0 + c * t) = A0 / (1 + c * A0 * t) := by
    rw [div_eq_div_iff hden hden2]
    field_simp
  exact h2.trans h3

/-- `2A → P` integrated law with `ν = -2`: `[A]₀ / (1 + 2k[A]₀t)`. -/
noncomputable def secondOrderAASol (A0 k : ℝ) (t : ℝ) : ℝ := A0 / (1 + 2 * k * A0 * t)

/-- The `2A → P` solution starts at `[A]₀`. -/
theorem secondOrderAASol_zero (A0 k : ℝ) : secondOrderAASol A0 k 0 = A0 := by
  simp [secondOrderAASol]

/-- The `2A → P` denominator stays positive for `t ≥ 0`. -/
theorem secondOrderAASol_denom_pos (A0 k t : ℝ) (hk : 0 < k) (hA0 : 0 < A0)
    (ht : 0 ≤ t) : 0 < 1 + 2 * k * A0 * t := by positivity

/-- The `2A → P` solution stays positive for `t ≥ 0`. -/
theorem secondOrderAASol_pos (A0 k t : ℝ) (hk : 0 < k) (hA0 : 0 < A0)
    (ht : 0 ≤ t) : 0 < secondOrderAASol A0 k t := by
  show 0 < A0 / (1 + 2 * k * A0 * t)
  exact div_pos hA0 (secondOrderAASol_denom_pos A0 k t hk hA0 ht)

/-- The `2A → P` solution satisfies `f' = -(2k) f²`. -/
theorem hasDerivAt_secondOrderAASol (A0 k t : ℝ)
    (hM : 1 + 2 * k * A0 * t ≠ 0) :
    HasDerivAt (secondOrderAASol A0 k)
      (-(2 * k) * (secondOrderAASol A0 k t)^2) t := by
  have hM' : HasDerivAt (fun s : ℝ => 1 + 2 * k * A0 * s) _ t :=
    ((hasDerivAt_id' t).const_mul (2 * k * A0)).const_add 1
  have hchain : HasDerivAt (fun s : ℝ => A0 / (1 + 2 * k * A0 * s)) _ t :=
    (hasDerivAt_const t A0).div hM' hM
  have hderiv : deriv (fun s : ℝ => A0 / (1 + 2 * k * A0 * s)) t
      = -(2 * k) * (A0 / (1 + 2 * k * A0 * t))^2 := by
    rw [hchain.deriv]
    have hM2 : (1 + 2 * k * A0 * t)^2 ≠ 0 := pow_ne_zero 2 hM
    field_simp; ring
  have hfinal := hchain.differentiableAt.hasDerivAt
  rw [hderiv] at hfinal
  show HasDerivAt (fun s : ℝ => A0 / (1 + 2 * k * A0 * s))
    (-(2 * k) * (A0 / (1 + 2 * k * A0 * t))^2) t
  exact hfinal

/-- Uniqueness for the `2A → P` ODE on `t ≥ 0`. -/
theorem secondOrderAASol_unique (A0 k : ℝ) (g : ℝ → ℝ) (hk : 0 < k)
    (hA0 : 0 < A0)
    (hg : ∀ t : ℝ, 0 ≤ t → HasDerivAt g (-(2 * k) * (g t)^2) t)
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 < g t) (hg0 : g 0 = A0)
    (t : ℝ) (ht : 0 ≤ t) : g t = secondOrderAASol A0 k t := by
  have h2k : (0:ℝ) < 2 * k := by positivity
  have hgen := secondOrderGen_unique A0 (2 * k) g h2k hA0 hg hpos hg0 t ht
  have hbridge : A0 / (1 + (2 * k) * A0 * t) = secondOrderAASol A0 k t := by
    show A0 / (1 + (2 * k) * A0 * t) = A0 / (1 + 2 * k * A0 * t)
    congr 1
  exact hgen.trans hbridge

/-- `2A → P` half-life: `1 / (2k[A]₀)`. -/
theorem secondOrderAASol_halfLife (A0 k : ℝ) (hk : 0 < k) (hA0 : 0 < A0) :
    secondOrderAASol A0 k (1 / (2 * k * A0)) = A0 / 2 := by
  have hpos : (0:ℝ) < 2 * k * A0 := by positivity
  have hne : (2:ℝ) * k * A0 ≠ 0 := ne_of_gt hpos
  have hD : (2:ℝ) * k * A0 * (1 / (2 * k * A0)) = 1 := by field_simp
  show A0 / (1 + 2 * k * A0 * (1 / (2 * k * A0))) = A0 / 2
  rw [hD]
  norm_num

/-- The `2A → P` half-life time is unique. -/
theorem secondOrderAASol_halfLife_unique (A0 k t : ℝ) (hk : 0 < k)
    (hA0 : 0 < A0)
    (h : secondOrderAASol A0 k t = A0 / 2) : t = 1 / (2 * k * A0) := by
  have hA0ne : A0 ≠ 0 := ne_of_gt hA0
  have h2kA0ne : (2:ℝ) * k * A0 ≠ 0 := ne_of_gt (by positivity)
  simp only [secondOrderAASol] at h
  have hDne : 1 + 2 * k * A0 * t ≠ 0 := by
    by_contra hD0
    rw [hD0] at h
    simp only [div_zero] at h
    have hpos2 : (0:ℝ) < A0 / 2 := div_pos hA0 (by norm_num)
    linarith
  rw [div_eq_div_iff hDne (by norm_num : (2:ℝ) ≠ 0)] at h
  have h2 : 1 + 2 * k * A0 * t = 2 := mul_left_cancel₀ hA0ne h.symm
  rw [eq_div_iff h2kA0ne]
  linarith

/-! ## Order 2: A+B with unequal and equal initial amounts -/

/-- `A + B` integrated law for `[A]`, unequal initial amounts. -/
noncomputable def secondOrderABSolA (A0 B0 k : ℝ) (t : ℝ) : ℝ :=
  A0 * (B0 - A0) * Real.exp (-k * (B0 - A0) * t)
    / (B0 - A0 * Real.exp (-k * (B0 - A0) * t))

/-- `A + B` integrated law for `[B]`: `[A](t) + ([B]₀ - [A]₀)`. -/
noncomputable def secondOrderABSolB (A0 B0 k : ℝ) (t : ℝ) : ℝ :=
  secondOrderABSolA A0 B0 k t + (B0 - A0)

/-- The `A + B` solution for `[A]` starts at `[A]₀`. -/
theorem secondOrderABSolA_zero (A0 B0 k : ℝ) (hΔ : B0 - A0 ≠ 0) :
    secondOrderABSolA A0 B0 k 0 = A0 := by
  simp only [secondOrderABSolA, mul_zero, Real.exp_zero, mul_one]
  rw [div_eq_iff hΔ]

/-- The `A + B` solution for `[B]` starts at `[B]₀`. -/
theorem secondOrderABSolB_zero (A0 B0 k : ℝ) (hΔ : B0 - A0 ≠ 0) :
    secondOrderABSolB A0 B0 k 0 = B0 := by
  rw [secondOrderABSolB, secondOrderABSolA_zero A0 B0 k hΔ]
  ring

/-- The `A + B` denominator stays nonzero for `t ≥ 0` when amounts differ. -/
theorem secondOrderAB_denom_ne (A0 B0 k t : ℝ) (hA0 : 0 < A0) (_hB0 : 0 < B0)
    (hk : 0 < k) (hΔ : B0 - A0 ≠ 0) (ht : 0 ≤ t) :
    B0 - A0 * Real.exp (-k * (B0 - A0) * t) ≠ 0 := by
  rcases lt_or_gt_of_ne hΔ with hneg | hpos
  · have hΔle : B0 - A0 ≤ 0 := le_of_lt hneg
    have hx : (0:ℝ) ≤ -k * (B0 - A0) * t := by
      have hnk : -k ≤ 0 := by linarith [hk]
      have h1 : (0:ℝ) ≤ (-k) * (B0 - A0) :=
        mul_nonneg_of_nonpos_of_nonpos hnk (le_of_lt hneg)
      exact mul_nonneg h1 ht
    have hE1 : (1:ℝ) ≤ Real.exp (-k * (B0 - A0) * t) := by
      have h := Real.add_one_le_exp (-k * (B0 - A0) * t)
      linarith
    have hle := mul_le_mul_of_nonneg_left hE1 (le_of_lt hA0)
    have hMneg : B0 - A0 * Real.exp (-k * (B0 - A0) * t) < 0 := by linarith
    exact ne_of_lt hMneg
  · have hΔnn : (0:ℝ) ≤ B0 - A0 := le_of_lt hpos
    have hx0 : (0:ℝ) ≤ k * (B0 - A0) * t := by positivity
    have hE1 : Real.exp (-k * (B0 - A0) * t) ≤ 1 := by
      have hx : -k * (B0 - A0) * t ≤ 0 := by linarith
      exact (Real.exp_le_one_iff).mpr hx
    have hle := mul_le_mul_of_nonneg_left hE1 (le_of_lt hA0)
    have hMpos : (0:ℝ) < B0 - A0 * Real.exp (-k * (B0 - A0) * t) := by linarith
    exact ne_of_gt hMpos

/-- The `A + B` solution for `[A]` satisfies the system ODE. -/
theorem hasDerivAt_secondOrderABSolA (A0 B0 k t : ℝ)
    (hM : B0 - A0 * Real.exp (-k * (B0 - A0) * t) ≠ 0) :
    HasDerivAt (secondOrderABSolA A0 B0 k)
      (-k * (secondOrderABSolA A0 B0 k t)
        * (secondOrderABSolA A0 B0 k t + (B0 - A0))) t := by
  have hE : HasDerivAt (fun s : ℝ => Real.exp (-k * (B0 - A0) * s)) _ t :=
    ((hasDerivAt_id' t).const_mul (-k * (B0 - A0))).exp
  have hN : HasDerivAt
      (fun s : ℝ => A0 * (B0 - A0) * Real.exp (-k * (B0 - A0) * s)) _ t :=
    hE.const_mul (A0 * (B0 - A0))
  have hM' : HasDerivAt
      (fun s : ℝ => B0 - A0 * Real.exp (-k * (B0 - A0) * s)) _ t :=
    (hasDerivAt_const t B0).sub (hE.const_mul A0)
  have hchain : HasDerivAt (fun s : ℝ =>
      A0 * (B0 - A0) * Real.exp (-k * (B0 - A0) * s)
        / (B0 - A0 * Real.exp (-k * (B0 - A0) * s))) _ t :=
    hN.div hM' hM
  have hderiv : deriv (fun s : ℝ =>
        A0 * (B0 - A0) * Real.exp (-k * (B0 - A0) * s)
          / (B0 - A0 * Real.exp (-k * (B0 - A0) * s))) t
      = -k * (A0 * (B0 - A0) * Real.exp (-k * (B0 - A0) * t)
          / (B0 - A0 * Real.exp (-k * (B0 - A0) * t)))
        * ((A0 * (B0 - A0) * Real.exp (-k * (B0 - A0) * t)
          / (B0 - A0 * Real.exp (-k * (B0 - A0) * t))) + (B0 - A0)) := by
    rw [hchain.deriv]
    set E := Real.exp (-k * (B0 - A0) * t) with hEdef
    have hME : B0 - A0 * E ≠ 0 := by rw [hEdef]; exact hM
    have hME2 : (B0 - A0 * E)^2 ≠ 0 := pow_ne_zero 2 hME
    field_simp
    ring
  have hfinal := hchain.differentiableAt.hasDerivAt
  rw [hderiv] at hfinal
  show HasDerivAt (fun s : ℝ =>
      A0 * (B0 - A0) * Real.exp (-k * (B0 - A0) * s)
        / (B0 - A0 * Real.exp (-k * (B0 - A0) * s)))
    (-k * (A0 * (B0 - A0) * Real.exp (-k * (B0 - A0) * t)
        / (B0 - A0 * Real.exp (-k * (B0 - A0) * t)))
      * ((A0 * (B0 - A0) * Real.exp (-k * (B0 - A0) * t)
        / (B0 - A0 * Real.exp (-k * (B0 - A0) * t))) + (B0 - A0))) t
  exact hfinal

/-- The `A + B` solution for `[B]` satisfies the system ODE. -/
theorem hasDerivAt_secondOrderABSolB (A0 B0 k t : ℝ)
    (hM : B0 - A0 * Real.exp (-k * (B0 - A0) * t) ≠ 0) :
    HasDerivAt (secondOrderABSolB A0 B0 k)
      (-k * (secondOrderABSolA A0 B0 k t)
        * (secondOrderABSolB A0 B0 k t)) t := by
  have hA := hasDerivAt_secondOrderABSolA A0 B0 k t hM
  have hchain : HasDerivAt
      (fun s : ℝ => secondOrderABSolA A0 B0 k s + (B0 - A0)) _ t :=
    hA.add (hasDerivAt_const t (B0 - A0))
  have hderiv : deriv (fun s : ℝ => secondOrderABSolA A0 B0 k s + (B0 - A0)) t
      = -k * (secondOrderABSolA A0 B0 k t)
        * (secondOrderABSolB A0 B0 k t) := by
    have e : secondOrderABSolB A0 B0 k t
        = secondOrderABSolA A0 B0 k t + (B0 - A0) := rfl
    rw [hchain.deriv, e]; ring
  have hfinal := hchain.differentiableAt.hasDerivAt
  rw [hderiv] at hfinal
  show HasDerivAt (fun s : ℝ => secondOrderABSolA A0 B0 k s + (B0 - A0))
    (-k * (secondOrderABSolA A0 B0 k t) * (secondOrderABSolB A0 B0 k t)) t
  exact hfinal

/-- The `A + B` solutions conserve `[B] - [A]`. -/
theorem secondOrderABSol_conserved (A0 B0 k t : ℝ) :
    secondOrderABSolB A0 B0 k t - secondOrderABSolA A0 B0 k t = B0 - A0 := by
  simp only [secondOrderABSolB]; ring

/-- Any `A + B` solution pair conserves `[B] - [A]`. -/
theorem ab_conservation (A0 B0 k : ℝ) (gA gB : ℝ → ℝ)
    (hgA : ∀ t : ℝ, 0 ≤ t → HasDerivAt gA (-k * gA t * gB t) t)
    (hgB : ∀ t : ℝ, 0 ≤ t → HasDerivAt gB (-k * gA t * gB t) t)
    (hgA0 : gA 0 = A0) (hgB0 : gB 0 = B0)
    (t : ℝ) (ht : 0 ≤ t) : gB t - gA t = B0 - A0 := by
  have hh : ∀ s : ℝ, 0 ≤ s →
      HasDerivAt (fun s : ℝ => gB s - gA s - (B0 - A0)) 0 s := by
    intro s hs
    have hchain : HasDerivAt (fun s : ℝ => gB s - gA s - (B0 - A0)) _ s :=
      ((hgB s hs).sub (hgA s hs)).sub (hasDerivAt_const s (B0 - A0))
    have hderiv : deriv (fun s : ℝ => gB s - gA s - (B0 - A0)) s = 0 := by
      rw [hchain.deriv]; ring
    have hfinal := hchain.differentiableAt.hasDerivAt
    rw [hderiv] at hfinal
    exact hfinal
  have h0 : (fun s : ℝ => gB s - gA s - (B0 - A0)) 0 = 0 := by
    simp only [hgA0, hgB0, sub_self]
  have heq := eq_of_hasDerivAt_zero _ hh h0 t ht
  have heq' : gB t - gA t - (B0 - A0) = 0 := heq
  linarith

/-- Uniqueness for `A + B` with unequal initial amounts, via `[A]/[B]`. -/
theorem secondOrderABSol_unique (A0 B0 k : ℝ) (gA gB : ℝ → ℝ)
    (hA0 : 0 < A0) (hB0 : 0 < B0) (hk : 0 < k) (hΔ : B0 - A0 ≠ 0)
    (hgA : ∀ t : ℝ, 0 ≤ t → HasDerivAt gA (-k * gA t * gB t) t)
    (hgB : ∀ t : ℝ, 0 ≤ t → HasDerivAt gB (-k * gA t * gB t) t)
    (_hposA : ∀ t : ℝ, 0 ≤ t → 0 < gA t)
    (hposB : ∀ t : ℝ, 0 ≤ t → 0 < gB t)
    (hgA0 : gA 0 = A0) (hgB0 : gB 0 = B0)
    (t : ℝ) (ht : 0 ≤ t) : gA t = secondOrderABSolA A0 B0 k t := by
  have hcons : ∀ s : ℝ, 0 ≤ s → gB s - gA s = B0 - A0 :=
    fun s hs => ab_conservation A0 B0 k gA gB hgA hgB hgA0 hgB0 s hs
  have hu_ode : ∀ s : ℝ, 0 ≤ s →
      HasDerivAt (fun s : ℝ => gA s / gB s)
        (-(k * (B0 - A0)) * (gA s / gB s)) s := by
    intro s hs
    have hchain : HasDerivAt (fun s : ℝ => gA s / gB s) _ s :=
      (hgA s hs).div (hgB s hs) (ne_of_gt (hposB s hs))
    have hderiv : deriv (fun s : ℝ => gA s / gB s) s
        = -(k * (B0 - A0)) * (gA s / gB s) := by
      rw [hchain.deriv]
      have hd := hcons s hs
      have hgBs : gB s = gA s + (B0 - A0) := by linarith
      have hBne : gB s ≠ 0 := ne_of_gt (hposB s hs)
      have hB2 : (gB s)^2 ≠ 0 := pow_ne_zero 2 hBne
      rw [hgBs] at hBne hB2 ⊢
      field_simp; ring
    have hfinal := hchain.differentiableAt.hasDerivAt
    rw [hderiv] at hfinal
    exact hfinal
  have hu0 : gA 0 / gB 0 = A0 / B0 := by rw [hgA0, hgB0]
  have hu : ∀ s : ℝ, 0 ≤ s → (fun s : ℝ => gA s / gB s) s
      = firstOrderSol (A0 / B0) (k * (B0 - A0)) s :=
    fun s hs => firstOrderSol_unique (A0 / B0) (k * (B0 - A0))
      (fun s => gA s / gB s) hu_ode hu0 s hs
  have key : ∀ s : ℝ, 0 ≤ s → gA s = secondOrderABSolA A0 B0 k s := by
    intro s hs
    have hd : gB s - gA s = B0 - A0 := hcons s hs
    have hgBs : gB s = gA s + (B0 - A0) := by linarith
    have hBne : gB s ≠ 0 := ne_of_gt (hposB s hs)
    have hB0ne : B0 ≠ 0 := ne_of_gt hB0
    have hEarg : (-(k * (B0 - A0))) * s = -k * (B0 - A0) * s := by ring
    have hu_s : gA s / gB s = (A0 / B0) * Real.exp (-k * (B0 - A0) * s) := by
      have h := hu s hs
      simp only [firstOrderSol] at h
      rw [hEarg] at h
      exact h
    have h1u : 1 - gA s / gB s = (B0 - A0) / gB s := by
      have hBeq : gA s + (B0 - A0) ≠ 0 := by rw [← hgBs]; exact hBne
      rw [hgBs]
      field_simp; ring
    have h1mrE : (1:ℝ) - (A0 / B0) * Real.exp (-k * (B0 - A0) * s) ≠ 0 := by
      rw [← hu_s, h1u]
      exact div_ne_zero hΔ hBne
    have hmul : gA s = (A0 / B0) * Real.exp (-k * (B0 - A0) * s) * gB s := by
      rw [← hu_s]
      field_simp
    rw [hgBs] at hmul
    have hsol : gA s = (A0 / B0) * Real.exp (-k * (B0 - A0) * s) * (B0 - A0)
        / (1 - (A0 / B0) * Real.exp (-k * (B0 - A0) * s)) := by
      rw [eq_div_iff h1mrE]
      linarith [hmul]
    have hbridge : (A0 / B0) * Real.exp (-k * (B0 - A0) * s) * (B0 - A0)
          / (1 - (A0 / B0) * Real.exp (-k * (B0 - A0) * s))
        = secondOrderABSolA A0 B0 k s := by
      have hM : B0 - A0 * Real.exp (-k * (B0 - A0) * s) ≠ 0 :=
        secondOrderAB_denom_ne A0 B0 k s hA0 hB0 hk hΔ hs
      show (A0 / B0) * Real.exp (-k * (B0 - A0) * s) * (B0 - A0)
          / (1 - (A0 / B0) * Real.exp (-k * (B0 - A0) * s))
        = A0 * (B0 - A0) * Real.exp (-k * (B0 - A0) * s)
          / (B0 - A0 * Real.exp (-k * (B0 - A0) * s))
      rw [div_eq_div_iff h1mrE hM]
      field_simp
    exact hsol.trans hbridge
  exact key t ht

/-- `A + B` integrated law with equal initial amounts. -/
noncomputable def secondOrderABEqualSol (A0 k : ℝ) (t : ℝ) : ℝ := A0 / (1 + k * A0 * t)

/-- The equal-initial-amounts solution starts at `[A]₀`. -/
theorem secondOrderABEqualSol_zero (A0 k : ℝ) :
    secondOrderABEqualSol A0 k 0 = A0 := by
  simp [secondOrderABEqualSol]

/-- The equal-initial-amounts denominator stays positive for `t ≥ 0`. -/
theorem secondOrderABEqualSol_denom_pos (A0 k t : ℝ) (hk : 0 < k)
    (hA0 : 0 < A0) (ht : 0 ≤ t) : 0 < 1 + k * A0 * t := by positivity

/-- The equal-initial-amounts solution stays positive for `t ≥ 0`. -/
theorem secondOrderABEqualSol_pos (A0 k t : ℝ) (hk : 0 < k) (hA0 : 0 < A0)
    (ht : 0 ≤ t) : 0 < secondOrderABEqualSol A0 k t := by
  show 0 < A0 / (1 + k * A0 * t)
  exact div_pos hA0 (secondOrderABEqualSol_denom_pos A0 k t hk hA0 ht)

/-- The equal-initial-amounts solution satisfies `f' = -k f²`. -/
theorem hasDerivAt_secondOrderABEqualSol (A0 k t : ℝ)
    (hM : 1 + k * A0 * t ≠ 0) :
    HasDerivAt (secondOrderABEqualSol A0 k)
      (-k * (secondOrderABEqualSol A0 k t)^2) t := by
  have hM' : HasDerivAt (fun s : ℝ => 1 + k * A0 * s) _ t :=
    ((hasDerivAt_id' t).const_mul (k * A0)).const_add 1
  have hchain : HasDerivAt (fun s : ℝ => A0 / (1 + k * A0 * s)) _ t :=
    (hasDerivAt_const t A0).div hM' hM
  have hderiv : deriv (fun s : ℝ => A0 / (1 + k * A0 * s)) t
      = -k * (A0 / (1 + k * A0 * t))^2 := by
    rw [hchain.deriv]
    have hM2 : (1 + k * A0 * t)^2 ≠ 0 := pow_ne_zero 2 hM
    field_simp; ring
  have hfinal := hchain.differentiableAt.hasDerivAt
  rw [hderiv] at hfinal
  show HasDerivAt (fun s : ℝ => A0 / (1 + k * A0 * s))
    (-k * (A0 / (1 + k * A0 * t))^2) t
  exact hfinal

/-- Uniqueness for `A + B` with equal initial amounts. -/
theorem secondOrderABEqualSol_unique (A0 k : ℝ) (gA gB : ℝ → ℝ)
    (hA0 : 0 < A0) (hk : 0 < k)
    (hgA : ∀ t : ℝ, 0 ≤ t → HasDerivAt gA (-k * gA t * gB t) t)
    (hgB : ∀ t : ℝ, 0 ≤ t → HasDerivAt gB (-k * gA t * gB t) t)
    (hposA : ∀ t : ℝ, 0 ≤ t → 0 < gA t)
    (hgA0 : gA 0 = A0) (hgB0 : gB 0 = A0)
    (t : ℝ) (ht : 0 ≤ t) : gA t = secondOrderABEqualSol A0 k t := by
  have hcons : ∀ s : ℝ, 0 ≤ s → gB s - gA s = A0 - A0 :=
    fun s hs => ab_conservation A0 A0 k gA gB hgA hgB hgA0 hgB0 s hs
  have hgA' : ∀ s : ℝ, 0 ≤ s → HasDerivAt gA (-k * (gA s)^2) s := by
    intro s hs
    have h := hgA s hs
    have hgBeq : gB s = gA s := by
      have hc := hcons s hs
      linarith
    have hderiv : deriv gA s = -k * (gA s)^2 := by
      rw [h.deriv, hgBeq]
      ring
    have hfinal := h.differentiableAt.hasDerivAt
    rw [hderiv] at hfinal
    exact hfinal
  have hgen := secondOrderGen_unique A0 k gA hk hA0 hgA' hposA hgA0 t ht
  exact hgen

/-- Equal-initial-amounts half-life: `1 / (k[A]₀)`. -/
theorem secondOrderABEqualSol_halfLife (A0 k : ℝ) (hk : 0 < k) (hA0 : 0 < A0) :
    secondOrderABEqualSol A0 k (1 / (k * A0)) = A0 / 2 := by
  have hpos : (0:ℝ) < k * A0 := by positivity
  have hne : k * A0 ≠ 0 := ne_of_gt hpos
  have hD : k * A0 * (1 / (k * A0)) = 1 := by field_simp
  show A0 / (1 + k * A0 * (1 / (k * A0))) = A0 / 2
  rw [hD]
  norm_num

/-! ## Half-lives -/

/-- Half-life by order: `[A]₀/(2k)`, `ln 2/k`, `1/(2k[A]₀)`. -/
noncomputable def halfLife (n : ℕ) (k A0 : ℝ) : ℝ :=
  match n with
  | 0 => A0 / (2 * k)
  | 1 => Real.log 2 / k
  | _ => 1 / (2 * k * A0)

/-- `halfLife 0` halves the zero-order solution. -/
theorem halfLife_correct_zero (A0 k : ℝ) (hk : 0 < k) (hA0 : 0 < A0) :
    zeroOrderSol A0 k (halfLife 0 k A0) = A0 / 2 := by
  show zeroOrderSol A0 k (A0 / (2 * k)) = A0 / 2
  exact zeroOrderSol_halfLife A0 k hk hA0

/-- `halfLife 1` halves the first-order solution. -/
theorem halfLife_correct_first (A0 k : ℝ) (hk : 0 < k) (hA0 : 0 < A0) :
    firstOrderSol A0 k (halfLife 1 k A0) = A0 / 2 := by
  show firstOrderSol A0 k (Real.log 2 / k) = A0 / 2
  exact firstOrderSol_halfLife A0 k hk hA0

/-- `halfLife 2` halves the `2A → P` solution. -/
theorem halfLife_correct_second (A0 k : ℝ) (hk : 0 < k) (hA0 : 0 < A0) :
    secondOrderAASol A0 k (halfLife 2 k A0) = A0 / 2 := by
  show secondOrderAASol A0 k (1 / (2 * k * A0)) = A0 / 2
  exact secondOrderAASol_halfLife A0 k hk hA0

/-- Among orders `{0, 1, 2}`, the half-life ignores `[A]₀` iff first order. -/
theorem halfLife_indep_iff_first_order (n : ℕ) (k : ℝ)
    (hn : n = 0 ∨ n = 1 ∨ n = 2) (hk : 0 < k) :
    ((∀ A0 A0' : ℝ, 0 < A0 → 0 < A0' →
      halfLife n k A0 = halfLife n k A0') ↔ n = 1) := by
  rcases hn with rfl | rfl | rfl
  · constructor
    · intro h
      exfalso
      have h2 := h 1 2 (by norm_num) (by norm_num)
      have hcon : (1:ℝ) / (2 * k) = 2 / (2 * k) := h2
      have h2kne : (2:ℝ) * k ≠ 0 := ne_of_gt (by positivity)
      rw [div_eq_div_iff h2kne h2kne] at hcon
      linarith
    · intro h01
      exact absurd h01 (by decide)
  · constructor
    · intro _
      rfl
    · intro _ A0 A0' _ _
      rfl
  · constructor
    · intro h
      exfalso
      have h2 := h 1 2 (by norm_num) (by norm_num)
      have hcon : (1:ℝ) / (2 * k * 1) = 1 / (2 * k * 2) := h2
      have h2k1 : (2:ℝ) * k * 1 ≠ 0 := ne_of_gt (by positivity)
      have h2k2 : (2:ℝ) * k * 2 ≠ 0 := ne_of_gt (by positivity)
      rw [div_eq_div_iff h2k1 h2k2] at hcon
      linarith
    · intro h21
      exact absurd h21 (by decide)

/-! ## Rate-constant units via the dimensionless group -/

/-- Dimensionless group `k t [A]₀^(n-1)` fixing the units of `k`. -/
noncomputable def rateGroup (n : ℕ) (k t A0 : ℝ) : ℝ := k * t * A0 ^ ((n:ℤ) - 1)

/-- The order-0 rate group is `kt / [A]₀`. -/
theorem rateGroup_zero (k t A0 : ℝ) : rateGroup 0 k t A0 = k * t / A0 := by
  have e : ((0:ℕ):ℤ) - 1 = -1 := by norm_num
  simp only [rateGroup, e, zpow_neg_one]
  rw [div_eq_mul_inv]

/-- The order-1 rate group is `kt`. -/
theorem rateGroup_one (k t A0 : ℝ) : rateGroup 1 k t A0 = k * t := by
  have e : ((1:ℕ):ℤ) - 1 = 0 := by norm_num
  simp only [rateGroup, e, zpow_zero, mul_one]

/-- The order-2 rate group is `kt[A]₀`. -/
theorem rateGroup_two (k t A0 : ℝ) : rateGroup 2 k t A0 = k * t * A0 := by
  have e : ((2:ℕ):ℤ) - 1 = 1 := by norm_num
  simp only [rateGroup, e, zpow_one]

/-- `k` in units of the group: concentration^(1-n) per time. -/
theorem k_of_rateGroup (n : ℕ) (k t A0 : ℝ) (ht : t ≠ 0) (hA0 : 0 < A0) :
    rateGroup n k t A0 / (t * A0 ^ ((n:ℤ) - 1)) = k := by
  have he : (0:ℝ) < A0 ^ ((n:ℤ) - 1) := by positivity
  rw [div_eq_iff (mul_ne_zero ht (ne_of_gt he))]
  simp only [rateGroup]
  ring

/-- First-order solution in terms of the rate group. -/
theorem firstOrderSol_rateGroup (A0 k t : ℝ) :
    firstOrderSol A0 k t = A0 * Real.exp (-(rateGroup 1 k t A0)) := by
  simp only [firstOrderSol, rateGroup_one]
  congr 1
  congr 1
  ring

/-- `2A → P` solution in terms of the rate group. -/
theorem secondOrderAASol_rateGroup (A0 k t : ℝ) :
    secondOrderAASol A0 k t = A0 / (1 + 2 * rateGroup 2 k t A0) := by
  simp only [secondOrderAASol, rateGroup_two]
  congr 1
  ring

/-- Zero-order solution in terms of the rate group. -/
theorem zeroOrderSol_rateGroup (A0 k t : ℝ) (hA0 : A0 ≠ 0) :
    zeroOrderSol A0 k t = A0 * (1 - rateGroup 0 k t A0) := by
  rw [rateGroup_zero k t A0]
  simp only [zeroOrderSol]
  field_simp

/-! ## Pseudo-first-order approximation -/

/-- Observed pseudo-first-order constant `k[B]₀`. -/
def pfoRateConst (B0 k : ℝ) : ℝ := k * B0

/-- Pseudo-first-order approximation `[A]₀ exp(-k[B]₀t)`. -/
noncomputable def pfoSol (A0 B0 k : ℝ) (t : ℝ) : ℝ := A0 * Real.exp (-(k * B0) * t)

/-- The pseudo-first-order approximation starts at `[A]₀`. -/
theorem pfoSol_zero (A0 B0 k : ℝ) : pfoSol A0 B0 k 0 = A0 := by
  simp [pfoSol]

/-- The pseudo-first-order approximation satisfies its ODE. -/
theorem hasDerivAt_pfoSol (A0 B0 k t : ℝ) :
    HasDerivAt (pfoSol A0 B0 k) (-(pfoRateConst B0 k) * pfoSol A0 B0 k t) t :=
  hasDerivAt_firstOrderSol A0 (k * B0) t

/-- Excess ratio `r = [A]₀ / [B]₀`. -/
noncomputable def pfoRatio (A0 B0 : ℝ) : ℝ := A0 / B0

/-- Pseudo-first-order error bound, explicit in `r`. -/
theorem pfo_error_bound (A0 B0 k t : ℝ) (hA0 : 0 < A0) (hB0 : 0 < B0)
    (hk : 0 < k) (hlt : A0 < B0) (ht : 0 ≤ t) :
    |secondOrderABSolA A0 B0 k t - pfoSol A0 B0 k t|
      ≤ A0 * pfoRatio A0 B0 * (1 / (1 - pfoRatio A0 B0) + k * B0 * t) := by
  simp only [pfoRatio]
  have hΔ : (0:ℝ) < B0 - A0 := sub_pos.mpr hlt
  have hΔne : B0 - A0 ≠ 0 := ne_of_gt hΔ
  have hB0ne : B0 ≠ 0 := ne_of_gt hB0
  have hr0 : (0:ℝ) < A0 / B0 := div_pos hA0 hB0
  have hr1 : A0 / B0 < 1 := (div_lt_one hB0).mpr hlt
  have h1mr : (0:ℝ) < 1 - A0 / B0 := by linarith
  have h1mrne : (1:ℝ) - A0 / B0 ≠ 0 := ne_of_gt h1mr
  have hΔnn : (0:ℝ) ≤ B0 - A0 := le_of_lt hΔ
  have hx0 : (0:ℝ) ≤ k * (B0 - A0) * t := by positivity
  have hE0 : (0:ℝ) < Real.exp (-k * (B0 - A0) * t) := Real.exp_pos _
  have hE1 : Real.exp (-k * (B0 - A0) * t) ≤ 1 := by
    have hx : -k * (B0 - A0) * t ≤ 0 := by linarith
    exact (Real.exp_le_one_iff).mpr hx
  have hM : B0 - A0 * Real.exp (-k * (B0 - A0) * t) ≠ 0 :=
    secondOrderAB_denom_ne A0 B0 k t hA0 hB0 hk hΔne ht
  have h1mrE : (0:ℝ) < 1 - (A0 / B0) * Real.exp (-k * (B0 - A0) * t) := by
    have hle : (A0 / B0) * Real.exp (-k * (B0 - A0) * t) ≤ (A0 / B0) * 1 :=
      mul_le_mul_of_nonneg_left hE1 (le_of_lt hr0)
    have hlt1 : (A0 / B0) * Real.exp (-k * (B0 - A0) * t) < 1 := by
      linarith [hle, hr1]
    linarith
  have h1mrEne : (1:ℝ) - (A0 / B0) * Real.exp (-k * (B0 - A0) * t) ≠ 0 :=
    ne_of_gt h1mrE
  have hexp : Real.exp (-(k * B0) * t)
      = Real.exp (-k * (B0 - A0) * t) * Real.exp (-k * A0 * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hdecomp : secondOrderABSolA A0 B0 k t - pfoSol A0 B0 k t
      = A0 * Real.exp (-k * (B0 - A0) * t)
        * ((1 - A0 / B0) / (1 - (A0 / B0) * Real.exp (-k * (B0 - A0) * t))
          - Real.exp (-k * A0 * t)) := by
    simp only [secondOrderABSolA, pfoSol]
    rw [hexp]
    field_simp
  have hT1 : |(1 - A0 / B0) / (1 - (A0 / B0) * Real.exp (-k * (B0 - A0) * t)) - 1|
      ≤ (A0 / B0) / (1 - A0 / B0) := by
    have heq : (1 - A0 / B0) / (1 - (A0 / B0) * Real.exp (-k * (B0 - A0) * t)) - 1
        = -((A0 / B0) * (1 - Real.exp (-k * (B0 - A0) * t))
          / (1 - (A0 / B0) * Real.exp (-k * (B0 - A0) * t))) := by
      set E := Real.exp (-k * (B0 - A0) * t) with hEdef
      have hME : B0 - A0 * E ≠ 0 := by rw [hEdef]; exact hM
      have h1E : 1 - A0 / B0 * E ≠ 0 := by rw [hEdef]; exact h1mrEne
      field_simp
      ring
    rw [heq, abs_neg]
    have hnn1 : (0:ℝ) ≤ (A0 / B0) * (1 - Real.exp (-k * (B0 - A0) * t)) :=
      mul_nonneg (le_of_lt hr0) (sub_nonneg.mpr hE1)
    have hdivnn : (0:ℝ) ≤ (A0 / B0) * (1 - Real.exp (-k * (B0 - A0) * t))
        / (1 - (A0 / B0) * Real.exp (-k * (B0 - A0) * t)) :=
      div_nonneg hnn1 (le_of_lt h1mrE)
    rw [abs_of_nonneg hdivnn, div_le_div_iff₀ h1mrE h1mr]
    have key : (A0 / B0) * (1 - Real.exp (-k * (B0 - A0) * t)) * (1 - A0 / B0)
        + ((A0 / B0) * (A0 / B0) * (1 - Real.exp (-k * (B0 - A0) * t))
          + (A0 / B0) * Real.exp (-k * (B0 - A0) * t) * (1 - A0 / B0))
        = (A0 / B0) * (1 - (A0 / B0) * Real.exp (-k * (B0 - A0) * t)) := by
      ring
    have hnn2 : (0:ℝ) ≤ (A0 / B0) * (A0 / B0) * (1 - Real.exp (-k * (B0 - A0) * t))
        + (A0 / B0) * Real.exp (-k * (B0 - A0) * t) * (1 - A0 / B0) :=
      add_nonneg
        (mul_nonneg (mul_nonneg (le_of_lt hr0) (le_of_lt hr0)) (sub_nonneg.mpr hE1))
        (mul_nonneg (mul_nonneg (le_of_lt hr0) (le_of_lt hE0)) (le_of_lt h1mr))
    linarith
  have hT2 : |1 - Real.exp (-k * A0 * t)| ≤ k * A0 * t := by
    have hx : (0:ℝ) ≤ k * A0 * t := by positivity
    have hle : Real.exp (-k * A0 * t) ≤ 1 := by
      have hx' : -k * A0 * t ≤ 0 := by linarith
      exact (Real.exp_le_one_iff).mpr hx'
    have hnn : (0:ℝ) ≤ 1 - Real.exp (-k * A0 * t) := sub_nonneg.mpr hle
    have hge := Real.add_one_le_exp (-k * A0 * t)
    rw [abs_of_nonneg hnn]
    linarith
  have htri : |(1 - A0 / B0) / (1 - (A0 / B0) * Real.exp (-k * (B0 - A0) * t))
        - Real.exp (-k * A0 * t)|
      ≤ |(1 - A0 / B0) / (1 - (A0 / B0) * Real.exp (-k * (B0 - A0) * t)) - 1|
        + |1 - Real.exp (-k * A0 * t)| := by
    calc |(1 - A0 / B0) / (1 - (A0 / B0) * Real.exp (-k * (B0 - A0) * t))
          - Real.exp (-k * A0 * t)|
        = |(((1 - A0 / B0) / (1 - (A0 / B0) * Real.exp (-k * (B0 - A0) * t)) - 1)
          + (1 - Real.exp (-k * A0 * t)))| := by
          congr 1
          ring
      _ ≤ _ := abs_add_le _ _
  have hYnn : (0:ℝ)
      ≤ |(1 - A0 / B0) / (1 - (A0 / B0) * Real.exp (-k * (B0 - A0) * t)) - 1|
        + |1 - Real.exp (-k * A0 * t)| :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hA0E : (0:ℝ) < A0 * Real.exp (-k * (B0 - A0) * t) := mul_pos hA0 hE0
  rw [hdecomp, abs_mul, abs_of_pos hA0E]
  have s1 : A0 * Real.exp (-k * (B0 - A0) * t)
        * |(1 - A0 / B0) / (1 - (A0 / B0) * Real.exp (-k * (B0 - A0) * t))
          - Real.exp (-k * A0 * t)|
      ≤ A0 * Real.exp (-k * (B0 - A0) * t)
        * (|(1 - A0 / B0) / (1 - (A0 / B0) * Real.exp (-k * (B0 - A0) * t)) - 1|
          + |1 - Real.exp (-k * A0 * t)|) :=
    mul_le_mul_of_nonneg_left htri (le_of_lt hA0E)
  have s2 : A0 * Real.exp (-k * (B0 - A0) * t)
        * (|(1 - A0 / B0) / (1 - (A0 / B0) * Real.exp (-k * (B0 - A0) * t)) - 1|
          + |1 - Real.exp (-k * A0 * t)|)
      ≤ A0 * (|(1 - A0 / B0) / (1 - (A0 / B0) * Real.exp (-k * (B0 - A0) * t))
          - 1| + |1 - Real.exp (-k * A0 * t)|) := by
    have hE1' : Real.exp (-k * (B0 - A0) * t)
          * (|(1 - A0 / B0) / (1 - (A0 / B0) * Real.exp (-k * (B0 - A0) * t))
            - 1| + |1 - Real.exp (-k * A0 * t)|)
        ≤ 1 * (|(1 - A0 / B0) / (1 - (A0 / B0) * Real.exp (-k * (B0 - A0) * t))
            - 1| + |1 - Real.exp (-k * A0 * t)|) :=
      mul_le_mul_of_nonneg_right hE1 hYnn
    have hA := mul_le_mul_of_nonneg_left hE1' (le_of_lt hA0)
    linarith
  have s3 : A0 * (|(1 - A0 / B0) / (1 - (A0 / B0) * Real.exp (-k * (B0 - A0) * t))
          - 1| + |1 - Real.exp (-k * A0 * t)|)
      ≤ A0 * ((A0 / B0) / (1 - A0 / B0) + k * A0 * t) :=
    mul_le_mul_of_nonneg_left (add_le_add hT1 hT2) (le_of_lt hA0)
  have hfin : A0 * ((A0 / B0) / (1 - A0 / B0) + k * A0 * t)
      = A0 * (A0 / B0) * (1 / (1 - A0 / B0) + k * B0 * t) := by
    field_simp
  rw [← hfin]
  linarith [s1, s2, s3]

/-- Relative pseudo-first-order error bound. -/
theorem pfo_rel_error_bound (A0 B0 k t : ℝ) (hA0 : 0 < A0) (hB0 : 0 < B0)
    (hk : 0 < k) (hlt : A0 < B0) (ht : 0 ≤ t) :
    |secondOrderABSolA A0 B0 k t - pfoSol A0 B0 k t| / A0
      ≤ pfoRatio A0 B0 * (1 / (1 - pfoRatio A0 B0) + k * B0 * t) := by
  rw [div_le_iff₀ hA0]
  calc |secondOrderABSolA A0 B0 k t - pfoSol A0 B0 k t|
      ≤ A0 * pfoRatio A0 B0 * (1 / (1 - pfoRatio A0 B0) + k * B0 * t) :=
        pfo_error_bound A0 B0 k t hA0 hB0 hk hlt ht
    _ = pfoRatio A0 B0 * (1 / (1 - pfoRatio A0 B0) + k * B0 * t) * A0 := by
        ring

end Chemistry.Kinetics
