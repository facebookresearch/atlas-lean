/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Operating-point linearization (small-signal model)

## i. Overview

The small-signal model of a smooth device law `f` at an operating
point: the remainder of the first-order Taylor approximation is
bounded by half the second-derivative bound times the square of
the deviation, on any segment where the stated bound on the
second derivative (in the Pi sup norm, not an Euclidean Hessian
norm) holds. The bound is attained by a quadratic device law, so
the constant `1/2` is exact. Piecewise device laws inherit nothing
here: each lemma uses exactly the smoothness it states, and the
second-derivative bound itself is only evaluated on the box or
segment in question.

## ii. Key results

- `smallSignal_remainder_le_of_hessian_bound`: the remainder
  bound from a second-derivative bound along the segment.
- `smallSignal_remainder_le_of_segment_bound`: the same bound
  from a bound on the derivative's Lipschitz constant.
- `smallSignal_quadratic_attains_factor`: a quadratic law
  attains the factor `1/2`, so it cannot be improved in general.

## iii. Table of contents

- A. The small-signal remainder bound

## iv. References

- A. S. Sedra and K. C. Smith, *Microelectronic Circuits*, eighth
  edition, Oxford University Press, 2020: small-signal models of
  nonlinear devices at an operating point and the quadratic
  remainder of the linearization.

## A. The small-signal remainder bound

Discharges ECE roadmap leaf `ECE.EL.SMALLSIGNAL.L1` (small-signal
operating-point linearization).
-/

@[expose] public section

/-- Membership in a closed interval from membership in the open interval. -/
private theorem mem_Icc_of_mem_Ioo {x a b : ℝ} (h : x ∈ Set.Ioo a b) :
    x ∈ Set.Icc a b :=
  Set.mem_Icc.mpr ⟨le_of_lt (Set.mem_Ioo.mp h).1, le_of_lt (Set.mem_Ioo.mp h).2⟩

/-- Membership in `[0, 1]` from membership in `(0, c)` with `c < 1`. -/
private theorem mem_Icc_of_mem_Ioo_of_lt {x c : ℝ} (h : x ∈ Set.Ioo 0 c)
    (hc : c < 1) : x ∈ Set.Icc (0 : ℝ) 1 :=
  Set.mem_Icc.mpr ⟨le_of_lt (Set.mem_Ioo.mp h).1,
    le_trans (le_of_lt (Set.mem_Ioo.mp h).2) (le_of_lt hc)⟩

/-- One-dimensional first-order Taylor bound: for `g : ℝ → ℝ` of class `C²`
with `|g'' t| ≤ K` on `[0, 1]`, `|g 1 - g 0 - g' 0| ≤ K / 2`.
Proved by applying Rolle's theorem twice. -/
private theorem abs_taylor_remainder_le_of_second_deriv_bound (g : ℝ → ℝ) (K : ℝ)
    (hC2 : ContDiff ℝ 2 g)
    (hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv g) t| ≤ K) :
    |g 1 - g 0 - deriv g 0| ≤ K / 2 := by
  have hdiff1 : Differentiable ℝ g := hC2.differentiable (by decide)
  have hdeq : deriv g = fun x => (fderiv ℝ g x) 1 := by
    apply deriv_eq
    intro x
    exact (hdiff1 x).hasDerivAt
  have hC1fderiv : ContDiff ℝ 1 (fderiv ℝ g) := by
    have hh1 : ContDiff ℝ 2 (Function.uncurry fun _ : ℝ => g) :=
      hC2.comp contDiff_snd
    have hh2 : ContDiff ℝ (1 : WithTop ℕ∞) (id : ℝ → ℝ) := contDiff_id
    have hh3 : (1 : WithTop ℕ∞) + 1 ≤ 2 := by decide
    exact ContDiff.fderiv (f := fun _ : ℝ => g) (g := id) hh1 hh2 hh3
  have hDat : ∀ x, DifferentiableAt ℝ (fderiv ℝ g) x := fun x =>
    (hC1fderiv.contDiffAt (x := x)).differentiableAt (by decide)
  have hdiffD : Differentiable ℝ (deriv g) := by
    set E1 : (ℝ →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ 1 with hE1def
    have hE1app : ∀ L : ℝ →L[ℝ] ℝ, E1 L = L 1 := fun L => rfl
    have hcomp : Differentiable ℝ (E1 ∘ fderiv ℝ g) := by
      intro x
      exact DifferentiableAt.comp x E1.differentiableAt (hDat x)
    have hfun2 : (fun x => (fderiv ℝ g x) 1) = E1 ∘ fderiv ℝ g := by
      funext x
      simp [Function.comp_apply, hE1app]
    rw [hdeq, hfun2]
    exact hcomp
  set R : ℝ := g 1 - g 0 - deriv g 0 with hRdef
  set φ : ℝ → ℝ := fun t => g t - g 0 - t * deriv g 0 - (t * t) * R with hφdef
  set ψ : ℝ → ℝ := fun t => (deriv g t - 1 * deriv g 0) - (1 * t + t * 1) * R
    with hψdef
  have hid : ∀ x : ℝ, HasDerivAt (fun t : ℝ => t) 1 x := fun x => hasDerivAt_id' x
  have hφderivG : ∀ x : ℝ,
      HasDerivAt φ ((deriv g x - 1 * deriv g 0) - (1 * x + x * 1) * R) x := by
    intro x
    have hgx : HasDerivAt g (deriv g x) x := (hdiff1 x).hasDerivAt
    have h1 : HasDerivAt (fun t : ℝ => g t - g 0) (deriv g x) x :=
      hgx.sub_const (g 0)
    have h2 : HasDerivAt (fun t : ℝ => t * deriv g 0) (1 * deriv g 0) x :=
      (hid x).mul_const (deriv g 0)
    have hA : HasDerivAt (fun t : ℝ => (g t - g 0) - t * deriv g 0)
        (deriv g x - 1 * deriv g 0) x := h1.sub h2
    have hsq : HasDerivAt (fun t : ℝ => t * t) (1 * x + x * 1) x :=
      (hid x).mul (hid x)
    have hB : HasDerivAt (fun t : ℝ => (t * t) * R) ((1 * x + x * 1) * R) x :=
      hsq.mul_const R
    have hφ := hA.sub hB
    have hfunEqφ : φ = (fun t : ℝ => (g t - g 0) - t * deriv g 0)
        - (fun t : ℝ => (t * t) * R) := by
      funext t
      simp [hφdef, Pi.sub_apply]
    rw [hfunEqφ]
    exact hφ
  have hφderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt φ ((deriv g x - 1 * deriv g 0) - (1 * x + x * 1) * R) x :=
    fun x _ => hφderivG x
  have hφcont : ContinuousOn φ (Set.Icc (0 : ℝ) 1) := by
    have hcontAt : ∀ x : ℝ, ContinuousAt φ x := fun x => (hφderivG x).continuousAt
    exact (continuous_iff_continuousAt.mpr hcontAt).continuousOn
  have hφends : φ 0 = φ 1 := by simp [hφdef, hRdef]
  have h01 : (0 : ℝ) < 1 := by norm_num
  obtain ⟨c, hcmem, hc⟩ := exists_hasDerivAt_eq_zero h01 hφcont hφends hφderiv
  have hcmem' : 0 < c ∧ c < 1 := Set.mem_Ioo.mp hcmem
  have hψderivG : ∀ x : ℝ,
      HasDerivAt ψ (deriv (deriv g) x - (1 * 1 + 1 * 1) * R) x := by
    intro x
    have hDx : HasDerivAt (deriv g) (deriv (deriv g) x) x := (hdiffD x).hasDerivAt
    have h1 : HasDerivAt (fun t : ℝ => deriv g t - 1 * deriv g 0)
        (deriv (deriv g) x) x :=
      hDx.sub_const (1 * deriv g 0)
    have h2a : HasDerivAt (fun t : ℝ => 1 * t) (1 * 1) x := (hid x).const_mul 1
    have h2b : HasDerivAt (fun t : ℝ => t * 1) (1 * 1) x := (hid x).mul_const 1
    have h2 : HasDerivAt (fun t : ℝ => 1 * t + t * 1) (1 * 1 + 1 * 1) x :=
      h2a.add h2b
    have hB : HasDerivAt (fun t : ℝ => (1 * t + t * 1) * R) ((1 * 1 + 1 * 1) * R)
        x := h2.mul_const R
    have hψ := h1.sub hB
    have hfunEqψ : ψ = (fun t : ℝ => deriv g t - 1 * deriv g 0)
        - (fun t : ℝ => (1 * t + t * 1) * R) := by
      funext t
      simp [hψdef, Pi.sub_apply]
    rw [hfunEqψ]
    exact hψ
  have hψderiv : ∀ x ∈ Set.Ioo (0 : ℝ) c,
      HasDerivAt ψ (deriv (deriv g) x - (1 * 1 + 1 * 1) * R) x :=
    fun x _ => hψderivG x
  have hψcont : ContinuousOn ψ (Set.Icc (0 : ℝ) c) := by
    have hcontAt : ∀ x : ℝ, ContinuousAt ψ x := fun x => (hψderivG x).continuousAt
    exact (continuous_iff_continuousAt.mpr hcontAt).continuousOn
  have hψc : ψ c = 0 := by simpa [hψdef] using hc
  have hψ0 : ψ 0 = 0 := by simp [hψdef]
  have hψends : ψ 0 = ψ c := hψ0.trans hψc.symm
  obtain ⟨d, hdmemi, hd⟩ :=
    exists_hasDerivAt_eq_zero hcmem'.1 hψcont hψends hψderiv
  have h2val : (1 : ℝ) * 1 + 1 * 1 = 2 := by norm_num
  rw [h2val] at hd
  have hR : R = deriv (deriv g) d / 2 := by linarith
  have hdmem : d ∈ Set.Icc (0 : ℝ) 1 := mem_Icc_of_mem_Ioo_of_lt hdmemi hcmem'.2
  have hK := hseg d hdmem
  have h2abs : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
  calc |R| = |deriv (deriv g) d| / 2 := by rw [hR, abs_div, h2abs]
    _ ≤ K / 2 := by linarith [hK]

namespace PhyslibExt.Electronics.OperatingPointLinearization

/-- The one-dimensional segment pullback of the device law along the
perturbation: `g t = i (v0 + t • dv)`, the leaf's `t -> i(v0+t*dv)`. -/
def segmentPullback {n : ℕ} (i : (Fin n → ℝ) → ℝ) (v0 dv : Fin n → ℝ) (t : ℝ) : ℝ :=
  i (v0 + t • dv)

/-- Small-signal remainder of the device law at the operating point `v0`
for perturbation `dv`: `r = i (v0 + dv) - i v0 - Di(v0)[dv]`, where
`Di(v0)[dv]` is `fderiv ℝ i v0 dv`. -/
noncomputable def smallSignalRemainder {n : ℕ} (i : (Fin n → ℝ) → ℝ) (v0 dv : Fin n → ℝ) : ℝ :=
  i (v0 + dv) - i v0 - fderiv ℝ i v0 dv

/-- Box form: with `i` of class `C²` on an open operating regime `U`
containing the box `Set.Icc lo hi` and sup-norm Hessian bound
`‖fderiv ℝ (fderiv ℝ i) y‖ <= M` on the box, the small-signal remainder
satisfies `|r| <= M * ‖dv‖^2 / 2` (Pi sup norm) for `v0, v0 + dv` in the box.
This is the one-dimensional Taylor remainder bound applied along the
segment `v0 + t • dv`. -/
lemma smallSignal_remainder_le_of_hessian_bound {n : ℕ}
    (i : (Fin n → ℝ) → ℝ) (M : ℝ) (lo hi v0 dv : Fin n → ℝ)
    (U : Set (Fin n → ℝ)) (hU : IsOpen U) (hbox : Set.Icc lo hi ⊆ U)
    (hC2 : ContDiffOn ℝ 2 i U)
    (hM : ∀ y ∈ Set.Icc lo hi, ‖fderiv ℝ (fderiv ℝ i) y‖ ≤ M)
    (hv0 : v0 ∈ Set.Icc lo hi) (hvdv : v0 + dv ∈ Set.Icc lo hi) :
    |smallSignalRemainder i v0 dv| ≤ M * ‖dv‖ ^ 2 / 2 := by
  have hconv : Convex ℝ (Set.Icc lo hi) := convex_Icc lo hi
  have hpath : ∀ t ∈ Set.Icc (0 : ℝ) 1, v0 + t • dv ∈ Set.Icc lo hi := by
    intro t ht
    have ht' : 0 ≤ t ∧ t ≤ 1 := Set.mem_Icc.mp ht
    have hcomb : (1 - t) • v0 + t • (v0 + dv) ∈ Set.Icc lo hi :=
      hconv hv0 hvdv (by linarith [ht'.1, ht'.2]) ht'.1 (by ring)
    have e : v0 + t • dv = (1 - t) • v0 + t • (v0 + dv) := by
      rw [sub_smul, one_smul, smul_add]
      abel
    rw [e]
    exact hcomb
  have hpathU : ∀ t ∈ Set.Icc (0 : ℝ) 1, v0 + t • dv ∈ U :=
    fun t ht => hbox (hpath t ht)
  have hCat : ∀ y ∈ U, ContDiffAt ℝ 2 i y := by
    intro y hy
    have hw : ContDiffWithinAt ℝ 2 i U y := hC2 y hy
    exact hw.contDiffAt (hU.mem_nhds hy)
  have hid : ∀ x : ℝ, HasDerivAt (fun t : ℝ => t) 1 x := fun x => hasDerivAt_id' x
  have hsmG : ∀ s : ℝ, HasDerivAt (fun t : ℝ => t • dv) dv s := by
    intro s
    have h := (hid s).smul_const dv
    rwa [one_smul] at h
  have hinnerG : ∀ s : ℝ, HasDerivAt (fun t : ℝ => v0 + t • dv) dv s := by
    intro s
    exact (hsmG s).const_add v0
  set g : ℝ → ℝ := fun t : ℝ => i (v0 + t • dv) with hgdef
  have hchainG : ∀ s ∈ (fun t : ℝ => v0 + t • dv) ⁻¹' U,
      HasDerivAt g ((fderiv ℝ i (v0 + s • dv)) dv) s := by
    intro s hs
    have hmem : v0 + s • dv ∈ U := hs
    have hfi : HasFDerivAt i (fderiv ℝ i (v0 + s • dv)) (v0 + s • dv) :=
      ((hCat _ hmem).differentiableAt (by decide)).hasFDerivAt
    have hinner : HasDerivAt (fun t : ℝ => v0 + t • dv) dv s := hinnerG s
    have hcomp : HasDerivAt (i ∘ fun t : ℝ => v0 + t • dv)
        ((fderiv ℝ i (v0 + s • dv)) dv) s :=
      HasFDerivAt.comp_hasDerivAt s hfi hinner
    show HasDerivAt (fun t : ℝ => i (v0 + t • dv)) ((fderiv ℝ i (v0 + s • dv)) dv) s
    exact hcomp
  have hderivEq : ∀ s ∈ (fun t : ℝ => v0 + t • dv) ⁻¹' U,
      deriv g s = (fderiv ℝ i (v0 + s • dv)) dv :=
    fun s hs => (hchainG s hs).deriv
  have hApply : ∃ A : ((Fin n → ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ, ∀ H, A H = H dv :=
    ⟨ContinuousLinearMap.apply ℝ _ dv, fun H => rfl⟩
  obtain ⟨A, hA⟩ := hApply
  have h2chain : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => (fderiv ℝ i (v0 + s • dv)) dv)
        (((fderiv ℝ (fderiv ℝ i) (v0 + x • dv)) dv) dv) x := by
    intro x hx
    have hmem : v0 + x • dv ∈ U := hpathU x hx
    have hCiAt : ContDiffAt ℝ 2 i (v0 + x • dv) := hCat _ hmem
    have hCfderiv : ContDiffAt ℝ 1 (fderiv ℝ i) (v0 + x • dv) := by
      have hh1 : ContDiffAt ℝ 2 (Function.uncurry fun _ : Fin n → ℝ => i)
          (v0 + x • dv, v0 + x • dv) :=
        ContDiffAt.comp (v0 + x • dv, v0 + x • dv) hCiAt contDiff_snd.contDiffAt
      have hh2 : ContDiffAt ℝ (1 : WithTop ℕ∞) (id : (Fin n → ℝ) → (Fin n → ℝ))
          (v0 + x • dv) := contDiff_id.contDiffAt
      have hh3 : (1 : WithTop ℕ∞) + 1 ≤ 2 := by decide
      exact ContDiffAt.fderiv (f := fun _ : Fin n → ℝ => i) (g := id) hh1 hh2 hh3
    have hfderiv : HasFDerivAt (fderiv ℝ i)
        (fderiv ℝ (fderiv ℝ i) (v0 + x • dv)) (v0 + x • dv) :=
      (hCfderiv.differentiableAt (by decide)).hasFDerivAt
    have hAcomp : HasFDerivAt (A ∘ fderiv ℝ i)
        (A.comp (fderiv ℝ (fderiv ℝ i) (v0 + x • dv))) (v0 + x • dv) :=
      HasFDerivAt.comp (v0 + x • dv) A.hasFDerivAt hfderiv
    have hinner : HasDerivAt (fun t : ℝ => v0 + t • dv) dv x := hinnerG x
    have hcomp : HasDerivAt ((A ∘ fderiv ℝ i) ∘ fun t : ℝ => v0 + t • dv)
        ((A.comp (fderiv ℝ (fderiv ℝ i) (v0 + x • dv))) dv) x :=
      HasFDerivAt.comp_hasDerivAt x hAcomp hinner
    have hfunEq : ((A ∘ fderiv ℝ i) ∘ fun t : ℝ => v0 + t • dv)
        = fun s : ℝ => (fderiv ℝ i (v0 + s • dv)) dv := by
      funext s
      simp [Function.comp_def, hA]
    have hderivEq2 : (A.comp (fderiv ℝ (fderiv ℝ i) (v0 + x • dv))) dv
        = ((fderiv ℝ (fderiv ℝ i) (v0 + x • dv)) dv) dv := by
      simp [ContinuousLinearMap.comp_apply, hA]
    rw [← hfunEq, ← hderivEq2]
    exact hcomp
  have hpcont : Continuous (fun t : ℝ => v0 + t • dv) :=
    continuous_iff_continuousAt.mpr (fun s => (hinnerG s).continuousAt)
  have hopen : IsOpen ((fun t : ℝ => v0 + t • dv) ⁻¹' U) := IsOpen.preimage hpcont hU
  have hderivG : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (deriv g) (((fderiv ℝ (fderiv ℝ i) (v0 + x • dv)) dv) dv) x := by
    intro x hx
    have hmemU : v0 + x • dv ∈ U := hpathU x hx
    have hnhds : (fun t : ℝ => v0 + t • dv) ⁻¹' U ∈ nhds x :=
      hopen.mem_nhds hmemU
    have heq : (deriv g) =ᶠ[nhds x] (fun s : ℝ => (fderiv ℝ i (v0 + s • dv)) dv) :=
      Filter.eventually_of_mem hnhds (fun s hs => hderivEq s hs)
    have h2 := h2chain x hx
    exact h2.congr_of_eventuallyEq heq
  set R : ℝ := g 1 - g 0 - deriv g 0 with hRdef
  set φ : ℝ → ℝ := fun t => g t - g 0 - t * deriv g 0 - (t * t) * R with hφdef
  set ψ : ℝ → ℝ := fun t => (deriv g t - 1 * deriv g 0) - (1 * t + t * 1) * R
    with hψdef
  have hchainIcc : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt g ((fderiv ℝ i (v0 + x • dv)) dv) x := by
    intro x hx
    have hmemU : (fun t : ℝ => v0 + t • dv) x ∈ U := hpathU x hx
    exact hchainG x hmemU
  have hφderivG : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt φ ((deriv g x - 1 * deriv g 0) - (1 * x + x * 1) * R) x := by
    intro x hx
    have hgx : HasDerivAt g (deriv g x) x := by
      have h := hchainIcc x hx
      have e : deriv g x = (fderiv ℝ i (v0 + x • dv)) dv := h.deriv
      rw [e]
      exact h
    have h1 : HasDerivAt (fun t : ℝ => g t - g 0) (deriv g x) x :=
      hgx.sub_const (g 0)
    have h2 : HasDerivAt (fun t : ℝ => t * deriv g 0) (1 * deriv g 0) x :=
      (hid x).mul_const (deriv g 0)
    have hA : HasDerivAt (fun t : ℝ => (g t - g 0) - t * deriv g 0)
        (deriv g x - 1 * deriv g 0) x := h1.sub h2
    have hsq : HasDerivAt (fun t : ℝ => t * t) (1 * x + x * 1) x :=
      (hid x).mul (hid x)
    have hB : HasDerivAt (fun t : ℝ => (t * t) * R) ((1 * x + x * 1) * R) x :=
      hsq.mul_const R
    have hφ := hA.sub hB
    have hfunEqφ : φ = (fun t : ℝ => (g t - g 0) - t * deriv g 0)
        - (fun t : ℝ => (t * t) * R) := by
      funext t
      simp [hφdef, Pi.sub_apply]
    rw [hfunEqφ]
    exact hφ
  have hφderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt φ ((deriv g x - 1 * deriv g 0) - (1 * x + x * 1) * R) x :=
    fun x hx => hφderivG x (mem_Icc_of_mem_Ioo hx)
  have hφcont : ContinuousOn φ (Set.Icc (0 : ℝ) 1) := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    exact (hφderivG x hx).continuousAt
  have hφends : φ 0 = φ 1 := by simp [hφdef, hRdef]
  have h01 : (0 : ℝ) < 1 := by norm_num
  obtain ⟨c, hcmem, hc⟩ := exists_hasDerivAt_eq_zero h01 hφcont hφends hφderiv
  have hcmem' : 0 < c ∧ c < 1 := Set.mem_Ioo.mp hcmem
  have hψderivG : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt ψ (deriv (deriv g) x - (1 * 1 + 1 * 1) * R) x := by
    intro x hx
    have hDx : HasDerivAt (deriv g) (deriv (deriv g) x) x := by
      have h := hderivG x hx
      have e : deriv (deriv g) x =
          (((fderiv ℝ (fderiv ℝ i) (v0 + x • dv)) dv) dv) := h.deriv
      rw [e]
      exact h
    have h1 : HasDerivAt (fun t : ℝ => deriv g t - 1 * deriv g 0)
        (deriv (deriv g) x) x :=
      hDx.sub_const (1 * deriv g 0)
    have h2a : HasDerivAt (fun t : ℝ => 1 * t) (1 * 1) x := (hid x).const_mul 1
    have h2b : HasDerivAt (fun t : ℝ => t * 1) (1 * 1) x := (hid x).mul_const 1
    have h2 : HasDerivAt (fun t : ℝ => 1 * t + t * 1) (1 * 1 + 1 * 1) x :=
      h2a.add h2b
    have hB : HasDerivAt (fun t : ℝ => (1 * t + t * 1) * R) ((1 * 1 + 1 * 1) * R)
        x := h2.mul_const R
    have hψ := h1.sub hB
    have hfunEqψ : ψ = (fun t : ℝ => deriv g t - 1 * deriv g 0)
        - (fun t : ℝ => (1 * t + t * 1) * R) := by
      funext t
      simp [hψdef, Pi.sub_apply]
    rw [hfunEqψ]
    exact hψ
  have hψderiv : ∀ x ∈ Set.Ioo (0 : ℝ) c,
      HasDerivAt ψ (deriv (deriv g) x - (1 * 1 + 1 * 1) * R) x := by
    intro x hx
    have hx' : 0 < x ∧ x < c := Set.mem_Ioo.mp hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 :=
      Set.mem_Icc.mpr ⟨le_of_lt hx'.1, le_trans (le_of_lt hx'.2)
        (le_of_lt hcmem'.2)⟩
    exact hψderivG x hxIcc
  have hψcont : ContinuousOn ψ (Set.Icc (0 : ℝ) c) := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hx' : 0 ≤ x ∧ x ≤ c := Set.mem_Icc.mp hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 :=
      Set.mem_Icc.mpr ⟨hx'.1, le_trans hx'.2 (le_of_lt hcmem'.2)⟩
    exact (hψderivG x hxIcc).continuousAt
  have hψc : ψ c = 0 := by simpa [hψdef] using hc
  have hψ0 : ψ 0 = 0 := by simp [hψdef]
  have hψends : ψ 0 = ψ c := hψ0.trans hψc.symm
  obtain ⟨d, hdmemi, hd⟩ :=
    exists_hasDerivAt_eq_zero hcmem'.1 hψcont hψends hψderiv
  have h2val : (1 : ℝ) * 1 + 1 * 1 = 2 := by norm_num
  rw [h2val] at hd
  have hdIcc : d ∈ Set.Icc (0 : ℝ) 1 := mem_Icc_of_mem_Ioo_of_lt hdmemi hcmem'.2
  have hddEq : deriv (deriv g) d =
      (((fderiv ℝ (fderiv ℝ i) (v0 + d • dv)) dv) dv) :=
    (hderivG d hdIcc).deriv
  rw [hddEq] at hd
  have hR2 : R = (((fderiv ℝ (fderiv ℝ i) (v0 + d • dv)) dv) dv) / 2 := by
    linarith
  have hHop : ‖((fderiv ℝ (fderiv ℝ i) (v0 + d • dv)) dv) dv‖ ≤ M * ‖dv‖ ^ 2 := by
    have h1 := ((fderiv ℝ (fderiv ℝ i) (v0 + d • dv)) dv).le_opNorm dv
    have h2 := (fderiv ℝ (fderiv ℝ i) (v0 + d • dv)).le_opNorm dv
    have h3 := hM (v0 + d • dv) (hpath d hdIcc)
    have hnn : (0 : ℝ) ≤ ‖dv‖ := norm_nonneg _
    calc ‖((fderiv ℝ (fderiv ℝ i) (v0 + d • dv)) dv) dv‖
        ≤ ‖(fderiv ℝ (fderiv ℝ i) (v0 + d • dv)) dv‖ * ‖dv‖ := h1
      _ ≤ (‖fderiv ℝ (fderiv ℝ i) (v0 + d • dv)‖ * ‖dv‖) * ‖dv‖ :=
          mul_le_mul_of_nonneg_right h2 hnn
      _ = ‖fderiv ℝ (fderiv ℝ i) (v0 + d • dv)‖ * (‖dv‖ ^ 2) := by ring
      _ ≤ M * (‖dv‖ ^ 2) := mul_le_mul_of_nonneg_right h3 (by positivity)
  have h2abs : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
  have hfin : |R| ≤ M * ‖dv‖ ^ 2 / 2 := by
    rw [hR2, abs_div, h2abs, ← Real.norm_eq_abs]
    linarith [hHop]
  have hg1 : g 1 = i (v0 + dv) := by simp [hgdef]
  have hg0 : g 0 = i v0 := by simp [hgdef]
  have hchain0 : deriv g 0 = fderiv ℝ i v0 dv := by
    have h := hchainIcc 0 (Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩)
    have e := h.deriv
    have e0 : v0 + (0 : ℝ) • dv = v0 := by simp
    rw [e0] at e
    exact e
  have hr : smallSignalRemainder i v0 dv = g 1 - g 0 - deriv g 0 := by
    unfold smallSignalRemainder
    rw [hg1, hg0, hchain0]
  rw [hr, ← hRdef]
  exact hfin

/-- Segment form: if `i` is differentiable at `v0`, the pullback
`g t = i (v0 + t • dv)` is `C²` on `ℝ`, and the second-derivative
bound `|g'' t| <= M * ‖dv‖^2` holds on `[0,1]` (sup norm), then
`|r| <= M * ‖dv‖^2 / 2`. No box or global `C²` hypothesis on `i`
itself; only the bound, not the smoothness, is segment-local. -/
lemma smallSignal_remainder_le_of_segment_bound {n : ℕ}
    (i : (Fin n → ℝ) → ℝ) (v0 dv : Fin n → ℝ) (M : ℝ)
    (hdiff : DifferentiableAt ℝ i v0)
    (hC2 : ContDiff ℝ 2 (fun t : ℝ => i (v0 + t • dv)))
    (hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (fun t : ℝ => i (v0 + t • dv))) t| ≤ M * ‖dv‖ ^ 2) :
    |smallSignalRemainder i v0 dv| ≤ M * ‖dv‖ ^ 2 / 2 := by
  have hmain := abs_taylor_remainder_le_of_second_deriv_bound
    (fun t : ℝ => i (v0 + t • dv)) (M * ‖dv‖ ^ 2) hC2 hseg
  have hg1 : (fun t : ℝ => i (v0 + t • dv)) 1 = i (v0 + dv) := by simp
  have hg0 : (fun t : ℝ => i (v0 + t • dv)) 0 = i v0 := by simp
  have hchain : deriv (fun t : ℝ => i (v0 + t • dv)) 0 = fderiv ℝ i v0 dv := by
    have h0 : (fun t : ℝ => v0 + t • dv) 0 = v0 := by simp
    have hfi : HasFDerivAt i (fderiv ℝ i v0) ((fun t : ℝ => v0 + t • dv) 0) := by
      rw [h0]
      exact hdiff.hasFDerivAt
    have hid : HasDerivAt (fun t : ℝ => t) 1 (0 : ℝ) := hasDerivAt_id' 0
    have hsm : HasDerivAt (fun t : ℝ => t • dv) dv 0 := by
      have h := hid.smul_const dv
      rwa [one_smul] at h
    have hinner : HasDerivAt (fun t : ℝ => v0 + t • dv) dv 0 := hsm.const_add v0
    have hcomp : HasDerivAt (i ∘ fun t : ℝ => v0 + t • dv)
        ((fderiv ℝ i v0) dv) 0 :=
      HasFDerivAt.comp_hasDerivAt (0 : ℝ) hfi hinner
    exact hcomp.deriv
  have hr : smallSignalRemainder i v0 dv
      = (fun t : ℝ => i (v0 + t • dv)) 1 - (fun t : ℝ => i (v0 + t • dv)) 0
        - deriv (fun t : ℝ => i (v0 + t • dv)) 0 := by
    unfold smallSignalRemainder
    rw [hg1, hg0, hchain]
  rw [hr]
  exact hmain

/-- Sharpness: the one-terminal square law at the origin attains the half
factor: its remainder at perturbation `a` is exactly `a ^ 2`, i.e. the
bound `M * ‖dv‖^2 / 2` with `M = 2` and `‖dv‖ = |a|` is an equality. -/
lemma smallSignal_quadratic_attains_factor (a : ℝ) :
    smallSignalRemainder (fun v : Fin 1 → ℝ => (v 0) ^ 2) 0 (fun _ => a)
      = a ^ 2 := by
  have hfd : fderiv ℝ (fun v : Fin 1 → ℝ => (v 0) ^ 2) 0 = 0 := by
    have hproj : HasFDerivAt (fun v : Fin 1 → ℝ => v 0)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) (0 : Fin 1)) 0 :=
      ContinuousLinearMap.hasFDerivAt
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) (0 : Fin 1))
    have hmul := hproj.mul hproj
    simp only [Pi.zero_apply, zero_smul, add_zero] at hmul
    have hmul2 : HasFDerivAt (fun v : Fin 1 → ℝ => (v 0) ^ 2)
        (0 : (Fin 1 → ℝ) →L[ℝ] ℝ) 0 := by
      have hfun : (fun v : Fin 1 → ℝ => (v 0)^2)
          = (fun v : Fin 1 → ℝ => v 0) * (fun v : Fin 1 → ℝ => v 0) := by
        funext v
        simp [pow_two, Pi.mul_apply]
      rw [hfun]
      exact hmul
    exact hmul2.fderiv
  unfold smallSignalRemainder
  rw [hfd]
  simp

end PhyslibExt.Electronics.OperatingPointLinearization
