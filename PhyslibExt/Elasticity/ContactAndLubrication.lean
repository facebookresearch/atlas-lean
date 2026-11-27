/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Sign
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.Analysis.InnerProductSpace.Stampacchia

/-!
# Contact and lubrication

Reduced models of contact and lubrication. Section A solves the one-dimensional Reynolds equation
for a plane slider with a linear converging film in closed form; the pressure and the load per
unit width are positive for the converging orientation. Section B treats frictionless scalar
unilateral contact as an instance of Stampacchia's variational inequality, with the obstacle
reaction as its complementarity multiplier. Section C states the set-valued Coulomb friction
law, its dissipation and the static-equilibrium criterion. Section D adds the Coulomb friction
cone and the admission conditions for a unilateral interface with friction, in
compression-positive form. Section E adds the vector Coulomb sliding and sticking law at
that interface and its frictional power.

## i. Overview

Section A treats plane-slider lubrication.

A plane slider of length `L > 0` carries an incompressible isoviscous lubricant of viscosity
`μ > 0` in the film `h x = h0 + (hL - h0) x / L` between the inlet `x = 0` and the outlet
`x = L`. The lower surface slides with speed `U > 0` in the direction of increasing `x`. The
stated reduced model is the Reynolds equation `(h³ p')' = 6 μ U h'` on `[0, L]` with ambient
pressure `p 0 = p L = 0` at both ends and no cavitation; it is a model input, not a proved thin
film limit of the Navier-Stokes equations. Here the model is the predicate
`IsReynoldsSolution`: within `[0, L]` (one-sided at the ends) `p` has derivative `p'` and the
flux `h³ p'` has derivative `6 μ U (hL - h0) / L`, so only values on `[0, L]` matter.

For positive end thicknesses `h0 ≠ hL` the model has exactly one solution,
`p = 6 μ U L (h0 - h) (h - hL) / ((h0² - hL²) h²)`, with gradient
`p' = 6 μ U (h - h_m) / h³` and `h_m = 2 h0 hL / (h0 + hL)`. Its load per unit width is
`W = ∫₀ᴸ p = 6 μ U L² / (h0 - hL)² (log (h0 / hL) - 2 (h0 - hL) / (h0 + hL))`. For the
converging film `h0 > hL > 0` the pressure is positive inside the slider and `W > 0`. For a
diverging film `0 < h0 < hL` the same formula is negative inside the slider: the gauge pressure
falls below ambient, where a real film cavitates, so the no-cavitation model is not valid there.
A film that closes at the outlet, `hL = 0`, admits no solution at all.

Cavitation models, side leakage, thermal and elastic effects and the derivation of the Reynolds
equation are not treated.

Section B treats scalar unilateral contact.

A frictionless scalar body of stiffness `k > 0` under a load `f` moves towards a rigid obstacle
at position `g`. Its displacement `u` is the solution of the variational inequality of
Stampacchia's theorem on the nonpenetration set `u ≤ g`, and the obstacle reaction is the
complementarity multiplier of that inequality.

The real line is a Hilbert space, the admissible set `admissibleSet g = Set.Iic g` is nonempty,
closed and convex, and the spring `stiffnessMap k = k • id` satisfies the coercivity hypothesis
`α ‖u‖ ^ 2 ≤ ⟪A u, u⟫` with `α = k` when `k > 0`. These are exactly the hypotheses of
Stampacchia's theorem (operator form), so the variational inequality

  `u ≤ g` and `0 ≤ ⟪k u - f, v - u⟫` for every `v ≤ g`

has exactly one solution. It is the contact displacement `u = min g (f / k)`. With the contact
force `λ = f - k u` and the gap `g - u`, the solution satisfies the complementarity conditions
`λ ≥ 0`, `g - u ≥ 0` and `λ (g - u) = 0`.

Sign convention: `u` and `f` are positive in the same direction, towards the obstacle. The
obstacle pushes on the body with the force `-λ` along increasing `u`, so it opposes further
penetration, and equilibrium reads `f - k u - λ = 0`. For `k = 2`, `g = 1`, `f = 4` the spring
force is `-2`, the load `+4` and the contact force `-2`; they sum to zero.

Model inputs (hypotheses):

* frictionless scalar displacement, linear spring of stiffness `k > 0`, rigid obstacle at `g`;
* the contact force opposes increasing `u` (the multiplier `λ` is its magnitude).

Non-goals for Section B: no multidimensional contact, no constraint qualification or general
KKT theory, no friction in the scalar model (Section C states the scalar Coulomb law separately
and Section D the interface admission conditions), no adhesion, impact or wear, and no empirical
adequacy or system safety claim.

Section C treats Coulomb friction.

A body slides on a fixed surface with tangential velocity `v`, pressed against it by the normal
force `N`, with friction coefficient `μ`. The declared reduced Coulomb law
`IsCoulombFriction μ N v F` is set valued: a slipping body (`v ≠ 0`) feels the friction force
`F = -μ N sign v`, and a sticking body (`v = 0`) any force `F ∈ [-μ N, μ N]`. The friction port
pairs `F` with `v`; its power `F v` is the power delivered by the friction force to the body.
On the graph `F v = -μ N |v|`, so for `μ, N ≥ 0` friction never supplies power and the port
dissipates `μ N |v| ≥ 0`. A body at rest under an applied tangential force `Fa` is in static
equilibrium, `Fa + F = 0` with an admissible stick force `F`, exactly when
`Fa ∈ [-μ N, μ N]`. At rest the force is not determined when `μ N > 0`. A negative coefficient
is inadmissible: with `μ < 0 < N` no force is admissible at rest, and slip would supply the
positive power `-μ N |v|`.

Sign convention: `v`, `F` and `Fa` are measured along one tangent direction. For `μ = 1/2`,
`N = 10` and `v = 2` the friction force is `-5`, opposing the motion, and the friction power
is `-10`.

Model inputs (hypotheses): the reduced scalar law with supplied coefficient `μ` and normal
force `N`, both nonnegative where the dissipation statement uses them; the normal force is
given, not solved from a contact problem. Non-goals: no existence or uniqueness of
trajectories of the differential inclusion, no distinction between static and kinetic
coefficients, no contact-pressure solution and no wear rate.

Section D treats unilateral contact with Coulomb friction.

A unit normal `n` of a rigid unilateral interface points out of the body on which the traction
`τ` acts. The normal force is compression-positive, `N = -⟪τ, n⟫`, the tangent traction is
`t = τ - ⟪τ, n⟫ • n`, and `τ = t - N • n`. With the normal gap `g` (open contact for `0 < g`,
closed contact for `g = 0`) and a fixed dimensionless friction coefficient `μ`, physically
`0 ≤ μ`, a contact state is admissible when `0 ≤ N`, `0 ≤ g`, `N * g = 0` and the Coulomb
bound `‖t‖ ≤ μ * N` holds: `IsAdmissibleContact μ N g t`. Here `t` lies in a real inner product
space `E` and `‖·‖` is its inner-product norm, so the friction cone
`frictionCone μ = {(N, t) | ‖t‖ ≤ μ * N ∧ 0 ≤ N}` is isotropic; the slip threshold
`‖t‖ = μ * N` is included, and at `μ = 0` it is the nonnegative normal ray `t = 0`,
`0 ≤ N`; admission keeps its own `0 ≤ N`. The friction cone is convex for `0 ≤ μ`; the
complementarity set in the `(N, g)` plane is not. Symbols are reused across sections with
different meanings: `μ` is viscosity in Section A and the friction coefficient in Sections C
and D; `g` is the obstacle position in Section B and the gap in Section D; `admissibleSet g`
collects displacements in Section B, while `IsAdmissibleContact` is a property of contact states
in Section D.

Section D states no sliding rule, slip direction, frictional work, or existence or uniqueness
of contact solutions: it is the static admission interface only, distinct from the scalar
set-valued friction graph of Section C. The sliding rule is Section E.

Section E treats Coulomb sliding and sticking at the interface of Section D.
`IsCoulombTraction μ N v t` says that at a nonzero slip velocity `v` the tangent traction is
`t = -(μ * N) • (‖v‖⁻¹ • v)`, opposite to `v` with norm `μ * N` when `0 < μ * N`, and at
`v = 0` any traction with `‖t‖ ≤ μ * N` may act; the stick branch involves no division. On
the physical domain `0 ≤ μ`, `0 ≤ N` the frictional power is `⟪t, v⟫ = -(μ * N * ‖v‖) ≤ 0`;
for `μ * N < 0` the stick branch is empty and the law supplies positive power. Slip and
stick tractions are admissible closed contact states, and on a tangent line `E = ℝ` the
vector law is exactly the scalar friction graph of Section C. Here `v` is the vector slip
velocity, not the scalar sliding velocity of Section C, and the scalar force `F` of
Section C corresponds to the tangent traction `t`.

## ii. Key results

- `Elasticity.ContactAndLubrication.sliderPressure_isReynoldsSolution`: the closed-form
  pressure solves the model.
- `Elasticity.ContactAndLubrication.isReynoldsSolution_unique`: every solution is the closed-form
  pressure.
- `Elasticity.ContactAndLubrication.sliderPressure_pos`: the pressure is positive for a converging
  film.
- `Elasticity.ContactAndLubrication.sliderLoad_eq`: the load per unit width in closed form.
- `Elasticity.ContactAndLubrication.sliderLoad_pos`: the load is positive for a converging film.
- `Elasticity.ContactAndLubrication.sliderPressure_neg_of_diverging`: a diverging film gives
  negative pressure.
- `Elasticity.ContactAndLubrication.not_isReynoldsSolution_of_hL_eq_zero`: an outlet thickness
  `hL = 0` is rejected.
- `Elasticity.ContactAndLubrication.inner_stiffnessMap_sub`: the inner product of the variational
  inequality on `ℝ`.
- `Elasticity.ContactAndLubrication.admissibleSet_nonempty`, `isClosed_admissibleSet`,
  `convex_admissibleSet`, `stiffnessMap_coercive`: the hypotheses of Stampacchia's theorem.
- `Elasticity.ContactAndLubrication.existsUnique_contact`: exactly one solution of the contact
  variational inequality.
- `Elasticity.ContactAndLubrication.contact_vi_iff`: that solution is
  `contactDisplacement k g f = min g (f / k)`.
- `Elasticity.ContactAndLubrication.complementarity_of_vi`, `contactDisplacement_complementarity`:
  `λ ≥ 0`, `g - u ≥ 0` and `λ (g - u) = 0`.
- `Elasticity.ContactAndLubrication.isCoulombFriction_of_ne_zero`, `isCoulombFriction_zero`:
  the slip and stick branches of the Coulomb friction graph.
- `Elasticity.ContactAndLubrication.coulomb_power_eq`, `coulomb_power_nonpos`: the friction
  power is `-μ N |v|`, nonpositive for `μ, N ≥ 0`.
- `Elasticity.ContactAndLubrication.coulomb_static_equilibrium_iff`: static equilibrium is
  admissible exactly when the applied force is in `[-μ N, μ N]`.
- `Elasticity.ContactAndLubrication.coulomb_stick_not_unique`: the force at rest is not unique
  when `μ, N > 0`.
- `Elasticity.ContactAndLubrication.coulomb_not_exists_stick_of_neg`,
  `coulomb_slip_power_pos_of_neg`: a negative coefficient admits no stick force and makes slip
  supply power.
- `Elasticity.ContactAndLubrication.frictionCone`, `IsAdmissibleContact`: the Coulomb cone and
  the admission conditions of Section D.
- `Elasticity.ContactAndLubrication.normal_tangent_decomposition_iff`: the traction splits as
  `τ = t - N • n` with `t` orthogonal to the unit normal `n` exactly when `N = -⟪τ, n⟫` and
  `t = τ - ⟪τ, n⟫ • n`.
- `Elasticity.ContactAndLubrication.convex_frictionCone`,
  `not_convex_complementarity`: the friction cone is convex for `0 ≤ μ`; the complementarity
  set in the `(N, g)` plane is not.
- `Elasticity.ContactAndLubrication.IsAdmissibleContact.eq_zero_of_gap_pos`,
  `isAdmissibleContact_zero_tangent_iff`: an open gap carries no force, and the frictionless
  slice `t = 0` is exactly the scalar complementarity of Section B.
- `Elasticity.ContactAndLubrication.IsCoulombTraction`,
  `IsCoulombTraction.inner_eq_and_nonpos`, `IsCoulombTraction.inner_pos_of_mul_neg`,
  `IsCoulombTraction.isAdmissibleContact`, `isCoulombTraction_iff_isCoulombFriction`: the
  vector Coulomb law of Section E, its frictional power and sign, the invalid-sign control,
  admission at closed contact, and the reduction to Section C on a tangent line.

## iii. Table of contents

- A. Plane-slider lubrication
  - A.1. Film, model and closed-form pressure
  - A.2. Solution of the Reynolds model
  - A.3. Positivity and load for the converging film
  - A.4. Diverging and closed films
- B. Scalar unilateral contact
  - B.1. The contact model
  - B.2. The hypotheses of Stampacchia's theorem
  - B.3. Existence, uniqueness and the contact displacement
  - B.4. Complementarity
- C. Coulomb friction
  - C.1. The friction graph
  - C.2. Friction power and dissipation
  - C.3. Static equilibrium and non-uniqueness at rest
  - C.4. Negative coefficient
- D. Unilateral contact with Coulomb friction
- E. Coulomb sliding and sticking at a unilateral interface

## iv. References

- O. Reynolds, On the theory of lubrication and its application to Mr. Beauchamp Tower's
  experiments, *Philosophical Transactions of the Royal Society of London* 177 (1886).
- B. J. Hamrock, S. R. Schmid and B. O. Jacobson, *Fundamentals of Fluid Film Lubrication*,
  2nd ed., Marcel Dekker (2004): the Reynolds equation and the fixed-incline slider bearing.
- G. Stampacchia, *Formes bilinéaires coercitives sur les ensembles convexes*, C. R. Acad. Sci.
  Paris 258 (1964), 4413–4416.
- D. Kinderlehrer and G. Stampacchia, *An Introduction to Variational Inequalities and Their
  Applications*, Academic Press (1980), Chapter II (the obstacle problem).
- N. Kikuchi and J. T. Oden, *Contact Problems in Elasticity*, SIAM (1988), Chapter 2
  (unilateral constraints and the Signorini conditions).
- P. Wriggers, *Computational Contact Mechanics*, 2nd edition, Springer, 2006: the Signorini
  conditions and the Coulomb friction law; the compression-positive normal form used here,
  with the slip threshold included in the friction cone, is this file's sign convention.
- `MathlibExt.Analysis.InnerProductSpace.Stampacchia.exists_unique_stampacchia`
  (`MathlibExt.Analysis.InnerProductSpace.Stampacchia`): Stampacchia's theorem, operator form.
- C. A. Coulomb, *Théorie des machines simples*, Mémoires de mathématique et de physique
  présentés à l'Académie royale des sciences 10 (1785), 161–332.
- J. J. Moreau, *Unilateral contact and dry friction in finite freedom dynamics*, in
  *Nonsmooth Mechanics and Applications*, CISM Courses and Lectures 302, Springer (1988),
  1–82 (the set-valued friction law).
- R. C. Hibbeler, *Engineering Mechanics: Statics*, 14th edition, chapter 8 (dry friction:
  impending motion and the friction cone).
-/

@[expose] public section

namespace Elasticity.ContactAndLubrication

/-! ## A. Plane-slider lubrication -/

/-! ### A.1. Film, model and closed-form pressure -/

/-- Linear film thickness of the plane slider: `h0` at the inlet `x = 0` and `hL` at the
outlet `x = L`. -/
noncomputable def sliderFilm (h0 hL L x : ℝ) : ℝ :=
  h0 + (hL - h0) * x / L

/-- The stated Reynolds model on `[0, L]`: within `[0, L]` (one-sided at the ends) the pressure
`p` has derivative `p'` and the flux `h³ p'` has derivative `6 μ U h'` with the film slope
`h' = (hL - h0) / L`, and `p` vanishes at both ends. The predicate depends only on the values of
`p` and `p'` on `[0, L]`. -/
def IsReynoldsSolution (μ U h0 hL L : ℝ) (p p' : ℝ → ℝ) : Prop :=
  (∀ x ∈ Set.Icc 0 L, HasDerivWithinAt p (p' x) (Set.Icc 0 L) x) ∧
    (∀ x ∈ Set.Icc 0 L,
      HasDerivWithinAt (fun y => sliderFilm h0 hL L y ^ 3 * p' y) (6 * μ * U * ((hL - h0) / L))
        (Set.Icc 0 L) x) ∧
    p 0 = 0 ∧ p L = 0

/-- Closed-form plane-slider pressure `6 μ U L (h0 - h) (h - hL) / ((h0² - hL²) h²)` with
`h = sliderFilm h0 hL L x`. -/
noncomputable def sliderPressure (μ U h0 hL L x : ℝ) : ℝ :=
  6 * μ * U * L * (h0 - sliderFilm h0 hL L x) * (sliderFilm h0 hL L x - hL) /
    ((h0 ^ 2 - hL ^ 2) * sliderFilm h0 hL L x ^ 2)

/-- Plane-slider pressure gradient `6 μ U (h - 2 h0 hL / (h0 + hL)) / h³` with
`h = sliderFilm h0 hL L x`. -/
noncomputable def sliderPressureGradient (μ U h0 hL L x : ℝ) : ℝ :=
  6 * μ * U * (sliderFilm h0 hL L x - 2 * h0 * hL / (h0 + hL)) / sliderFilm h0 hL L x ^ 3

/-- Load per unit width: the integral of the slider pressure over `[0, L]`. -/
noncomputable def sliderLoad (μ U h0 hL L : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..L, sliderPressure μ U h0 hL L x

/-- The film stays open: for positive end thicknesses the film is positive on `[0, L]`. -/
lemma sliderFilm_pos {h0 hL L x : ℝ} (h0pos : 0 < h0) (hLpos : 0 < hL) (hL0 : 0 < L)
    (hx : x ∈ Set.Icc 0 L) :
    0 < sliderFilm h0 hL L x := by
  unfold sliderFilm
  obtain ⟨hx0, hxL⟩ := hx
  have hLne : L ≠ 0 := ne_of_gt hL0
  have hnum : 0 < h0 * L + (hL - h0) * x := by
    by_cases hx0' : x = 0
    · subst hx0'
      simp only [mul_zero, add_zero]
      exact mul_pos h0pos hL0
    · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx0')
      have h1 : 0 ≤ h0 * (L - x) := mul_nonneg (le_of_lt h0pos) (sub_nonneg.mpr hxL)
      have h2 : 0 < hL * x := mul_pos hLpos hxpos
      have heq : h0 * L + (hL - h0) * x = h0 * (L - x) + hL * x := by ring
      linarith
  have heq : h0 + (hL - h0) * x / L = (h0 * L + (hL - h0) * x) / L := by
    field_simp
  rw [heq]
  exact div_pos hnum hL0

private lemma hasDerivAt_sliderFilm {h0 hL L x : ℝ} :
    HasDerivAt (sliderFilm h0 hL L) ((hL - h0) / L) x := by
  have hfun : sliderFilm h0 hL L = fun x => h0 + ((hL - h0) / L) * x := by
    funext y
    unfold sliderFilm
    ring
  rw [hfun]
  have h1 : HasDerivAt (fun y : ℝ => ((hL - h0) / L) * y) (((hL - h0) / L) * 1) x :=
    HasDerivAt.const_mul _ (hasDerivAt_id x)
  simp only [mul_one] at h1
  exact HasDerivAt.const_add _ h1

private lemma sliderFilm_zero {h0 hL L : ℝ} : sliderFilm h0 hL L 0 = h0 := by
  unfold sliderFilm
  simp

private lemma sliderFilm_right {h0 hL L : ℝ} (hL0 : 0 < L) : sliderFilm h0 hL L L = hL := by
  have hLne : L ≠ 0 := ne_of_gt hL0
  unfold sliderFilm
  field_simp
  ring

private lemma const_of_hasDerivWithinAt_zero {f : ℝ → ℝ} {L : ℝ}
    (hf : ∀ x ∈ Set.Icc 0 L, HasDerivWithinAt f 0 (Set.Icc 0 L) x) :
    ∀ x ∈ Set.Icc 0 L, f x = f 0 :=
  constant_of_has_deriv_right_zero (fun x hx => (hf x hx).continuousWithinAt)
    (fun x hx => (hf x (Set.Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hx))

/-! ### A.2. Solution of the Reynolds model -/

/-- Existence: for positive end thicknesses `h0 ≠ hL` and `L > 0`, the closed-form pressure,
with the closed-form gradient, solves the stated Reynolds model. -/
lemma sliderPressure_isReynoldsSolution {μ U h0 hL L : ℝ} (h0pos : 0 < h0) (hLpos : 0 < hL)
    (hne : h0 ≠ hL) (hL0 : 0 < L) :
    IsReynoldsSolution μ U h0 hL L (sliderPressure μ U h0 hL L)
      (sliderPressureGradient μ U h0 hL L) := by
  unfold IsReynoldsSolution
  have hLne : L ≠ 0 := ne_of_gt hL0
  have hsum_ne : h0 + hL ≠ 0 := ne_of_gt (add_pos h0pos hLpos)
  have hdiff_ne : h0 - hL ≠ 0 := sub_ne_zero.mpr hne
  have hsq_ne : h0 ^ 2 - hL ^ 2 ≠ 0 := by
    have hfac : h0 ^ 2 - hL ^ 2 = (h0 - hL) * (h0 + hL) := by ring
    rw [hfac]
    exact mul_ne_zero hdiff_ne hsum_ne
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    apply HasDerivAt.hasDerivWithinAt
    have hpos : 0 < sliderFilm h0 hL L x := sliderFilm_pos h0pos hLpos hL0 hx
    have hfilm_ne : sliderFilm h0 hL L x ≠ 0 := ne_of_gt hpos
    have hh : HasDerivAt (sliderFilm h0 hL L) ((hL - h0) / L) x := hasDerivAt_sliderFilm
    have h1 : HasDerivAt (fun y => h0 - sliderFilm h0 hL L y) (0 - (hL - h0) / L) x :=
      (hasDerivAt_const x h0).sub hh
    have h2 : HasDerivAt (fun y => sliderFilm h0 hL L y - hL) ((hL - h0) / L - 0) x :=
      hh.sub (hasDerivAt_const x hL)
    have h3 : HasDerivAt (fun y => (h0 - sliderFilm h0 hL L y) * (sliderFilm h0 hL L y - hL))
        ((0 - (hL - h0) / L) * (sliderFilm h0 hL L x - hL) +
          (h0 - sliderFilm h0 hL L x) * ((hL - h0) / L - 0)) x :=
      h1.mul h2
    have hN : HasDerivAt
        (fun y => (6 * μ * U * L) * ((h0 - sliderFilm h0 hL L y) * (sliderFilm h0 hL L y - hL)))
        ((6 * μ * U * L) * ((0 - (hL - h0) / L) * (sliderFilm h0 hL L x - hL) +
          (h0 - sliderFilm h0 hL L x) * ((hL - h0) / L - 0))) x :=
      h3.const_mul _
    have hD2' : HasDerivAt (fun y => sliderFilm h0 hL L y * sliderFilm h0 hL L y)
        (((hL - h0) / L) * sliderFilm h0 hL L x + sliderFilm h0 hL L x * ((hL - h0) / L)) x :=
      hh.mul hh
    have hD2 : HasDerivAt (fun y => sliderFilm h0 hL L y ^ 2)
        (((hL - h0) / L) * sliderFilm h0 hL L x + sliderFilm h0 hL L x * ((hL - h0) / L)) x :=
      hD2'.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => by
        change sliderFilm h0 hL L y ^ 2 = sliderFilm h0 hL L y * sliderFilm h0 hL L y
        ring))
    have hD : HasDerivAt (fun y => (h0 ^ 2 - hL ^ 2) * sliderFilm h0 hL L y ^ 2)
        ((h0 ^ 2 - hL ^ 2) *
          (((hL - h0) / L) * sliderFilm h0 hL L x + sliderFilm h0 hL L x * ((hL - h0) / L))) x :=
      hD2.const_mul _
    have hDne : (h0 ^ 2 - hL ^ 2) * sliderFilm h0 hL L x ^ 2 ≠ 0 :=
      mul_ne_zero hsq_ne (pow_ne_zero 2 hfilm_ne)
    have hp0 := hN.div hD hDne
    have hF'eq : (((6 * μ * U * L) * ((0 - (hL - h0) / L) * (sliderFilm h0 hL L x - hL) +
          (h0 - sliderFilm h0 hL L x) * ((hL - h0) / L - 0))) *
          ((h0 ^ 2 - hL ^ 2) * sliderFilm h0 hL L x ^ 2) -
          ((6 * μ * U * L) * ((h0 - sliderFilm h0 hL L x) * (sliderFilm h0 hL L x - hL))) *
          ((h0 ^ 2 - hL ^ 2) *
            (((hL - h0) / L) * sliderFilm h0 hL L x + sliderFilm h0 hL L x * ((hL - h0) / L)))) /
          ((h0 ^ 2 - hL ^ 2) * sliderFilm h0 hL L x ^ 2) ^ 2 =
        sliderPressureGradient μ U h0 hL L x := by
      unfold sliderPressureGradient
      field_simp
      ring
    rw [← hF'eq]
    exact hp0.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => by
      change sliderPressure μ U h0 hL L y =
        ((fun y => (6 * μ * U * L) * ((h0 - sliderFilm h0 hL L y) * (sliderFilm h0 hL L y - hL))) /
          (fun y => (h0 ^ 2 - hL ^ 2) * sliderFilm h0 hL L y ^ 2)) y
      unfold sliderPressure
      simp only [Pi.div_apply]
      ring))
  · intro x hx
    apply HasDerivAt.hasDerivWithinAt
    have hpos : 0 < sliderFilm h0 hL L x := sliderFilm_pos h0pos hLpos hL0 hx
    have hfilm_ne : sliderFilm h0 hL L x ≠ 0 := ne_of_gt hpos
    have hh : HasDerivAt (sliderFilm h0 hL L) ((hL - h0) / L) x := hasDerivAt_sliderFilm
    have hev := hh.continuousAt.eventually_ne hfilm_ne
    have hsub : HasDerivAt (fun y => sliderFilm h0 hL L y - 2 * h0 * hL / (h0 + hL))
        ((hL - h0) / L - 0) x :=
      hh.sub (hasDerivAt_const x (2 * h0 * hL / (h0 + hL)))
    have hRHS0 : HasDerivAt
        (fun y => (6 * μ * U) * (sliderFilm h0 hL L y - 2 * h0 * hL / (h0 + hL)))
        ((6 * μ * U) * ((hL - h0) / L - 0)) x :=
      hsub.const_mul _
    have hval : (6 * μ * U) * ((hL - h0) / L - 0) = 6 * μ * U * ((hL - h0) / L) := by ring
    rw [hval] at hRHS0
    exact hRHS0.congr_of_eventuallyEq (hev.mono (fun y hy => by
      change sliderFilm h0 hL L y ^ 3 * sliderPressureGradient μ U h0 hL L y =
        (6 * μ * U) * (sliderFilm h0 hL L y - 2 * h0 * hL / (h0 + hL))
      unfold sliderPressureGradient
      field_simp))
  · have h0eq : sliderFilm h0 hL L 0 = h0 := sliderFilm_zero
    unfold sliderPressure
    rw [h0eq]
    simp
  · have hLeq : sliderFilm h0 hL L L = hL := sliderFilm_right hL0
    unfold sliderPressure
    rw [hLeq]
    simp

/-- Uniqueness: for positive end thicknesses `h0 ≠ hL` and `L > 0`, every solution of the
stated Reynolds model is the closed-form pressure on `[0, L]`. -/
lemma isReynoldsSolution_unique {μ U h0 hL L : ℝ} {p p' : ℝ → ℝ} (h0pos : 0 < h0)
    (hLpos : 0 < hL) (hne : h0 ≠ hL) (hL0 : 0 < L)
    (hp : IsReynoldsSolution μ U h0 hL L p p') :
    ∀ x ∈ Set.Icc 0 L, p x = sliderPressure μ U h0 hL L x := by
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
  have hP := sliderPressure_isReynoldsSolution (μ := μ) (U := U) h0pos hLpos hne hL0
  obtain ⟨hP1, hP2, hP3, hP4⟩ := hP
  have hLne : L ≠ 0 := ne_of_gt hL0
  have hdiff_ne : h0 - hL ≠ 0 := sub_ne_zero.mpr hne
  have hsq_ne : h0 ^ 2 - hL ^ 2 ≠ 0 := by
    have hfac : h0 ^ 2 - hL ^ 2 = (h0 - hL) * (h0 + hL) := by ring
    rw [hfac]
    exact mul_ne_zero hdiff_ne (ne_of_gt (add_pos h0pos hLpos))
  have hslope_ne : (hL - h0) / L ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr (Ne.symm hne)) hLne
  have hq : ∀ x ∈ Set.Icc 0 L,
      HasDerivWithinAt (fun y => sliderFilm h0 hL L y ^ 3 * p' y - sliderFilm h0 hL L y ^ 3 *
        sliderPressureGradient μ U h0 hL L y) 0 (Set.Icc 0 L) x := by
    intro x hx
    have hKK : (6 * μ * U * ((hL - h0) / L)) - (6 * μ * U * ((hL - h0) / L)) = 0 :=
      sub_self _
    have h' : HasDerivWithinAt
        (fun y => sliderFilm h0 hL L y ^ 3 * p' y - sliderFilm h0 hL L y ^ 3 *
          sliderPressureGradient μ U h0 hL L y)
        ((6 * μ * U * ((hL - h0) / L)) - (6 * μ * U * ((hL - h0) / L))) (Set.Icc 0 L) x :=
      (hp2 x hx).sub (hP2 x hx)
    rw [hKK] at h'
    exact h'
  have hqconst : ∀ x ∈ Set.Icc 0 L,
      (sliderFilm h0 hL L x ^ 3 * p' x - sliderFilm h0 hL L x ^ 3 *
        sliderPressureGradient μ U h0 hL L x) =
      (sliderFilm h0 hL L 0 ^ 3 * p' 0 - sliderFilm h0 hL L 0 ^ 3 *
        sliderPressureGradient μ U h0 hL L 0) :=
    const_of_hasDerivWithinAt_zero hq
  set C := sliderFilm h0 hL L 0 ^ 3 * p' 0 - sliderFilm h0 hL L 0 ^ 3 *
    sliderPressureGradient μ U h0 hL L 0
  have hG : ∀ x ∈ Set.Icc 0 L,
      HasDerivAt (fun y => (-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L y ^ 2)⁻¹)
        ((sliderFilm h0 hL L x ^ 3)⁻¹) x := by
    intro x hx
    have hpos : 0 < sliderFilm h0 hL L x := sliderFilm_pos h0pos hLpos hL0 hx
    have hfilm_ne : sliderFilm h0 hL L x ≠ 0 := ne_of_gt hpos
    have hh : HasDerivAt (sliderFilm h0 hL L) ((hL - h0) / L) x := hasDerivAt_sliderFilm
    have hD2' : HasDerivAt (fun y => sliderFilm h0 hL L y * sliderFilm h0 hL L y)
        (((hL - h0) / L) * sliderFilm h0 hL L x + sliderFilm h0 hL L x * ((hL - h0) / L)) x :=
      hh.mul hh
    have hD2 : HasDerivAt (fun y => sliderFilm h0 hL L y ^ 2)
        (((hL - h0) / L) * sliderFilm h0 hL L x + sliderFilm h0 hL L x * ((hL - h0) / L)) x :=
      hD2'.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => by
        change sliderFilm h0 hL L y ^ 2 = sliderFilm h0 hL L y * sliderFilm h0 hL L y
        ring))
    have hD2ne : sliderFilm h0 hL L x ^ 2 ≠ 0 := pow_ne_zero 2 hfilm_ne
    have hinv : HasDerivAt (fun y => (sliderFilm h0 hL L y ^ 2)⁻¹)
        (-(((hL - h0) / L) * sliderFilm h0 hL L x + sliderFilm h0 hL L x * ((hL - h0) / L)) /
          (sliderFilm h0 hL L x ^ 2) ^ 2) x :=
      hD2.inv hD2ne
    have hG0 : HasDerivAt (fun y => (-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L y ^ 2)⁻¹)
        ((-(1 / (2 * ((hL - h0) / L)))) * (-(((hL - h0) / L) * sliderFilm h0 hL L x +
          sliderFilm h0 hL L x * ((hL - h0) / L)) / (sliderFilm h0 hL L x ^ 2) ^ 2)) x :=
      hinv.const_mul _
    have hG'eq : ((-(1 / (2 * ((hL - h0) / L)))) * (-(((hL - h0) / L) * sliderFilm h0 hL L x +
          sliderFilm h0 hL L x * ((hL - h0) / L)) / (sliderFilm h0 hL L x ^ 2) ^ 2)) =
        (sliderFilm h0 hL L x ^ 3)⁻¹ := by
      field_simp
      ring
    rw [hG'eq] at hG0
    exact hG0
  have hr : ∀ x ∈ Set.Icc 0 L,
      HasDerivWithinAt (fun y => (p y - sliderPressure μ U h0 hL L y) - C *
        ((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L y ^ 2)⁻¹)) 0 (Set.Icc 0 L) x := by
    intro x hx
    have hpos : 0 < sliderFilm h0 hL L x := sliderFilm_pos h0pos hLpos hL0 hx
    have hfilm_ne : sliderFilm h0 hL L x ≠ 0 := ne_of_gt hpos
    have hsub1 : HasDerivWithinAt (fun y => p y - sliderPressure μ U h0 hL L y)
        (p' x - sliderPressureGradient μ U h0 hL L x) (Set.Icc 0 L) x :=
      (hp1 x hx).sub (hP1 x hx)
    have hCG : HasDerivWithinAt
        (fun y => C * ((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L y ^ 2)⁻¹))
        (C * (sliderFilm h0 hL L x ^ 3)⁻¹) (Set.Icc 0 L) x :=
      (hG x hx).hasDerivWithinAt.const_mul C
    have hr0 : HasDerivWithinAt
        (fun y => (p y - sliderPressure μ U h0 hL L y) - C *
          ((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L y ^ 2)⁻¹))
        ((p' x - sliderPressureGradient μ U h0 hL L x) - C * (sliderFilm h0 hL L x ^ 3)⁻¹)
        (Set.Icc 0 L) x :=
      hsub1.sub hCG
    have hqC : sliderFilm h0 hL L x ^ 3 * p' x - sliderFilm h0 hL L x ^ 3 *
        sliderPressureGradient μ U h0 hL L x = C := hqconst x hx
    have hfilm3_ne : sliderFilm h0 hL L x ^ 3 ≠ 0 := pow_ne_zero 3 hfilm_ne
    have hr'eq : (p' x - sliderPressureGradient μ U h0 hL L x) -
        C * (sliderFilm h0 hL L x ^ 3)⁻¹ = 0 := by
      field_simp
      linear_combination hqC
    rw [hr'eq] at hr0
    exact hr0
  have hrconst : ∀ x ∈ Set.Icc 0 L,
      ((p x - sliderPressure μ U h0 hL L x) - C *
        ((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L x ^ 2)⁻¹)) =
      ((p 0 - sliderPressure μ U h0 hL L 0) - C *
        ((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L 0 ^ 2)⁻¹)) :=
    const_of_hasDerivWithinAt_zero hr
  have hGdiff_ne : ((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L L ^ 2)⁻¹) -
      ((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L 0 ^ 2)⁻¹) ≠ 0 := by
    have hfilmL : sliderFilm h0 hL L L = hL := sliderFilm_right hL0
    have hfilm0 : sliderFilm h0 hL L 0 = h0 := sliderFilm_zero
    have ha : hL ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hLpos)
    have hb : h0 ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt h0pos)
    have h2s_ne : 2 * ((hL - h0) / L) ≠ 0 := mul_ne_zero (by norm_num) hslope_ne
    have hc_ne : (-(1 / (2 * ((hL - h0) / L)))) ≠ 0 :=
      neg_ne_zero.mpr (div_ne_zero one_ne_zero h2s_ne)
    have hsub_inv_ne : (hL ^ 2)⁻¹ - (h0 ^ 2)⁻¹ ≠ 0 := by
      have heq : (hL ^ 2)⁻¹ - (h0 ^ 2)⁻¹ = (h0 ^ 2 - hL ^ 2) / (hL ^ 2 * h0 ^ 2) := by
        field_simp
      rw [heq]
      exact div_ne_zero hsq_ne (mul_ne_zero ha hb)
    have hGdiff : ((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L L ^ 2)⁻¹) -
        ((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L 0 ^ 2)⁻¹) =
        (-(1 / (2 * ((hL - h0) / L)))) * ((hL ^ 2)⁻¹ - (h0 ^ 2)⁻¹) := by
      rw [hfilmL, hfilm0]
      ring
    rw [hGdiff]
    exact mul_ne_zero hc_ne hsub_inv_ne
  have hLmem : L ∈ Set.Icc 0 L := ⟨le_of_lt hL0, le_rfl⟩
  have hrL := hrconst L hLmem
  have hrL' : (p L - sliderPressure μ U h0 hL L L) - C *
      ((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L L ^ 2)⁻¹) =
      (p 0 - sliderPressure μ U h0 hL L 0) - C *
        ((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L 0 ^ 2)⁻¹) := hrL
  rw [hp3, hP3, hp4, hP4] at hrL'
  have hCeq : C * (((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L L ^ 2)⁻¹) -
      ((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L 0 ^ 2)⁻¹)) = 0 := by
    linear_combination -hrL'
  have hC0 : C = 0 := by
    rcases mul_eq_zero.mp hCeq with h | h
    · exact h
    · exact absurd h hGdiff_ne
  intro x hx
  have hrx := hrconst x hx
  have hrx' : (p x - sliderPressure μ U h0 hL L x) - C *
      ((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L x ^ 2)⁻¹) =
      (p 0 - sliderPressure μ U h0 hL L 0) - C *
        ((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L 0 ^ 2)⁻¹) := hrx
  rw [hC0, hp3, hP3] at hrx'
  simp only [zero_mul, sub_zero, sub_self] at hrx'
  exact sub_eq_zero.mp hrx'

/-! ### A.3. Positivity and load for the converging film -/

/-- For the converging film `h0 > hL > 0` with `μ, U, L > 0` the pressure is positive inside
the slider. -/
lemma sliderPressure_pos {μ U h0 hL L x : ℝ} (hμ : 0 < μ) (hU : 0 < U) (hL0 : 0 < L)
    (hLpos : 0 < hL) (hconv : hL < h0) (hx : x ∈ Set.Ioo 0 L) :
    0 < sliderPressure μ U h0 hL L x := by
  have h0pos : 0 < h0 := lt_trans hLpos hconv
  have hLne : L ≠ 0 := ne_of_gt hL0
  obtain ⟨hx0, hxL⟩ := hx
  have hxIcc : x ∈ Set.Icc 0 L := ⟨le_of_lt hx0, le_of_lt hxL⟩
  have hpos : 0 < sliderFilm h0 hL L x := sliderFilm_pos h0pos hLpos hL0 hxIcc
  have hdiff : 0 < h0 - hL := sub_pos.mpr hconv
  have e1 : h0 - sliderFilm h0 hL L x = (h0 - hL) * x / L := by
    unfold sliderFilm
    field_simp
    ring
  have e2 : sliderFilm h0 hL L x - hL = (h0 - hL) * (L - x) / L := by
    unfold sliderFilm
    field_simp
    ring
  have g1 : 0 < h0 - sliderFilm h0 hL L x := by
    rw [e1]
    exact div_pos (mul_pos hdiff hx0) hL0
  have g2 : 0 < sliderFilm h0 hL L x - hL := by
    rw [e2]
    exact div_pos (mul_pos hdiff (sub_pos.mpr hxL)) hL0
  have g3 : 0 < h0 ^ 2 - hL ^ 2 := by
    have hfac : h0 ^ 2 - hL ^ 2 = (h0 - hL) * (h0 + hL) := by ring
    rw [hfac]
    exact mul_pos hdiff (add_pos h0pos hLpos)
  have g4 : 0 < sliderFilm h0 hL L x ^ 2 := pow_pos hpos 2
  have n1 : (0 : ℝ) < 6 * μ * U * L :=
    mul_pos (mul_pos (mul_pos (by norm_num) hμ) hU) hL0
  unfold sliderPressure
  refine div_pos ?_ (mul_pos g3 g4)
  exact mul_pos (mul_pos n1 g1) g2

/-- Load per unit width in closed form, for positive end thicknesses `h0 ≠ hL` and `L > 0`:
`W = 6 μ U L² / (h0 - hL)² (log (h0 / hL) - 2 (h0 - hL) / (h0 + hL))`. -/
lemma sliderLoad_eq {μ U h0 hL L : ℝ} (h0pos : 0 < h0) (hLpos : 0 < hL) (hne : h0 ≠ hL)
    (hL0 : 0 < L) :
    sliderLoad μ U h0 hL L =
      6 * μ * U * L ^ 2 / (h0 - hL) ^ 2 *
        (Real.log (h0 / hL) - 2 * (h0 - hL) / (h0 + hL)) := by
  have hLne : L ≠ 0 := ne_of_gt hL0
  have h0ne : h0 ≠ 0 := ne_of_gt h0pos
  have hLne' : hL ≠ 0 := ne_of_gt hLpos
  have hsum_ne : h0 + hL ≠ 0 := ne_of_gt (add_pos h0pos hLpos)
  have hdiff_ne : h0 - hL ≠ 0 := sub_ne_zero.mpr hne
  have hLH_ne : hL - h0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hsq_ne : h0 ^ 2 - hL ^ 2 ≠ 0 := by
    have hfac : h0 ^ 2 - hL ^ 2 = (h0 - hL) * (h0 + hL) := by ring
    rw [hfac]
    exact mul_ne_zero hdiff_ne hsum_ne
  have hP := sliderPressure_isReynoldsSolution (μ := μ) (U := U) h0pos hLpos hne hL0
  obtain ⟨hP1, -, -, -⟩ := hP
  have hΦ : ∀ y ∈ Set.uIcc 0 L,
      HasDerivAt (fun t => (6 * μ * U * L ^ 2 / ((h0 ^ 2 - hL ^ 2) * (hL - h0))) *
        (-sliderFilm h0 hL L t + (h0 + hL) * Real.log (sliderFilm h0 hL L t) +
          (h0 * hL) / (sliderFilm h0 hL L t)))
        ((sliderPressure μ U h0 hL L) y) y := by
    intro y hy
    rw [Set.uIcc_of_le (le_of_lt hL0)] at hy
    have hpos : 0 < sliderFilm h0 hL L y := sliderFilm_pos h0pos hLpos hL0 hy
    have hfilm_ne : sliderFilm h0 hL L y ≠ 0 := ne_of_gt hpos
    have hh : HasDerivAt (sliderFilm h0 hL L) ((hL - h0) / L) y := hasDerivAt_sliderFilm
    have h1 : HasDerivAt (fun t => -sliderFilm h0 hL L t) (-((hL - h0) / L)) y := hh.neg
    have hlog : HasDerivAt (fun t => Real.log (sliderFilm h0 hL L t))
        (((hL - h0) / L) / sliderFilm h0 hL L y) y :=
      hh.log hfilm_ne
    have h2 : HasDerivAt (fun t => (h0 + hL) * Real.log (sliderFilm h0 hL L t))
        ((h0 + hL) * (((hL - h0) / L) / sliderFilm h0 hL L y)) y :=
      hlog.const_mul _
    have h3 : HasDerivAt (fun t => (h0 * hL) / (sliderFilm h0 hL L t))
        ((0 * sliderFilm h0 hL L y - (h0 * hL) * ((hL - h0) / L)) /
          (sliderFilm h0 hL L y) ^ 2) y :=
      (hasDerivAt_const y (h0 * hL)).div hh hfilm_ne
    have h12 : HasDerivAt
        (fun t => -sliderFilm h0 hL L t + (h0 + hL) * Real.log (sliderFilm h0 hL L t))
        ((-((hL - h0) / L)) + (h0 + hL) * (((hL - h0) / L) / sliderFilm h0 hL L y)) y :=
      h1.add h2
    have h123 : HasDerivAt
        (fun t => -sliderFilm h0 hL L t + (h0 + hL) * Real.log (sliderFilm h0 hL L t) +
          (h0 * hL) / (sliderFilm h0 hL L t))
        (((-((hL - h0) / L)) + (h0 + hL) * (((hL - h0) / L) / sliderFilm h0 hL L y)) +
          ((0 * sliderFilm h0 hL L y - (h0 * hL) * ((hL - h0) / L)) /
            (sliderFilm h0 hL L y) ^ 2)) y :=
      h12.add h3
    have hΦ0 : HasDerivAt
        (fun t => (6 * μ * U * L ^ 2 / ((h0 ^ 2 - hL ^ 2) * (hL - h0))) *
          (-sliderFilm h0 hL L t + (h0 + hL) * Real.log (sliderFilm h0 hL L t) +
            (h0 * hL) / (sliderFilm h0 hL L t)))
        ((6 * μ * U * L ^ 2 / ((h0 ^ 2 - hL ^ 2) * (hL - h0))) *
          (((-((hL - h0) / L)) + (h0 + hL) * (((hL - h0) / L) / sliderFilm h0 hL L y)) +
            ((0 * sliderFilm h0 hL L y - (h0 * hL) * ((hL - h0) / L)) /
              (sliderFilm h0 hL L y) ^ 2))) y :=
      h123.const_mul _
    have hΦ'eq : (6 * μ * U * L ^ 2 / ((h0 ^ 2 - hL ^ 2) * (hL - h0))) *
          (((-((hL - h0) / L)) + (h0 + hL) * (((hL - h0) / L) / sliderFilm h0 hL L y)) +
            ((0 * sliderFilm h0 hL L y - (h0 * hL) * ((hL - h0) / L)) /
              (sliderFilm h0 hL L y) ^ 2)) =
        sliderPressure μ U h0 hL L y := by
      unfold sliderPressure
      field_simp
      ring
    rw [hΦ'eq] at hΦ0
    exact hΦ0
  have hPcontIcc : ContinuousOn (sliderPressure μ U h0 hL L) (Set.Icc 0 L) := by
    intro y hy
    exact (hP1 y hy).continuousWithinAt
  have hPcont : ContinuousOn (sliderPressure μ U h0 hL L) (Set.uIcc 0 L) := by
    rw [Set.uIcc_of_le (le_of_lt hL0)]
    exact hPcontIcc
  have hPint : IntervalIntegrable (sliderPressure μ U h0 hL L) MeasureTheory.volume 0 L :=
    hPcont.intervalIntegrable
  have hInt := intervalIntegral.integral_eq_sub_of_hasDerivAt hΦ hPint
  have hLoad : sliderLoad μ U h0 hL L =
      (6 * μ * U * L ^ 2 / ((h0 ^ 2 - hL ^ 2) * (hL - h0))) *
        (-sliderFilm h0 hL L L + (h0 + hL) * Real.log (sliderFilm h0 hL L L) +
          (h0 * hL) / (sliderFilm h0 hL L L)) -
      (6 * μ * U * L ^ 2 / ((h0 ^ 2 - hL ^ 2) * (hL - h0))) *
        (-sliderFilm h0 hL L 0 + (h0 + hL) * Real.log (sliderFilm h0 hL L 0) +
          (h0 * hL) / (sliderFilm h0 hL L 0)) := hInt
  rw [hLoad, sliderFilm_right hL0, sliderFilm_zero, Real.log_div h0ne hLne']
  field_simp
  ring

/-- For the converging film `h0 > hL > 0` with `μ, U, L > 0` the load per unit width is
positive. -/
lemma sliderLoad_pos {μ U h0 hL L : ℝ} (hμ : 0 < μ) (hU : 0 < U) (hL0 : 0 < L)
    (hLpos : 0 < hL) (hconv : hL < h0) :
    0 < sliderLoad μ U h0 hL L := by
  have h0pos : 0 < h0 := lt_trans hLpos hconv
  have hne : h0 ≠ hL := ne_of_gt hconv
  have hP := sliderPressure_isReynoldsSolution (μ := μ) (U := U) h0pos hLpos hne hL0
  obtain ⟨hP1, -, -, hP4⟩ := hP
  have hcont : ContinuousOn (sliderPressure μ U h0 hL L) (Set.Icc 0 L) := by
    intro y hy
    exact (hP1 y hy).continuousWithinAt
  have hnonneg : ∀ x ∈ Set.Ioc 0 L, 0 ≤ sliderPressure μ U h0 hL L x := by
    intro x hx
    obtain ⟨hx0, hxL⟩ := hx
    by_cases h : x < L
    · exact le_of_lt (sliderPressure_pos hμ hU hL0 hLpos hconv ⟨hx0, h⟩)
    · have hxeq : x = L := le_antisymm hxL (not_lt.mp h)
      subst hxeq
      rw [hP4]
  have hmid : L / 2 ∈ Set.Ioo 0 L := ⟨by linarith, by linarith⟩
  have hex : ∃ c ∈ Set.Icc 0 L, 0 < sliderPressure μ U h0 hL L c :=
    ⟨L / 2, ⟨le_of_lt hmid.1, le_of_lt hmid.2⟩,
      sliderPressure_pos hμ hU hL0 hLpos hconv hmid⟩
  unfold sliderLoad
  exact intervalIntegral.integral_pos hL0 hcont hnonneg hex

/-! ### A.4. Diverging and closed films -/

/-- A diverging film `0 < h0 < hL` with `μ, U, L > 0` gives negative pressure inside the
slider, so the no-cavitation model fails there. -/
lemma sliderPressure_neg_of_diverging {μ U h0 hL L x : ℝ} (hμ : 0 < μ) (hU : 0 < U)
    (hL0 : 0 < L) (h0pos : 0 < h0) (hdiv : h0 < hL) (hx : x ∈ Set.Ioo 0 L) :
    sliderPressure μ U h0 hL L x < 0 := by
  have hLpos : 0 < hL := lt_trans h0pos hdiv
  have hLne : L ≠ 0 := ne_of_gt hL0
  obtain ⟨hx0, hxL⟩ := hx
  have hxIcc : x ∈ Set.Icc 0 L := ⟨le_of_lt hx0, le_of_lt hxL⟩
  have hpos : 0 < sliderFilm h0 hL L x := sliderFilm_pos h0pos hLpos hL0 hxIcc
  have hdiff : h0 - hL < 0 := sub_neg.mpr hdiv
  have e1 : h0 - sliderFilm h0 hL L x = (h0 - hL) * x / L := by
    unfold sliderFilm
    field_simp
    ring
  have e2 : sliderFilm h0 hL L x - hL = (h0 - hL) * (L - x) / L := by
    unfold sliderFilm
    field_simp
    ring
  have g1 : h0 - sliderFilm h0 hL L x < 0 := by
    rw [e1]
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hdiff hx0) hL0
  have g2 : sliderFilm h0 hL L x - hL < 0 := by
    rw [e2]
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hdiff (sub_pos.mpr hxL)) hL0
  have g3 : h0 ^ 2 - hL ^ 2 < 0 := by
    have hfac : h0 ^ 2 - hL ^ 2 = (h0 - hL) * (h0 + hL) := by ring
    rw [hfac]
    exact mul_neg_of_neg_of_pos hdiff (add_pos h0pos hLpos)
  have g4 : 0 < sliderFilm h0 hL L x ^ 2 := pow_pos hpos 2
  have n1 : (0 : ℝ) < 6 * μ * U * L :=
    mul_pos (mul_pos (mul_pos (by norm_num) hμ) hU) hL0
  have npos : 0 < 6 * μ * U * L * (h0 - sliderFilm h0 hL L x) * (sliderFilm h0 hL L x - hL) := by
    have hprod : 0 < (h0 - sliderFilm h0 hL L x) * (sliderFilm h0 hL L x - hL) :=
      mul_pos_of_neg_of_neg g1 g2
    have heq : 6 * μ * U * L * (h0 - sliderFilm h0 hL L x) * (sliderFilm h0 hL L x - hL) =
        (6 * μ * U * L) * ((h0 - sliderFilm h0 hL L x) * (sliderFilm h0 hL L x - hL)) := by
      ring
    rw [heq]
    exact mul_pos n1 hprod
  have dneg : (h0 ^ 2 - hL ^ 2) * sliderFilm h0 hL L x ^ 2 < 0 := mul_neg_of_neg_of_pos g3 g4
  unfold sliderPressure
  exact div_neg_of_pos_of_neg npos dneg

/-- An outlet thickness `hL = 0` is rejected: for `h0, μ, U, L > 0` the stated Reynolds model
with the film closing at `x = L` has no solution. -/
lemma not_isReynoldsSolution_of_hL_eq_zero {μ U h0 L : ℝ} {p p' : ℝ → ℝ} (hμ : 0 < μ)
    (hU : 0 < U) (h0pos : 0 < h0) (hL0 : 0 < L) :
    ¬ IsReynoldsSolution μ U h0 0 L p p' := by
  intro hp
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
  have hLne : L ≠ 0 := ne_of_gt hL0
  have hr0 : ∀ x ∈ Set.Icc 0 L,
      HasDerivWithinAt
        (fun y => sliderFilm h0 0 L y ^ 3 * p' y - (6 * μ * U) * sliderFilm h0 0 L y) 0
        (Set.Icc 0 L) x := by
    intro x hx
    have h6 : HasDerivAt (fun y => (6 * μ * U) * sliderFilm h0 0 L y)
        ((6 * μ * U) * ((0 - h0) / L)) x :=
      HasDerivAt.const_mul _ hasDerivAt_sliderFilm
    have hKK : (6 * μ * U * ((0 - h0) / L)) - (6 * μ * U) * ((0 - h0) / L) = 0 := by ring
    have h' : HasDerivWithinAt
        (fun y => sliderFilm h0 0 L y ^ 3 * p' y - (6 * μ * U) * sliderFilm h0 0 L y)
        ((6 * μ * U * ((0 - h0) / L)) - (6 * μ * U) * ((0 - h0) / L)) (Set.Icc 0 L) x :=
      (hp2 x hx).sub h6.hasDerivWithinAt
    rw [hKK] at h'
    exact h'
  have hrconst : ∀ x ∈ Set.Icc 0 L,
      (sliderFilm h0 0 L x ^ 3 * p' x - (6 * μ * U) * sliderFilm h0 0 L x) =
      (sliderFilm h0 0 L 0 ^ 3 * p' 0 - (6 * μ * U) * sliderFilm h0 0 L 0) :=
    const_of_hasDerivWithinAt_zero hr0
  have hfilmL0 : sliderFilm h0 0 L L = 0 := sliderFilm_right hL0
  have hLmem : L ∈ Set.Icc 0 L := ⟨le_of_lt hL0, le_rfl⟩
  have hrL := hrconst L hLmem
  have hrL' : sliderFilm h0 0 L L ^ 3 * p' L - (6 * μ * U) * sliderFilm h0 0 L L =
      sliderFilm h0 0 L 0 ^ 3 * p' 0 - (6 * μ * U) * sliderFilm h0 0 L 0 := hrL
  rw [hfilmL0] at hrL'
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, mul_zero,
    sub_self] at hrL'
  have hr0eq : sliderFilm h0 0 L 0 ^ 3 * p' 0 - (6 * μ * U) * sliderFilm h0 0 L 0 = 0 :=
    hrL'.symm
  have hr_zero : ∀ y ∈ Set.Icc 0 L,
      sliderFilm h0 0 L y ^ 3 * p' y - (6 * μ * U) * sliderFilm h0 0 L y = 0 := by
    intro y hy
    have h2 : sliderFilm h0 0 L y ^ 3 * p' y - (6 * μ * U) * sliderFilm h0 0 L y =
        sliderFilm h0 0 L 0 ^ 3 * p' 0 - (6 * μ * U) * sliderFilm h0 0 L 0 :=
      hrconst y hy
    rw [hr0eq] at h2
    exact h2
  have hcont : ContinuousOn p (Set.Icc 0 L) := by
    intro y hy
    exact (hp1 y hy).continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioo 0 L, HasDerivAt p (p' x) x := by
    intro x hx
    obtain ⟨hx0, hxL⟩ := hx
    exact (hp1 x ⟨le_of_lt hx0, le_of_lt hxL⟩).hasDerivAt (Icc_mem_nhds hx0 hxL)
  obtain ⟨c, hcIoo, hceq⟩ := exists_hasDerivAt_eq_slope p p' hL0 hcont hderiv
  obtain ⟨hc0, hcL⟩ := hcIoo
  have hcIcc : c ∈ Set.Icc 0 L := ⟨le_of_lt hc0, le_of_lt hcL⟩
  have hposc : 0 < sliderFilm h0 0 L c := by
    have e : sliderFilm h0 0 L c = h0 * (L - c) / L := by
      unfold sliderFilm
      field_simp
      ring
    rw [e]
    exact div_pos (mul_pos h0pos (sub_pos.mpr hcL)) hL0
  have hnec : sliderFilm h0 0 L c ≠ 0 := ne_of_gt hposc
  have hry : sliderFilm h0 0 L c ^ 3 * p' c - (6 * μ * U) * sliderFilm h0 0 L c = 0 :=
    hr_zero c hcIcc
  have hmul : p' c * (sliderFilm h0 0 L c) ^ 3 = 6 * μ * U * (sliderFilm h0 0 L c) := by
    linear_combination hry
  have hcancel : p' c * (sliderFilm h0 0 L c) ^ 2 = 6 * μ * U := by
    have h2 : (p' c * (sliderFilm h0 0 L c) ^ 2) * (sliderFilm h0 0 L c) =
        (6 * μ * U) * (sliderFilm h0 0 L c) := by
      linear_combination hmul
    exact mul_right_cancel₀ hnec h2
  have h2ne : (sliderFilm h0 0 L c) ^ 2 ≠ 0 := pow_ne_zero 2 hnec
  have hp'_eq : p' c = 6 * μ * U / ((sliderFilm h0 0 L c) ^ 2) :=
    (eq_div_iff h2ne).mpr hcancel
  have h6pos : (0 : ℝ) < 6 * μ * U := mul_pos (mul_pos (by norm_num) hμ) hU
  have hpos' : 0 < p' c := by
    rw [hp'_eq]
    exact div_pos h6pos (pow_pos hposc 2)
  rw [hp3, hp4] at hceq
  simp at hceq
  linarith

/-! ## B. Scalar unilateral contact -/

open scoped InnerProductSpace

/-! ### B.1. The contact model -/

/-- The admissible displacements below a rigid obstacle at position `g`: the nonpenetration
constraint `u ≤ g`. -/
def admissibleSet (g : ℝ) : Set ℝ := Set.Iic g

/-- The linear spring `u ↦ k u` of stiffness `k`, as a continuous linear operator on `ℝ`. -/
noncomputable def stiffnessMap (k : ℝ) : ℝ →L[ℝ] ℝ := k • ContinuousLinearMap.id ℝ ℝ

/-- The contact displacement `min g (f / k)` of a spring of stiffness `k` under the load `f`
below an obstacle at `g`. -/
noncomputable def contactDisplacement (k g f : ℝ) : ℝ := min g (f / k)

/-- The magnitude `λ = f - k u` of the contact force; the obstacle pushes on the body with `-λ`
along increasing `u`. -/
def contactForce (k f u : ℝ) : ℝ := f - k * u

/-- The gap `g - u` between the obstacle and the body. -/
def contactGap (g u : ℝ) : ℝ := g - u

private lemma stiffnessMap_apply (k u : ℝ) : stiffnessMap k u = k * u := by
  simp [stiffnessMap, smul_eq_mul]

private lemma real_inner (x y : ℝ) : ⟪x, y⟫_ℝ = x * y := by
  have h : ⟪x, y⟫_ℝ = y * x := by simp [RCLike.inner_apply]
  exact h.trans (mul_comm y x)

/-- On `ℝ`, the inner product of the variational inequality is the product
`(k u - f) w`. -/
lemma inner_stiffnessMap_sub (k u f w : ℝ) :
    ⟪stiffnessMap k u - f, w⟫_ℝ = (k * u - f) * w := by
  rw [stiffnessMap_apply, real_inner]

/-! ### B.2. The hypotheses of Stampacchia's theorem -/

/-- The admissible set is nonempty: it contains the obstacle position. -/
lemma admissibleSet_nonempty (g : ℝ) : (admissibleSet g).Nonempty := by
  exact ⟨g, le_refl g⟩

/-- The admissible set is closed. -/
lemma isClosed_admissibleSet (g : ℝ) : IsClosed (admissibleSet g) := by
  unfold admissibleSet
  exact isClosed_Iic

/-- The admissible set is convex. -/
lemma convex_admissibleSet (g : ℝ) : Convex ℝ (admissibleSet g) := by
  unfold admissibleSet
  exact convex_Iic g

/-- A spring of positive stiffness is coercive, in the form of the hypothesis of Stampacchia's
theorem: `α ‖u‖ ^ 2 ≤ ⟪k u, u⟫` for some `α > 0` (namely `α = k`). -/
lemma stiffnessMap_coercive {k : ℝ} (hk : 0 < k) :
    ∃ α : ℝ, 0 < α ∧ ∀ u : ℝ, α * ‖u‖ ^ 2 ≤ ⟪stiffnessMap k u, u⟫_ℝ := by
  refine ⟨k, hk, fun u => le_of_eq ?_⟩
  rw [stiffnessMap_apply, real_inner, Real.norm_eq_abs, sq_abs]
  ring

private lemma vi_iff_contactDisplacement {k : ℝ} (hk : 0 < k) (g f u : ℝ) :
    (u ∈ admissibleSet g ∧ ∀ v ∈ admissibleSet g, 0 ≤ ⟪stiffnessMap k u - f, v - u⟫_ℝ) ↔
      u = contactDisplacement k g f := by
  have hkne : k ≠ 0 := ne_of_gt hk
  have hka : k * (f / k) = f := mul_div_cancel₀ f hkne
  constructor
  · rintro ⟨hug, hvi⟩
    have hug' : u ≤ g := hug
    by_cases hcase : f / k ≤ g
    · have hva : f / k ∈ admissibleSet g := hcase
      have h1 := hvi (f / k) hva
      rw [inner_stiffnessMap_sub] at h1
      have heq : k * u - f = k * (u - f / k) := by
        have h : k * (u - f / k) = k * u - f := by rw [mul_sub, hka]
        exact h.symm
      rw [heq] at h1
      have hsq : k * (u - f / k) * (f / k - u) = -(k * (u - f / k) ^ 2) := by ring
      rw [hsq] at h1
      have hle : k * (u - f / k) ^ 2 ≤ 0 := by linarith
      have hnn : 0 ≤ k * (u - f / k) ^ 2 := mul_nonneg (le_of_lt hk) (sq_nonneg _)
      have hsq0 : (u - f / k) ^ 2 = 0 :=
        (mul_eq_zero.mp (le_antisymm hle hnn)).resolve_left hkne
      have hdiff : u - f / k = 0 := sq_eq_zero_iff.mp hsq0
      have hueq : u = f / k := sub_eq_zero.mp hdiff
      have hmin : contactDisplacement k g f = f / k := min_eq_right hcase
      rw [hmin]
      exact hueq
    · push Not at hcase
      have hgu : g ≤ u := by
        by_contra hcon
        push Not at hcon
        have hvg : g ∈ admissibleSet g := le_refl g
        have h1 := hvi g hvg
        rw [inner_stiffnessMap_sub] at h1
        have hua : u < f / k := lt_of_lt_of_le hcon (le_of_lt hcase)
        have hmul : k * u < k * (f / k) := mul_lt_mul_of_pos_left hua hk
        rw [hka] at hmul
        have hneg : k * u - f < 0 := by linarith
        have hpos : (0 : ℝ) < g - u := by linarith
        have hneg2 : (k * u - f) * (g - u) < 0 := mul_neg_of_neg_of_pos hneg hpos
        linarith
      have hmin : contactDisplacement k g f = g := min_eq_left (le_of_lt hcase)
      have hueq : u = g := le_antisymm hug' hgu
      rw [hmin]
      exact hueq
  · intro hueq
    have hmin : u = min g (f / k) := hueq
    refine ⟨?_, ?_⟩
    · change u ≤ g
      rw [hmin]
      exact min_le_left g (f / k)
    · intro v hv
      have hv' : v ≤ g := hv
      rw [inner_stiffnessMap_sub]
      by_cases hcase : f / k ≤ g
      · have hueq2 : u = f / k := by rw [hmin, min_eq_right hcase]
        have hzero : k * u - f = 0 := by rw [hueq2, sub_eq_zero.mpr hka]
        simp [hzero]
      · push Not at hcase
        have hueq2 : u = g := by rw [hmin, min_eq_left (le_of_lt hcase)]
        have h1 : k * u - f ≤ 0 := by
          rw [hueq2]
          have hmul : k * g < k * (f / k) := mul_lt_mul_of_pos_left hcase hk
          rw [hka] at hmul
          linarith
        have h2 : v - u ≤ 0 := by
          rw [hueq2]
          linarith
        exact mul_nonneg_of_nonpos_of_nonpos h1 h2

/-! ### B.3. Existence, uniqueness and the contact displacement -/

/-- **Scalar unilateral contact as a Stampacchia variational inequality.** For `k > 0`, the
instance of Stampacchia's theorem with `K = admissibleSet g`, `A = stiffnessMap k` and right-hand
side `f`: exactly one admissible `u` satisfies `0 ≤ ⟪k u - f, v - u⟫` for every admissible
`v`. -/
lemma existsUnique_contact {k : ℝ} (hk : 0 < k) (g f : ℝ) :
    ∃! u, u ∈ admissibleSet g ∧
      ∀ v ∈ admissibleSet g, 0 ≤ ⟪stiffnessMap k u - f, v - u⟫_ℝ := by
  obtain ⟨α, hα, hcoer⟩ := stiffnessMap_coercive hk
  exact MathlibExt.Analysis.InnerProductSpace.Stampacchia.exists_unique_stampacchia
    (admissibleSet_nonempty g) (isClosed_admissibleSet g) (convex_admissibleSet g)
    (stiffnessMap k) hα hcoer f

/-- The solution of the contact variational inequality is the contact displacement
`min g (f / k)`. -/
lemma contact_vi_iff {k : ℝ} (hk : 0 < k) (g f u : ℝ) :
    (u ∈ admissibleSet g ∧ ∀ v ∈ admissibleSet g, 0 ≤ ⟪stiffnessMap k u - f, v - u⟫_ℝ) ↔
      u = contactDisplacement k g f := by
  exact vi_iff_contactDisplacement hk g f u

/-! ### B.4. Complementarity -/

/-- **Complementarity from the variational inequality.** A solution of the contact
variational inequality has a nonnegative contact force `λ = f - k u`, a nonnegative gap `g - u`,
and `λ (g - u) = 0`: the force vanishes off contact and the gap vanishes under load. -/
lemma complementarity_of_vi {k g f u : ℝ}
    (hu : u ∈ admissibleSet g ∧ ∀ v ∈ admissibleSet g, 0 ≤ ⟪stiffnessMap k u - f, v - u⟫_ℝ) :
    0 ≤ contactForce k f u ∧ 0 ≤ contactGap g u ∧ contactForce k f u * contactGap g u = 0 := by
  have hug : u ≤ g := hu.1
  have hgap : (0 : ℝ) ≤ g - u := by linarith
  have hv : u - 1 ∈ admissibleSet g := by
    change u - 1 ≤ g
    linarith
  have h1 := hu.2 (u - 1) hv
  rw [inner_stiffnessMap_sub] at h1
  have hring : (k * u - f) * ((u - 1) - u) = -((k * u - f)) := by ring
  rw [hring] at h1
  have hle : k * u - f ≤ 0 := by linarith
  have hlam : (0 : ℝ) ≤ f - k * u := by linarith
  have hvg : g ∈ admissibleSet g := le_refl g
  have h2 := hu.2 g hvg
  rw [inner_stiffnessMap_sub] at h2
  have h3 : (k * u - f) * (g - u) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle hgap
  have heq : (k * u - f) * (g - u) = 0 := le_antisymm h3 h2
  have hforce : contactForce k f u = f - k * u := rfl
  have hgapdef : contactGap g u = g - u := rfl
  rw [hforce, hgapdef]
  refine ⟨hlam, hgap, ?_⟩
  have hfactor : (f - k * u) * (g - u) = -((k * u - f) * (g - u)) := by ring
  rw [hfactor, heq, neg_zero]

/-- The contact displacement `u = min g (f / k)` satisfies the complementarity conditions
`λ ≥ 0`, `g - u ≥ 0` and `λ (g - u) = 0` with `λ = f - k u`. -/
lemma contactDisplacement_complementarity {k : ℝ} (hk : 0 < k) (g f : ℝ) :
    0 ≤ contactForce k f (contactDisplacement k g f) ∧
      0 ≤ contactGap g (contactDisplacement k g f) ∧
      contactForce k f (contactDisplacement k g f) * contactGap g (contactDisplacement k g f) =
        0 := by
  have hvi := (contact_vi_iff hk g f (contactDisplacement k g f)).mpr rfl
  exact complementarity_of_vi hvi

/-! ## C. Coulomb friction -/

/-! ### C.1. The friction graph -/

/-- The declared scalar Coulomb friction graph with coefficient `μ` and normal force `N`: at a
nonzero sliding velocity `v` the friction force is `F = -μ N sign v`, and at `v = 0` it may take
any value in `[-μ N, μ N]`. -/
def IsCoulombFriction (μ N v F : ℝ) : Prop :=
  (v ≠ 0 → F = -(μ * N) * Real.sign v) ∧ (v = 0 → F ∈ Set.Icc (-(μ * N)) (μ * N))

/-- Slip: at a nonzero velocity the law determines the force, `F = -μ N sign v`. -/
lemma isCoulombFriction_of_ne_zero {μ N v F : ℝ} (hv : v ≠ 0) :
    IsCoulombFriction μ N v F ↔ F = -(μ * N) * Real.sign v := by
  constructor
  · intro h
    obtain ⟨hslip, -⟩ := h
    exact hslip hv
  · intro hF
    constructor
    · intro _
      exact hF
    · intro h0
      exact absurd h0 hv

/-- Stick: at zero velocity the admissible forces are exactly the interval `[-μ N, μ N]`. -/
lemma isCoulombFriction_zero {μ N F : ℝ} :
    IsCoulombFriction μ N 0 F ↔ F ∈ Set.Icc (-(μ * N)) (μ * N) := by
  constructor
  · intro h
    obtain ⟨-, hstick⟩ := h
    exact hstick rfl
  · intro hF
    constructor
    · intro h0
      exact absurd rfl h0
    · intro _
      exact hF

/-! ### C.2. Friction power and dissipation -/

/-- The friction power `F v`, delivered by the friction force to the body, is `-μ N |v|` on the
graph, at slip and at stick. -/
lemma coulomb_power_eq {μ N v F : ℝ} (h : IsCoulombFriction μ N v F) :
    F * v = -(μ * N * |v|) := by
  by_cases hv : v = 0
  · subst hv
    simp
  · obtain ⟨hslip, -⟩ := h
    have hF := hslip hv
    have hsign : Real.sign v * v = |v| := by
      rcases lt_or_gt_of_ne hv with hneg | hpos
      · rw [Real.sign_of_neg hneg, abs_of_neg hneg]
        ring
      · rw [Real.sign_of_pos hpos, abs_of_pos hpos]
        ring
    rw [hF]
    calc (-(μ * N) * Real.sign v) * v
        = -(μ * N) * (Real.sign v * v) := by ring
      _ = -(μ * N) * |v| := by rw [hsign]
      _ = -(μ * N * |v|) := by ring

/-- Dissipation: for `μ, N ≥ 0` the friction force never supplies power, `F v ≤ 0`. -/
lemma coulomb_power_nonpos {μ N v F : ℝ} (hμ : 0 ≤ μ) (hN : 0 ≤ N)
    (h : IsCoulombFriction μ N v F) :
    F * v ≤ 0 := by
  rw [coulomb_power_eq h]
  have hnn : 0 ≤ μ * N * |v| := mul_nonneg (mul_nonneg hμ hN) (abs_nonneg v)
  linarith

/-! ### C.3. Static equilibrium and non-uniqueness at rest -/

/-- Static equilibrium: a body at rest under the applied tangential force `Fa` balances it with an
admissible stick force, `Fa + F = 0`, exactly when `Fa ∈ [-μ N, μ N]`. -/
lemma coulomb_static_equilibrium_iff {μ N Fa : ℝ} :
    (∃ F, IsCoulombFriction μ N 0 F ∧ Fa + F = 0) ↔ Fa ∈ Set.Icc (-(μ * N)) (μ * N) := by
  constructor
  · rintro ⟨F, hF, hadd⟩
    rw [isCoulombFriction_zero] at hF
    obtain ⟨hlo, hhi⟩ := Set.mem_Icc.mp hF
    exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  · intro hFa
    refine ⟨-Fa, ?_, add_neg_cancel Fa⟩
    rw [isCoulombFriction_zero]
    obtain ⟨hlo, hhi⟩ := Set.mem_Icc.mp hFa
    exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩

/-- At rest the law does not determine the friction force: for `μ, N > 0` two different forces
are admissible at `v = 0`. -/
lemma coulomb_stick_not_unique {μ N : ℝ} (hμ : 0 < μ) (hN : 0 < N) :
    ∃ F₁ F₂, F₁ ≠ F₂ ∧ IsCoulombFriction μ N 0 F₁ ∧ IsCoulombFriction μ N 0 F₂ := by
  have hpos : 0 < μ * N := mul_pos hμ hN
  refine ⟨0, μ * N, ne_of_lt hpos, ?_, ?_⟩ <;> rw [isCoulombFriction_zero]
  · exact Set.mem_Icc.mpr ⟨neg_nonpos.mpr (le_of_lt hpos), le_of_lt hpos⟩
  · exact Set.mem_Icc.mpr ⟨neg_le_self (le_of_lt hpos), le_rfl⟩

/-! ### C.4. Negative coefficient -/

/-- A negative coefficient admits no stick force: for `μ < 0 < N` the interval `[-μ N, μ N]` is
empty, so no force is admissible at rest. -/
lemma coulomb_not_exists_stick_of_neg {μ N : ℝ} (hμ : μ < 0) (hN : 0 < N) :
    ¬ ∃ F, IsCoulombFriction μ N 0 F := by
  rintro ⟨F, hF⟩
  rw [isCoulombFriction_zero] at hF
  obtain ⟨hlo, hhi⟩ := Set.mem_Icc.mp hF
  have hneg : μ * N < 0 := mul_neg_of_neg_of_pos hμ hN
  linarith

/-- A negative coefficient makes slip supply power: for `μ < 0 < N` and `v ≠ 0`, every force on
the graph has `F v > 0`. -/
lemma coulomb_slip_power_pos_of_neg {μ N v F : ℝ} (hμ : μ < 0) (hN : 0 < N) (hv : v ≠ 0)
    (h : IsCoulombFriction μ N v F) :
    0 < F * v := by
  have hneg : μ * N < 0 := mul_neg_of_neg_of_pos hμ hN
  have habs : 0 < |v| := abs_pos.mpr hv
  have hmul : μ * N * |v| < 0 := mul_neg_of_neg_of_pos hneg habs
  have hpow := coulomb_power_eq h
  linarith

/-! ## D. Unilateral contact with Coulomb friction -/

open scoped InnerProductSpace

/-- The Coulomb friction cone in `(N, t)` coordinates, `‖t‖ ≤ μ * N` with `0 ≤ N`, for the
compression-positive normal force `N` and the tangent traction `t`. The inner product on `E`
is required by design, though unused in the body: it makes `‖·‖` the Euclidean norm, so the
cone is isotropic. -/
@[nolint unusedArguments]
def frictionCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (μ : ℝ) :
    Set (ℝ × E) :=
  {p | ‖p.2‖ ≤ μ * p.1 ∧ 0 ≤ p.1}

/-- An admissible contact state for the friction coefficient `μ`: compression-positive
normal force `0 ≤ N`, gap `0 ≤ g`, complementarity `N * g = 0`, and the Coulomb bound
`‖t‖ ≤ μ * N` on the tangent traction `t`, measured in the inner-product norm of `E`.
Physically meaningful for `0 ≤ μ`. -/
@[nolint unusedArguments]
def IsAdmissibleContact {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ N g : ℝ) (t : E) : Prop :=
  0 ≤ N ∧ 0 ≤ g ∧ N * g = 0 ∧ ‖t‖ ≤ μ * N

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Normal/tangent frame of an interface traction. For a unit normal `n` pointing out of the
body, the traction `τ` on the body splits as `τ = t - N • n` with `t` orthogonal to `n`
exactly when `N = -⟪τ, n⟫` is the compression-positive normal force and
`t = τ - ⟪τ, n⟫ • n` is the tangent traction. For a body with tension-positive Cauchy stress
`σ`, `τ` is the Cauchy traction `σ n` and `N` is the compression-positive normal stress. -/
lemma normal_tangent_decomposition_iff {n τ t : E} {N : ℝ} (hn : ‖n‖ = 1) :
    (τ = t - N • n ∧ ⟪t, n⟫_ℝ = 0) ↔ (N = -⟪τ, n⟫_ℝ ∧ t = τ - ⟪τ, n⟫_ℝ • n) := by
  have hnn : ⟪n, n⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hn, one_pow]
  constructor
  · rintro ⟨hτ, ht⟩
    have hinner : ⟪τ, n⟫_ℝ = -N := by
      rw [hτ, inner_sub_left, ht, real_inner_smul_left, hnn, mul_one, zero_sub]
    have hN' : N = -⟪τ, n⟫_ℝ := by linarith
    have ht' : t = τ + N • n := by
      rw [hτ]
      abel
    refine ⟨hN', ?_⟩
    rw [ht', hinner, neg_smul]
    abel
  · rintro ⟨hN, ht⟩
    refine ⟨?_, ?_⟩
    · rw [ht, hN, neg_smul]
      abel
    · rw [ht, inner_sub_left, real_inner_smul_left, hnn, mul_one, sub_self]

/-- Main result, convex part: for a friction coefficient `0 ≤ μ` the friction cone is convex
in `(N, t)`. This is the only convexity claim; the complementarity set is not convex
(`not_convex_complementarity`). -/
lemma convex_frictionCone {μ : ℝ} (hμ : 0 ≤ μ) :
    Convex ℝ (frictionCone (E := E) μ) := by
  intro x hx y hy a b ha hb _
  have _hμ : 0 ≤ μ := hμ
  simp only [frictionCone, Set.mem_ofPred_eq] at hx hy ⊢
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have h2 : (a • x + b • y).2 = a • x.2 + b • y.2 := by simp
  have h1 : (a • x + b • y).1 = a * x.1 + b * y.1 := by simp [smul_eq_mul]
  rw [h2, h1]
  constructor
  · have e1 : a * ‖x.2‖ ≤ a * (μ * x.1) := mul_le_mul_of_nonneg_left hx1 ha
    have e2 : b * ‖y.2‖ ≤ b * (μ * y.1) := mul_le_mul_of_nonneg_left hy1 hb
    have hnorm : ‖a • x.2‖ + ‖b • y.2‖ = a * ‖x.2‖ + b * ‖y.2‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ha, abs_of_nonneg hb]
    have hring : a * (μ * x.1) + b * (μ * y.1) = μ * (a * x.1 + b * y.1) := by ring
    have htri : ‖a • x.2 + b • y.2‖ ≤ ‖a • x.2‖ + ‖b • y.2‖ := norm_add_le _ _
    linarith [htri, hnorm, e1, e2, hring, _hμ]
  · exact add_nonneg (mul_nonneg ha hx2) (mul_nonneg hb hy2)

/-- Main result, non-convex part: the unilateral complementarity set
`{(N, g) | 0 ≤ N ∧ 0 ≤ g ∧ N * g = 0}` in the `(N, g)` plane, the union of the two
nonnegative half-axes, is not convex. -/
lemma not_convex_complementarity :
    ¬ Convex ℝ {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 * p.2 = 0} := by
  intro hconv
  have hp : ((1, 0) : ℝ × ℝ) ∈ {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 * p.2 = 0} := by
    show (0 : ℝ) ≤ 1 ∧ (0 : ℝ) ≤ 0 ∧ (1 : ℝ) * 0 = 0
    exact ⟨zero_le_one, le_rfl, mul_zero 1⟩
  have hq : ((0, 1) : ℝ × ℝ) ∈ {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 * p.2 = 0} := by
    show (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 ∧ (0 : ℝ) * 1 = 0
    exact ⟨le_rfl, zero_le_one, zero_mul 1⟩
  have hmid := hconv hp hq (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hpt : (1 / 2 : ℝ) • ((1, 0) : ℝ × ℝ) + (1 / 2 : ℝ) • ((0, 1) : ℝ × ℝ) =
      (1 / 2, 1 / 2) := by
    ext <;> simp [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  rw [hpt, Set.mem_ofPred_eq] at hmid
  obtain ⟨-, -, hprod⟩ := hmid
  have h12 : ((1 / 2, 1 / 2) : ℝ × ℝ).1 * (1 / 2, 1 / 2).2 = (1 / 2 : ℝ) * (1 / 2) := rfl
  rw [h12] at hprod
  norm_num at hprod

/-- Separated contact carries no force: an admissible contact state with an open gap
`0 < g` has zero normal force and zero tangent traction, for every `μ`. -/
lemma IsAdmissibleContact.eq_zero_of_gap_pos {μ N g : ℝ} {t : E}
    (h : IsAdmissibleContact μ N g t) (hg : 0 < g) :
    N = 0 ∧ t = 0 := by
  simp only [IsAdmissibleContact] at h
  obtain ⟨-, -, hNg, htb⟩ := h
  have hN0 : N = 0 := by
    rcases mul_eq_zero.mp hNg with hN | hg0
    · exact hN
    · exact absurd hg0 (ne_of_gt hg)
  refine ⟨hN0, ?_⟩
  rw [hN0, mul_zero] at htb
  have htnorm : ‖t‖ = 0 := le_antisymm htb (norm_nonneg _)
  exact norm_eq_zero.mp htnorm

/-- Frictionless slice: for `0 ≤ μ`, a contact state with zero tangent traction is admissible
exactly when `(N, g)` satisfies the scalar unilateral complementarity. This is the
conclusion shape of `Elasticity.ContactAndLubrication.complementarity_of_vi` with
`N = contactForce k f u` and the gap `contactGap x₀ u` of an obstacle at `x₀`, so the
frictionless scalar contact solution is admissible for every `0 ≤ μ`. -/
lemma isAdmissibleContact_zero_tangent_iff {μ N g : ℝ} (hμ : 0 ≤ μ) :
    IsAdmissibleContact μ N g (0 : E) ↔ 0 ≤ N ∧ 0 ≤ g ∧ N * g = 0 := by
  simp only [IsAdmissibleContact, norm_zero]
  constructor
  · rintro ⟨hN, hg, hNg, -⟩
    exact ⟨hN, hg, hNg⟩
  · rintro ⟨hN, hg, hNg⟩
    exact ⟨hN, hg, hNg, mul_nonneg hμ hN⟩

/-! ## E. Coulomb sliding and sticking at a unilateral interface -/

/-- The vector Coulomb friction law at a unilateral interface, with friction coefficient `μ`
and compression-positive normal force `N`: at a nonzero tangential slip velocity `v` the
tangent traction is `t = -(μ * N) • (‖v‖⁻¹ • v)`, of norm `|μ * N|` and opposite to `v` when
`0 < μ * N`; at `v = 0` (stick) it may be any `t` with `‖t‖ ≤ μ * N`. The stick branch
involves no division. Physically meaningful for `0 ≤ μ` and `0 ≤ N`. -/
def IsCoulombTraction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ N : ℝ) (v t : E) : Prop :=
  (v ≠ 0 → t = -(μ * N) • (‖v‖⁻¹ • v)) ∧ (v = 0 → ‖t‖ ≤ μ * N)


/-- Main result, frictional power: on the physical domain `0 ≤ μ`, `0 ≤ N` a Coulomb traction
delivers the power `⟪t, v⟫ = -(μ * N * ‖v‖) ≤ 0`. A sliding contact (`v ≠ 0`) dissipates
`μ * N * ‖v‖`; a sticking contact (`v = 0`) does no work, for every stick traction allowed
by the separate stick rule and without dividing by `‖v‖`. -/
lemma IsCoulombTraction.inner_eq_and_nonpos {μ N : ℝ} {v t : E} (hμ : 0 ≤ μ) (hN : 0 ≤ N)
    (h : IsCoulombTraction μ N v t) :
    ⟪t, v⟫_ℝ = -(μ * N * ‖v‖) ∧ ⟪t, v⟫_ℝ ≤ 0 := by
  by_cases hv : v = 0
  · subst hv
    rw [inner_zero_right, norm_zero, mul_zero, neg_zero]
    exact ⟨rfl, le_refl 0⟩
  · rw [h.1 hv, real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have hnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hpow : ‖v‖⁻¹ * ‖v‖ ^ 2 = ‖v‖ := by
      rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hnorm, one_mul]
    rw [hpow]
    have hNN : 0 ≤ μ * N * ‖v‖ := mul_nonneg (mul_nonneg hμ hN) (norm_nonneg _)
    have heq : -(μ * N) * ‖v‖ = -(μ * N * ‖v‖) := by ring
    rw [heq]
    exact ⟨rfl, neg_nonpos.mpr hNN⟩

/-- Control, invalid sign: if `μ * N < 0`, the stick rule admits no traction
(`‖t‖ ≤ μ * N < 0` is impossible), so every Coulomb traction is a sliding one and the friction
law supplies positive power. The sign in `IsCoulombTraction.inner_eq_and_nonpos` therefore
needs `0 ≤ μ * N`; both `μ < 0 < N` and `N < 0 < μ` reverse it. -/
lemma IsCoulombTraction.inner_pos_of_mul_neg {μ N : ℝ} {v t : E} (hμN : μ * N < 0)
    (h : IsCoulombTraction μ N v t) :
    0 < ⟪t, v⟫_ℝ := by
  by_cases hv : v = 0
  · exfalso
    have hle := h.2 hv
    have hnn : 0 ≤ ‖t‖ := norm_nonneg _
    linarith
  · rw [h.1 hv, real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have hnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hpow : ‖v‖⁻¹ * ‖v‖ ^ 2 = ‖v‖ := by
      rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hnorm, one_mul]
    rw [hpow]
    have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    exact mul_pos (neg_pos.mpr hμN) hpos

/-- Slip and stick tractions are admissible contact states: for `0 ≤ μ` and `0 ≤ N` a Coulomb
traction, sliding or sticking, is an admissible closed contact state (`g = 0`). A sliding
traction has norm `μ * N`, the slip threshold; a sticking traction satisfies the Coulomb
bound by the stick rule. -/
lemma IsCoulombTraction.isAdmissibleContact {μ N : ℝ} {v t : E} (hμ : 0 ≤ μ) (hN : 0 ≤ N)
    (h : IsCoulombTraction μ N v t) :
    IsAdmissibleContact μ N 0 t := by
  refine ⟨hN, le_refl 0, mul_zero N, ?_⟩
  by_cases hv : v = 0
  · exact h.2 hv
  · have hnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hmul : 0 ≤ μ * N := mul_nonneg hμ hN
    have hslide : ‖t‖ = μ * N := by
      rw [h.1 hv, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg hmul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ hnorm, mul_one]
    rw [hslide]

/-- On a tangent line, `E = ℝ`, the vector law is exactly the scalar Coulomb friction graph:
for `v ≠ 0`, `‖v‖⁻¹ • v = Real.sign v`, and `‖F‖ ≤ μ * N` holds iff
`F ∈ [-(μ * N), μ * N]`. -/
lemma isCoulombTraction_iff_isCoulombFriction {μ N v F : ℝ} :
    IsCoulombTraction μ N v F ↔ IsCoulombFriction μ N v F := by
  have hsign : ∀ {v : ℝ}, v ≠ 0 → |v|⁻¹ * v = Real.sign v := by
    intro v hv
    rcases lt_or_gt_of_ne hv with hneg | hpos
    · rw [Real.sign_of_neg hneg, abs_of_neg hneg, inv_neg, neg_mul,
        inv_mul_cancel₀ (ne_of_lt hneg)]
    · rw [Real.sign_of_pos hpos, abs_of_pos hpos, inv_mul_cancel₀ (ne_of_gt hpos)]
  unfold IsCoulombTraction IsCoulombFriction
  constructor
  · rintro ⟨hslip, hstick⟩
    refine ⟨fun hv => ?_, fun hv0 => ?_⟩
    · rw [hslip hv, smul_eq_mul, smul_eq_mul, Real.norm_eq_abs, hsign hv]
    · have hle := hstick hv0
      rw [Real.norm_eq_abs] at hle
      rw [Set.mem_Icc]
      exact abs_le.mp hle
  · rintro ⟨hslip, hstick⟩
    refine ⟨fun hv => ?_, fun hv0 => ?_⟩
    · rw [hslip hv, smul_eq_mul, smul_eq_mul, Real.norm_eq_abs, hsign hv]
    · have hmem := hstick hv0
      rw [Set.mem_Icc] at hmem
      rw [Real.norm_eq_abs]
      exact abs_le.mpr hmem


end Elasticity.ContactAndLubrication
