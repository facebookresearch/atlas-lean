/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_CerednikDrinfeld_DrinfeldUpperHalfPlane.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# The Drinfeld upper half plane and its theta functions

Let `K / K₀` be a field extension (`[Algebra K₀ K]`). The *Drinfeld upper half plane*
`upperHalfPlane K₀ K` is the set of points of `K` that do not come from `K₀`. These are exactly
the points of `ℙ¹(K) \ ℙ¹(K₀)`, since `∞` is `K₀`-rational. For `ℚ_p ⊆ ℂ_p` they are the
`ℂ_p`-points of Drinfeld's `p`-adic upper half plane; for `ℝ ⊆ ℂ` they form `ℂ \ ℝ`.

The group `PGL(2, K₀)` acts on the projective line `OnePoint K` by Möbius transformations
(through `algebraMap K₀ K`), and this action preserves the upper half plane.

## Main definitions

* `DrinfeldUpperHalfPlane.glAction`, `DrinfeldUpperHalfPlane.pglAction`: the actions of
  `GL(2, K₀)` and `PGL(2, K₀)` on `OnePoint K` (scoped instances).
* `DrinfeldUpperHalfPlane.moebius`: the affine Möbius formula `(a z + b) / (c z + d)`.
* `DrinfeldUpperHalfPlane.toAffine`, `DrinfeldUpperHalfPlane.pmoebius`: the affine reading of the
  projective action, a total function that reads `∞` as `0`.
* `DrinfeldUpperHalfPlane.upperHalfPlane`: the Drinfeld upper half plane.
* `DrinfeldUpperHalfPlane.crossRatio`, `DrinfeldUpperHalfPlane.thetaFactor`,
  `DrinfeldUpperHalfPlane.theta`, `DrinfeldUpperHalfPlane.ThetaMultipliable`: the theta function
  `θ(a, b; z) = ∏_γ [z, z₀; γ a, γ b]` attached to `ρ : G →* PGL(2, K₀)`.
* `DrinfeldUpperHalfPlane.IsAutomorphicWithMultiplier`, `DrinfeldUpperHalfPlane.IsInvariant`,
  `DrinfeldUpperHalfPlane.period`.

## Conventions

* `pmoebius` reads `∞` as `0`, so it is the Möbius transformation only where the image is
  finite: on the upper half plane (`coe_pmoebius_of_mem`), or for a representative whose
  denominator does not vanish (`pmoebius_mk`). Every construction below only applies it there:
  the parameters of `thetaFactor`, `theta` and `ThetaMultipliable`, and the points `a`, `z₀` of
  `period`, are points of the upper half plane, and `IsAutomorphicWithMultiplier` reads the action
  on `OnePoint K`, so that no `K₀`-rational point sent to `∞` is replaced by `0`.
* Divisions follow Lean's convention `x / 0 = 0`. In particular a theta factor is `0` whenever its
  denominator vanishes, that is, when `z = γ b` or `z₀ = γ a`.
* The theta function is normalized at `z₀` (every factor is `1` at `z = z₀`) only when `z₀` avoids
  the orbits of both parameters, `γ a ≠ z₀` and `γ b ≠ z₀` for every `γ`, as the source's theorems
  assume. The definitions do not require this. If `z₀ = γ a` or `z₀ = γ b` for some `γ`, that factor
  is `0`, the product converges to `0`, and `theta` and `period` return this totalized value, which
  is neither a normalized theta function nor an analytic period.
* `theta` is the unconditional infinite product `∏'`. It is the limit of the products only when
  they converge (`ThetaMultipliable`); otherwise `∏'` returns `1`. The coefficient field is a
  Hausdorff topological ring, so that the limit is unique (`theta_eq_of_hasProd`).
-/

@[expose] public section

open scoped MatrixGroups Topology

namespace DrinfeldUpperHalfPlane

section Moebius

variable (K₀ : Type*) [Field K₀] (K : Type*) [Field K] [Algebra K₀ K]

/-- The action of `GL(2, K₀)` on the projective line `OnePoint K`: a matrix acts through its image
under `algebraMap K₀ K`, by Mathlib's Möbius action of `GL(2, K)`. It is scoped and has low
priority, so that it does not compete with Mathlib's action when `K₀ = K`. -/
noncomputable scoped instance (priority := low) glAction [DecidableEq K] :
    MulAction (GL (Fin 2) K₀) (OnePoint K) :=
  MulAction.compHom (OnePoint K) (Matrix.GeneralLinearGroup.map (algebraMap K₀ K))

/-- A matrix over `K₀` acts on `OnePoint K` as its image under `algebraMap K₀ K` does. -/
theorem gl_smul_def [DecidableEq K] (g : GL (Fin 2) K₀) (x : OnePoint K) :
    g • x = (Matrix.GeneralLinearGroup.map (algebraMap K₀ K) g) • x := rfl

/-- Scalar matrices act trivially on `OnePoint K`, so the action of `GL(2, K₀)` descends to
`PGL(2, K₀)`. -/
theorem scalar_smul_eq [DecidableEq K] (u : K₀ˣ) (x : OnePoint K) :
    (Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) K₀) • x = x := by
  have h10 : (Matrix.GeneralLinearGroup.map (algebraMap K₀ K)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) K₀)) 1 0 = 0 := by
    rw [Matrix.GeneralLinearGroup.map_apply]
    simp [Matrix.GeneralLinearGroup.scalar]
  have h00 : (Matrix.GeneralLinearGroup.map (algebraMap K₀ K)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) K₀)) 0 0 =
        algebraMap K₀ K (u : K₀) := by
    rw [Matrix.GeneralLinearGroup.map_apply]
    simp [Matrix.GeneralLinearGroup.scalar]
  have h11 : (Matrix.GeneralLinearGroup.map (algebraMap K₀ K)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) K₀)) 1 1 =
        algebraMap K₀ K (u : K₀) := by
    rw [Matrix.GeneralLinearGroup.map_apply]
    simp [Matrix.GeneralLinearGroup.scalar]
  have h01 : (Matrix.GeneralLinearGroup.map (algebraMap K₀ K)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) K₀)) 0 1 = 0 := by
    rw [Matrix.GeneralLinearGroup.map_apply]
    simp [Matrix.GeneralLinearGroup.scalar]
  have hu : algebraMap K₀ K (u : K₀) ≠ 0 := by
    simp
  induction x using OnePoint.rec with
  | infty => rw [gl_smul_def, OnePoint.smul_infty_eq_ite, ite_eq_left h10]
  | coe k =>
    rw [gl_smul_def, OnePoint.smul_some_eq_ite, h10, h11, h00, h01, zero_mul, zero_add,
      ite_eq_right hu, add_zero, mul_div_cancel_left₀ _ hu]

/-- The action of `PGL(2, K₀)` on `OnePoint K` induced by `glAction` (scalar matrices act
trivially by `scalar_smul_eq`). It is scoped and has low priority, like `glAction`. -/
noncomputable scoped instance (priority := low) pglAction [DecidableEq K] :
    MulAction PGL(2, K₀) (OnePoint K) :=
  Matrix.ProjGenLinGroup.mulActionOfGL (fun u x => scalar_smul_eq K₀ K u x)

/-- The class of `g` in `PGL(2, K₀)` acts on `OnePoint K` as `g` does. -/
theorem mk_smul_eq [DecidableEq K] (g : GL (Fin 2) K₀) (x : OnePoint K) :
    Matrix.ProjGenLinGroup.mk g • x = g • x :=
  Matrix.ProjGenLinGroup.mk_smul _ g x

/-- The affine Möbius formula `(a z + b) / (c z + d)` of `g = !![a, b; c, d]` at `z : K`, with the
entries of `g` mapped to `K`. At a pole (`c z + d = 0`) it takes Lean's value `x / 0 = 0`;
`pmoebius_mk` identifies it with the projective action away from the pole. -/
def moebius (g : GL (Fin 2) K₀) (z : K) : K :=
  (algebraMap K₀ K (g 0 0) * z + algebraMap K₀ K (g 0 1)) /
    (algebraMap K₀ K (g 1 0) * z + algebraMap K₀ K (g 1 1))

variable {K} in
/-- The affine coordinate of a point of the projective line: a finite point `z` is read as `z`,
and `∞` is read as `0`. It is only meaningful on finite points (`toAffine_coe`). -/
def toAffine (x : OnePoint K) : K := OnePoint.elim x 0 id

/-- `toAffine` reads a finite point as itself. -/
@[simp] theorem toAffine_coe (z : K) : toAffine (z : OnePoint K) = z := rfl

/-- `toAffine` reads `∞` as `0`. -/
@[simp] theorem toAffine_infty : toAffine (OnePoint.infty : OnePoint K) = 0 := rfl

variable {K} in
/-- The affine reading `toAffine (g • z)` of the projective action of `g ∈ PGL(2, K₀)` on `z : K`.
When `g` sends `z` to `∞` (which happens only for `K₀`-rational `z`) the result is `0`, not a
point of the projective line, so `pmoebius` is the Möbius transformation only where the image is
finite: on the upper half plane (`coe_pmoebius_of_mem`), or for a representative of `g` whose
denominator does not vanish at `z` (`pmoebius_mk`). -/
noncomputable def pmoebius [DecidableEq K] (g : PGL(2, K₀)) (z : K) : K :=
  toAffine (g • (z : OnePoint K))

variable {K} in
/-- Away from the pole of a representative `g`, `pmoebius` is the Möbius formula of `g`. -/
theorem pmoebius_mk [DecidableEq K] (g : GL (Fin 2) K₀) (z : K)
    (hz : algebraMap K₀ K (g 1 0) * z + algebraMap K₀ K (g 1 1) ≠ 0) :
    pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) z = moebius K₀ K g z := by
  rw [pmoebius, mk_smul_eq, gl_smul_def, OnePoint.smul_some_eq_ite]
  simp only [Matrix.GeneralLinearGroup.map_apply] at *
  rw [ite_eq_right (by simpa using hz)]
  rfl

end Moebius

/-- The Drinfeld upper half plane of the extension `K / K₀`: the points of `K` outside the image
of `K₀`, that is, the points of `ℙ¹(K) \ ℙ¹(K₀)` (all finite, as `∞` is `K₀`-rational). -/
def upperHalfPlane (K₀ : Type*) [Field K₀] (K : Type*) [Field K] [Algebra K₀ K] : Set K :=
  (Set.range (algebraMap K₀ K))ᶜ

/-- A point of `K` lies in the upper half plane if and only if it is not the image of an element
of `K₀`. -/
theorem mem_upperHalfPlane_iff (K₀ : Type*) [Field K₀] {K : Type*} [Field K] [Algebra K₀ K]
    (z : K) :
    z ∈ upperHalfPlane K₀ K ↔ ∀ x : K₀, algebraMap K₀ K x ≠ z := by
  simp [upperHalfPlane]

section OmegaAction

variable (K₀ : Type*) [Field K₀] {K : Type*} [Field K] [Algebra K₀ K]

/-- A point of the upper half plane is never a pole of a Möbius transformation with coefficients
in `K₀`: the denominator `c z + d` does not vanish. -/
theorem moebius_denom_ne_zero_of_mem {z : K} (hz : z ∈ upperHalfPlane K₀ K) (g : GL (Fin 2) K₀) :
    algebraMap K₀ K (g 1 0) * z + algebraMap K₀ K (g 1 1) ≠ 0 := by
  rw [mem_upperHalfPlane_iff] at hz
  intro h
  by_cases hc : g 1 0 = 0
  · have hd : g 1 1 ≠ 0 := by
      intro hd
      apply g.det_ne_zero
      rw [Matrix.det_fin_two]
      simp [hc, hd]
    rw [hc, map_zero, zero_mul, zero_add] at h
    exact hd ((algebraMap K₀ K).injective (by rw [h, map_zero]))
  · have hc' : algebraMap K₀ K (g 1 0) ≠ 0 := by
      intro h'; exact hc ((algebraMap K₀ K).injective (by rw [h', map_zero]))
    apply hz (-(g 1 1) / g 1 0)
    rw [map_div₀, map_neg, div_eq_iff hc', eq_comm, ← sub_eq_zero]
    rw [← h]; ring

variable [DecidableEq K]

/-- On the upper half plane `pmoebius` is the projective action: `g` sends `z` to the finite point
`pmoebius K₀ g z`. -/
theorem coe_pmoebius_of_mem {z : K} (hz : z ∈ upperHalfPlane K₀ K) (g : PGL(2, K₀)) :
    ((pmoebius K₀ g z : K) : OnePoint K) = g • (z : OnePoint K) := by
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | _ g =>
    rw [pmoebius, mk_smul_eq, gl_smul_def, OnePoint.smul_some_eq_ite]
    simp only [Matrix.GeneralLinearGroup.map_apply]
    rw [ite_eq_right (moebius_denom_ne_zero_of_mem K₀ hz g)]
    rfl

/-- `PGL(2, K₀)` preserves the upper half plane. -/
theorem pmoebius_mem_upperHalfPlane {z : K} (hz : z ∈ upperHalfPlane K₀ K) (g : PGL(2, K₀)) :
    pmoebius K₀ g z ∈ upperHalfPlane K₀ K := by
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | _ g =>
    have hden := moebius_denom_ne_zero_of_mem K₀ hz g
    rw [pmoebius_mk K₀ g z hden, mem_upperHalfPlane_iff]
    rw [mem_upperHalfPlane_iff] at hz
    intro t ht
    rw [moebius, eq_div_iff hden] at ht
    have key : algebraMap K₀ K (g 0 0 - t * g 1 0) * z = algebraMap K₀ K (t * g 1 1 - g 0 1) := by
      rw [map_sub, map_sub, map_mul, map_mul]
      linear_combination -ht
    by_cases h0 : g 0 0 - t * g 1 0 = 0
    · have h1 : t * g 1 1 - g 0 1 = 0 := by
        have := key
        rw [h0, map_zero, zero_mul] at this
        exact ((algebraMap K₀ K).injective (by rw [← this, map_zero])).symm
      apply g.det_ne_zero
      rw [Matrix.det_fin_two]
      have ha : g 0 0 = t * g 1 0 := sub_eq_zero.mp h0
      have hb : g 0 1 = t * g 1 1 := (sub_eq_zero.mp h1).symm
      change g 0 0 * g 1 1 - g 0 1 * g 1 0 = 0
      rw [ha, hb]; ring
    · apply hz ((t * g 1 1 - g 0 1) / (g 0 0 - t * g 1 0))
      have h0' : algebraMap K₀ K (g 0 0 - t * g 1 0) ≠ 0 := by
        intro h'; exact h0 ((algebraMap K₀ K).injective (by rw [h', map_zero]))
      rw [map_div₀, div_eq_iff h0', ← key, mul_comm]

/-- The identity of `PGL(2, K₀)` fixes every point of `K`. -/
@[simp] theorem pmoebius_one (z : K) : pmoebius K₀ (1 : PGL(2, K₀)) z = z := by
  rw [pmoebius, one_smul, toAffine_coe]

/-- On the upper half plane `pmoebius` is compatible with multiplication in `PGL(2, K₀)`. -/
theorem pmoebius_mul {z : K} (hz : z ∈ upperHalfPlane K₀ K) (g h : PGL(2, K₀)) :
    pmoebius K₀ (g * h) z = pmoebius K₀ g (pmoebius K₀ h z) := by
  rw [pmoebius, pmoebius, mul_smul, coe_pmoebius_of_mem K₀ hz h]

end OmegaAction

section Theta

variable {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] {G : Type*} [Group G]

/-- The cross-ratio `[z, z₀; x, y] = ((z - x) (z₀ - y)) / ((z - y) (z₀ - x))` of four points of
`K`. For distinct `x`, `y` and `z₀ ∉ {x, y}` it is the value at `z` of the Möbius function with a
zero at `x` and a pole at `y` that takes the value `1` at `z₀`. When `z = y` or `z₀ = x` the
denominator vanishes and the value is `0` (`x / 0 = 0`). -/
def crossRatio (z z₀ x y : K) : K := ((z - x) * (z₀ - y)) / ((z - y) * (z₀ - x))

/-- The factor `[z, z₀; γ a, γ b]` of the theta function attached to `ρ : G →* PGL(2, K₀)` at
`γ : G`. The parameters `a` and `b` are points of the upper half plane, so `pmoebius K₀ (ρ γ) a`
and `pmoebius K₀ (ρ γ) b` are their actual images, never `∞` (`coe_pmoebius_of_mem`); a
`K₀`-rational parameter could be sent to `∞`, which the affine formula cannot represent. When
`z = γ b` or `z₀ = γ a` the denominator vanishes and the factor is `0` (`crossRatio`); when
`z₀ = γ b` the numerator vanishes for every `z`. So the factor is `1` at `z = z₀` exactly when
`z₀ ≠ γ a` and `z₀ ≠ γ b`. -/
noncomputable def thetaFactor [DecidableEq K] (ρ : G →* PGL(2, K₀)) (a b : upperHalfPlane K₀ K)
    (z₀ z : K) (γ : G) : K :=
  crossRatio z z₀ (pmoebius K₀ (ρ γ) a) (pmoebius K₀ (ρ γ) b)

/-- The theta function `θ(a, b; z) = ∏_γ [z, z₀; γ a, γ b]` attached to `ρ`, as an unconditional
infinite product in `K`. It is normalized at `z₀` only when `z₀` avoids the orbits of `a` and `b`
(`γ a ≠ z₀` and `γ b ≠ z₀` for every `γ`), which the source's theorems assume and this definition
does not: if `z₀ = γ a` or `z₀ = γ b`, the `γ`-th factor is `0`, the product converges to `0`, and
`theta` is this totalized value, not a theta function. It is the limit of the finite products only
when they converge (`ThetaMultipliable`); otherwise `∏'` returns `1`. `K` is a Hausdorff
topological ring, so that this limit is unique (`theta_eq_of_hasProd`). The formula itself does
not use `[IsTopologicalRing K] [T2Space K]`; they only restrict the setting. -/
@[nolint unusedArguments]
noncomputable def theta [DecidableEq K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    (ρ : G →* PGL(2, K₀)) (a b : upperHalfPlane K₀ K) (z₀ : K) (z : K) : K :=
  ∏' γ : G, thetaFactor ρ a b z₀ z γ

/-- The theta product converges at `z`: the factors `thetaFactor ρ a b z₀ z γ` are
(unconditionally) multipliable in the Hausdorff topological ring `K`. A product with a factor `0`
converges (to `0`), so this does not exclude the degenerate normalization points `z₀ = γ a` and
`z₀ = γ b`; the source states that orbit avoidance separately. As for `theta`, the hypotheses
`[IsTopologicalRing K] [T2Space K]` only restrict the setting. -/
@[nolint unusedArguments]
def ThetaMultipliable [DecidableEq K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    (ρ : G →* PGL(2, K₀)) (a b : upperHalfPlane K₀ K) (z₀ z : K) : Prop :=
  Multipliable (thetaFactor ρ a b z₀ z)

/-- When the factors have product `x`, the theta function takes the value `x`: the limit of a
convergent product is unique because `K` is Hausdorff. -/
theorem theta_eq_of_hasProd [DecidableEq K] [TopologicalSpace K] [IsTopologicalRing K]
    [T2Space K] {ρ : G →* PGL(2, K₀)} {a b : upperHalfPlane K₀ K} {z₀ z x : K}
    (h : HasProd (thetaFactor ρ a b z₀ z) x) : theta ρ a b z₀ z = x :=
  h.tprod_eq

/-- `f : K → K` is automorphic on `Ω` for `ρ` with multiplier `c : G →* Kˣ`: for every `γ : G`
and `z ∈ Ω` whose image `ρ γ • z` in `OnePoint K` is a finite point `w`, `f w = c γ * f z`.
A point of `Ω` that `ρ γ` sends to `∞` imposes no condition (`f` has no value at `∞`), rather than
being read through `pmoebius` as `0`. On a subset of the upper half plane no point is sent to `∞`
and the condition is `f (pmoebius K₀ (ρ γ) z) = c γ * f z`
(`isAutomorphicWithMultiplier_iff_of_subset`). -/
def IsAutomorphicWithMultiplier [DecidableEq K] (ρ : G →* PGL(2, K₀)) (Ω : Set K) (f : K → K)
    (c : G →* Kˣ) : Prop :=
  ∀ γ : G, ∀ z ∈ Ω, ∀ w : K, ρ γ • (z : OnePoint K) = (w : OnePoint K) → f w = (c γ : K) * f z

/-- On a subset of the upper half plane, automorphy with multiplier `c` is the pointwise
condition `f (pmoebius K₀ (ρ γ) z) = c γ * f z`. -/
theorem isAutomorphicWithMultiplier_iff_of_subset [DecidableEq K] {ρ : G →* PGL(2, K₀)}
    {Ω : Set K} (hΩ : Ω ⊆ upperHalfPlane K₀ K) {f : K → K} {c : G →* Kˣ} :
    IsAutomorphicWithMultiplier ρ Ω f c ↔
      ∀ γ : G, ∀ z ∈ Ω, f (pmoebius K₀ (ρ γ) z) = (c γ : K) * f z := by
  refine ⟨fun h γ z hz => h γ z hz _ (coe_pmoebius_of_mem K₀ (hΩ hz) (ρ γ)).symm,
    fun h γ z hz w hw => ?_⟩
  have hw' : pmoebius K₀ (ρ γ) z = w :=
    OnePoint.coe_injective ((coe_pmoebius_of_mem K₀ (hΩ hz) (ρ γ)).trans hw)
  rw [← hw']
  exact h γ z hz

/-- `f` is invariant on `Ω` under `ρ`: automorphic with the trivial multiplier. -/
def IsInvariant [DecidableEq K] (ρ : G →* PGL(2, K₀)) (Ω : Set K) (f : K → K) : Prop :=
  IsAutomorphicWithMultiplier ρ Ω f 1

/-- The period `θ(a, α a; β z₀)` of `ρ` at `α, β : G`, for points `a` and `z₀` of the upper half
plane: the theta function with parameters `a` and `α a = pmoebius K₀ (ρ α) a`, normalized at `z₀`,
evaluated at `β z₀ = pmoebius K₀ (ρ β) z₀`. Both images are actual points of the upper half plane
(`pmoebius_mem_upperHalfPlane`). Like `theta`, it needs a Hausdorff topological ring `K`. It is the
analytic period only when `z₀` avoids the orbit of `a` (which is also the orbit of `α a`) and the
theta product converges at `β z₀`, as the source's theorem on periods assumes; the definition
requires neither. If `z₀ = γ a` for some `γ`, the `γ`-th factor is `0` and `period` is the
totalized value `0`: for the trivial group it is `1` when `a ≠ z₀` and `0` when `a = z₀`. -/
noncomputable def period [DecidableEq K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    (ρ : G →* PGL(2, K₀)) (a z₀ : upperHalfPlane K₀ K) (α β : G) : K :=
  theta ρ a ⟨pmoebius K₀ (ρ α) a, pmoebius_mem_upperHalfPlane K₀ a.2 (ρ α)⟩ z₀
    (pmoebius K₀ (ρ β) z₀)

end Theta

end DrinfeldUpperHalfPlane
