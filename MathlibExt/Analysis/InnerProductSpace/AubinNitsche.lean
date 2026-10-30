/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Topology.MetricSpace.HausdorffDistance

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Aubin–Nitsche lemma

Let `H` be a real Hilbert space, `B : H →L[ℝ] H →L[ℝ] ℝ` a bounded
bilinear form, `Vh` a subspace of `H` (the discrete space), and
`e : H` an error satisfying Galerkin orthogonality, `B e wh = 0` for
all `wh ∈ Vh`. Let `L` be a second real Hilbert space (the weaker-norm
space, e.g. `L²`) and `J : H →L[ℝ] L` a bounded linear map (the
embedding of the strong space into the weak space). The *adjoint
problem* is to find `z : H` with `B v z = ⟪J e, J v⟫_ℝ` for all `v : H`.

The **Aubin–Nitsche lemma** is the duality argument that upgrades a
strong-norm error estimate to a weak-norm estimate:

* `aubinNitsche_pointwise`: for every competitor `zh ∈ Vh`,
  `‖J e‖² ≤ ‖B‖ * ‖e‖ * ‖z - zh‖`, since `‖J e‖² = ⟪J e, J e⟫ = B e z`
  and Galerkin orthogonality lets `z` be replaced by `z - zh`.
* `aubinNitsche_core`: the infimum form,
  `‖J e‖² ≤ ‖B‖ * ‖e‖ * Metric.infDist z Vh`.
* `adjointSolution_norm_le`: if `B` is coercive with constant `α` and
  `‖J‖ ≤ Cemb`, then `α * ‖z‖ ≤ Cemb * ‖J e‖` (adjoint stability).
* `aubinNitsche_rate`: if in addition the adjoint solution is
  approximable in `Vh`, `‖z - zh‖ ≤ Capp * h * ‖z‖` for some
  `zh ∈ Vh`, then `α * ‖J e‖ ≤ ‖B‖ * Cemb * Capp * h * ‖e‖` — the
  weak-norm error gains the extra factor `h` over the strong-norm
  error `‖e‖`.
* `exists_adjointSolution`: if `B` is coercive, the adjoint problem
  has a solution. The proof applies the Lax–Milgram theorem in Mathlib
  to the transposed form `B.flip`; the right-hand side is the element
  `J† (J e)` of `H`, whose inner product with `v` is `⟪J e, J v⟫_ℝ`.

No symmetry of `B` is assumed, and the core estimate needs no
coercivity or completeness. This is the duality counterpart of the
Céa and Strang estimates (conforming and nonconforming Galerkin
error in the strong norm), which are not repeated here. It is not
one of the 72 targets of `v1/Atlas/IntroductionToFunctionalAnalysis`,
and the Aubin–Nitsche lemma is not in the pinned Mathlib or in base
MathlibExt.

Reference: J.-P. Aubin, "Behavior of the error of the approximate
solutions of boundary value problems for linear elliptic operators by
Galerkin's and finite difference methods", Ann. Scuola Norm. Sup. Pisa
21 (1967); J. A. Nitsche, "Ein Kriterium für die
Quasi-Optimalität des Ritzschen Verfahrens", Numer. Math. 11 (1968);
see also Brenner–Scott, *The Mathematical Theory of Finite Element
Methods*, the Aubin–Nitsche duality argument (Chapter 5).
-/

@[expose] public section

open scoped _root_.InnerProductSpace

namespace MathlibExt.Analysis.InnerProductSpace.AubinNitsche

variable {H L : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup L] [InnerProductSpace ℝ L]

/-- For real `a`, `a ≤ ‖a‖`. -/
private theorem le_norm_self_real (a : ℝ) : a ≤ ‖a‖ := by
  rw [Real.norm_eq_abs]
  exact le_abs_self a

/-- The transpose of a coercive bilinear form is coercive with the
same constant, since `B.flip u u = B u u`. -/
theorem isCoercive_flip {B : H →L[ℝ] H →L[ℝ] ℝ} (hB : IsCoercive B) :
    IsCoercive B.flip := by
  obtain ⟨C, hC, hco⟩ := hB
  refine ⟨C, hC, fun u => ?_⟩
  rw [ContinuousLinearMap.flip_apply]
  exact hco u

/-- **Existence for the adjoint problem.** If `B` is coercive, then
for every `e : H` there is `z : H` with `B v z = ⟪J e, J v⟫_ℝ` for
all `v : H`. -/
theorem exists_adjointSolution [CompleteSpace H] [CompleteSpace L]
    {B : H →L[ℝ] H →L[ℝ] ℝ} {J : H →L[ℝ] L} (hB : IsCoercive B) (e : H) :
    ∃ z : H, ∀ v : H, B v z = ⟪J e, J v⟫_ℝ := by
  have hBflip : IsCoercive B.flip := isCoercive_flip hB
  have hmem : ContinuousLinearMap.adjoint J (J e) ∈
      (InnerProductSpace.continuousLinearMapOfBilin B.flip).range := by
    rw [hBflip.range_eq_top]
    exact Submodule.mem_top
  obtain ⟨z, hz⟩ := hmem
  have hz' : InnerProductSpace.continuousLinearMapOfBilin B.flip z
      = ContinuousLinearMap.adjoint J (J e) := hz
  refine ⟨z, fun v => ?_⟩
  have h1 := InnerProductSpace.continuousLinearMapOfBilin_apply B.flip z v
  rw [hz'] at h1
  rw [ContinuousLinearMap.flip_apply] at h1
  rw [← h1]
  exact ContinuousLinearMap.adjoint_inner_left J v (J e)

/-- **Aubin–Nitsche lemma, pointwise form.** If `e` satisfies Galerkin
orthogonality against `Vh` and `z` solves the adjoint problem, then
for every competitor `zh ∈ Vh`,
`‖J e‖² ≤ ‖B‖ * ‖e‖ * ‖z - zh‖`. -/
theorem aubinNitsche_pointwise {B : H →L[ℝ] H →L[ℝ] ℝ} {J : H →L[ℝ] L}
    {e z : H} {Vh : Submodule ℝ H} {zh : H} (hzh : zh ∈ Vh)
    (horth : ∀ wh ∈ Vh, B e wh = 0) (hadj : ∀ v : H, B v z = ⟪J e, J v⟫_ℝ) :
    ‖J e‖ ^ 2 ≤ ‖B‖ * ‖e‖ * ‖z - zh‖ := by
  have hident : B e z = B e (z - zh) := by
    have hsub := map_sub (B e) z zh
    have h0 := horth zh hzh
    linarith
  calc ‖J e‖ ^ 2 = ⟪J e, J e⟫_ℝ := (real_inner_self_eq_norm_sq _).symm
    _ = B e z := (hadj e).symm
    _ = B e (z - zh) := hident
    _ ≤ ‖B e (z - zh)‖ := le_norm_self_real _
    _ ≤ ‖B‖ * ‖e‖ * ‖z - zh‖ := B.le_opNorm₂ e (z - zh)

/-- **Aubin–Nitsche lemma, infimum form.** With the same hypotheses,
`‖J e‖² ≤ ‖B‖ * ‖e‖ * Metric.infDist z Vh`. -/
theorem aubinNitsche_core {B : H →L[ℝ] H →L[ℝ] ℝ} {J : H →L[ℝ] L}
    {e z : H} {Vh : Submodule ℝ H}
    (horth : ∀ wh ∈ Vh, B e wh = 0) (hadj : ∀ v : H, B v z = ⟪J e, J v⟫_ℝ) :
    ‖J e‖ ^ 2 ≤ ‖B‖ * ‖e‖ * Metric.infDist z (Vh : Set H) := by
  by_contra hcon
  rw [not_le] at hcon
  have hCnn : 0 ≤ ‖B‖ * ‖e‖ :=
    mul_nonneg B.opNorm_nonneg (norm_nonneg _)
  set δ := (‖J e‖ ^ 2 - ‖B‖ * ‖e‖ * Metric.infDist z (Vh : Set H))
    / (‖B‖ * ‖e‖ + 1) with hδ
  have hδpos : 0 < δ := by
    apply div_pos _ _
    · linarith
    · linarith
  obtain ⟨zh, hzh, hdist⟩ := (Metric.infDist_lt_iff
    (s := (Vh : Set H)) (x := z) ⟨0, Vh.zero_mem⟩).mp
    (show Metric.infDist z (Vh : Set H) < Metric.infDist z (Vh : Set H) + δ
      from lt_add_of_pos_right _ hδpos)
  have hp := aubinNitsche_pointwise hzh horth hadj
  rw [dist_eq_norm] at hdist
  have hCδ : (‖B‖ * ‖e‖) * δ
      < ‖J e‖ ^ 2 - ‖B‖ * ‖e‖ * Metric.infDist z (Vh : Set H) := by
    have hD : 0 < ‖J e‖ ^ 2 - ‖B‖ * ‖e‖ * Metric.infDist z (Vh : Set H) := by
      linarith
    have hK1 : (0 : ℝ) < ‖B‖ * ‖e‖ + 1 := by linarith
    rw [hδ, ← mul_div_assoc, div_lt_iff₀ hK1]
    have hEq : (‖J e‖ ^ 2 - ‖B‖ * ‖e‖ * Metric.infDist z (Vh : Set H))
        * (‖B‖ * ‖e‖ + 1)
        - (‖B‖ * ‖e‖) * (‖J e‖ ^ 2 - ‖B‖ * ‖e‖ * Metric.infDist z (Vh : Set H))
        = ‖J e‖ ^ 2 - ‖B‖ * ‖e‖ * Metric.infDist z (Vh : Set H) := by ring
    linarith
  have hdist_le : ‖z - zh‖ ≤ Metric.infDist z (Vh : Set H) + δ := le_of_lt hdist
  have h1 : (‖B‖ * ‖e‖) * ‖z - zh‖
      ≤ (‖B‖ * ‖e‖) * Metric.infDist z (Vh : Set H) + (‖B‖ * ‖e‖) * δ := by
    have h2 := mul_le_mul_of_nonneg_left hdist_le hCnn
    rwa [mul_add] at h2
  linarith

/-- **Adjoint stability.** If `B` is coercive with constant `α` and
`‖J‖ ≤ Cemb`, then the adjoint solution satisfies
`α * ‖z‖ ≤ Cemb * ‖J e‖`. -/
theorem adjointSolution_norm_le {B : H →L[ℝ] H →L[ℝ] ℝ} {J : H →L[ℝ] L}
    {α Cemb : ℝ} (hco : ∀ v : H, α * ‖v‖ * ‖v‖ ≤ B v v)
    (hJ : ‖J‖ ≤ Cemb) {e z : H} (hadj : ∀ v : H, B v z = ⟪J e, J v⟫_ℝ) :
    α * ‖z‖ ≤ Cemb * ‖J e‖ := by
  have hCemb : 0 ≤ Cemb := le_trans (norm_nonneg _) hJ
  by_cases hz : z = 0
  · rw [hz, norm_zero, mul_zero]
    exact mul_nonneg hCemb (norm_nonneg _)
  · have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have h1 : α * ‖z‖ * ‖z‖ ≤ B z z := hco z
    have h2 : B z z = ⟪J e, J z⟫_ℝ := hadj z
    have h3 : ⟪J e, J z⟫_ℝ ≤ ‖J e‖ * ‖J z‖ := real_inner_le_norm _ _
    have h4 : ‖J z‖ ≤ Cemb * ‖z‖ := by
      calc ‖J z‖ ≤ ‖J‖ * ‖z‖ := J.le_opNorm z
        _ ≤ Cemb * ‖z‖ := mul_le_mul_of_nonneg_right hJ (norm_nonneg _)
    have h5 : (α * ‖z‖) * ‖z‖ ≤ (Cemb * ‖J e‖) * ‖z‖ := by
      calc (α * ‖z‖) * ‖z‖ = α * ‖z‖ * ‖z‖ := by ring
        _ ≤ B z z := h1
        _ = ⟪J e, J z⟫_ℝ := h2
        _ ≤ ‖J e‖ * ‖J z‖ := h3
        _ ≤ ‖J e‖ * (Cemb * ‖z‖) :=
          mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
        _ = (Cemb * ‖J e‖) * ‖z‖ := by ring
    exact le_of_mul_le_mul_right h5 hzn

/-- **Aubin–Nitsche lemma, rate form.** If in addition the adjoint
solution is approximable in `Vh` with `‖z - zh‖ ≤ Capp * h * ‖z‖`
for some `zh ∈ Vh`, then the weak-norm error gains the factor `h`:
`α * ‖J e‖ ≤ ‖B‖ * Cemb * Capp * h * ‖e‖`. -/
theorem aubinNitsche_rate {B : H →L[ℝ] H →L[ℝ] ℝ} {J : H →L[ℝ] L}
    {Vh : Submodule ℝ H} {α Cemb Capp h : ℝ} (hα : 0 < α)
    (hco : ∀ v : H, α * ‖v‖ * ‖v‖ ≤ B v v) (hJ : ‖J‖ ≤ Cemb)
    (hCemb : 0 ≤ Cemb) (hCapp : 0 ≤ Capp) (hh : 0 ≤ h)
    {e z : H} (horth : ∀ wh ∈ Vh, B e wh = 0)
    (hadj : ∀ v : H, B v z = ⟪J e, J v⟫_ℝ)
    (happrox : ∃ zh ∈ Vh, ‖z - zh‖ ≤ Capp * h * ‖z‖) :
    α * ‖J e‖ ≤ ‖B‖ * Cemb * Capp * h * ‖e‖ := by
  obtain ⟨zh, hzh, happrox'⟩ := happrox
  have hstab := adjointSolution_norm_le hco hJ hadj
  by_cases hJe : J e = 0
  · rw [hJe, norm_zero, mul_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg B.opNorm_nonneg
      hCemb) hCapp) hh) (norm_nonneg _)
  · have hJen : 0 < ‖J e‖ := norm_pos_iff.mpr hJe
    have hcore : ‖J e‖ ^ 2 ≤ ‖B‖ * ‖e‖ * ‖z - zh‖ :=
      aubinNitsche_pointwise hzh horth hadj
    have hnonneg : 0 ≤ ‖B‖ * ‖e‖ * (Capp * h) :=
      mul_nonneg (mul_nonneg B.opNorm_nonneg (norm_nonneg _))
        (mul_nonneg hCapp hh)
    have h1 : α * ‖J e‖ ^ 2 ≤ (‖B‖ * Cemb * Capp * h * ‖e‖) * ‖J e‖ := by
      calc α * ‖J e‖ ^ 2
          ≤ α * (‖B‖ * ‖e‖ * ‖z - zh‖) :=
            mul_le_mul_of_nonneg_left hcore hα.le
        _ ≤ α * (‖B‖ * ‖e‖ * (Capp * h * ‖z‖)) := by
            apply mul_le_mul_of_nonneg_left _ hα.le
            exact mul_le_mul_of_nonneg_left happrox'
              (mul_nonneg B.opNorm_nonneg (norm_nonneg _))
        _ = (‖B‖ * ‖e‖ * (Capp * h)) * (α * ‖z‖) := by ring
        _ ≤ (‖B‖ * ‖e‖ * (Capp * h)) * (Cemb * ‖J e‖) :=
            mul_le_mul_of_nonneg_left hstab hnonneg
        _ = (‖B‖ * Cemb * Capp * h * ‖e‖) * ‖J e‖ := by ring
    have h2 : (α * ‖J e‖) * ‖J e‖ ≤ (‖B‖ * Cemb * Capp * h * ‖e‖) * ‖J e‖ := by
      calc (α * ‖J e‖) * ‖J e‖ = α * ‖J e‖ ^ 2 := by ring
        _ ≤ (‖B‖ * Cemb * Capp * h * ‖e‖) * ‖J e‖ := h1
    exact le_of_mul_le_mul_right h2 hJen

end MathlibExt.Analysis.InnerProductSpace.AubinNitsche
