/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Strang's first lemma for variational crimes

Let `E` be a real inner-product space, `B : E →L[ℝ] E →L[ℝ] ℝ` a bounded bilinear
form and `ℓ : E →L[ℝ] ℝ` a bounded linear functional. The *variational
problem* is to find `u : E` with `B u w = ℓ w` for all `w : E`.

In a numerical method one rarely solves this problem exactly: the bilinear
form and the functional are replaced by approximations `Bh` and `ℓh` on a
discrete space `V` (the *variational crimes*), and one solves the discrete
problem `Bh uh w = ℓh w` for all `w : V`, where `V` is embedded in `E` by a
linear isometry `J : V →ₗᵢ[ℝ] E`. **Strang's first lemma** bounds the error
`‖u - J uh‖` by the sum of the best-approximation error of `u` in `J V`
and the consistency errors measuring how far `Bh` and `ℓh` are from the
restrictions of `B` and `ℓ`:

* `strang_first_lemma`: the pointwise form, for an arbitrary competitor
  `vh : V`.
* `strang_first_lemma_iInf`: the infimum form, with the best-approximation
  error `⨅ vh : V, ‖u - J vh‖`.

No symmetry of `B` or `Bh` is assumed: the proof uses only coercivity of
`Bh` and boundedness of `B`. No completeness hypothesis is needed for the
estimates themselves (existence of the solutions `u` and `uh` follows from
the Lax-Milgram theorem in Mathlib when the spaces are complete and the
forms are coercive, but is taken as a hypothesis here). Setting the
consistency errors to zero recovers the Céa-type estimate for the
unperturbed Galerkin method.

It is not one of the 72 targets of
`v1/Atlas/IntroductionToFunctionalAnalysis`, and Strang's lemma is not in
the pinned Mathlib or in base MathlibExt.

Reference: G. Strang, "Variational crimes in the finite element method"
(1972); see also Brenner-Scott, *The Mathematical Theory of Finite Element
Methods*, Lemma 10.1.8.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.StrangLemma

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- For real `a`, `a ≤ ‖a‖`. -/
private theorem le_norm_self_real (a : ℝ) : a ≤ ‖a‖ := by
  rw [Real.norm_eq_abs]
  exact le_abs_self a

/-- **Strang's first lemma** (pointwise form): if `u` solves the exact
variational problem `B u w = ℓ w` and `uh` solves the perturbed problem
`Bh uh w = ℓh w` on the discrete space `V` (embedded by the linear isometry
`J`), and `Bh` is coercive with constant `α`, then for every competitor
`vh : V` the error `‖u - J uh‖` is bounded by the best-approximation
error of `u` at `vh` plus the consistency errors. Here
`Bh - B.bilinearComp J J` measures the bilinear-form crime and
`ℓh - ℓ.comp J` measures the functional crime. -/
theorem strang_first_lemma
    {B : E →L[ℝ] E →L[ℝ] ℝ} {Bh : V →L[ℝ] V →L[ℝ] ℝ}
    {ℓ : E →L[ℝ] ℝ} {ℓh : V →L[ℝ] ℝ} {J : V →ₗᵢ[ℝ] E}
    {α : ℝ} (hα : 0 < α) (hco : ∀ v, α * ‖v‖ * ‖v‖ ≤ Bh v v)
    {u : E} {uh : V} (hu : ∀ w, B u w = ℓ w) (huh : ∀ w, Bh uh w = ℓh w)
    (vh : V) :
    ‖u - J uh‖ ≤ (1 + (‖B‖ + ‖Bh - B.bilinearComp J.toContinuousLinearMap
        J.toContinuousLinearMap‖) / α) * ‖u - J vh‖
      + (‖ℓh - ℓ.comp J.toContinuousLinearMap‖
        + ‖Bh - B.bilinearComp J.toContinuousLinearMap
          J.toContinuousLinearMap‖ * ‖u‖) / α := by
  set D := Bh - B.bilinearComp J.toContinuousLinearMap J.toContinuousLinearMap with hD
  set F := ℓh - ℓ.comp J.toContinuousLinearMap with hF
  have hBhsub : Bh (uh - vh) = Bh uh - Bh vh := map_sub Bh uh vh
  have hBhww : Bh (uh - vh) (uh - vh) = ℓh (uh - vh) - Bh vh (uh - vh) := by
    rw [hBhsub, sub_apply, huh]
  have hFsub : ∀ w, F w = ℓh w - ℓ (J w) := by
    intro w
    rw [hF]
    simp [ContinuousLinearMap.comp_apply]
  have hDsub : ∀ x y, D x y = Bh x y - B (J x) (J y) := by
    intro x y
    rw [hD]
    simp [ContinuousLinearMap.bilinearComp_apply]
  have hBsub : B (u - J vh) (J (uh - vh))
      = B u (J (uh - vh)) - B (J vh) (J (uh - vh)) := by
    have h := map_sub B u (J vh)
    rw [h, sub_apply]
  have hident : Bh (uh - vh) (uh - vh)
      = F (uh - vh) + B (u - J vh) (J (uh - vh)) - D vh (uh - vh) := by
    rw [hBhww, hFsub, hBsub, hDsub, hu]
    ring
  have hbF : ‖F (uh - vh)‖ ≤ ‖F‖ * ‖uh - vh‖ := F.le_opNorm _
  have hbB : ‖B (u - J vh) (J (uh - vh))‖ ≤ ‖B‖ * ‖u - J vh‖ * ‖uh - vh‖ := by
    have h := B.le_opNorm₂ (u - J vh) (J (uh - vh))
    rwa [J.norm_map] at h
  have hbD : ‖D vh (uh - vh)‖ ≤ ‖D‖ * ‖vh‖ * ‖uh - vh‖ := D.le_opNorm₂ vh _
  have hbound : Bh (uh - vh) (uh - vh)
      ≤ (‖F‖ + ‖B‖ * ‖u - J vh‖ + ‖D‖ * ‖vh‖) * ‖uh - vh‖ := by
    calc Bh (uh - vh) (uh - vh) ≤ ‖Bh (uh - vh) (uh - vh)‖ := le_norm_self_real _
      _ = ‖F (uh - vh) + B (u - J vh) (J (uh - vh)) - D vh (uh - vh)‖ := by
          rw [hident]
      _ ≤ ‖F (uh - vh)‖ + ‖B (u - J vh) (J (uh - vh))‖ + ‖D vh (uh - vh)‖ := by
          have h1 := norm_sub_le (F (uh - vh) + B (u - J vh) (J (uh - vh)))
            (D vh (uh - vh))
          have h2 := norm_add_le (F (uh - vh)) (B (u - J vh) (J (uh - vh)))
          linarith
      _ ≤ ‖F‖ * ‖uh - vh‖ + (‖B‖ * ‖u - J vh‖ * ‖uh - vh‖)
            + ‖D‖ * ‖vh‖ * ‖uh - vh‖ := add_le_add (add_le_add hbF hbB) hbD
      _ = (‖F‖ + ‖B‖ * ‖u - J vh‖ + ‖D‖ * ‖vh‖) * ‖uh - vh‖ := by ring
  have hCnn : 0 ≤ ‖F‖ + ‖B‖ * ‖u - J vh‖ + ‖D‖ * ‖vh‖ := by positivity
  have hαw : α * ‖uh - vh‖ ≤ ‖F‖ + ‖B‖ * ‖u - J vh‖ + ‖D‖ * ‖vh‖ := by
    by_cases hw0 : ‖uh - vh‖ = 0
    · rw [hw0]
      simp only [mul_zero]
      exact hCnn
    · have hwpos : 0 < ‖uh - vh‖ := lt_of_le_of_ne' (norm_nonneg _) hw0
      have hle : (α * ‖uh - vh‖) * ‖uh - vh‖
          ≤ (‖F‖ + ‖B‖ * ‖u - J vh‖ + ‖D‖ * ‖vh‖) * ‖uh - vh‖ := by
        calc (α * ‖uh - vh‖) * ‖uh - vh‖ = α * ‖uh - vh‖ * ‖uh - vh‖ := by ring
          _ ≤ Bh (uh - vh) (uh - vh) := hco _
          _ ≤ (‖F‖ + ‖B‖ * ‖u - J vh‖ + ‖D‖ * ‖vh‖) * ‖uh - vh‖ := hbound
      exact le_of_mul_le_mul_right hle hwpos
  have hvh : ‖vh‖ ≤ ‖u‖ + ‖u - J vh‖ := by
    have h1 : ‖J vh‖ ≤ ‖J vh - u‖ + ‖u‖ := by
      have h := norm_add_le (J vh - u) u
      rwa [sub_add_cancel] at h
    rw [J.norm_map vh, norm_sub_rev] at h1
    linarith
  have hmain : α * ‖uh - vh‖
      ≤ ‖F‖ + ‖B‖ * ‖u - J vh‖ + ‖D‖ * (‖u‖ + ‖u - J vh‖) := by
    have hδ : ‖D‖ * ‖vh‖ ≤ ‖D‖ * (‖u‖ + ‖u - J vh‖) :=
      mul_le_mul_of_nonneg_left hvh D.opNorm_nonneg
    linarith [hαw, hδ]
  have hα0 : α ≠ 0 := ne_of_gt hα
  calc ‖u - J uh‖ ≤ ‖u - J vh‖ + ‖uh - vh‖ := by
        have hsplit : u - J uh = (u - J vh) - J (uh - vh) := by
          rw [map_sub J]
          abel
        calc ‖u - J uh‖ = ‖(u - J vh) - J (uh - vh)‖ := by rw [hsplit]
          _ ≤ ‖u - J vh‖ + ‖J (uh - vh)‖ := norm_sub_le _ _
          _ = ‖u - J vh‖ + ‖uh - vh‖ := by rw [J.norm_map]
    _ ≤ ‖u - J vh‖ + (‖F‖ + ‖B‖ * ‖u - J vh‖ + ‖D‖ * (‖u‖ + ‖u - J vh‖)) / α := by
        have hwnorm : ‖uh - vh‖
            ≤ (‖F‖ + ‖B‖ * ‖u - J vh‖ + ‖D‖ * (‖u‖ + ‖u - J vh‖)) / α := by
          rw [le_div_iff₀ hα, mul_comm ‖uh - vh‖ α]
          exact hmain
        linarith [hwnorm]
    _ = (1 + (‖B‖ + ‖D‖) / α) * ‖u - J vh‖ + (‖F‖ + ‖D‖ * ‖u‖) / α := by
        field_simp
        ring

/-- **Strang's first lemma** (infimum form): the error is bounded by the
best-approximation error `⨅ vh : V, ‖u - J vh‖` plus the consistency
errors. -/
theorem strang_first_lemma_iInf
    {B : E →L[ℝ] E →L[ℝ] ℝ} {Bh : V →L[ℝ] V →L[ℝ] ℝ}
    {ℓ : E →L[ℝ] ℝ} {ℓh : V →L[ℝ] ℝ} {J : V →ₗᵢ[ℝ] E}
    {α : ℝ} (hα : 0 < α) (hco : ∀ v, α * ‖v‖ * ‖v‖ ≤ Bh v v)
    {u : E} {uh : V} (hu : ∀ w, B u w = ℓ w) (huh : ∀ w, Bh uh w = ℓh w) :
    ‖u - J uh‖ ≤ (1 + (‖B‖ + ‖Bh - B.bilinearComp J.toContinuousLinearMap
        J.toContinuousLinearMap‖) / α) * (⨅ vh : V, ‖u - J vh‖)
      + (‖ℓh - ℓ.comp J.toContinuousLinearMap‖
        + ‖Bh - B.bilinearComp J.toContinuousLinearMap
          J.toContinuousLinearMap‖ * ‖u‖) / α := by
  have hA : 0 ≤ 1 + (‖B‖ + ‖Bh - B.bilinearComp J.toContinuousLinearMap
      J.toContinuousLinearMap‖) / α := by
    have h1 : 0 ≤ (‖B‖ + ‖Bh - B.bilinearComp J.toContinuousLinearMap
        J.toContinuousLinearMap‖) / α :=
      div_nonneg (by positivity) hα.le
    linarith
  have hsub : ‖u - J uh‖
      - (‖ℓh - ℓ.comp J.toContinuousLinearMap‖
        + ‖Bh - B.bilinearComp J.toContinuousLinearMap
          J.toContinuousLinearMap‖ * ‖u‖) / α
      ≤ (1 + (‖B‖ + ‖Bh - B.bilinearComp J.toContinuousLinearMap
        J.toContinuousLinearMap‖) / α) * ⨅ vh : V, ‖u - J vh‖ := by
    rw [Real.mul_iInf_of_nonneg hA]
    refine le_ciInf fun vh => ?_
    have h := strang_first_lemma (J := J) hα hco hu huh vh
    linarith
  exact sub_le_iff_le_add.mp hsub

end MathlibExt.Analysis.InnerProductSpace.StrangLemma
