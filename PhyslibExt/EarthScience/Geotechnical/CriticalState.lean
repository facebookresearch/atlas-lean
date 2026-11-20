/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.EarthScience.Geotechnical.EffectiveStress
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Modified Cam-Clay yield-domain geometry

## i. Overview

Fixed modified Cam-Clay yield geometry at critical-state
stress ratio `M` and preconsolidation pressure `pc`. Here
`p` is the compression-positive effective mean stress (the
`meanStress` of the compression-positive effective tensor,
the negative of the tension-positive mean stress) and `q`
is the deviatoric invariant, `√(3 J₂)` for symmetric
(Cauchy) stress and equal to `|σa - σr|` in triaxial
stress; the physical branch is
`q ≥ 0`, while section A allows signed `q` with the same
`M` in extension. The elastic domain is the translated
ellipse `F(p, q) ≤ 0`, convex for every real `M` and `pc`
(the whole line `q = 0` at `M = 0`, for every `pc`; a
single point at `pc = 0` when `M ≠ 0`). The
preconsolidation pressure is fixed: no flow rule, hardening
evolution, or return map is included.

## ii. Key results

- `EarthScience.modifiedCamClayYield` and
  `modifiedCamClayElasticDomain`: the yield function and
  its elastic domain.
- `EarthScience.convex_modifiedCamClayElasticDomain` and
  `modifiedCamClayElasticDomain_bounds`: convexity and the
  stress bounds `0 ≤ p ≤ pc`, `|q| ≤ M pc / 2`.
- `EarthScience.modifiedCamClayYield_eq_zero_on_critical_line_iff`:
  on the physical branch the critical-state line `q = M p`
  meets the yield locus exactly at the origin and
  `(pc / 2, M pc / 2)`.
- `EarthScience.deviatoricInvariant`: `q` from the stress
  tensor, unchanged by pore pressure and by the stress
  sign convention.

## iii. Table of contents

- A. Yield domain geometry
- B. Compression-positive invariant bridge

## iv. References

- K. H. Roscoe and J. B. Burland, "On the generalised
  stress-strain behaviour of 'wet' clay", in *Engineering
  Plasticity*, Cambridge University Press, 1968: the
  modified Cam-Clay yield surface.
- D. M. Wood, *Soil Behaviour and Critical State Soil
  Mechanics*, Cambridge University Press, 1990: the
  invariants `p` and `q = √(3 J₂)`.
- `PhyslibExt.CondensedMatter.Elasticity.StressStrain` for
  `meanStress`, `deviatoricStress`, and
  `compressionPositiveStress`.
-/

@[expose] public section

open scoped Matrix
open Elasticity

namespace EarthScience

/-! ## A. Yield domain geometry -/

/-- Modified Cam-Clay yield function at fixed `M`, `pc`:
`q ^ 2 + M ^ 2 * p * (p - pc)`. -/
noncomputable def modifiedCamClayYield (M pc p q : ℝ) : ℝ :=
  q ^ 2 + M ^ 2 * p * (p - pc)

/-- Closed modified Cam-Clay elastic domain `F(p, q) ≤ 0`
in the `(p, q)` plane. -/
def modifiedCamClayElasticDomain (M pc : ℝ) : Set (ℝ × ℝ) :=
  {x | modifiedCamClayYield M pc x.1 x.2 ≤ 0}

/-- Translated-ellipse form: center `(pc / 2, 0)`; for
`M, pc > 0` the semi-axes are `pc / 2` and `M * pc / 2`
(in signed generality with `M ≠ 0` the geometric lengths
are `|pc| / 2` and `|M * pc| / 2`). At `M = 0` the
identity reduces to `q ^ 2 ≤ 0`: the domain is the line
`q = 0` with `p` unbounded, and there is no finite `p`
semi-axis. -/
lemma modifiedCamClayYield_eq_translated_ellipse (M pc p q : ℝ) :
    modifiedCamClayYield M pc p q
      = M ^ 2 * (p - pc / 2) ^ 2 + q ^ 2 - (M * pc / 2) ^ 2 := by
  unfold modifiedCamClayYield
  ring

/-- Membership in the modified Cam-Clay elastic domain in
translated-ellipse form. -/
lemma mem_modifiedCamClayElasticDomain_iff {M pc : ℝ} {x : ℝ × ℝ} :
    x ∈ modifiedCamClayElasticDomain M pc ↔
      M ^ 2 * (x.1 - pc / 2) ^ 2 + x.2 ^ 2 ≤ (M * pc / 2) ^ 2 := by
  have h := modifiedCamClayYield_eq_translated_ellipse M pc x.1 x.2
  unfold modifiedCamClayElasticDomain
  simp only [Set.mem_ofPred_eq]
  rw [h]
  constructor <;> intro hh <;> linarith

/-- Convexity of the modified Cam-Clay elastic domain
(holds for every real `M`, `pc`). -/
theorem convex_modifiedCamClayElasticDomain (M pc : ℝ) :
    Convex ℝ (modifiedCamClayElasticDomain M pc) := by
  intro x hx y hy a b ha hb hab
  have hx0 : modifiedCamClayYield M pc x.1 x.2 ≤ 0 := hx
  have hy0 : modifiedCamClayYield M pc y.1 y.2 ≤ 0 := hy
  have e1 : (a • x + b • y).1 = a * x.1 + b * y.1 := by
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
  have e2 : (a • x + b • y).2 = a * x.2 + b * y.2 := by
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  have h1 : a * modifiedCamClayYield M pc x.1 x.2 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ha hx0
  have h2 : b * modifiedCamClayYield M pc y.1 y.2 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hb hy0
  have hnn : (0 : ℝ) ≤ a * b * (M ^ 2 * (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2) :=
    mul_nonneg (mul_nonneg ha hb)
      (add_nonneg (mul_nonneg (sq_nonneg M) (sq_nonneg _)) (sq_nonneg _))
  have hfr : b = 1 - a := by linarith
  have key : modifiedCamClayYield M pc (a * x.1 + b * y.1) (a * x.2 + b * y.2)
      = a * modifiedCamClayYield M pc x.1 x.2
        + b * modifiedCamClayYield M pc y.1 y.2
        - a * b * (M ^ 2 * (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2) := by
    rw [hfr]
    unfold modifiedCamClayYield
    ring
  change modifiedCamClayYield M pc (a • x + b • y).1 (a • x + b • y).2 ≤ 0
  rw [e1, e2, key]
  linarith

/-- Stress bounds in the modified Cam-Clay elastic domain
for `M, pc > 0`. -/
theorem modifiedCamClayElasticDomain_bounds {M pc : ℝ} (hM : 0 < M)
    (hpc : 0 < pc) {x : ℝ × ℝ} (hx : x ∈ modifiedCamClayElasticDomain M pc) :
    0 ≤ x.1 ∧ x.1 ≤ pc ∧ |x.2| ≤ M * pc / 2 := by
  rw [mem_modifiedCamClayElasticDomain_iff] at hx
  have hM2pos : (0 : ℝ) < M ^ 2 := pow_pos hM 2
  have hq2 : x.2 ^ 2 ≤ (M * pc / 2) ^ 2 := by
    have hnn : (0 : ℝ) ≤ M ^ 2 * (x.1 - pc / 2) ^ 2 :=
      mul_nonneg (sq_nonneg M) (sq_nonneg _)
    linarith
  have habs : |x.2| ≤ M * pc / 2 :=
    abs_le_of_sq_le_sq hq2 (by positivity)
  have hpsq : (x.1 - pc / 2) ^ 2 ≤ (pc / 2) ^ 2 := by
    have h3 : (M * pc / 2) ^ 2 = M ^ 2 * (pc / 2) ^ 2 := by ring
    rw [h3] at hx
    have h1 : M ^ 2 * (x.1 - pc / 2) ^ 2 ≤ M ^ 2 * (pc / 2) ^ 2 := by
      have hnn2 : (0 : ℝ) ≤ x.2 ^ 2 := sq_nonneg _
      linarith
    exact le_of_mul_le_mul_left h1 hM2pos
  have habs1 : |x.1 - pc / 2| ≤ pc / 2 :=
    abs_le_of_sq_le_sq hpsq (by positivity)
  rw [abs_le] at habs1
  exact ⟨by linarith [habs1.1], by linarith [habs1.2], habs⟩

/-- Restriction of the yield function to the critical-state line `q = M * p`:
`F(p, M * p) = M ^ 2 * p * (2 * p - pc)`. -/
lemma modifiedCamClayYield_on_critical_line (M pc p : ℝ) :
    modifiedCamClayYield M pc p (M * p) = M ^ 2 * p * (2 * p - pc) := by
  unfold modifiedCamClayYield
  ring

/-- Critical-line intersection with the yield locus on the physical branch
(`M, pc > 0`, `q ≥ 0`): the points on `q = M * p` with `F = 0` are exactly the
origin and the critical point `(pc / 2, M * pc / 2)`. Yield-locus geometry at
fixed `pc`; no flow rule or hardening evolution. -/
theorem modifiedCamClayYield_eq_zero_on_critical_line_iff {M pc p q : ℝ}
    (hM : 0 < M) (hpc : 0 < pc) :
    (0 ≤ q ∧ q = M * p ∧ modifiedCamClayYield M pc p q = 0) ↔
      (p = 0 ∧ q = 0) ∨ (p = pc / 2 ∧ q = M * pc / 2) := by
  constructor
  · rintro ⟨hq, hline, hF⟩
    rw [hline, modifiedCamClayYield_on_critical_line] at hF
    have hM2 : M ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hM)
    rcases mul_eq_zero.mp hF with h | h2
    · rcases mul_eq_zero.mp h with hM2' | hp0
      · exact absurd hM2' hM2
      · left
        exact ⟨hp0, by rw [hline, hp0, mul_zero]⟩
    · right
      have hp2 : p = pc / 2 := by linarith
      exact ⟨hp2, by rw [hline, hp2]; ring⟩
  · rintro (⟨hp0, hq0⟩ | ⟨hp2, hq2⟩)
    · subst hp0
      subst hq0
      refine ⟨le_rfl, (mul_zero M).symm, ?_⟩
      unfold modifiedCamClayYield
      ring
    · subst hp2
      subst hq2
      refine ⟨?_, by ring, ?_⟩
      · exact div_nonneg (mul_nonneg (le_of_lt hM) (le_of_lt hpc)) (by linarith)
      · unfold modifiedCamClayYield
        ring

/-- Nonzero critical-line intersection: on the physical branch, a point on
`q = M * p` with `F = 0` and `p ≠ 0` is the critical point
`(pc / 2, M * pc / 2)`; the origin is the excluded second intersection. -/
theorem modifiedCamClayYield_eq_zero_on_critical_line_of_ne_zero {M pc p q : ℝ}
    (hM : 0 < M) (hpc : 0 < pc) (hq : 0 ≤ q) (hline : q = M * p)
    (hF : modifiedCamClayYield M pc p q = 0) (hp : p ≠ 0) :
    p = pc / 2 ∧ q = M * pc / 2 := by
  have h := (modifiedCamClayYield_eq_zero_on_critical_line_iff hM hpc).mp ⟨hq, hline, hF⟩
  rcases h with ⟨hp0, -⟩ | h
  · exact absurd hp0 hp
  · exact h

/-- Off-yield points on the critical-state line: with `M > 0`, a point
`(p, M * p)` with `p` different from both intersection abscissae is not on the
yield locus. -/
lemma modifiedCamClayYield_on_critical_line_ne_zero {M pc p : ℝ}
    (hM : 0 < M) (hp0 : p ≠ 0) (hpc2 : p ≠ pc / 2) :
    modifiedCamClayYield M pc p (M * p) ≠ 0 := by
  rw [modifiedCamClayYield_on_critical_line]
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact pow_ne_zero 2 (ne_of_gt hM)
    · exact hp0
  · intro hcon
    apply hpc2
    linarith

/-! ## B. Compression-positive invariant bridge -/

/-- Deviatoric invariant in Frobenius form,
`q = √(3/2 · tr (sᵀ s))` for the deviatoric part `s`.
For symmetric (Cauchy) stress this is `√(3 J₂)` (see
`deviatoricInvariant_eq_sqrt_neg_stressInvariant2_deviatoric`);
for a nonsymmetric matrix it is the Frobenius extension,
not `J₂`. -/
noncomputable def deviatoricInvariant (σ : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  Real.sqrt (3 / 2 * ((deviatoricStress σ)ᵀ * deviatoricStress σ).trace)

/-- For symmetric (Cauchy) stress, the Frobenius-form
invariant is `√(3 J₂)`, with
`J₂ = -stressInvariant2` of the deviatoric part. -/
lemma deviatoricInvariant_eq_sqrt_neg_stressInvariant2_deviatoric
    {σ : Matrix (Fin 3) (Fin 3) ℝ} (hσ : IsSymmetricStress σ) :
    deviatoricInvariant σ
      = Real.sqrt (3 * (-stressInvariant2 (deviatoricStress σ))) := by
  have hσ' : σᵀ = σ := hσ
  have hsymm : (deviatoricStress σ)ᵀ = deviatoricStress σ := by
    unfold deviatoricStress
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, hσ']
  have htr : (deviatoricStress σ).trace = 0 := by
    unfold deviatoricStress meanStress
    rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
    simp only [Fintype.card_fin, smul_eq_mul]
    ring
  unfold deviatoricInvariant stressInvariant2
  rw [hsymm, htr]
  congr 1
  ring

/-- Pore pressure lowers the compression-positive mean
stress by `u`. -/
lemma meanStress_effectiveStressCompressionPositive
    (σc : Matrix (Fin 3) (Fin 3) ℝ) (u : ℝ) :
    meanStress (effectiveStressCompressionPositive σc u)
      = meanStress σc - u := by
  unfold meanStress effectiveStressCompressionPositive
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
  simp [Fintype.card_fin, smul_eq_mul]
  ring

/-- Pore pressure does not change `q`. -/
lemma deviatoricInvariant_effectiveStressCompressionPositive
    (σc : Matrix (Fin 3) (Fin 3) ℝ) (u : ℝ) :
    deviatoricInvariant (effectiveStressCompressionPositive σc u)
      = deviatoricInvariant σc := by
  have hdev : deviatoricStress (effectiveStressCompressionPositive σc u) =
      deviatoricStress σc := by
    unfold deviatoricStress
    rw [meanStress_effectiveStressCompressionPositive, sub_smul]
    unfold effectiveStressCompressionPositive
    abel
  unfold deviatoricInvariant
  rw [hdev]

/-- `q` is the same in both sign conventions. -/
lemma deviatoricInvariant_compressionPositiveStress
    (σ : Matrix (Fin 3) (Fin 3) ℝ) :
    deviatoricInvariant (compressionPositiveStress σ)
      = deviatoricInvariant σ := by
  have hmean : meanStress (compressionPositiveStress σ) = -meanStress σ := by
    unfold meanStress compressionPositiveStress
    rw [Matrix.trace_neg]
    ring
  have hdev : deviatoricStress (compressionPositiveStress σ)
      = -deviatoricStress σ := by
    unfold deviatoricStress
    rw [hmean, neg_smul]
    unfold compressionPositiveStress
    abel
  unfold deviatoricInvariant
  rw [hdev, Matrix.transpose_neg, neg_mul, mul_neg, neg_neg]

end EarthScience
