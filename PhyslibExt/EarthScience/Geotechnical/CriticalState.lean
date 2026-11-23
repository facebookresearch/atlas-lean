/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.EarthScience.Geotechnical.EffectiveStress
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
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
preconsolidation pressure is fixed. The file also carries
the specified pointwise associated-flow volumetric increment
and its critical-line diagnostic; still no hardening
evolution, return map, flow trajectory, or critical-state
prediction is included.

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
- `EarthScience.modifiedCamClayYieldPartialP`,
  `modifiedCamClayPlasticVolumetricIncrement`, and
  `modifiedCamClayPlasticVolumetricIncrement_eq_zero_iff_on_yield_locus`:
  for `M, pc > 0` on the yield locus with `p > 0`, `q ≥ 0`
  and a positive plastic multiplier, the specified
  associated-flow increment vanishes exactly at `p = pc / 2`,
  equivalently on `q = M p`.
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
condition `F ≤ 0` reduces to `q ^ 2 ≤ 0`: the domain is the line
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

/-- Partial derivative of the yield function with respect to the
compression-positive pressure `p` at fixed `M`, `pc` and `q`, as the
explicit algebraic expression `M ^ 2 * (2 * p - pc)`. It does not
depend on `q`. -/
noncomputable def modifiedCamClayYieldPartialP (M pc p : ℝ) : ℝ :=
  M ^ 2 * (2 * p - pc)

/-- Specified plastic volumetric increment for associated flow at
fixed `M`, `pc`: the plastic multiplier `lam` times the partial
derivative of the yield function with respect to `p`, in the
compression-positive strain convention (a positive increment is
compactive, a negative increment is dilative). A definition at a
fixed stress point, not an evolution law. -/
noncomputable def modifiedCamClayPlasticVolumetricIncrement
    (M pc p lam : ℝ) : ℝ :=
  lam * modifiedCamClayYieldPartialP M pc p

/-- The algebraic partial derivative is the derivative of the yield
function in `p` at fixed `M`, `pc` and `q`. -/
lemma hasDerivAt_modifiedCamClayYield_p (M pc q p : ℝ) :
    HasDerivAt (fun x => modifiedCamClayYield M pc x q)
      (modifiedCamClayYieldPartialP M pc p) p := by
  unfold modifiedCamClayYieldPartialP
  rw [hasDerivAt_iff_tendsto]
  have hres : ∀ x' : ℝ, modifiedCamClayYield M pc x' q
      - modifiedCamClayYield M pc p q - (x' - p) * (M ^ 2 * (2 * p - pc))
      = M ^ 2 * (x' - p) ^ 2 := by
    intro x'
    unfold modifiedCamClayYield
    ring
  have hfun : (fun x' : ℝ => ‖x' - p‖⁻¹ * ‖modifiedCamClayYield M pc x' q
      - modifiedCamClayYield M pc p q - (x' - p) • (M ^ 2 * (2 * p - pc))‖)
      = fun x' : ℝ => ‖M ^ 2 * (x' - p)‖ := by
    funext x'
    by_cases hx : x' = p
    · subst hx
      simp
    · have hne : x' - p ≠ 0 := sub_ne_zero.mpr hx
      have hnx : ‖x' - p‖ ≠ 0 := norm_ne_zero_iff.mpr hne
      simp only [smul_eq_mul, hres x', norm_mul, norm_pow]
      field_simp
  rw [hfun]
  have hcont : ContinuousAt (fun x' : ℝ => M ^ 2 * (x' - p)) p :=
    continuousAt_const.mul (continuousAt_id.sub continuousAt_const)
  have htend := hcont.norm.tendsto
  have h0 : M ^ 2 * (p - p) = 0 := by ring
  rw [h0, norm_zero] at htend
  exact htend

/-- The algebraic partial derivative as a `deriv` value in `p` at
fixed `M`, `pc` and `q`. -/
lemma deriv_modifiedCamClayYield_p (M pc q p : ℝ) :
    deriv (fun x => modifiedCamClayYield M pc x q) p
      = modifiedCamClayYieldPartialP M pc p :=
  (hasDerivAt_modifiedCamClayYield_p M pc q p).deriv

/-- Vanishing of the specified increment for a positive multiplier:
with `M > 0` and `lam > 0`, the increment is zero exactly at
`p = pc / 2`. No yield-locus hypothesis is needed for this
equivalence; with `lam = 0` the increment is zero at every `p`. -/
lemma modifiedCamClayPlasticVolumetricIncrement_eq_zero_iff
    {M pc p lam : ℝ} (hM : 0 < M) (hlam : 0 < lam) :
    modifiedCamClayPlasticVolumetricIncrement M pc p lam = 0
      ↔ p = pc / 2 := by
  unfold modifiedCamClayPlasticVolumetricIncrement modifiedCamClayYieldPartialP
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have hM2 : M ^ 2 ≠ 0 := by positivity
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 hlam'
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 hM2
      · linarith
  · intro h
    rw [h]
    have hz : 2 * (pc / 2) - pc = 0 := by ring
    rw [hz, mul_zero, mul_zero]

/-- Associated-flow diagnostic on the yield locus: with `M, pc > 0`,
`F = 0`, `p > 0`, `q ≥ 0` and a positive plastic multiplier, the
specified plastic volumetric increment vanishes exactly at
`p = pc / 2`, which on the locus holds exactly on the critical-state
line `q = M * p`. A pointwise diagnostic at fixed `pc`; it asserts
no hardening evolution and no prediction that flow reaches or stays
at a critical state. -/
theorem
    modifiedCamClayPlasticVolumetricIncrement_eq_zero_iff_on_yield_locus
    {M pc p q lam : ℝ} (hM : 0 < M) (hpc : 0 < pc) (hp : 0 < p)
    (hq : 0 ≤ q) (hF : modifiedCamClayYield M pc p q = 0)
    (hlam : 0 < lam) :
    (modifiedCamClayPlasticVolumetricIncrement M pc p lam = 0
      ↔ p = pc / 2) ∧ (p = pc / 2 ↔ q = M * p) := by
  constructor
  · exact modifiedCamClayPlasticVolumetricIncrement_eq_zero_iff hM hlam
  · constructor
    · intro hp2
      have hMp : 0 < M * p := mul_pos hM hp
      have hsq : q ^ 2 = (M * p) ^ 2 := by
        rw [hp2] at hF ⊢
        unfold modifiedCamClayYield at hF
        linear_combination hF
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
      · exact h
      · exfalso
        linarith
    · intro hline
      exact (modifiedCamClayYield_eq_zero_on_critical_line_of_ne_zero hM hpc
        hq hline hF (ne_of_gt hp)).1

/-- Dry-side sign: with `M > 0` and a positive multiplier, the
specified increment is negative (dilative) on the side
`p < pc / 2` of the critical pressure. -/
lemma modifiedCamClayPlasticVolumetricIncrement_neg_of_lt
    {M pc p lam : ℝ} (hM : 0 < M) (hlam : 0 < lam) (hlt : p < pc / 2) :
    modifiedCamClayPlasticVolumetricIncrement M pc p lam < 0 := by
  unfold modifiedCamClayPlasticVolumetricIncrement modifiedCamClayYieldPartialP
  have h1 : 0 < lam * M ^ 2 := by positivity
  have h2 : 2 * p - pc < 0 := by linarith
  have h := mul_neg_of_pos_of_neg h1 h2
  rwa [mul_assoc] at h

/-- Wet-side sign: with `M > 0` and a positive multiplier, the
specified increment is positive (compactive) on the side
`pc / 2 < p` of the critical pressure. -/
lemma modifiedCamClayPlasticVolumetricIncrement_pos_of_gt
    {M pc p lam : ℝ} (hM : 0 < M) (hlam : 0 < lam) (hgt : pc / 2 < p) :
    0 < modifiedCamClayPlasticVolumetricIncrement M pc p lam := by
  unfold modifiedCamClayPlasticVolumetricIncrement modifiedCamClayYieldPartialP
  have h1 : 0 < lam * M ^ 2 := by positivity
  have h2 : 0 < 2 * p - pc := by linarith
  have h := mul_pos h1 h2
  rwa [mul_assoc] at h

/-! ## B. Compression-positive invariant bridge -/

/-- Deviatoric invariant in Frobenius form,
`q = √(3/2 · tr (sᵀ s))` for the deviatoric part `s`.
For symmetric (Cauchy) stress this is `√(3 J₂)` (see
`deviatoricInvariant_eq_sqrt_neg_stressInvariant2_deviatoric`);
for a nonsymmetric matrix it is the Frobenius extension,
not `√(3 J₂)`. -/
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
