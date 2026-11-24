/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The dual distance formula

For a subspace `S` of a normed space `E` and a point `x : E`, the distance
from `x` to `S` is the supremum of `‖f x‖` over the continuous linear
functionals `f` of norm at most `1` that vanish on `S`, and the supremum is
attained: there is such an `f` with `f x = infDist x S`, and if the distance
is positive, `f` can be chosen with `‖f‖ = 1`. No closedness hypothesis on
`S` is needed: a functional vanishing on `S` vanishes on its closure, and
the quotient seminorm on `E ⧸ S` is the distance to `S` whether or not `S`
is closed.

The proof is the quotient form of Hahn–Banach: apply the norming functional
(`exists_dual_vector''`) to the class of `x` in `E ⧸ S`, whose seminorm is
`infDist x S`, and pull the resulting functional back along the quotient
map `S.mkQL`, which has norm at most `1`.

This is a derived supporting result for the Hahn–Banach material in
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HahnBanach.lean`.
The audited archive and its 72-target inventory provide related extension
and norming-functional statements. The distance formula is constructed
here from Mathlib's seminormed quotient and `exists_dual_vector''`.

## Main declarations

* `norm_mkQL_apply` : `‖S.mkQL x‖ = infDist x S`.
* `norm_mkQL_le` : `‖S.mkQL‖ ≤ 1`.
* `exists_annihilating_apply_eq_infDist` : there is `f` of norm at most `1`,
  vanishing on `S`, with `f x = infDist x S`.
* `exists_annihilating_norm_one` : if `0 < infDist x S`, the `f` above can
  be chosen with `‖f‖ = 1`.
* `exists_annihilating_of_notMem` : the norm-one form for a point outside a
  closed subspace.
* `infDist_eq_sSup_norm_apply` : `infDist x S` is the supremum of `‖f x‖`
  over functionals of norm at most `1` vanishing on `S`.
-/

@[expose] public section

namespace MathlibExt.Analysis.Normed.Module.DualDistanceFormula

open Metric

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Quotient seminorm equals distance to the subspace.** Let $E$ be a normed space over
$\mathbb{K}$, where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$, let $S$ be a linear subspace of
$E$, and give $E/S$ the quotient seminorm. Then for every $x \in E$ the class $q(x)$ of $x$ under
the quotient map $q \colon E \to E/S$ satisfies $\|q(x)\| = d(x, S)$, where
$d(x, S) = \inf_{s \in S} \|x - s\|$ is the distance from $x$ to $S$. -/
theorem norm_mkQL_apply (S : Submodule 𝕜 E) (x : E) :
    ‖S.mkQL x‖ = Metric.infDist x (S : Set E) :=
  QuotientAddGroup.norm_mk x

/-- **The quotient map has norm at most one.** Let $E$ be a normed space over $\mathbb{K}$,
where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$, let $S$ be a linear subspace of $E$, and give
$E/S$ the quotient seminorm. Then the quotient map $q \colon E \to E/S$, a continuous linear map,
has operator norm $\|q\| \le 1$. -/
theorem norm_mkQL_le (S : Submodule 𝕜 E) : ‖S.mkQL‖ ≤ 1 := by
  refine S.mkQL.opNorm_le_bound zero_le_one fun y => ?_
  rw [norm_mkQL_apply, one_mul]
  calc Metric.infDist y (S : Set E) ≤ dist y 0 :=
        Metric.infDist_le_dist_of_mem (zero_mem S)
    _ = ‖y‖ := by simp [dist_eq_norm]

/-- **Hahn–Banach distance formula, attainment form.** Let $E$ be a normed space over
$\mathbb{K}$, where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$, let $S$ be a linear subspace of
$E$, not necessarily closed, and let $x \in E$. Then there is a continuous linear functional
$f \colon E \to \mathbb{K}$ with $\|f\| \le 1$ that vanishes on $S$ and satisfies
$f(x) = d(x, S)$, where $d(x, S) = \inf_{s \in S} \|x - s\|$ is the distance from $x$ to $S$. -/
theorem exists_annihilating_apply_eq_infDist (S : Submodule 𝕜 E) (x : E) :
    ∃ f : E →L[𝕜] 𝕜, (∀ s ∈ S, f s = 0) ∧ ‖f‖ ≤ 1 ∧
      f x = (Metric.infDist x (S : Set E) : 𝕜) := by
  obtain ⟨g, hg_norm, hg_val⟩ := exists_dual_vector'' 𝕜 (S.mkQL x)
  refine ⟨g.comp S.mkQL, ?_, ?_, ?_⟩
  · intro s hs
    have h0 : S.mkQL s = 0 := by
      rw [Submodule.mkQL_apply]
      exact (Submodule.Quotient.mk_eq_zero S).mpr hs
    simp [h0]
  · calc ‖g.comp S.mkQL‖ ≤ ‖g‖ * ‖S.mkQL‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hg_norm (norm_mkQL_le S) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · rw [ContinuousLinearMap.comp_apply, hg_val, norm_mkQL_apply]

/-- **Norm-one annihilating functional at positive distance.** Let $E$ be a normed space over
$\mathbb{K}$, where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$, let $S$ be a linear subspace of
$E$, and let $x \in E$ have positive distance $d(x, S) = \inf_{s \in S} \|x - s\| > 0$ from $S$.
Then there is a continuous linear functional $f \colon E \to \mathbb{K}$ with $\|f\| = 1$ that
vanishes on $S$ and satisfies $f(x) = d(x, S)$.

A functional with $\|f\| \le 1$ that vanishes on $S$ and satisfies $f(x) = d(x, S)$ has norm
exactly $1$: for $s \in S$ we have $d(x, S) = |f(x - s)| \le \|f\| \, \|x - s\|$, and $s$ can be
chosen with $\|x - s\|$ arbitrarily close to $d(x, S) > 0$. -/
theorem exists_annihilating_norm_one (S : Submodule 𝕜 E) {x : E}
    (hx : 0 < Metric.infDist x (S : Set E)) :
    ∃ f : E →L[𝕜] 𝕜, (∀ s ∈ S, f s = 0) ∧ ‖f‖ = 1 ∧
      f x = (Metric.infDist x (S : Set E) : 𝕜) := by
  obtain ⟨f, hfvan, hf_norm, hf_val⟩ := exists_annihilating_apply_eq_infDist S x
  refine ⟨f, hfvan, le_antisymm hf_norm ?_, hf_val⟩
  by_contra hlt
  rw [not_le] at hlt
  have hfpos : 0 < ‖f‖ := by
    by_contra h0
    rw [not_lt] at h0
    have hfz : f = 0 := norm_le_zero_iff.mp h0
    have h2 := congrArg (fun z : 𝕜 => ‖z‖) hf_val
    rw [hfz] at h2
    simp only [zero_apply, norm_zero] at h2
    rw [RCLike.norm_ofReal, abs_of_nonneg Metric.infDist_nonneg] at h2
    exact (ne_of_gt hx) h2.symm
  have hdiv : Metric.infDist x (S : Set E) < Metric.infDist x (S : Set E) / ‖f‖ := by
    rw [lt_div_iff₀ hfpos]
    calc Metric.infDist x (S : Set E) * ‖f‖ < Metric.infDist x (S : Set E) * 1 :=
          mul_lt_mul_of_pos_left hlt hx
      _ = Metric.infDist x (S : Set E) := mul_one _
  obtain ⟨s, hs, hdist⟩ := (Metric.infDist_lt_iff ⟨0, zero_mem S⟩).mp hdiv
  have hle : Metric.infDist x (S : Set E) ≤ ‖f‖ * dist x s := by
    have h1 : f x = f (x - s) := by rw [map_sub, hfvan s hs, sub_zero]
    calc Metric.infDist x (S : Set E) = ‖f x‖ := by
          rw [hf_val, RCLike.norm_ofReal, abs_of_nonneg Metric.infDist_nonneg]
      _ = ‖f (x - s)‖ := by rw [h1]
      _ ≤ ‖f‖ * ‖x - s‖ := f.le_opNorm (x - s)
      _ = ‖f‖ * dist x s := by rw [dist_eq_norm]
  have hlt2 : ‖f‖ * dist x s < Metric.infDist x (S : Set E) := by
    calc ‖f‖ * dist x s < ‖f‖ * (Metric.infDist x (S : Set E) / ‖f‖) :=
          mul_lt_mul_of_pos_left hdist hfpos
      _ = Metric.infDist x (S : Set E) := mul_div_cancel₀ _ (ne_of_gt hfpos)
  exact absurd (lt_of_le_of_lt hle hlt2) (lt_irrefl _)

/-- **Norm-one annihilating functional outside a closed subspace.** Let $E$ be a normed space
over $\mathbb{K}$, where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$, let $S$ be a closed linear
subspace of $E$ and let $x \in E$ with $x \notin S$. Then there is a continuous linear functional
$f \colon E \to \mathbb{K}$ with $\|f\| = 1$ that vanishes on $S$ and satisfies
$f(x) = d(x, S)$, where $d(x, S) = \inf_{s \in S} \|x - s\|$ is the distance from $x$ to $S$.

Since $S$ is closed and $x \notin S$, the distance $d(x, S)$ is positive. -/
theorem exists_annihilating_of_notMem (S : Submodule 𝕜 E) (hS : IsClosed (S : Set E))
    {x : E} (hx : x ∉ S) :
    ∃ f : E →L[𝕜] 𝕜, (∀ s ∈ S, f s = 0) ∧ ‖f‖ = 1 ∧
      f x = (Metric.infDist x (S : Set E) : 𝕜) :=
  exists_annihilating_norm_one S ((hS.notMem_iff_infDist_pos ⟨0, zero_mem S⟩).mp hx)

/-- **Hahn–Banach distance formula.** Let $E$ be a normed space over $\mathbb{K}$, where
$\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$, let $S$ be a linear subspace of $E$, not
necessarily closed, and let $x \in E$. Then the distance $d(x, S) = \inf_{s \in S} \|x - s\|$
from $x$ to $S$ equals the supremum of $|f(x)|$ over all continuous linear functionals
$f \colon E \to \mathbb{K}$ with $\|f\| \le 1$ that vanish on $S$.

The supremum is attained, by the attainment form of the distance formula. -/
theorem infDist_eq_sSup_norm_apply (S : Submodule 𝕜 E) (x : E) :
    Metric.infDist x (S : Set E) =
      sSup { r : ℝ | ∃ f : E →L[𝕜] 𝕜, ‖f‖ ≤ 1 ∧ (∀ s ∈ S, f s = 0) ∧ ‖f x‖ = r } := by
  have hbound : ∀ r ∈ { r : ℝ | ∃ f : E →L[𝕜] 𝕜, ‖f‖ ≤ 1 ∧ (∀ s ∈ S, f s = 0) ∧
      ‖f x‖ = r }, r ≤ Metric.infDist x (S : Set E) := by
    intro r hr
    obtain ⟨f, hf_norm, hfvan, hfr⟩ := hr
    rw [← hfr]
    refine (Metric.le_infDist ⟨0, zero_mem S⟩).mpr fun s hs => ?_
    calc ‖f x‖ = ‖f (x - s)‖ := by rw [map_sub, hfvan s hs, sub_zero]
      _ ≤ ‖f‖ * ‖x - s‖ := f.le_opNorm (x - s)
      _ ≤ 1 * ‖x - s‖ := mul_le_mul_of_nonneg_right hf_norm (norm_nonneg _)
      _ = dist x s := by rw [one_mul, dist_eq_norm]
  have hmem : Metric.infDist x (S : Set E) ∈
      { r : ℝ | ∃ f : E →L[𝕜] 𝕜, ‖f‖ ≤ 1 ∧ (∀ s ∈ S, f s = 0) ∧ ‖f x‖ = r } := by
    obtain ⟨f, hfvan, hf_norm, hf_val⟩ := exists_annihilating_apply_eq_infDist S x
    refine ⟨f, hf_norm, hfvan, ?_⟩
    rw [hf_val, RCLike.norm_ofReal, abs_of_nonneg Metric.infDist_nonneg]
  apply le_antisymm
  · exact le_csSup ⟨Metric.infDist x (S : Set E), hbound⟩ hmem
  · exact csSup_le ⟨0, ⟨0, by simp, fun s _ => by simp, by simp⟩⟩ hbound

end MathlibExt.Analysis.Normed.Module.DualDistanceFormula
