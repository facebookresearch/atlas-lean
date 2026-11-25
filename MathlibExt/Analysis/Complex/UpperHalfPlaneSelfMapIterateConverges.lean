/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 OpenBMB

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

Attribution and modification notice: the statement is adapted from openbmb/ma-proofbench at commit
31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_34.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; also distributed in the Hugging Face dataset
openbmb/MA-ProofBench), under the MIT license above. The ATLAS import converted the statement to
`theorem_wanted`, named and documented it in the namespace below, and used a public module import.
This file preserves the statement and audited docstring, supplies a proof, and narrows the imports.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.UnitDisc.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.Analysis.Complex.DiskToUpperHalfPlaneCayley

/-!
# Convergence of upper half-plane iterates

The Cayley map conjugates the self-map to a normalized disk map. The given value at the starting
point rules out equality in Schwarz's lemma. The divided difference has a maximum strictly below
one on the closed disk containing the orbit, which gives geometric convergence.
-/

open Complex Set Metric Filter
open scoped Topology

noncomputable section

namespace MathlibExt.Analysis.Complex.UpperHalfPlaneSelfMapIterateConvergesWanted

private abbrev disk := ball (0 : ℂ) 1
private abbrev upper : Set ℂ := {z | 0 < z.im}

private def fromDisk (w : ℂ) : ℂ := Complex.I * (1 - w) / (1 + w)
private def toDisk (z : ℂ) : ℂ := (Complex.I - z) / (Complex.I + z)

private theorem fromDisk_bij : BijOn fromDisk disk upper :=
  MathlibExt.Analysis.Complex.DiskToUpperHalfPlaneCayleyWanted.bijOn_cayley_ball_upperHalfPlane
    fromDisk rfl

private theorem fromDisk_denom {w : ℂ} (hw : w ∈ disk) : 1 + w ≠ 0 :=
  UnitDisc.one_add_coe_ne_zero ⟨w, hw⟩

private theorem toDisk_denom {z : ℂ} (hz : z ∈ upper) : I + z ≠ 0 := by
  change 0 < z.im at hz
  intro h
  have hh := congrArg Complex.im h
  simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at hh
  linarith

private theorem toDisk_fromDisk {w : ℂ} (hw : w ∈ disk) : toDisk (fromDisk w) = w := by
  have hd := toDisk_denom (fromDisk_bij.mapsTo hw)
  apply (div_eq_iff hd).mpr
  dsimp only [fromDisk]
  field_simp [fromDisk_denom hw]
  ring

private theorem toDisk_maps_inverse {z : ℂ} (hz : z ∈ upper) :
    toDisk z ∈ disk ∧ fromDisk (toDisk z) = z := by
  obtain ⟨w, hw, rfl⟩ := fromDisk_bij.surjOn hz
  rw [toDisk_fromDisk hw]
  exact ⟨hw, rfl⟩

private theorem fromDisk_differentiable : DifferentiableOn ℂ fromDisk disk := by
  intro w hw
  exact (((differentiableAt_const _).mul ((differentiableAt_const _).sub differentiableAt_id)).div
    ((differentiableAt_const _).add differentiableAt_id) (fromDisk_denom hw)).differentiableWithinAt

private theorem toDisk_differentiable : DifferentiableOn ℂ toDisk upper := by
  intro z hz
  exact (((differentiableAt_const _).sub differentiableAt_id).div
    ((differentiableAt_const _).add differentiableAt_id) (toDisk_denom hz)).differentiableWithinAt

private theorem fromDisk_zero : fromDisk 0 = I := by simp [fromDisk]
private theorem toDisk_I : toDisk I = 0 := by simp [toDisk]

private theorem fromDisk_seed : fromDisk (-(1 / 3 : ℂ)) = 2 * I := by
  unfold fromDisk
  apply (div_eq_iff (by norm_num : 1 + -(1 / 3 : ℂ) ≠ 0)).mpr
  ring

private theorem fromDisk_first : fromDisk (-(7 / 23 : ℂ)) = (15 / (8 : ℂ)) * I := by
  unfold fromDisk
  apply (div_eq_iff (by norm_num : 1 + -(7 / 23 : ℂ) ≠ 0)).mpr
  ring

private theorem seed_mem_disk : -(1 / 3 : ℂ) ∈ disk := by
  rw [mem_ball_zero_iff, norm_neg, norm_div, norm_one, Complex.norm_ofNat]
  norm_num

private theorem first_mem_disk : -(7 / 23 : ℂ) ∈ disk := by
  rw [mem_ball_zero_iff, norm_neg, norm_div, Complex.norm_ofNat, Complex.norm_ofNat]
  norm_num

/-- One strict Schwarz inequality gives a uniform contraction on every smaller closed disk. -/
private theorem disk_iterates_tendsto_of_strict {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g disk) (hm : MapsTo g disk disk) (hg0 : g 0 = 0)
    {w : ℂ} (hw : w ∈ disk) (hs : ‖g w‖ < ‖w‖) {a : ℂ} (ha : a ∈ disk) :
    Tendsto (fun n : ℕ => (g^[n]) a) atTop (𝓝 0) := by
  have hmap : MapsTo g disk (closedBall (g 0) 1) := by
    rw [hg0]
    exact hm.mono_right ball_subset_closedBall
  have hslope (z : ℂ) (hz : z ∈ disk) : ‖dslope g 0 z‖ < 1 := by
    have hle : ‖dslope g 0 z‖ ≤ 1 := by
      simpa only [div_one] using Complex.norm_dslope_le_div_of_mapsTo_ball hg hmap hz
    apply lt_of_le_of_ne hle
    intro heq
    have hAffine := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div hg hmap hz
      (by simpa only [div_one] using heq)
    have he := hAffine hw
    simp only [hg0, sub_zero, zero_add] at he
    have hnorm : ‖g w‖ = ‖w‖ := by rw [he, norm_smul, heq, mul_one]
    exact hs.ne hnorm
  let S := closedBall (0 : ℂ) ‖a‖
  have hS : S ⊆ disk := by
    intro z hz
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hz).trans_lt (mem_ball_zero_iff.mp ha))
  have hS₀ : S.Nonempty := ⟨0, mem_closedBall_self (norm_nonneg a)⟩
  have hdiff : DifferentiableOn ℂ (dslope g 0) disk :=
    (Complex.differentiableOn_dslope (ball_mem_nhds (0 : ℂ) zero_lt_one)).mpr hg
  obtain ⟨z₀, hz₀, hkMax⟩ := (isCompact_closedBall (0 : ℂ) ‖a‖).exists_isMaxOn hS₀
    (hdiff.continuousOn.mono hS).norm
  let k := ‖dslope g 0 z₀‖
  have hk0 : 0 ≤ k := norm_nonneg _
  have hk1 : k < 1 := hslope z₀ (hS hz₀)
  have hg_le (z : ℂ) (hz : z ∈ S) : ‖g z‖ ≤ k * ‖z‖ := by
    by_cases hz0 : z = 0
    · simp [hz0, hg0]
    have he : z • dslope g 0 z = g z := by
      rw [dslope_of_ne _ hz0, slope_def_module, sub_zero, hg0, sub_zero, smul_inv_smul₀ hz0]
    have hzle : ‖dslope g 0 z‖ ≤ k := isMaxOn_iff.mp hkMax z hz
    calc
      ‖g z‖ = ‖z‖ * ‖dslope g 0 z‖ := by rw [← norm_smul, he]
      _ ≤ ‖z‖ * k := mul_le_mul_of_nonneg_left hzle (norm_nonneg _)
      _ = k * ‖z‖ := mul_comm _ _
  have horbit (n : ℕ) : ‖(g^[n]) a‖ ≤ ‖a‖ ∧ ‖(g^[n]) a‖ ≤ ‖a‖ * k ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hmem : (g^[n]) a ∈ S := mem_closedBall_zero_iff.mpr ih.1
      have hsuc := hg_le ((g^[n]) a) hmem
      have hkle : k * ‖(g^[n]) a‖ ≤ ‖(g^[n]) a‖ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hk1.le (norm_nonneg ((g^[n]) a))
      constructor
      · exact (hsuc.trans hkle).trans ih.1
      · calc
          _ ≤ k * (‖a‖ * k ^ n) := hsuc.trans (mul_le_mul_of_nonneg_left ih.2 hk0)
          _ = ‖a‖ * k ^ (n + 1) := by rw [pow_succ]; ring
  have hdecay : Tendsto (fun n : ℕ => ‖a‖ * k ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hk0 hk1)
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero (fun _ => norm_nonneg _) (fun n => (horbit n).2) hdecay)

/-- **Iterates of a self-map of the upper half-plane fixing $i$.** Let
$\mathbb{H}=\{z\in\mathbb{C} : \mathrm{Im}\,z>0\}$ be the upper half-plane, and let $f$ be a
complex function that is holomorphic on $\mathbb{H}$, maps $\mathbb{H}$ into $\mathbb{H}$, and
satisfies $f(i)=i$ and $f(2i)=\frac{15}{8}i$. Then the iterates $f^{\circ n}(2i)$ converge to $i$
as $n\to\infty$, where $f^{\circ n}$ is the $n$-fold composite of $f$ with itself.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functions of a complex
variable; Geometric function theory), `benchmark/level2/ma_proofbench_l2_34.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem tendsto_iterate_two_mul_I_of_fixed_I
    (f : ℂ → ℂ)
    (hf_maps : ∀ z : ℂ, 0 < z.im → 0 < (f z).im)
    (hf_holo : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hfi : f Complex.I = Complex.I)
    (hf2i : f (2 * Complex.I) = ((15 / (8 : ℂ)) * Complex.I)) :
    Filter.Tendsto (fun n : ℕ => (f^[n]) (2 * Complex.I)) Filter.atTop (nhds Complex.I) := by
  let a : ℂ := -(1 / 3 : ℂ)
  let b : ℂ := -(7 / 23 : ℂ)
  let g := toDisk ∘ f ∘ fromDisk
  have hF : MapsTo f upper upper := fun {z} hz => hf_maps z hz
  have hT : MapsTo toDisk upper disk := fun {_} hz => (toDisk_maps_inverse hz).1
  have hm : MapsTo g disk disk := hT.comp (hF.comp fromDisk_bij.mapsTo)
  have hd : DifferentiableOn ℂ g disk :=
    toDisk_differentiable.comp (hf_holo.comp fromDisk_differentiable fromDisk_bij.mapsTo)
      (hF.comp fromDisk_bij.mapsTo)
  have h0 : g 0 = 0 := by simp [g, fromDisk_zero, hfi, toDisk_I]
  have ha : a ∈ disk := seed_mem_disk
  have hgb : g a = b := by
    change toDisk (f (fromDisk (-(1 / 3 : ℂ)))) = -(7 / 23 : ℂ)
    rw [fromDisk_seed, hf2i, ← fromDisk_first, toDisk_fromDisk first_mem_disk]
  have hstrict : ‖g a‖ < ‖a‖ := by
    rw [hgb]
    norm_num [a, b, norm_neg, norm_div, Complex.norm_ofNat]
  have hlim : Tendsto (fun n : ℕ => (g^[n]) a) atTop (𝓝 0) :=
    disk_iterates_tendsto_of_strict hd hm h0 ha hstrict ha
  have hmem (n : ℕ) : (g^[n]) a ∈ disk := by
    induction n with
    | zero => exact ha
    | succ n ih => rw [Function.iterate_succ_apply']; exact hm ih
  have hconj (n : ℕ) : fromDisk ((g^[n]) a) = (f^[n]) (2 * Complex.I) := by
    induction n with
    | zero => exact fromDisk_seed
    | succ n ih =>
      simp only [Function.iterate_succ_apply']
      rw [← ih]
      exact (toDisk_maps_inverse (hF (fromDisk_bij.mapsTo (hmem n)))).2
  have hcont : ContinuousAt fromDisk 0 :=
    (fromDisk_differentiable.differentiableAt (ball_mem_nhds (0 : ℂ) zero_lt_one)).continuousAt
  have h := hcont.tendsto.comp hlim
  rw [fromDisk_zero] at h
  exact Filter.Tendsto.congr' (Filter.Eventually.of_forall hconj) h

end MathlibExt.Analysis.Complex.UpperHalfPlaneSelfMapIterateConvergesWanted
