/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Analysis/WienerLevy.lean` (leanprover/lean-eval, commit
38361be884302c7edce1908c4aef8296eb2cb27e), problem `wiener_levy_analytic_calculus` (manifest
`manifests/problems/wiener_levy_analytic_calculus.toml`, revision 1, submitted by Kim Morrison,
status archived). This attribution covers the definition of `InWienerAlgebra` and the statement
of `wiener_levy_analytic_calculus`.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License");
you may not use these portions except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). The former wanted module replaced the
benchmark marker and import with the Batteries wanted command and import, placed the declarations
in the ATLAS namespace, and updated their docstrings. The declarations move here with their
full names, definition, statement and docstrings preserved. The proof is new.
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Topology.MetricSpace.Thickening
import MathlibExt.Analysis.Complex.RectilinearCycle
import MathlibExt.Analysis.FunctionalAnalysis.IntConvolution

/-!
# Wiener–Lévy theorem (analytic functional calculus)

§226 of Oliver Knill's *Some Fundamental Theorems in Mathematics*. The
Wiener–Lévy theorem: if `φ` is complex-analytic on a neighbourhood of the
range of a Wiener-algebra function `f`, then the composition `φ ∘ f` is again
in the Wiener algebra.

mathlib has the additive circle, the Fourier characters `fourier`, Fourier
coefficients `fourierCoeff`, and `hasSum_fourier_series_of_summable`, but not
the Wiener algebra or its analytic functional calculus.

## Proof

Fourier synthesis identifies the characters of the `ℓ¹(ℤ)` convolution algebra with
evaluations on the circle. We integrate the resolvent along the boundary of a finite union
of squares surrounding the range, and the scalar Cauchy formula computes every evaluation
of the resulting element.
-/

namespace MathlibExt.Analysis.WienerLevyWanted.Analysis.WienerLevy

open Set Filter Complex MeasureTheory
open MathlibExt.Analysis.FunctionalAnalysis.IntConvolution
open scoped lp ENNReal Topology Interval

noncomputable section

private abbrev WienerSequence := ℓ¹(ℤ, ℂ)

private local instance instWienerSequenceRing : CommRing WienerSequence where
  __ := (inferInstance : AddCommGroup WienerSequence)
  one := l1Delta
  mul := l1Conv
  mul_assoc := l1Conv_assoc
  one_mul := l1Conv_delta_left
  mul_one := l1Conv_delta_right
  mul_comm := l1Conv_comm
  left_distrib := l1Conv_add_right
  right_distrib a b c := l1Conv_add_left a b c
  zero_mul := l1Conv_zero_left
  mul_zero := l1Conv_zero_right

private local instance instWienerSequenceNormedRing : NormedCommRing WienerSequence where
  __ := instWienerSequenceRing
  __ := (inferInstance : NormedAddCommGroup WienerSequence)
  norm_mul_le := norm_l1Conv_le

private local instance instWienerSequenceNormOne : NormOneClass WienerSequence where
  norm_one := norm_l1Delta

private local instance instWienerSequenceNormedAlgebra : NormedAlgebra ℂ WienerSequence where
  __ := (inferInstance : NormedSpace ℂ WienerSequence)
  __ := Algebra.ofModule
    (fun c f g => l1Conv_smul_left c f g)
    (fun c f g => l1Conv_smul_right c f g)

variable {T : ℝ} [Fact (0 < T)]

private theorem summable_norm_seq (a : WienerSequence) : Summable (fun n => ‖a n‖) := by
  simpa using (memℓp_gen_iff (by simp : 0 < (1 : ℝ≥0∞).toReal)).mp a.property

private theorem summable_synthesis_terms (a : WienerSequence) :
    Summable (fun n => a n • (@fourier T n)) :=
  .of_norm (by simpa only [norm_smul, fourier_norm, mul_one] using summable_norm_seq a)

private def synthesis : WienerSequence →L[ℂ] C(AddCircle T, ℂ) :=
  LinearMap.mkContinuous
    { toFun a := ∑' n, a n • fourier n
      map_add' a b := by
        simpa only [lp.coeFn_add, Pi.add_apply, add_smul] using
          (summable_synthesis_terms (T := T) a).tsum_add (summable_synthesis_terms (T := T) b)
      map_smul' c a := by
        simpa only [lp.coeFn_smul, Pi.smul_apply, smul_assoc, RingHom.id_apply] using
          (summable_synthesis_terms (T := T) a).tsum_const_smul c } 1 fun a => by
    rw [one_mul]
    refine (norm_tsum_le_tsum_norm ?_).trans_eq ?_
    · simpa only [norm_smul, fourier_norm, mul_one] using summable_norm_seq a
    · simpa only [norm_smul, fourier_norm, mul_one] using tsum_norm_l1 a

private theorem synthesis_apply (a : WienerSequence) (x : AddCircle T) :
    synthesis a x = ∑' n, a n * fourier n x := by
  change ContinuousMap.evalCLM ℂ x (∑' n, a n • fourier n) = _
  rw [ContinuousLinearMap.map_tsum]
  · rfl
  · exact .of_norm (by simpa only [norm_smul, fourier_norm, mul_one] using summable_norm_seq a)

private theorem synthesis_single (n : ℤ) (c : ℂ) (x : AddCircle T) :
    synthesis (lp.single 1 n c : WienerSequence) x = c * fourier n x := by
  rw [synthesis_apply, tsum_eq_single n]
  · rw [lp.single_apply_self]
  · intro m hm
    rw [lp.single_apply_ne _ _ _ hm, zero_mul]

private theorem synthesis_shift (a : WienerSequence) (m : ℤ) (x : AddCircle T) :
    synthesis (shiftLp m a) x = fourier m x * synthesis a x := by
  rw [synthesis_apply, synthesis_apply, ← tsum_mul_left]
  convert (Equiv.addLeft m).tsum_eq (fun n : ℤ => shiftLp m a n * fourier n x) |>.symm
    using 1
  apply tsum_congr
  intro n
  simp [shiftLp_apply, mul_left_comm]

private def synthesisAt (x : AddCircle T) : WienerSequence →ₐ[ℂ] ℂ where
  toFun a := synthesis a x
  map_one' := by
    change synthesis (lp.single 1 (0 : ℤ) 1 : WienerSequence) x = 1
    rw [synthesis_single, fourier_zero, one_mul]
  map_zero' := by rw [map_zero]; rfl
  map_add' a b := by rw [map_add]; rfl
  map_mul' a b := by
    change ContinuousMap.evalCLM ℂ x (synthesis (l1Conv a b)) =
      synthesis a x * synthesis b x
    rw [l1Conv, ← ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.map_tsum _ (summable_l1Conv_term a b)]
    change (∑' n : ℤ, (ContinuousMap.evalCLM ℂ x ∘L synthesis) (a n • shiftLp n b)) = _
    simp only [map_smul, ContinuousLinearMap.comp_apply, ContinuousMap.evalCLM_apply, smul_eq_mul,
      synthesis_shift]
    rw [synthesis_apply (T := T) a x, ← tsum_mul_right]
    simp only [mul_assoc]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul]
    change c * synthesis (lp.single 1 (0 : ℤ) 1 : WienerSequence) x = c
    rw [synthesis_single, fourier_zero, mul_one, mul_one]

private theorem synthesis_fourierCoeff (a : WienerSequence) :
    fourierCoeff (synthesis (T := T) a) = (a : ℤ → ℂ) := by
  apply fourierCoeff_eq_of_hasSum_of_summable_norm _ (summable_norm_seq a)
  intro x
  rw [synthesis_apply]
  simpa only [smul_eq_mul, mul_comm] using
    (Summable.of_norm (f := fun n => a n * (@fourier T n) x)
      (by simpa only [norm_mul, fourier_apply, Circle.norm_coe, mul_one] using
        summable_norm_seq a)).hasSum

private def basis (n : ℤ) : WienerSequence := lp.single 1 n 1

private theorem basis_zero : basis 0 = 1 := rfl

private theorem basis_add (i j : ℤ) : basis (i + j) = basis i * basis j := by
  change basis (i + j) = l1Conv (lp.single 1 i 1 : WienerSequence) (lp.single 1 j 1)
  rw [l1Conv_single_single, one_mul, basis]

private theorem norm_basis (n : ℤ) : ‖basis n‖ = 1 := by
  rw [basis, lp.norm_single (by simp : (0 : ℝ≥0∞) < 1), norm_one]

private theorem character_eq_synthesisAt (χ : WienerSequence →ₐ[ℂ] ℂ) :
    ∃ x : AddCircle T, χ = synthesisAt x := by
  have hnorm (n : ℤ) : ‖χ (basis n)‖ ≤ 1 :=
    (AlgHom.norm_apply_le_self χ _).trans_eq (norm_basis n)
  have hprod : χ (basis 1) * χ (basis (-1)) = 1 := by
    rw [← map_mul, ← basis_add, show (1 : ℤ) + -1 = 0 by norm_num, basis_zero, map_one]
  have hone : ‖χ (basis 1)‖ = 1 := by
    apply le_antisymm (hnorm 1)
    calc
      1 = ‖χ (basis 1) * χ (basis (-1))‖ := by rw [hprod, norm_one]
      _ ≤ ‖χ (basis 1)‖ := by
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (hnorm (-1))
  have hT : T ≠ 0 := (Fact.out : 0 < T).ne'
  let e := AddCircle.homeomorphCircle hT
  let z : Circle := ⟨χ (basis 1), by
    simpa [Circle, Submonoid.unitSphere, Metric.mem_sphere, dist_zero_right] using hone⟩
  let x := e.symm z
  have hx : fourier 1 x = χ (basis 1) := by
    rw [fourier_one, ← AddCircle.homeomorphCircle_apply hT]
    exact congrArg Subtype.val (e.apply_symm_apply z)
  have hb (n : ℤ) : χ (basis n) = fourier n x := by
    induction n using Int.induction_on with
    | zero => rw [basis_zero, map_one, fourier_zero]
    | succ n ih => rw [basis_add, map_mul, fourier_add, ih, hx]
    | pred n ih =>
      apply mul_right_cancel₀ (show χ (basis 1) ≠ 0 from norm_ne_zero_iff.mp (by simp [hone]))
      rw [← map_mul, ← basis_add, sub_add_cancel, ih, ← hx, ← fourier_add, sub_add_cancel]
  refine ⟨x, ?_⟩
  ext a
  change χ a = synthesis a x
  rw [synthesis_apply]
  calc
    χ a = ∑' n, χ (lp.single 1 n (a n) : WienerSequence) :=
      (χ.toContinuousLinearMap.hasSum (lp.hasSum_single (by simp) a)).tsum_eq.symm
    _ = _ := by
      apply tsum_congr
      intro n
      have hsingle : (lp.single 1 n (a n) : WienerSequence) = a n • basis n := by
        rw [basis, ← lp.single_smul, smul_eq_mul, mul_one]
      rw [hsingle, map_smul, smul_eq_mul, hb]

private theorem spectrum_subset_range (a : WienerSequence) :
    spectrum ℂ a ⊆ range (synthesis (T := T) a) := by
  intro z hz
  obtain ⟨χ, hχ⟩ := WeakDual.CharacterSpace.mem_spectrum_iff_exists.mp hz
  obtain ⟨x, hx⟩ := character_eq_synthesisAt (T := T)
    (WeakDual.CharacterSpace.equivAlgHom χ)
  exact ⟨x, (DFunLike.congr_fun hx a).symm.trans hχ⟩

namespace Grid

private abbrev Cell := ℤ × ℤ

-- A horizontal edge (false) runs right; a vertical edge (true) runs up.
private abbrev Edge := Bool × Cell

private def coord (s : ℝ) (n : ℤ) : ℝ := n * s

private theorem coord_mono {s : ℝ} (hs : 0 < s) : StrictMono (coord s) :=
  fun _ _ h => mul_lt_mul_of_pos_right (by exact_mod_cast h) hs

private theorem coord_lt_succ {s : ℝ} (hs : 0 < s) (n : ℤ) :
    coord s n < coord s (n + 1) := coord_mono hs (by omega)

private def east (p : Cell) : Cell := p + (1, 0)
private def north (p : Cell) : Cell := p + (0, 1)

private def cell (s : ℝ) (p : Cell) : RectilinearRectangle :=
  RectilinearRectangle.ofBounds (coord s p.1) (coord s (p.1 + 1))
    (coord s p.2) (coord s (p.2 + 1))

private theorem mem_cell {s : ℝ} (hs : 0 < s) (p : Cell) (z : ℂ) :
    z ∈ (cell s p).carrier ↔
      z.re ∈ Icc (coord s p.1) (coord s (p.1 + 1)) ∧
      z.im ∈ Icc (coord s p.2) (coord s (p.2 + 1)) := by
  simp only [cell, RectilinearRectangle.carrier, Rectangle, mem_reProdIm,
    RectilinearRectangle.ofBounds_first_re, RectilinearRectangle.ofBounds_second_re,
    RectilinearRectangle.ofBounds_first_im, RectilinearRectangle.ofBounds_second_im]
  simp only [uIcc_of_le (coord_lt_succ hs p.1).le,
    uIcc_of_le (coord_lt_succ hs p.2).le]

private def inner (s : ℝ) (p : Cell) : Set ℂ :=
  Ioo (coord s p.1) (coord s (p.1 + 1)) ×ℂ Ioo (coord s p.2) (coord s (p.2 + 1))

private theorem closure_inner {s : ℝ} (hs : 0 < s) (p : Cell) :
    closure (inner s p) = (cell s p).carrier := by
  rw [inner, closure_reProdIm, closure_Ioo (coord_lt_succ hs p.1).ne,
    closure_Ioo (coord_lt_succ hs p.2).ne]
  ext z
  rw [mem_reProdIm, mem_cell hs]

private theorem cell_covers {s : ℝ} (hs : 0 < s) (z : ℂ) :
    z ∈ (cell s (⌊z.re / s⌋, ⌊z.im / s⌋)).carrier := by
  rw [mem_cell hs]
  have h (x : ℝ) : x ∈ Icc (coord s ⌊x / s⌋) (coord s (⌊x / s⌋ + 1)) := by
    refine ⟨(le_div_iff₀ hs).mp (Int.floor_le _), ?_⟩
    exact ((div_lt_iff₀ hs).mp (Int.lt_floor_add_one _)).le.trans_eq
      (by simp [coord])
  exact ⟨h z.re, h z.im⟩

private theorem eq_of_mem_inner_cell {s : ℝ} (hs : 0 < s) {p q : Cell} {z : ℂ}
    (hp : z ∈ inner s p) (hq : z ∈ (cell s q).carrier) : p = q := by
  rw [inner, mem_reProdIm] at hp
  rw [mem_cell hs] at hq
  have eqIndex {x : ℝ} {i j : ℤ}
      (hi : x ∈ Ioo (coord s i) (coord s (i + 1)))
      (hj : x ∈ Icc (coord s j) (coord s (j + 1))) : i = j := by
    rcases lt_trichotomy i j with hij | h | hji
    · exact False.elim ((hi.2.trans_le ((coord_mono hs).monotone (by omega))).not_ge hj.1)
    · exact h
    · exact False.elim ((hi.1.trans_le' ((coord_mono hs).monotone (by omega))).not_ge hj.2)
  exact Prod.ext (eqIndex hp.1 hq.1) (eqIndex hp.2 hq.2)

private def edgeIndex (e : Edge) : ℤ := if e.1 then e.2.2 else e.2.1

private def edgePoint (s : ℝ) (e : Edge) (t : ℝ) : ℂ :=
  if e.1 then (coord s e.2.1 : ℂ) + t * I else (t : ℂ) + coord s e.2.2 * I

private theorem continuous_edgePoint (s : ℝ) (e : Edge) : Continuous (edgePoint s e) := by
  obtain ⟨d, p⟩ := e
  change Continuous (fun t => edgePoint s (d, p) t)
  cases d
  · change Continuous (fun t : ℝ => (t : ℂ) + (coord s p.2 : ℂ) * I)
    fun_prop
  · change Continuous (fun t : ℝ => (coord s p.1 : ℂ) + (t : ℂ) * I)
    fun_prop

private def interval (s : ℝ) (e : Edge) : Set ℝ :=
  [[coord s (edgeIndex e), coord s (edgeIndex e + 1)]]

private def edgeCarrier (s : ℝ) (e : Edge) : Set ℂ := edgePoint s e '' interval s e

private theorem compact_edgeCarrier (s : ℝ) (e : Edge) :
    IsCompact (edgeCarrier s e) := isCompact_uIcc.image (continuous_edgePoint s e)

private theorem mem_horizontal_cells {s : ℝ} (hs : 0 < s) {p : Cell} {z : ℂ}
    (hz : z ∈ edgeCarrier s (false, p)) :
    z ∈ (cell s p).carrier ∧ z ∈ (cell s (p - (0, 1))).carrier := by
  obtain ⟨t, ht, rfl⟩ := hz
  simp only [interval, edgeIndex, Bool.false_eq_true, ite_false,
    uIcc_of_le (coord_lt_succ hs _).le] at ht
  simp only [mem_cell hs, edgePoint, Bool.false_eq_true, ite_false, add_re, add_im, mul_re, mul_im,
    ofReal_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add,
    Prod.fst_sub, Prod.snd_sub, sub_add_cancel]
  exact ⟨⟨ht, le_rfl, (coord_lt_succ hs p.2).le⟩,
    ⟨ht, (coord_mono hs).monotone (show p.2 - 1 ≤ p.2 by omega), le_rfl⟩⟩

private theorem mem_vertical_cells {s : ℝ} (hs : 0 < s) {p : Cell} {z : ℂ}
    (hz : z ∈ edgeCarrier s (true, p)) :
    z ∈ (cell s p).carrier ∧ z ∈ (cell s (p - (1, 0))).carrier := by
  obtain ⟨t, ht, rfl⟩ := hz
  simp only [interval, edgeIndex, ite_true,
    uIcc_of_le (coord_lt_succ hs _).le] at ht
  simp only [mem_cell hs, edgePoint, ite_true, add_re, add_im, mul_re, mul_im,
    ofReal_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add,
    Prod.fst_sub, Prod.snd_sub, sub_add_cancel]
  exact ⟨⟨⟨le_rfl, (coord_lt_succ hs p.1).le⟩, ht⟩,
    ⟨⟨(coord_mono hs).monotone (show p.1 - 1 ≤ p.1 by omega), le_rfl⟩, ht⟩⟩

-- Using a finitely supported signed sum cancels shared sides before any integration.
private def cellBoundary (p : Cell) : Edge →₀ ℤ :=
  Finsupp.single (false, p) 1 - Finsupp.single (false, north p) 1 +
    Finsupp.single (true, east p) 1 - Finsupp.single (true, p) 1

private def boundary (S : Finset Cell) : Edge →₀ ℤ := ∑ p ∈ S, cellBoundary p

private theorem boundary_horizontal (S : Finset Cell) (p : Cell) :
    boundary S (false, p) =
      (if p ∈ S then 1 else 0) - (if p - (0, 1) ∈ S then 1 else 0) := by
  classical
  simp only [boundary, Finsupp.finsetSum_apply, cellBoundary, Finsupp.sub_apply, Finsupp.add_apply,
    Finsupp.single_apply, Prod.mk.injEq, Bool.true_eq_false, false_and, ite_false, true_and,
    add_zero, Finset.sum_const_zero, sub_zero, Finset.sum_sub_distrib, north, ← eq_sub_iff_add_eq,
    Finset.sum_ite_eq']

private theorem boundary_vertical (S : Finset Cell) (p : Cell) :
    boundary S (true, p) =
      (if p - (1, 0) ∈ S then 1 else 0) - (if p ∈ S then 1 else 0) := by
  classical
  simp only [boundary, Finsupp.finsetSum_apply, cellBoundary, Finsupp.sub_apply, Finsupp.add_apply,
    Finsupp.single_apply, Prod.mk.injEq, Bool.false_eq_true, false_and, ite_false, true_and,
    zero_sub, neg_zero, zero_add, Finset.sum_sub_distrib, east, ← eq_sub_iff_add_eq,
    Finset.sum_ite_eq']

private theorem boundary_avoids {s : ℝ} (hs : 0 < s) {K : Set ℂ} {S : Finset Cell}
    (hS : ∀ p z, z ∈ (cell s p).carrier → z ∈ K → p ∈ S)
    {e : Edge} (he : e ∈ (boundary S).support) {z : ℂ} (hz : z ∈ edgeCarrier s e) :
    z ∉ K := by
  classical
  intro hk
  obtain ⟨d, p⟩ := e
  rw [Finsupp.mem_support_iff] at he
  cases d with
  | false =>
    obtain ⟨h₁, h₂⟩ := mem_horizontal_cells hs hz
    simp [boundary_horizontal, hS p z h₁ hk, hS _ z h₂ hk] at he
  | true =>
    obtain ⟨h₁, h₂⟩ := mem_vertical_cells hs hz
    simp [boundary_vertical, hS p z h₁ hk, hS _ z h₂ hk] at he

private theorem boundary_subset {s : ℝ} (hs : 0 < s) {U : Set ℂ} {S : Finset Cell}
    (hS : ∀ p ∈ S, (cell s p).carrier ⊆ U)
    {e : Edge} (he : e ∈ (boundary S).support) :
    edgeCarrier s e ⊆ U := by
  classical
  intro z hz
  obtain ⟨d, p⟩ := e
  rw [Finsupp.mem_support_iff] at he
  cases d with
  | false =>
    obtain ⟨h₁, h₂⟩ := mem_horizontal_cells hs hz
    by_cases hp : p ∈ S
    · exact hS p hp h₁
    · by_cases hp' : p - (0, 1) ∈ S
      · exact hS _ hp' h₂
      · simp [boundary_horizontal, hp, hp'] at he
  | true =>
    obtain ⟨h₁, h₂⟩ := mem_vertical_cells hs hz
    by_cases hp : p ∈ S
    · exact hS p hp h₁
    · by_cases hp' : p - (1, 0) ∈ S
      · exact hS _ hp' h₂
      · simp [boundary_vertical, hp, hp'] at he

private theorem dist_le_of_mem_cell {s : ℝ} (hs : 0 < s) {p : Cell} {z w : ℂ}
    (hz : z ∈ (cell s p).carrier) (hw : w ∈ (cell s p).carrier) :
    dist z w ≤ 2 * s := by
  rw [mem_cell hs] at hz hw
  have width (j : ℤ) : coord s (j + 1) = coord s j + s := by
    simp [coord, add_mul]
  have hre : |z.re - w.re| ≤ s := by
    have hzu := hz.1.2
    have hwu := hw.1.2
    rw [width] at hzu hwu
    exact abs_le.mpr ⟨by linarith [hz.1.1], by linarith [hw.1.1]⟩
  have him : |z.im - w.im| ≤ s := by
    have hzu := hz.2.2
    have hwu := hw.2.2
    rw [width] at hzu hwu
    exact abs_le.mpr ⟨by linarith [hz.2.1], by linarith [hw.2.1]⟩
  rw [dist_eq_norm]
  exact (norm_le_abs_re_add_abs_im _).trans (by rw [sub_re, sub_im]; linarith)

private theorem exists_cells {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (s : ℝ) (S : Finset Cell), 0 < s ∧
      (∀ p z, z ∈ (cell s p).carrier → z ∈ K → p ∈ S) ∧
      (∀ p ∈ S, (cell s p).carrier ⊆ U) := by
  classical
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  let s := δ / 2
  have hs : 0 < s := half_pos hδ
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  let N : ℤ := ⌈B / s⌉ + 2
  let S : Finset Cell := ((Finset.Icc (-N) N) ×ˢ (Finset.Icc (-N) N)).filter
    fun p => ∃ z ∈ K, z ∈ (cell s p).carrier
  refine ⟨s, S, hs, ?_, ?_⟩
  · intro p z hz hzK
    have boundIndex (x : ℝ) (j : ℤ)
        (hx : x ∈ Icc (coord s j) (coord s (j + 1))) (habs : |x| ≤ B) :
        j ∈ Finset.Icc (-N) N := by
      have hj₁ : (j : ℝ) ≤ x / s := (le_div_iff₀ hs).mpr hx.1
      have hj₂ : x / s ≤ (j : ℝ) + 1 :=
        (div_le_iff₀ hs).mpr (by simpa [coord] using hx.2)
      have hxu := div_le_div_of_nonneg_right (abs_le.mp habs).2 hs.le
      have hxl := div_le_div_of_nonneg_right (abs_le.mp habs).1 hs.le
      have hceil := Int.le_ceil (B / s)
      rw [neg_div] at hxl
      rw [Finset.mem_Icc]
      have hj : ((-N : ℤ) : ℝ) ≤ (j : ℝ) ∧ (j : ℝ) ≤ (N : ℝ) := by
        simp only [Int.cast_neg, N, Int.cast_add, Int.cast_ofNat]
        constructor <;> linarith
      exact ⟨by exact_mod_cast hj.1, by exact_mod_cast hj.2⟩
    have hz' := (mem_cell hs p z).mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨boundIndex _ _ hz'.1 ((abs_re_le_norm z).trans (hB z hzK)),
       boundIndex _ _ hz'.2 ((abs_im_le_norm z).trans (hB z hzK))⟩, z, hzK, hz⟩
  · intro p hp z hz
    obtain ⟨w, hwK, hw⟩ := (Finset.mem_filter.mp hp).2
    apply hδU
    exact Metric.closedBall_subset_cthickening hwK δ (by
      rw [Metric.mem_closedBall]
      exact (dist_le_of_mem_cell hs hz hw).trans_eq (by dsimp [s]; ring))

section Integral

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

private def edgeFactor (e : Edge) : ℂ := if e.1 then I else 1

private def edgeIntegral (s : ℝ) (e : Edge) (f : ℂ → E) : E :=
  edgeFactor e • ∫ t in coord s (edgeIndex e)..coord s (edgeIndex e + 1), f (edgePoint s e t)

private def integralHom (s : ℝ) (f : ℂ → E) : (Edge →₀ ℤ) →+ E :=
  Finsupp.liftAddHom fun e =>
    { toFun n := n • edgeIntegral s e f
      map_zero' := zero_zsmul _
      map_add' := fun a b => add_zsmul _ a b }

private def integral (s : ℝ) (S : Finset Cell) (f : ℂ → E) : E :=
  integralHom s f (boundary S)

private theorem integral_support (s : ℝ) (S : Finset Cell) (f : ℂ → E) :
    integral s S f = ∑ e ∈ (boundary S).support, boundary S e • edgeIntegral s e f :=
  rfl

private theorem integral_cells [CompleteSpace E] (s : ℝ) (S : Finset Cell) (f : ℂ → E) :
    integral s S f = ∑ p ∈ S, (cell s p).boundaryIntegral f := by
  simp only [integral, boundary, map_sum, cellBoundary, map_sub, map_add]
  apply Finset.sum_congr rfl
  intro p _
  simp only [integralHom, Finsupp.liftAddHom_apply_single, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    edgeIntegral, edgeFactor, edgeIndex, edgePoint, Bool.false_eq_true, ite_false,
    ite_true, one_smul, north, east, Prod.fst_add, Prod.snd_add, add_zero, cell,
    RectilinearRectangle.boundaryIntegral, RectilinearRectangle.ofBounds_first_re,
    RectilinearRectangle.ofBounds_second_re, RectilinearRectangle.ofBounds_first_im,
    RectilinearRectangle.ofBounds_second_im]

omit [NormedSpace ℂ E] in
private theorem edge_continuousOn {s : ℝ} {e : Edge} {f : ℂ → E}
    (hf : ContinuousOn f (edgeCarrier s e)) : ContinuousOn (fun t => f (edgePoint s e t))
      (interval s e) :=
  hf.comp (continuous_edgePoint s e).continuousOn (mapsTo_image _ _)

private theorem map_integral [CompleteSpace E] [CompleteSpace F]
    (L : E →L[ℂ] F) (s : ℝ) (S : Finset Cell) (f : ℂ → E)
    (hf : ∀ e ∈ (boundary S).support, ContinuousOn f (edgeCarrier s e)) :
    L (integral s S f) = integral s S (fun z => L (f z)) := by
  simp only [integral_support, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro e he
  congr 1
  rw [edgeIntegral, edgeIntegral, map_smul,
    L.intervalIntegral_comp_comm ((edge_continuousOn (hf e he)).intervalIntegrable)]

end Integral

private theorem continuousOn_edge_kernel {s : ℝ} (hs : 0 < s) (e : Edge) :
    ContinuousOn (fun w => edgeIntegral s e (fun z => (z - w)⁻¹))
      (edgeCarrier s e)ᶜ := by
  rw [continuousOn_iff_continuous_domRestrict]
  let a := coord s (edgeIndex e)
  let b := coord s (edgeIndex e + 1)
  have hab : a ≤ b := (coord_lt_succ hs _).le
  let project (t : ℝ) : Icc a b := projIcc a b hab t
  have hp : Continuous project := continuous_projIcc
  let X := (edgeCarrier s e)ᶜ
  let f (w : X) (t : ℝ) : ℂ := (edgePoint s e (project t) - (w : ℂ))⁻¹
  have hF : Continuous (Function.uncurry f) := by
    apply Continuous.inv₀
    · exact ((continuous_edgePoint s e).comp
        (continuous_subtype_val.comp (hp.comp continuous_snd))).sub
        (continuous_subtype_val.comp continuous_fst)
    · intro ⟨w, t⟩ ht
      apply w.property
      have heq : edgePoint s e (project t) = (w : ℂ) := sub_eq_zero.mp ht
      rw [← heq]
      refine ⟨project t, ?_, rfl⟩
      change (project t : ℝ) ∈ [[a, b]]
      rw [uIcc_of_le hab]
      exact (project t).property
  have hint := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) hF a b
  refine (hint.const_smul (edgeFactor e)).congr ?_
  intro w
  change edgeFactor e • (∫ t in a..b, f w t) =
    edgeFactor e • (∫ t in a..b, (edgePoint s e t - (w : ℂ))⁻¹)
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hab] at ht
  simp [f, project, projIcc_of_mem hab ht]

private theorem integral_kernel {s : ℝ} (hs : 0 < s) {S : Finset Cell}
    {p : Cell} (hp : p ∈ S) {w : ℂ} (hw : w ∈ (cell s p).carrier)
    (havoid : ∀ e ∈ (boundary S).support, w ∉ edgeCarrier s e) :
    integral s S (fun z => (z - w)⁻¹) = (2 * Real.pi : ℂ) * I := by
  classical
  have hinterior (v : ℂ) (hv : v ∈ inner s p) :
      integral s S (fun z => (z - v)⁻¹) = (2 * Real.pi : ℂ) * I := by
    rw [integral_cells, Finset.sum_eq_single_of_mem p hp]
    · rw [inner, mem_reProdIm] at hv
      exact RectilinearRectangle.boundaryIntegral_ofBounds_inv_sub_eq_two_pi_mul_I
        hv.1.1 hv.1.2 hv.2.1 hv.2.2
    · intro q _ hqp
      exact (cell s q).boundaryIntegral_inv_sub_eq_zero_of_not_mem_carrier
        (fun hq => hqp (eq_of_mem_inner_cell hs hv hq).symm)
  have hcont : ContinuousAt (fun v => integral s S (fun z => (z - v)⁻¹)) w := by
    simp only [integral_support]
    apply tendsto_finsetSum
    intro e he
    have hopen := (compact_edgeCarrier s e).isClosed.isOpen_compl
    exact ((continuousOn_edge_kernel hs e).continuousAt
      (hopen.mem_nhds (havoid e he))).const_smul _
  -- The pole may lie on a cancelled grid edge. Approach it from inside the selected cell.
  have hclosure : w ∈ closure (inner s p) := by rwa [closure_inner hs]
  have : (𝓝[inner s p] w).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hclosure
  exact tendsto_nhds_unique hcont.continuousWithinAt
    (tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall
      fun v hv => (hinterior v hv).symm))

private theorem cauchy_formula {s : ℝ} (hs : 0 < s) {S : Finset Cell}
    {U : Set ℂ} (hSU : ∀ p ∈ S, (cell s p).carrier ⊆ U) {φ : ℂ → ℂ}
    (hφ : AnalyticOnNhd ℂ φ U)
    {p : Cell} (hp : p ∈ S) {w : ℂ} (hw : w ∈ (cell s p).carrier)
    (havoid : ∀ e ∈ (boundary S).support, w ∉ edgeCarrier s e) :
    integral s S (fun z => φ z * (z - w)⁻¹) = ((2 * Real.pi : ℂ) * I) * φ w := by
  classical
  let D := dslope φ w
  have hD : AnalyticOnNhd ℂ D U := fun z hz => (hφ z hz).dslope w
  have hzero : integral s S D = 0 := by
    rw [integral_cells]
    exact Finset.sum_eq_zero (fun q hq =>
      (cell s q).boundaryIntegral_eq_zero (hD.differentiableOn.mono (hSU q hq)))
  have hedge (e : Edge) (he : e ∈ (boundary S).support) :
      edgeIntegral s e (fun z => φ z * (z - w)⁻¹) =
        edgeIntegral s e D + φ w • edgeIntegral s e (fun z => (z - w)⁻¹) := by
    have hsub : edgeCarrier s e ⊆ U := boundary_subset hs hSU he
    have hD' := (edge_continuousOn (hD.continuousOn.mono hsub)).intervalIntegrable (μ := volume)
    have hK : ContinuousOn (fun z : ℂ => (z - w)⁻¹) (edgeCarrier s e) :=
      (continuous_id.sub continuous_const).continuousOn.inv₀
        (fun z hz => sub_ne_zero.mpr (ne_of_mem_of_not_mem hz (havoid e he)))
    have hK' := (edge_continuousOn hK).intervalIntegrable (μ := volume)
    have hpoint (z : ℂ) (hz : z ∈ edgeCarrier s e) :
        φ z * (z - w)⁻¹ = D z + φ w • (z - w)⁻¹ := by
      have hne := sub_ne_zero.mpr (ne_of_mem_of_not_mem hz (havoid e he))
      apply (mul_right_cancel₀ hne)
      rw [mul_assoc, inv_mul_cancel₀ hne, mul_one, add_mul, smul_eq_mul,
        mul_assoc, inv_mul_cancel₀ hne, mul_one, mul_comm (D z)]
      exact sub_eq_iff_eq_add.mp (sub_smul_dslope φ w z).symm
    have hadd := intervalIntegral.integral_add hD' (hK'.smul (φ w))
    simp only [Pi.smul_apply] at hadd
    unfold edgeIntegral
    rw [show (∫ t in coord s (edgeIndex e)..coord s (edgeIndex e + 1),
          φ (edgePoint s e t) * (edgePoint s e t - w)⁻¹) =
        ∫ t in coord s (edgeIndex e)..coord s (edgeIndex e + 1),
          D (edgePoint s e t) + φ w • (edgePoint s e t - w)⁻¹ from
        intervalIntegral.integral_congr (fun t ht => hpoint _ ⟨t, ht, rfl⟩),
      hadd, intervalIntegral.integral_smul,
      smul_add, smul_comm (edgeFactor e)]
  calc
    _ = integral s S D + φ w • integral s S (fun z => (z - w)⁻¹) := by
      simp only [integral_support, Finset.smul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e he
      rw [hedge e he, smul_add, smul_comm (boundary S e)]
    _ = _ := by rw [hzero, zero_add, integral_kernel hs hp hw havoid, smul_eq_mul, mul_comm]

end Grid

private theorem synthesisAt_resolvent (a : WienerSequence) (x : AddCircle T) {z : ℂ}
    (hz : z ∈ resolventSet ℂ a) :
    synthesisAt x (resolvent a z) = (z - synthesisAt x a)⁻¹ := by
  have h : (algebraMap ℂ WienerSequence z - a) * resolvent a z = 1 := by
    rw [spectrum.resolvent_eq hz]
    exact hz.mul_val_inv
  apply eq_inv_of_mul_eq_one_right
  simpa only [map_mul, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, map_one]
    using congrArg (synthesisAt x) h

private theorem synthesis_comp (a : WienerSequence) (φ : ℂ → ℂ) (U : Set ℂ)
    (hU : IsOpen U) (hKU : range (synthesis (T := T) a) ⊆ U)
    (hφ : AnalyticOnNhd ℂ φ U) :
    ∃ b : WienerSequence, ∀ x : AddCircle T, synthesis b x = φ (synthesis a x) := by
  let K := range (synthesis (T := T) a)
  obtain ⟨s, S, hs, hS, hSU⟩ :=
    Grid.exists_cells (K := K) (isCompact_range (synthesis (T := T) a).continuous) hU hKU
  let F : ℂ → WienerSequence := fun z => φ z • resolvent a z
  let c : ℂ := (2 * Real.pi : ℂ) * Complex.I
  let b := c⁻¹ • Grid.integral s S F
  have hc : c ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have hres (e) (he : e ∈ (Grid.boundary S).support) {z} (hz : z ∈ Grid.edgeCarrier s e) :
      z ∈ resolventSet ℂ a := by
    by_contra hza
    exact Grid.boundary_avoids hs hS he hz (spectrum_subset_range (T := T) a hza)
  have hF (e) (he : e ∈ (Grid.boundary S).support) :
      ContinuousOn F (Grid.edgeCarrier s e) :=
    (hφ.continuousOn.mono (Grid.boundary_subset hs hSU he)).smul (fun _ hz =>
      (spectrum.hasDerivAt_resolvent_const_left (hres e he hz)).continuousAt.continuousWithinAt)
  refine ⟨b, fun x => ?_⟩
  let L := (synthesisAt x).toContinuousLinearMap
  let w := synthesis a x
  let p := (⌊w.re / s⌋, ⌊w.im / s⌋)
  have hw : w ∈ (Grid.cell s p).carrier := Grid.cell_covers hs w
  have hwK : w ∈ K := ⟨x, rfl⟩
  have hp : p ∈ S := hS p w hw hwK
  have havoid (e) (he : e ∈ (Grid.boundary S).support) : w ∉ Grid.edgeCarrier s e :=
    fun hw' => Grid.boundary_avoids hs hS he hw' hwK
  have heval (e) (he : e ∈ (Grid.boundary S).support) {z} (hz : z ∈ Grid.edgeCarrier s e) :
      L (F z) = φ z * (z - w)⁻¹ := by
    change synthesisAt x (φ z • resolvent a z) = _
    rw [map_smul, synthesisAt_resolvent a x (hres e he hz), smul_eq_mul]
    rfl
  have hint :
      Grid.integral s S (fun z => L (F z)) = Grid.integral s S (fun z => φ z * (z - w)⁻¹) := by
    simp only [Grid.integral_support]
    apply Finset.sum_congr rfl
    intro e he
    congr 1
    unfold Grid.edgeIntegral
    congr 1
    exact intervalIntegral.integral_congr (fun t ht => heval e he ⟨t, ht, rfl⟩)
  change L (c⁻¹ • Grid.integral s S F) = φ w
  rw [map_smul, Grid.map_integral L s S F hF, hint, Grid.cauchy_formula hs hSU hφ hp hw havoid]
  rw [smul_eq_mul]
  change c⁻¹ * (c * φ w) = φ w
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

@[expose] public section

set_option linter.dupNamespace false in
/-- **Wiener algebra on the circle.** Let $T > 0$. A continuous function
$f : \mathbb{R}/T\mathbb{Z} \to \mathbb{C}$ lies in the Wiener algebra when the family of its
Fourier coefficients $\hat f(n) = \frac{1}{T} \int_0^T f(x) e^{-2\pi i n x / T} \, dx$,
$n \in \mathbb{Z}$, is summable in $\mathbb{C}$.

For complex families, summability is equivalent to $\sum_{n \in \mathbb{Z}} |\hat f(n)| < \infty$,
so these are the functions with absolutely convergent Fourier series. -/
def InWienerAlgebra (f : C(AddCircle T, ℂ)) : Prop :=
  Summable (fourierCoeff f)

set_option linter.dupNamespace false in
/-- **Wiener–Lévy theorem.** Let $T > 0$, and let $f : \mathbb{R}/T\mathbb{Z} \to \mathbb{C}$ be a
continuous function in the Wiener algebra. Let $U \subseteq \mathbb{C}$ be an open set containing
the range of $f$, and let $\varphi : \mathbb{C} \to \mathbb{C}$ be analytic at every point of $U$.
Then there is a continuous function $g : \mathbb{R}/T\mathbb{Z} \to \mathbb{C}$ with
$g(x) = \varphi(f(x))$ for every $x$, and $g$ lies in the Wiener algebra.

Source: P. Lévy, Sur la convergence absolue des séries de Fourier, Compositio Math. 1 (1935), 1-14;
N. Wiener, Tauberian theorems, Ann. of Math. 33 (1932), 1-100. Listed as §226 in O. Knill, Some
Fundamental Theorems in Mathematics
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Knill, §226. Via
leanprover/lean-eval@38361be, problem `wiener_levy_analytic_calculus`. -/
public theorem wiener_levy_analytic_calculus (f : C(AddCircle T, ℂ))
    (φ : ℂ → ℂ) (U : Set ℂ) (hf : InWienerAlgebra f)
    (hU : IsOpen U) (hrange : range f ⊆ U)
    (hφ : AnalyticOnNhd ℂ φ U) :
    ∃ g : C(AddCircle T, ℂ),
      (∀ x, g x = φ (f x)) ∧ InWienerAlgebra g := by
  let a : WienerSequence := ⟨fourierCoeff f, (memℓp_gen_iff (by simp)).mpr (by
    simpa using (show Summable (fourierCoeff f) from hf).norm)⟩
  have ha : synthesis a = f := (hasSum_fourier_series_of_summable hf).tsum_eq
  obtain ⟨b, hb⟩ := synthesis_comp a φ U hU (by rwa [ha]) hφ
  refine ⟨synthesis b, ?_, ?_⟩
  · simpa only [ha] using hb
  · change Summable (fourierCoeff (synthesis b))
    rw [synthesis_fourierCoeff]
    exact .of_norm (summable_norm_seq b)

end

end

end MathlibExt.Analysis.WienerLevyWanted.Analysis.WienerLevy
