/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Ordered

/-!
# Jordan decomposition of real continuous-function functionals

For a compact topological space `X`, every bounded real functional `F : C(X,ℝ) → ℝ` has positive
bounded parts `F⁺,F⁻` satisfying `F=F⁺-F⁻`, `‖F‖=F⁺(1)+F⁻(1)`, and `‖F⁺‖=F⁺(1)`, `‖F⁻‖=F⁻(1)`.

The positive part is obtained from the lattice positive part of the functional, and the negative
part is the positive part of `-F`. No Hausdorff or nonempty-space condition is required.
-/

public section

open Set

namespace MathlibExt.Analysis.FunctionalAnalysis

noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X] [CompactSpace X]

private def coneImage (F : StrongDual ℝ C(X, ℝ)) (f : C(X, ℝ)) : Set ℝ :=
  F '' Set.Icc 0 f

omit [CompactSpace X] in
private theorem coneImage_nonempty (F : StrongDual ℝ C(X, ℝ)) {f : C(X, ℝ)} (hf : 0 ≤ f) :
    (coneImage F f).Nonempty := by
  exact ⟨0, 0, ⟨le_rfl, hf⟩, map_zero F⟩

private theorem norm_le_norm_of_nonneg_le {f g : C(X, ℝ)} (hf : 0 ≤ f) (hfg : f ≤ g) :
    ‖f‖ ≤ ‖g‖ := by
  apply (ContinuousMap.norm_le f (norm_nonneg g)).2
  intro x
  rw [Real.norm_of_nonneg (ContinuousMap.le_def.mp hf x)]
  exact (ContinuousMap.le_def.mp hfg x).trans
    ((le_abs_self (g x)).trans (g.norm_coe_le_norm x))

omit [CompactSpace X] in
private theorem cm_add_nonneg {f g : C(X, ℝ)} (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f + g := by
  rw [ContinuousMap.le_def]
  intro x
  exact add_nonneg (ContinuousMap.le_def.mp hf x) (ContinuousMap.le_def.mp hg x)

omit [CompactSpace X] in
private theorem cm_add_le_add {a b c d : C(X, ℝ)} (hac : a ≤ c) (hbd : b ≤ d) :
    a + b ≤ c + d := by
  rw [ContinuousMap.le_def]
  intro x
  exact add_le_add (ContinuousMap.le_def.mp hac x) (ContinuousMap.le_def.mp hbd x)

omit [CompactSpace X] in
private theorem cm_sub_nonneg {f g : C(X, ℝ)} (hgf : g ≤ f) : 0 ≤ f - g := by
  rw [ContinuousMap.le_def]
  intro x
  exact sub_nonneg.mpr (ContinuousMap.le_def.mp hgf x)

omit [CompactSpace X] in
private theorem cm_smul_nonneg {f : C(X, ℝ)} {c : ℝ} (hc : 0 ≤ c) (hf : 0 ≤ f) :
    0 ≤ c • f := by
  rw [ContinuousMap.le_def]
  intro x
  exact mul_nonneg hc (ContinuousMap.le_def.mp hf x)

omit [CompactSpace X] in
private theorem cm_smul_le_smul {f g : C(X, ℝ)} {c : ℝ} (hc : 0 ≤ c) (hfg : f ≤ g) :
    c • f ≤ c • g := by
  rw [ContinuousMap.le_def]
  intro x
  exact mul_le_mul_of_nonneg_left (ContinuousMap.le_def.mp hfg x) hc

private theorem coneImage_bddAbove (F : StrongDual ℝ C(X, ℝ)) {f : C(X, ℝ)} (_hf : 0 ≤ f) :
    BddAbove (coneImage F f) := by
  refine ⟨‖F‖ * ‖f‖, ?_⟩
  rintro y ⟨g, hg, rfl⟩
  calc
    F g ≤ ‖F g‖ := Real.le_norm_self _
    _ ≤ ‖F‖ * ‖g‖ := F.le_opNorm g
    _ ≤ ‖F‖ * ‖f‖ := mul_le_mul_of_nonneg_left
      (norm_le_norm_of_nonneg_le hg.1 hg.2) (norm_nonneg F)

private noncomputable def positiveAux (F : StrongDual ℝ C(X, ℝ)) (f : C(X, ℝ)) : ℝ :=
  sSup (coneImage F f)

private theorem apply_le_positiveAux (F : StrongDual ℝ C(X, ℝ)) {f g : C(X, ℝ)}
    (hf : 0 ≤ f) (hg : g ∈ Set.Icc (0 : C(X, ℝ)) f) :
    F g ≤ positiveAux F f := by
  exact le_csSup (coneImage_bddAbove F hf) ⟨g, hg, rfl⟩

omit [CompactSpace X] in
private theorem positiveAux_le (F : StrongDual ℝ C(X, ℝ)) {f : C(X, ℝ)}
    (hf : 0 ≤ f) {C : ℝ} (hC : ∀ g ∈ Set.Icc (0 : C(X, ℝ)) f, F g ≤ C) :
    positiveAux F f ≤ C := by
  apply csSup_le (coneImage_nonempty F hf)
  rintro y ⟨g, hg, rfl⟩
  exact hC g hg

private theorem positiveAux_nonneg (F : StrongDual ℝ C(X, ℝ)) {f : C(X, ℝ)} (hf : 0 ≤ f) :
    0 ≤ positiveAux F f := by
  simpa using apply_le_positiveAux F hf (show (0 : C(X, ℝ)) ∈ Set.Icc 0 f from ⟨le_rfl, hf⟩)

private theorem positiveAux_zero (F : StrongDual ℝ C(X, ℝ)) : positiveAux F 0 = 0 := by
  apply le_antisymm
  · apply positiveAux_le F le_rfl
    intro g hg
    have : g = 0 := le_antisymm hg.2 hg.1
    simp [this]
  · exact positiveAux_nonneg F le_rfl

omit [CompactSpace X] in
private theorem exists_riesz_split {f g h : C(X, ℝ)} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hh : 0 ≤ h) (hfg : h ≤ f + g) :
    ∃ a b : C(X, ℝ), 0 ≤ a ∧ a ≤ f ∧ 0 ≤ b ∧ b ≤ g ∧ h = a + b := by
  let a : C(X, ℝ) := h ⊓ f
  let b : C(X, ℝ) := h - a
  refine ⟨a, b, ?_, inf_le_right, cm_sub_nonneg inf_le_left, ?_, ?_⟩
  · exact le_inf hh hf
  · rw [ContinuousMap.le_def]
    intro x
    have hpoint := ContinuousMap.le_def.mp hfg x
    dsimp only [a, b]
    simp only [ContinuousMap.sub_apply, ContinuousMap.inf_apply]
    change h x ≤ f x + g x at hpoint
    rcases le_total (h x) (f x) with hle | hle
    · rw [min_eq_left hle]
      simpa using ContinuousMap.le_def.mp hg x
    · rw [min_eq_right hle]
      linarith
  · ext x
    simp only [b, ContinuousMap.add_apply, ContinuousMap.sub_apply]
    ring

private theorem positiveAux_add (F : StrongDual ℝ C(X, ℝ)) {f g : C(X, ℝ)}
    (hf : 0 ≤ f) (hg : 0 ≤ g) :
    positiveAux F (f + g) = positiveAux F f + positiveAux F g := by
  apply le_antisymm
  · apply positiveAux_le F (cm_add_nonneg hf hg)
    intro h hh
    obtain ⟨a, b, ha0, haf, hb0, hbg, rfl⟩ :=
      exists_riesz_split hf hg hh.1 hh.2
    rw [map_add]
    exact add_le_add (apply_le_positiveAux F hf ⟨ha0, haf⟩)
      (apply_le_positiveAux F hg ⟨hb0, hbg⟩)
  · apply le_iff_forall_pos_le_add.mpr
    intro ε hε
    obtain ⟨ya, ⟨a, ha, rfl⟩, hya⟩ := exists_lt_of_lt_csSup
      (coneImage_nonempty F hf) (sub_lt_self _ (half_pos hε))
    obtain ⟨yb, ⟨b, hb, rfl⟩, hyb⟩ := exists_lt_of_lt_csSup
      (coneImage_nonempty F hg) (sub_lt_self _ (half_pos hε))
    change positiveAux F f - ε / 2 < F a at hya
    change positiveAux F g - ε / 2 < F b at hyb
    have hab : F a + F b ≤ positiveAux F (f + g) := by
      rw [← map_add]
      apply apply_le_positiveAux F (cm_add_nonneg hf hg)
      exact ⟨cm_add_nonneg ha.1 hb.1, cm_add_le_add ha.2 hb.2⟩
    linarith

private theorem positiveAux_smul (F : StrongDual ℝ C(X, ℝ)) {f : C(X, ℝ)}
    (hf : 0 ≤ f) {c : ℝ} (hc : 0 ≤ c) :
    positiveAux F (c • f) = c * positiveAux F f := by
  rcases hc.eq_or_lt with rfl | hc
  · simp [positiveAux_zero]
  apply le_antisymm
  · apply positiveAux_le F (cm_smul_nonneg hc.le hf)
    intro h hh
    let a : C(X, ℝ) := c⁻¹ • h
    have ha : a ∈ Set.Icc (0 : C(X, ℝ)) f := by
      constructor
      · exact cm_smul_nonneg (inv_nonneg.mpr hc.le) hh.1
      · have hscaled := cm_smul_le_smul (inv_nonneg.mpr hc.le) hh.2
        simpa [a, smul_smul, hc.ne'] using hscaled
    have hha : h = c • a := by
      simp [a, smul_smul, hc.ne']
    rw [hha, map_smul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (apply_le_positiveAux F hf ha) hc.le
  · have hle : positiveAux F f ≤ c⁻¹ * positiveAux F (c • f) := by
      apply positiveAux_le F hf
      intro a ha
      have hca : c • a ∈ Set.Icc (0 : C(X, ℝ)) (c • f) :=
        ⟨cm_smul_nonneg hc.le ha.1, cm_smul_le_smul hc.le ha.2⟩
      have := apply_le_positiveAux F (cm_smul_nonneg hc.le hf) hca
      rw [map_smul, smul_eq_mul] at this
      calc
        F a ≤ positiveAux F (c • f) / c := (le_div_iff₀ hc).2 (by simpa [mul_comm] using this)
        _ = c⁻¹ * positiveAux F (c • f) := by field_simp
    calc
      c * positiveAux F f ≤ c * (c⁻¹ * positiveAux F (c • f)) :=
        mul_le_mul_of_nonneg_left hle hc.le
      _ = positiveAux F (c • f) := by field_simp

omit [CompactSpace X] in
private theorem cm_posPart_nonneg (f : C(X, ℝ)) : 0 ≤ f⁺ := by
  rw [ContinuousMap.le_def]
  intro x
  exact posPart_nonneg (f x)

omit [CompactSpace X] in
private theorem cm_negPart_nonneg (f : C(X, ℝ)) : 0 ≤ f⁻ := by
  rw [ContinuousMap.le_def]
  intro x
  exact negPart_nonneg (f x)

omit [CompactSpace X] in
private theorem cm_posPart_sub_negPart (f : C(X, ℝ)) : f⁺ - f⁻ = f := by
  ext x
  change (f x)⁺ - (f x)⁻ = f x
  exact posPart_sub_negPart (f x)

private theorem positiveAux_sub_eq (F : StrongDual ℝ C(X, ℝ))
    {a b c d : C(X, ℝ)} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h : a - b = c - d) :
    positiveAux F a - positiveAux F b = positiveAux F c - positiveAux F d := by
  have hadd : a + d = c + b := sub_eq_sub_iff_add_eq_add.mp h
  have haux := congrArg (positiveAux F) hadd
  rw [positiveAux_add F ha hd, positiveAux_add F hc hb] at haux
  linarith

private noncomputable def jordanPositiveLinearMap (F : StrongDual ℝ C(X, ℝ)) :
    C(X, ℝ) →ₗ[ℝ] ℝ where
  toFun f := positiveAux F f⁺ - positiveAux F f⁻
  map_add' f g := by
    have hdecomp : (f + g)⁺ - (f + g)⁻ =
        (f⁺ + g⁺) - (f⁻ + g⁻) := by
      calc
        (f + g)⁺ - (f + g)⁻ = f + g := cm_posPart_sub_negPart (f + g)
        _ = (f⁺ - f⁻) + (g⁺ - g⁻) := by
          rw [cm_posPart_sub_negPart f, cm_posPart_sub_negPart g]
        _ = (f⁺ + g⁺) - (f⁻ + g⁻) := by abel
    have hind := positiveAux_sub_eq F (cm_posPart_nonneg (f + g))
      (cm_negPart_nonneg (f + g)) (cm_add_nonneg (cm_posPart_nonneg f) (cm_posPart_nonneg g))
      (cm_add_nonneg (cm_negPart_nonneg f) (cm_negPart_nonneg g)) hdecomp
    rw [positiveAux_add F (cm_posPart_nonneg f) (cm_posPart_nonneg g),
      positiveAux_add F (cm_negPart_nonneg f) (cm_negPart_nonneg g)] at hind
    calc
      positiveAux F (f + g)⁺ - positiveAux F (f + g)⁻ =
          positiveAux F f⁺ + positiveAux F g⁺ -
            (positiveAux F f⁻ + positiveAux F g⁻) := hind
      _ = (positiveAux F f⁺ - positiveAux F f⁻) +
          (positiveAux F g⁺ - positiveAux F g⁻) := by ring
  map_smul' c f := by
    rcases le_total 0 c with hc | hc
    · have hdecomp : (c • f)⁺ - (c • f)⁻ = c • f⁺ - c • f⁻ := by
        calc
          (c • f)⁺ - (c • f)⁻ = c • f := cm_posPart_sub_negPart (c • f)
          _ = c • (f⁺ - f⁻) := by rw [cm_posPart_sub_negPart f]
          _ = c • f⁺ - c • f⁻ := by rw [smul_sub]
      have hind := positiveAux_sub_eq F (cm_posPart_nonneg (c • f))
        (cm_negPart_nonneg (c • f)) (cm_smul_nonneg hc (cm_posPart_nonneg f))
        (cm_smul_nonneg hc (cm_negPart_nonneg f)) hdecomp
      rw [positiveAux_smul F (cm_posPart_nonneg f) hc,
        positiveAux_smul F (cm_negPart_nonneg f) hc] at hind
      simpa [smul_eq_mul, mul_sub] using hind
    · have hc' : 0 ≤ -c := neg_nonneg.mpr hc
      have hdecomp : (c • f)⁺ - (c • f)⁻ =
          (-c) • f⁻ - (-c) • f⁺ := by
        calc
          (c • f)⁺ - (c • f)⁻ = c • f := cm_posPart_sub_negPart (c • f)
          _ = c • (f⁺ - f⁻) := by rw [cm_posPart_sub_negPart f]
          _ = (-c) • f⁻ - (-c) • f⁺ := by
            simp only [smul_sub]
            module
      have hind := positiveAux_sub_eq F (cm_posPart_nonneg (c • f))
        (cm_negPart_nonneg (c • f)) (cm_smul_nonneg hc' (cm_negPart_nonneg f))
        (cm_smul_nonneg hc' (cm_posPart_nonneg f)) hdecomp
      rw [positiveAux_smul F (cm_negPart_nonneg f) hc',
        positiveAux_smul F (cm_posPart_nonneg f) hc'] at hind
      calc
        positiveAux F (c • f)⁺ - positiveAux F (c • f)⁻ =
            (-c) * positiveAux F f⁻ - (-c) * positiveAux F f⁺ := hind
        _ = c * (positiveAux F f⁺ - positiveAux F f⁻) := by ring

private theorem jordanPositiveLinearMap_apply_of_nonneg (F : StrongDual ℝ C(X, ℝ))
    {f : C(X, ℝ)} (hf : 0 ≤ f) :
    jordanPositiveLinearMap F f = positiveAux F f := by
  have hdecomp : f⁺ - f⁻ = f - 0 := by
    rw [cm_posPart_sub_negPart f, sub_zero]
  have hind := positiveAux_sub_eq F (cm_posPart_nonneg f) (cm_negPart_nonneg f)
    hf le_rfl hdecomp
  rw [positiveAux_zero] at hind
  simpa [jordanPositiveLinearMap] using hind

private theorem jordanPositiveLinearMap_nonneg (F : StrongDual ℝ C(X, ℝ))
    {f : C(X, ℝ)} (hf : 0 ≤ f) :
    0 ≤ jordanPositiveLinearMap F f := by
  rw [jordanPositiveLinearMap_apply_of_nonneg F hf]
  exact positiveAux_nonneg F hf

private noncomputable def jordanPositiveLinear (F : StrongDual ℝ C(X, ℝ)) :
    C(X, ℝ) →ₚ[ℝ] ℝ :=
  { jordanPositiveLinearMap F with
    monotone' := by
      intro f g hfg
      rw [← sub_nonneg]
      change 0 ≤ jordanPositiveLinearMap F g - jordanPositiveLinearMap F f
      rw [← (jordanPositiveLinearMap F).map_sub]
      exact jordanPositiveLinearMap_nonneg F (cm_sub_nonneg hfg) }

private theorem positiveLinear_norm_bound (P : C(X, ℝ) →ₚ[ℝ] ℝ) (f : C(X, ℝ)) :
    ‖P f‖ ≤ P 1 * ‖f‖ := by
  have hP1 : 0 ≤ P 1 := P.map_nonneg (by
    rw [ContinuousMap.le_def]
    exact fun _ ↦ zero_le_one)
  have hupperFun : f ≤ ‖f‖ • (1 : C(X, ℝ)) := by
    rw [ContinuousMap.le_def]
    intro x
    simpa using ContinuousMap.apply_le_norm f x
  have hlowerFun : -(‖f‖ • (1 : C(X, ℝ))) ≤ f := by
    rw [ContinuousMap.le_def]
    intro x
    simpa using ContinuousMap.neg_norm_le_apply f x
  have hupper : P f ≤ P (‖f‖ • (1 : C(X, ℝ))) := P.monotone' hupperFun
  have hlower : P (-(‖f‖ • (1 : C(X, ℝ)))) ≤ P f := P.monotone' hlowerFun
  simp only [map_smul, smul_eq_mul] at hupper
  simp only [map_neg, map_smul, smul_eq_mul] at hlower
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · simpa [mul_comm] using hlower
  · simpa [mul_comm] using hupper

private noncomputable def positiveLinearToContinuous (P : C(X, ℝ) →ₚ[ℝ] ℝ) :
    C(X, ℝ) →P[ℝ] ℝ :=
  { toPositiveLinearMap := P
    cont := (P.toLinearMap.mkContinuous (P 1) (positiveLinear_norm_bound P)).cont }

private theorem norm_positiveLinearToContinuous (P : C(X, ℝ) →ₚ[ℝ] ℝ) :
    ‖(positiveLinearToContinuous P).toContinuousLinearMap‖ = P 1 := by
  apply le_antisymm
  · change ‖P.toLinearMap.mkContinuous (P 1) (positiveLinear_norm_bound P)‖ ≤ P 1
    exact LinearMap.mkContinuous_norm_le P.toLinearMap
      (P.map_nonneg (by rw [ContinuousMap.le_def]; exact fun _ ↦ zero_le_one))
      (positiveLinear_norm_bound P)
  · rcases isEmpty_or_nonempty X with hX | hX
    · let _ := hX
      have hfun : ∀ f : C(X, ℝ), f = 0 := by
        intro f
        ext x
        exact isEmptyElim x
      have hP1 : P 1 = 0 := by rw [hfun (1 : C(X, ℝ))]; exact map_zero P
      rw [hP1]
      exact ContinuousLinearMap.opNorm_nonneg _
    · let _ := hX
      have hle := (positiveLinearToContinuous P).toContinuousLinearMap.le_opNorm
        (1 : C(X, ℝ))
      have hP1 : 0 ≤ P 1 := P.map_nonneg (by
        rw [ContinuousMap.le_def]
        exact fun _ ↦ zero_le_one)
      calc
        P 1 = ‖P 1‖ := (Real.norm_of_nonneg hP1).symm
        _ = ‖(positiveLinearToContinuous P).toContinuousLinearMap 1‖ := rfl
        _ ≤ ‖(positiveLinearToContinuous P).toContinuousLinearMap‖ * ‖(1 : C(X, ℝ))‖ := hle
        _ = ‖(positiveLinearToContinuous P).toContinuousLinearMap‖ := by simp

private noncomputable def jordanNegativeLinearMap (F : StrongDual ℝ C(X, ℝ)) :
    C(X, ℝ) →ₗ[ℝ] ℝ :=
  jordanPositiveLinearMap F - F.toLinearMap

private theorem jordanNegativeLinearMap_nonneg (F : StrongDual ℝ C(X, ℝ))
    {f : C(X, ℝ)} (hf : 0 ≤ f) :
    0 ≤ jordanNegativeLinearMap F f := by
  rw [jordanNegativeLinearMap, LinearMap.sub_apply,
    jordanPositiveLinearMap_apply_of_nonneg F hf]
  exact sub_nonneg.mpr (apply_le_positiveAux F hf ⟨hf, le_rfl⟩)

private noncomputable def jordanNegativeLinear (F : StrongDual ℝ C(X, ℝ)) :
    C(X, ℝ) →ₚ[ℝ] ℝ :=
  { jordanNegativeLinearMap F with
    monotone' := by
      intro f g hfg
      rw [← sub_nonneg]
      change 0 ≤ jordanNegativeLinearMap F g - jordanNegativeLinearMap F f
      rw [← (jordanNegativeLinearMap F).map_sub]
      exact jordanNegativeLinearMap_nonneg F (cm_sub_nonneg hfg) }

private noncomputable def jordanPositiveContinuous (F : StrongDual ℝ C(X, ℝ)) :
    C(X, ℝ) →P[ℝ] ℝ :=
  positiveLinearToContinuous (jordanPositiveLinear F)

private noncomputable def jordanNegativeContinuous (F : StrongDual ℝ C(X, ℝ)) :
    C(X, ℝ) →P[ℝ] ℝ :=
  positiveLinearToContinuous (jordanNegativeLinear F)

private theorem jordan_sub_eq (F : StrongDual ℝ C(X, ℝ)) :
    (jordanPositiveContinuous F).toContinuousLinearMap -
      (jordanNegativeContinuous F).toContinuousLinearMap = F := by
  ext f
  change jordanPositiveLinearMap F f -
    (jordanPositiveLinearMap F f - F f) = F f
  ring

private theorem jordan_norm_pos (F : StrongDual ℝ C(X, ℝ)) :
    ‖(jordanPositiveContinuous F).toContinuousLinearMap‖ = jordanPositiveContinuous F 1 := by
  exact norm_positiveLinearToContinuous (jordanPositiveLinear F)

private theorem jordan_norm_neg (F : StrongDual ℝ C(X, ℝ)) :
    ‖(jordanNegativeContinuous F).toContinuousLinearMap‖ = jordanNegativeContinuous F 1 := by
  exact norm_positiveLinearToContinuous (jordanNegativeLinear F)

omit [CompactSpace X] in
private theorem cm_one_nonneg : (0 : C(X, ℝ)) ≤ 1 := by
  rw [ContinuousMap.le_def]
  exact fun _ ↦ zero_le_one

private theorem two_mul_positiveAux_one_sub_apply_le_norm (F : StrongDual ℝ C(X, ℝ)) :
    2 * positiveAux F 1 - F 1 ≤ ‖F‖ := by
  have haux : positiveAux F 1 ≤ (‖F‖ + F 1) / 2 := by
    apply positiveAux_le F cm_one_nonneg
    intro g hg
    let u : C(X, ℝ) := (2 : ℝ) • g - 1
    have huNorm : ‖u‖ ≤ 1 := by
      apply (ContinuousMap.norm_le u zero_le_one).2
      intro x
      rw [Real.norm_eq_abs, abs_le]
      have hg0 := ContinuousMap.le_def.mp hg.1 x
      have hg1 := ContinuousMap.le_def.mp hg.2 x
      have hg0' : 0 ≤ g x := by simpa using hg0
      have hg1' : g x ≤ 1 := by simpa using hg1
      dsimp only [u, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
        ContinuousMap.one_apply]
      change -1 ≤ 2 * g x - 1 ∧ 2 * g x - 1 ≤ 1
      constructor <;> linarith
    have hFu : F u ≤ ‖F‖ := by
      calc
        F u ≤ ‖F u‖ := Real.le_norm_self _
        _ ≤ ‖F‖ * ‖u‖ := F.le_opNorm u
        _ ≤ ‖F‖ * 1 := mul_le_mul_of_nonneg_left huNorm (norm_nonneg F)
        _ = ‖F‖ := mul_one _
    have huApply : F u = 2 * F g - F 1 := by
      rw [show u = (2 : ℝ) • g - 1 from rfl, map_sub, map_smul]
      rfl
    linarith
  linarith

private theorem jordan_norm_eq (F : StrongDual ℝ C(X, ℝ)) :
    ‖F‖ = jordanPositiveContinuous F 1 + jordanNegativeContinuous F 1 := by
  apply le_antisymm
  · calc
      ‖F‖ = ‖(jordanPositiveContinuous F).toContinuousLinearMap -
          (jordanNegativeContinuous F).toContinuousLinearMap‖ := by rw [jordan_sub_eq]
      _ ≤ ‖(jordanPositiveContinuous F).toContinuousLinearMap‖ +
          ‖(jordanNegativeContinuous F).toContinuousLinearMap‖ := by
        let P : C(X, ℝ) →L[ℝ] ℝ := (jordanPositiveContinuous F).toContinuousLinearMap
        let N : C(X, ℝ) →L[ℝ] ℝ := (jordanNegativeContinuous F).toContinuousLinearMap
        change ‖P - N‖ ≤ ‖P‖ + ‖N‖
        rw [sub_eq_add_neg]
        exact (norm_add_le P (-N)).trans_eq (by
          congr 1
          exact norm_neg N)
      _ = jordanPositiveContinuous F 1 + jordanNegativeContinuous F 1 := by
        rw [jordan_norm_pos, jordan_norm_neg]
  · change jordanPositiveLinearMap F 1 + jordanNegativeLinearMap F 1 ≤ ‖F‖
    rw [jordanNegativeLinearMap, LinearMap.sub_apply,
      jordanPositiveLinearMap_apply_of_nonneg F cm_one_nonneg]
    calc
      positiveAux F 1 + (positiveAux F 1 - F 1) =
          2 * positiveAux F 1 - F 1 := by ring
      _ ≤ ‖F‖ := two_mul_positiveAux_one_sub_apply_le_norm F

/-- **Positive and negative decomposition of a real continuous-function dual.** Let `X` be a
compact topological space, with no separation or nonempty-space assumption, and `F ∈
C(X,ℝ)*` a bounded real-linear functional. `RealDualJordan F` contains positive bounded
real-linear parts `F⁺,F⁻` with `F=F⁺-F⁻`, `‖F‖=F⁺(1)+F⁻(1)`, `‖F⁺‖=F⁺(1)` and
`‖F⁻‖=F⁻(1)`. -/
structure RealDualJordan (F : StrongDual ℝ C(X, ℝ)) where
  /-- **Positive Jordan functional.** Let `X` be a compact topological space, with no
  separation or nonempty-space assumption, and `F ∈ C(X,ℝ)*` a bounded real-linear
  functional. the positive part `F⁺ : C(X,ℝ) → ℝ` is bounded and real-linear, and
  nonnegative on nonnegative continuous functions. -/
  pos : C(X, ℝ) →P[ℝ] ℝ
  /-- **Negative Jordan functional.** Let `X` be a compact topological space, with no
  separation or nonempty-space assumption, and `F ∈ C(X,ℝ)*` a bounded real-linear
  functional. the part `F⁻ : C(X,ℝ) → ℝ` is bounded, real-linear and positive, with
  `F=F⁺-F⁻`. -/
  neg : C(X, ℝ) →P[ℝ] ℝ
  /-- **Difference equation of the Jordan functional parts.** Let `X` be a compact topological
  space, with no separation or nonempty-space assumption, and `F ∈ C(X,ℝ)*` a bounded
  real-linear functional. the bounded positive parts satisfy `F⁺-F⁻=F` as continuous
  real-linear maps. -/
  sub_eq : pos.toContinuousLinearMap - neg.toContinuousLinearMap = F
  /-- **Jordan masses add to the dual norm.** Let `X` be a compact topological space, with no
  separation or nonempty-space assumption, and `F ∈ C(X,ℝ)*` a bounded real-linear
  functional. the decomposition satisfies `‖F‖=F⁺(1)+F⁻(1)`. -/
  norm_eq : ‖F‖ = pos 1 + neg 1
  /-- **Norm of the positive Jordan part.** Let `X` be a compact topological space, with no
  separation or nonempty-space assumption, and `F ∈ C(X,ℝ)*` a bounded real-linear
  functional. `‖F⁺‖=F⁺(1)` for the bounded positive part. -/
  norm_pos : ‖pos.toContinuousLinearMap‖ = pos 1
  /-- **Norm of the negative Jordan part.** Let `X` be a compact topological space, with no
  separation or nonempty-space assumption, and `F ∈ C(X,ℝ)*` a bounded real-linear
  functional. `‖F⁻‖=F⁻(1)` for the bounded positive part of `-F`. -/
  norm_neg : ‖neg.toContinuousLinearMap‖ = neg 1

/-- **Construction of positive and negative Jordan parts.** Let `X` be a compact topological
space, with no separation or nonempty-space assumption, and `F ∈ C(X,ℝ)*` a bounded
real-linear functional. `realDualJordan F` gives the lattice positive part `F⁺` and the
positive part `F⁻` of `-F`, with their difference and exact norm-mass identities. -/
noncomputable def realDualJordan (F : StrongDual ℝ C(X, ℝ)) : RealDualJordan F where
  pos := jordanPositiveContinuous F
  neg := jordanNegativeContinuous F
  sub_eq := jordan_sub_eq F
  norm_eq := jordan_norm_eq F
  norm_pos := jordan_norm_pos F
  norm_neg := jordan_norm_neg F

end

end MathlibExt.Analysis.FunctionalAnalysis
