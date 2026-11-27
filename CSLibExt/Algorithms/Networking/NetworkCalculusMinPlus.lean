/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Networking.NetworkCalculus
public import Mathlib.Data.EReal.Operations
public import Mathlib.Order.Hom.Basic

/-!
# Min-plus operators on extended network-calculus curves

Le Boudec and Thiran, *Network Calculus* (2022 online edition), §3.1.3, p. 105,
take continuous-time curves to be left-continuous. Here time is real but no
continuity is required. In particular a curve can jump from zero to infinity
at the origin. Definition 3.1.10, (3.7), p. 111 gives the convolution, including
its zero value before time zero. Definition 3.1.13, (3.15), p. 122 gives the
deconvolution. We take the signed difference only at times for which no shift
requires subtracting two infinities.

The order bounds, the endpoint formula, the finite-clock comparison and the
nonclosure witness below are deductions; none uses attainment of an extremum.
-/

@[expose] public section

namespace Cslib.Algorithms.Networking.NetworkCalculus

open scoped NNReal ENNReal

/-- A nondecreasing map from real times to extended nonnegative reals that
vanishes at every strictly negative time. Neither continuity nor a zero value
at the origin is required. -/
structure ExtendedCurve where
  /-- The nondecreasing map `ℝ →o ℝ≥0∞` of a network-calculus curve. It vanishes
  before time zero but need not vanish at zero. -/
  toOrderHom : ℝ →o ℝ≥0∞
  /-- For a network-calculus curve `f : ℝ →o ℝ≥0∞`, the value `f t` is zero at
  every `t < 0`. This condition does not constrain `f 0` to be zero. -/
  zero_of_neg : ∀ {t : ℝ}, t < 0 → toOrderHom t = 0

namespace ExtendedCurve

instance : FunLike ExtendedCurve ℝ ℝ≥0∞ where
  coe f := f.toOrderHom
  coe_injective := by
    rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    congr
    exact DFunLike.coe_injective h

instance : OrderHomClass ExtendedCurve ℝ ℝ≥0∞ where
  map_rel f _ _ h := f.toOrderHom.monotone h

/-- Extend a monotone finite clock `f : ℝ≥0 → ℝ≥0` to a real-time curve:
coerce its values to `ℝ≥0∞` on nonnegative times and use zero before time zero. -/
noncomputable def ofNNReal (f : ℝ≥0 → ℝ≥0) (hf : Monotone f) : ExtendedCurve where
  toOrderHom := {
    toFun := fun t => if ht : 0 ≤ t then (f ⟨t, ht⟩ : ℝ≥0∞) else 0
    monotone' := by
      intro a b hab
      by_cases ha : 0 ≤ a
      · simp only [dite_eq_left ha, dite_eq_left (ha.trans hab)]
        exact ENNReal.coe_le_coe.mpr (hf (show (⟨a, ha⟩ : ℝ≥0) ≤ ⟨b, ha.trans hab⟩ from hab))
      · simp only [dite_eq_right ha]
        exact zero_le }
  zero_of_neg ht := dite_eq_right ht.not_ge

/-- At a nonnegative real time the zero extension of a monotone finite clock
returns its original value, coerced from `ℝ≥0` to `ℝ≥0∞`. -/
@[simp] theorem ofNNReal_apply (f : ℝ≥0 → ℝ≥0) (hf : Monotone f) (t : ℝ≥0) :
    ofNNReal f hf t = (f t : ℝ≥0∞) := dite_eq_left t.2

private theorem splitInf_mono {f g : ExtendedCurve} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (⨅ r : Set.Icc 0 a, f (a - r) + g r) ≤ ⨅ s : Set.Icc 0 b, f (b - s) + g s := by
  apply le_iInf
  intro s
  -- Shorten a split of the longer interval until it fits in the shorter one.
  let r : Set.Icc 0 a := ⟨min (s : ℝ) a, le_min s.2.1 ha, min_le_right ..⟩
  refine (iInf_le (fun v : Set.Icc 0 a => f (a - v) + g v) r).trans (add_le_add ?_ ?_)
  · apply f.toOrderHom.monotone
    change a - min (s : ℝ) a ≤ b - s
    rcases le_total (s : ℝ) a with h | h
    · rw [min_eq_left h]
      exact sub_le_sub_right hab _
    · rw [min_eq_right h, sub_self]
      exact sub_nonneg.mpr s.2.2
  · exact g.toOrderHom.monotone (min_le_left ..)

/-- Min-plus convolution of two extended curves. At real time `t ≥ 0` it is
the infimum in `ℝ≥0∞` of `f (t - s) + g s` over `0 ≤ s ≤ t`; at `t < 0` it
is zero. The result is again nondecreasing. -/
noncomputable def conv (f g : ExtendedCurve) : ExtendedCurve where
  toOrderHom := {
    toFun := fun t => if t < 0 then 0 else ⨅ s : Set.Icc 0 t, f (t - s) + g s
    monotone' := by
      intro a b hab
      by_cases ha : a < 0
      · simp only [ite_eq_left ha]
        exact zero_le
      · simp only [ite_eq_right ha, ite_eq_right (not_lt.mpr ((le_of_not_gt ha).trans hab))]
        exact splitInf_mono (le_of_not_gt ha) hab }
  zero_of_neg ht := ite_eq_left ht

/-- At nonnegative real time `t`, the convolution of extended curves is the
infimum in `ℝ≥0∞` of `f (t - s) + g s` over the closed interval `0 ≤ s ≤ t`. -/
theorem conv_apply_of_nonneg (f g : ExtendedCurve) {t : ℝ} (ht : 0 ≤ t) :
    f.conv g t = ⨅ s : Set.Icc 0 t, f (t - s) + g s := ite_eq_right ht.not_gt

/-- For extended curves, every split `0 ≤ s ≤ t` bounds their convolution
at `t` from above by `f (t - s) + g s`. -/
theorem conv_le (f g : ExtendedCurve) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    f.conv g t ≤ f (t - s) + g s := by
  rw [conv_apply_of_nonneg f g (hs.trans hst)]
  exact iInf_le _ (⟨s, hs, hst⟩ : Set.Icc 0 t)

/-- At any real `t ≥ 0`, an extended nonnegative real bounds the convolution
of extended curves `f, g` from below exactly when it is at most
`f (t - s) + g s` for every real split `0 ≤ s ≤ t`. -/
theorem le_conv_iff (f g : ExtendedCurve) {t : ℝ} (ht : 0 ≤ t) {c : ℝ≥0∞} :
    c ≤ f.conv g t ↔ ∀ s ∈ Set.Icc 0 t, c ≤ f (t - s) + g s := by
  rw [conv_apply_of_nonneg f g ht, le_iInf_iff]
  exact Subtype.forall

/-- At time zero, convolution gives the sum in `ℝ≥0∞` of the two endpoint
values. These values need not be zero or finite. -/
@[simp] theorem conv_zero (f g : ExtendedCurve) : f.conv g 0 = f 0 + g 0 := by
  apply le_antisymm
  · simpa using conv_le f g (s := 0) le_rfl le_rfl
  · apply (le_conv_iff f g le_rfl).2
    intro s hs
    rw [le_antisymm hs.2 hs.1, sub_self]

/-- On monotone finite clocks `f g : ℝ≥0 → ℝ≥0` at any nonnegative time,
convolution of their zero extensions agrees in `ℝ≥0∞` with `minPlusConv f g`.
No endpoint normalization is needed. -/
theorem conv_ofNNReal (f g : ℝ≥0 → ℝ≥0) (hf : Monotone f) (hg : Monotone g) (t : ℝ≥0) :
    (ofNNReal f hf).conv (ofNNReal g hg) t = minPlusConv f g t := by
  have term (u : ℝ≥0) (hu : u ≤ t) :
      ofNNReal f hf ((t : ℝ) - (u : ℝ)) + ofNNReal g hg u = (↑(f (t - u) + g u) : ℝ≥0∞) := by
    rw [← NNReal.coe_sub hu, ofNNReal_apply, ofNNReal_apply, ENNReal.coe_add]
  apply le_antisymm
  · apply le_iInf
    intro s
    exact (conv_le _ _ s.val.2 (show (s.val : ℝ) ≤ t from s.property)).trans_eq (term s s.property)
  · apply (le_conv_iff _ _ t.2).2
    intro s hs
    let u : ℝ≥0 := ⟨s, hs.1⟩
    have hu : u ≤ t := hs.2
    exact (minPlusConv_le hu).trans_eq (term u hu).symm

/-- Real times `t` at which signed deconvolution of `f` by `g` is defined:
for every nonnegative shift `u`, `f (t + u)` and `g u` are not both infinite.
Either value alone may be infinite. -/
def deconvDomain (f g : ExtendedCurve) : Set ℝ :=
  {t | ∀ u : ℝ≥0, ¬ (f (t + u) = ⊤ ∧ g u = ⊤)}

/-- At an admissible real time `t`, the signed min-plus deconvolution of
extended curves `f` by `g` is the supremum in `EReal` of `f (t + u) - g u`
over nonnegative shifts. No shift may make both operands infinite. Both operands are
embedded in `EReal` before subtraction: for the zero curve deconvolved by
a curve equal to one from time zero onwards, the value is `-1` at every time. -/
noncomputable def deconv (f g : ExtendedCurve) (t : f.deconvDomain g) : EReal :=
  ⨆ u : ℝ≥0, (f (t.val + u) : EReal) - (g u : EReal)

/-- Let `t` be a real time at which the extended curves `f, g` never have
both `f (t + u)` and `g u` infinite for `u ≥ 0`. For each such shift the signed
difference `f (t + u) - g u` lies below their deconvolution at `t` in `EReal`. -/
theorem le_deconv (f g : ExtendedCurve) (t : f.deconvDomain g) (u : ℝ≥0) :
    (f (t.val + u) : EReal) - (g u : EReal) ≤ f.deconv g t :=
  le_iSup (fun v : ℝ≥0 => (f (t.val + v) : EReal) - (g v : EReal)) u

/-- Let `t` be a real time at which no nonnegative shift makes both
`f (t + u)` and `g u` infinite. A value `c : EReal` bounds the deconvolution
from above at `t` exactly when `f (t + u) - g u ≤ c` for every `u ≥ 0`,
with signed extended-real subtraction. -/
theorem deconv_le_iff (f g : ExtendedCurve) (t : f.deconvDomain g) {c : EReal} :
    f.deconv g t ≤ c ↔ ∀ u : ℝ≥0, (f (t.val + u) : EReal) - (g u : EReal) ≤ c :=
  iSup_le_iff

/-- Some extended curves have strictly positive deconvolution at an admissible
strictly negative time. For example, take `f` equal to one from zero onwards
and zero before zero, and `g` identically zero. At `t = -1` the shift `u = 1`
already gives a strictly positive lower bound. -/
theorem exists_pos_deconv_at_neg : ∃ (f g : ExtendedCurve) (t : f.deconvDomain g),
    t.val < 0 ∧ 0 < f.deconv g t := by
  let f := ofNNReal (fun _ => 1) monotone_const
  let g := ofNNReal (fun _ => 0) monotone_const
  have ht : -1 ∈ f.deconvDomain g := fun u => by simp [g]
  refine ⟨f, g, ⟨-1, ht⟩, by norm_num, lt_of_lt_of_le ?_ (le_deconv _ _ _ 1)⟩
  change (0 : EReal) < (f (-1 + (1 : ℝ≥0)) : EReal) - (g (1 : ℝ≥0) : EReal)
  rw [show (-1 : ℝ) + (1 : ℝ≥0) = ↑(0 : ℝ≥0) by norm_num]
  rw [ofNNReal_apply, ofNNReal_apply]
  norm_num

end ExtendedCurve

end Cslib.Algorithms.Networking.NetworkCalculus
