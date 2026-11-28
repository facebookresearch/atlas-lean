/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portion of this file adapted from `LeanEval/KnotTheory/Linking.lean`
(leanprover/lean-eval at commit 38361be884302c7edce1908c4aef8296eb2cb27e).
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Benchmark submitter: Kim Morrison.

The theorem statement is retained; the proof and the concrete links are new.
-/

module

public import MathlibExt.Topology.ConwayKnotShared
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Homotopy.Lifting

/-!
# Non-isotopic oriented two-component links

The unlink and the Hopf link are oriented smooth links in `ℝ³` with ordered components.
Here both first components are the same unit circle in the `xy`-plane. The second component
of the unlink extends to a disk in its complement. In contrast, the second component of the
Hopf link projects to a loop with one turn around the origin under the map from the complement
to the punctured complex plane given by radial displacement from the unit cylinder and height.
Lifting through the complex exponential detects this obstruction even after an
orientation-preserving reparametrization.

## References

* Kim Morrison (benchmark submitter), *Existence of a non-isotopic pair of oriented
  two-component links*, lean-eval, problem `exists_nonisotopic_link`, revision 1.
* *Linking number*, <https://en.wikipedia.org/wiki/Linking_number>, for the classical example.
  The proof below uses a covering-space obstruction rather than the Gauss linking integral.
* Allen Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §1.3,
  Propositions 1.33 and 1.34, pp. 61–62, for existence and uniqueness of lifts.
-/

namespace MathlibExt.Topology.LinkingWanted.KnotTheory

open MathlibExt.Topology.ConwayKnotShared.KnotTheory
open Set

private theorem eq_of_cos_sin_eq {s t : ℝ} (hs : s ∈ Ico 0 (2 * Real.pi))
    (ht : t ∈ Ico 0 (2 * Real.pi)) (hc : Real.cos s = Real.cos t)
    (hi : Real.sin s = Real.sin t) : s = t := by
  apply injOn_circleMap_of_abs_sub_le' (c := 0) (R := 1) one_ne_zero
    (by rw [sub_zero]) hs ht
  exact Complex.ext (by simpa only [circleMap_zero_re, one_mul] using hc)
    (by simpa only [circleMap_zero_im, one_mul] using hi)

private noncomputable def equator : Knot where
  curve t := !₂[Real.cos t, Real.sin t, 0]
  smooth := (contDiff_piLp 2).2 fun i => by
    fin_cases i
    · exact Real.contDiff_cos
    · exact Real.contDiff_sin
    · exact contDiff_const
  periodic t := by simp [Real.cos_add_two_pi, Real.sin_add_two_pi]
  injOn := by
    intro s hs t ht h
    exact eq_of_cos_sin_eq hs ht
      (congrArg (fun p : R3 => p 0) h) (congrArg (fun p : R3 => p 1) h)
  immersion t := by
    have h : HasDerivAt (fun s : ℝ => ![Real.cos s, Real.sin s, 0])
        ![-Real.sin t, Real.cos t, 0] t := by
      refine hasDerivAt_pi.2 fun i => ?_
      fin_cases i
      · exact Real.hasDerivAt_cos t
      · exact Real.hasDerivAt_sin t
      · exact hasDerivAt_const t 0
    let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
    have h' := (e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t h).deriv
    change deriv (e.toContinuousLinearMap ∘ (fun s : ℝ => ![Real.cos s, Real.sin s, 0])) t ≠ 0
    rw [h']
    intro hz
    have hs : -Real.sin t = 0 := congrArg (fun p : R3 => p 0) hz
    have hc : Real.cos t = 0 := congrArg (fun p : R3 => p 1) hz
    nlinarith [Real.sin_sq_add_cos_sq t]

private noncomputable def meridian (c : ℝ) : Knot where
  curve t := !₂[c + Real.cos t / 2, 0, Real.sin t / 2]
  smooth := (contDiff_piLp 2).2 fun i => by
    fin_cases i
    · change ContDiff ℝ _ (fun t => c + Real.cos t / 2)
      fun_prop
    · exact contDiff_const
    · change ContDiff ℝ _ (fun t => Real.sin t / 2)
      fun_prop
  periodic t := by simp [Real.cos_add_two_pi, Real.sin_add_two_pi]
  injOn := by
    intro s hs t ht h
    have hx : c + Real.cos s / 2 = c + Real.cos t / 2 := congrArg (fun p : R3 => p 0) h
    have hz : Real.sin s / 2 = Real.sin t / 2 := congrArg (fun p : R3 => p 2) h
    exact eq_of_cos_sin_eq hs ht (by linarith) (by linarith)
  immersion t := by
    have h : HasDerivAt (fun s : ℝ => ![c + Real.cos s / 2, 0, Real.sin s / 2])
        ![-Real.sin t / 2, 0, Real.cos t / 2] t := by
      refine hasDerivAt_pi.2 fun i => ?_
      fin_cases i
      · exact ((Real.hasDerivAt_cos t).div_const 2).const_add c
      · exact hasDerivAt_const t 0
      · exact (Real.hasDerivAt_sin t).div_const 2
    let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
    have h' := (e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t h).deriv
    change deriv (e.toContinuousLinearMap ∘
      (fun s : ℝ => ![c + Real.cos s / 2, 0, Real.sin s / 2])) t ≠ 0
    rw [h']
    intro hz
    have hs : -Real.sin t / 2 = 0 := congrArg (fun p : R3 => p 0) hz
    have hc : Real.cos t / 2 = 0 := congrArg (fun p : R3 => p 2) hz
    have : Real.sin t = 0 := by linarith
    have : Real.cos t = 0 := by linarith
    nlinarith [Real.sin_sq_add_cos_sq t]

-- The factor of two normalizes the radius of the meridian in the Hopf link.
private noncomputable def complementCoord (p : R3) : ℂ :=
  ⟨2 * (‖(⟨p 0, p 1⟩ : ℂ)‖ - 1), 2 * p 2⟩

private theorem complementCoord_eq_zero_iff (p : R3) :
    complementCoord p = 0 ↔ p ∈ range equator.curve := by
  constructor
  · intro h
    let w : ℂ := ⟨p 0, p 1⟩
    have hr : 2 * (‖w‖ - 1) = 0 := congrArg Complex.re h
    have hz : 2 * p 2 = 0 := congrArg Complex.im h
    have hw : ‖w‖ = 1 := by linarith
    have harg : circleMap 0 1 w.arg = w := hw ▸ circleMap_zero_norm_arg w
    refine ⟨w.arg, ?_⟩
    ext i
    fin_cases i
    · change Real.cos w.arg = w.re
      simpa only [circleMap_zero_re, one_mul] using congrArg Complex.re harg
    · change Real.sin w.arg = w.im
      simpa only [circleMap_zero_im, one_mul] using congrArg Complex.im harg
    · change 0 = p 2
      linarith
  · rintro ⟨t, rfl⟩
    have hxy : (⟨Real.cos t, Real.sin t⟩ : ℂ) = circleMap 0 1 t := by
      apply Complex.ext <;> simp [circleMap_zero_re, circleMap_zero_im]
    change Complex.mk (2 * (‖(⟨Real.cos t, Real.sin t⟩ : ℂ)‖ - 1)) (2 * 0) = 0
    rw [hxy]
    apply Complex.ext <;> simp

private theorem complementCoord_xz (x z : ℝ) (hx : 0 ≤ x) :
    complementCoord !₂[x, 0, z] = ⟨2 * (x - 1), 2 * z⟩ := by
  change Complex.mk (2 * (‖(x : ℂ)‖ - 1)) (2 * z) = _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]

private theorem complementCoord_meridian (t : ℝ) :
    complementCoord ((meridian 1).curve t) = circleMap 0 1 t := by
  change complementCoord !₂[1 + Real.cos t / 2, 0, Real.sin t / 2] = _
  rw [complementCoord_xz _ _ (by linarith [Real.neg_one_le_cos t])]
  apply Complex.ext <;> simp only [circleMap_zero_re, circleMap_zero_im, one_mul] <;> linarith

/-- An oriented two-component unlink: the unit circle in the `xy`-plane and the radius-`1/2`
circle in the `xz`-plane centered at `(3, 0, 0)`, in that order. -/
public noncomputable def unlink : TwoLink where
  K := equator
  L := meridian 3
  disjoint := disjoint_left.2 <| by
    rintro _ ⟨s, rfl⟩ ⟨t, h⟩
    have hx : 3 + Real.cos t / 2 = Real.cos s := congrArg (fun p : R3 => p 0) h
    linarith [Real.cos_le_one s, Real.neg_one_le_cos t]

/-- The oriented Hopf link with the unit circle in the `xy`-plane first and the radius-`1/2`
circle in the `xz`-plane centered at `(1, 0, 0)` second. -/
public noncomputable def hopfLink : TwoLink where
  K := equator
  L := meridian 1
  disjoint := disjoint_left.2 <| by
    rintro _ h ⟨t, rfl⟩
    have hz := (complementCoord_eq_zero_iff _).2 h
    rw [complementCoord_meridian] at hz
    exact circleMap_ne_center one_ne_zero hz

/-- The two parametrizations of `unlink`, with angles in radians. -/
public theorem unlink_curves (t : ℝ) :
    (unlink.K.curve t, unlink.L.curve t) =
      (!₂[Real.cos t, Real.sin t, 0], !₂[3 + Real.cos t / 2, 0, Real.sin t / 2]) := by
  unfold unlink
  rfl

/-- The two parametrizations of `hopfLink`, with angles in radians. -/
public theorem hopfLink_curves (t : ℝ) :
    (hopfLink.K.curve t, hopfLink.L.curve t) =
      (!₂[Real.cos t, Real.sin t, 0], !₂[1 + Real.cos t / 2, 0, Real.sin t / 2]) := by
  unfold hopfLink
  rfl

-- Extend the second component of the unlink to the whole plane, while keeping x > 1.
private noncomputable def unlinkExtension (w : ℂ) : R3 := !₂[3 + max (-1) w.re / 2, 0, w.im / 2]

private theorem unlinkExtension_notMem (w : ℂ) : unlinkExtension w ∉ range equator.curve := by
  rintro ⟨t, h⟩
  have hx : Real.cos t = 3 + max (-1) w.re / 2 := congrArg (fun p : R3 => p 0) h
  linarith [Real.cos_le_one t, le_max_left (-1 : ℝ) w.re]

private theorem unlinkExtension_circleMap (t : ℝ) :
    unlinkExtension (circleMap 0 1 t) = unlink.L.curve t := by
  change !₂[3 + max (-1) (circleMap 0 1 t).re / 2, 0, (circleMap 0 1 t).im / 2] = _
  simp [circleMap_zero_re, circleMap_zero_im, max_eq_right (Real.neg_one_le_cos t), unlink,
    meridian]

private theorem unlink_not_isotopic_hopfLink : ¬ unlink.Isotopic hopfLink := by
  intro h
  obtain ⟨Φ, σ, τ, hK, hL⟩ := TwoLink.isotopic_iff.mp h
  have hΦ (w : ℂ) : Φ.H 1 (unlinkExtension w) ∉ range equator.curve := by
    rintro ⟨t, ht⟩
    apply unlinkExtension_notMem w
    refine ⟨σ.finv t, Function.LeftInverse.injective (Φ.inv_left 1) ?_⟩
    have hs := hK (σ.finv t)
    rw [σ.right_inv] at hs
    exact hs.trans ht
  have hc : Continuous (Φ.H 1) :=
    Φ.smooth.continuous.comp
      (show Continuous (fun x : R3 => ((1 : ℝ), x)) by fun_prop)
  have hd : Continuous unlinkExtension := by
    unfold unlinkExtension
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun w : ℂ => 3 + max (-1) w.re / 2)
      fun_prop
    · exact continuous_const
    · change Continuous (fun w : ℂ => w.im / 2)
      fun_prop
  have he : Continuous complementCoord := by
    have hmk : Continuous (fun q : ℝ × ℝ => Complex.mk q.1 q.2) :=
      Complex.equivRealProdCLM.symm.continuous
    have hproj (i : Fin 3) : Continuous (fun p : R3 => p i) :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).continuous
    have hxy : Continuous (fun p : R3 => (⟨p 0, p 1⟩ : ℂ)) :=
      hmk.comp ((hproj 0).prodMk (hproj 1))
    exact hmk.comp ((continuous_const.mul (hxy.norm.sub continuous_const)).prodMk
      (continuous_const.mul (hproj 2)))
  let F : C(ℂ, {z : ℂ // z ≠ 0}) :=
    ⟨fun w => ⟨complementCoord (Φ.H 1 (unlinkExtension w)), fun hz =>
      hΦ w ((complementCoord_eq_zero_iff _).1 hz)⟩, (he.comp (hc.comp hd)).subtype_mk _⟩
  let angle : ℝ → ℂ := fun t => (τ.f t : ℂ) * Complex.I
  have hF (t : ℝ) : (F (circleMap 0 1 t) : ℂ) = Complex.exp (angle t) := by
    change complementCoord (Φ.H 1 (unlinkExtension (circleMap 0 1 t))) = _
    rw [unlinkExtension_circleMap, hL]
    simpa [angle, circleMap_zero, hopfLink] using complementCoord_meridian (τ.f t)
  obtain ⟨G, ⟨hG₀, hG⟩, -⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts
    F (circleMap 0 1 0) (angle 0) (Subtype.ext (hF 0).symm)
  have hg : Continuous (fun t : ℝ => G (circleMap 0 1 t)) := by
    apply G.continuous.comp
    unfold circleMap
    fun_prop
  have ha : Continuous angle := by
    dsimp [angle]
    have := τ.smooth.continuous
    fun_prop
  have heq : EqOn (fun t : ℝ => G (circleMap 0 1 t)) angle univ :=
    Complex.isCoveringMap_exp.eqOn_of_comp_eqOn isPreconnected_univ hg.continuousOn
      ha.continuousOn (fun t _ => Subtype.ext <|
        (congrArg Subtype.val (congrFun hG (circleMap 0 1 t))).trans (hF t)) (mem_univ 0) hG₀
  have he : angle (0 + 2 * Real.pi) = angle 0 := by
    rw [← heq (mem_univ (0 + 2 * Real.pi)), ← heq (mem_univ (0 : ℝ))]
    exact congrArg (fun z => G z) (periodic_circleMap 0 1 0)
  have hτ : τ.f (0 + 2 * Real.pi) = τ.f 0 := by simpa [angle] using congrArg Complex.im he
  linarith [τ.periodic 0, Real.pi_pos]

/-- **Non-isotopic two-component links exist.** There exist two oriented smooth two-component
links $L_1$ and $L_2$ in $\mathbb{R}^3$ that are not ambient isotopic as oriented links with
ordered components: no ambient isotopy of $\mathbb{R}^3$ carries the first component of $L_1$ to
the first component of $L_2$ and the second component of $L_1$ to the second component of $L_2$,
each up to an orientation-preserving reparametrization of the circle.

Source: Classical; see https://en.wikipedia.org/wiki/Linking_number. Via
leanprover/lean-eval@38361be, problem `exists_nonisotopic_link`. -/
public theorem exists_nonisotopic_link : ∃ L₁ L₂ : TwoLink, ¬ L₁.Isotopic L₂ :=
  ⟨unlink, hopfLink, unlink_not_isotopic_hopfLink⟩

end MathlibExt.Topology.LinkingWanted.KnotTheory
