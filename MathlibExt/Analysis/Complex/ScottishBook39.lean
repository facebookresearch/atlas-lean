/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Topology.Instances.Complex
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.SetTheory.Cardinal.Rat
import Mathlib.Topology.Instances.Rat
import Mathlib.Tactic.NormNum

/-! # A discontinuous multiplicative modulus on `ℂ`

Transposing two elements of a real transcendence basis extends to an automorphism of `ℂ`.
Their absolute values are different, whereas any continuous modulus obtained by composing a
field automorphism with the norm must agree with the usual norm on the real axis.
-/

public section

open Function Set Cardinal MvPolynomial
open scoped Cardinal

namespace MathlibExt.Analysis.Complex.ScottishBook39Wanted

private theorem equiv_basis_apply {ι : Type*} (b : ι → ℂ) (hb : IsTranscendenceBasis ℚ b)
    (e : ι ≃ ι) (i : ι) : IsAlgClosed.equivOfTranscendenceBasis b b e hb hb (b i) = b (e i) := by
  let x := hb.1.aevalEquiv (X i)
  have hx : algebraMap (Algebra.adjoin ℚ (range b)) ℂ x = b i := by
    simp only [x, hb.1.algebraMap_aevalEquiv, aeval_X]
  conv_lhs => rw [← hx]
  simp only [IsAlgClosed.equivOfTranscendenceBasis, IsAlgClosure.equivOfEquiv_algebraMap]
  change algebraMap (Algebra.adjoin ℚ (range b)) ℂ
    (hb.1.aevalEquiv (rename e (hb.1.aevalEquiv.symm x))) = b (e i)
  simp only [x, AlgEquiv.symm_apply_apply, rename_X, hb.1.algebraMap_aevalEquiv, aeval_X]

/-- **Discontinuous subadditive multiplicative functions on $\mathbb{C}$.** There is a function
$\varphi : \mathbb{C} \to \mathbb{R}$ that is not continuous, satisfies $\varphi(x) \ge 0$ for
all $x \in \mathbb{C}$, is not identically $0$, satisfies $\varphi(x) \ne 1$ for some
$x \ne 0$, and satisfies $\varphi(x + y) \le \varphi(x) + \varphi(y)$ and
$\varphi(xy) = \varphi(x)\varphi(y)$ for all $x, y \in \mathbb{C}$.

This answers Problem 39 of the Scottish Book (Auerbach), which notes that the continuous
functions with these properties are exactly $\varphi(x) = |x|^\alpha$ with $0 < \alpha \le 1$ and
asks whether discontinuous ones exist. The source's condition that $\varphi$ is not identically
$1$ is read, as in Mazur's addendum, as excluding the trivial absolute value ($\varphi(0) = 0$
and $\varphi(x) = 1$ for $x \ne 0$), which is discontinuous at $0$ and has the other properties.
Mazur's answer is $\varphi(x) = |f(x)|$ for a discontinuous field automorphism $f$ of
$\mathbb{C}$; it satisfies $\varphi(2) = 2$.

Source: H. Auerbach, Problem 39 of the Scottish Book; addendum of S. Mazur,
10 April 1937, in the Scottish Book, via Lebesgue's theorem on the existence
of a discontinuous automorphism of `ℂ` (Kamke); see the commentary in
R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem exists_discontinuous_subadditive_multiplicative :
    ∃ φ : ℂ → ℝ, ¬ Continuous φ ∧ (∀ x, 0 ≤ φ x) ∧
      ¬ (∀ x, φ x = 0) ∧ ¬ (∀ x, x ≠ 0 → φ x = 1) ∧
      (∀ x y, φ (x + y) ≤ φ x + φ y) ∧ (∀ x y, φ (x * y) = φ x * φ y) := by
  classical
  -- A real transcendence basis is still a basis in the algebraic extension `ℂ/ℝ`.
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ ℝ
  let b : s → ℂ := fun i => (i.val : ℂ)
  have hb : IsTranscendenceBasis ℚ b := hs.algebraMap_comp (A := ℂ)
  have hbig : ℵ₀ < #ℂ := by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  have hcard : #ℂ = #s := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'
    b hb (Cardinal.mk_le_aleph0_iff.mpr inferInstance) hbig
  have hnot : ¬ s.Subsingleton := fun h =>
    (not_le_of_gt (hcard ▸ hbig)) (h.cardinalMk_le_one.trans Cardinal.one_le_aleph0)
  have hp : ∃ i j : s, i ≠ j := by
    by_contra! h
    exact hnot (fun x hx y hy => congrArg Subtype.val (h ⟨x, hx⟩ ⟨y, hy⟩))
  obtain ⟨i, j, hij⟩ := hp
  -- Distinct basis values cannot be equal or opposite, by algebraic independence.
  have habs : |i.val| ≠ |j.val| := by
    intro h
    rcases abs_eq_abs.mp h with heq | hneg
    · exact hij (Subtype.ext heq)
    · have hvanish : aeval (R := ℚ) (fun u : s => u.val) (X i + X j) = 0 := by
        simp [hneg]
      have hpoly : (X i + X j : MvPolynomial s ℚ) = 0 := by
        apply hs.1
        simpa only [map_zero] using hvanish
      have h := congrArg (MvPolynomial.eval (fun _ : s => (1 : ℚ))) hpoly
      norm_num at h
  let e : s ≃ s := Equiv.swap i j
  let σ := IsAlgClosed.equivOfTranscendenceBasis b b e hb hb
  let φ (z : ℂ) : ℝ := ‖σ z‖
  have hi : σ (b i) = b j := by
    rw [show σ (b i) = b (e i) from equiv_basis_apply b hb e i]
    simp [e]
  -- If the new modulus were continuous, its restriction to the real axis would be fixed
  -- by its values on the rationals. The transposition violates that equality.
  have hdisc : ¬ Continuous φ := by
    intro hc
    have hr : (fun x : ℝ => φ (x : ℂ)) = fun x : ℝ => |x| :=
      (Rat.denseRange_cast (𝕜 := ℝ)).equalizer (hc.comp Complex.continuous_ofReal)
        continuous_abs (by
          funext q
          change ‖σ (Complex.ofReal (q : ℝ))‖ = |(q : ℝ)|
          rw [Complex.ofReal_ratCast, map_ratCast, ← Complex.ofReal_ratCast,
            Complex.norm_real, Real.norm_eq_abs])
    have hre := congrFun hr i.val
    change ‖σ (b i)‖ = |i.val| at hre
    rw [hi] at hre
    exact habs (by simpa only [b, Complex.norm_real, Real.norm_eq_abs] using hre.symm)
  have htwo : φ (2 : ℂ) = 2 := calc
    _ = ‖(2 : ℂ)‖ := congrArg norm (map_natCast σ 2)
    _ = ‖(2 : ℝ)‖ := Complex.norm_real 2
    _ = 2 := by norm_num [Real.norm_eq_abs]
  refine ⟨φ, hdisc, fun x => norm_nonneg _, ?_, ?_, ?_, ?_⟩
  · intro h
    simpa [φ] using h 1
  · intro h
    exact (by norm_num : (2 : ℝ) ≠ 1) (htwo.symm.trans (h 2 (by norm_num)))
  · intro z w
    simpa only [φ, map_add] using norm_add_le (σ z) (σ w)
  · intro z w
    simp only [φ, map_mul, norm_mul]

end MathlibExt.Analysis.Complex.ScottishBook39Wanted
