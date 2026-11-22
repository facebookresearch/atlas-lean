/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PathSignature.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Multiplicative functionals of finite p-variation

Lyons builds rough path theory on *multiplicative functionals*: maps `(s, t) ↦ X_{s,t}` into the
truncated tensor algebra `T^{(n)}` with `X⁰ = 1` and `X_{r,s} ⊗ X_{s,t} = X_{r,t}`, the algebraic
form of Chen's identity, of finite `p`-variation controlled by a control function `ω`:
`‖Xⁱ_{s,t}‖ ≤ ω(s, t)^{i/p} / (β (i/p)!)` (T. Lyons, *Differential equations driven by rough
signals*, Rev. Mat. Iberoam. 14 (1998), Definitions 1.2.2 and 2.1.2, inequality (1.20) and
Lemma 2.1.1). For `ℝ^ι` we use coordinates over words and the `ℓ¹` norm of the coefficients of
each tensor level, which satisfies `‖u ⊗ v‖ ≤ ‖u‖ ‖v‖` and is invariant under permuting the
tensor factors, as Lyons requires.

We prove that the signature of a path with continuous velocity is a multiplicative functional of
every degree (Chen's identity) controlled, with `p = 1` and `β = 1`, by its length
`ω(s, t) = ∫_s^t ‖v‖₁`: the factorial decay `‖Sⁱ_{s,t}‖ ≤ ω(s, t)^i / i!`. Lyons's extension
theorem is recorded in `MathlibExt.Analysis.PathSignature.ExtensionTheoremWanted`.
-/

open MeasureTheory intervalIntegral

@[expose] public section

namespace MathlibExt.Analysis.PathSignature

variable {ι : Type*}

/-- **Norm of a tensor level.** For a tensor series with coefficients `F : List ι → ℝ` over a
finite alphabet, the `ℓ¹` norm `∑_{|w| = i} |F(w)|` of its degree-`i` component. -/
noncomputable def levelNorm [Fintype ι] (F : List ι → ℝ) (i : ℕ) : ℝ :=
  ∑ g : Fin i → ι, |F (List.ofFn g)|

/-- **Control function (Lyons).** A function `ω` of pairs of times in `J` is a control if it is
continuous on `{(s, t) : s ≤ t}`, nonnegative, zero on the diagonal and superadditive,
`ω(s, t) + ω(t, u) ≤ ω(s, u)` for `s ≤ t ≤ u` (T. Lyons, *Differential equations driven by rough
signals*, Rev. Mat. Iberoam. 14 (1998), Definition 1.2.2 and inequality (1.20); "regular" there
asks for continuity near the diagonal, here on the whole simplex). -/
def IsControl (ω : ℝ → ℝ → ℝ) (J : Set ℝ) : Prop :=
  ContinuousOn (fun q : ℝ × ℝ => ω q.1 q.2) {q | q.1 ∈ J ∧ q.2 ∈ J ∧ q.1 ≤ q.2} ∧
    (∀ t ∈ J, ω t t = 0) ∧ (∀ s ∈ J, ∀ t ∈ J, s ≤ t → 0 ≤ ω s t) ∧
    ∀ s ∈ J, ∀ t ∈ J, ∀ u ∈ J, s ≤ t → t ≤ u → ω s t + ω t u ≤ ω s u

/-- **Multiplicative functional of degree `n` (Lyons).** A map `(s, t) ↦ X_{s,t}` of pairs of times
`s ≤ t` in `J` to tensor series, read in the truncated tensor algebra `T^{(n)}` (coefficients of
words of length at most `n`), with `X⁰_{s,t} = 1` and `X_{r,t} = X_{r,s} ⊗ X_{s,t}` for
`r ≤ s ≤ t` (T. Lyons, *Differential equations driven by rough signals*, Rev. Mat. Iberoam. 14
(1998), Definition 2.1.2). -/
def IsMultiplicativeFunctional (n : ℕ) (X : ℝ → ℝ → List ι → ℝ) (J : Set ℝ) : Prop :=
  (∀ s ∈ J, ∀ t ∈ J, s ≤ t → X s t [] = 1) ∧
    ∀ r ∈ J, ∀ s ∈ J, ∀ t ∈ J, r ≤ s → s ≤ t → ∀ w : List ι, w.length ≤ n →
      X r t w = tensorMul (X r s) (X s t) w

/-- **`p`-variation controlled by `ω` (Lyons).** The levels `1 ≤ i ≤ n` of `X` satisfy
`‖Xⁱ_{s,t}‖ ≤ ω(s, t)^{i/p} / (β Γ(i/p + 1))` for `s ≤ t` in `J`, where `Γ(i/p + 1) = (i/p)!`
(T. Lyons, *Differential equations driven by rough signals*, Rev. Mat. Iberoam. 14 (1998),
Lemma 2.1.1 and inequality (2.20)). -/
def IsControlledBy [Fintype ι] (p β : ℝ) (n : ℕ) (X : ℝ → ℝ → List ι → ℝ) (ω : ℝ → ℝ → ℝ)
    (J : Set ℝ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i ≤ n → ∀ s ∈ J, ∀ t ∈ J, s ≤ t →
    levelNorm (X s t) i ≤ ω s t ^ ((i : ℝ) / p) / (β * Real.Gamma ((i : ℝ) / p + 1))

/-- **Finite `p`-variation of degree `n`.** Some control `ω` and weight `β > 0` control the levels
`1, …, n` of `X` in the sense of `IsControlledBy` (T. Lyons, Rev. Mat. Iberoam. 14 (1998),
Definition 1.2.2 and Lemma 2.1.1). -/
def HasFinitePVariation [Fintype ι] (p : ℝ) (n : ℕ) (X : ℝ → ℝ → List ι → ℝ) (J : Set ℝ) :
    Prop :=
  ∃ ω, IsControl ω J ∧ ∃ β > 0, IsControlledBy p β n X ω J

variable {v : ι → ℝ → ℝ}

/-- **The signature is a multiplicative functional.** For a path whose velocity is interval
integrable on every interval, `(s, t) ↦ S(X)_{s,t}` is a multiplicative functional of every
degree, on every set of times: this is Chen's identity (T. Lyons, Rev. Mat. Iberoam. 14 (1998),
§2.1, where multiplicative functionals are introduced as the abstraction of Chen's identity for
iterated integrals). -/
theorem isMultiplicativeFunctional_signature (hv : ∀ i a b, IntervalIntegrable (v i) volume a b)
    (n : ℕ) (J : Set ℝ) : IsMultiplicativeFunctional n (signature v) J :=
  ⟨fun s _ t _ _ => signature_nil v s t, fun r _ s _ t _ _ _ w _ =>
    signature_chen hv r s t w⟩

/-- **Factorial decay of the signature.** For a path with continuous velocity over a finite
alphabet and `s ≤ t`, the degree-`i` level of the signature is bounded by the length of the path:
`‖Sⁱ_{s,t}‖₁ ≤ ω(s, t)^i / i!` with `ω(s, t) = ∫_s^t ∑_j |vʲ(u)| du` (T. Lyons, *Differential
equations driven by rough signals*, Rev. Mat. Iberoam. 14 (1998), the bound (2.21) for paths of
bounded variation, `p = 1`, `β = 1`). -/
theorem levelNorm_signature_le [Fintype ι] (hv : ∀ i, Continuous (v i)) {s t : ℝ} (hst : s ≤ t)
    (i : ℕ) :
    levelNorm (signature v s t) i ≤
      (∫ u in s..t, ∑ j, |v j u|) ^ i / i.factorial := by
  set g : ℝ → ℝ := fun u => ∑ j, |v j u|
  have hg : Continuous g := continuous_finsetSum _ fun j _ => (hv j).abs
  have hcont : ∀ w : List ι, Continuous fun t => signature v s t w :=
    continuous_signature (fun i a b => (hv i).intervalIntegrable a b) s
  induction i generalizing t with
  | zero => simp [levelNorm]
  | succ i ih =>
    set F : ℝ → ℝ := fun u => ∫ x in s..u, g x
    unfold levelNorm
    rw [sum_fin_succ_ofFn i (fun w => |signature v s t w|)]
    simp_rw [signature_concat]
    have hFc : Continuous F := continuous_primitive (fun a b => hg.intervalIntegrable a b) s
    -- Bound each coordinate by the integral of absolute values.
    have hle : ∀ j (x : Fin i → ι),
        |∫ u in s..t, signature v s u (List.ofFn x) * v j u| ≤
          ∫ u in s..t, |signature v s u (List.ofFn x)| * |v j u| := by
      intro j x
      simpa [abs_mul] using intervalIntegral.abs_integral_le_integral_abs hst
        (f := fun u => signature v s u (List.ofFn x) * v j u)
    have hstep : ∑ j, ∑ x : Fin i → ι, |∫ u in s..t, signature v s u (List.ofFn x) * v j u| ≤
        ∫ u in s..t, (∑ x : Fin i → ι, |signature v s u (List.ofFn x)|) * g u := by
      calc _ ≤ ∑ j, ∑ x : Fin i → ι, ∫ u in s..t, |signature v s u (List.ofFn x)| * |v j u| :=
            Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun x _ => hle j x
        _ = ∫ u in s..t, ∑ j, ∑ x : Fin i → ι, |signature v s u (List.ofFn x)| * |v j u| := by
            rw [intervalIntegral.integral_finsetSum fun j _ => ?_]
            · refine Finset.sum_congr rfl fun j _ => ?_
              rw [intervalIntegral.integral_finsetSum fun x _ => ?_]
              exact ((hcont _).abs.mul (hv j).abs).intervalIntegrable _ _
            · exact (continuous_finsetSum _ fun x _ =>
                (hcont _).abs.mul (hv j).abs).intervalIntegrable _ _
        _ = ∫ u in s..t, (∑ x : Fin i → ι, |signature v s u (List.ofFn x)|) * g u := by
            refine intervalIntegral.integral_congr fun u _ => ?_
            simp only [g, Finset.mul_sum, Finset.sum_mul]
    refine hstep.trans ?_
    have hint : IntervalIntegrable (fun x => F x ^ i / i.factorial * g x) volume s t :=
      (((hFc.pow i).div_const _).mul hg).intervalIntegrable s t
    -- Use the induction hypothesis under the integral, then integrate exactly.
    have hmono : ∫ u in s..t, (∑ x : Fin i → ι, |signature v s u (List.ofFn x)|) * g u ≤
        ∫ u in s..t, F u ^ i / i.factorial * g u := by
      refine intervalIntegral.integral_mono_on hst ?_ hint fun u hu => ?_
      · exact ((continuous_finsetSum _ fun x _ => (hcont _).abs).mul hg).intervalIntegrable _ _
      · exact mul_le_mul_of_nonneg_right (ih hu.1) (Finset.sum_nonneg fun j _ => abs_nonneg _)
    refine hmono.trans (le_of_eq ?_)
    have hF : ∀ u, HasDerivAt F (g u) u := fun u => (hg.integral_hasStrictDerivAt s u).hasDerivAt
    have hderiv : ∀ x ∈ Set.uIcc s t, HasDerivAt (fun u => F u ^ (i + 1) / (i + 1).factorial)
        (F x ^ i / i.factorial * g x) x := by
      intro x _
      have := ((hF x).pow (i + 1)).div_const ((i + 1).factorial : ℝ)
      convert this using 1
      rw [Nat.factorial_succ, Nat.cast_mul]
      have : ((i.factorial : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      push_cast
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    simp [F]

/-- **The length of a path is a control.** For a continuous velocity over a finite alphabet,
`ω(s, t) = ∫_s^t ∑_j |vʲ(u)| du`, the `ℓ¹` length of the path between `s` and `t`, is a control
function on every set of times (continuous, nonnegative for `s ≤ t`, zero on the diagonal and
additive, hence superadditive). -/
theorem isControl_length [Fintype ι] (hv : ∀ i, Continuous (v i)) (J : Set ℝ) :
    IsControl (fun s t => ∫ u in s..t, ∑ j, |v j u|) J := by
  set g : ℝ → ℝ := fun u => ∑ j, |v j u|
  have hg : Continuous g := continuous_finsetSum _ fun j _ => (hv j).abs
  have hgi : ∀ a b, IntervalIntegrable g volume a b := fun a b => hg.intervalIntegrable a b
  refine ⟨?_, fun t _ => intervalIntegral.integral_same, fun s _ t _ hst => ?_,
    fun s _ t _ u _ _ _ => (intervalIntegral.integral_add_adjacent_intervals (hgi s t)
      (hgi t u)).le⟩
  · have : (fun q : ℝ × ℝ => ∫ u in q.1..q.2, g u) =
        fun q => (∫ u in (0 : ℝ)..q.2, g u) - ∫ u in (0 : ℝ)..q.1, g u := by
      funext q
      rw [intervalIntegral.integral_interval_sub_left (hgi 0 q.2) (hgi 0 q.1)]
    rw [this]
    exact (((continuous_primitive hgi 0).comp continuous_snd).sub
      ((continuous_primitive hgi 0).comp continuous_fst)).continuousOn
  · exact intervalIntegral.integral_nonneg hst fun u _ =>
      Finset.sum_nonneg fun j _ => abs_nonneg _

/-- **The signature of a path of bounded variation is controlled by its length, with `p = 1`.**
For a continuous velocity over a finite alphabet, the signature satisfies Lyons's estimate
`‖Sⁱ_{s,t}‖ ≤ ω(s, t)^{i/p} / (β (i/p)!)` with `p = 1`, `β = 1` and `ω` the length of the path,
in every degree (T. Lyons, *Differential equations driven by rough signals*, Rev. Mat. Iberoam. 14
(1998), inequalities (2.20)–(2.21)). -/
theorem isControlledBy_signature [Fintype ι] (hv : ∀ i, Continuous (v i)) (n : ℕ) (J : Set ℝ) :
    IsControlledBy 1 1 n (signature v) (fun s t => ∫ u in s..t, ∑ j, |v j u|) J := by
  intro i _ _ s _ t _ hst
  have h := levelNorm_signature_le hv hst i
  rw [div_one, one_mul, Real.rpow_natCast, Real.Gamma_nat_eq_factorial]
  exact h

/-- **Signatures of paths of bounded variation have finite `1`-variation in every degree.** -/
theorem hasFinitePVariation_signature [Fintype ι] (hv : ∀ i, Continuous (v i)) (n : ℕ)
    (J : Set ℝ) : HasFinitePVariation 1 n (signature v) J :=
  ⟨_, isControl_length hv J, 1, one_pos, isControlledBy_signature hv n J⟩

end MathlibExt.Analysis.PathSignature
