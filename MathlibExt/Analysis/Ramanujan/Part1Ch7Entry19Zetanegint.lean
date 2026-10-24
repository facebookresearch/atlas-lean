/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Meromorphic.Basic
public import MathlibExt.Analysis.Ramanujan.Part1Ch7Phi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Set.Defs
import Mathlib.NumberTheory.LSeries.ZMod
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Basic

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 7

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry19Zetanegint

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

set_option backward.proofsInPublic true in
def chapter7Entry19Left (p q : ℕ) (hp : 0 < p) (hpq : p < q) (r : ℂ) : ℂ :=
  Complex.cpow ((2 * Real.pi * q : ℝ) : ℂ) r / (4 * Complex.Gamma r) *
    (chapter7Phi (r - 1) ⟨(p : ℝ) / q - 1, by
        constructor
        · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
          have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hpq
          have := div_pos hp0 hq0
          linarith
        · have hpqr : (p : ℝ) < q := by exact_mod_cast hpq
          have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hpq
          exact sub_neg.mpr ((div_lt_one hq0).2 hpqr)⟩ -
      chapter7Phi (r - 1) ⟨-((p : ℝ) / q), by
        constructor
        · have hpqr : (p : ℝ) < q := by exact_mod_cast hpq
          have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hpq
          linarith [((div_lt_one hq0).2 hpqr)]
        · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
          have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hpq
          exact neg_neg_of_pos (div_pos hp0 hq0)⟩)

set_option backward.proofsInPublic true in
def chapter7Entry19Right (p q : ℕ) (r : ℂ) : ℂ :=
  Complex.sin (Real.pi * r / 2) *
    ∑ j ∈ (Icc 1 ((q - 1) / 2)).attach,
      (Real.sin (2 * Real.pi * (j : ℕ) * p / q) : ℂ) *
        (chapter7Phi (-r) ⟨(j : ℕ) / (q : ℝ) - 1, by
            have hjmem : (j : ℕ) ∈ Icc 1 ((q - 1) / 2) := j.property
            have hj0 : 0 < (j : ℕ) := by
              have := (Finset.mem_Icc.mp hjmem).1
              omega
            have hjq : (j : ℕ) < q := by
              have := (Finset.mem_Icc.mp hjmem).2
              omega
            constructor
            · have hj0r : (0 : ℝ) < (j : ℕ) := by exact_mod_cast hj0
              have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hjq
              linarith [div_pos hj0r hq0]
            · have hjqr : ((j : ℕ) : ℝ) < q := by exact_mod_cast hjq
              have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hjq
              exact sub_neg.mpr ((div_lt_one hq0).2 hjqr)⟩ -
          chapter7Phi (-r) ⟨-((j : ℕ) / (q : ℝ)), by
            have hjmem : (j : ℕ) ∈ Icc 1 ((q - 1) / 2) := j.property
            have hj0 : 0 < (j : ℕ) := by
              have := (Finset.mem_Icc.mp hjmem).1
              omega
            have hjq : (j : ℕ) < q := by
              have := (Finset.mem_Icc.mp hjmem).2
              omega
            constructor
            · have hjqr : ((j : ℕ) : ℝ) < q := by exact_mod_cast hjq
              have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hjq
              linarith [((div_lt_one hq0).2 hjqr)]
            · have hj0r : (0 : ℝ) < (j : ℕ) := by exact_mod_cast hj0
              have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hjq
              exact neg_neg_of_pos (div_pos hj0r hq0)⟩)

private theorem left_eq_odd (p q : ℕ) (hp : 0 < p) (hpq : p < q) (r : ℂ) :
    chapter7Entry19Left p q hp hpq r =
      Complex.cpow ((2 * Real.pi * q : ℝ) : ℂ) r / (4 * Complex.Gamma r) *
        (-2 * HurwitzZeta.hurwitzZetaOdd ((↑((p : ℝ) / q) : ℝ) : UnitAddCircle) (1 - r)) := by
  have hs : (-(r - 1) : ℂ) = 1 - r := by ring
  have hcirc1 : ((((⟨(p : ℝ) / q - 1, by
        constructor
        · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
          have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hpq
          have := div_pos hp0 hq0
          linarith
        · have hpqr : (p : ℝ) < q := by exact_mod_cast hpq
          have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hpq
          exact sub_neg.mpr ((div_lt_one hq0).2 hpqr)⟩ : Chapter7PhiArgument) : ℝ) + 1 : ℝ) :
              UnitAddCircle)
      = ((↑((p : ℝ) / q) : ℝ) : UnitAddCircle) := by
    congr 1
    push_cast
    ring
  have hcirc2 : ((((-((p : ℝ) / q) + 1) : ℝ)) : UnitAddCircle)
      = -(((↑((p : ℝ) / q) : ℝ)) : UnitAddCircle) := by
    rw [AddCircle.coe_add]
    simp [AddCircle.coe_period]
  unfold chapter7Entry19Left
  congr 1
  have hPhi1 : chapter7Phi (r - 1) ⟨(p : ℝ) / q - 1, by
        constructor
        · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
          have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hpq
          have := div_pos hp0 hq0
          linarith
        · have hpqr : (p : ℝ) < q := by exact_mod_cast hpq
          have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hpq
          exact sub_neg.mpr ((div_lt_one hq0).2 hpqr)⟩
      = riemannZeta (1 - r) -
        HurwitzZeta.hurwitzZeta ((↑((p : ℝ) / q) : ℝ) : UnitAddCircle) (1 - r) := by
    unfold chapter7Phi
    rw [hs, hcirc1]
  have hPhi2 : chapter7Phi (r - 1) ⟨-((p : ℝ) / q), by
        constructor
        · have hpqr : (p : ℝ) < q := by exact_mod_cast hpq
          have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hpq
          linarith [((div_lt_one hq0).2 hpqr)]
        · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
          have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hpq
          exact neg_neg_of_pos (div_pos hp0 hq0)⟩
      = riemannZeta (1 - r) -
        HurwitzZeta.hurwitzZeta (-(((↑((p : ℝ) / q) : ℝ)) : UnitAddCircle)) (1 - r) := by
    unfold chapter7Phi
    have hcirc2' : (((((⟨-((p : ℝ) / q), by
        constructor
        · have hpqr : (p : ℝ) < q := by exact_mod_cast hpq
          have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hpq
          linarith [((div_lt_one hq0).2 hpqr)]
        · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
          have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hpq
          exact neg_neg_of_pos (div_pos hp0 hq0)⟩ : Chapter7PhiArgument) : ℝ) + 1 : ℝ)) :
              UnitAddCircle)
        = -(((↑((p : ℝ) / q) : ℝ)) : UnitAddCircle) := by
      have hval : (((⟨-((p : ℝ) / q), by
        constructor
        · have hpqr : (p : ℝ) < q := by exact_mod_cast hpq
          have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hpq
          linarith [((div_lt_one hq0).2 hpqr)]
        · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
          have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hpq
          exact neg_neg_of_pos (div_pos hp0 hq0)⟩ : Chapter7PhiArgument) : ℝ) + 1 : ℝ)
        = -((p : ℝ) / q) + 1 := rfl
      rw [hval, hcirc2]
    rw [hs, hcirc2']
  rw [hPhi1, hPhi2]
  have hZ : HurwitzZeta.hurwitzZeta (((↑((p : ℝ) / q) : ℝ)) : UnitAddCircle) (1 - r) =
      HurwitzZeta.hurwitzZetaEven (((↑((p : ℝ) / q) : ℝ)) : UnitAddCircle) (1 - r) +
        HurwitzZeta.hurwitzZetaOdd (((↑((p : ℝ) / q) : ℝ)) : UnitAddCircle) (1 - r) := rfl
  have hZn : HurwitzZeta.hurwitzZeta (-(((↑((p : ℝ) / q) : ℝ)) : UnitAddCircle)) (1 - r) =
      HurwitzZeta.hurwitzZetaEven (((↑((p : ℝ) / q) : ℝ)) : UnitAddCircle) (1 - r) -
        HurwitzZeta.hurwitzZetaOdd (((↑((p : ℝ) / q) : ℝ)) : UnitAddCircle) (1 - r) := by
    calc HurwitzZeta.hurwitzZeta (-(((↑((p : ℝ) / q) : ℝ)) : UnitAddCircle)) (1 - r)
        = HurwitzZeta.hurwitzZetaEven (-(((↑((p : ℝ) / q) : ℝ)) : UnitAddCircle)) (1 - r) +
          HurwitzZeta.hurwitzZetaOdd (-(((↑((p : ℝ) / q) : ℝ)) : UnitAddCircle)) (1 - r) := rfl
      _ = HurwitzZeta.hurwitzZetaEven (((↑((p : ℝ) / q) : ℝ)) : UnitAddCircle) (1 - r) +
          (-HurwitzZeta.hurwitzZetaOdd (((↑((p : ℝ) / q) : ℝ)) : UnitAddCircle) (1 - r)) := by
          rw [HurwitzZeta.hurwitzZetaEven_neg, HurwitzZeta.hurwitzZetaOdd_neg]
      _ = _ := by ring
  rw [hZ, hZn]
  ring

private theorem phiDiff_right (j q : ℕ) (r : ℂ)
    (h1 : Chapter7PhiArgument) (h1val : (h1 : ℝ) = (j : ℝ) / q - 1)
    (h2 : Chapter7PhiArgument) (h2val : (h2 : ℝ) = -((j : ℝ) / q)) :
    chapter7Phi (-r) h1 - chapter7Phi (-r) h2 =
      -2 * HurwitzZeta.hurwitzZetaOdd ((↑((j : ℝ) / q) : ℝ) : UnitAddCircle) r := by
  have hsr : (-(-r) : ℂ) = r := by ring
  have hcirc1 : ((((h1 : ℝ) + 1 : ℝ)) : UnitAddCircle)
      = ((↑((j : ℝ) / q) : ℝ) : UnitAddCircle) := by
    rw [h1val]
    congr 1
    ring
  have hcirc2 : ((((h2 : ℝ) + 1 : ℝ)) : UnitAddCircle)
      = -(((↑((j : ℝ) / q) : ℝ)) : UnitAddCircle) := by
    rw [h2val]
    have : ((-((j : ℝ) / q) + 1 : ℝ)) = -((j : ℝ) / q) + 1 := rfl
    rw [this]
    rw [AddCircle.coe_add]
    simp [AddCircle.coe_period]
  have hPhi1 : chapter7Phi (-r) h1
      = riemannZeta r -
        HurwitzZeta.hurwitzZeta ((↑((j : ℝ) / q) : ℝ) : UnitAddCircle) r := by
    unfold chapter7Phi
    rw [hsr, hcirc1]
  have hPhi2 : chapter7Phi (-r) h2
      = riemannZeta r -
        HurwitzZeta.hurwitzZeta (-(((↑((j : ℝ) / q) : ℝ)) : UnitAddCircle)) r := by
    unfold chapter7Phi
    rw [hsr, hcirc2]
  rw [hPhi1, hPhi2]
  have hZ : HurwitzZeta.hurwitzZeta (((↑((j : ℝ) / q) : ℝ)) : UnitAddCircle) r =
      HurwitzZeta.hurwitzZetaEven (((↑((j : ℝ) / q) : ℝ)) : UnitAddCircle) r +
        HurwitzZeta.hurwitzZetaOdd (((↑((j : ℝ) / q) : ℝ)) : UnitAddCircle) r := rfl
  have hZn : HurwitzZeta.hurwitzZeta (-(((↑((j : ℝ) / q) : ℝ)) : UnitAddCircle)) r =
      HurwitzZeta.hurwitzZetaEven (((↑((j : ℝ) / q) : ℝ)) : UnitAddCircle) r -
        HurwitzZeta.hurwitzZetaOdd (((↑((j : ℝ) / q) : ℝ)) : UnitAddCircle) r := by
    calc HurwitzZeta.hurwitzZeta (-(((↑((j : ℝ) / q) : ℝ)) : UnitAddCircle)) r
        = HurwitzZeta.hurwitzZetaEven (-(((↑((j : ℝ) / q) : ℝ)) : UnitAddCircle)) r +
          HurwitzZeta.hurwitzZetaOdd (-(((↑((j : ℝ) / q) : ℝ)) : UnitAddCircle)) r := rfl
      _ = _ := by
          rw [HurwitzZeta.hurwitzZetaEven_neg, HurwitzZeta.hurwitzZetaOdd_neg]
          ring
  rw [hZ, hZn]
  ring

private theorem left_differentiable (p q : ℕ) (hp : 0 < p) (hpq : p < q) :
    Differentiable ℂ (chapter7Entry19Left p q hp hpq) := by
  have hq0 : 0 < q := lt_trans hp hpq
  have hB : ((2 * Real.pi * q : ℝ) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    apply ne_of_gt
    have hpi : 0 < Real.pi := Real.pi_pos
    have hqr : (0 : ℝ) < q := by exact_mod_cast hq0
    positivity
  have hcpow : Differentiable ℂ (fun r : ℂ => Complex.cpow ((2 * Real.pi * q : ℝ) : ℂ) r) :=
    Differentiable.const_cpow differentiable_id (Or.inl hB)
  have hGammaInv : Differentiable ℂ (fun r : ℂ => (Complex.Gamma r)⁻¹) :=
    Complex.differentiable_one_div_Gamma
  have hodd : Differentiable ℂ
      (fun r : ℂ => HurwitzZeta.hurwitzZetaOdd ((↑((p : ℝ) / q) : ℝ) : UnitAddCircle) (1 - r)) :=
    (HurwitzZeta.differentiable_hurwitzZetaOdd _).comp
      ((differentiable_const (1 : ℂ)).sub differentiable_id)
  have hmain : Differentiable ℂ (fun r : ℂ =>
      Complex.cpow ((2 * Real.pi * q : ℝ) : ℂ) r * (Complex.Gamma r)⁻¹ *
        HurwitzZeta.hurwitzZetaOdd ((↑((p : ℝ) / q) : ℝ) : UnitAddCircle) (1 - r) *
          (-2 / 4)) := by
    apply Differentiable.mul
    · apply Differentiable.mul
      · apply Differentiable.mul
        · exact hcpow
        · exact hGammaInv
      · exact hodd
    · exact differentiable_const _
  have heq : chapter7Entry19Left p q hp hpq = (fun r : ℂ =>
      Complex.cpow ((2 * Real.pi * q : ℝ) : ℂ) r * (Complex.Gamma r)⁻¹ *
        HurwitzZeta.hurwitzZetaOdd ((↑((p : ℝ) / q) : ℝ) : UnitAddCircle) (1 - r) *
          (-2 / 4)) := by
    funext r
    rw [left_eq_odd p q hp hpq r]
    rw [div_eq_mul_inv, mul_inv]
    ring
  rw [heq]
  exact hmain

private theorem left_meromorphic (p q : ℕ) (hp : 0 < p) (hpq : p < q) :
    MeromorphicOn (chapter7Entry19Left p q hp hpq) Set.univ := by
  intro z _hz
  exact (Differentiable.analyticAt (left_differentiable p q hp hpq) z).meromorphicAt

private theorem perTerm_simple (q : ℕ) (r : ℂ) (a : ↥(Icc 1 ((q - 1) / 2))) :
    chapter7Phi (-r) ⟨(a : ℕ) / (q : ℝ) - 1, by
            have hjmem : (a : ℕ) ∈ Icc 1 ((q - 1) / 2) := a.property
            have hj0 : 0 < (a : ℕ) := by
              have := (Finset.mem_Icc.mp hjmem).1
              omega
            have hjq : (a : ℕ) < q := by
              have := (Finset.mem_Icc.mp hjmem).2
              omega
            constructor
            · have hj0r : (0 : ℝ) < (a : ℕ) := by exact_mod_cast hj0
              have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hjq
              linarith [div_pos hj0r hq0]
            · have hjqr : ((a : ℕ) : ℝ) < q := by exact_mod_cast hjq
              have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hjq
              exact sub_neg.mpr ((div_lt_one hq0).2 hjqr)⟩ -
      chapter7Phi (-r) ⟨-((a : ℕ) / (q : ℝ)), by
            have hjmem : (a : ℕ) ∈ Icc 1 ((q - 1) / 2) := a.property
            have hj0 : 0 < (a : ℕ) := by
              have := (Finset.mem_Icc.mp hjmem).1
              omega
            have hjq : (a : ℕ) < q := by
              have := (Finset.mem_Icc.mp hjmem).2
              omega
            constructor
            · have hjqr : ((a : ℕ) : ℝ) < q := by exact_mod_cast hjq
              have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hjq
              linarith [((div_lt_one hq0).2 hjqr)]
            · have hj0r : (0 : ℝ) < (a : ℕ) := by exact_mod_cast hj0
              have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hjq
              exact neg_neg_of_pos (div_pos hj0r hq0)⟩
    = -2 * HurwitzZeta.hurwitzZetaOdd ((↑(((a : ℕ) : ℝ) / q) : ℝ) : UnitAddCircle) r := by
  exact phiDiff_right _ _ _ _ rfl _ rfl

private theorem right_eq_odd (p q : ℕ) (r : ℂ) :
    chapter7Entry19Right p q r =
      Complex.sin (Real.pi * r / 2) *
        (∑ j ∈ Icc 1 ((q - 1) / 2),
          (Real.sin (2 * Real.pi * j * p / q) : ℂ) *
            (-2 * HurwitzZeta.hurwitzZetaOdd ((↑((j : ℝ) / q) : ℝ) : UnitAddCircle) r)) := by
  unfold chapter7Entry19Right
  congr 1
  rw [← Finset.sum_attach (Icc 1 ((q - 1) / 2))
    (fun j => (Real.sin (2 * Real.pi * j * p / q) : ℂ) *
      (-2 * HurwitzZeta.hurwitzZetaOdd ((↑((j : ℝ) / q) : ℝ) : UnitAddCircle) r))]
  apply Finset.sum_congr rfl
  intro a ha
  change (Real.sin (2 * Real.pi * (a : ℕ) * p / q) : ℂ) * (_ - _) = _
  congr 1
  have h := perTerm_simple q r a
  exact h

private theorem right_differentiable (p q : ℕ) : Differentiable ℂ (chapter7Entry19Right p q) := by
  have heq : chapter7Entry19Right p q = (fun r : ℂ =>
      Complex.sin (Real.pi * r / 2) *
        (∑ j ∈ Icc 1 ((q - 1) / 2),
          (Real.sin (2 * Real.pi * j * p / q) : ℂ) *
            (-2 * HurwitzZeta.hurwitzZetaOdd ((↑((j : ℝ) / q) : ℝ) : UnitAddCircle) r))) := by
    funext r
    exact right_eq_odd p q r
  rw [heq]
  apply Differentiable.mul
  · apply Complex.differentiable_sin.comp
    apply Differentiable.div_const
    exact Differentiable.const_mul differentiable_id _
  · apply Differentiable.fun_sum
    intro j _hj
    apply Differentiable.const_mul
    apply Differentiable.const_mul
    exact HurwitzZeta.differentiable_hurwitzZetaOdd _

private theorem right_meromorphic (p q : ℕ) :
    MeromorphicOn (chapter7Entry19Right p q) Set.univ := by
  intro z _hz
  exact (Differentiable.analyticAt (right_differentiable p q) z).meromorphicAt

private theorem left_eq_sinZeta (p q : ℕ) (hp : 0 < p) (hpq : p < q) (r : ℂ) (hr : 0 < r.re) :
    chapter7Entry19Left p q hp hpq r =
      -(Complex.cpow ((q : ℝ) : ℂ) r) * Complex.sin (Real.pi * r / 2) *
        HurwitzZeta.sinZeta ((↑((p : ℝ) / q) : ℝ) : UnitAddCircle) r := by
  have hrne : ∀ n : ℕ, r ≠ -(n : ℂ) := by
    intro n h
    have hre : r.re = (-(n : ℂ)).re := congrArg Complex.re h
    have h1 : (-(n : ℂ)).re = -((n : ℕ) : ℝ) := by simp
    rw [h1] at hre
    have hn : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hGammaNe : Complex.Gamma r ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hr
  have hOdd := HurwitzZeta.hurwitzZetaOdd_one_sub
    ((↑((p : ℝ) / q) : ℝ) : UnitAddCircle) hrne
  rw [left_eq_odd p q hp hpq r]
  change ((2 * Real.pi * q : ℝ) : ℂ) ^ r / (4 * Complex.Gamma r) *
      (-2 * HurwitzZeta.hurwitzZetaOdd ((↑((p : ℝ) / q) : ℝ) : UnitAddCircle) (1 - r)) =
    -(((q : ℝ) : ℂ) ^ r) * Complex.sin (Real.pi * r / 2) *
      HurwitzZeta.sinZeta ((↑((p : ℝ) / q) : ℝ) : UnitAddCircle) r
  rw [hOdd]
  have hbase : (2 : ℂ) * ((Real.pi : ℝ) : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  have hB : ((2 * Real.pi * q : ℝ) : ℂ) = ((2 * Real.pi : ℝ) : ℂ) * ((q : ℝ) : ℂ) := by
    push_cast; ring
  rw [hbase]
  rw [hB]
  have h2pi_nonneg : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hq_nonneg : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
  have hsplit : (((2 * Real.pi : ℝ) : ℂ) * ((q : ℝ) : ℂ)) ^ r =
      (((2 * Real.pi : ℝ) : ℂ) ^ r) * (((q : ℝ) : ℂ) ^ r) := by
    have h := Complex.mul_cpow_ofReal_nonneg h2pi_nonneg hq_nonneg r
    simpa using h
  rw [hsplit]
  have hneg : (((2 * Real.pi : ℝ) : ℂ) ^ (-r)) = ((((2 * Real.pi : ℝ) : ℂ) ^ r))⁻¹ := by
    exact Complex.cpow_neg _ _
  rw [hneg]
  have h2pi_cpow_ne : (((2 * Real.pi : ℝ) : ℂ) ^ r) ≠ 0 := by
    simp [Complex.cpow_eq_zero_iff]
  field_simp
  ring

private theorem exp_sub_div_aux (x : ℂ) :
    (Complex.exp (x * Complex.I) - Complex.exp (-(x * Complex.I))) / (2 * Complex.I)
      = Complex.sin x := by
  have hneg : (-(x * Complex.I) : ℂ) = (-x) * Complex.I := by ring
  rw [hneg, Complex.exp_mul_I, ← Complex.cos_sub_sin_I]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp
  ring

private theorem stdAddChar_eq_exp (q : ℕ) [NeZero q] (w : ZMod q) :
    ZMod.stdAddChar w =
      Complex.exp ((((2 * Real.pi * w.val / q : ℝ)) : ℂ) * Complex.I) := by
  rw [ZMod.stdAddChar_apply]
  have h := ZMod.toCircle_apply w
  rw [h]
  congr 1
  push_cast
  ring

private theorem stdAddChar_sub_div (q : ℕ) [NeZero q] (w : ZMod q) :
    (ZMod.stdAddChar w - ZMod.stdAddChar (-w)) / (2 * Complex.I)
      = Complex.sin ((((2 * Real.pi * w.val / q : ℝ)) : ℂ)) := by
  have hpos : ZMod.stdAddChar w =
      Complex.exp ((((2 * Real.pi * w.val / q : ℝ)) : ℂ) * Complex.I) :=
    stdAddChar_eq_exp q w
  have hneg_char : ZMod.stdAddChar (-w) = (starRingEnd ℂ) (ZMod.stdAddChar w) := by
    exact AddChar.map_neg_eq_conj _ _
  rw [hneg_char, hpos]
  have hθ : (starRingEnd ℂ) ((((2 * Real.pi * w.val / q : ℝ)) : ℂ))
      = ((((2 * Real.pi * w.val / q : ℝ)) : ℂ)) := Complex.conj_ofReal _
  have hconj : (starRingEnd ℂ) (Complex.exp ((((2 * Real.pi * w.val / q : ℝ)) : ℂ) * Complex.I))
      = Complex.exp (-((((2 * Real.pi * w.val / q : ℝ)) : ℂ) * Complex.I)) := by
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, hθ, Complex.conj_I]
    ring
  rw [hconj]
  exact exp_sub_div_aux _

private theorem sin_mod_eq (a q : ℕ) (hq : 0 < q) :
    Real.sin (2 * Real.pi * ((a % q : ℕ) : ℝ) / q)
      = Real.sin (2 * Real.pi * (a : ℝ) / q) := by
  have hmod : a % q + q * (a / q) = a := Nat.mod_add_div a q
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  have ha : (a : ℝ) = ((a % q : ℕ) : ℝ) + (q : ℝ) * ((a / q : ℕ) : ℝ) := by
    have h := congrArg (Nat.cast : ℕ → ℝ) hmod
    push_cast at h
    linarith [h]
  have heq_nat : (2 * Real.pi * (a : ℝ) / (q : ℝ))
      = (2 * Real.pi * ((a % q : ℕ) : ℝ) / (q : ℝ)) + ((a / q : ℕ) : ℝ) * (2 * Real.pi) := by
    conv_lhs => rw [ha]
    field_simp
  have heq_int : (2 * Real.pi * (a : ℝ) / (q : ℝ))
      = (2 * Real.pi * ((a % q : ℕ) : ℝ) / (q : ℝ)) + ((((a / q : ℕ) : ℤ) : ℝ)) *
          (2 * Real.pi) := by
    rw [Int.cast_natCast]
    exact heq_nat
  rw [heq_int]
  exact (Real.sin_add_int_mul_two_pi _ _).symm

private theorem phi_eq_sin (q : ℕ) [NeZero q] (p : ℕ) (hpq : p < q) (j : ZMod q) :
    (ZMod.stdAddChar ((p : ZMod q) * j) - ZMod.stdAddChar (-((p : ZMod q) * j))) / (2 * Complex.I)
      = ((Real.sin (2 * Real.pi * p * j.val / q) : ℝ) : ℂ) := by
  have hq0 : 0 < q := NeZero.pos q
  have hval : ((p : ZMod q) * j).val = (p * j.val) % q := by
    rw [ZMod.val_mul, ZMod.val_natCast_of_lt hpq]
  have hbase := stdAddChar_sub_div q ((p : ZMod q) * j)
  rw [hval] at hbase
  have hcast : ((p * j.val : ℕ) : ℝ) = (p : ℝ) * (j.val : ℝ) := by push_cast; ring
  have hsin := sin_mod_eq (p * j.val) q hq0
  rw [hcast] at hsin
  rw [hbase, ← Complex.ofReal_sin, hsin]
  congr 1
  congr 1
  ring

private theorem k_ne_zero (q p : ℕ) [NeZero q] (hp : 0 < p) (hpq : p < q) : (p : ZMod q) ≠ 0 := by
  intro h0
  have hval : ((p : ZMod q)).val = 0 := by rw [h0]; exact (ZMod.val_eq_zero _).mpr rfl
  rw [ZMod.val_natCast_of_lt hpq] at hval
  omega

private theorem toAddCircle_k (q p : ℕ) [NeZero q] (hpq : p < q) :
    ZMod.toAddCircle (p : ZMod q) = ((((p : ℝ) / q : ℝ)) : UnitAddCircle) := by
  rw [ZMod.toAddCircle_apply, ZMod.val_natCast_of_lt hpq]

private theorem LFunction_sub_div (q : ℕ) [NeZero q] (Φ₁ Φ₂ : ZMod q → ℂ) (s : ℂ) :
    (ZMod.LFunction Φ₁ s - ZMod.LFunction Φ₂ s) / (2 * Complex.I)
      = ZMod.LFunction (fun j => (Φ₁ j - Φ₂ j) / (2 * Complex.I)) s := by
  unfold ZMod.LFunction
  have hmul : (↑q : ℂ) ^ (-s) * ∑ j, Φ₁ j * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s -
      (↑q : ℂ) ^ (-s) * ∑ j, Φ₂ j * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s
      = (↑q : ℂ) ^ (-s) * (∑ j, Φ₁ j * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s -
        ∑ j, Φ₂ j * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s) := by ring
  rw [hmul]
  have hdiv : ((↑q : ℂ) ^ (-s) * (∑ j, Φ₁ j * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s -
        ∑ j, Φ₂ j * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s)) / (2 * Complex.I)
      = (↑q : ℂ) ^ (-s) * ((∑ j, Φ₁ j * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s -
        ∑ j, Φ₂ j * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) s) / (2 * Complex.I)) := by ring
  rw [hdiv]
  congr 1
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  simp only
  ring

private theorem phi_odd (q : ℕ) [NeZero q] (p : ℕ) :
    Function.Odd (fun j : ZMod q => (ZMod.stdAddChar ((p : ZMod q) * j) -
      ZMod.stdAddChar (-((p : ZMod q) * j))) / (2 * Complex.I)) := by
  intro j
  change (ZMod.stdAddChar ((p : ZMod q) * (-j)) -
      ZMod.stdAddChar (-((p : ZMod q) * (-j)))) / (2 * Complex.I) = _
  have h1 : (p : ZMod q) * (-j) = -((p : ZMod q) * j) := by ring
  rw [h1]
  have h2' : (-(-((p : ZMod q) * j)) : ZMod q) = (p : ZMod q) * j := neg_neg _
  rw [h2']
  ring

private theorem sinZeta_eq_LFunction (q p : ℕ) [NeZero q] (hp : 0 < p) (hpq : p < q) (s : ℂ) :
    HurwitzZeta.sinZeta ((((p : ℝ) / q : ℝ)) : UnitAddCircle) s =
      (ZMod.LFunction (fun j => ZMod.stdAddChar ((p : ZMod q) * j)) s -
        ZMod.LFunction (fun j => ZMod.stdAddChar (-((p : ZMod q) * j))) s) / (2 * Complex.I) := by
  have hk : (p : ZMod q) ≠ 0 := k_ne_zero q p hp hpq
  have hk_neg : (-(p : ZMod q)) ≠ 0 := neg_ne_zero.mpr hk
  have ha : ZMod.toAddCircle (p : ZMod q) = ((((p : ℝ) / q : ℝ)) : UnitAddCircle) :=
    toAddCircle_k q p hpq
  have ha_neg : ZMod.toAddCircle (-(p : ZMod q)) = -((((p : ℝ) / q : ℝ)) : UnitAddCircle) := by
    rw [map_neg, ha]
  have h1 : ZMod.LFunction (fun j => ZMod.stdAddChar ((p : ZMod q) * j)) s
      = HurwitzZeta.expZeta ((((p : ℝ) / q : ℝ)) : UnitAddCircle) s := by
    have h := ZMod.LFunction_stdAddChar_eq_expZeta ((p : ZMod q)) s (Or.inl hk)
    rw [ha] at h
    exact h
  have h2 : ZMod.LFunction (fun j => ZMod.stdAddChar (-((p : ZMod q) * j))) s
      = HurwitzZeta.expZeta (-((((p : ℝ) / q : ℝ)) : UnitAddCircle)) s := by
    have hneg_mul : (fun j : ZMod q => ZMod.stdAddChar (-((p : ZMod q) * j)))
        = (fun j => ZMod.stdAddChar ((-(p : ZMod q)) * j)) := by
      funext j
      congr 1
      ring
    rw [hneg_mul]
    have h := ZMod.LFunction_stdAddChar_eq_expZeta (-(p : ZMod q)) s (Or.inl hk_neg)
    rw [ha_neg] at h
    exact h
  rw [h1, h2]
  exact HurwitzZeta.sinZeta_eq _ _

private theorem qpow_mul_sinZeta (q p : ℕ) [NeZero q] (hp : 0 < p) (hpq : p < q) (s : ℂ) :
    (((q : ℕ) : ℂ) ^ s) * HurwitzZeta.sinZeta ((((p : ℝ) / q : ℝ)) : UnitAddCircle) s =
      ∑ j : ZMod q, ((ZMod.stdAddChar ((p : ZMod q) * j) -
        ZMod.stdAddChar (-((p : ZMod q) * j))) / (2 * Complex.I)) *
        HurwitzZeta.hurwitzZetaOdd (ZMod.toAddCircle j) s := by
  have hPhi_odd := phi_odd q p
  have hL := ZMod.LFunction_def_odd hPhi_odd s
  have hsin := sinZeta_eq_LFunction q p hp hpq s
  have hlin := LFunction_sub_div q (fun j => ZMod.stdAddChar ((p : ZMod q) * j))
    (fun j => ZMod.stdAddChar (-((p : ZMod q) * j))) s
  rw [hsin, hlin, hL]
  have hqNe : (((q : ℕ)) : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have h1 : (((q : ℕ)) : ℂ) ^ s * ((((q : ℕ)) : ℂ) ^ (-s)) = 1 := by
    rw [← Complex.cpow_add _ _ hqNe]
    simp
  calc (((q : ℕ)) : ℂ) ^ s * ((((q : ℕ)) : ℂ) ^ (-s) *
      ∑ j : ZMod q, ((ZMod.stdAddChar ((p : ZMod q) * j) -
        ZMod.stdAddChar (-((p : ZMod q) * j))) / (2 * Complex.I)) *
        HurwitzZeta.hurwitzZetaOdd (ZMod.toAddCircle j) s)
      = ((((q : ℕ)) : ℂ) ^ s * ((((q : ℕ)) : ℂ) ^ (-s))) *
        ∑ j : ZMod q, ((ZMod.stdAddChar ((p : ZMod q) * j) -
          ZMod.stdAddChar (-((p : ZMod q) * j))) / (2 * Complex.I)) *
          HurwitzZeta.hurwitzZetaOdd (ZMod.toAddCircle j) s := by ring
    _ = _ := by rw [h1, one_mul]

private theorem zmod_sum_eq_range_sum (q p : ℕ) [NeZero q] (s : ℂ) :
    (∑ j : ZMod q, ((Real.sin (2 * Real.pi * p * j.val / q) : ℝ) : ℂ) *
      HurwitzZeta.hurwitzZetaOdd (ZMod.toAddCircle j) s)
    = ∑ j ∈ Finset.range q, ((Real.sin (2 * Real.pi * p * j / q) : ℝ) : ℂ) *
      HurwitzZeta.hurwitzZetaOdd ((((j : ℝ) / q : ℝ)) : UnitAddCircle) s := by
  let hequiv : (Fin q) ≃ (ZMod q) := (ZMod.finEquiv q).toEquiv
  let g : (ZMod q) → ℂ := fun j => ((Real.sin (2 * Real.pi * p * j.val / q) : ℝ) : ℂ) *
    HurwitzZeta.hurwitzZetaOdd (ZMod.toAddCircle j) s
  let f : ℕ → ℂ := fun j => ((Real.sin (2 * Real.pi * p * j / q) : ℝ) : ℂ) *
    HurwitzZeta.hurwitzZetaOdd ((((j : ℝ) / q : ℝ)) : UnitAddCircle) s
  have h1 : (∑ j : ZMod q, g j) = (∑ x : Fin q, g (hequiv x)) := by
    exact (Fintype.sum_equiv hequiv _ _ (fun _ => rfl)).symm
  have hval_all : ∀ x : Fin q, (hequiv x).val = (x.val : ℕ) := by
    intro x
    have hq : q ≠ 0 := NeZero.ne q
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
    rfl
  have h2 : (∑ x : Fin q, g (hequiv x)) = (∑ x : Fin q, f (x.val : ℕ)) := by
    apply Fintype.sum_congr _ _ _
    intro x
    simp only [g, f]
    have hval := hval_all x
    have hcirc : ZMod.toAddCircle (hequiv x) = ((((x.val : ℝ) / q : ℝ)) : UnitAddCircle) := by
      rw [ZMod.toAddCircle_apply, hval]
    rw [hval, hcirc]
  have h3 : (∑ x : Fin q, f (x.val : ℕ)) = (∑ j ∈ Finset.range q, f j) := by
    exact Fin.sum_univ_eq_sum_range f q
  calc (∑ j : ZMod q, g j) = (∑ x : Fin q, g (hequiv x)) := h1
    _ = (∑ x : Fin q, f (x.val : ℕ)) := h2
    _ = (∑ j ∈ Finset.range q, f j) := h3

private theorem sin_reflect (p q j : ℕ) (hq : 0 < q) (hj : j ≤ q) :
    Real.sin (2 * Real.pi * p * ((q - j : ℕ) : ℝ) / q)
      = -Real.sin (2 * Real.pi * p * (j : ℝ) / q) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  have hsub : (((q - j : ℕ)) : ℝ) = (q : ℝ) - (j : ℝ) := Nat.cast_sub hj
  have heq_nat : (2 * Real.pi * (p : ℝ) * (((q - j : ℕ)) : ℝ) / (q : ℝ))
      = (-(2 * Real.pi * (p : ℝ) * (j : ℝ) / (q : ℝ))) + (p : ℝ) * (2 * Real.pi) := by
    rw [hsub]
    field_simp
    ring
  have heq_int : (2 * Real.pi * (p : ℝ) * (((q - j : ℕ)) : ℝ) / (q : ℝ))
      = (-(2 * Real.pi * (p : ℝ) * (j : ℝ) / (q : ℝ))) + ((((p : ℕ) : ℤ)) : ℝ) * (2 * Real.pi) := by
    rw [Int.cast_natCast]
    exact heq_nat
  rw [heq_int]
  rw [Real.sin_add_int_mul_two_pi]
  rw [Real.sin_neg]

private theorem zodd_reflect (q j : ℕ) (hq : 0 < q) (hj : j ≤ q) (s : ℂ) :
    HurwitzZeta.hurwitzZetaOdd (((((q - j : ℕ) : ℝ) / q : ℝ)) : UnitAddCircle) s
      = -HurwitzZeta.hurwitzZetaOdd (((((j : ℝ) / q : ℝ))) : UnitAddCircle) s := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  have hsubR : ((((q - j : ℕ)) : ℝ)) = (q : ℝ) - (j : ℝ) := Nat.cast_sub hj
  have hreal : ((((q - j : ℕ) : ℝ) / (q : ℝ) : ℝ)) = (-(((j : ℝ) / (q : ℝ))) + 1 : ℝ) := by
    rw [hsubR]
    field_simp
    ring
  have hcirc : (((( ((((q - j : ℕ) : ℝ) / (q : ℝ) : ℝ)))) : UnitAddCircle))
      = -((((((j : ℝ) / (q : ℝ) : ℝ)))) : UnitAddCircle) := by
    rw [hreal]
    rw [AddCircle.coe_add]
    simp [AddCircle.coe_period]
  rw [hcirc]
  exact HurwitzZeta.hurwitzZetaOdd_neg _ _

private theorem f_reflect (p q j : ℕ) (hq : 0 < q) (hj : j ≤ q) (s : ℂ) :
    (((Real.sin (2 * Real.pi * p * ((q - j : ℕ) : ℝ) / q) : ℝ) : ℂ) *
      HurwitzZeta.hurwitzZetaOdd (((((q - j : ℕ) : ℝ) / q : ℝ)) : UnitAddCircle) s)
    = (((Real.sin (2 * Real.pi * p * (j : ℝ) / q) : ℝ) : ℂ) *
      HurwitzZeta.hurwitzZetaOdd (((((j : ℝ) / q : ℝ))) : UnitAddCircle) s) := by
  rw [sin_reflect p q j hq hj, zodd_reflect q j hq hj s]
  push_cast
  ring

private theorem range_double (p q m : ℕ) (hq : q = 2 * m + 1) (s : ℂ) :
    (∑ j ∈ Finset.range q, ((Real.sin (2 * Real.pi * p * j / q) : ℝ) : ℂ) *
      HurwitzZeta.hurwitzZetaOdd ((((j : ℝ) / q : ℝ)) : UnitAddCircle) s)
    = 2 * ∑ j ∈ Finset.Icc 1 m, ((Real.sin (2 * Real.pi * p * j / q) : ℝ) : ℂ) *
      HurwitzZeta.hurwitzZetaOdd ((((j : ℝ) / q : ℝ)) : UnitAddCircle) s := by
  subst hq
  have hq0 : 0 < 2 * m + 1 := by omega
  have hsplit : Finset.range (2 * m + 1) = ({0} ∪ Finset.Icc 1 m) ∪ Finset.Icc (m + 1) (2 * m) := by
    ext j
    simp [Finset.mem_range, Finset.mem_Icc, Finset.mem_union]
    omega
  rw [hsplit]
  have hdisjA : Disjoint ({0} : Finset ℕ) (Finset.Icc 1 m) := by
    rw [Finset.disjoint_left]
    intro j hj0 hjI
    simp at hj0
    simp [Finset.mem_Icc] at hjI
    omega
  have hdisjB : Disjoint (({0} : Finset ℕ) ∪ Finset.Icc 1 m) (Finset.Icc (m + 1) (2 * m)) := by
    rw [Finset.disjoint_left]
    intro j hjU hj2
    simp [Finset.mem_Icc] at hj2
    simp only [singleton_union, mem_insert, mem_Icc] at hjU
    rcases hjU with rfl | hj1 <;> omega
  rw [Finset.sum_union hdisjB, Finset.sum_union hdisjA, Finset.sum_singleton]
  have hz0 : ((Real.sin (2 * Real.pi * (p : ℝ) * ((0 : ℕ) : ℝ) / ((2 * m + 1 : ℕ) : ℝ)) : ℝ) : ℂ) *
      HurwitzZeta.hurwitzZetaOdd (((((0 : ℕ) : ℝ) / ((2 * m + 1 : ℕ) : ℝ) : ℝ)) : UnitAddCircle) s =
          0 := by
    simp
  rw [hz0, zero_add]
  have hpair : (∑ j ∈ Finset.Icc (m + 1) (2 * m),
      ((Real.sin (2 * Real.pi * (p : ℝ) * (j : ℝ) / ((2*m+1 : ℕ) : ℝ)) : ℝ) : ℂ) *
      HurwitzZeta.hurwitzZetaOdd ((((j : ℝ) / ((2*m+1 : ℕ) : ℝ) : ℝ)) : UnitAddCircle) s)
      = (∑ j ∈ Finset.Icc 1 m, ((Real.sin (2 * Real.pi * (p : ℝ) * (j : ℝ) / ((2*m+1 : ℕ) : ℝ)) : ℝ)
          : ℂ) *
        HurwitzZeta.hurwitzZetaOdd ((((j : ℝ) / ((2*m+1 : ℕ) : ℝ) : ℝ)) : UnitAddCircle) s) := by
    apply Finset.sum_nbij' (fun j => (2 * m + 1 - j)) (fun j => (2 * m + 1 - j))
    · intro a ha
      simp [Finset.mem_Icc] at ha ⊢
      omega
    · intro a ha
      simp [Finset.mem_Icc] at ha ⊢
      omega
    · intro a ha
      simp [Finset.mem_Icc] at ha
      omega
    · intro a ha
      simp [Finset.mem_Icc] at ha
      omega
    · intro a ha
      have haj : a ≤ 2 * m + 1 := by simp [Finset.mem_Icc] at ha; omega
      have h := f_reflect p (2*m+1) a hq0 haj s
      exact h.symm
  rw [hpair]
  ring

private theorem fourier_identity (p q m : ℕ) [NeZero q] (hp : 0 < p) (hpq : p < q)
    (hqm : q = 2 * m + 1) (s : ℂ) :
    (((q : ℕ) : ℂ) ^ s) * HurwitzZeta.sinZeta ((((p : ℝ) / q : ℝ)) : UnitAddCircle) s =
      2 * ∑ j ∈ Finset.Icc 1 m, ((Real.sin (2 * Real.pi * p * j / q) : ℝ) : ℂ) *
        HurwitzZeta.hurwitzZetaOdd ((((j : ℝ) / q : ℝ)) : UnitAddCircle) s := by
  have hqpow := qpow_mul_sinZeta q p hp hpq s
  have hphi_sum : (∑ j : ZMod q, ((ZMod.stdAddChar ((p : ZMod q) * j) -
        ZMod.stdAddChar (-((p : ZMod q) * j))) / (2 * Complex.I)) *
        HurwitzZeta.hurwitzZetaOdd (ZMod.toAddCircle j) s)
      = (∑ j : ZMod q, ((Real.sin (2 * Real.pi * p * j.val / q) : ℝ) : ℂ) *
        HurwitzZeta.hurwitzZetaOdd (ZMod.toAddCircle j) s) := by
    apply Fintype.sum_congr _ _ _
    intro j
    have h := phi_eq_sin q p hpq j
    rw [h]
  rw [hphi_sum] at hqpow
  have hrange := zmod_sum_eq_range_sum q p s
  rw [hrange] at hqpow
  have hdouble := range_double p q m hqm s
  rw [hdouble] at hqpow
  exact hqpow

private theorem left_eq_right_of_re_pos (p q m : ℕ) (hp : 0 < p) (hpq : p < q) (hqm : q = 2 * m + 1)
    (r : ℂ) (hr : 0 < r.re) :
    chapter7Entry19Left p q hp hpq r = chapter7Entry19Right p q r := by
  have hq0 : 0 < q := lt_trans hp hpq
  have : NeZero q := ⟨by omega⟩
  have hm_eq : (q - 1) / 2 = m := by omega
  have hleft := left_eq_sinZeta p q hp hpq r hr
  have hfour := fourier_identity p q m hp hpq hqm r
  have hright := right_eq_odd p q r
  rw [hm_eq] at hright
  have hqcast : ((((q : ℝ)) : ℂ)) = ((((q : ℕ)) : ℂ)) := Complex.ofReal_natCast q
  rw [hqcast] at hleft
  have hsum_eq : (∑ j ∈ Finset.Icc 1 m, ((Real.sin (2 * Real.pi * j * p / q) : ℝ) : ℂ) *
        (-2 * HurwitzZeta.hurwitzZetaOdd ((((j : ℝ) / q : ℝ)) : UnitAddCircle) r))
      = -2 * ∑ j ∈ Finset.Icc 1 m, ((Real.sin (2 * Real.pi * p * j / q) : ℝ) : ℂ) *
        HurwitzZeta.hurwitzZetaOdd ((((j : ℝ) / q : ℝ)) : UnitAddCircle) r := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have harg : (2 * Real.pi * (j : ℝ) * (p : ℝ) / (q : ℝ))
        = (2 * Real.pi * (p : ℝ) * (j : ℝ) / (q : ℝ)) := by ring
    rw [harg]
    ring
  rw [hsum_eq] at hright
  have hfour_cpow : Complex.cpow ((((q : ℕ)) : ℂ)) r *
        HurwitzZeta.sinZeta ((((p : ℝ) / q : ℝ)) : UnitAddCircle) r
      = 2 * ∑ j ∈ Finset.Icc 1 m, ((Real.sin (2 * Real.pi * p * j / q) : ℝ) : ℂ) *
        HurwitzZeta.hurwitzZetaOdd ((((j : ℝ) / q : ℝ)) : UnitAddCircle) r := hfour
  have hEq : -(Complex.cpow ((((q : ℕ)) : ℂ)) r) * Complex.sin (Real.pi * r / 2) *
        HurwitzZeta.sinZeta ((((p : ℝ) / q : ℝ)) : UnitAddCircle) r
      = Complex.sin (Real.pi * r / 2) *
        (-2 * ∑ j ∈ Finset.Icc 1 m, ((Real.sin (2 * Real.pi * p * j / q) : ℝ) : ℂ) *
          HurwitzZeta.hurwitzZetaOdd ((((j : ℝ) / q : ℝ)) : UnitAddCircle) r) := by
    have h := hfour_cpow
    calc -(Complex.cpow ((((q : ℕ)) : ℂ)) r) * Complex.sin (Real.pi * r / 2) *
          HurwitzZeta.sinZeta ((((p : ℝ) / q : ℝ)) : UnitAddCircle) r
        = -Complex.sin (Real.pi * r / 2) * (Complex.cpow ((((q : ℕ)) : ℂ)) r *
          HurwitzZeta.sinZeta ((((p : ℝ) / q : ℝ)) : UnitAddCircle) r) := by ring
      _ = -Complex.sin (Real.pi * r / 2) *
          (2 * ∑ j ∈ Finset.Icc 1 m, ((Real.sin (2 * Real.pi * p * j / q) : ℝ) : ℂ) *
            HurwitzZeta.hurwitzZetaOdd ((((j : ℝ) / q : ℝ)) : UnitAddCircle) r) := by rw [h]
      _ = _ := by ring
  rw [hleft, hright]
  exact hEq

/-- **Ramanujan's functional equation for $\varphi$ at rationals with odd denominator.** For
$-1 < x < 0$ and $r \in \mathbb{C}$ let $\varphi_r(x) = \zeta(-r) - \zeta(-r, x + 1)$, where
$\zeta$ is the Riemann zeta function and $\zeta(s, a)$ the Hurwitz zeta function. Let $p$ and $q$
be natural numbers with $0 < p < q$ and $q$ odd, and for $r \in \mathbb{C}$ put
$L(r) = \frac{(2\pi q)^r}{4\,\Gamma(r)} \bigl(\varphi_{r-1}(p/q - 1) - \varphi_{r-1}(-p/q)\bigr)$
and $R(r) = \sin(\pi r/2) \sum_{j=1}^{(q-1)/2} \sin(2\pi j p/q)\, D_j(r)$, where
$D_j(r) = \varphi_{-r}(j/q - 1) - \varphi_{-r}(-j/q)$. Then $L$ and $R$ are meromorphic on
$\mathbb{C}$ and agree outside a closed discrete subset of $\mathbb{C}$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 7.
-/
theorem ramanujan_part1_ch7_entry19_zetanegint
    (p q : ℕ) (hp : 0 < p) (hpq : p < q) (hq : Odd q) :
    MeromorphicOn (chapter7Entry19Left p q hp hpq) Set.univ ∧
      MeromorphicOn (chapter7Entry19Right p q) Set.univ ∧
      (chapter7Entry19Left p q hp hpq) =ᶠ[codiscrete ℂ]
        (chapter7Entry19Right p q) := by
  refine ⟨left_meromorphic p q hp hpq, right_meromorphic p q, ?_⟩
  obtain ⟨m, hqm⟩ := hq
  have hL : AnalyticOnNhd ℂ (chapter7Entry19Left p q hp hpq) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (left_differentiable p q hp hpq)
  have hR : AnalyticOnNhd ℂ (chapter7Entry19Right p q) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (right_differentiable p q)
  have hev : (chapter7Entry19Left p q hp hpq) =ᶠ[nhds (1 : ℂ)]
      (chapter7Entry19Right p q) := by
    have hmem : (1 : ℂ) ∈ {z | (0 : ℝ) < z.re} := by norm_num
    have hnb : {z | (0 : ℝ) < z.re} ∈ nhds (1 : ℂ) :=
      (Complex.isOpen_re_gt 0).mem_nhds hmem
    filter_upwards [hnb] with z hz using left_eq_right_of_re_pos p q m hp hpq hqm z hz
  have heq : (chapter7Entry19Left p q hp hpq) = (chapter7Entry19Right p q) :=
    hL.eq_of_eventuallyEq hR hev
  exact Filter.EventuallyEq.of_eq heq

end
end Entry19Zetanegint
end MathlibExt.Analysis.Ramanujan.Part1Ch7
end
