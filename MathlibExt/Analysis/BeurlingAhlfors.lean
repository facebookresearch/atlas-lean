/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace MathlibExt.Analysis.BeurlingAhlfors

open MeasureTheory Filter Topology

/-!
# The Beurling--Ahlfors transform constant

The principal-value singular integral defining the Beurling--Ahlfors
transform (totalized as a `Filter.limUnder` of truncated integrals), its
`L^p` operator norm as an infimum of admissible bound constants over
strongly measurable functions, and
`C₅₄ = sup_{1<p<∞} ‖B‖ₚ / (p* - 1)`.

Source: Optimization Problems, record 54a, "Beurling–Ahlfors transform
constant", frozen at teorth/optimizationproblems commit
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`; `constants/54a.md` SHA-256
`a4e91439ac5a3b22b692ed0bb1cf097b2eea1dc486d57520b6276b509e09b54e`.

Scope notes: `B` is modeled pointwise on functions rather than as a
bounded operator on `L^p` quotient classes; convergence of the
principal value, `L^p` boundedness, and the conversion of the atomic
norm bounds in `WantedExt` into bounds on `beurlingAhlforsConstant`
are not formalized.
-/

/-- `p* = max (p, p / (p - 1))`, the exponent factor in the Beurling--
Ahlfors norm problem. -/
noncomputable def pstar (p : ℝ) : ℝ :=
  max p (p / (p - 1))

theorem pstar_two : pstar 2 = 2 := by
  rw [pstar]
  norm_num

theorem two_le_pstar {p : ℝ} (hp : 1 < p) : 2 ≤ pstar p := by
  rw [pstar]
  by_cases h : 2 ≤ p
  · exact h.trans (le_max_left _ _)
  · have hp1 : (0:ℝ) < p - 1 := by linarith
    have : (2:ℝ) ≤ p / (p - 1) := by
      rw [le_div_iff₀ hp1]
      nlinarith
    exact this.trans (le_max_right _ _)

theorem one_le_pstar_sub_one {p : ℝ} (hp : 1 < p) : 1 ≤ pstar p - 1 := by
  have h := two_le_pstar hp
  linarith

/-- The truncated Beurling--Ahlfors integral at cutoff `ε`, on arbitrary
complex functions. -/
noncomputable def beurlingTrunc (ε : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  -(1 / ((Real.pi : ℝ) : ℂ)) * ∫ w in { w : ℂ | ε < ‖w - z‖ }, f w / (z - w) ^ 2

/-- The Beurling--Ahlfors transform as the principal-value limit of the
truncated integrals, totalized by `Filter.limUnder`. For the `L^p` functions
of the source theory the limit exists almost everywhere; no existence
or representability statement is made here. -/
noncomputable def beurlingTransform (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  Filter.limUnder (𝓝[Set.Ioi 0] 0) fun ε => beurlingTrunc ε f z

/-- `C` is an admissible `L^p` bound constant for the transform, over
all strongly measurable functions, in extended `L^p` norms. -/
def IsBound (p C : ℝ) : Prop :=
  ∀ f : ℂ → ℂ, AEStronglyMeasurable f volume →
    eLpNorm (beurlingTransform f) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume

theorem IsBound.mono {p C C' : ℝ} (h : IsBound p C) (hCC : C ≤ C') :
    IsBound p C' := by
  intro f hf
  refine (h f hf).trans ?_
  gcongr

/-- The operator norm `‖B‖ₚ`, totalized as the infimum of nonnegative
admissible bound constants in this model. The totalization takes the
value `0` when there is no admissible bound at all, so norm inequalities
alone do not assert boundedness; use `beurlingNorm_le_of_isBound` to
derive them from an actual admissible bound. -/
noncomputable def beurlingNorm (p : ℝ) : ℝ :=
  sInf { C : ℝ | 0 ≤ C ∧ IsBound p C }

/-- Characteristic lemma for the totalized norm: any nonnegative
admissible bound bounds `beurlingNorm p` above. This is the correct way
to turn a concrete `L^p` bound into a statement about `beurlingNorm`. -/
theorem beurlingNorm_le_of_isBound {p C : ℝ} (hC : 0 ≤ C) (h : IsBound p C) :
    beurlingNorm p ≤ C :=
  csInf_le ⟨0, fun _ hD => hD.1⟩ ⟨hC, h⟩

/-- The Beurling--Ahlfors constant `C₅₄ = sup_{1<p<∞} ‖B‖ₚ / (p* - 1)`,
totalized by real `sSup`. -/
noncomputable def beurlingAhlforsConstant : ℝ :=
  sSup { r : ℝ | ∃ p : ℝ, 1 < p ∧ r = beurlingNorm p / (pstar p - 1) }

/-- Iwaniec's conjecture: `‖B‖ₚ = p* - 1` for every `1 < p` (equivalently
the constant above equals `1`, given Lehto's lower bound). Stated as a
proposition only. -/
def IwaniecConjecture : Prop :=
  ∀ p : ℝ, 1 < p → beurlingNorm p = pstar p - 1

end MathlibExt.Analysis.BeurlingAhlfors
