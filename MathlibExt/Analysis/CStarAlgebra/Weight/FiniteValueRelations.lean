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

public import MathlibExt.Analysis.CStarAlgebra.Weight.FiniteSquareSubmodule
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Finite-positive value relations for the actual weight pairing

The real coordinates of finite-positive weight values respect equality,
addition and real scaling of their original signed differences. Every
relation below is proved from the global positive weight's own laws;
no scalar extension or positive-inner certificate is supplied.

The final definitions polarize the actual finite-square values on the
literal complex domain. Their Hermitian and scalar laws are constructor
obligations for the weight pre-inner-product structure, not assumed data.
The imaginary coordinate uses the first argument multiplied by i, matching
a complex inner product linear in its second argument.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped NNReal ENNReal

namespace CStarAlgebra.ScalarWeight

noncomputable section

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

/-- Finite positive additivity is actual additivity of the original real values. -/
theorem Weight.finite_toReal_add (φ : Weight A) (a b : PositiveElement A)
    (ha : φ.value a < ⊤) (hb : φ.value b < ⊤) :
    (φ.value (positiveAdd a b)).toReal = (φ.value a).toReal + (φ.value b).toReal := by
  rw [φ.add_value, ENNReal.toReal_add ha.ne hb.ne]

/-- Real coordinates of finite positive scaling obey the original scalar law. -/
theorem Weight.toReal_positiveSmul (φ : Weight A) (r : NNReal) (a : PositiveElement A) :
    (φ.value (positiveSmul r a)).toReal = (r : ℝ) * (φ.value a).toReal := by
  rw [φ.smul_value, ENNReal.toReal_mul, ENNReal.coe_toReal]

/-- Equal original positive differences have equal differences of their finite weight values. -/
theorem Weight.finite_toReal_sub_eq_sub (φ : Weight A) (a b c d : PositiveElement A)
    (ha : φ.value a < ⊤) (hb : φ.value b < ⊤)
    (hc : φ.value c < ⊤) (hd : φ.value d < ⊤)
    (h : (a : A) - (b : A) = (c : A) - (d : A)) :
    (φ.value a).toReal - (φ.value b).toReal = (φ.value c).toReal - (φ.value d).toReal := by
  have hadd : (a : A) + (d : A) = (c : A) + (b : A) := by
    calc
      (a : A) + (d : A) = ((a : A) - (b : A)) + ((b : A) + (d : A)) := by abel
      _ = ((c : A) - (d : A)) + ((b : A) + (d : A)) := by rw [h]
      _ = (c : A) + (b : A) := by abel
  have hpositive : positiveAdd a d = positiveAdd c b := Subtype.ext hadd
  have hvalues := congrArg (fun z : PositiveElement A => (φ.value z).toReal) hpositive
  rw [φ.finite_toReal_add a d ha hd, φ.finite_toReal_add c b hc hb] at hvalues
  linarith

/-- The real values preserve addition of original finite-positive differences. -/
theorem Weight.finite_toReal_sub_eq_add_sub
    (φ : Weight A) (a b c d e f : PositiveElement A)
    (ha : φ.value a < ⊤) (hb : φ.value b < ⊤)
    (hc : φ.value c < ⊤) (hd : φ.value d < ⊤)
    (he : φ.value e < ⊤) (hf : φ.value f < ⊤)
    (h : (a : A) - (b : A) = ((c : A) - (d : A)) + ((e : A) - (f : A))) :
    (φ.value a).toReal - (φ.value b).toReal =
      ((φ.value c).toReal - (φ.value d).toReal) + ((φ.value e).toReal - (φ.value f).toReal) := by
  have hraw : (a : A) - (b : A) =
      (positiveAdd c e : A) - (positiveAdd d f : A) := by
    rw [h]
    change ((c : A) - (d : A)) + ((e : A) - (f : A)) =
      ((c : A) + (e : A)) - ((d : A) + (f : A))
    abel
  have hvalues := φ.finite_toReal_sub_eq_sub a b (positiveAdd c e) (positiveAdd d f)
    ha hb ((φ.finite_add_iff c e).2 ⟨hc, he⟩) ((φ.finite_add_iff d f).2 ⟨hd, hf⟩) hraw
  rw [φ.finite_toReal_add c e hc he, φ.finite_toReal_add d f hd hf] at hvalues
  linarith

/-- Original nonnegative-real scaling of finite-positive differences scales their real values. -/
theorem Weight.finite_toReal_sub_eq_nonneg_smul_sub
    (φ : Weight A) (r : NNReal) (a b c d : PositiveElement A)
    (ha : φ.value a < ⊤) (hb : φ.value b < ⊤)
    (hc : φ.value c < ⊤) (hd : φ.value d < ⊤)
    (h : (a : A) - (b : A) = (r : ℝ) • ((c : A) - (d : A))) :
    (φ.value a).toReal - (φ.value b).toReal =
      (r : ℝ) * ((φ.value c).toReal - (φ.value d).toReal) := by
  have hraw : (a : A) - (b : A) =
      (positiveSmul r c : A) - (positiveSmul r d : A) := by
    change (a : A) - (b : A) = (r : ℝ) • (c : A) - (r : ℝ) • (d : A)
    rw [← smul_sub]
    exact h
  have hvalues := φ.finite_toReal_sub_eq_sub a b (positiveSmul r c) (positiveSmul r d)
    ha hb (φ.finite_positiveSmul r c hc) (φ.finite_positiveSmul r d hd) hraw
  rw [φ.toReal_positiveSmul r c, φ.toReal_positiveSmul r d] at hvalues
  calc
    (φ.value a).toReal - (φ.value b).toReal =
        (r : ℝ) * (φ.value c).toReal - (r : ℝ) * (φ.value d).toReal := hvalues
    _ = _ := by ring

/-- Every real scaling of an original finite-positive difference scales its real value. -/
theorem Weight.finite_toReal_sub_eq_real_smul_sub
    (φ : Weight A) (r : ℝ) (a b c d : PositiveElement A)
    (ha : φ.value a < ⊤) (hb : φ.value b < ⊤)
    (hc : φ.value c < ⊤) (hd : φ.value d < ⊤)
    (h : (a : A) - (b : A) = r • ((c : A) - (d : A))) :
    (φ.value a).toReal - (φ.value b).toReal =
      r * ((φ.value c).toReal - (φ.value d).toReal) := by
  by_cases hr : 0 ≤ r
  · exact φ.finite_toReal_sub_eq_nonneg_smul_sub (NNReal.mk r hr) a b c d ha hb hc hd h
  · have hrneg : 0 ≤ -r := le_of_lt (neg_pos.mpr (lt_of_not_ge hr))
    have hraw : (a : A) - (b : A) = (-r) • ((d : A) - (c : A)) := by
      rw [h]
      simp only [neg_smul, smul_sub]
      abel
    have hvalues := φ.finite_toReal_sub_eq_nonneg_smul_sub
      (NNReal.mk (-r) hrneg) a b d c ha hb hd hc hraw
    change (φ.value a).toReal - (φ.value b).toReal =
      (-r) * ((φ.value d).toReal - (φ.value c).toReal) at hvalues
    calc
      (φ.value a).toReal - (φ.value b).toReal =
          (-r) * ((φ.value d).toReal - (φ.value c).toReal) := hvalues
      _ = _ := by ring

/-- The actual finite-square value, where the original ENNReal weight value is finite. -/
def Weight.finiteSquareValue (φ : Weight A) (x : φ.finiteSquareSubmodule) : ℝ :=
  (φ.value (leftSquare (x : A))).toReal

/-- The real polarization of actual finite-square values on the literal domain. -/
def Weight.finiteSquarePolarRe (φ : Weight A) (x y : φ.finiteSquareSubmodule) : ℝ :=
  (φ.finiteSquareValue (x + y) - φ.finiteSquareValue (x - y)) / 4

/-- The original scalar-weight polarization, with the second-variable-linear complex sign. -/
def Weight.finiteSquarePolarInner (φ : Weight A) (x y : φ.finiteSquareSubmodule) : ℂ :=
  ⟨φ.finiteSquarePolarRe x y, φ.finiteSquarePolarRe (Complex.I • x) y⟩

end

end CStarAlgebra.ScalarWeight
