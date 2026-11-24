/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Milnor.K2Derived

/-!
# Symmetry and torsion laws for `K₂` symbols

This module proves elementary symmetry properties of binary symbols
`{a,b}` in `K₂^M(F)`:

* diagonal reduction `{a,a} = {a,-1}`, identifying the self-symbol with
  the 2-torsion element `{a,-1}`;
* skew-symmetry `{a,b} + {b,a} = 0`, obtained from `{ab,-ab}=0`;
* anticommutativity `{a,b} = -{b,a}`.

These are the textbook consequences of the Steinberg relation
`{a,1-a}=0` and bimultiplicativity that yield
`{a,-a}=0` and `{a,-1}` 2-torsion.
-/

@[expose] public section

namespace MilnorK
namespace MilnorKRing

variable {F : Type*} [Field F]

/-- Diagonal reduction in `K₂`: `{a,a} = {a,-1}`.

The self-symbol is 2-torsion-related via `{a,-a}=0` and right bilinearity.
Writing `{a,-a}= {a,-1}+{a,a}=0` gives `{a,a}=-{a,-1}`, and
`{a,-1}+{a,-1}=0` forces `-{a,-1}={a,-1}`. -/
theorem k2Symbol_a_a (a : Fˣ) :
    k2Symbol (F := F) a a = k2Symbol a (-1 : Fˣ) := by
  have hvan : k2Symbol (F := F) a (-a) = 0 := k2Symbol_a_neg_a a
  have h_expand :
      k2Symbol (F := F) a (-a) =
        k2Symbol (F := F) a (-1 : Fˣ) + k2Symbol a a :=
    k2Symbol_neg_right a a
  have h_sum :
      k2Symbol (F := F) a (-1 : Fˣ) + k2Symbol (F := F) a a = 0 := by
    rw [← h_expand]
    exact hvan
  have h_two :
      k2Symbol (F := F) a (-1 : Fˣ) + k2Symbol (F := F) a (-1 : Fˣ) = 0 :=
    k2Symbol_neg_one_add_self_right a
  have h_aa_eq_neg :
      k2Symbol (F := F) a a = - k2Symbol (F := F) a (-1 : Fˣ) :=
    eq_neg_of_add_eq_zero_right h_sum
  have h_neg_eq :
      - k2Symbol (F := F) a (-1 : Fˣ) =
        k2Symbol (F := F) a (-1 : Fˣ) :=
    neg_eq_of_add_eq_zero_right h_two
  calc
    k2Symbol (F := F) a a = - k2Symbol (F := F) a (-1 : Fˣ) := h_aa_eq_neg
    _ = k2Symbol (F := F) a (-1 : Fˣ) := h_neg_eq

/-- Skew-symmetry of `K₂` symbols: `{a,b} + {b,a} = 0`.

From the vanishing `{(ab),-(ab)}=0` and bimultiplicativity,
`{a,-ab}+ {b,-ab}=0`. Expanding `-ab = (-a)b = (-b)a` and cancelling the
terms `{a,-a}=0` and `{b,-b}=0` leaves the symmetric sum. -/
theorem k2Symbol_add_swap (a b : Fˣ) :
    k2Symbol (F := F) a b + k2Symbol b a = 0 := by
  have h_zero : k2Symbol (F := F) (a * b) (-(a * b)) = 0 :=
    k2Symbol_a_neg_a (a * b)
  have h_expand_left :
      k2Symbol (F := F) (a * b) (-(a * b)) =
        k2Symbol a (-(a * b)) + k2Symbol b (-(a * b)) :=
    k2Symbol_mul_left a b (-(a * b))
  have h_eq1 : (-(a * b) : Fˣ) = (-a : Fˣ) * b := by
    ext
    simp
  have h_eq2 : (-(a * b) : Fˣ) = (-b : Fˣ) * a := by
    ext
    simp [mul_comm]
  have h1 : k2Symbol (F := F) a (-(a * b)) =
      k2Symbol a (-a) + k2Symbol a b := by
    calc
      k2Symbol (F := F) a (-(a * b)) =
          k2Symbol a ((-a : Fˣ) * b) := by rw [h_eq1]
      _ = k2Symbol a (-a) + k2Symbol a b :=
        k2Symbol_mul_right a (-a) b
  have h2 : k2Symbol (F := F) b (-(a * b)) =
      k2Symbol b (-b) + k2Symbol b a := by
    calc
      k2Symbol (F := F) b (-(a * b)) =
          k2Symbol b ((-b : Fˣ) * a) := by rw [h_eq2]
      _ = k2Symbol b (-b) + k2Symbol b a :=
        k2Symbol_mul_right b (-b) a
  have h_a : k2Symbol (F := F) a (-a) = 0 := k2Symbol_a_neg_a a
  have h_b : k2Symbol (F := F) b (-b) = 0 := k2Symbol_a_neg_a b
  have h_sum :
      k2Symbol (F := F) a (-a) + k2Symbol a b +
        (k2Symbol (F := F) b (-b) + k2Symbol b a) = 0 := by
    calc
      k2Symbol (F := F) a (-a) + k2Symbol a b +
          (k2Symbol (F := F) b (-b) + k2Symbol b a)
        = (k2Symbol (F := F) a (-a) + k2Symbol a b) +
          (k2Symbol (F := F) b (-b) + k2Symbol b a) := by
        rw [add_assoc]
      _ = k2Symbol (F := F) a (-(a * b)) +
          k2Symbol b (-(a * b)) := by rw [← h1, ← h2]
      _ = k2Symbol (F := F) (a * b) (-(a * b)) := by rw [← h_expand_left]
      _ = 0 := h_zero
  have h_sum' :
      k2Symbol (F := F) a b + k2Symbol b a = 0 := by
    simpa only [h_a, h_b, zero_add, add_zero] using h_sum
  exact h_sum'

/-- Anticommutativity of `K₂` symbols: `{a,b} = -{b,a}`.

Reformulation of `k2Symbol_add_swap` via `a = -b ↔ a + b = 0` in
the additive group `K₂^M(F)`. -/
theorem k2Symbol_anticomm (a b : Fˣ) :
    k2Symbol (F := F) a b = - k2Symbol b a :=
  eq_neg_iff_add_eq_zero.mpr (k2Symbol_add_swap a b)

end MilnorKRing
end MilnorK
