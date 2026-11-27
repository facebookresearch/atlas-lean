/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Wall interface temperatures from cumulative resistance

## i. Overview

For steady one-dimensional conduction through `n` planar
layers and two surface films at common area `A`, the total
series resistance is the sum of the two film resistances and
the layer resistances `L i / (k i * A)`. With the common heat
rate `Q`, the temperature at the interface after the inside
film and the first `m` layers is the inside air temperature
minus `Q` times the cumulative resistance up to that
interface. Adjacent modeled interfaces differ by the layer
drop, and the reconstruction with the recovered heat rate
matches the outside air temperature after the final film
drop. This is the steady, one-dimensional, constant-property
model only. The definitions below are the displayed algebraic
formulas for arbitrary real inputs; the physical
series-resistance interpretation is the positive domain
`A, hin, hout > 0`, layer conductivities `k i > 0`, and
nonnegative layer thicknesses `L i ≥ 0`, where the total
resistance is positive.

## ii. Key results

- `Engineering.ThermalInterfaces.thermalInterfaceTemp_succ_sub`:
  adjacent interface drop.
- `Engineering.ThermalInterfaces.thermalInterfaceTemp_last_sub_film`:
  end matching at the
  outside air temperature.
- `Engineering.ThermalInterfaces.thermalTotalResistance_pos` and
  `Engineering.ThermalInterfaces.thermalInterfaceTemp_last_sub_film_of_pos`:
  the physical positive-domain form.

## iii. Table of contents

- A. Interface reconstruction

## iv. References

- F. P. Incropera, D. P. DeWitt, T. L. Bergman and
  A. S. Lavine, *Fundamentals of Heat and Mass Transfer*
  (plane-wall series resistance and interface temperatures).
-/

@[expose] public section

/-! ## A. Interface reconstruction -/
namespace Engineering.ThermalInterfaces


/-- Total series-resistance formula for `n` planar layers and
two films at common area `A` (the same formula as the
series-resistance package). As a definition this is the
totalized algebraic formula; its physical resistance
interpretation is the positive domain in
`thermalTotalResistance_pos`. -/
noncomputable def thermalTotalResistance {n : ℕ} (A hin hout : ℝ)
    (L k : ℕ → ℝ) : ℝ :=
  1 / (hin * A) + (∑ i ∈ Finset.range n, L i / (k i * A))
    + 1 / (hout * A)

/-- Interface temperature after the inside film and the first
`m` layers, reconstructed from the inside air temperature
`Tin` and the common steady heat rate `Q` by cumulative
resistance drops. The total layer count is not part of
this cumulative definition; end matching chooses `m = n`. -/
noncomputable def thermalInterfaceTemp (A hin Tin Q : ℝ)
    (L k : ℕ → ℝ) (m : ℕ) : ℝ :=
  Tin - Q * (1 / (hin * A)
    + ∑ i ∈ Finset.range m, L i / (k i * A))

/-- Adjacent cumulative interface temperatures
differ by the layer drop `Q * (L m / (k m * A))`. -/
theorem thermalInterfaceTemp_succ_sub {m : ℕ}
    (A hin Tin Q : ℝ) (L k : ℕ → ℝ) :
    thermalInterfaceTemp A hin Tin Q L k m
        - thermalInterfaceTemp A hin Tin Q L k (m + 1)
      = Q * (L m / (k m * A)) := by
  unfold thermalInterfaceTemp
  rw [Finset.sum_range_succ]
  have hA : Q * (1 / (hin * A)
          + (∑ x ∈ Finset.range m, L x / (k x * A) + L m / (k m * A)))
        = Q * (1 / (hin * A) + ∑ x ∈ Finset.range m, L x / (k x * A))
          + Q * (L m / (k m * A)) := by
    rw [← add_assoc, mul_add]
  rw [hA, sub_add_eq_sub_sub]
  exact sub_sub_cancel _ _

/-- End matching: with the recovered heat rate
`Q = (Tin - Tout) / R` for nonzero total resistance `R`, the
last interface temperature minus the outside film drop is the
outside air temperature `Tout`. -/
theorem thermalInterfaceTemp_last_sub_film {n : ℕ}
    {A hin hout Tin Tout : ℝ} (L k : ℕ → ℝ)
    (hR : thermalTotalResistance (n := n) A hin hout L k ≠ 0) :
    thermalInterfaceTemp A hin Tin
        ((Tin - Tout)
          / thermalTotalResistance (n := n) A hin hout L k) L k n
      - ((Tin - Tout)
          / thermalTotalResistance (n := n) A hin hout L k)
        * (1 / (hout * A))
    = Tout := by
  unfold thermalTotalResistance at hR
  unfold thermalInterfaceTemp thermalTotalResistance
  set S : ℝ := ∑ i ∈ Finset.range n, L i / (k i * A) with hS
  set a : ℝ := 1 / (hin * A) with ha
  set b : ℝ := 1 / (hout * A) with hb
  have hQ : (Tin - Tout) / (a + S + b) * (a + S)
        + (Tin - Tout) / (a + S + b) * b = Tin - Tout := by
    rw [← mul_add]
    exact div_mul_cancel₀ _ hR
  rw [sub_sub, hQ]
  exact sub_sub_cancel _ _

/-- On the physical positive domain (positive common area and
film coefficients, positive layer conductivities, and
nonnegative layer thicknesses), the total series resistance is
positive. -/
lemma thermalTotalResistance_pos {n : ℕ}
    {A hin hout : ℝ} (hA : 0 < A) (hhin : 0 < hin)
    (hhout : 0 < hout) (L k : ℕ → ℝ)
    (hL : ∀ i : ℕ, i < n → 0 ≤ L i)
    (hk : ∀ i : ℕ, i < n → 0 < k i) :
    0 < thermalTotalResistance (n := n) A hin hout L k := by
  unfold thermalTotalResistance
  have hfilm1 : 0 < 1 / (hin * A) :=
    one_div_pos.mpr (mul_pos hhin hA)
  have hsum : 0 ≤ ∑ i ∈ Finset.range n, L i / (k i * A) := by
    apply Finset.sum_nonneg
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    exact div_nonneg (hL i hi') (le_of_lt (mul_pos (hk i hi') hA))
  have hfilm2 : 0 < 1 / (hout * A) :=
    one_div_pos.mpr (mul_pos hhout hA)
  linarith

/-- Physical positive-domain end matching: with positive area
and film coefficients, positive layer conductivities, and
nonnegative layer thicknesses, the recovered heat rate is
formed with a positive total resistance and the last interface
minus the outside film drop is the outside air temperature. -/
lemma thermalInterfaceTemp_last_sub_film_of_pos {n : ℕ}
    {A hin hout Tin Tout : ℝ} (hA : 0 < A) (hhin : 0 < hin)
    (hhout : 0 < hout) (L k : ℕ → ℝ)
    (hL : ∀ i : ℕ, i < n → 0 ≤ L i)
    (hk : ∀ i : ℕ, i < n → 0 < k i) :
    thermalInterfaceTemp A hin Tin
        ((Tin - Tout)
          / thermalTotalResistance (n := n) A hin hout L k) L k n
      - ((Tin - Tout)
          / thermalTotalResistance (n := n) A hin hout L k)
        * (1 / (hout * A))
    = Tout :=
  thermalInterfaceTemp_last_sub_film L k
    (ne_of_gt (thermalTotalResistance_pos hA hhin hhout L k hL hk))

end Engineering.ThermalInterfaces
