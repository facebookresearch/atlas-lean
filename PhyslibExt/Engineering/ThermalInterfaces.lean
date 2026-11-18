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
model only.

## ii. Key results

- `Engineering.ThermalInterfaces.thermalInterfaceTemp_succ_sub`:
  adjacent interface drop.
- `Engineering.ThermalInterfaces.thermalInterfaceTemp_last_sub_film`:
  end matching at the
  outside air temperature.

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


/-- Total series resistance of `n` planar layers and two films
at common area `A` (the same formula as the series-resistance
package). -/
noncomputable def thermalTotalResistance {n : ℕ} (A hin hout : ℝ)
    (L k : ℕ → ℝ) : ℝ :=
  1 / (hin * A) + (∑ i ∈ Finset.range n, L i / (k i * A))
    + 1 / (hout * A)

/-- Interface temperature after the inside film and the first
`m` layers, reconstructed from the inside air temperature
`Tin` and the common steady heat rate `Q` by cumulative
resistance drops. The modeled interfaces are `m ≤ n`. -/
noncomputable def thermalInterfaceTemp {n : ℕ} (A hin Tin Q : ℝ)
    (L k : ℕ → ℝ) (m : ℕ) : ℝ :=
  Tin - Q * (1 / (hin * A)
    + ∑ i ∈ Finset.range m, L i / (k i * A))

/-- Adjacent interface temperatures within the modeled layers
differ by the layer drop `Q * (L m / (k m * A))`. -/
theorem thermalInterfaceTemp_succ_sub {n m : ℕ}
    (A hin Tin Q : ℝ) (L k : ℕ → ℝ) (_hm : m < n) :
    thermalInterfaceTemp (n := n) A hin Tin Q L k m
        - thermalInterfaceTemp (n := n) A hin Tin Q L k (m + 1)
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
    thermalInterfaceTemp (n := n) A hin Tin
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

end Engineering.ThermalInterfaces
