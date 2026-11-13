/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.GHSLebowitz
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.MagnetizationConcavity

/-!
# The GHS inequality and the susceptibility bound

The Griffiths–Hurst–Sherman inequality for finite ferromagnetic Ising models, with its consequences:
concavity of the magnetization in the field and `χ(h) ≤ 1/h`.

## i. Overview

For a finite graph with nonnegative uniform coupling `β` and field `h ≥ 0`, the third Ursell
function `u₃(o, x, y) = ⟨σ_oσ_xσ_y⟩ - ⟨σ_o⟩⟨σ_xσ_y⟩ - ⟨σ_oσ_x⟩⟨σ_y⟩ - ⟨σ_oσ_y⟩⟨σ_x⟩ +
2⟨σ_o⟩⟨σ_x⟩⟨σ_y⟩` is nonpositive (the GHS inequality). Here this is derived from Lebowitz's
duplicated-variable proof, and it gives the sign condition `GHSSignDominance` at every field.

Since `∂²_h ⟨σ_o⟩ = β² ∑_{x,y} u₃(o, x, y)`, the magnetization is concave on `[0, ∞)`. Together with
`⟨σ_o⟩_{β,0} = 0` this bounds the susceptibility by `1/h`.

## ii. Key results

- `ghs_signDominance` : the GHS inequality `u₃(o, x, y) ≤ 0` for distinct sites
- `ghs_magnetization_concaveOn` : concavity of `h ↦ ⟨σ_o⟩` on `[0, ∞)`
- `ghs_susceptibility_le_inv_field` : `χ(h) = β ∑_x Cov(σ_o, σ_x)` and `χ(h) ≤ 1/h` for `h > 0`

## iii. Table of contents

- A. The GHS inequality and its consequences

## iv. References

- R. B. Griffiths, C. A. Hurst, S. Sherman, "Concavity of magnetization of an Ising ferromagnet in a
  positive external field", J. Math. Phys. 11 (1970) 790–795
- J. L. Lebowitz, "GHS and other inequalities", Comm. Math. Phys. 35 (1974) 87–92

-/

@[expose] public section

open scoped BigOperators
open Set SimpleGraph

namespace StatMech
namespace Sharpness

open Ising Walls Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. The GHS inequality and its consequences -/

/-- The Griffiths–Hurst–Sherman inequality: for `β ≥ 0` and `h ≥ 0`, the third Ursell function
`u₃(o, x, y)` is nonpositive for distinct sites. Reference: R. B. Griffiths, C. A. Hurst, S.
Sherman, "Concavity of magnetization of an Ising ferromagnet in a positive external field", J. Math.
Phys. 11 (1970) 790–795; proof via J. L. Lebowitz, "GHS and other inequalities", Comm. Math. Phys.
35 (1974) 87–92. -/
theorem ghs_signDominance (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) :
    GHSSignDominance G β h o := by
  intro x y hox _ _
  have hpair := ghsL_pair G β h hβ hh o x y hox
  rw [← sub_nonpos, ghsThreePoint_eq_ursell] at hpair
  simpa [eg_ursell3] using hpair

/-- GHS concavity: for `β ≥ 0` the magnetization `h ↦ ⟨σ_o⟩_{β,h}` is concave on `[0, ∞)`.
Reference: R. B. Griffiths, C. A. Hurst, S. Sherman, "Concavity of magnetization of an Ising
ferromagnet in a positive external field", J. Math. Phys. 11 (1970) 790–795. -/
theorem ghs_magnetization_concaveOn (β : ℝ) (hβ : 0 ≤ β) (o : V) :
    ConcaveOn ℝ (Ici 0) (fun h => isingExpectation G β h (fun s => spin s o)) :=
  gc4_magnetization_concaveOn G β hβ o
    (fun h hh => ghs_signDominance G β h hβ hh o)

/-- The GHS susceptibility bound: for `β ≥ 0` and `h > 0`, the field derivative of the magnetization
equals `β ∑_x (⟨σ_oσ_x⟩ - ⟨σ_o⟩⟨σ_x⟩)` and is at most `1/h`. Reference: R. B. Griffiths, C. A.
Hurst, S. Sherman, "Concavity of magnetization of an Ising ferromagnet in a positive external
field", J. Math. Phys. 11 (1970) 790–795. Scope: a finite graph with uniform coupling and uniform
field, the field entering the Hamiltonian as `-h ∑ σ_x` and the derivative taken in `h`; `χ ≤ 1/h`
is the weak form of the GHS consequence `χ ≤ m/h`, the full concavity statement being
`ghs_magnetization_concaveOn`. The hypotheses `β ≥ 0`, `h > 0` are satisfiable. -/
theorem ghs_susceptibility_le_inv_field (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 < h)
    (o : V) :
    deriv (fun t => isingExpectation G β t (fun s => spin s o)) h =
        β * ∑ x, (isingExpectation G β h (fun s => spin s o * spin s x) -
          isingExpectation G β h (fun s => spin s o) *
            isingExpectation G β h (fun s => spin s x))
      ∧ deriv (fun t => isingExpectation G β t (fun s => spin s o)) h ≤ 1 / h := by
  refine ⟨deriv_magnetization_eq_sum_cov G β h o, ?_⟩
  exact (ghs_susceptibility_bound G β h hh o
    (ghs_magnetization_concaveOn G β hβ o)).2

end Sharpness
end StatMech
