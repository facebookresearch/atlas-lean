/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Commutator length in `Aut F_n` (Kourovka Notebook Problem 14.15)

Kourovka Notebook, Problem 14.15 (V. G. Bardakov): for `A_n = Aut F_n`, `n ≥ 3`, find the supremum
`k_n` of the commutator lengths of the elements of `A_n'`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.AutFreeGroupCommutatorLengthKourovka14Problem15Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 14.15 (V. G. Bardakov). UnsolvedMath record
UM-00701000 (`KOU-14.15`), dataset ulamai/UnsolvedMath v1.8.0.

The answer `k_n = ∞` is stated as: for every `n ≥ 3` and every `k`, some element of the derived
subgroup of `Aut F_n` is not a product of `k` commutators `x y x⁻¹ y⁻¹`.
-/

/-- `z` is a product of at most `n` commutators `x y x⁻¹ y⁻¹` of elements of `G`. -/
def IsProductOfCommutators {G : Type*} [Group G] (n : ℕ) (z : G) : Prop :=
  ∃ l : List (G × G), l.length ≤ n ∧ (l.map fun p => p.1 * p.2 * p.1⁻¹ * p.2⁻¹).prod = z

/-- Kourovka 14.15 (V. G. Bardakov), answer `kₙ = ∞`: for every `n ≥ 3`, the commutator length is
unbounded on the derived subgroup of `Aut F_n`, so the supremum `kₙ` is infinite. -/
def autFreeGroupCommutatorLengthUnbounded : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ k : ℕ, ∃ z ∈ commutator (MulAut (FreeGroup (Fin n))),
    ¬ IsProductOfCommutators k z

/--
Resolved true: `kₙ = ∞` for every `n ≥ 3`, because `Aut F_n` is acylindrically hyperbolic
(Genevois-Horbez) and acylindrically hyperbolic groups have infinite commutator width
(Bestvina-Bromberg-Fujiwara); the Kourovka Notebook (21st issue) marks 14.15 solved. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Problem 14.15 (V. G. Bardakov); resolution: A. Genevois and C.
Horbez, J. Topology 14 (2021), 963-991 (Aut F_n is acylindrically hyperbolic); M. Bestvina, K.
Bromberg and K. Fujiwara, Algebr. Geom. Topol. 19 (2019), 477-489 (acylindrically hyperbolic groups
have infinite commutator width), the Kourovka Notebook (21st issue) marks 14.15 solved: k_n = ∞ for
n ≥ 3.
-/
public theorem_wanted autFreeGroupCommutatorLengthUnbounded_holds :
    autFreeGroupCommutatorLengthUnbounded

end MathlibExt.GroupTheory.AutFreeGroupCommutatorLengthKourovka14Problem15Wanted
