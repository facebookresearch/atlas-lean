/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Linearity of ⟨a, b | [[a, b], b] = 1⟩ (Kourovka Notebook Problem 18.86)

Kourovka Notebook, Archive of Solved Problems, Problem 18.86 (V. A. Roman'kov): is the group `G =
⟨a, b | [[a, b], b] = 1⟩`, which is isomorphic to the group of all unitriangular automorphisms of
the free group of rank `3`, linear?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.UnitriangularOneRelatorLinearKourovka18Problem86Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.86 (V. A.
Roman'kov). UnsolvedMath record UM-00701515 (`KOU-18.86`), dataset ulamai/UnsolvedMath v1.8.0.

`[x, y] = x⁻¹ y⁻¹ x y` (the other convention gives an isomorphic group, via `a ↦ a⁻¹`, `b ↦ b⁻¹`);
linear means a faithful homomorphism into `GLₙ(K)` for some field `K` and some `n`.
-/

/-- The relator `[[a, b], b]` on the free generators `a = x₀`, `b = x₁`, with
`[x, y] = x⁻¹ y⁻¹ x y`. -/
def relator : FreeGroup (Fin 2) :=
  let a := FreeGroup.of (0 : Fin 2)
  let b := FreeGroup.of (1 : Fin 2)
  let c := a⁻¹ * b⁻¹ * a * b
  c⁻¹ * b⁻¹ * c * b

/-- The group `⟨a, b | [[a, b], b] = 1⟩`. -/
abbrev OneRelatorGroup : Type := PresentedGroup ({relator} : Set (FreeGroup (Fin 2)))

/-- Kourovka 18.86 (V. A. Roman'kov): the group `⟨a, b | [[a, b], b] = 1⟩` is linear, that is, it
has a faithful representation in `GLₙ(K)` for some field `K` and some `n`. -/
def oneRelatorGroupIsLinear : Prop :=
  ∃ (K : Type) (_ : Field K) (n : ℕ) (ρ : OneRelatorGroup →* Matrix.GeneralLinearGroup (Fin n) K),
    Function.Injective ρ

/--
Resolved true: the Kourovka Archive answers 18.86 "Yes, it is linear": `G` embeds in the holomorph
`Hol F₂`, which is linear by Corollary 3 of Bardakov-Bryukhanov (2007); another proof is in
Roman'kov (2013). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory:
The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem
18.86 (V. A. Roman'kov); resolution: V. G. Bardakov and O. V. Bryukhanov, Vestnik Novosibirsk Univ.
Ser. Mat. Mekh. Inf. 7 (2007), no. 3, 45-58 (Russian); V. A. Roman'kov, J. Siberian Federal Univ.
Math. Phys. 6 (2013), no. 4, 516-520, Kourovka Archive, Problem 18.86: Yes, it is linear, since it
embeds in Hol F_2 (adding c = [a, b] gives G = ⟨a, b, c | a^b = ac, c^b = c⟩), and Hol F_2 is linear
by Corollary 3 of Bardakov-Bryukhanov; another proof by Roman'kov,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted oneRelatorGroupIsLinear_holds : oneRelatorGroupIsLinear

end MathlibExt.GroupTheory.UnitriangularOneRelatorLinearKourovka18Problem86Wanted
