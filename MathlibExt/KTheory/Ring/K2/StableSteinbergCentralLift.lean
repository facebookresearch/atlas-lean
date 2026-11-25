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

public import MathlibExt.GroupTheory.CentralExtensionCommutator
public import MathlibExt.KTheory.Ring.K2.StableElementaryRelations
public import MathlibExt.KTheory.Ring.K2.SteinbergPresentation

/-! # Canonical lifts of stable elementary generators

Constructs central-extension lifts of Steinberg generators and identifies their projections.
-/

@[expose] public section

namespace AlgebraicKTheory

namespace StableSteinberg

universe u v w

variable {R : Type u} [Ring R] {N : Type v} {E : Type w} [Group N] [Group E]

open scoped commutatorElement

/-- Canonical lifted generator for a central extension of `StableE R`.

For `⟨i,j,hij,a⟩` choose fresh index `k := max i j + 1` and take
`S.liftCommutator (natElementary i k _ a) (natElementary k j _ 1)`. -/
noncomputable def centralLiftGenerator
    (S : GroupExtension N E (StableE R)) :
    SteinbergGenerator R → E
  | ⟨i, j, hij, a⟩ =>
    S.liftCommutator
      (StableE.natElementary i (max i j + 1) (by omega) a)
      (StableE.natElementary (max i j + 1) j (by omega) (1 : R))

/-- Projection of the lifted generator is the corresponding stable elementary
generator, via `rightHom_liftCommutator` and `natElementary_chev` with
coefficient order `a * 1`. -/
theorem rightHom_centralLiftGenerator
    (S : GroupExtension N E (StableE R))
    (i j : ℕ) (hij : i ≠ j) (a : R) :
    S.rightHom (centralLiftGenerator (R := R) (N := N) (E := E) S ⟨i, j, hij, a⟩) =
      StableE.natElementary i j hij a := by
  unfold centralLiftGenerator
  simp only
  have hik : i ≠ max i j + 1 := by omega
  have hkj : max i j + 1 ≠ j := by omega
  have h_comm : S.rightHom
      (S.liftCommutator
        (StableE.natElementary i (max i j + 1) hik a)
        (StableE.natElementary (max i j + 1) j hkj (1 : R))) =
      ⁅StableE.natElementary i (max i j + 1) hik a,
        StableE.natElementary (max i j + 1) j hkj (1 : R)⁆ :=
    S.rightHom_liftCommutator _ _
  rw [h_comm]
  have hchev :
      ⁅StableE.natElementary (R := R) i (max i j + 1) hik a,
        StableE.natElementary (R := R) (max i j + 1) j hkj (1 : R)⁆ =
      StableE.natElementary (R := R) i j hij (a * 1) :=
    StableE.natElementary_chev i (max i j + 1) j hik hkj hij a (1 : R)
  rw [hchev, mul_one]

/-- Comparison: if `u, v : E` project to the same two fixed fresh-index
elementary roots used in `centralLiftGenerator`, then the lifted generator
equals `⁅u, v⁆`, via `IsCentral.liftCommutator_eq`.

This fixes the auxiliary index `k := max i j + 1`; independence from a
different auxiliary index is not claimed here. -/
theorem centralLiftGenerator_eq_commutator
    {S : GroupExtension N E (StableE R)} (hS : S.IsCentral)
    (i j : ℕ) (hij : i ≠ j) (a : R)
    (u v : E)
    (hu : S.rightHom u =
      StableE.natElementary (R := R) i (max i j + 1) (by omega) a)
    (hv : S.rightHom v =
      StableE.natElementary (R := R) (max i j + 1) j (by omega) (1 : R)) :
    centralLiftGenerator (R := R) (N := N) (E := E) S ⟨i, j, hij, a⟩ = ⁅u, v⁆ := by
  unfold centralLiftGenerator
  simp only
  have h := hS.liftCommutator_eq hu hv
  exact h.symm

end StableSteinberg

end AlgebraicKTheory

end
