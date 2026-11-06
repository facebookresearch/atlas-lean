/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReduction

/-! A certificate mechanism for the binary orbit-cover step of Höhn--Seysen
§3.2. Every edge uses the genuine Conway action of an actual local stabilizer
element. Strictly decreasing natural ranks certify termination at listed roots;
an unchecked union-find table is not an orbit-cover proof. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The genuine type-four binary orbit, as a subtype of the actual lattice coordinates. -/
abbrev generatedAxisGlobalBinaryOrbit :=
  MulAction.orbit Co1 (toAdd (qQuotHom sourceOmegaQ))

/-- An actual local element acts on the genuine binary Ω orbit through its Conway projection. -/
noncomputable def generatedAxisGlobalBinaryAct (h : H)
    (x : generatedAxisGlobalBinaryOrbit) : generatedAxisGlobalBinaryOrbit :=
  ⟨co1BinaryAction (projH h) x.val, by
    obtain ⟨g, hg⟩ := x.property
    refine ⟨projH h * g, ?_⟩
    change co1BinaryAction (projH h * g) (toAdd (qQuotHom sourceOmegaQ)) = _
    rw [map_mul, LinearEquiv.mul_apply]
    exact congrArg (co1BinaryAction (projH h)) hg⟩

/-- Composition of genuine binary actions agrees with actual local multiplication. -/
theorem generatedAxisGlobalBinaryAct_mul (h k : H)
    (x : generatedAxisGlobalBinaryOrbit) :
    generatedAxisGlobalBinaryAct (h * k) x =
      generatedAxisGlobalBinaryAct h (generatedAxisGlobalBinaryAct k x) := by
  apply Subtype.ext
  change co1BinaryAction (projH (h * k)) x.val = _
  rw [map_mul, map_mul, LinearEquiv.mul_apply]
  rfl

/-- The genuine binary orbit acted on by certificate stabilizers
has exactly 8,292,375 points. -/
theorem generatedAxisGlobalBinaryOrbit_card :
    Nat.card generatedAxisGlobalBinaryOrbit = 8292375 := co1OmegaFrame_orbit_card

/-- A finite descending-edge certificate proves genuine stabilizer-orbit
coverage. The inputs are local edge equalities and decreasing ranks, rather
than an assumed statement that every point is already in a listed orbit. -/
theorem generatedAxisGlobalBinary_cover_of_descent {κ : Type*}
    (C : Subgroup H) (root : κ → generatedAxisGlobalBinaryOrbit)
    (label : generatedAxisGlobalBinaryOrbit → κ)
    (rank : generatedAxisGlobalBinaryOrbit → ℕ)
    (hedge : ∀ x, x = root (label x) ∨ ∃ y c,
      c ∈ C ∧ rank y < rank x ∧ label y = label x ∧
        generatedAxisGlobalBinaryAct c y = x) :
    ∀ x, ∃ c : H, c ∈ C ∧ generatedAxisGlobalBinaryAct c (root (label x)) = x := by
  have hmain : ∀ n x, rank x = n →
      ∃ c : H, c ∈ C ∧ generatedAxisGlobalBinaryAct c (root (label x)) = x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx
      rcases hedge x with hr | ⟨y, c, hc, hy, hl, he⟩
      · refine ⟨1, C.one_mem, ?_⟩
        apply Subtype.ext
        change co1BinaryAction (projH 1) (root (label x)).val = x.val
        rw [map_one, map_one]
        exact congrArg Subtype.val hr.symm
      · obtain ⟨d, hd, he'⟩ := ih (rank y) (hx ▸ hy) y rfl
        refine ⟨c * d, C.mul_mem hc hd, ?_⟩
        rw [generatedAxisGlobalBinaryAct_mul, ← hl, he', he]
  intro x
  exact hmain (rank x) x rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
