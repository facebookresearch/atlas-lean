/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.Matching.RuralHospitals
public import MathlibExt.GameTheory.Matching.StableMechanism
public import Mathlib.Data.Fintype.Option

/-! # Tests for the rural hospitals theorem, marriage case

A market with two men and three women that has two distinct stable matchings, in which woman
`2` is single; the theorem then says she is single at every stable matching.
-/

namespace MathlibExtTest.GameTheory.Matching.RuralHospitals

open MathlibExt.GameTheory.Matching.RuralHospitals
open MathlibExt.GameTheory.Matching.StableMechanism (rankOrder rothMenPrefs rothWomenPrefs rothX
  roth_isStable_iff)

/-- Rank on `Option α`: `r` on partners, `k` for remaining single. -/
abbrev optRank {α : Type} (r : α → ℕ) (k : ℕ) : Option α → ℕ
  | none => k
  | some a => r a

/-- Men: `m₀ : w₀ ≻ w₁ ≻ single ≻ w₂`, `m₁ : w₁ ≻ w₀ ≻ single ≻ w₂`. -/
abbrev mp : MPrefsSingle (Fin 2) (Fin 3) := fun m =>
  rankOrder (optRank (![![0, 1, 3], ![1, 0, 3]] m) 2) (by revert m; decide)

/-- Women: `w₀ : m₁ ≻ m₀ ≻ single`, `w₁ : m₀ ≻ m₁ ≻ single`, `w₂ : m₀ ≻ m₁ ≻ single`. -/
abbrev wp : WPrefsSingle (Fin 2) (Fin 3) := fun w =>
  rankOrder (optRank (![![1, 0], ![0, 1], ![0, 1]] w) 2) (by revert w; decide)

/-- The men-preferred matching `(m₀, w₀), (m₁, w₁)`, with `w₂` single. -/
abbrev μ : Fin 2 ≃. Fin 3 :=
  ⟨![some 0, some 1], ![some 0, some 1, none], by decide⟩

/-- The women-preferred matching `(m₀, w₁), (m₁, w₀)`, with `w₂` single. -/
abbrev ν : Fin 2 ≃. Fin 3 :=
  ⟨![some 1, some 0], ![some 1, some 0, none], by decide⟩

theorem hμ : IsStableSingle mp wp μ := by unfold IsStableSingle; decide

theorem hν : IsStableSingle mp wp ν := by unfold IsStableSingle; decide

/-- The two stable matchings differ, so the hypotheses are non-degenerate. -/
example : μ ≠ ν := fun h => absurd (congrArg (· 0) h) (by decide)

/-- Woman `2` is single at `μ`, hence at every stable matching. -/
example (ρ : Fin 2 ≃. Fin 3) (hρ : IsStableSingle mp wp ρ) : ρ.symm 2 = none :=
  Option.not_isSome_iff_eq_none.1 fun h =>
    absurd ((isSome_symm_iff_of_isStableSingle hμ hρ 2).2 h) (by decide)

/-- Bridge: Roth's 1982 market, with remaining single ranked last, has `rothX` stable as a
matching with singles, and every stable matching with singles of it is perfect. -/
example : IsStableSingle (fun m => withSingleLast (rothMenPrefs m))
    (fun w => withSingleLast (rothWomenPrefs w)) rothX.toPEquiv :=
  (isStableSingle_toPEquiv_iff _ _ _).2 ((roth_isStable_iff _).2 (Or.inl rfl))

example {ρ : Fin 3 ≃. Fin 3}
    (hρ : IsStableSingle (fun m => withSingleLast (rothMenPrefs m))
      (fun w => withSingleLast (rothWomenPrefs w)) ρ) (m : Fin 3) : (ρ m).isSome :=
  isSome_of_isStableSingle_withSingleLast rfl _ _ hρ m

#print axioms isSome_iff_of_isStableSingle
#print axioms isSome_symm_iff_of_isStableSingle
#print axioms isStableSingle_toPEquiv_iff
#print axioms isSome_of_isStableSingle_withSingleLast

end MathlibExtTest.GameTheory.Matching.RuralHospitals
