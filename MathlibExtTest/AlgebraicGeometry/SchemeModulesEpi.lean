/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.SchemeModulesEpi

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u v

-- Consumer with the original binders.
example {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) :
    Epi φ ↔ ∀ (U : X.Opens) (s : Γ(N, U)), ∀ x ∈ U, ∃ (V : X.Opens) (i : V ≤ U),
      x ∈ V ∧ N.presheaf.map (homOfLE i).op s ∈ Set.range (φ.app V) :=
  AlgebraicGeometry.Scheme.Modules.Hom.epi_iff_locallySurjective φ

-- Higher-universe consumer: the statement is universe-polymorphic.
example {X : Scheme.{max u v}} {M N : X.Modules} (φ : M ⟶ N) :
    Epi φ ↔ ∀ (U : X.Opens) (s : Γ(N, U)), ∀ x ∈ U, ∃ (V : X.Opens) (i : V ≤ U),
      x ∈ V ∧ N.presheaf.map (homOfLE i).op s ∈ Set.range (φ.app V) :=
  AlgebraicGeometry.Scheme.Modules.Hom.epi_iff_locallySurjective φ

-- The identity is an epimorphism, hence locally surjective with no shrinking
-- needed beyond the given open.
example {X : Scheme.{u}} {M : X.Modules} (U : X.Opens) (s : Γ(M, U)) (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (i : V ≤ U), x ∈ V ∧
      M.presheaf.map (homOfLE i).op s ∈ Set.range ((𝟙 M : M ⟶ M).app V) := by
  have h := (AlgebraicGeometry.Scheme.Modules.Hom.epi_iff_locallySurjective (𝟙 M)).1
    inferInstance U s x hx
  obtain ⟨V, i, hxV, t, ht⟩ := h
  exact ⟨V, i, hxV, t, ht⟩
