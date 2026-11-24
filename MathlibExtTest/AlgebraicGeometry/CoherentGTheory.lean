/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.CoherentGTheory

/-!
# Tests for the Waldhausen S-construction of finitely presented sheaves

Exact flags have zero diagonals; an `S₀` flag is zero everywhere; the subquotient
`F(i, j) → F(i, k) → F(j, k)` of `i ≤ j ≤ k` is short exact, so its first map is a mono and its
second an epi. Restriction along the identity is the identity, restriction along a composite is
the composite of restrictions, and exact functors act on flags by composition. The supported
sheaves of an open are finitely presented and include the zero sheaf.
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.WaldhausenExactFlags MathlibExt.AlgebraicGeometry.CoherentGTheory
open scoped ZeroObject

variable {C : Type} [Category C] [Abelian C] (P : ObjectProperty C)

/-- Exact flags vanish on the diagonal. -/
example {n : ℕ} (F : Arrow (Fin (n + 1)) ⥤ C) (hF : IsSFlag P n F) (i : Fin (n + 1)) :
    IsZero (F.obj (interval i i le_rfl)) :=
  hF.2.1 i

/-- An `S₀` flag is zero everywhere: its only interval is the diagonal one. -/
example (F : Arrow (Fin 1) ⥤ C) (hF : IsSFlag P 0 F) (a : Arrow (Fin 1)) : IsZero (F.obj a) :=
  (hF.2.1 0).of_iso (F.mapIso (Arrow.isoMk (eqToIso (Subsingleton.elim _ _))
    (eqToIso (Subsingleton.elim _ _)) (Subsingleton.elim _ _)))

/-- The subquotient sequence `F(i, j) → F(i, k) → F(j, k)` of an exact flag is short exact. -/
example {n : ℕ} (F : Arrow (Fin (n + 1)) ⥤ C) (hF : IsSFlag P n F) {i j k : Fin (n + 1)}
    (h : i ≤ j) (h' : j ≤ k) : Mono (F.map (first h h')) ∧ Epi (F.map (second h h')) := by
  obtain ⟨w, hw⟩ := hF.2.2 i j k h h'
  exact ⟨hw.mono_f, hw.epi_g⟩

/-- Restriction along the identity is the identity. -/
example {n : ℕ} (F : Arrow (Fin (n + 1)) ⥤ C) : restriction OrderHom.id F = F :=
  rfl

/-- Restriction along a composite is the composite of the restrictions. -/
example {l m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (β : Fin (l + 1) →o Fin (m + 1)) :
    restrictFunctor P (α.comp β) = restrictFunctor P α ⋙ restrictFunctor P β :=
  rfl

/-- The zero flag is zero on every interval. -/
example (hP : P 0) (n : ℕ) (a : Arrow (Fin (n + 1))) : (zeroFlag P hP n).obj.obj a = 0 :=
  rfl

/-- Exact functors act on flags by composition. -/
example {D : Type} [Category D] [Abelian D] (Q : ObjectProperty D) (G : C ⥤ D) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (hG : ∀ x, P x → Q (G.obj x)) {n : ℕ}
    (A : SLevel P n) : ((mapLevel P Q G hG n).obj A).obj = A.obj ⋙ G :=
  rfl

/-- The supported sheaves of an open are finitely presented. -/
example (X : Scheme.{0}) (U : X.Opens) (F : X.Modules) (h : supported X U F) :
    finitelyPresented X F :=
  supported_finitelyPresented X U F h

/-- The zero sheaf is supported on every open. -/
example (X : Scheme.{0}) (U : X.Opens) : supported X U 0 :=
  Or.inl (isZero_zero _)
