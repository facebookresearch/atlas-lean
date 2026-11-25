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

The faces of an `S₁` flag are zero, and so is the degenerate `S₁` flag of an `S₀` flag. In
degree one, the map induced by an exact functor applies the functor to the off-diagonal term
`F(0, 1)` of the `S₁` flags of a simplex: the supported inclusion keeps that term and restriction
to an open restricts it. These tests pin the realized maps to the actual functors on flags; they
do not assert that a realized map is homotopically nontrivial (restriction to the empty open is
not).
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite
open MathlibExt.AlgebraicGeometry.WaldhausenExactFlags MathlibExt.AlgebraicGeometry.CoherentGTheory
open scoped ZeroObject Simplicial

variable {C : Type} [Category C] [Abelian C] (P : ObjectProperty C)

/-- Exact flags vanish on the diagonal. -/
example {n : ℕ} (F : Arrow (Fin (n + 1)) ⥤ C) (hF : IsSFlag P n F) (i : Fin (n + 1)) :
    IsZero (F.obj (interval i i le_rfl)) :=
  hF.2.1 i

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

/-- An `S₀` flag is zero everywhere: its only interval is the diagonal one. -/
theorem sZero_isZero {F : Arrow (Fin 1) ⥤ C} (hF : IsSFlag P 0 F) (a : Arrow (Fin 1)) :
    IsZero (F.obj a) :=
  (hF.2.1 0).of_iso (F.mapIso (Arrow.isoMk (eqToIso (Subsingleton.elim _ _))
    (eqToIso (Subsingleton.elim _ _)) (Subsingleton.elim _ _)))

/-- The faces of an `S₁` flag, its restrictions to a vertex, are zero. -/
example (F : Arrow (Fin 2) ⥤ C) (hF : IsSFlag P 1 F) (α : Fin 1 →o Fin 2) (a : Arrow (Fin 1)) :
    IsZero ((restriction α F).obj a) :=
  sZero_isZero P (restriction_isSFlag P α F hF) a

/-- The degenerate `S₁` flag of an `S₀` flag is zero everywhere. -/
example (F : Arrow (Fin 1) ⥤ C) (hF : IsSFlag P 0 F) (σ : Fin 2 →o Fin 1) (a : Arrow (Fin 2)) :
    IsZero ((restriction σ F).obj a) :=
  sZero_isZero P hF _

variable {D : Type} [Category D] [Abelian D] (Q : ObjectProperty D)

/-- In degree one, the diagonal map of an exact functor applies the functor to the off-diagonal
term `F(0, 1)` of both `S₁` flags of a one-simplex. -/
theorem mapDiagonal_offDiagonal (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] (hG : ∀ x, P x → Q (G.obj x)) (a : (diagonal P) _⦋1⦌)
    (k : Fin 2) :
    (((mapDiagonal P Q G hG).app (op ⦋1⦌) a).obj k).of.obj.obj
        (interval (0 : Fin 2) 1 (by decide)) =
      G.obj ((a.obj k).of.obj.obj (interval (0 : Fin 2) 1 (by decide))) :=
  rfl

/-- The supported inclusion is the realization of the diagonal map of the identity functor. -/
example (X : Scheme.{0}) (U : X.Opens) :
    supportedInclusion X U = SSet.toTop.map (mapDiagonal (supported X U) (finitelyPresented X)
      (𝟭 X.Modules) (supported_finitelyPresented X U)) :=
  rfl

/-- In degree one it keeps the off-diagonal terms of supported `S₁` flags. -/
example (X : Scheme.{0}) (U : X.Opens) (a : (diagonal (supported X U)) _⦋1⦌) (k : Fin 2) :
    (((mapDiagonal (supported X U) (finitelyPresented X) (𝟭 X.Modules)
      (supported_finitelyPresented X U)).app (op ⦋1⦌) a).obj k).of.obj.obj
        (interval (0 : Fin 2) 1 (by decide)) =
      (a.obj k).of.obj.obj (interval (0 : Fin 2) 1 (by decide)) :=
  rfl

/-- Restriction to an open is the realization of the diagonal map of the restriction functor. -/
example (X : Scheme.{0}) (U : X.Opens) [RestrictionFinitePresentation X U] :
    restriction X U = SSet.toTop.map (mapDiagonal (finitelyPresented X) (finitelyPresented U)
      (Scheme.Modules.restrictFunctor U.ι)
      (RestrictionFinitePresentation.preserves (X := X) (U := U))) :=
  rfl

/-- In degree one it restricts the off-diagonal terms of `S₁` flags to the open. -/
example (X : Scheme.{0}) (U : X.Opens) [RestrictionFinitePresentation X U]
    (a : (diagonal (finitelyPresented X)) _⦋1⦌) (k : Fin 2) :
    (((mapDiagonal (finitelyPresented X) (finitelyPresented U)
      (Scheme.Modules.restrictFunctor U.ι)
      (RestrictionFinitePresentation.preserves (X := X) (U := U))).app (op ⦋1⦌) a).obj
        k).of.obj.obj (interval (0 : Fin 2) 1 (by decide)) =
      (Scheme.Modules.restrictFunctor U.ι).obj
        ((a.obj k).of.obj.obj (interval (0 : Fin 2) 1 (by decide))) :=
  rfl
