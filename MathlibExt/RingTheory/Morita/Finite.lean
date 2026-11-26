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

public import Mathlib.RingTheory.Morita.Basic
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import MathlibExt.Algebra.Category.ModuleCat.Equivalence
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import MathlibExt.Algebra.Category.FGProjectiveCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import MathlibExt.CategoryTheory.ExactCategory.Split
public import MathlibExt.CategoryTheory.ExactCategory.Abelian
public import MathlibExt.CategoryTheory.ExactCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Finite module categories under Morita equivalence

Finite generation and finite projectivity are invariant under module isomorphisms over any ring.
Let R₀ be a commutative semiring and A,B possibly noncommutative R₀-algebra rings in independent
universes u₁,u₂. A Morita equivalence over R₀ restricts, in module universe max(u₁,u₂), to
equivalences of finitely generated modules and of finitely generated projective modules.

The forward and inverse restricted functors are additive. On the finite-projective categories
they preserve the split exact structures without a Noetherian hypothesis. If A and B are
Noetherian, the finitely generated module categories are abelian, and the restricted equivalence
and inverse preserve their exact structures as well.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace ModuleCat

/-- For a ring R in universe u and modules in an independent carrier universe v, finite generation
is closed under module isomorphisms. A linear equivalence carries a finite generating family to
a generating family of the target. -/
instance isFG_isClosedUnderIsomorphisms {R : Type u} [Ring R] :
    (isFG.{v} (R := R)).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    have : Module.Finite R X := hX
    exact Module.Finite.equiv e.toLinearEquiv

/-- Let R be any ring in universe u and modules have carriers in v. The property of being finitely
generated and projective over R is closed under module isomorphisms. A linear equivalence
preserves both finiteness and algebraic module projectivity. -/
instance isFGProjective_isClosedUnderIsomorphisms {R : Type u} [Ring R] :
    (isFGProjective.{v} (R := R)).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    obtain ⟨hFin, hProj⟩ := hX
    constructor
    · have : Module.Finite R X := hFin
      exact Module.Finite.equiv e.toLinearEquiv
    · have : Module.Projective R X := hProj
      exact Module.Projective.of_equiv' e.toLinearEquiv

end ModuleCat

universe u₀ u₁ u₂

variable {R₀ : Type u₀} [CommSemiring R₀] {A : Type u₁} [Ring A] [Algebra R₀ A]
  {B : Type u₂} [Ring B] [Algebra R₀ B]

namespace MoritaEquivalence

private theorem projective_iff (e : MoritaEquivalence R₀ A B)
    (X : ModuleCat.{max u₁ u₂} A) :
    Module.Projective A X ↔ Module.Projective B (e.eqv.functor.obj X) := by
  simpa [IsProjective.iff_projective] using (e.eqv.map_projective_iff X).symm

/-- Let R₀ be a commutative semiring in universe u₀ and A,B possibly noncommutative R₀-algebra rings
in universes u₁,u₂. Let e be a Morita equivalence over R₀, on module carriers in W=max(u₁,u₂).
The underlying module equivalence preserves and reflects finite generation, so it restricts to
an equivalence FGMod_W(A)≅FGMod_W(B). Its object and morphism maps are those of e, and no
Noetherian hypothesis is required. -/
noncomputable def fgModuleCatEquivalence (e : MoritaEquivalence R₀ A B) :
    FGModuleCat.{max u₁ u₂} A ≌ FGModuleCat.{max u₁ u₂} B :=
  e.eqv.congrFullSubcategory (by
    ext X
    exact (ModuleCat.finite_iff e.eqv X).symm)

/-- Let R₀ be a commutative semiring in universe u₀ and A,B possibly noncommutative R₀-algebra rings
in universes u₁,u₂. Let e be a Morita equivalence over R₀, on module carriers in W=max(u₁,u₂).
Preservation and reflection of finite generation and projectivity give an equivalence
FGProj_W(A)≅FGProj_W(B). The full subcategories use the same module and morphism maps as e and
require no Noetherian assumption. -/
noncomputable def fgProjectiveCatEquivalence (e : MoritaEquivalence R₀ A B) :
    FGProjectiveCat.{max u₁ u₂} A ≌ FGProjectiveCat.{max u₁ u₂} B :=
  e.eqv.congrFullSubcategory (by
    ext X
    constructor
    · rintro ⟨hFinB, hProjB⟩
      exact ⟨(ModuleCat.finite_iff e.eqv X).mpr hFinB, (projective_iff e X).mpr hProjB⟩
    · rintro ⟨hFinA, hProjA⟩
      exact ⟨(ModuleCat.finite_iff e.eqv X).mp hFinA, (projective_iff e X).mp hProjA⟩)

/-- Let R₀ be a commutative semiring in universe u₀ and A,B possibly noncommutative R₀-algebra rings
in universes u₁,u₂. Let e be a Morita equivalence over R₀, on module carriers in W=max(u₁,u₂).
The forward restricted functor FGMod_W(A)→FGMod_W(B) is additive. It preserves sums of module
morphisms through the additive underlying Morita equivalence. -/
instance fgModuleCatEquivalence_additive (e : MoritaEquivalence R₀ A B) :
    e.fgModuleCatEquivalence.functor.Additive := by
  dsimp only [fgModuleCatEquivalence, Equivalence.congrFullSubcategory]
  infer_instance

/-- Let R₀ be a commutative semiring in universe u₀ and A,B possibly noncommutative R₀-algebra rings
in universes u₁,u₂. Let e be a Morita equivalence over R₀, on module carriers in W=max(u₁,u₂).
The inverse restricted functor FGMod_W(B)→FGMod_W(A) is additive, with the same morphism sums as
the inverse module equivalence. -/
instance fgModuleCatEquivalence_inverse_additive (e : MoritaEquivalence R₀ A B) :
    e.fgModuleCatEquivalence.inverse.Additive := by
  infer_instance

/-- Let R₀ be a commutative semiring in universe u₀ and A,B possibly noncommutative R₀-algebra rings
in universes u₁,u₂. Let e be a Morita equivalence over R₀, on module carriers in W=max(u₁,u₂).
The forward functor FGProj_W(A)→FGProj_W(B) preserves sums of parallel morphisms. Its maps are
the restriction of the additive underlying module equivalence. -/
instance fgProjectiveCatEquivalence_additive (e : MoritaEquivalence R₀ A B) :
    e.fgProjectiveCatEquivalence.functor.Additive := by
  dsimp only [fgProjectiveCatEquivalence, Equivalence.congrFullSubcategory]
  infer_instance

/-- Let R₀ be a commutative semiring in universe u₀ and A,B possibly noncommutative R₀-algebra rings
in universes u₁,u₂. Let e be a Morita equivalence over R₀, on module carriers in W=max(u₁,u₂).
The inverse functor FGProj_W(B)→FGProj_W(A) is additive on every Hom group, inherited from the
inverse underlying module equivalence. -/
instance fgProjectiveCatEquivalence_inverse_additive (e : MoritaEquivalence R₀ A B) :
    e.fgProjectiveCatEquivalence.inverse.Additive := by
  infer_instance

/-- Let R₀ be a commutative semiring in universe u₀ and A,B possibly noncommutative R₀-algebra rings
in universes u₁,u₂. Let e be a Morita equivalence over R₀, on module carriers in W=max(u₁,u₂).
The forward restricted functor FGProj_W(A)→FGProj_W(B) is exact for the split exact structures.
Additivity preserves every split short exact sequence, without a Noetherian condition on A or B. -/
instance fgProjectiveCatEquivalence_isExact (e : MoritaEquivalence R₀ A B) :
    e.fgProjectiveCatEquivalence.functor.IsExact :=
  ExactCategory.isExact_splitSource _

/-- Let R₀ be a commutative semiring in universe u₀ and A,B possibly noncommutative R₀-algebra rings
in universes u₁,u₂. Let e be a Morita equivalence over R₀, on module carriers in W=max(u₁,u₂).
The inverse restricted functor FGProj_W(B)→FGProj_W(A) is exact for the split exact structures.
It is additive and therefore preserves their split short exact sequences. -/
instance fgProjectiveCatEquivalence_inverse_isExact (e : MoritaEquivalence R₀ A B) :
    e.fgProjectiveCatEquivalence.inverse.IsExact :=
  ExactCategory.isExact_splitSource _

/-- Let R₀ be a commutative semiring in universe u₀ and A,B possibly noncommutative R₀-algebra rings
in universes u₁,u₂. Let e be a Morita equivalence over R₀, on module carriers in W=max(u₁,u₂).
Assume additionally that A and B are Noetherian rings. The forward restricted functor
FGMod_W(A)→FGMod_W(B) is exact for the abelian exact structures: it preserves finite limits and
finite colimits and hence short exact sequences. -/
instance fgModuleCatEquivalence_isExact (e : MoritaEquivalence R₀ A B)
    [IsNoetherianRing A] [IsNoetherianRing B] :
    e.fgModuleCatEquivalence.functor.IsExact := by
  rw [Functor.isExact_iff_preservesFiniteLimits_and_colimits]
  exact ⟨inferInstance, inferInstance⟩

/-- Let R₀ be a commutative semiring in universe u₀ and A,B possibly noncommutative R₀-algebra rings
in universes u₁,u₂. Let e be a Morita equivalence over R₀, on module carriers in W=max(u₁,u₂).
When both A and B are Noetherian, the inverse restricted functor FGMod_W(B)→FGMod_W(A) is exact
for their abelian exact structures. The Noetherian hypotheses are retained for this
finite-module exactness statement. -/
instance fgModuleCatEquivalence_inverse_isExact (e : MoritaEquivalence R₀ A B)
    [IsNoetherianRing A] [IsNoetherianRing B] :
    e.fgModuleCatEquivalence.inverse.IsExact := by
  rw [Functor.isExact_iff_preservesFiniteLimits_and_colimits]
  exact ⟨inferInstance, inferInstance⟩

end MoritaEquivalence
