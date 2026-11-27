/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Authors: @toskua, Avocado
module
public import MathlibExt.CategoryTheory.Abelian.RightDerived.HorseshoeComparisonExtension
public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.Precomposition

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v u' v' u'' v''
namespace CategoryTheory.Functor.RightDerived
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasInjectiveResolutions D]
variable {A : Type u''} [Category.{v''} A] [Abelian A]
variable (E : C ⥤ D) [E.Additive] [E.PreservesInjectiveObjects] [E.PreservesHomology]
variable [PreservesFiniteLimits E] [PreservesFiniteColimits E]
variable (B : D ⥤ A) [B.Additive]

/-- Let `C,A` be abelian, with injective resolutions in `C`, and
`F : C → A` additive. For short exact `S` and any injective horseshoe
`H` for `S`, the canonical boundary `R^nF(S.X₃) → R^(n+1)F(S.X₁)`
equals the cohomology boundary computed from `H`. -/
theorem canonicalConnecting_eq_horseshoe (F : C ⥤ A) [F.Additive] (n : ℕ)
    {S : ShortComplex C} {hS : S.ShortExact} (H : HorseshoeData S hS) :
    (Functor.rightDerivedConnecting F n).app ⟨S, hS⟩ = H.delta F n (n + 1) rfl :=
  (HorseshoeData.ofEndpoints S hS (injectiveResolution S.X₁)
    (injectiveResolution S.X₃)).delta_eq n H

/-- Let `C,D,A` be abelian, with injective resolutions in `C,D`,
`E : C → D` additive and preserving injectives, homology, finite limits,
and finite colimits, and `B : D → A` additive. For short exact `S : X₁ → X₂ → X₃`, the forward degree
precomposition comparisons satisfy
`δ_(E⋙B),n ≫ e_(n+1),X₁ = e_n,X₃ ≫ δ_B,n(E(S))`. -/
theorem canonicalConnecting_precomp (n : ℕ) (S : ShortComplex.ShortExactSequences C) :
    (Functor.rightDerivedConnecting (E ⋙ B) n).app S ≫
      (Functor.rightDerivedPrecompIso E B (n + 1)).hom.app S.obj.X₁ =
    (Functor.rightDerivedPrecompIso E B n).hom.app S.obj.X₃ ≫
      (Functor.rightDerivedConnecting B n).app ⟨S.obj.map E, S.property.map_of_exact E⟩ := by
  let H := HorseshoeData.ofEndpoints S.obj S.property
    (injectiveResolution S.obj.X₁) (injectiveResolution S.obj.X₃)
  have hES := S.property.map_of_exact E
  have h := H.delta_precomp E B hES n
  have hc := canonicalConnecting_eq_horseshoe B n (H.mapExact E hES)
  change H.delta (E ⋙ B) n (n + 1) rfl ≫ _ = _
  rw [hc]
  exact h

end CategoryTheory.Functor.RightDerived

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v u' v' u'' v''
namespace CategoryTheory.Functor.RightDerived
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasInjectiveResolutions D]
variable {A : Type u''} [Category.{v''} A] [Abelian A]
variable (E : C ⥤ D) [E.Additive] [E.PreservesInjectiveObjects] [E.PreservesHomology]
variable [PreservesFiniteLimits E] [PreservesFiniteColimits E]
variable (B : D ⥤ A) [B.Additive] [PreservesFiniteLimits B]

omit [HasInjectiveResolutions C] [HasInjectiveResolutions D]
  [E.PreservesInjectiveObjects] [E.PreservesHomology] in
/-- Let `C,D` be abelian and `E : C → D` additive and preserving
finite limits and finite colimits. Mapping any short exact sequence
`S` by `E` gives a short exact sequence `E(S)`. -/
theorem precompShortExact (S : ShortComplex C) (hS : S.ShortExact) :
    (S.map E).ShortExact := hS.map_of_exact E

/-- Let `C,D,A` be abelian, with injective resolutions in `C,D`,
`E : C → D` additive and preserving injectives, homology, finite limits,
and finite colimits, and `B : D → A` additive. The forward degree comparisons form a morphism from the
right-derived delta-functor of `E ⋙ B` to that of `B` precomposed
with `E`. -/
def precompDeltaHom : Functor.rightDerivedDeltaFunctor (E ⋙ B) ⟶
    CohomologicalDeltaFunctor.precompose E (precompShortExact E)
      (Functor.rightDerivedDeltaFunctor B) :=
  CohomologicalDeltaFunctor.homMk C A
    (fun n => (Functor.rightDerivedPrecompIso E B n).hom)
    (fun n S => canonicalConnecting_precomp E B n S)

omit [PreservesFiniteLimits B] in
@[simp] theorem precompDeltaHom_app (n : ℕ) :
    CohomologicalDeltaFunctor.Hom.app (precompDeltaHom E B) n =
      (Functor.rightDerivedPrecompIso E B n).hom := rfl

/-- Let `C,D,A` be abelian, with injective resolutions in `C,D`,
`E : C → D` additive and preserving injectives, homology, finite limits,
and finite colimits, and `B : D → A` additive. Suppose also that `B` preserves finite limits. For additive
`P : C → A` and `α : P ≅ E ⋙ B`, deriving `α` and precomposing
with `E` gives a morphism from the right-derived delta-functor of `P`
to the delta-functor of `B` precomposed with `E`. -/
def precompDeltaHomOfIso {P : C ⥤ A} [P.Additive]
    (α : P ≅ E ⋙ B) : Functor.rightDerivedDeltaFunctor P ⟶
    CohomologicalDeltaFunctor.precompose E (precompShortExact E)
      (Functor.rightDerivedDeltaFunctor B) :=
  NatTrans.rightDerivedDeltaFunctorMap α.hom ≫ precompDeltaHom E B

omit [PreservesFiniteLimits B] in
@[simp] theorem precompDeltaHomOfIso_app {P : C ⥤ A} [P.Additive]
    (α : P ≅ E ⋙ B) (n : ℕ) :
    CohomologicalDeltaFunctor.Hom.app (precompDeltaHomOfIso E B α) n =
      (Functor.rightDerivedPrecompIsoOfIso E B α n).hom := rfl

end CategoryTheory.Functor.RightDerived

end
