/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Abelian.RightDerived.DeltaComparison
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Degree-zero normalization of right-derived precomposition

For exact injective-preserving `T : C → D` between abelian categories
with injective resolutions and additive left-exact `P : C → A`,
`B : D → A` with `P ≅ T ⋙ B`, the derived precomposition comparison
is the unique cohomological delta-functor morphism whose degree-zero
map becomes the given coefficient isomorphism under `R⁰P ≅ P` and
`T ⋙ R⁰B ≅ T ⋙ B`. Its connecting squares also have elementwise forms
for additive-group-valued functors.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits

universe uC vC uD vD uA vA

namespace CategoryTheory.Functor.RightDerived

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type uD} [Category.{vD} D] [Abelian D] [HasInjectiveResolutions D]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (T : C ⥤ D) [T.Additive] [T.PreservesInjectiveObjects] [T.PreservesHomology]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
variable (B : D ⥤ A) [B.Additive] [PreservesFiniteLimits B]
variable {P : C ⥤ A} [P.Additive] [PreservesFiniteLimits P] (α : P ≅ T ⋙ B)

/-- Let `C,A` be abelian, with injective resolutions in `C`, and
`P : C → A` additive and preserving finite limits. The degree-zero
part of its right-derived delta-functor is canonically isomorphic to `P`. -/
def precompSourceZeroIso : P.rightDerivedDeltaFunctor.T 0 ≅ P := P.rightDerivedZeroIsoSelf

/-- Let `C,D,A` be abelian, with injective resolutions in `D`,
`T : C → D` additive and preserving finite limits and finite colimits,
and `B : D → A` additive and preserving finite limits. The degree-zero
part of the right-derived delta-functor of `B` precomposed with `T`
is canonically isomorphic to `T ⋙ B`. -/
def precompTargetZeroIso :
    (CohomologicalDeltaFunctor.precompose T (precompShortExact T) B.rightDerivedDeltaFunctor).T 0 ≅ T ⋙ B :=
  Functor.isoWhiskerLeft T B.rightDerivedZeroIsoSelf

/-- Let `C,D,A` be abelian, with injective resolutions in `C,D`,
`T : C → D` additive and preserving injectives, homology, finite limits
and finite colimits, `B : D → A` additive and preserving finite limits,
and `P : C → A` additive and preserving finite limits. Fix
`α : P ≅ T ⋙ B`. The degree-zero map of the precomposition delta-functor
isomorphism satisfies `e_derived,0 ≫ e_target,0 = e_source,0 ≫ α`. -/
theorem precompDeltaIsoOfIso_zero_normalization :
    CohomologicalDeltaFunctor.Hom.app (precompDeltaIsoOfIso T B α).hom 0 ≫
        (precompTargetZeroIso T B).hom = (precompSourceZeroIso (P := P)).hom ≫ α.hom := by
  apply NatTrans.ext
  funext X
  change (Functor.rightDerivedPrecompIsoOfIso T B α 0).hom.app X ≫
      B.rightDerivedZeroIsoSelf.hom.app (T.obj X) = P.rightDerivedZeroIsoSelf.hom.app X ≫ α.hom.app X
  exact Functor.rightDerivedPrecompIsoOfIso_zeroIsoSelf T B α X

/-- Let `C,D,A` be abelian, with injective resolutions in `C,D`,
`T : C → D` additive and preserving injectives, homology, finite limits
and finite colimits, `B : D → A` additive and preserving finite limits,
and `P : C → A` additive and preserving finite limits. Fix
`α : P ≅ T ⋙ B`. The forward precomposition delta-functor morphism is the
outgoing universal extension of `α`, after the canonical source
and target degree-zero identifications. -/
theorem precompDeltaIsoOfIso_normalizedExtension :
    (precompDeltaIsoOfIso T B α).hom =
      CohomologicalDeltaFunctor.normalizedExtension P.rightDerivedDeltaFunctor
        (CohomologicalDeltaFunctor.precompose T (precompShortExact T) B.rightDerivedDeltaFunctor)
        P.isUniversal_rightDerivedDeltaFunctor (precompSourceZeroIso (P := P))
        (precompTargetZeroIso T B) α.hom := by
  apply CohomologicalDeltaFunctor.hom_eq_of_app_zero _ P.isUniversal_rightDerivedDeltaFunctor _
  apply (cancel_mono (precompTargetZeroIso T B).hom).1
  exact (precompDeltaIsoOfIso_zero_normalization T B α).trans
    (CohomologicalDeltaFunctor.normalizedExtension_normalization _ _ P.isUniversal_rightDerivedDeltaFunctor
      (precompSourceZeroIso (P := P)) (precompTargetZeroIso T B) α.hom).symm

/-- Let `C,D,A` be abelian, with injective resolutions in `C,D`,
`T : C → D` additive and preserving injectives, homology, finite limits
and finite colimits, `B : D → A` additive and preserving finite limits,
and `P : C → A` additive and preserving finite limits. Fix
`α : P ≅ T ⋙ B`. Any cohomological delta-functor morphism with the same normalized
degree-zero map `α` equals the forward precomposition comparison. -/
theorem precompDeltaIsoOfIso_unique
    (f : P.rightDerivedDeltaFunctor ⟶
      CohomologicalDeltaFunctor.precompose T (precompShortExact T) B.rightDerivedDeltaFunctor)
    (h₀ : CohomologicalDeltaFunctor.Hom.app f 0 ≫ (precompTargetZeroIso T B).hom =
      (precompSourceZeroIso (P := P)).hom ≫ α.hom) :
    f = (precompDeltaIsoOfIso T B α).hom := by
  apply CohomologicalDeltaFunctor.hom_eq_of_app_zero _ P.isUniversal_rightDerivedDeltaFunctor _
  apply (cancel_mono (precompTargetZeroIso T B).hom).1
  exact h₀.trans (precompDeltaIsoOfIso_zero_normalization T B α).symm

omit [PreservesFiniteLimits P] [PreservesFiniteLimits B] in
/-- Let `C,D,A` be abelian, with injective resolutions in `C,D`,
`T : C → D` additive and preserving injectives, homology, finite limits
and finite colimits, `B : D → A` additive and preserving finite limits,
and `P : C → A` additive with `α : P ≅ T ⋙ B`. For short exact `S`,
the comparisons in degrees `n,n+1` commute with the connecting maps
of `P` on `S` and of `B` on `T(S)`. -/
theorem canonicalConnecting_precompOfIso (n : ℕ) (S : ShortComplex.ShortExactSequences C) :
    (Functor.rightDerivedConnecting P n).app S ≫
      (Functor.rightDerivedPrecompIsoOfIso T B α (n + 1)).hom.app S.obj.X₁ =
    (Functor.rightDerivedPrecompIsoOfIso T B α n).hom.app S.obj.X₃ ≫
      (Functor.rightDerivedConnecting B n).app ⟨S.obj.map T, precompShortExact T S.obj S.property⟩ :=
  DeltaFunctor.System.comm (precompDeltaHomOfIso T B α).hom n S

/-- Let `C,D` be abelian with injective resolutions, `T′ : C → D`
additive and preserving injectives, homology, finite limits and finite
colimits, and `B′ : D → Ab`, `P′ : C → Ab` additive with
`α′ : P′ ≅ T′ ⋙ B′`. For short exact `S` and
`y ∈ R^nP′(S.X₃)`, comparison in degree `n+1` of its boundary equals
the boundary of its degree-`n` comparison in `R^nB′(T′(S.X₃))`. -/
theorem canonicalConnecting_precompOfIso_value
    (T' : C ⥤ D) [T'.Additive] [T'.PreservesInjectiveObjects] [T'.PreservesHomology]
    [PreservesFiniteLimits T'] [PreservesFiniteColimits T']
    (B' : D ⥤ AddCommGrpCat.{vA}) [B'.Additive]
    {P' : C ⥤ AddCommGrpCat.{vA}} [P'.Additive] (α' : P' ≅ T' ⋙ B')
    (n : ℕ) (S : ShortComplex.ShortExactSequences C) (y : (P'.rightDerived n).obj S.obj.X₃) :
    (Functor.rightDerivedPrecompIsoOfIso T' B' α' (n + 1)).hom.app S.obj.X₁
        ((Functor.rightDerivedConnecting P' n).app S y) =
      (Functor.rightDerivedConnecting B' n).app ⟨S.obj.map T', precompShortExact T' S.obj S.property⟩
        ((Functor.rightDerivedPrecompIsoOfIso T' B' α' n).hom.app S.obj.X₃ y) := by
  let a := (Functor.rightDerivedConnecting P' n).app S
  let b := (Functor.rightDerivedPrecompIsoOfIso T' B' α' (n + 1)).hom.app S.obj.X₁
  let c := (Functor.rightDerivedPrecompIsoOfIso T' B' α' n).hom.app S.obj.X₃
  let d := (Functor.rightDerivedConnecting B' n).app
    ⟨S.obj.map T', precompShortExact T' S.obj S.property⟩
  have h := ConcreteCategory.congr_hom (canonicalConnecting_precompOfIso T' B' α' n S) y
  exact (ConcreteCategory.comp_apply a b y).symm.trans
    (h.trans (ConcreteCategory.comp_apply c d y))

/-- Let `e₃ : H₃ → G₃`, `e₁ : H₁ → G₁`, `c₃ : G₃ → B₃`,
`c₁ : G₁ → B₁` be functions, with boundary functions `δ_H,δ_G,δ_B`.
If `δ_G(e₃x)=e₁(δ_Hx)` and `c₁(δ_Gy)=δ_B(c₃y)` for all `x,y`,
then `δ_B(c₃(e₃x))=c₁(e₁(δ_Hx))` for every `x`. -/
theorem pastedConnector_apply {H₃ H₁ G₃ G₁ B₃ B₁ : Type*}
    (e₃ : H₃ → G₃) (e₁ : H₁ → G₁) {c₃ : G₃ → B₃} {c₁ : G₁ → B₁}
    (δH : H₃ → H₁) {δG : G₃ → G₁} {δB : B₃ → B₁}
    (hG : ∀ x, δG (e₃ x) = e₁ (δH x)) (hC : ∀ y, c₁ (δG y) = δB (c₃ y)) (x : H₃) :
    δB (c₃ (e₃ x)) = c₁ (e₁ (δH x)) :=
  (hC (e₃ x)).symm.trans (congrArg c₁ (hG x))

end CategoryTheory.Functor.RightDerived
