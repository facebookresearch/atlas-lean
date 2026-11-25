/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.FieldCanonicalCoindResolutionNaturality
public import MathlibExt.CategoryTheory.Action.DiscreteCoinductionInvariantPowers
public import MathlibExt.CategoryTheory.Action.DiscreteCoinductionNativeAcyclicity

/-! Actual original field native comparison proof components. -/

/-! Original qualified proof block: FieldCoindCanonicalExact -/
/-! The original field canonical coinduction diagram has genuine coefficient exactness and acyclic terms. -/
@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

instance fieldCoindCanonicalComplexFunctor_preservesZero :
    (fieldCoindCanonicalComplexFunctor.{u, w} k Ω).PreservesZeroMorphisms where
  map_zero := by
    intro M N
    apply HomologicalComplex.Hom.ext
    funext n
    change ((fieldCoindCanonicalComplexFunctor.{u, w} k Ω).map (0 : M ⟶ N)).f n = 0
    rw [fieldCoindCanonicalComplexFunctor_map_f]
    let T := DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)
    let : (Monad.monadPow T (n + 1)).PreservesZeroMorphisms :=
      DiscreteAbelianAction.coindMonadPower_preservesZero.{u, w} Gal(Ω/k) (n + 1)
    have hn := Monad.coresolutionObjIso_naturality T (0 : M ⟶ N) n
    have hz : (Monad.monadPow T (n + 1)).map (0 : M ⟶ N) = 0 := (Monad.monadPow T (n + 1)).map_zero M N
    apply (cancel_mono (Monad.coresolutionObjIso T N n).hom).mp
    exact hn.trans ((congrArg (fun q => (Monad.coresolutionObjIso T M n).hom ≫ q) hz).trans
      comp_zero) |>.trans zero_comp.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual original coefficient short exact sequence remains short exact in every
canonical coinduction degree, via the exact same stored monad power coordinates. -/
theorem fieldCoindCanonicalComplex_shortExact
    (S : ShortComplex (DiscreteAbelianAction.{u, max u w} Gal(Ω/k))) (hS : S.ShortExact) :
    (S.map (fieldCoindCanonicalComplexFunctor.{u, w} k Ω)).ShortExact := by
  let T := DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)
  let U := DiscreteAbelianAction.forget.{u, max u w} Gal(Ω/k)
  have hU : (S.map U).ShortExact := (fieldModule_shortExact_iff_forget.{u, w} k Ω S).mp hS
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let Q := (S.map (fieldCoindCanonicalComplexFunctor.{u, w} k Ω)).map
    (HomologicalComplex.eval _ (ComplexShape.up ℕ) n)
  let : (Monad.monadPow T (n + 1)).PreservesZeroMorphisms :=
    DiscreteAbelianAction.coindMonadPower_preservesZero.{u, w} Gal(Ω/k) (n + 1)
  let P := S.map (Monad.monadPow T (n + 1))
  let e : Q ≅ P := ShortComplex.isoMk
    (Monad.coresolutionObjIso T S.X₁ n)
    (Monad.coresolutionObjIso T S.X₂ n)
    (Monad.coresolutionObjIso T S.X₃ n)
    (Monad.coresolutionObjIso_naturality T S.f n).symm
    (Monad.coresolutionObjIso_naturality T S.g n).symm
  exact ShortComplex.shortExact_of_iso e.symm
    (DiscreteAbelianAction.coindPower_shortExact.{u, w} Gal(Ω/k) S hU (n + 1))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every literal canonical coinduction term is acyclic for SAME native derived invariants. -/
theorem fieldCoindCanonicalComplex_rightDerived_isZero
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (q n : ℕ) :
    IsZero (((fieldInvariantFunctor.{u, w} k Ω).rightDerived (n + 1)).obj
      ((fieldCoindCanonicalComplex.{u, w} k Ω M).X q)) := by
  let G : ProfiniteGrp.{u} := InfiniteGalois.profiniteGalGrp k Ω
  let : LocallyCompactSpace G := by infer_instance
  let U := ContinuousCohomology.discreteCoefficientForget.{max u w}
  let B : DiscreteAbelianAction.{u, max u w} G :=
    (Monad.coresolution (DiscreteAbelianAction.coindMonad.{u, w} G) M).obj (SimplexCategory.mk q)
  have hnative : IsZero (continuousCohomology.{0, u, w} (n + 1)
      (DiscreteAbelianAction.toTopRep.obj B)) :=
    DiscreteAbelianAction.coindCoresolution_native_isZero_succ.{u, w} G M q n
  have hz : IsZero ((fieldContinuousCohomologyFunctor.{u, w} k Ω (n + 1)).obj B) := by
    change IsZero (U.obj (continuousCohomology.{0, u, w} (n + 1)
      (DiscreteAbelianAction.toTopRep.obj B)))
    exact U.map_isZero hnative
  change IsZero (((fieldInvariantFunctor.{u, w} k Ω).rightDerived (n + 1)).obj B)
  exact IsZero.of_iso hz ((fieldContinuousDerivedInvariantsIso.{u, w} k Ω (n + 1)).app B).symm

end AlgebraicGeometry.Scheme.DerivedSections
end

/-! Original qualified proof block: AlternatingCofaceFunctorComm -/
/-! Actual natural commutation of the alternating coface functor with additive coefficient functors. -/
@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe uC vC uD vD
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- The literal identity-component additive alternating comparison. -/
def actualAlternatingCoefficientIso
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (A : CosimplicialObject C) :
    AlternatingCofaceMapComplex.obj (A ⋙ F) ≅
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (AlternatingCofaceMapComplex.obj A)) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (fun i j hij => additiveAlternatingCofaceComm F A i j hij)

/-- The same actual identity components preserve every original cosimplicial arrow. -/
theorem actualAlternatingCoefficientIso_naturality
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {A B : CosimplicialObject C} (f : A ⟶ B) :
    AlternatingCofaceMapComplex.map (Functor.whiskerRight f F) ≫
      (actualAlternatingCoefficientIso F B).hom =
    (actualAlternatingCoefficientIso F A).hom ≫
      (F.mapHomologicalComplex (ComplexShape.up ℕ)).map (AlternatingCofaceMapComplex.map f) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change F.map (f.app (SimplexCategory.mk n)) ≫ 𝟙 _ =
    𝟙 _ ≫ F.map (f.app (SimplexCategory.mk n))
  exact (Category.comp_id _).trans (Category.id_comp _).symm

end AlgebraicGeometry.Scheme.DerivedSections
end

/-! Original qualified proof block: AlternatingCofaceFunctorNatComm -/
/-! Actual additive alternating commutation as one natural isomorphism. -/
@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe uC vC uD vD
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- The exact original coefficient commutation is natural in the actual cosimplicial object. -/
def actualAlternatingCoefficientNatIso
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] :
    (CosimplicialObject.whiskering C D).obj F ⋙ alternatingCofaceMapComplex D ≅
      alternatingCofaceMapComplex C ⋙ F.mapHomologicalComplex (ComplexShape.up ℕ) :=
  NatIso.ofComponents (actualAlternatingCoefficientIso F)
    (actualAlternatingCoefficientIso_naturality F)

end AlgebraicGeometry.Scheme.DerivedSections
end
