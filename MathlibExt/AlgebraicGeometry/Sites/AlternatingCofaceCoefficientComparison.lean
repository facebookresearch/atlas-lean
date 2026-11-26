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

/-!
# Coinduction exactness and additive coface comparisons

For a field `k` with separable closure `Ω`, the canonical coinduction complex of a discrete
Galois module preserves short exact coefficient sequences and has terms acyclic for positive
derived invariants.

For any additive functor between preadditive categories, the alternating coface complex
commutes with applying that functor. The degreewise identity coordinates are natural in
cosimplicial objects, with independent category universes.
-/

/-!
# Field coinduction complexes

The coefficient category consists of discrete Galois modules in universe `max u w`, for `k`
and its separable closure in universe `u`.
-/
/-!
Canonical coinduction complexes take short exact coefficient sequences to degreewise short
exact sequences. Each term is acyclic for positive derived invariants.
-/
@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- Canonical field coinduction complex preserves zero maps.

The canonical coinduction-complex functor on discrete `Gal(Ω/k)`-modules preserves zero
morphisms. -/
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
/-- Canonical coinduction complexes preserve short exact sequences.

A short exact sequence of discrete Galois modules remains short exact after the canonical
coinduction-complex functor. -/
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
/-- Canonical coinduction terms are acyclic for derived invariants.

Every cochain term of the canonical field coinduction complex has zero right-derived
invariants in every positive degree. -/
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

/-!
# Additive functors and alternating cofaces

An additive functor takes the alternating sum of cofaces to the alternating sum of their
images.
-/
/-!
Applying an additive coefficient functor to a cosimplicial object and then taking its
alternating complex agrees with applying it degreewise to the alternating complex.
-/
@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe uC vC uD vD
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- Additive functor commutes with an alternating coface complex.

For an additive functor `F : C ⥤ D` between preadditive categories, the alternating complex of
`A ⋙ F` is isomorphic to `F` applied degreewise to the alternating complex of `A`, with
identity component maps. -/
def actualAlternatingCoefficientIso
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (A : CosimplicialObject C) :
    AlternatingCofaceMapComplex.obj (A ⋙ F) ≅
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (AlternatingCofaceMapComplex.obj A)) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (fun i j hij => additiveAlternatingCofaceComm F A i j hij)

/-- Alternating coface coefficient comparison is natural.

The identity-component comparison commutes with maps of cosimplicial objects and their images
under the additive functor. -/
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

/-!
# Naturality of coface coefficient comparisons

A cosimplicial morphism commutes with the coefficient comparison in each cochain degree.
-/
/-!
The identity component maps give one natural isomorphism of the two alternating-coface
functors.
-/
@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe uC vC uD vD
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- Natural commutation of additive functors with alternating cofaces.

The objectwise comparisons assemble to a natural isomorphism between applying `F` before and
after the alternating coface-complex construction. -/
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
