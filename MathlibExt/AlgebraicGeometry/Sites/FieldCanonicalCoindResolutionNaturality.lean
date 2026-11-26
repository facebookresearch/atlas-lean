/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.AlgebraicGeometry.Sites.FieldCanonicalCoindResolution

/-!
# Natural canonical coinduction resolutions

Canonical coinduction complexes vary functorially in discrete Galois coefficients. Their maps
are the coefficient maps of the monad coresolution in each degree, and the coaugmentation is
natural.

The coaugmentation is a quasi-isomorphism for every discrete Galois module in the common
coefficient universe.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- Functor of canonical coinduction complexes.

The coinduction-monad coresolution functor followed by alternating cofaces gives the canonical
cochain-complex functor. -/
abbrev fieldCoindCanonicalComplexFunctor :
    DiscreteAbelianAction.{u, max u w} Gal(Ω/k) ⥤
      CochainComplex (DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) ℕ :=
  Monad.coresolutionFunctor (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)) ⋙
    alternatingCofaceMapComplex _

set_option backward.isDefEq.respectTransparency.types false in
/-- Canonical coinduction map in a fixed degree.

The degree-`n` map of a coefficient morphism is the monad-coresolution natural transformation
evaluated at the simplex of degree `n`. -/
theorem fieldCoindCanonicalComplexFunctor_map_f
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (f : M ⟶ N) (n : ℕ) :
    ((fieldCoindCanonicalComplexFunctor.{u, w} k Ω).map f).f n =
      ((Monad.coresolutionFunctor (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k))).map f).app
        (SimplexCategory.mk n) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Degree zero coaugmentation is natural in coefficients.

The source coaugmentation component followed by the degree-zero coinduction map equals the
coefficient map followed by the target coaugmentation component. -/
theorem fieldCoindCanonicalCoaugmentation_coefficient_zero
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (f : M ⟶ N) :
    (fieldCoindCanonicalCoaugmentation.{u, w} k Ω M).f 0 ≫
      ((fieldCoindCanonicalComplexFunctor.{u, w} k Ω).map f).f 0 =
    f ≫ (fieldCoindCanonicalCoaugmentation.{u, w} k Ω N).f 0 := by
  rw [fieldCoindCanonicalCoaugmentation_f_zero, fieldCoindCanonicalCoaugmentation_f_zero,
    fieldCoindCanonicalComplexFunctor_map_f, Monad.coresolutionAugmented_hom_zero,
    Monad.coresolutionAugmented_hom_zero]
  let T := DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)
  have h := Monad.coresolutionObjIso_naturality T f 0
  have hM : (Monad.coresolutionObjIso T M 0).hom = 𝟙 (T.obj M) := by
    rw [Monad.coresolutionObjIso_hom]
    rfl
  have hN : (Monad.coresolutionObjIso T N 0).hom = 𝟙 (T.obj N) := by
    rw [Monad.coresolutionObjIso_hom]
    rfl
  have h' : ((Monad.coresolutionFunctor T).map f).app (SimplexCategory.mk 0) = T.map f :=
    (Category.comp_id _).symm.trans
      ((congrArg (fun q => ((Monad.coresolutionFunctor T).map f).app (SimplexCategory.mk 0) ≫ q)
          hN.symm).trans (h.trans
          ((congrArg (fun q => q ≫ (Monad.monadPow T 1).map f) hM).trans (Category.id_comp _))))
  exact (congrArg (fun q : T.obj M ⟶ T.obj N => T.η.app M ≫ q) h').trans (T.η.naturality f).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Coinduction coaugmentation is coefficient natural.

The full coaugmentation square commutes with a coefficient map and its image under the
canonical coinduction-complex functor. -/
theorem fieldCoindCanonicalCoaugmentation_coefficient_naturality
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (f : M ⟶ N) :
    fieldCoindCanonicalCoaugmentation.{u, w} k Ω M ≫
      (fieldCoindCanonicalComplexFunctor.{u, w} k Ω).map f =
    (CochainComplex.single₀ _).map f ≫ fieldCoindCanonicalCoaugmentation.{u, w} k Ω N := by
  apply (CochainComplex.fromSingle₀Equiv _ _).injective
  apply Subtype.ext
  change (fieldCoindCanonicalCoaugmentation.{u, w} k Ω M ≫
      (fieldCoindCanonicalComplexFunctor.{u, w} k Ω).map f).f 0 =
    ((CochainComplex.single₀ _).map f ≫ fieldCoindCanonicalCoaugmentation.{u, w} k Ω N).f 0
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero]
  exact fieldCoindCanonicalCoaugmentation_coefficient_zero.{u, w} k Ω f

set_option backward.isDefEq.respectTransparency.types false in
/-- Every canonical coinduction coaugmentation is a quasi isomorphism.

The canonical map from a discrete Galois module in degree zero to its coinduction complex is a
quasi-isomorphism. -/
theorem fieldCoindCanonicalCoaugmentation_quasiIso
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    QuasiIso (fieldCoindCanonicalCoaugmentation.{u, w} k Ω M) := by
  let E := fieldSheafGaloisEquivalence.{u, w} k Ω
  let F := E.inverse.obj M
  let e := E.counitIso.app M
  have hgeometric : QuasiIso (fieldCoindCanonicalCoaugmentation.{u, w} k Ω (E.functor.obj F)) :=
    fieldCoindCanonicalCoaugmentation_quasiIso_geometric.{u, w} k Ω F
  let : QuasiIso (fieldCoindCanonicalCoaugmentation.{u, w} k Ω (E.functor.obj F)) := hgeometric
  let R := fieldCoindCanonicalComplexFunctor.{u, w} k Ω
  let q := R.map e.hom
  have hqIso : IsIso q := (R.mapIso e).isIso_hom
  have hq : QuasiIso q := quasiIso_of_isIso q
  have hsource : QuasiIso (fieldCoindCanonicalCoaugmentation.{u, w} k Ω (E.functor.obj F) ≫ q) :=
    quasiIso_comp _ _ (hφ := hgeometric) (hφ' := hq)
  have htarget : QuasiIso ((CochainComplex.single₀ _).map e.hom ≫
      fieldCoindCanonicalCoaugmentation.{u, w} k Ω M) :=
    (fieldCoindCanonicalCoaugmentation_coefficient_naturality.{u, w} k Ω e.hom) ▸ hsource
  let : QuasiIso ((CochainComplex.single₀ _).map e.hom ≫
      fieldCoindCanonicalCoaugmentation.{u, w} k Ω M) := htarget
  let q₀ := (CochainComplex.single₀ (DiscreteAbelianAction.{u, max u w} Gal(Ω/k))).map e.hom
  have hq₀Iso : IsIso q₀ := ((CochainComplex.single₀ _).mapIso e).isIso_hom
  let : QuasiIso q₀ := quasiIso_of_isIso q₀
  exact quasiIso_of_comp_left q₀ _

end AlgebraicGeometry.Scheme.DerivedSections
