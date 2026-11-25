/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.AlgebraicGeometry.Sites.FieldCanonicalCoindResolution

/-! Actual canonical coinduction resolutions of every original field coefficient. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- The actual original alternating coinduction complex, functorial in its same coefficient. -/
abbrev fieldCoindCanonicalComplexFunctor :
    DiscreteAbelianAction.{u, max u w} Gal(Ω/k) ⥤
      CochainComplex (DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) ℕ :=
  Monad.coresolutionFunctor (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)) ⋙
    alternatingCofaceMapComplex _

set_option backward.isDefEq.respectTransparency.types false in
/-- Its coefficient-map component is the actual stored canonical coresolution map. -/
theorem fieldCoindCanonicalComplexFunctor_map_f
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (f : M ⟶ N) (n : ℕ) :
    ((fieldCoindCanonicalComplexFunctor.{u, w} k Ω).map f).f n =
      ((Monad.coresolutionFunctor (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k))).map f).app
        (SimplexCategory.mk n) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The same actual coefficient map preserves the canonical degree-zero augmented unit. -/
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
/-- The full actual augmented map is fixed by its degree-zero original unit square. -/
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
/-- The actual geometric equivalence counit transports the canonical coaugmentation
quasi-isomorphism to every original coefficient, without a homology-reflection premise. -/
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
