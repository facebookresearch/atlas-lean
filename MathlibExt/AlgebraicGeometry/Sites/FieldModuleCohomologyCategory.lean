/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.Action.DiscreteTopRep
public import MathlibExt.AlgebraicGeometry.Sites.FieldSheafGaloisEquivalence
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleGeometricStalkExactness
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! # The actual field-module category for continuous cohomology -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w

namespace AlgebraicGeometry.Scheme.DerivedSections

attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

instance fieldModule_isAlgebraic : Algebra.IsAlgebraic k Ω :=
  IsSepClosure.separable.isAlgebraic

instance fieldModule_isIntegral : Algebra.IsIntegral k Ω :=
  Algebra.isAlgebraic_iff_isIntegral.mp (IsSepClosure.separable.isAlgebraic)

instance fieldModule_totallyDisconnected : TotallyDisconnectedSpace Gal(Ω/k) := by
  infer_instance


/-- The category of discrete `Gal(Ω/k)`-modules, with coefficients in universe `max u w`. -/
abbrev FieldCohomologyModule := DiscreteAbelianAction.{u, max u w} Gal(Ω/k)

instance fieldModule_inverse_isEquivalence :
    (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).IsEquivalence :=
  (fieldSheafGaloisEquivalence.{u, w} k Ω).isEquivalence_inverse

instance fieldModule_stalk_isEquivalence :
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).IsEquivalence :=
  (fieldSheafGaloisEquivalence.{u, w} k Ω).isEquivalence_functor

/-- Finite products are transported through the actual constructed inverse. -/
instance fieldModule_hasFiniteProducts : HasFiniteProducts (FieldCohomologyModule.{u, w} k Ω) where
  out n := by
    let : HasLimitsOfShape (Discrete (Fin n))
        (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :=
      HasFiniteProducts.out n
    exact Adjunction.hasLimitsOfShape_of_equivalence
      (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω)

/-- The original action category is abelian by the same actual sheaf equivalence. -/
@[instance_reducible]
def fieldModuleAbelian : Abelian (FieldCohomologyModule.{u, w} k Ω) :=
  abelianOfEquivalence (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω)

@[nolint defsWithUnderscore]
instance fieldModule_abelian : Abelian (FieldCohomologyModule.{u, w} k Ω) :=
  fieldModuleAbelian.{u, w} k Ω

/-- Enough injectives come from the actual common sheaf category through the same inverse. -/
theorem fieldModuleEnoughInjectives : EnoughInjectives (FieldCohomologyModule.{u, w} k Ω) :=
  EnoughInjectives.of_equivalence (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω)

instance fieldModule_enoughInjectives : EnoughInjectives (FieldCohomologyModule.{u, w} k Ω) :=
  fieldModuleEnoughInjectives.{u, w} k Ω

/-- The fixed counit identifies R followed by the original exact stalk with actual U. -/
def fieldModuleForgetIso :
    fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω ⋙
        smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω) ≅
      DiscreteAbelianAction.forget Gal(Ω/k) := by
  let E := fieldSheafGaloisEquivalence.{u, w} k Ω
  let U := DiscreteAbelianAction.forget.{u, max u w} Gal(Ω/k)
  refine NatIso.ofComponents (fun M => U.mapIso (E.counitIso.app M)) ?_
  intro M N f
  change U.map (E.functor.map (E.inverse.map f)) ≫ U.map (E.counitIso.hom.app N) =
    U.map (E.counitIso.hom.app M) ≫ U.map f
  rw [← U.map_comp, ← U.map_comp]
  exact congrArg U.map (E.counitIso.hom.naturality f)

/-- Its forward map is exactly forgetting the SAME evaluation counit. -/
theorem fieldModuleForgetIso_hom (M : FieldCohomologyModule.{u, w} k Ω) :
    (fieldModuleForgetIso.{u, w} k Ω).hom.app M =
      (DiscreteAbelianAction.forget Gal(Ω/k)).map
        ((fieldSheafGaloisEquivalence.{u, w} k Ω).counitIso.hom.app M) := by
  rfl

instance fieldModuleForget_additive :
    (DiscreteAbelianAction.forget.{u, max u w} Gal(Ω/k)).Additive where
  map_add := by intro M N f g; rfl

instance fieldModuleForget_preservesFiniteLimits :
    PreservesFiniteLimits (DiscreteAbelianAction.forget.{u, max u w} Gal(Ω/k)) :=
  preservesFiniteLimits_of_natIso (fieldModuleForgetIso.{u, w} k Ω)

instance fieldModuleForget_preservesFiniteColimits :
    PreservesFiniteColimits (DiscreteAbelianAction.forget.{u, max u w} Gal(Ω/k)) :=
  preservesFiniteColimits_of_natIso (fieldModuleForgetIso.{u, w} k Ω)

instance fieldModuleForget_preservesHomology :
    (DiscreteAbelianAction.forget.{u, max u w} Gal(Ω/k)).PreservesHomology := by
  infer_instance

/-- Actual categorical short exactness is preserved and reflected by actual U. -/
theorem fieldModule_shortExact_iff_forget
    (S : ShortComplex (FieldCohomologyModule.{u, w} k Ω)) :
    S.ShortExact ↔ (S.map (DiscreteAbelianAction.forget Gal(Ω/k))).ShortExact := by
  constructor
  · intro hS
    exact hS.map_of_exact (DiscreteAbelianAction.forget Gal(Ω/k))
  · intro hS
    let U := DiscreteAbelianAction.forget.{u, max u w} Gal(Ω/k)
    exact ShortComplex.ShortExact.mk'
      (Functor.reflects_exact_of_faithful U S hS.exact)
      (U.mono_of_mono_map hS.mono_f) (U.epi_of_epi_map hS.epi_g)

/-- The complete literal criterion for every stored original pair of maps. -/
theorem fieldModule_shortExact_iff_original_maps
    (S : ShortComplex (FieldCohomologyModule.{u, w} k Ω)) :
    S.ShortExact ↔
      Function.Injective (DiscreteAbelianAction.homToAdd S.f) ∧
      (DiscreteAbelianAction.homToAdd S.f).range =
        (DiscreteAbelianAction.homToAdd S.g).ker ∧
      Function.Surjective (DiscreteAbelianAction.homToAdd S.g) := by
  rw [fieldModule_shortExact_iff_forget.{u, w} k Ω S]
  let U := DiscreteAbelianAction.forget.{u, max u w} Gal(Ω/k)
  constructor
  · intro hS
    exact ⟨hS.ab_injective_f, hS.exact.ab_range_eq_ker, hS.ab_surjective_g⟩
  · rintro ⟨hf, hex, hg⟩
    exact ShortComplex.ShortExact.mk'
      ((S.map U).ab_exact_iff_range_eq_ker.mpr hex)
      ((AddCommGrpCat.mono_iff_injective _).mpr hf)
      ((AddCommGrpCat.epi_iff_surjective _).mpr hg)

/-- All category, original coinduction and actual underlying-map laws together. -/
def OriginalFieldModuleCohomologyCategoryLaws : Prop :=
  let D := FieldCohomologyModule.{u, w} k Ω
  let P := DiscreteAbelianAction.toTopRep.{u, max u w} (G := Gal(Ω/k))
  let C := DiscreteAbelianAction.coind.{u, w} (G := Gal(Ω/k))
  let U := DiscreteAbelianAction.forget.{u, max u w} Gal(Ω/k)
  Nonempty (Abelian D) ∧ EnoughInjectives D ∧
  (∀ M : D, (P.obj M).V = DiscreteAbelianAction.underlying M) ∧
  (∀ (M : D) (g : Gal(Ω/k)) (m : DiscreteAbelianAction.underlying M),
    (P.obj M).ρ g m = g • m) ∧
  (∀ (M N : D) (f : M ⟶ N) (m : DiscreteAbelianAction.underlying M),
    (P.map f).hom m = DiscreteAbelianAction.homToAdd f m) ∧
  P.Full ∧ P.Faithful ∧
  (∀ M : D, DiscreteTopology (P.obj M)) ∧
  (∀ M : D, ((TopRep.toActionTopModFunc (k := ℤ) (G := Gal(Ω/k))).obj
    (P.obj M)).IsContinuous) ∧
  (∀ M : D, (DiscreteAbelianAction.underlying (C.obj M) : Type (max u w)) =
    C(Gal(Ω/k), DiscreteAbelianAction.underlying M)) ∧
  (∀ (M : D) (g x : Gal(Ω/k)) (F : DiscreteAbelianAction.underlying (C.obj M)),
    DiscreteAbelianAction.coindFunction.{u, w} M
      (((C.obj M).obj.obj.ρ g).asHom.hom F) x =
      (M.obj.obj.ρ g).asHom.hom (DiscreteAbelianAction.coindFunction.{u, w} M F (g⁻¹ * x))) ∧
  (∀ (M N : D) (f : M ⟶ N) (F : DiscreteAbelianAction.underlying (C.obj M))
    (x : Gal(Ω/k)), DiscreteAbelianAction.coindFunction.{u, w} N
      (DiscreteAbelianAction.homToAdd (C.map f) F) x =
      DiscreteAbelianAction.homToAdd f (DiscreteAbelianAction.coindFunction.{u, w} M F x)) ∧
  (∀ (M : D) (m : DiscreteAbelianAction.underlying M) (x : Gal(Ω/k)),
    DiscreteAbelianAction.coindFunction.{u, w} M
      (DiscreteAbelianAction.homToAdd (DiscreteAbelianAction.coindIota.{u, w}.app M) m) x = m) ∧
  (∀ (M : D) (F : DiscreteAbelianAction.underlying (C.obj M)),
    DiscreteAbelianAction.coindEvalOne.{u, w} M F =
      DiscreteAbelianAction.coindFunction.{u, w} M F 1) ∧
  (∀ (M : D) (m : DiscreteAbelianAction.underlying M),
    DiscreteAbelianAction.coindEvalOne.{u, w} M
      (DiscreteAbelianAction.homToAdd (DiscreteAbelianAction.coindIota.{u, w}.app M) m) = m) ∧
  (∀ M : D, Mono (DiscreteAbelianAction.coindIota.{u, w}.app M)) ∧
  PreservesFiniteLimits U ∧ PreservesFiniteColimits U ∧ U.PreservesHomology ∧
  (∀ M : D, (fieldModuleForgetIso.{u, w} k Ω).hom.app M =
    U.map ((fieldSheafGaloisEquivalence.{u, w} k Ω).counitIso.hom.app M)) ∧
  (∀ S : ShortComplex D, S.ShortExact ↔ (S.map U).ShortExact) ∧
  ∀ S : ShortComplex D, S.ShortExact ↔
    Function.Injective (DiscreteAbelianAction.homToAdd S.f) ∧
    (DiscreteAbelianAction.homToAdd S.f).range = (DiscreteAbelianAction.homToAdd S.g).ker ∧
    Function.Surjective (DiscreteAbelianAction.homToAdd S.g)

/-- The full actual field-module category source unit, with no structure certificates. -/
theorem original_field_module_cohomology_category :
    OriginalFieldModuleCohomologyCategoryLaws.{u, w} k Ω := by
  refine ⟨⟨fieldModuleAbelian.{u, w} k Ω⟩, fieldModuleEnoughInjectives.{u, w} k Ω,
    DiscreteAbelianAction.toTopRep_obj, DiscreteAbelianAction.toTopRep_action,
    (fun _ _ f m => DiscreteAbelianAction.toTopRep_map_apply f m),
    inferInstance, inferInstance, (fun M => inferInstance),
    DiscreteAbelianAction.toTopRep_action_isContinuous,
    DiscreteAbelianAction.coind_obj, DiscreteAbelianAction.coind_action_apply,
    (fun _ _ f F x => DiscreteAbelianAction.coind_map_apply f F x),
    DiscreteAbelianAction.coindIota_apply, DiscreteAbelianAction.coindEvalOne_apply,
    DiscreteAbelianAction.coindEvalOne_iota, (fun M => inferInstance),
    inferInstance, inferInstance, inferInstance, fieldModuleForgetIso_hom.{u, w} k Ω,
    fieldModule_shortExact_iff_forget.{u, w} k Ω,
    fieldModule_shortExact_iff_original_maps.{u, w} k Ω⟩

end AlgebraicGeometry.Scheme.DerivedSections
