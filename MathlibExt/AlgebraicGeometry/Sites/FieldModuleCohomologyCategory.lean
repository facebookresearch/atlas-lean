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

/-!
# Discrete Galois modules as a cohomology category

Let k and Ω be fields in universe u, with Ω a separable closure of k,
and G = Gal(Ω/k). The category D of discrete abelian groups with continuous
G-action and coefficient universe c = max(u, w) is abelian and has enough
injectives. The coefficients are abelian groups, regarded as ℤ-modules.

The geometric stalk at Spec Ω → Spec k gives an equivalence from
AddCommGrpCat c-valued étale sheaves on Spec k to D. The underlying-group
functor U : D → AddCommGrpCat c identifies with taking the stalk of
the inverse sheaf. It preserves finite limits, finite colimits and homology,
and detects short exact sequences by injectivity, equality of image and
kernel, and surjectivity of the underlying maps.

The topological representation of a coefficient retains its underlying
group and G-action. Its coinduction is C(G, M) with diagonal action,
constant-function unit, and evaluation at the identity on underlying groups.
-/

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


/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, and put G = Gal(Ω/k) and c = max(u, w). Let D be the category
of discrete abelian groups in universe c with continuous G-action.
FieldCohomologyModule k Ω is D, the category of discrete continuous
G-modules. Its objects are abelian groups with continuous G-action;
morphisms are equivariant additive maps. -/
abbrev FieldCohomologyModule := DiscreteAbelianAction.{u, max u w} Gal(Ω/k)

instance fieldModule_inverse_isEquivalence :
    (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).IsEquivalence :=
  (fieldSheafGaloisEquivalence.{u, w} k Ω).isEquivalence_inverse

instance fieldModule_stalk_isEquivalence :
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).IsEquivalence :=
  (fieldSheafGaloisEquivalence.{u, w} k Ω).isEquivalence_functor

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, and put G = Gal(Ω/k) and c = max(u, w). Let D be the category
of discrete abelian groups in universe c with continuous G-action.
The category D has finite products. They are the finite products of
the underlying abelian groups with diagonal G-action and discrete topology. -/
instance fieldModule_hasFiniteProducts : HasFiniteProducts (FieldCohomologyModule.{u, w} k Ω) where
  out n := by
    let : HasLimitsOfShape (Discrete (Fin n))
        (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :=
      HasFiniteProducts.out n
    exact Adjunction.hasLimitsOfShape_of_equivalence
      (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω)

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, and put G = Gal(Ω/k) and c = max(u, w). Let D be the category
of discrete abelian groups in universe c with continuous G-action.
The category D is abelian. Its abelian structure is compatible with
the equivalence between D and abelian sheaves on the small étale site
of Spec k given by the geometric stalk and invariant-skyscraper inverse. -/
@[instance_reducible]
def fieldModuleAbelian : Abelian (FieldCohomologyModule.{u, w} k Ω) :=
  abelianOfEquivalence (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω)

@[nolint defsWithUnderscore]
instance fieldModule_abelian : Abelian (FieldCohomologyModule.{u, w} k Ω) :=
  fieldModuleAbelian.{u, w} k Ω

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, and put G = Gal(Ω/k) and c = max(u, w). Let D be the category
of discrete abelian groups in universe c with continuous G-action.
The category D has enough injectives: every discrete continuous
G-module admits a monomorphism into an injective object of D. -/
theorem fieldModuleEnoughInjectives : EnoughInjectives (FieldCohomologyModule.{u, w} k Ω) :=
  EnoughInjectives.of_equivalence (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω)

instance fieldModule_enoughInjectives : EnoughInjectives (FieldCohomologyModule.{u, w} k Ω) :=
  fieldModuleEnoughInjectives.{u, w} k Ω

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, and put G = Gal(Ω/k) and c = max(u, w). Let D be the category
of discrete abelian groups in universe c with continuous G-action.
Let Φ : D → Sheaf(Spec k)_ét be the invariant-skyscraper inverse
to the geometric-stalk Galois equivalence, with coefficients in universe c.
Taking the stalk of Φ(M) at Spec Ω → Spec k is naturally isomorphic
to the underlying-group functor U(M). -/
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

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, and put G = Gal(Ω/k) and c = max(u, w). Let D be the category
of discrete abelian groups in universe c with continuous G-action.
For M ∈ D, the forward stalk-to-underlying-group isomorphism is
the underlying additive map of the Galois sheaf equivalence's counit
E(Φ(M)) → M, where E is the geometric-stalk functor. -/
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

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, and put G = Gal(Ω/k) and c = max(u, w). Let D be the category
of discrete abelian groups in universe c with continuous G-action.
For a short complex S₁ → S₂ → S₃ in D, it is short exact if
and only if the underlying abelian-group short complex is short exact.
The forgetful functor U therefore preserves and reflects short exactness. -/
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

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, and put G = Gal(Ω/k) and c = max(u, w). Let D be the category
of discrete abelian groups in universe c with continuous G-action.
A short complex with equivariant additive maps a : M₁ → M₂ and
b : M₂ → M₃ is short exact in D exactly when the underlying a is
injective, range(a) = ker(b), and the underlying b is surjective. -/
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

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, and put G = Gal(Ω/k) and c = max(u, w). Let D be the category
of discrete abelian groups in universe c with continuous G-action.
This proposition collects D's abelian structure and enough injectives;
the fully faithful realization as discrete topological ℤ-representations
with unchanged group, action and morphism values; and coinduction
C(G, M), with (g • φ)(x) = g • φ(g⁻¹x), postcomposition on maps,
constant unit and evaluation at 1. It also records monicity of that unit,
finite-limit, finite-colimit and homology preservation by U, the inverse-sheaf
stalk counit formula, and both categorical and elementwise short-exactness criteria. -/
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

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, and put G = Gal(Ω/k) and c = max(u, w). Let D be the category
of discrete abelian groups in universe c with continuous G-action.
The discrete continuous G-action category has all the stated
abelian, injective, topological realization and coinduction properties.
Its underlying-group functor is exact, identifies with the inverse-sheaf
geometric stalk via the counit, and detects short exactness through
injectivity, image–kernel equality and surjectivity. -/
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
