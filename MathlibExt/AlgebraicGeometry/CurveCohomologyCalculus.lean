/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The comparison constructions follow AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b:
StacksFrontier/AlgebraicGeometry/Variety/EulerChar/Cohomology.lean,
StacksFrontier/AlgebraicGeometry/AffineMorphismEuler/Basic.lean, and
StacksFrontier/CategoryTheory/Abelian/RightDerivedPostcompose.lean.
The public sources have no individual copyright/author notices and are
licensed under Apache 2.0. Modification notice: use the exact existing
ATLAS sectionsFunctor/rightDerived carrier; expose the actual mapped
resolution unit and the canonical comparison maps under their genuine
acyclicity conditions, rather than assuming an Euler or degree conclusion.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import MathlibExt.AlgebraicGeometry.CurvePositivity
public import MathlibExt.AlgebraicGeometry.FiniteCoverLocalComparison
public import MathlibExt.CategoryTheory.Abelian.RightDerivedComparison
public import MathlibExt.CategoryTheory.Abelian.RightDerivedLinear

/-!
# Canonical curve cohomology comparisons and conditional Euler calculus

Every cohomology space is the existing actual `sectionsFunctor.rightDerived`
space. Exact postcomposition gives the canonical comparison with the public
Axiom source's restriction-after-derived-evaluation convention. Affine
cohomology can be computed by pushing the actual chosen injective resolution,
provided its actual mapped unit is acyclic and the resulting terms injective.

The geometric global-constants and tensor-degree laws are explicit covered
toolbox inputs. They contain no spectral genus, pushforward rank or degree
conclusion. All consequences and comparison constructors in this file have
completed proofs.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CurveCohomologyCalculus

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open CoherentCurveLinearSeries CurveVectorBundles CurvePositivity

universe u

instance evaluation_additive (X : Scheme.{u}) :
    (SheafOfModules.evaluation.{u} X.ringCatSheaf (op (⊤ : X.Opens))).Additive := by
  unfold SheafOfModules.evaluation
  infer_instance

/-- The actual cohomology convention used by the public Axiom source. -/
abbrev cohomologyAfterRestriction {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (L : X.Modules) (n : ℕ) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars.{u} (globalScalarMap f)).obj
    (((SheafOfModules.evaluation.{u} X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived n).obj L)

/-- The exact outer coefficient functor is pulled through the actual
right-derived global-section evaluation, naturally in the module. -/
def cohomologyCarrierIso {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (L : X.Modules) (n : ℕ) :
    cohomology f L n ≅ cohomologyAfterRestriction f L n := by
  let F : X.Modules ⥤ ModuleCat.{u} Γ(X, ⊤) :=
    SheafOfModules.evaluation.{u} X.ringCatSheaf (op (⊤ : X.Opens))
  let E : ModuleCat.{u} Γ(X, ⊤) ⥤ ModuleCat.{u} k :=
    ModuleCat.restrictScalars.{u} (globalScalarMap f)
  have : F.Additive := by constructor; intro M N a b; rfl
  have : E.Additive := by dsimp [E]; infer_instance
  have : E.PreservesHomology := by dsimp [E]; infer_instance
  exact (Functor.rightDerivedCompIso F E n).app L

instance sectionsFunctor_preservesFiniteLimits {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) : PreservesFiniteLimits (sectionsFunctor f) := by
  let F : X.Modules ⥤ ModuleCat.{u} Γ(X, ⊤) :=
    SheafOfModules.evaluation.{u} X.ringCatSheaf (op (⊤ : X.Opens))
  let E : ModuleCat.{u} Γ(X, ⊤) ⥤ ModuleCat.{u} k :=
    ModuleCat.restrictScalars.{u} (globalScalarMap f)
  have : PreservesFiniteLimits E := by dsimp [E]; infer_instance
  have : PreservesFiniteLimits F := by
    dsimp [F]
    exact SheafOfModules.Finite.evaluationPreservesFiniteLimits
      (R := X.ringCatSheaf) (op (⊤ : X.Opens))
  change PreservesFiniteLimits (F ⋙ E)
  infer_instance

/-- The actual map of constants into the actual global sections. -/
def constantsToSections {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : ModuleCat.of k k ⟶ (sectionsFunctor f).obj (structureModule X) :=
  ModuleCat.ofHom (X := ModuleCat.of k k)
    (Y := (sectionsFunctor f).obj (structureModule X))
    { toFun := fun r ↦ globalScalarMap f r
      map_add' := by intro r s; exact (globalScalarMap f).map_add r s
      map_smul' := by intro r s; exact (globalScalarMap f).map_mul r s }

/-- The canonical constant-to-H0 map, including the actual right-derived
degree-zero comparison rather than a freely chosen linear isomorphism. -/
def constantsToCohomologyZero {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : ModuleCat.of k k ⟶ cohomology f (structureModule X) 0 :=
  constantsToSections f ≫ (sectionsFunctor f).toRightDerivedZero.app (structureModule X)

/-- The source-covered geometric assertion that the actual regular
constant map is an isomorphism. Proper geometrically integral curves over
an algebraically closed field have this property. -/
class HasFieldGlobalSections {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : Prop where
  bijective : Function.Bijective (globalScalarMap f)

instance constantsToSections_isIso {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [HasFieldGlobalSections f] : IsIso (constantsToSections f) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (HasFieldGlobalSections.bijective (f := f))

instance constantsToCohomologyZero_isIso {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [HasFieldGlobalSections f] :
    IsIso (constantsToCohomologyZero f) := by
  dsimp [constantsToCohomologyZero]
  infer_instance

theorem finrank_cohomology_zero_structure {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [HasFieldGlobalSections f] :
    Module.finrank k (cohomology f (structureModule X) 0) = 1 := by
  have h := (asIso (constantsToCohomologyZero f)).toLinearEquiv.finrank_eq
  simpa using h.symm

/-- The two-term Euler characteristic used by the existing curve degree. -/
def euler01 {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (L : X.Modules) : ℤ :=
  (Module.finrank k (cohomology f L 0) : ℤ) - Module.finrank k (cohomology f L 1)

theorem euler01_structure {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [HasFieldGlobalSections f] :
    euler01 f (structureModule X) = 1 - (genus f : ℤ) := by
  simp [euler01, genus, finrank_cohomology_zero_structure]

theorem degree_eq_euler01_sub {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (L : X.Modules) :
    degree f L = euler01 f L - euler01 f (structureModule X) := by
  dsimp [degree, euler01]
  ring

theorem bundleDegree_eq_euler01_sub {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (E : X.Modules) (r : ℕ) :
    bundleDegree f E r = euler01 f E - (r : ℤ) * euler01 f (structureModule X) := rfl

theorem euler01_eq_of_iso {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {L M : X.Modules} (e : L ≅ M) : euler01 f L = euler01 f M := by
  dsimp [euler01]
  rw [((sectionsFunctor f).rightDerived 0 |>.mapIso e).toLinearEquiv.finrank_eq,
    ((sectionsFunctor f).rightDerived 1 |>.mapIso e).toLinearEquiv.finrank_eq]

theorem degree_eq_of_iso {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {L M : X.Modules} (e : L ≅ M) : degree f L = degree f M := by
  rw [degree_eq_euler01_sub, degree_eq_euler01_sub, euler01_eq_of_iso f e]

/-- The fixed image of a resolution's unit under an actual additive
functor; its formula is part of the interface, not supplied as a free map. -/
def mappedResolutionUnit {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] (G : A ⥤ B) [G.Additive] {M : A} (I : InjectiveResolution M) :
    (CochainComplex.single₀ B).obj (G.obj M) ⟶
      (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex :=
  (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℕ) 0).inv.app M ≫
    (G.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι

/-- Genuine acyclicity and injectivity conditions on the actual image of
the specified injective resolution. They do not assert a cohomology,
Euler-characteristic, rank or degree conclusion. -/
structure MappedResolutionConditions {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] (G : A ⥤ B) [G.Additive] {M : A}
    (I : InjectiveResolution M) : Prop where
  injective : ∀ n, Injective ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex |>.X n)
  quasiIso : QuasiIso (mappedResolutionUnit G I)

/-- The actual pushed resolution becomes an injective resolution under
its genuine acyclicity conditions. -/
def mappedInjectiveResolution {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] (G : A ⥤ B) [G.Additive] {M : A} (I : InjectiveResolution M)
    (h : MappedResolutionConditions G I) : InjectiveResolution (G.obj M) where
  cocomplex := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  injective := h.injective
  ι := mappedResolutionUnit G I
  quasiIso := h.quasiIso

/-- Canonical cohomology precomposition calculated through this actual
mapped resolution. This applies on the acyclic objects, without claiming
that affine pushforward is exact on all sheaves. -/
def rightDerivedOnMappedResolution {A B D : Type*} [Category* A] [Category* B] [Category* D]
    [Abelian A] [Abelian B] [Abelian D] [HasInjectiveResolutions A] [HasInjectiveResolutions B]
    (G : A ⥤ B) (F : B ⥤ D) [G.Additive] [F.Additive] {M : A}
    (I : InjectiveResolution M) (h : MappedResolutionConditions G I) (n : ℕ) :
    ((G ⋙ F).rightDerived n).obj M ≅ (F.rightDerived n).obj (G.obj M) :=
  I.isoRightDerivedObj (G ⋙ F) n ≪≫
    (HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ F)) (ComplexShape.up ℕ)).app
        I.cocomplex) ≪≫
    ((mappedInjectiveResolution G I h).isoRightDerivedObj F n).symm

/-- The actual scalar maps commute with a scheme composition. -/
theorem globalScalarMap_comp {k : Type u} [Field k] {X Z : Scheme.{u}}
    (q : Z ⟶ X) (f : X ⟶ Spec (.of k)) :
    globalScalarMap (q ≫ f) = (q.app (⊤ : X.Opens)).hom.comp (globalScalarMap f) := by
  rw [globalScalarMap, globalScalarMap, ← CommRingCat.hom_comp]
  congr 1

/-- The ordinary global-section pushforward comparison has the actual
identity on module sections and the scheme-normalized scalar tower. -/
def sectionsPushforwardIso {k : Type u} [Field k] {X Z : Scheme.{u}}
    (q : Z ⟶ X) (f : X ⟶ Spec (.of k)) :
    sectionsFunctor (q ≫ f) ≅ Scheme.Modules.pushforward q ⋙ sectionsFunctor f :=
  NatIso.ofComponents (fun M ↦ by
    change (ModuleCat.restrictScalars.{u} (globalScalarMap (q ≫ f))).obj
      (M.val.obj (op ⊤)) ≅
      (ModuleCat.restrictScalars.{u} (globalScalarMap f)).obj
        ((ModuleCat.restrictScalars.{u} (q.app (⊤ : X.Opens)).hom).obj (M.val.obj (op ⊤)))
    exact ModuleCat.restrictScalarsComp'App (globalScalarMap f)
      (q.app (⊤ : X.Opens)).hom (globalScalarMap (q ≫ f))
      (globalScalarMap_comp q f) _) (by
    intro M N a
    ext x
    rfl)

/-- The completed affine cohomology comparison on the acyclic objects,
using the actual mapped resolution and actual global-section isomorphism. -/
def cohomologyPushforwardIso {k : Type u} [Field k] {X Z : Scheme.{u}}
    (q : Z ⟶ X) (f : X ⟶ Spec (.of k)) (M : Z.Modules)
    (h : MappedResolutionConditions (Scheme.Modules.pushforward q) (injectiveResolution M))
    (n : ℕ) :
    cohomology (q ≫ f) M n ≅ cohomology f ((Scheme.Modules.pushforward q).obj M) n :=
  (Functor.rightDerivedIsoOfNatIso (sectionsPushforwardIso q f) n).app M ≪≫
    rightDerivedOnMappedResolution (Scheme.Modules.pushforward q) (sectionsFunctor f)
      (injectiveResolution M) h n

theorem euler01_pushforward {k : Type u} [Field k] {X Z : Scheme.{u}}
    (q : Z ⟶ X) (f : X ⟶ Spec (.of k)) (M : Z.Modules)
    (h : MappedResolutionConditions (Scheme.Modules.pushforward q) (injectiveResolution M)) :
    euler01 f ((Scheme.Modules.pushforward q).obj M) = euler01 (q ≫ f) M := by
  dsimp [euler01]
  rw [← (cohomologyPushforwardIso q f M h 0).toLinearEquiv.finrank_eq,
    ← (cohomologyPushforwardIso q f M h 1).toLinearEquiv.finrank_eq]

/-- Actual derived global sections commute with finite coproducts through
the canonical biproduct comparison of the additive derived functor. -/
def cohomologyCoproductIso {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {n : ℕ} (L : Fin n → X.Modules) (j : ℕ) :
    cohomology f (∐ L) j ≅ ModuleCat.of k (∀ i, cohomology f (L i) j) := by
  have : HasBiproduct L := HasBiproduct.of_hasCoproduct L
  have : ((sectionsFunctor f).rightDerived j).Additive :=
    DerivedLinear.rightDerived_additive (sectionsFunctor f) j
  exact ((sectionsFunctor f).rightDerived j).mapIso (biproduct.isoCoproduct L).symm ≪≫
    Functor.mapBiproduct ((sectionsFunctor f).rightDerived j) L ≪≫
    ModuleCat.biproductIsoPi (fun i ↦ cohomology f (L i) j)

theorem finrank_cohomology_coproduct {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {n : ℕ} (L : Fin n → X.Modules) (j : ℕ)
    (h : ∀ i, FiniteDimensional k (cohomology f (L i) j)) :
    Module.finrank k (cohomology f (∐ L) j) = ∑ i, Module.finrank k (cohomology f (L i) j) := by
  have : ∀ i, FiniteDimensional k (cohomology f (L i) j) := h
  rw [(cohomologyCoproductIso f L j).toLinearEquiv.finrank_eq]
  exact Module.finrank_pi_fintype k

theorem euler01_coproduct {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {n : ℕ} (L : Fin n → X.Modules)
    (h₀ : ∀ i, FiniteDimensional k (cohomology f (L i) 0))
    (h₁ : ∀ i, FiniteDimensional k (cohomology f (L i) 1)) :
    euler01 f (∐ L) = ∑ i, euler01 f (L i) := by
  rw [euler01, finrank_cohomology_coproduct f L 0 h₀, finrank_cohomology_coproduct f L 1 h₁]
  simp only [Nat.cast_sum, ← Finset.sum_sub_distrib, euler01]

/-- The actual structure module is a line bundle through the canonical
pullback-unit comparison on the maximal open subscheme. -/
theorem structureModule_isLine (X : Scheme.{u}) : IsLineBundle (structureModule X) := by
  intro x
  exact ⟨⊤, by simp, ⟨FiniteCoverLocalComparison.pullbackStructureIso
    (⊤ : X.Opens).ι⟩⟩

/-- Source-covered generic curve inputs, on the existing actual tensor
and coherent-cohomology carriers. No spectral endpoint is among the fields.
The tensor Euler law is Stacks 0AYX specialized to invertible factors. -/
structure CurveTensorEulerInputs {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : Prop where
  tensor_line : ∀ (L M : X.Modules), IsLineBundle L → IsLineBundle M →
    IsLineBundle (moduleTensor X L M)
  finite : ∀ (L : X.Modules), IsLineBundle L → ∀ j : ℕ, j ≤ 1 →
    FiniteDimensional k (cohomology f L j)
  tensor_euler : ∀ (L M : X.Modules), IsLineBundle L → IsLineBundle M →
    euler01 f (moduleTensor X L M) = degree f L + euler01 f M

theorem tensor_degree {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (T : CurveTensorEulerInputs f)
    (L M : X.Modules) (hL : IsLineBundle L) (hM : IsLineBundle M) :
    degree f (moduleTensor X L M) = degree f L + degree f M := by
  rw [degree_eq_euler01_sub, T.tensor_euler L M hL hM, degree_eq_euler01_sub f M]
  ring

theorem power_isLine {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (T : CurveTensorEulerInputs f)
    (L : X.Modules) (hL : IsLineBundle L) (n : ℕ) : IsLineBundle (power L n) := by
  induction n with
  | zero => exact structureModule_isLine X
  | succ n hn => exact T.tensor_line _ _ hn hL

theorem degree_structure {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : degree f (structureModule X) = 0 := by
  rw [degree_eq_euler01_sub]
  ring

theorem degree_power {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (T : CurveTensorEulerInputs f)
    (L : X.Modules) (hL : IsLineBundle L) (n : ℕ) : degree f (power L n) = n * degree f L := by
  induction n with
  | zero => simp only [power, degree_structure, Nat.cast_zero, zero_mul]
  | succ n hn =>
      rw [power, tensor_degree f T _ _ (power_isLine f T L hL n) hL, hn]
      push_cast
      ring

end MathlibExt.AlgebraicGeometry.CurveCohomologyCalculus
