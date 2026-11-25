/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.DGModelContracts
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Actual DG modules and quasi-representable bimodule models

Right modules are the source DG functors to actual coefficient cochains.
The native formal localization inverts their component quasi-isomorphisms.
Bimodules are the curried C to right-D-module DG functors, hence have
variance `C × Dᵒᵖ → Ch(k)`. Toën's `C-Mod` denotes covariant modules
(§3, p.12); his right quasi-representable `(C ⊗ Dᵒᵖ)-Mod` therefore has
columns `Dᵒᵖ → Ch(k)` represented by `D(-, y)` (Definition 4.1, p.17).
Our separately named `RightModule C` is conventional contravariant
`Cᵒᵖ → Ch(k)`, so it is Toën's `Cᵒᵖ-Mod`.

Point evaluation is normalized in every cochain degree. Its construction
can be supplied as a shared provider, but no internal-Hom equivalence or
moduli geometricity is assumed. References: Toën arXiv:math/0408337v7,
Definitions 4.1 and Theorem 6.1; Brav--Dyckerhoff arXiv:1606.00619v1,
§2.1. Completed DG/Yoneda bodies retain their source attribution in
MathlibExt.CategoryTheory.DGSource.
-/

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.DGQuasiFunctorModels

open _root_.CategoryTheory MonoidalCategory Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open CochainComplex CochainComplex.HomComplex

universe u

variable (k : Type u) [CommRing k]

/-- Actual right DG modules (DG presheaves), including their full DG action. On the one-object
category of a DG algebra `A`, where `a ≫ b = a * b`, these are left `A`-modules; use the opposite DG
algebra (with the Koszul sign) for conventional right `A`-modules. -/
abbrev RightModule (C : Type u) [DGCategory k C] :=
  DGFunctor k Cᵒᵖ (Cochains k)

variable {k}

/-- The native closed degree-zero cochain map represented by a map out
of the tensor unit. -/
def cochainFromUnit {F G : Cochains k}
    (a : 𝟙_ (Cochains k) ⟶ dgHomComplex k F G) : F ⟶ G := by
  let h := ForgetEnrichment.homOf (Cochains k) a
  let z : Cochain F G 0 := dgClosedHom (C := Cochains k) k h
  apply Cocycle.homOf
  refine ⟨z, ?_⟩
  change δ 0 1 z = 0
  have hz := dgClosedHom_mem_dgCycles (C := Cochains k) k h
  simpa only [z, mem_dgCycles, dgDifferential_linearHomComplex, zero_add] using! hz

/-- Point evaluation fixes the actual cochain object and every map. It
does not choose an arbitrary module realization. -/
structure ModuleEvaluation (C : Type u) [DGCategory k C] (x : Cᵒᵖ) where
  functor : RightModule k C ⥤ Cochains k
  objectIso : ∀ M : RightModule k C,
    functor.obj M ≅ M.toEnrichedFunctor.obj x
  map_eq : ∀ {M N : RightModule k C} (f : M ⟶ N),
    functor.map f ≫ (objectIso N).hom =
      (objectIso M).hom ≫ cochainFromUnit (f.app x)

/-- The actual closed cochain map at a module component. -/
def moduleComponent {C : Type u} [DGCategory k C]
    {M N : RightModule k C} (f : M ⟶ N) (x : Cᵒᵖ) :
    M.toEnrichedFunctor.obj x ⟶ N.toEnrichedFunctor.obj x := by
  apply Cocycle.homOf
  apply Cocycle.mk (f.dgApp x) 1 (by omega)
  have h := f.dgApp_mem_dgCycles x
  simpa only [mem_dgCycles, dgDifferential_linearHomComplex, zero_add] using! h

/-- Component evaluation preserves the native identity and composition,
using the already-proved DG natural-transformation component formulas. -/
def moduleEvaluationFunctor {C : Type u} [DGCategory k C] (x : Cᵒᵖ) :
    RightModule k C ⥤ Cochains k where
  obj M := M.toEnrichedFunctor.obj x
  map f := moduleComponent f x
  map_id M := by
    ext1 n
    change ((DGNatTrans.id M.toEnrichedFunctor).dgApp x : Cochain _ _ 0).v n n _ = _
    rw [DGNatTrans.dgApp_id, dgId_linearHomComplex]
    rfl
  map_comp f g := by
    ext1 n
    change ((DGNatTrans.comp f g).dgApp x : Cochain _ _ 0).v n n _ =
      (f.dgApp x : Cochain _ _ 0).v n n _ ≫ (g.dgApp x : Cochain _ _ 0).v n n _
    rw [DGNatTrans.dgApp_comp, dgCompZero_def, dgComp_linearHomComplex]
    simp only [mul_zero, Int.negOnePow_zero, one_smul]
    exact Cochain.comp_v _ _ _ n n n _ _

/-- The completed native point-evaluation provider. -/
def canonicalEvaluation {C : Type u} [DGCategory k C] (x : Cᵒᵖ) :
    ModuleEvaluation (k := k) C x where
  functor := moduleEvaluationFunctor x
  objectIso M := Iso.refl _
  map_eq f := by
    ext1 n
    change (f.dgApp x : Cochain _ _ 0).v n n _ =
      (dgClosedHom (C := Cochains k) k (ForgetEnrichment.homOf _ (f.app x)) :
        Cochain _ _ 0).v n n _
    rw [f.dgApp_eq_dgClosedHom]

/-- Componentwise DG-module quasi-isomorphisms on the fixed evaluation
models. -/
def moduleWeakEquivalences {C : Type u} [DGCategory k C]
    (E : ∀ x : Cᵒᵖ, ModuleEvaluation (k := k) C x) : MorphismProperty (RightModule k C) :=
  fun _ _ f => ∀ x : Cᵒᵖ, QuasiIso ((E x).functor.map f)

/-- The actual right-module derived localization. It is not the derived
category of the abelian category of DG modules a second time. -/
abbrev ModuleDerived {C : Type u} [DGCategory k C]
    (E : ∀ x : Cᵒᵖ, ModuleEvaluation (k := k) C x) :=
  (moduleWeakEquivalences E).Localization

/-- The native localization functor for DG modules. -/
abbrev moduleQ {C : Type u} [DGCategory k C]
    (E : ∀ x : Cᵒᵖ, ModuleEvaluation (k := k) C x) :=
  (moduleWeakEquivalences E).Q

/-- Toën's curried `(C ⊗ Dᵒᵖ)-Mod`: covariant in C and contravariant
in D. The module morphism direction is retained. -/
abbrev Bimodule (k : Type u) [CommRing k] (C D : Type u)
    [DGCategory k C] [DGCategory k D] :=
  DGFunctor k C (RightModule k D)

/-- The graph module of a strict DG functor is the actual functor
followed by Yoneda(D), with columns `D(-, f(x))`. -/
def graph {C D : Type u} [DGCategory k C] [DGCategory k D]
    (f : EnrichedFunctor (Cochains k) C D) : Bimodule k C D :=
  ⟨f.comp (Cochains k) (dgYoneda k (C := D))⟩

/-- Right quasi-representability is literal isomorphism to the Yoneda
column in the actual localization of right modules. -/
def IsRightQuasiRepresentable {C D : Type u} [DGCategory k C] [DGCategory k D]
    (E : ∀ y : Dᵒᵖ, ModuleEvaluation (k := k) D y) (M : Bimodule k C D) : Prop :=
  ∀ x : C, ∃ y : D,
    Nonempty ((moduleQ E).obj (M.toEnrichedFunctor.obj x) ≅
      (moduleQ E).obj ((dgYoneda k (C := D)).obj y))

/-- A graph column is representable with the source-selected image,
independently of any Morita theorem. -/
theorem graph_isRightQuasiRepresentable {C D : Type u}
    [DGCategory k C] [DGCategory k D]
    (E : ∀ y : Dᵒᵖ, ModuleEvaluation (k := k) D y)
    (f : EnrichedFunctor (Cochains k) C D) :
    IsRightQuasiRepresentable E (graph f) := by
  intro x
  refine ⟨f.obj x, ?_⟩
  exact ⟨Iso.refl _⟩

/-- The standard projective DG-module trivial fibrations are the actual
component quasi-isomorphisms which are surjective in every degree. -/
def IsModuleTrivialFibration {C : Type u} [DGCategory k C]
    {M N : RightModule k C} (f : M ⟶ N) : Prop :=
  ∀ x : Cᵒᵖ, QuasiIso (moduleComponent f x) ∧
    ∀ n : ℤ, Function.Surjective ((moduleComponent f x).f n)

/-- The initial-object lifting property in the actual right-module
category. This retains module action and closed naturality. -/
def IsCofibrantModule {C : Type u} [DGCategory k C] (M : RightModule k C) : Prop :=
  ∀ (N P : RightModule k C) (p : N ⟶ P), IsModuleTrivialFibration p →
    ∀ f : M ⟶ P, ∃ g : M ⟶ N, g ≫ p = f

/-- A surjective quasi-isomorphism of cochain complexes of modules lifts degree-zero cocycles:
it suffices that it is a quasi-isomorphism in degree zero and surjective in degree `-1`. Lift the
class of `c` to a cocycle `z`; then `c - φ z = d w`, and lifting `w` to `u` corrects `z` to the
cocycle `z + d u` over `c`. -/
theorem exists_cocycle_lift_of_quasiIsoAt_zero {N P : Cochains k} (φ : N ⟶ P)
    [QuasiIsoAt φ 0] (hsurj : Function.Surjective (φ.f (-1))) (c : P.X 0)
    (hc : P.d 0 1 c = 0) :
    ∃ c' : N.X 0, N.d 0 1 c' = 0 ∧ φ.f 0 c' = c := by
  have hq : ShortComplex.QuasiIso
      ((HomologicalComplex.shortComplexFunctor' _ _ (-1) 0 1).map φ) :=
    (quasiIsoAt_iff' φ (-1) 0 1 (by simp) (by simp)).1 inferInstance
  set S := N.sc' (-1) 0 1 with hS
  set S' := P.sc' (-1) 0 1 with hS'
  set ψ := (HomologicalComplex.shortComplexFunctor' _ _ (-1) 0 1).map φ with hψ
  have hc' : c ∈ LinearMap.ker S'.g.hom := hc
  let x' : S'.cycles := S'.moduleCatCyclesIso.inv ⟨c, hc'⟩
  have hx' : S'.iCycles x' = c := by
    change (S'.moduleCatCyclesIso.inv ≫ S'.iCycles) ⟨c, hc'⟩ = c
    rw [S'.moduleCatCyclesIso_inv_iCycles]
    rfl
  obtain ⟨h, hh⟩ : ∃ h, ShortComplex.homologyMap ψ h = S'.homologyπ x' :=
    (ConcreteCategory.bijective_of_isIso (ShortComplex.homologyMap ψ)).2 _
  obtain ⟨z, rfl⟩ : ∃ z, S.homologyπ z = h :=
    (ModuleCat.epi_iff_surjective S.homologyπ).1 inferInstance h
  have key : S'.homologyπ (ShortComplex.cyclesMap ψ z) = S'.homologyπ x' := by
    rw [← hh, ← ConcreteCategory.comp_apply, ← ShortComplex.homologyπ_naturality,
      ConcreteCategory.comp_apply]
  have e : ∀ a, S'.moduleCatHomologyIso.hom (S'.homologyπ a) =
      S'.moduleCatLeftHomologyData.π (S'.moduleCatCyclesIso.hom a) := fun a => by
    rw [← ConcreteCategory.comp_apply, S'.π_moduleCatCyclesIso_hom, ConcreteCategory.comp_apply]
  have key2 := congrArg S'.moduleCatHomologyIso.hom key
  rw [e, e] at key2
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _ at key2
  obtain ⟨w, hw⟩ := (Submodule.Quotient.eq _).1 key2
  have hval : ∀ y, S'.moduleCatLeftHomologyData.i (S'.moduleCatCyclesIso.hom y) =
      S'.iCycles y := fun y => by
    rw [← S'.moduleCatCyclesIso_hom_i, ConcreteCategory.comp_apply]
  have hw' : S'.f w = S'.iCycles (ShortComplex.cyclesMap ψ z) - S'.iCycles x' := by
    rw [← hval, ← hval, ← map_sub, ← hw]
    rfl
  rw [hx', ← ConcreteCategory.comp_apply, ShortComplex.cyclesMap_i,
    ConcreteCategory.comp_apply] at hw'
  obtain ⟨u, rfl⟩ := hsurj w
  let z₀ : N.X 0 := S.iCycles z
  have hz₀ : N.d 0 1 z₀ = 0 := by
    change (S.iCycles ≫ S.g) z = 0
    rw [S.iCycles_g]
    rfl
  refine ⟨z₀ - N.d (-1) 0 u, ?_, ?_⟩
  · have h2 : N.d 0 1 (N.d (-1) 0 u) = 0 := by
      rw [← ConcreteCategory.comp_apply, N.d_comp_d]
      rfl
    rw [map_sub, hz₀, h2, sub_zero]
  · have h3 : φ.f 0 (N.d (-1) 0 u) = P.d (-1) 0 (φ.f (-1) u) := by
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, φ.comm]
    change P.d (-1) 0 (φ.f (-1) u) = φ.f 0 z₀ - c at hw'
    rw [map_sub, h3, hw']
    abel

/-- Component evaluation sends composites of module morphisms to composites. -/
theorem moduleComponent_comp {C : Type u} [DGCategory k C] {M N P : RightModule k C}
    (f : M ⟶ N) (g : N ⟶ P) (x : Cᵒᵖ) :
    moduleComponent (f ≫ g) x = moduleComponent f x ≫ moduleComponent g x :=
  (moduleEvaluationFunctor x).map_comp f g

/-- Under the DG Yoneda bijection, composing a morphism out of the representable module
`Hom(-, X)` with `β` applies the component of `β` at `X` to the corresponding cocycle. -/
theorem dgYonedaEquiv_comp_coe {C : Type u} [DGCategory k C] (X : C) {F G : RightModule k C}
    (α : (⟨dgRepresentable k X⟩ : RightModule k C) ⟶ F) (β : F ⟶ G) :
    ((dgYonedaEquiv X G.toEnrichedFunctor (α ≫ β)) : (G.toEnrichedFunctor.obj (op X)).X 0) =
      (moduleComponent β (op X)).f 0 (dgYonedaEquiv X F.toEnrichedFunctor α) := by
  rw [dgYonedaEquiv_apply_coe, dgYonedaEquiv_apply_coe]
  change (moduleComponent (α ≫ β) (op X)).f 0 (dgId k X) =
    (moduleComponent β (op X)).f 0 ((moduleComponent α (op X)).f 0 (dgId k X))
  rw [moduleComponent_comp]
  rfl

/-- **Representable right DG modules are cofibrant.** By the DG Yoneda lemma a morphism
`Hom(-, X) ⟶ P` is a degree-zero cocycle of `P(X)`; a trivial fibration `N ⟶ P` is a surjective
quasi-isomorphism at `X`, so the cocycle lifts to a cocycle of `N(X)`
(`exists_cocycle_lift_of_quasiIsoAt_zero`), which is the required lift. -/
theorem isCofibrantModule_dgRepresentable {C : Type u} [DGCategory k C] (X : C) :
    IsCofibrantModule (⟨dgRepresentable k X⟩ : RightModule k C) := by
  intro N P p hp f
  obtain ⟨hq, hs⟩ := hp (op X)
  obtain ⟨c', hc', hlift⟩ := exists_cocycle_lift_of_quasiIsoAt_zero (moduleComponent p (op X))
    (hs (-1)) (dgYonedaEquiv X P.toEnrichedFunctor f)
    (LinearMap.mem_ker.1 (dgYonedaEquiv X P.toEnrichedFunctor f).2)
  refine ⟨(dgYonedaEquiv X N.toEnrichedFunctor).symm ⟨c', LinearMap.mem_ker.2 hc'⟩, ?_⟩
  apply (dgYonedaEquiv X P.toEnrichedFunctor).injective
  apply Subtype.ext
  rw [dgYonedaEquiv_comp_coe, Equiv.apply_symm_apply]
  exact hlift

/-- The actual DG category of cofibrant right modules, with its source
Hom complexes. Passing to H0 before this construction would lose the
derived mapping data. For a small pretriangulated idempotent-complete C,
its comparison with stable Ind(C) is a separate theorem, not assumed
here. -/
abbrev DGDerivedModules (k : Type u) [CommRing k] (C : Type u) [DGCategory k C] :=
  DGFullSubcategory (fun M : RightModule k C => IsCofibrantModule M)

/-- A source-normalized module replacement has an actual augmentation,
not a freely supplied object called a derived module. -/
structure ModuleReplacement {C : Type u} [DGCategory k C] (M : RightModule k C) where
  module : RightModule k C
  augmentation : module ⟶ M
  cofibrant : IsCofibrantModule module
  trivialFibration : IsModuleTrivialFibration augmentation

end MathlibExt.CategoryTheory.DGQuasiFunctorModels
