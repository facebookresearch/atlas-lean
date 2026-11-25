/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @junekim623, Muse
-/

module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import MathlibExt.Algebra.Category.ModuleCat.Sheaf.OverLocalSurjective
public import MathlibExt.CategoryTheory.Sites.CoversTop

/-!
# Coherence for sheaves of modules — general ringed site

General-site coherence (Stacks 01BV):

A sheaf of modules `M` over `R : Sheaf J RingCat` is coherent if
- it is finite type
- for every `U : C` and every `n` and every map `φ : (O_U)^n ⟶ M|_U`, `ker φ` is finite type

The local quantification over every `U` is essential: a sheaf may have very few
global sections, so testing only `φ : O^n ⟶ M` on the whole space is strictly weaker
than Stacks 01BV and would not imply `IsFinitePresentation`.

Over a coherent base ring sheaf `R`, this is equivalent to `IsFinitePresentation`
(Stacks 01BZ, 01BY). The further equivalence `IsCoherent ↔ IsQuasicoherent ∧ IsFiniteType`
is **false** over a merely coherent ring: e.g. `R = k[x₁,x₂,…]` is coherent,
`M = R/(x₁,x₂,…)` is cyclic hence FT and QC but not FP, hence not coherent.
`QC ∧ FT ↔ Coherent` needs locally Noetherian (Stacks 01XZ): in this
repository it appears only as a comparison theorem under `[IsLocallyNoetherian X]`
at the scheme layer.

When `R` is a coherent ring sheaf, TFAE for `M`:
(i) locally finitely presented (IsFinitePresentation)
(ii) coherent (IsCoherent)
`QC ∧ FT` is a comparison theorem only under `[IsLocallyNoetherian]` (scheme layer).
-/

@[expose] public section

universe u v₁ w v₂

open _root_.CategoryTheory CategoryTheory Limits

variable {C : Type u} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X),
    HasWeakSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X),
    ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X) (Z : Over Y),
    HasWeakSheafify (((J.over X).over Y).over Z) AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X) (Z : Over Y),
    (((J.over X).over Y).over Z).WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace SheafOfModules

/-- Sheafification transports from an ordinary slice to the corresponding iterated slice. -/
private theorem hasSheafifyIteratedSlice
    {D : Type w} [Category.{v₂} D]
    (K : GrothendieckTopology D) (X : D) (Y : Over X)
    [HasSheafify (K.over Y.left) AddCommGrpCat.{u}] :
    HasSheafify ((K.over X).over Y) AddCommGrpCat.{u} := by
  let _ : (Y.iteratedSliceEquiv.inverse.sheafPushforwardContinuous AddCommGrpCat.{u}
      (K.over Y.left) ((K.over X).over Y)).IsEquivalence :=
    (Y.iteratedSliceEquiv.sheafCongr ((K.over X).over Y)
      (K.over Y.left) AddCommGrpCat.{u}).isEquivalence_functor
  exact Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
    (K.over Y.left) ((K.over X).over Y) (Over.iteratedSliceEquiv Y).inverse

/-- Compare free sheaves through a functor preserving the indexing coproduct,
using only weak sheafification on the target. -/
private noncomputable def weakMapFreeIso
    {D D' : Type w} [Category.{v₂} D] [Category.{v₂} D']
    {K : GrothendieckTopology D} {K' : GrothendieckTopology D'}
    {S : Sheaf K RingCat.{u}} {S' : Sheaf K' RingCat.{u}}
    [HasWeakSheafify K AddCommGrpCat.{u}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify K' AddCommGrpCat.{u}]
    [K'.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F : SheafOfModules.{u} S ⥤ SheafOfModules.{u} S') (I : Type u)
    [PreservesColimitsOfShape (Discrete I) F]
    (η : _root_.SheafOfModules.unit S' ≅ F.obj (_root_.SheafOfModules.unit S)) :
    _root_.SheafOfModules.free (R := S') I ≅ F.obj (_root_.SheafOfModules.free (R := S) I) :=
  (_root_.SheafOfModules.isColimitFreeCofan I).coconePointsIsoOfNatIso
    (isColimitOfPreserves F (_root_.SheafOfModules.isColimitFreeCofan I))
    (Discrete.natIso fun _ ↦ η)

@[reassoc]
private lemma ιFree_weakMapFreeIso_hom
    {D D' : Type w} [Category.{v₂} D] [Category.{v₂} D']
    {K : GrothendieckTopology D} {K' : GrothendieckTopology D'}
    {S : Sheaf K RingCat.{u}} {S' : Sheaf K' RingCat.{u}}
    [HasWeakSheafify K AddCommGrpCat.{u}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify K' AddCommGrpCat.{u}]
    [K'.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F : SheafOfModules.{u} S ⥤ SheafOfModules.{u} S') (I : Type u)
    [PreservesColimitsOfShape (Discrete I) F]
    (η : _root_.SheafOfModules.unit S' ≅ F.obj (_root_.SheafOfModules.unit S)) (i : I) :
    _root_.SheafOfModules.ιFree i ≫ (weakMapFreeIso F I
        η).hom = η.hom ≫ F.map (_root_.SheafOfModules.ιFree i) :=
  IsColimit.ι_map (_root_.SheafOfModules.isColimitFreeCofan I) (F.mapCocone
      (_root_.SheafOfModules.freeCofan I))
    (Discrete.natTrans fun _ ↦ η.hom) (Discrete.mk i)

private noncomputable def finiteFreeOverIso
    {D : Type w} [Category.{v₂} D] {K : GrothendieckTopology D}
    (S : Sheaf K RingCat.{u})
    [HasSheafify K AddCommGrpCat.{u}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (X : D) (n : ℕ)
    [HasWeakSheafify (K.over X) AddCommGrpCat.{u}]
    [(K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    _root_.SheafOfModules.free (R := S.over X) (ULift.{u} (Fin n)) ≅
      (_root_.SheafOfModules.overFunctor S X).obj (_root_.SheafOfModules.free (R :=
          S) (ULift.{u} (Fin n))) := by
  let I := ULift.{u} (Fin n)
  let F := _root_.SheafOfModules.overFunctor.{u} S X
  haveI hcomp : PreservesLimitsOfShape (Discrete I)
      (F ⋙ _root_.SheafOfModules.forget (S.over X)) := by
    constructor
    intro A
    constructor
    intro c hc
    refine ⟨PresheafOfModules.evaluationJointlyReflectsLimits
      (F := A ⋙ F ⋙ _root_.SheafOfModules.forget (S.over X))
      ((F ⋙ _root_.SheafOfModules.forget (S.over X)).mapCone c)
      (fun U => ?_)⟩
    change IsLimit ((_root_.SheafOfModules.forget S ⋙ PresheafOfModules.evaluation S.obj
      ((Over.forget X).op.obj U) ⋙
        ModuleCat.restrictScalars (RingHom.id _)).mapCone c)
    exact isLimitOfPreserves _ hc
  haveI hrefl : ReflectsLimitsOfShape (Discrete I) (_root_.SheafOfModules.forget (S.over X)) :=
    inferInstance
  haveI hlimits : PreservesLimitsOfShape (Discrete I) F :=
    preservesLimitsOfShape_of_reflects_of_preserves F (_root_.SheafOfModules.forget (S.over X))
  haveI hzero : F.PreservesZeroMorphisms := inferInstance
  haveI hbiproducts : PreservesBiproductsOfShape I F :=
    preservesBiproductsOfShape_of_preservesProductsOfShape F
  haveI hcolimits : PreservesColimitsOfShape (Discrete I) F :=
    preservesCoproductsOfShape_of_preservesBiproductsOfShape F
  exact (_root_.SheafOfModules.isColimitFreeCofan (R := S.over X) I).coconePointsIsoOfNatIso
    (isColimitOfPreserves F (_root_.SheafOfModules.isColimitFreeCofan (R := S) I))
    (Discrete.natIso fun _ ↦ Iso.refl _)

private lemma ιFree_finiteFreeOverIso_hom
    {D : Type w} [Category.{v₂} D] {K : GrothendieckTopology D}
    (S : Sheaf K RingCat.{u})
    [HasSheafify K AddCommGrpCat.{u}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (X : D) (n : ℕ)
    [HasWeakSheafify (K.over X) AddCommGrpCat.{u}]
    [(K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (i : ULift.{u} (Fin n)) :
    _root_.SheafOfModules.ιFree (R := S.over X) i ≫ (finiteFreeOverIso S X n).hom =
      (_root_.SheafOfModules.overFunctor S X).map (_root_.SheafOfModules.ιFree (R := S) i) := by
  change _root_.SheafOfModules.ιFree (R := S.over X) i ≫
      (_root_.SheafOfModules.isColimitFreeCofan (R := S.over X) (ULift.{u} (Fin n))).map
        ((_root_.SheafOfModules.overFunctor S X).mapCocone
          (_root_.SheafOfModules.freeCofan (R := S) (ULift.{u} (Fin n))))
        (Discrete.natIso (fun _ ↦ Iso.refl (_root_.SheafOfModules.unit (S.over X)))).hom = _
  rw [← _root_.SheafOfModules.freeCofan_inj]
  exact IsColimit.ι_map
    (_root_.SheafOfModules.isColimitFreeCofan (R := S.over X) (ULift.{u} (Fin n)))
    ((_root_.SheafOfModules.overFunctor S X).mapCocone
      (_root_.SheafOfModules.freeCofan (R := S) (ULift.{u} (Fin n))))
    (Discrete.natTrans (fun _ ↦ (Iso.refl (_root_.SheafOfModules.unit (S.over X))).hom))
    (Discrete.mk i)

/-- An equivalence transports generating sections under weak sheafification.
Unlike `GeneratingSections.map`, this needs no strong sheafification instance
on the target: the free comparison is built directly from its coproduct
universal property. -/
private noncomputable def _root_.SheafOfModules.GeneratingSections.mapEquivalenceWeak
    {D D' : Type w} [Category.{v₂} D] [Category.{v₂} D']
    {K : GrothendieckTopology D} {K' : GrothendieckTopology D'}
    {S : Sheaf K RingCat.{u}} {S' : Sheaf K' RingCat.{u}}
    [HasWeakSheafify K AddCommGrpCat.{u}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify K' AddCommGrpCat.{u}]
    [K'.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} S} (G : M.GeneratingSections)
    (E : SheafOfModules.{u} S ≌ SheafOfModules.{u} S')
    (η : _root_.SheafOfModules.unit S' ≅ E.functor.obj (_root_.SheafOfModules.unit S)) :
    (E.functor.obj M).GeneratingSections where
  I := G.I
  s := (E.functor.obj M).freeHomEquiv
    ((weakMapFreeIso E.functor G.I η).hom ≫ E.functor.map G.π)
  epi := by
    rw [Equiv.symm_apply_apply]
    infer_instance

private instance _root_.SheafOfModules.GeneratingSections.mapEquivalenceWeak_isFiniteType
    {D D' : Type w} [Category.{v₂} D] [Category.{v₂} D']
    {K : GrothendieckTopology D} {K' : GrothendieckTopology D'}
    {S : Sheaf K RingCat.{u}} {S' : Sheaf K' RingCat.{u}}
    [HasWeakSheafify K AddCommGrpCat.{u}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify K' AddCommGrpCat.{u}]
    [K'.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} S} (G : M.GeneratingSections)
    (E : SheafOfModules.{u} S ≌ SheafOfModules.{u} S')
    (η : _root_.SheafOfModules.unit S' ≅ E.functor.obj (_root_.SheafOfModules.unit
        S)) [G.IsFiniteType] :
    (G.mapEquivalenceWeak E η).IsFiniteType where
  finite := inferInstanceAs (Finite G.I)

/-- A quotient of a finite-type sheaf is finite type, with no binary-product
hypothesis (using `epi_over_of_epi`). The statement quantifies an
independent site universe so it applies after passing to a slice category. -/
theorem isFiniteType_of_epi' {D : Type w} [Category.{v₂} D]
    {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
    [HasSheafify K AddCommGrpCat.{u}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ (X : D), HasWeakSheafify (K.over X) AddCommGrpCat.{u}]
    [∀ (X : D), (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} S}
    (f : M ⟶ N) [Epi f] [_root_.SheafOfModules.IsFiniteType (R := S) M] :
    _root_.SheafOfModules.IsFiniteType (R := S) N := by
  obtain ⟨σ, hσ⟩ := _root_.SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  refine ⟨⟨σ.I, σ.X, σ.coversTop, fun i => ?_⟩, ⟨fun i => ?_⟩⟩
  · haveI := epi_over_of_epi f (σ.X i)
    exact (σ.generators i).ofEpi ((_root_.SheafOfModules.overFunctor S (σ.X i)).map f)
  · have := epi_over_of_epi f (σ.X i)
    have := hσ.isFiniteType i
    infer_instance

/-- Restriction to a slice preserves the specified cokernel. -/
private theorem preservesCokernel_overFunctor
    {D : Type w} [Category.{v₂} D]
    {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
    [HasSheafify K AddCommGrpCat.{u}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X : D, HasSheafify (K.over X) AddCommGrpCat.{u}]
    [∀ X : D, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} S} (φ : M ⟶ N) (X : D) :
    PreservesColimit (parallelPair φ 0) (_root_.SheafOfModules.overFunctor S X) := by
  apply preservesColimit_of_preserves_colimit_cocone
    (Limits.cokernelIsCokernel φ)
  apply (CokernelCofork.isColimitMapCoconeEquiv _ (_root_.SheafOfModules.overFunctor S X)).2
  exact mapCokernelPiOverIsColimit φ X

/-- A sheaf of rings `R` is coherent if for every `X : C` the kernel of every
map `free (Fin n) ⟶ unit` over `R.over X` is finite type. This is the local
version of the condition `O^n → O`. -/
class IsCoherentRing (R : Sheaf J RingCat.{u}) : Prop where
  kernel_finiteType : ∀ (X : C) {n : ℕ}
    (φ : _root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin n)) ⟶
      (_root_.SheafOfModules.unit (R := R.over X) : SheafOfModules.{u} (R.over X))),
    _root_.SheafOfModules.IsFiniteType (R := R.over X) (Limits.kernel φ)

/-- A sheaf of modules `M` over `R` is coherent if it is finite type and
for every `X : C` the kernel of every map `free (Fin n) ⟶ M.over X` over
`R.over X` is finite type. This quantifies over every restriction `M|_U`
as in Stacks 01BV; testing only global `O^n → M` would be strictly
weaker. -/
class IsCoherent (M : SheafOfModules.{u} R) : Prop where
  finiteType : _root_.SheafOfModules.IsFiniteType (R := R) M
  kernel_finiteType : ∀ (X : C) {n : ℕ}
    (φ : _root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin n)) ⟶ M.over X),
    _root_.SheafOfModules.IsFiniteType (R := R.over X) (Limits.kernel φ)

/-- `IsCoherent` as an `ObjectProperty`, mirroring `isQuasicoherent`. -/
abbrev isCoherent : ObjectProperty (SheafOfModules.{u} R) :=
  IsCoherent

instance {F : (isCoherent (R := R)).FullSubcategory} :
    IsCoherent (R := R) F.obj :=
  F.property

omit [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X),
    HasWeakSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X),
    ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X) (Z : Over Y),
    HasWeakSheafify (((J.over X).over Y).over Z) AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X) (Z : Over Y),
    (((J.over X).over Y).over Z).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Finite generating sections yield an epi from a finite free module. -/
private theorem epiFreeFin_of_finiteGenerators {X : C}
    {N : SheafOfModules.{u} (R.over X)} (G : N.GeneratingSections) [G.IsFiniteType] :
    ∃ (n : ℕ) (π : _root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin n)) ⟶ N), Epi π := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (α := G.I)
  let e' : G.I ≃ ULift.{u} (Fin n) := e.trans Equiv.ulift.symm
  have h2 : Epi (((_root_.SheafOfModules.freeFunctor (R := R.over X)).mapIso e'.toIso.symm).hom) :=
    inferInstance
  have hE : Epi ((((_root_.SheafOfModules.freeFunctor (R := R.over X)).mapIso e'.toIso.symm).hom ≫
      G.π :
      _root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin n)) ⟶ N)) :=
    @epi_comp _ _ _ _ _ _ h2 _ G.epi
  exact ⟨n, _, hE⟩

private theorem epiFreeFin_of_finiteGenerators_slice
    {D : Type w} [Category.{v₂} D]
    {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}} {Y : D}
    [HasWeakSheafify (K.over Y) AddCommGrpCat.{u}]
    [(K.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {A : SheafOfModules.{u} (S.over Y)}
    (G : A.GeneratingSections) [G.IsFiniteType] :
    ∃ (n : ℕ) (π : _root_.SheafOfModules.free (R := S.over Y) (ULift.{u} (Fin n)) ⟶ A), Epi π := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (α := G.I)
  let e' : G.I ≃ ULift.{u} (Fin n) := e.trans Equiv.ulift.symm
  have h2 : Epi (((_root_.SheafOfModules.freeFunctor (R := S.over Y)).mapIso e'.toIso.symm).hom) :=
    inferInstance
  have hE : Epi ((((_root_.SheafOfModules.freeFunctor (R := S.over Y)).mapIso e'.toIso.symm).hom ≫
      G.π :
      _root_.SheafOfModules.free (R := S.over Y) (ULift.{u} (Fin n)) ⟶ A)) :=
    @epi_comp _ _ _ _ _ _ h2 _ G.epi
  exact ⟨n, _, hE⟩

omit [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X) (Z : Over Y),
    HasWeakSheafify (((J.over X).over Y).over Z) AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X) (Z : Over Y),
    (((J.over X).over Y).over Z).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A module with an epi from a finite free whose kernel is finite type is
finitely presented: restrict the presentation to a finite-type cover of the kernel. -/
private theorem isFinitePresentation_of_epi_kernel_finiteType {X : C}
    {N : SheafOfModules.{u} (R.over X)}
    {n : ℕ} (π : _root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin n)) ⟶ N) [Epi π]
    [_root_.SheafOfModules.IsFiniteType (R := R.over X) (Limits.kernel π)] :
    _root_.SheafOfModules.IsFinitePresentation (R := R.over X) N := by
  classical
  obtain ⟨τ, hτ⟩ := _root_.SheafOfModules.IsFiniteType.exists_localGeneratorsData (Limits.kernel π)
  have hπls : Presheaf.IsLocallySurjective (J.over X)
      ((PresheafOfModules.toPresheaf (R.over X).obj).map π.val) :=
    locallySurjective_of_epi π
  let pres : ∀ j, { p : (N.over (τ.X j)).Presentation // p.IsFinite } := fun j => by
    haveI hjfin : (τ.generators j).IsFiniteType := hτ.isFiniteType j
    let F := _root_.SheafOfModules.overFunctor (R.over X) (τ.X j)
    have hπj := locallySurjective_over π hπls (τ.X j)
    haveI hπjE : Epi (F.map π) := epi_of_locallySurjective _ hπj
    letI : F.Additive := inferInstance
    letI : PreservesColimitsOfShape (Discrete (ULift.{u} (Fin n))) F := inferInstance
    let eG : _root_.SheafOfModules.free (R := (R.over X).over (τ.X j)) (ULift.{u} (Fin n)) ≅
        F.obj (_root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin n))) :=
      weakMapFreeIso F _ (Iso.refl _)
    let g : _root_.SheafOfModules.free (R := (R.over X).over (τ.X j)) (ULift.{u} (Fin n)) ⟶
        F.obj N := eG.hom ≫ F.map π
    haveI hg : Epi g := by dsimp [g]; infer_instance
    let ek : F.obj (Limits.kernel π) ≅ Limits.kernel (F.map π) :=
      PreservesKernel.iso (_root_.SheafOfModules.overFunctor (R.over X) (τ.X j)) π
    let ek' : Limits.kernel g ≅ Limits.kernel (F.map π) :=
      Limits.kernel.mapIso (f := g) (F.map π) eG (Iso.refl _)
        (by dsimp [g]; simp)
    let rel : (Limits.kernel g).GeneratingSections :=
      (τ.generators j).ofEpi (ek.hom ≫ ek'.inv)
    let gen : (F.obj N).GeneratingSections :=
      { I := ULift.{u} (Fin n)
        s := (F.obj N).freeHomEquiv g
        epi := by
          rw [Equiv.symm_apply_apply]
          exact hg }
    have hgen : gen.π = g := (F.obj N).freeHomEquiv.symm_apply_apply g
    let eRel : Limits.kernel g ≅ Limits.kernel gen.π :=
      eqToIso (congrArg (fun f ↦ Limits.kernel f) hgen.symm)
    let rel' : (Limits.kernel gen.π).GeneratingSections := rel.ofEpi eRel.hom
    let P : (F.obj N).Presentation := { generators := gen, relations := rel' }
    have hP : P.IsFinite := by
      constructor
      · change gen.IsFiniteType
        refine ⟨?_⟩
        change Finite (ULift.{u} (Fin n))
        exact inferInstance
      · change rel'.IsFiniteType
        exact ⟨hjfin.finite⟩
    exact ⟨P, hP⟩
  exact ⟨⟨τ.I, τ.X, τ.coversTop, fun j => (pres j).1⟩,
    ⟨fun j => (pres j).2⟩⟩


instance isFinitePresentation_of_isCoherent {M : SheafOfModules.{u} R}
    [IsCoherent (R := R) M] : _root_.SheafOfModules.IsFinitePresentation (R := R) M := by
  classical
  let : ∀ (X : C) (Y : Over X),
      HasSheafify ((J.over X).over Y) AddCommGrpCat.{u} :=
    fun X Y ↦ hasSheafifyIteratedSlice J X Y
  have : _root_.SheafOfModules.IsFiniteType (R := R) M := IsCoherent.finiteType
  obtain ⟨σ, hσ⟩ := _root_.SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  have hEpi : ∀ i, ∃ (n : ℕ)
      (π : _root_.SheafOfModules.free (R := R.over (σ.X i)) (ULift.{u} (Fin n)) ⟶ M.over (σ.X i)),
      Epi π := fun i => by
    have := hσ.isFiniteType i
    exact epiFreeFin_of_finiteGenerators (σ.generators i)
  choose n π hπ using hEpi
  have hFP : ∀ i, _root_.SheafOfModules.IsFinitePresentation (R :=
      R.over (σ.X i)) (M.over (σ.X i)) := by
    intro i
    have := hπ i
    have : _root_.SheafOfModules.IsFiniteType (R := R.over (σ.X i)) (Limits.kernel (π i)) :=
      IsCoherent.kernel_finiteType (σ.X i) (π i)
    exact isFinitePresentation_of_epi_kernel_finiteType (π i)
  choose D hD using fun i =>
    _root_.SheafOfModules.IsFinitePresentation.exists_quasicoherentData (M.over (σ.X i))
  let e : ∀ (i : σ.I) (j : (D i).I),
      SheafOfModules.{u} (R.over (((D i).X j).left)) ≌
        SheafOfModules.{u} ((R.over (σ.X i)).over ((D i).X j)) := fun i j =>
    _root_.SheafOfModules.overOverEquivalence (S := R) ((D i).X j)
  have hη : ∀ (i : σ.I) (j : (D i).I),
      _root_.SheafOfModules.unit (R.over (((D i).X j).left)) ≅
        (e i j).inverse.obj (_root_.SheafOfModules.unit ((R.over (σ.X i)).over ((D i).X j))) :=
    fun i j => Iso.refl _
  let data : M.QuasicoherentData :=
    ⟨(i : σ.I) × (D i).I, fun p => (((D p.1).X p.2).left),
      σ.coversTop.over (fun i => (D i).coversTop), fun ⟨i, j⟩ =>
      (((D i).presentation j).map (e i j).inverse (hη i j)).ofIsIso
        ((e i j).fullyFaithfulFunctor.preimageIso
        (by exact (e i j).counitIso.app ((M.over (σ.X i)).over ((D i).X j)))).hom⟩
  have hfin : ∀ p, (data.presentation p).IsFinite := by
    intro ⟨i, j⟩
    have hPi : ((D i).presentation j).IsFinite := (hD i).isFinite_presentation j
    refine { isFiniteType_generators := ⟨?_⟩, isFiniteType_relations := ⟨?_⟩ }
    · exact hPi.isFiniteType_generators.finite
    · exact hPi.isFiniteType_relations.finite
  let data' := data.shrink
  refine ⟨data', ⟨fun p => ?_⟩⟩
  exact hfin p.2.choose

-- When the base ring sheaf `R` is coherent, `𝒪 = unit R` is coherent.
-- This is the general bridge; together with `isCoherentRing_of_isLocallyNoetherian`
-- it gives `infer_instance` for `IsCoherent (unit X.ringCatSheaf)` when `[IsLocallyNoetherian X]`.
instance isCoherent_unit_of_isCoherentRing [IsCoherentRing (R := R)] :
    IsCoherent (R := R) (_root_.SheafOfModules.unit (R := R) : SheafOfModules.{u} R) := by
  classical
  -- Epi family from a rank-one finite free onto each restriction of `unit`.
  let e : ∀ (x : C), _root_.SheafOfModules.free (R := R.over x) (ULift.{u} (Fin 1)) ⟶
      (_root_.SheafOfModules.unit (R := R)).over x :=
    fun x => Sigma.desc (fun _ => 𝟙 _)
  have he : ∀ (x : C), Epi (e x) := by
    intro x
    have hret : _root_.SheafOfModules.ιFree (R := R.over x) (ULift.up (0 : Fin 1)) ≫ e x = 𝟙 _ :=
      Sigma.ι_comp_desc _ _
    have : IsSplitEpi (e x) := ⟨_, hret⟩
    infer_instance
  -- Canonical finite generators of each finite free, with `π = 𝟙`.
  let G₀ : ∀ (x : C),
      (_root_.SheafOfModules.free (R := R.over x) (ULift.{u} (Fin 1))).GeneratingSections :=
    fun x =>
      ⟨ULift.{u} (Fin 1), fun i => _root_.SheafOfModules.freeSection (R := R.over x) i, by
        have hπ : (_root_.SheafOfModules.freeHomEquiv
            (_root_.SheafOfModules.free (R := R.over x) (ULift.{u} (Fin 1)))).symm
            (fun i => _root_.SheafOfModules.freeSection (R := R.over x) i) = 𝟙 _ :=
          (_root_.SheafOfModules.freeHomEquiv _).symm_apply_apply _
        rw [hπ]
        infer_instance⟩
  have hG₀ : ∀ (x : C), (G₀ x).IsFiniteType :=
    fun x => ⟨inferInstance⟩
  constructor
  · -- `unit` is finite type: trivial cover `id : C → C`, one generator on each piece.
    refine ⟨⟨C, id, ?covers, fun x => (G₀ x).ofEpi (e x)⟩, ?fin⟩
    · intro X
      apply GrothendieckTopology.covering_of_eq_top
      rw [Sieve.ext_iff]
      intro _ f
      simp [Sieve.top_apply]
    · exact ⟨fun x => inferInstance⟩
  · -- Kernels into `(unit R).over X = unit (R.over X)` are finite type by hypothesis.
    intro X n φ
    exact IsCoherentRing.kernel_finiteType X φ

/-- The equivalence between sheaves on an iterated slice and on the direct slice. -/
private noncomputable abbrev kernelIteratedSliceEquivGeneral
    {D : Type w} [Category.{v₂} D]
    {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
    (X : D) (Y : Over X) :
    SheafOfModules.{u} (S.over Y.left) ≌
      SheafOfModules.{u} ((S.over X).over Y) :=
  _root_.SheafOfModules.overOverEquivalence (S := S) Y

/-- The iterated-slice equivalence for module sheaves over `R`. -/
private noncomputable abbrev kernelIteratedSliceEquiv (X : C) (Y : Over X) :
    SheafOfModules.{u} (R.over Y.left) ≌
      SheafOfModules.{u} ((R.over X).over Y) :=
  kernelIteratedSliceEquivGeneral (S := R) X Y

/-- Finite generating sections descend through an epimorphism after restriction
to an iterated slice. -/
private theorem kernelPieceGenerators
    {D : Type w} [Category.{v₂} D]
    {Ktop : GrothendieckTopology D} {S : Sheaf Ktop RingCat.{u}}
    [∀ Z : D, HasSheafify (Ktop.over Z) AddCommGrpCat.{u}]
    [∀ Z : D, HasWeakSheafify (Ktop.over Z) AddCommGrpCat.{u}]
    [∀ Z : D, (Ktop.over Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ (X' : D) (Y' : Over X'),
      HasWeakSheafify ((Ktop.over X').over Y') AddCommGrpCat.{u}]
    [∀ (X' : D) (Y' : Over X'),
      ((Ktop.over X').over Y').WEqualsLocallyBijective AddCommGrpCat.{u}]
    (K : SheafOfModules.{u} S)
    (X : D) (Y : Over X)
    (A : SheafOfModules.{u} (S.over X)) (α : A ⟶ K.over X) [Epi α]
    (G : (A.over Y).GeneratingSections) [G.IsFiniteType] :
    ∃ G' : ((K.over Y.left)).GeneratingSections, G'.IsFiniteType := by
  have hLSα : Presheaf.IsLocallySurjective ((Ktop.over X).over Y)
      ((PresheafOfModules.toPresheaf ((S.over X).over Y).obj).map
        (((_root_.SheafOfModules.overFunctor (S.over X) Y).map α)).val) :=
    locallySurjective_over α (locallySurjective_of_epi α) Y
  have hepiα : Epi ((_root_.SheafOfModules.overFunctor (S.over X) Y).map α) :=
    epi_of_locallySurjective _ hLSα
  -- The iterated-slice equivalence preserves colimits.


  have hEcol : PreservesColimitsOfSize.{u, u}
      (kernelIteratedSliceEquivGeneral (S := S) X Y).inverse := inferInstance
  have hpre : (kernelIteratedSliceEquivGeneral (S := S) X Y).functor.obj
        ((kernelIteratedSliceEquivGeneral (S := S) X Y).inverse.obj ((((K.over X).over Y)))) ≅
        (kernelIteratedSliceEquivGeneral (S := S) X Y).functor.obj (((K.over Y.left))) :=
    (kernelIteratedSliceEquivGeneral (S := S) X Y).counitIso.app _
  have hiso : (kernelIteratedSliceEquivGeneral (S := S) X Y).inverse.obj ((((K.over X).over Y))) ≅
        (((K.over Y.left))) :=
    (kernelIteratedSliceEquivGeneral (S := S) X Y).fullyFaithfulFunctor.preimageIso hpre
  -- Direct `finite` field proof: `ofEpi`/`mapEquivalenceWeak` preserve the
  -- index type definitionally (`I := σ.I`), so finiteness follows from `G`'s
  -- by `rfl` unfolding. Unlike `GeneratingSections.map`, the weak transport
  -- needs no strong sheafification on the iterated slice.
  exact ⟨(((G.ofEpi ((_root_.SheafOfModules.overFunctor (S.over X) Y).map α)).mapEquivalenceWeak
      (kernelIteratedSliceEquivGeneral (S := S) X Y).symm (Iso.refl _)).ofEpi hiso.hom),
    ⟨(inferInstance : G.IsFiniteType).finite⟩⟩

/-- Per-piece finite generators over a general slice, for nested covers.

This is the site-universe-independent copy of `kernelPieceGenerators` used in
`finiteType_kernel_to_coherent_over`, where the base is already a slice
(`D = Over X`) and `kernelIteratedSliceEquiv` (tied to `C`) does not apply.
The construction is identical, with an explicit generic
`pushforwardPushforwardEquivalence` for the iterated slice. -/
private theorem kernelPieceGeneratorsOver
    {D : Type w} [Category.{v₂} D]
    {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
    [∀ Z : D, HasSheafify (K.over Z) AddCommGrpCat.{u}]
    [∀ Z : D, HasWeakSheafify (K.over Z) AddCommGrpCat.{u}]
    [∀ Z : D, (K.over Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ (X' : D) (Y' : Over X'),
      HasWeakSheafify ((K.over X').over Y') AddCommGrpCat.{u}]
    [∀ (X' : D) (Y' : Over X'),
      ((K.over X').over Y').WEqualsLocallyBijective AddCommGrpCat.{u}]
    (Kmod : SheafOfModules.{u} S)
    (X : D) (Y : Over X)
    (A : SheafOfModules.{u} (S.over X)) (α : A ⟶ Kmod.over X) [Epi α]
    (G : (A.over Y).GeneratingSections) [G.IsFiniteType] :
    ∃ G' : ((Kmod.over Y.left)).GeneratingSections, G'.IsFiniteType := by
  have hLSα : Presheaf.IsLocallySurjective ((K.over X).over Y)
      ((PresheafOfModules.toPresheaf ((S.over X).over Y).obj).map
        (((_root_.SheafOfModules.overFunctor (S.over X) Y).map α)).val) :=
    locallySurjective_over α (locallySurjective_of_epi α) Y
  have hepiα : Epi ((_root_.SheafOfModules.overFunctor (S.over X) Y).map α) :=
    epi_of_locallySurjective _ hLSα
  have hEcol : PreservesColimitsOfSize.{u, u}
      (kernelIteratedSliceEquivGeneral (S := S) X Y).inverse := inferInstance
  have hpre : (kernelIteratedSliceEquivGeneral (S := S) X Y).functor.obj
        ((kernelIteratedSliceEquivGeneral (S := S) X Y).inverse.obj ((((Kmod.over X).over Y)))) ≅
        (kernelIteratedSliceEquivGeneral (S := S) X Y).functor.obj (((Kmod.over Y.left))) :=
    (kernelIteratedSliceEquivGeneral (S := S) X Y).counitIso.app _
  have hiso : (kernelIteratedSliceEquivGeneral (S :=
      S) X Y).inverse.obj ((((Kmod.over X).over Y))) ≅
        (((Kmod.over Y.left))) :=
    (kernelIteratedSliceEquivGeneral (S := S) X Y).fullyFaithfulFunctor.preimageIso hpre
  exact ⟨(((G.ofEpi ((_root_.SheafOfModules.overFunctor (S.over X) Y).map α)).mapEquivalenceWeak
      (kernelIteratedSliceEquivGeneral (S := S) X Y).symm (Iso.refl _)).ofEpi hiso.hom),
    ⟨(inferInstance : G.IsFiniteType).finite⟩⟩

omit [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X),
    HasWeakSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X),
    ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X) (Z : Over Y),
    HasWeakSheafify (((J.over X).over Y).over Z) AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X) (Z : Over Y),
    (((J.over X).over Y).over Z).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Transport generating sections along `overMap`, using only weak
sheafification on the target: the free comparison is built directly from its
coproduct universal property (`weakMapFreeIso`). Unlike Mathlib's
`GeneratingSections.map`, this needs no strong sheafification instance on the
target and no colimit-preservation hypothesis on the functor beyond the
supplied local-surjectivity proof. -/
private noncomputable def _root_.SheafOfModules.GeneratingSections.mapFinite {Y V : C}
    {M : SheafOfModules.{u} (R.over Y)} (G : M.GeneratingSections)
    (q : V ⟶ Y) [Finite G.I]
    (hG : Presheaf.IsLocallySurjective (J.over Y)
      ((PresheafOfModules.toPresheaf (R.over Y).obj).map G.π.val)) :
    ((_root_.SheafOfModules.overMap R q).obj M).GeneratingSections where
  I := G.I
  s := ((_root_.SheafOfModules.overMap R q).obj M).freeHomEquiv
    ((weakMapFreeIso (_root_.SheafOfModules.overMap R q) G.I (_root_.SheafOfModules.overMapUnitIso
        q).symm).hom ≫
      (_root_.SheafOfModules.overMap R q).map G.π)
  epi := by
    rw [Equiv.symm_apply_apply]
    have : Epi ((_root_.SheafOfModules.overMap R q).map G.π) :=
      epi_of_locallySurjective _ (locallySurjective_overMap G.π hG q)
    infer_instance


omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X),
    HasWeakSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X),
    ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X) (Z : Over Y),
    HasWeakSheafify (((J.over X).over Y).over Z) AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X) (Z : Over Y),
    (((J.over X).over Y).over Z).WEqualsLocallyBijective AddCommGrpCat.{u}] in
private lemma transported_section_eval_mapFinite {Y V : C} {M : SheafOfModules.{u} R}
    (G : (M.over Y).GeneratingSections) (q : V ⟶ Y) [Finite G.I]
    (k : G.I) (U' : (Over V)ᵒᵖ) :
    (((G.mapFinite q (locallySurjective_of_epi G.π)).ofEpi ((_root_.SheafOfModules.overFunctorMap R
        q).app M).hom).s k).eval U' =
      (G.s k).eval (Opposite.op (Over.mk (U'.unop.hom ≫ q))) := by
  have key : SheafOfModules.ιFree (R := R.over V) k ≫
        (weakMapFreeIso (_root_.SheafOfModules.overMap R q) G.I
            (_root_.SheafOfModules.overMapUnitIso q).symm).hom ≫
          (_root_.SheafOfModules.overMap R q).map G.π =
      (_root_.SheafOfModules.overMap R q).map (SheafOfModules.ιFree k ≫ G.π) := by
    rw [← Category.assoc, ιFree_weakMapFreeIso_hom,
      Category.assoc, ← Functor.map_comp, SheafOfModules.overMapUnitIso]
    exact Category.id_comp _
  have h2 : ((_root_.SheafOfModules.overMap R q).obj (M.over Y)).unitHomEquiv.symm
        ((G.mapFinite q (locallySurjective_of_epi G.π)).s k) =
      (_root_.SheafOfModules.overMap R q).map (SheafOfModules.ιFree k ≫ G.π) := by
    rw [show (G.mapFinite q (locallySurjective_of_epi G.π)).s k =
        ((_root_.SheafOfModules.overMap R q).obj (M.over Y)).unitHomEquiv
      (SheafOfModules.ιFree k ≫
        (weakMapFreeIso (_root_.SheafOfModules.overMap R q) G.I
            (_root_.SheafOfModules.overMapUnitIso q).symm).hom ≫
          (_root_.SheafOfModules.overMap R q).map G.π) from rfl, Equiv.symm_apply_apply, key]
  have hmapsec : (G.mapFinite q (locallySurjective_of_epi G.π)).s k =
      ((_root_.SheafOfModules.overMap R q).obj (M.over Y)).unitHomEquiv
        ((_root_.SheafOfModules.overMap R q).map (SheafOfModules.ιFree k ≫ G.π)) := by
    have h3 := congrArg ((_root_.SheafOfModules.overMap R q).obj (M.over Y)).unitHomEquiv h2
    rwa [Equiv.apply_symm_apply] at h3
  have hsymm : SheafOfModules.ιFree (R := R.over Y) k ≫ G.π =
      (M.over Y).unitHomEquiv.symm (G.s k) := by
    simpa using (SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply
      (M := M.over Y) (f := G.π) (i := k)).symm
  have hunfold : (((G.mapFinite q (locallySurjective_of_epi G.π)).ofEpi
      ((_root_.SheafOfModules.overFunctorMap R q).app M).hom).s k).eval U' =
      (((_root_.SheafOfModules.overMap R q).map ((M.over Y).unitHomEquiv.symm (G.s k))).val.app U'
        (1 : (R.over V).obj.obj U')) := by
    change (((_root_.SheafOfModules.overFunctorMap R q).app M).hom.val.app U'
      (((G.mapFinite q (locallySurjective_of_epi G.π)).s k).eval U')) = _
    rw [hmapsec]
    change (((_root_.SheafOfModules.overFunctorMap R q).app M).hom.val.app U'
      ((((_root_.SheafOfModules.overMap R q).map (SheafOfModules.ιFree k ≫ G.π)).val.app) U'
        (1 : (R.over V).obj.obj U'))) = _
    rw [hsymm]
    rfl
  rw [hunfold]
  change ((((M.over Y).unitHomEquiv.symm (G.s k))).val.app
    ((Over.map q).op.obj U') (1 : (R.over V).obj.obj U')) = _
  have hss : (M.over Y).unitHomEquiv ((M.over Y).unitHomEquiv.symm (G.s k)) = G.s k :=
    Equiv.apply_symm_apply _ _
  have hco := SheafOfModules.unitHomEquiv_apply_coe (M := M.over Y)
    ((M.over Y).unitHomEquiv.symm (G.s k)) ((Over.map q).op.obj U')
  rw [hss] at hco
  exact hco.symm

-- Thick subcategory for coherence (Stacks 01BY): kernels, cokernels and extensions
-- of coherent modules are coherent; no extra coherence hypothesis on `𝒪` needed.
-- N.B.: the `unusedSectionVars` linter walks the proof term per section variable
-- with no sharing cache (~23 min on this proof); vars are curated via `omit`.
set_option linter.unusedSectionVars false in
omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X) (Z : Over Y),
    HasWeakSheafify (((J.over X).over Y).over Z) AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X) (Z : Over Y),
    (((J.over X).over Y).over Z).WEqualsLocallyBijective AddCommGrpCat.{u}] in
theorem isCoherent_kernel {M N : SheafOfModules.{u} R}
    [IsCoherent (R := R) M] [IsCoherent (R := R) N]
    (_φ : M ⟶ N) :
    IsCoherent (R := R) (Limits.kernel _φ) := by
  classical
  constructor
  · -- `kernel _φ` is finite type, via a nested cover (Stacks 01BY, kernel part).
    have : _root_.SheafOfModules.IsFiniteType (R := R) M := IsCoherent.finiteType
    obtain ⟨σ, hσ⟩ := _root_.SheafOfModules.IsFiniteType.exists_localGeneratorsData M
    have hEpi : ∀ i, ∃ (n : ℕ)
        (π : _root_.SheafOfModules.free (R := R.over (σ.X i)) (ULift.{u} (Fin n)) ⟶ M.over (σ.X i)),
        Epi π := fun i => by
      have := hσ.isFiniteType i
      exact epiFreeFin_of_finiteGenerators (σ.generators i)
    choose n π hπ using hEpi
    have hK : ∀ i, _root_.SheafOfModules.IsFiniteType (R := R.over (σ.X i))
        (Limits.kernel ((π i) ≫ (_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ)) :=
      fun i => IsCoherent.kernel_finiteType (σ.X i)
        ((π i) ≫ (_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ)
    choose τ hτ using fun i => by
      haveI := hK i
      exact _root_.SheafOfModules.IsFiniteType.exists_localGeneratorsData
        (Limits.kernel ((π i) ≫ (_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ))
    -- Each `kernel (π i ≫ φ)` surjects onto `(kernel _φ).over _`:
    -- the comparison map is the pullback of the epi `π i`.
    have hα : ∀ i, ∃ (α : Limits.kernel ((π i) ≫
        (_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ)
        ⟶ (Limits.kernel _φ).over (σ.X i)), Epi α := by
      intro i
      have hπi : Epi (π i) := hπ i
      have h0 : (Limits.kernel.ι ((π i) ≫ (_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ) ≫
            (π i)) ≫ (_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ = 0 := by
        rw [Category.assoc]
        exact Limits.kernel.condition _
      have hm : Limits.pullback.fst (π i)
            (Limits.kernel.ι ((_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ)) ≫
            ((π i) ≫ (_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ) = 0 := by
        simp only [← Category.assoc, Limits.pullback.condition]
        simp only [Category.assoc, Limits.kernel.condition, comp_zero]
      have heq : Limits.kernel.lift ((π i) ≫ (_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ)
            (Limits.pullback.fst (π i)
              (Limits.kernel.ι ((_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ))) hm ≫
            Limits.kernel.lift ((_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ)
              (Limits.kernel.ι ((π i) ≫ (_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ) ≫
                (π i)) h0 =
            Limits.pullback.snd (π i)
              (Limits.kernel.ι ((_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ)) := by
        refine (cancel_mono
          (Limits.kernel.ι ((_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ))).mp ?_
        have e1 : Limits.kernel.lift ((_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ)
              (Limits.kernel.ι ((π i) ≫ (_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ) ≫
                (π i)) h0 ≫
              Limits.kernel.ι ((_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ) =
              Limits.kernel.ι ((π i) ≫ (_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ) ≫
                (π i) :=
          Limits.kernel.lift_ι _ _ _
        have e2 : Limits.kernel.lift ((π i) ≫ (_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ)
              (Limits.pullback.fst (π i)
                (Limits.kernel.ι ((_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ))) hm ≫
              Limits.kernel.ι ((π i) ≫ (_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ) =
              Limits.pullback.fst (π i)
                (Limits.kernel.ι ((_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ)) :=
          Limits.kernel.lift_ι _ _ _
        have step : (Limits.kernel.lift ((π i) ≫
            (_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ)
                (Limits.pullback.fst (π i)
                  (Limits.kernel.ι ((_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ))) hm ≫
              Limits.kernel.lift ((_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ)
                (Limits.kernel.ι ((π i) ≫ (_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ) ≫
                  (π i)) h0) ≫
              Limits.kernel.ι ((_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ) =
              Limits.pullback.fst (π i)
                (Limits.kernel.ι ((_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ)) ≫ (π i) :=
          (Category.assoc _ _ _).trans ((congrArg (Limits.kernel.lift
                ((π i) ≫ (_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ)
                (Limits.pullback.fst (π i)
                  (Limits.kernel.ι ((_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ))) hm ≫ ·)
              e1).trans
            ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (π i)) e2)))
        exact step.trans (Limits.pullback.condition (f := π i)
          (g := Limits.kernel.ι ((_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ)))
      have : Epi (Limits.pullback.snd (π i)
          (Limits.kernel.ι ((_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ))) := inferInstance
      have hLiftEpi : Epi (Limits.kernel.lift ((_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ)
          (Limits.kernel.ι ((π i) ≫ (_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ) ≫
            (π i)) h0) :=
        epi_of_epi_fac heq
      refine ⟨(Limits.kernel.lift ((_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ)
          (Limits.kernel.ι ((π i) ≫ (_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ) ≫
            (π i)) h0) ≫
          (PreservesKernel.iso (_root_.SheafOfModules.overFunctor R (σ.X i)) _φ).symm.hom,
        inferInstance⟩
    choose α hαEpi using hα
    -- Finite generators on each nested piece, transported to the base site
    -- along the iterated-slice equivalence.
    have piece : ∀ p : (i : σ.I) × (τ i).I,
        ∃ G : ((Limits.kernel _φ).over (((τ p.1).X p.2).left)).GeneratingSections,
          G.IsFiniteType := by
      intro ⟨i, j⟩
      have hfin : ((τ i).generators j).IsFiniteType := (hτ i).isFiniteType j
      have := hαEpi i
      -- Transfer finite generating sections through the iterated-slice equivalence.




      exact kernelPieceGenerators (Limits.kernel _φ) (σ.X i) ((τ i).X j)
        (Limits.kernel ((π i) ≫ (_root_.SheafOfModules.overFunctor R (σ.X i)).map _φ)) (α i)
        ((τ i).generators j)
    choose gen hgen using piece
    have hcover : J.CoversTop
        (fun p : (i : σ.I) × (τ i).I => ((τ p.1).X p.2).left) :=
      σ.coversTop.over (fun i => (τ i).coversTop)
    -- Shrinking the generating family preserves finiteness.


    exact ⟨((⟨(i : σ.I) × (τ i).I,
      fun p : (i : σ.I) × (τ i).I => ((τ p.1).X p.2).left, hcover, gen⟩ :
      (Limits.kernel _φ).LocalGeneratorsData)).shrink,
      _root_.SheafOfModules.LocalGeneratorsData.IsFiniteType.shrink
        (⟨(i : σ.I) × (τ i).I,
          fun p : (i : σ.I) × (τ i).I => ((τ p.1).X p.2).left, hcover, gen⟩ :
          (Limits.kernel _φ).LocalGeneratorsData)
        ⟨fun p ↦ hgen p⟩⟩
  · -- Kernels of maps from finite frees factor through `M`,
    -- where they are finite type by coherence of `M`.
    intro X n ψ
    set k : (Limits.kernel _φ).over X ≅
        Limits.kernel ((_root_.SheafOfModules.overFunctor R X).map _φ) :=
      PreservesKernel.iso (_root_.SheafOfModules.overFunctor R X) _φ with hk
    have hMonoι : Mono (k.hom ≫
        Limits.kernel.ι ((_root_.SheafOfModules.overFunctor R X).map _φ)) := inferInstance
    have hK : _root_.SheafOfModules.IsFiniteType (R := R.over X)
        (Limits.kernel (ψ ≫ k.hom ≫
          Limits.kernel.ι ((_root_.SheafOfModules.overFunctor R X).map _φ))) :=
      IsCoherent.kernel_finiteType X _
    set eker : Limits.kernel ψ ≅
        Limits.kernel (ψ ≫ k.hom ≫
          Limits.kernel.ι ((_root_.SheafOfModules.overFunctor R X).map _φ)) :=
      (Limits.kernelCompMono ψ (k.hom ≫
        Limits.kernel.ι ((_root_.SheafOfModules.overFunctor R X).map _φ))).symm with heker
    obtain ⟨δ, hδ⟩ := _root_.SheafOfModules.IsFiniteType.exists_localGeneratorsData
      (Limits.kernel (ψ ≫ k.hom ≫
        Limits.kernel.ι ((_root_.SheafOfModules.overFunctor R X).map _φ)))
    have piece : ∀ i : δ.I,
        ∃ G : ((Limits.kernel ψ).over (δ.X i)).GeneratingSections,
          G.IsFiniteType := by
      intro i
      have := hδ.isFiniteType i
      exact ⟨((δ.generators i).ofEpi
        (((_root_.SheafOfModules.overFunctor (R.over X) (δ.X i)).mapIso eker).symm.hom)),
        inferInstance⟩
    choose gen hgen using piece
    exact ⟨⟨δ.I, δ.X, δ.coversTop, gen⟩, ⟨fun i ↦ hgen i⟩⟩

/-- Cokernels of morphisms between coherent module sheaves are coherent. -/
theorem isCoherent_cokernel {M N : SheafOfModules.{u} R}
    [IsCoherent (R := R) M] [IsCoherent (R := R) N]
    (_φ : M ⟶ N) :
    IsCoherent (R := R) (Limits.cokernel _φ) := by
  classical
  have hMFT : _root_.SheafOfModules.IsFiniteType (R := R) M := IsCoherent.finiteType
  have hNFT : _root_.SheafOfModules.IsFiniteType (R := R) N := IsCoherent.finiteType
  constructor
  · have : Epi (Limits.cokernel.π _φ) := inferInstance
    exact isFiniteType_of_epi' (Limits.cokernel.π _φ)
  · intro X n ψ
    let hDouble : ∀ U : Over X,
        HasSheafify ((J.over X).over U) AddCommGrpCat.{u} :=
      fun U ↦ hasSheafifyIteratedSlice J X U
    let hTriple : ∀ (U : Over X) (V : Over U),
        HasSheafify (((J.over X).over U).over V) AddCommGrpCat.{u} :=
      fun U V ↦ hasSheafifyIteratedSlice (J.over X) U V
    have hπX : Epi ((_root_.SheafOfModules.overFunctor R X).map (Limits.cokernel.π _φ)) :=
      epi_over_of_epi _ _
    obtain ⟨σ, hσ⟩ := _root_.SheafOfModules.IsFiniteType.exists_localGeneratorsData M
    -- The `n` sections of the cokernel defined by `ψ`.
    set c : Fin n → ((Limits.cokernel _φ).over X).sections :=
      fun k => ((Limits.cokernel _φ).over X).freeHomEquiv ψ (ULift.up k) with hc
    -- The presheaf map of the restricted cokernel projection; it is locally
    -- surjective since the projection is an epi.
    set fπ := (PresheafOfModules.toPresheaf (R.over X).obj).map
      ((_root_.SheafOfModules.overFunctor R X).map (Limits.cokernel.π _φ)).val with hfπ
    have hLS : Presheaf.IsLocallySurjective (J.over X) fπ :=
      locallySurjective_of_epi _
    -- Finite intersections of image sieves are covering.
    have hInter : ∀ (V : Over X) (m : ℕ)
        (d : Fin m → ((Limits.cokernel _φ).over X).sections),
        Finset.univ.inf (fun k => Presheaf.imageSieve fπ
          ((d k).eval (Opposite.op V))) ∈ (J.over X) V :=
      fun V m d =>
        GrothendieckTopology.finsetInf_mem _ (fun k => Presheaf.imageSieve_mem (J.over X) fπ _)
    -- Witness sieve from `M`'s finite-type data, transported to the slice.
    have hT : ∀ (V : Over X),
        (Sieve.overEquiv V).symm (Sieve.ofObjects σ.X V.left) ∈ (J.over X) V :=
      fun V => J.overEquiv_symm_mem_over V _ (σ.coversTop V.left)
    have hR : ∀ (V : Over X),
        Finset.univ.inf (fun k : Fin n => Presheaf.imageSieve fπ
          ((c k).eval (Opposite.op V))) ⊓
        (Sieve.overEquiv V).symm (Sieve.ofObjects σ.X V.left) ∈ (J.over X) V :=
      fun V => (J.over X).intersection_covering (hInter V n c) (hT V)
    -- The combined cover family: over each `V`, arrows in both sieves.
    set Rsv : ∀ V : Over X, Sieve V := fun V =>
      Finset.univ.inf (fun k : Fin n => Presheaf.imageSieve fπ
        ((c k).eval (Opposite.op V))) ⊓
      (Sieve.overEquiv V).symm (Sieve.ofObjects σ.X V.left) with hRsv
    set I0 : Type _ := Σ (V : Over X) (U : Over X) (h : U ⟶ V),
      PLift ((Rsv V).arrows h) with hI0
    set Y0 : I0 → Over X := fun i => i.2.1 with hY0
    have hcover : (J.over X).CoversTop Y0 := by
      intro W
      apply (J.over X).superset_covering (S := Rsv W) _ (hR W)
      intro U a ha
      exact ⟨⟨W, U, a, PLift.up ha⟩, ⟨𝟙 U⟩⟩
    have piece : ∀ i0 : I0,
        ∃ (D : ((Limits.kernel ψ).over (Y0 i0)).LocalGeneratorsData),
          D.IsFiniteType := by
      intro ⟨V, U, h, hR⟩
      have hS : (Finset.univ.inf (fun k : Fin n => Presheaf.imageSieve fπ
          ((c k).eval (Opposite.op V)))).arrows h := hR.down.1
      have hT : ((Sieve.overEquiv V).symm
          (Sieve.ofObjects σ.X V.left)).arrows h := hR.down.2
      -- Membership extraction from the finite intersection.
      have hMem : ∀ (m : ℕ) (d : Fin m → ((Limits.cokernel _φ).over X).sections)
          (k : Fin m), (Finset.univ.inf (fun j => Presheaf.imageSieve fπ
            ((d j).eval (Opposite.op V)))).arrows h →
          (Presheaf.imageSieve fπ ((d k).eval (Opposite.op V))).arrows h :=
        fun m d k hh => Sieve.finsetInf_arrows _ h hh k
      have hmem : ∀ k : Fin n,
          Presheaf.imageSieve fπ ((c k).eval (Opposite.op V)) h :=
        fun k => hMem n c k hS
      choose t ht using hmem
      obtain ⟨iM, ⟨w⟩⟩ := (Sieve.mem_ofObjects_iff _ _).mp
        ((Sieve.overEquiv_symm_iff _ _).mp hT)
      -- Base object and the iterated-slice equivalence.
      set Z : C := U.left with hZ
      set fX : Z ⟶ X := U.hom with hfX
      set E : SheafOfModules.{u} (R.over Z) ≌ SheafOfModules.{u} ((R.over X).over U) :=
        _root_.SheafOfModules.overOverEquivalence (S := R) U with hE
      have hEcol : PreservesColimitsOfSize.{u, u} E.inverse := inferInstance
      have : IsIso (𝟙 ((R.over X).over U)) := ⟨𝟙 _, by simp, by simp⟩
      have : IsIso (𝟙 (R.over X)) := ⟨𝟙 _, by simp, by simp⟩
      -- Restricted modules over the double slice.
      set NS : SheafOfModules.{u} ((R.over X).over U) :=
        (_root_.SheafOfModules.overFunctor (R.over X) U).obj ((_root_.SheafOfModules.overFunctor R
            X).obj N) with hNS
      set MS : SheafOfModules.{u} ((R.over X).over U) :=
        (_root_.SheafOfModules.overFunctor (R.over X) U).obj ((_root_.SheafOfModules.overFunctor R
            X).obj M) with hMS
      set CS : SheafOfModules.{u} ((R.over X).over U) :=
        (_root_.SheafOfModules.overFunctor (R.over X) U).obj ((_root_.SheafOfModules.overFunctor R
            X).obj (Limits.cokernel _φ)) with hCS
      set FS : SheafOfModules.{u} ((R.over X).over U) :=
        (_root_.SheafOfModules.overFunctor (R.over X) U).obj (_root_.SheafOfModules.free (R :=
            R.over X) (ULift.{u} (Fin n))) with hFS
      set φS : MS ⟶ NS :=
        (_root_.SheafOfModules.overFunctor (R.over X) U).map ((_root_.SheafOfModules.overFunctor R
            X).map _φ) with hφS
      set πS : NS ⟶ CS :=
        (_root_.SheafOfModules.overFunctor (R.over X) U).map ((_root_.SheafOfModules.overFunctor R
            X).map (Limits.cokernel.π _φ)) with hπS
      set ψS : FS ⟶ CS := (_root_.SheafOfModules.overFunctor (R.over X) U).map ψ with hψS
      -- Free comparison isos (unit preservation is definitional for pushforwards).
      set eO : _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin n)) ≅ FS :=
        finiteFreeOverIso (R.over X) U n with heO
      set eE : _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin n)) ≅ E.inverse.obj
          (_root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin n))) :=
        weakMapFreeIso E.inverse _ (Iso.refl _) with heE
      set dF : _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin n)) ≅ E.inverse.obj FS :=
        eE ≪≫ E.inverse.mapIso eO with hdF
      -- Base-slice modules and maps (E-world).
      set NQ : SheafOfModules.{u} (R.over Z) := E.inverse.obj NS with hNQ
      set MQ : SheafOfModules.{u} (R.over Z) := E.inverse.obj MS with hMQ
      set CQ : SheafOfModules.{u} (R.over Z) := E.inverse.obj CS with hCQ
      set φQ : MQ ⟶ NQ := E.inverse.map φS with hφQ
      set πQ : NQ ⟶ CQ := E.inverse.map πS with hπQ
      set ψQ : _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin n)) ⟶ CQ :=
        dF.hom ≫ E.inverse.map ψS with hψQ
      -- The preimages as elements for the restricted projection.
      have htX : ∀ k : Fin n,
          ((_root_.SheafOfModules.overFunctor R X).map (Limits.cokernel.π _φ)).val.app
          (Opposite.op U) (t k)
          = ((_root_.SheafOfModules.overFunctor R X).obj (Limits.cokernel _φ)).val.map h.op ((c
              k).eval (Opposite.op V)) :=
        fun k => ht k
      have sm_eval : ∀ {M N : SheafOfModules.{u} ((R.over X).over U)}
          (f : M ⟶ N) (s : M.sections) (X),
          (_root_.SheafOfModules.sectionsMap f s).eval X = f.val.app X (s.eval X) :=
        fun f s X => rfl
      -- Lift sections over the double slice, from the preimage elements.
      let htilde : ∀ k : Fin n, NS.sections := fun k =>
        PresheafOfModules.sectionsMk (fun W' => (N.over X).val.map (W'.unop.hom).op (t k))
          (fun X' Y' f => by
            dsimp only
            have tri : Y'.unop.hom
                = (Over.forget U).map f.unop ≫ X'.unop.hom := (Over.w f.unop).symm
            have key : ((_root_.SheafOfModules.overFunctor (R.over X) U).obj (N.over X)).val.map f
                = (N.over X).val.map ((Over.forget U).map f.unop).op := rfl
            change ((_root_.SheafOfModules.overFunctor (R.over X) U).obj (N.over X)).val.map f
                    ((N.over X).val.map (X'.unop.hom).op (t k)) = _
            rw [key, tri]
            exact (PresheafOfModules.map_comp_apply (M := (N.over X).val)
              (i := (X'.unop.hom).op) (j := ((Over.forget U).map f.unop).op)
              (t k)).symm)
      have htilde_eval : ∀ k W',
          (htilde k).eval W' = (N.over X).val.map (W'.unop.hom).op (t k) :=
        fun k W' => rfl
      set utildeS : _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin n)) ⟶ NS :=
        (_root_.SheafOfModules.freeHomEquiv _).symm (fun j => htilde j.down) with hutildeS
      set utildeQ : _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin n)) ⟶ NQ :=
        eE.hom ≫ E.inverse.map utildeS with hutildeQ
      -- Characterization of `eO.hom` on free sections.
      have hd : ∀ j : ULift.{u} (Fin n),
          _root_.SheafOfModules.sectionsMap eO.hom (_root_.SheafOfModules.freeSection j)
            = FS.unitHomEquiv
              ((_root_.SheafOfModules.overFunctor (R.over X) U).map (_root_.SheafOfModules.ιFree
                  j)) := by
        intro j
        have e1 : _root_.SheafOfModules.freeSection (R := (R.over X).over U) j
            = (_root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin n))).unitHomEquiv
              (_root_.SheafOfModules.ιFree j ≫ 𝟙 _) := rfl
        simp only [e1, ← _root_.SheafOfModules.unitHomEquiv_comp_apply, Category.assoc,
            Category.id_comp,
          heO]
        rw [ιFree_finiteFreeOverIso_hom (R.over X) U n j]
      have eUtil : ∀ j, NS.freeHomEquiv utildeS j = htilde j.down := by
        intro j
        rw [hutildeS]
        exact congrFun ((_root_.SheafOfModules.freeHomEquiv NS).apply_symm_apply _) j
      -- The double-slice lift equation.
      have hS : utildeS ≫ πS = eO.hom ≫ ψS := by
        apply (_root_.SheafOfModules.freeHomEquiv _).injective
        funext j
        rw [_root_.SheafOfModules.freeHomEquiv_comp_apply,
            _root_.SheafOfModules.freeHomEquiv_comp_apply, eUtil,
          _root_.SheafOfModules.freeHomEquiv_apply, hd j]
        apply PresheafOfModules.sections_ext
        intro W'
        have eLHS : PresheafOfModules.sections.eval (_root_.SheafOfModules.sectionsMap πS (htilde
            j.down)) W'
            = PresheafOfModules.sections.eval (c j.down)
              (Opposite.op W'.unop.left) := by
          rw [sm_eval, htilde_eval, hπS]
          have eDouble : ((_root_.SheafOfModules.overFunctor (R.over X) U).map
              ((_root_.SheafOfModules.overFunctor R X).map
                  (Limits.cokernel.π _φ))).val.app W'
                  (((N.over X).val.map (W'.unop.hom).op) (t j.down))
              = ((_root_.SheafOfModules.overFunctor R X).map (Limits.cokernel.π _φ)).val.app
                  (Opposite.op W'.unop.left)
                  (((N.over X).val.map (W'.unop.hom).op) (t j.down)) := by

            rfl
          rw [eDouble]
          refine (PresheafOfModules.naturality_apply
            (((_root_.SheafOfModules.overFunctor R X).map (Limits.cokernel.π _φ)).val)
            (W'.unop.hom).op (t j.down)).trans ?_
          rw [htX j.down]
          refine (PresheafOfModules.map_comp_apply (M :=
              ((_root_.SheafOfModules.overFunctor R X).obj
              (Limits.cokernel _φ)).val) h.op (W'.unop.hom).op
            ((c j.down).eval (Opposite.op V))).symm.trans ?_
          exact PresheafOfModules.sections_property (c j.down) _
        have eRHS : (_root_.SheafOfModules.sectionsMap ψS (FS.unitHomEquiv
            ((_root_.SheafOfModules.overFunctor (R.over X) U).map (_root_.SheafOfModules.ιFree
                j)))).eval W'
            = ((c j.down).eval (Opposite.op W'.unop.left)) := by
          rw [sm_eval,
            show (FS.unitHomEquiv ((_root_.SheafOfModules.overFunctor (R.over X) U).map
                (_root_.SheafOfModules.ιFree j))).eval W'
              = (((_root_.SheafOfModules.overFunctor (R.over X) U).map (_root_.SheafOfModules.ιFree
                  j)).val.app W'
                (1 : ((R.over X).over U).obj.obj W')) from
              _root_.SheafOfModules.unitHomEquiv_apply_coe _ _ _,
            show ψS.val.app W' _
              = ψ.val.app (Opposite.op W'.unop.left) _ from rfl,
            show ((_root_.SheafOfModules.overFunctor (R.over X) U).map (_root_.SheafOfModules.ιFree
                j)).val.app W'
                (1 : ((R.over X).over U).obj.obj W')
              = (_root_.SheafOfModules.ιFree j).val.app (Opposite.op W'.unop.left)
                (1 : ((R.over X).obj.obj (Opposite.op W'.unop.left))) from rfl,
            show (ψ.val.app (Opposite.op W'.unop.left))
                (((_root_.SheafOfModules.ιFree j).val.app (Opposite.op W'.unop.left))
                  (1 : ((R.over X).obj.obj (Opposite.op W'.unop.left))))
              = ((_root_.SheafOfModules.ιFree (ULift.up j.down) ≫ ψ).val.app
                (Opposite.op W'.unop.left))
                (1 : ((R.over X).obj.obj (Opposite.op W'.unop.left))) from rfl]
          have e2 : ((c j.down).eval (Opposite.op W'.unop.left))
              = ((_root_.SheafOfModules.ιFree (ULift.up j.down) ≫
                  ψ).val.app (Opposite.op W'.unop.left))
                (1 : ((R.over X).obj.obj (Opposite.op W'.unop.left))) := by
            rw [hc]
            exact (_root_.SheafOfModules.unitHomEquiv_apply_coe _ _ _).symm
          rw [e2, ULift.up_down]
        exact eLHS.trans eRHS.symm
      have hlift : utildeQ ≫ πQ = ψQ := by
        rw [hutildeQ, hπQ, hψQ, hdF, Iso.trans_hom, Category.assoc,
          ← Functor.map_comp, hS, Functor.map_comp, Category.assoc,
          Functor.mapIso_hom]
      -- Restriction comparison iso (definitional for pushforwards).
      have dC : ∀ P : SheafOfModules.{u} R,
          (_root_.SheafOfModules.overFunctor R Z).obj P ≅ E.inverse.obj
            ((_root_.SheafOfModules.overFunctor (R.over X) U).obj
                ((_root_.SheafOfModules.overFunctor R X).obj P)) :=
        fun P => E.unitIso.app ((_root_.SheafOfModules.overFunctor R Z).obj P)
      -- Finite epi onto `M` over the piece, from `M`'s finite-type data.
      have hGiM : (σ.generators iM).IsFiniteType := hσ.isFiniteType iM
      have : Finite (σ.generators iM).I := hGiM.finite
      -- Universe-pinning ascription: the `.{u}` is load-bearing for inference;
      -- the proof comes from the shared `overMap_additive` instance.
      let : (_root_.SheafOfModules.overMap.{u} R w).Additive := inferInstance
      have hOMcol : PreservesColimitsOfShape (Discrete (σ.generators iM).I)
          (_root_.SheafOfModules.overMap R w) := inferInstance
      let mappedGiM : ((_root_.SheafOfModules.overMap R w).obj (M.over (σ.X
          iM))).GeneratingSections :=
        { I := (σ.generators iM).I
          s := ((_root_.SheafOfModules.overMap R w).obj (M.over (σ.X iM))).freeHomEquiv
            ((weakMapFreeIso (_root_.SheafOfModules.overMap R w) (σ.generators iM).I
              (_root_.SheafOfModules.overMapUnitIso w).symm).hom ≫
                (_root_.SheafOfModules.overMap R w).map (σ.generators iM).π)
          epi := by
            rw [Equiv.symm_apply_apply]
            have : Epi ((_root_.SheafOfModules.overMap R w).map (σ.generators iM).π) :=
              epi_overMap_of_epi (σ.generators iM).π w
            infer_instance }
      have : mappedGiM.IsFiniteType := ⟨inferInstance⟩
      obtain ⟨m, εX, hεX⟩ := epiFreeFin_of_finiteGenerators mappedGiM
      have := hεX
      set eM1 : (_root_.SheafOfModules.overMap R w).obj (M.over (σ.X
          iM)) ≅ (_root_.SheafOfModules.overFunctor R Z).obj M :=
        (_root_.SheafOfModules.overFunctorMap R w).app M with heM1
      have : Epi eM1.hom := IsIso.epi_of_iso _
      have : Epi (dC M).hom := IsIso.epi_of_iso _
      set εQ : _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin m)) ⟶ MQ :=
        εX ≫ eM1.hom ≫ (dC M).hom with hεQ
      have : Epi εQ := by infer_instance
      -- Free on a sum is the biproduct.
      set eSum : _root_.SheafOfModules.free (R :=
          R.over Z) (ULift.{u} (Fin n) ⊕ ULift.{u} (Fin m)) ≅
          _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin n)) ⊞
            _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin m)) :=
        {
          hom := (_root_.SheafOfModules.freeHomEquiv _).symm (Sum.elim
            (fun a => _root_.SheafOfModules.sectionsMap biprod.inl
                (_root_.SheafOfModules.freeSection a))
            (fun b => _root_.SheafOfModules.sectionsMap biprod.inr
                (_root_.SheafOfModules.freeSection b))),
          inv := biprod.desc (_root_.SheafOfModules.freeMap Sum.inl) (_root_.SheafOfModules.freeMap
              Sum.inr),
          hom_inv_id := by
            apply (_root_.SheafOfModules.freeHomEquiv _).injective
            funext s
            rcases s with ⟨a⟩ | ⟨b⟩
            · conv_rhs => rw [_root_.SheafOfModules.freeHomEquiv_apply,
                _root_.SheafOfModules.sectionsMap_id]
              simp only [_root_.SheafOfModules.freeHomEquiv_comp_apply, Equiv.apply_symm_apply,
                ← _root_.SheafOfModules.sectionsMap_comp, biprod.inl_desc,
                    _root_.SheafOfModules.sectionMap_freeMap_freeSection,
                Sum.elim_inl]
            · conv_rhs => rw [_root_.SheafOfModules.freeHomEquiv_apply,
                _root_.SheafOfModules.sectionsMap_id]
              simp only [_root_.SheafOfModules.freeHomEquiv_comp_apply, Equiv.apply_symm_apply,
                ← _root_.SheafOfModules.sectionsMap_comp, biprod.inr_desc,
                    _root_.SheafOfModules.sectionMap_freeMap_freeSection,
                Sum.elim_inr],
          inv_hom_id := by
            apply IsColimit.hom_ext (BinaryBiproduct.isColimit _ _)
            rintro ⟨_|_⟩
            · change (biprod.inl
                    (X := _root_.SheafOfModules.free (R := R.over Z)
                      (ULift.{u} (Fin n)))
                    (Y := _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin m)))) ≫
                    (biprod.desc
                      (_root_.SheafOfModules.freeMap (R := R.over Z) (Sum.inl : ULift.{u} (Fin n) →
                        ULift.{u} (Fin n) ⊕ ULift.{u} (Fin m)))
                      (_root_.SheafOfModules.freeMap (R := R.over Z) (Sum.inr : ULift.{u} (Fin m) →
                        ULift.{u} (Fin n) ⊕ ULift.{u} (Fin m))) ≫ _) =
                  (biprod.inl (X := _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin n)))
                    (Y := _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin m)))) ≫ 𝟙 _
              simp only [← Category.assoc, biprod.inl_desc]
              apply (_root_.SheafOfModules.freeHomEquiv _).injective
              funext a
              conv_rhs => rw [Category.comp_id, _root_.SheafOfModules.freeHomEquiv_apply]
              simp only [_root_.SheafOfModules.freeHomEquiv_comp_apply,
                  _root_.SheafOfModules.freeHomEquiv_freeMap,
                _root_.SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection,
                    Function.comp_apply,
                Sum.elim_inl]
            · change (biprod.inr
                    (X := _root_.SheafOfModules.free (R := R.over Z)
                      (ULift.{u} (Fin n)))
                    (Y := _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin m)))) ≫
                    (biprod.desc
                      (_root_.SheafOfModules.freeMap (R := R.over Z) (Sum.inl : ULift.{u} (Fin n) →
                        ULift.{u} (Fin n) ⊕ ULift.{u} (Fin m)))
                      (_root_.SheafOfModules.freeMap (R := R.over Z) (Sum.inr : ULift.{u} (Fin m) →
                        ULift.{u} (Fin n) ⊕ ULift.{u} (Fin m))) ≫ _) =
                  (biprod.inr (X := _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin n)))
                    (Y := _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin m)))) ≫ 𝟙 _
              simp only [← Category.assoc, biprod.inr_desc]
              apply (_root_.SheafOfModules.freeHomEquiv _).injective
              funext b
              conv_rhs => rw [Category.comp_id, _root_.SheafOfModules.freeHomEquiv_apply]
              simp only [_root_.SheafOfModules.freeHomEquiv_comp_apply,
                  _root_.SheafOfModules.freeHomEquiv_freeMap,
                _root_.SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection,
                    Function.comp_apply,
                Sum.elim_inr],
        }
      have e_nm : ULift.{u} (Fin n) ⊕ ULift.{u} (Fin m) ≃ ULift.{u} (Fin (n + m)) :=
        (Equiv.sumCongr Equiv.ulift Equiv.ulift).trans
          (finSumFinEquiv.trans Equiv.ulift.symm)
      set e_free : _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin (n + m))) ≅
          _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin n)) ⊞
            _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin m)) :=
        (_root_.SheafOfModules.freeFunctor.mapIso e_nm.symm.toIso) ≪≫ eSum with he_free
      -- The combined map, its coherent version, and the projection.
      set βb : _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin (n + m))) ⟶ NQ :=
        e_free.hom ≫ biprod.desc utildeQ (-(εQ ≫ φQ)) with hβb
      set βcoh : _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin (n + m))) ⟶
          (_root_.SheafOfModules.overFunctor R Z).obj N :=
        βb ≫ (dC N).inv with hβcoh
      have hKcoh : _root_.SheafOfModules.IsFiniteType (R := R.over Z) (Limits.kernel βcoh) :=
        IsCoherent.kernel_finiteType Z βcoh
      set pdesc : _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin (n + m))) ⟶
          _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin n)) :=
        e_free.hom ≫ biprod.fst with hpdesc
      have hφπ : φQ ≫ πQ = 0 := by
        rw [hφQ, hπQ, ← Functor.map_comp, ← Functor.map_comp,
          ← Functor.map_comp, cokernel.condition,
          Functor.map_zero (_root_.SheafOfModules.overFunctor.{u} R X) _ _,
          Functor.map_zero (_root_.SheafOfModules.overFunctor (R.over X) U) _ _]
        ext U'
        rfl
      have hfst : biprod.fst ≫ ψQ
          = (biprod.desc utildeQ (-(εQ ≫ φQ))) ≫ πQ := by
        apply IsColimit.hom_ext (BinaryBiproduct.isColimit _ _)
        rintro ⟨_|_⟩
        · change biprod.inl ≫ (biprod.fst ≫ ψQ)
            = biprod.inl ≫ ((biprod.desc utildeQ (-(εQ ≫ φQ))) ≫ πQ)
          simp only [← Category.assoc, biprod.inl_fst, biprod.inl_desc,
            Category.id_comp, hlift]
        · change biprod.inr ≫ (biprod.fst ≫ ψQ)
            = biprod.inr ≫ ((biprod.desc utildeQ (-(εQ ≫ φQ))) ≫ πQ)
          simp only [← Category.assoc, biprod.inr_fst, biprod.inr_desc,
            Limits.zero_comp]
          simp [hφπ]
      have hpu : (Limits.kernel.ι βb ≫ pdesc) ≫ ψQ = 0 := by
        calc (Limits.kernel.ι βb ≫ pdesc) ≫ ψQ
            = (Limits.kernel.ι βb ≫ e_free.hom) ≫ (biprod.fst ≫ ψQ) := by
              rw [hpdesc]; simp only [Category.assoc]
          _ = (Limits.kernel.ι βb ≫ e_free.hom) ≫
              ((biprod.desc utildeQ (-(εQ ≫ φQ))) ≫ πQ) := by rw [hfst]
          _ = ((Limits.kernel.ι βb ≫ e_free.hom) ≫
              (biprod.desc utildeQ (-(εQ ≫ φQ)))) ≫ πQ := by
            exact (Category.assoc _ _ _).symm
          _ = (Limits.kernel.ι βb ≫ βb) ≫ πQ := rfl
          _ = 0 := by rw [Limits.kernel.condition, Limits.zero_comp]
      set u : Limits.kernel βb ⟶ Limits.kernel ψQ :=
        Limits.kernel.lift ψQ (Limits.kernel.ι βb ≫ pdesc) hpu with hu
      -- Kernel preservation for the forgetful presheaf functors, via the
      -- `PreservesKernel` API (the forgetful functors preserve finite limits).
      have fkerIso : ∀ {A B : SheafOfModules.{u} (R.over Z)} (f : A ⟶ B),
          ∃ (e : (Limits.kernel f).val ≅ Limits.kernel f.val),
          e.hom ≫ Limits.kernel.ι _ = (Limits.kernel.ι f).val := by
        intro A B f
        refine ⟨PreservesKernel.iso (SheafOfModules.forget (R.over Z)) f, ?_⟩
        have h := PreservesKernel.iso_inv_ι (SheafOfModules.forget (R.over Z)) f
        have e : (PreservesKernel.iso (SheafOfModules.forget (R.over Z)) f).hom ≫
            Limits.kernel.ι ((SheafOfModules.forget (R.over Z)).map f) =
            (SheafOfModules.forget (R.over Z)).map (Limits.kernel.ι f) := by
          rw [← h, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
        exact e
      have kerIso : ∀ {A B : SheafOfModules.{u} (R.over Z)} (f : A ⟶ B),
          ∃ (e : (PresheafOfModules.toPresheaf (R.over Z).obj).obj (Limits.kernel f).val ≅
            Limits.kernel ((PresheafOfModules.toPresheaf (R.over Z).obj).map f.val)),
          e.hom ≫ Limits.kernel.ι _ = (PresheafOfModules.toPresheaf (R.over Z).obj).map
            (Limits.kernel.ι f).val := by
        intro A B f
        obtain ⟨e1, he1⟩ := fkerIso f
        have h := PreservesKernel.iso_inv_ι
          (PresheafOfModules.toPresheaf (R.over Z).obj) f.val
        have tri : (PreservesKernel.iso
              (PresheafOfModules.toPresheaf (R.over Z).obj) f.val).hom ≫
            Limits.kernel.ι ((PresheafOfModules.toPresheaf (R.over Z).obj).map f.val) =
            (PresheafOfModules.toPresheaf (R.over Z).obj).map
              (Limits.kernel.ι f.val) := by
          rw [← h, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
        refine ⟨(PresheafOfModules.toPresheaf (R.over Z).obj).mapIso e1 ≪≫
          PreservesKernel.iso (PresheafOfModules.toPresheaf (R.over Z).obj) f.val, ?_⟩
        rw [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, tri,
          ← Functor.map_comp, he1]
      -- Exactness shows that this particular cokernel is preserved by the
      -- first restriction, even though that functor need not preserve all
      -- colimits.
      have hPcX : PreservesColimit (parallelPair _φ 0) (_root_.SheafOfModules.overFunctor R X) :=
        preservesCokernel_overFunctor _φ X
      set isoA' : (_root_.SheafOfModules.overFunctor R X).obj (Limits.cokernel _φ) ≅
          Limits.cokernel ((_root_.SheafOfModules.overFunctor R X).map _φ) :=
        PreservesCokernel.iso (_root_.SheafOfModules.overFunctor R X) _φ with hisoA'
      have tA' := PreservesCokernel.π_iso_hom (_root_.SheafOfModules.overFunctor R X) _φ
      -- Only this specific cokernel is needed from the second restriction.
      have hPcU : PreservesColimit
          (parallelPair ((_root_.SheafOfModules.overFunctor R X).map _φ)
              0) (_root_.SheafOfModules.overFunctor (R.over X) U) :=
        preservesCokernel_overFunctor ((_root_.SheafOfModules.overFunctor R X).map _φ) U
      have hPcE : PreservesColimit
          (parallelPair ((_root_.SheafOfModules.overFunctor (R.over X) U).map
              ((_root_.SheafOfModules.overFunctor R X).map _φ)) 0)
          E.inverse := inferInstance
      set isoA : (_root_.SheafOfModules.overFunctor (R.over X) U).obj
          (Limits.cokernel ((_root_.SheafOfModules.overFunctor R X).map _φ)) ≅
          Limits.cokernel ((_root_.SheafOfModules.overFunctor (R.over X) U).map
              ((_root_.SheafOfModules.overFunctor R X).map _φ)) :=
        PreservesCokernel.iso (_root_.SheafOfModules.overFunctor (R.over X) U)
          ((_root_.SheafOfModules.overFunctor R X).map _φ) with hisoA
      set isoB : E.inverse.obj
          (Limits.cokernel ((_root_.SheafOfModules.overFunctor (R.over X) U).map
              ((_root_.SheafOfModules.overFunctor R X).map _φ))) ≅
          Limits.cokernel (E.inverse.map
            ((_root_.SheafOfModules.overFunctor (R.over X) U).map
                ((_root_.SheafOfModules.overFunctor R X).map _φ))) :=
        PreservesCokernel.iso _ _ with hisoB
      set isoC : E.inverse.obj ((_root_.SheafOfModules.overFunctor (R.over X) U).obj
          ((_root_.SheafOfModules.overFunctor R X).obj (Limits.cokernel
              _φ))) ≅ Limits.cokernel φQ :=
        E.inverse.mapIso ((_root_.SheafOfModules.overFunctor (R.over X) U).mapIso isoA') ≪≫
          E.inverse.mapIso isoA ≪≫ isoB with hisoC
      have tA := PreservesCokernel.π_iso_hom (_root_.SheafOfModules.overFunctor (R.over X) U)
        ((_root_.SheafOfModules.overFunctor R X).map _φ)
      have tB := PreservesCokernel.π_iso_hom E.inverse
        ((_root_.SheafOfModules.overFunctor (R.over X) U).map ((_root_.SheafOfModules.overFunctor R
            X).map _φ))
      have tA'U :
          (_root_.SheafOfModules.overFunctor (R.over X) U).map
              ((_root_.SheafOfModules.overFunctor R X).map (Limits.cokernel.π _φ)) ≫
            (_root_.SheafOfModules.overFunctor (R.over X) U).map isoA'.hom =
          (_root_.SheafOfModules.overFunctor (R.over X) U).map
            (Limits.cokernel.π ((_root_.SheafOfModules.overFunctor R X).map _φ)) := by
        rw [← (_root_.SheafOfModules.overFunctor (R.over X) U).map_comp, tA']
      have tA'UE :
          E.inverse.map ((_root_.SheafOfModules.overFunctor (R.over X) U).map
              ((_root_.SheafOfModules.overFunctor R X).map (Limits.cokernel.π _φ))) ≫
            E.inverse.map ((_root_.SheafOfModules.overFunctor (R.over X) U).map isoA'.hom) =
          E.inverse.map ((_root_.SheafOfModules.overFunctor (R.over X) U).map
            (Limits.cokernel.π ((_root_.SheafOfModules.overFunctor R X).map _φ))) := by
        rw [← E.inverse.map_comp, tA'U]
      have tAE :
          E.inverse.map ((_root_.SheafOfModules.overFunctor (R.over X) U).map
              (Limits.cokernel.π ((_root_.SheafOfModules.overFunctor R X).map _φ))) ≫
            (E.inverse.mapIso isoA).hom =
          E.inverse.map (Limits.cokernel.π
            ((_root_.SheafOfModules.overFunctor (R.over X) U).map
                ((_root_.SheafOfModules.overFunctor R X).map _φ))) := by
        rw [Functor.mapIso_hom, ← E.inverse.map_comp, hisoA, tA]
      have tBE :
          E.inverse.map (Limits.cokernel.π
              ((_root_.SheafOfModules.overFunctor (R.over X) U).map
                  ((_root_.SheafOfModules.overFunctor R X).map _φ))) ≫
            isoB.hom = Limits.cokernel.π φQ := by
        change E.inverse.map (Limits.cokernel.π
              ((_root_.SheafOfModules.overFunctor (R.over X) U).map
                  ((_root_.SheafOfModules.overFunctor R X).map _φ))) ≫
            isoB.hom = Limits.cokernel.π
              (E.inverse.map ((_root_.SheafOfModules.overFunctor (R.over X) U).map
                ((_root_.SheafOfModules.overFunctor R X).map _φ)))
        rw [hisoB]
        exact tB
      have htri : E.inverse.map ((_root_.SheafOfModules.overFunctor (R.over X) U).map
          ((_root_.SheafOfModules.overFunctor R X).map
          (Limits.cokernel.π _φ))) ≫ isoC.hom = Limits.cokernel.π φQ := by
        rw [hisoC, Iso.trans_hom, Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_hom]
        simp only [← Category.assoc]
        rw [tA'UE, tAE, tBE]
      -- Local surjectivity of the finite epi and the image factorization.
      have hLSep : Presheaf.IsLocallySurjective (J.over Z)
          ((PresheafOfModules.toPresheaf (R.over Z).obj).map εQ.val) :=
        locallySurjective_of_epi εQ
      have hLSft : Presheaf.IsLocallySurjective (J.over Z)
          ((PresheafOfModules.toPresheaf (R.over Z).obj).map
            (Abelian.factorThruImage φQ).val) := by
        have : Epi (Abelian.factorThruImage φQ) := inferInstance
        exact locallySurjective_of_epi (Abelian.factorThruImage φQ)
      -- The quotient map onto the kernel is an epi.
      have huEpi : Epi u := by
        refine epi_of_locallySurjective u ?_
        constructor
        intro V' x
        obtain ⟨eψ, heψ⟩ := kerIso ψQ
        let x' : ((Limits.kernel ψQ).val).obj (Opposite.op V') := x
        set x₁ := eψ.hom.app (Opposite.op V') x' with hx₁
        set a := (Limits.kernel.ι
          ((PresheafOfModules.toPresheaf (R.over Z).obj).map ψQ.val)).app
            (Opposite.op V') x₁ with ha
        have ha0 : ((PresheafOfModules.toPresheaf (R.over Z).obj).map ψQ.val).app
            (Opposite.op V') a = 0 := by
          rw [ha]
          exact ConcreteCategory.congr_hom
            (congr_app (Limits.kernel.condition
              ((PresheafOfModules.toPresheaf (R.over Z).obj).map ψQ.val))
              (Opposite.op V')) x₁
        obtain ⟨efc, hefc⟩ := fkerIso (Limits.cokernel.π φQ)
        set am : ((_root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin n))).val).obj
            (Opposite.op V') := a with ham
        have ha0m : ψQ.val.app (Opposite.op V') am = 0 := ha0
        let nm : (NQ.val).obj (Opposite.op V') :=
          utildeQ.val.app (Opposite.op V') am
        have hnm : nm = utildeQ.val.app (Opposite.op V') am := rfl
        have hn0 : πQ.val.app (Opposite.op V') nm = 0 := by
          calc πQ.val.app (Opposite.op V') nm
              = πQ.val.app (Opposite.op V') (utildeQ.val.app (Opposite.op V') am) := by
                rw [hnm]
            _ = ψQ.val.app (Opposite.op V') am := by
                change ((utildeQ ≫ πQ).val.app (Opposite.op V')) am = _
                exact ConcreteCategory.congr_hom
                  (congrArg (fun f : _root_.SheafOfModules.free (R :=
                      R.over Z) (ULift.{u} (Fin n)) ⟶ CQ =>
                    f.val.app (Opposite.op V')) hlift) am
            _ = 0 := ha0m
        have hc0 : (Limits.cokernel.π φQ).val.app (Opposite.op V') nm = 0 := by
          have h1 : (Limits.cokernel.π φQ).val.app (Opposite.op V') nm
              = isoC.hom.val.app (Opposite.op V') ((E.inverse.map
                ((_root_.SheafOfModules.overFunctor (R.over X) U).map
                  ((_root_.SheafOfModules.overFunctor R X).map (Limits.cokernel.π _φ)))).val.app
                (Opposite.op V') nm) := by
            change ((Limits.cokernel.π φQ).val.app (Opposite.op V')) nm =
              ((E.inverse.map ((_root_.SheafOfModules.overFunctor (R.over X) U).map
                ((_root_.SheafOfModules.overFunctor R X).map (Limits.cokernel.π
                    _φ))) ≫ isoC.hom).val.app
                  (Opposite.op V')) nm
            exact (ConcreteCategory.congr_hom
              (congrArg (fun f : NQ ⟶ Limits.cokernel φQ =>
                f.val.app (Opposite.op V')) htri) nm).symm
          have h2 : ((E.inverse.map ((_root_.SheafOfModules.overFunctor (R.over X) U).map
              ((_root_.SheafOfModules.overFunctor R X).map
              (Limits.cokernel.π _φ)))).val.app (Opposite.op V') nm)
              = πQ.val.app (Opposite.op V') nm := rfl
          rw [h1, h2, hn0]
          exact map_zero _
        let ev := PresheafOfModules.evaluation (R.over Z).obj (Opposite.op V')
        let f := (Limits.cokernel.π φQ).val
        let ek : ev.obj (Limits.kernel f) ≅ Limits.kernel (ev.map f) :=
          PreservesKernel.iso ev f
        let mk : ↥(Limits.kernel (ev.map f)) :=
          (ModuleCat.kernelIsoKer (ev.map f)).inv ⟨nm, hc0⟩
        let mbar : ((Abelian.image φQ).val).obj (Opposite.op V') :=
          efc.inv.app (Opposite.op V') (ek.inv mk)
        have hmbar0 : (Abelian.image.ι φQ).val.app (Opposite.op V') mbar = nm := by
          change ((Limits.kernel.ι (Limits.cokernel.π φQ)).val.app
            (Opposite.op V')) mbar = nm
          have hefcV := ConcreteCategory.congr_hom
            (congrArg (fun k => k.app (Opposite.op V')) hefc)
          rw [← hefcV mbar]
          change (ev.map (Limits.kernel.ι f))
            (efc.hom.app (Opposite.op V') mbar) = nm
          have hcancel : efc.hom.app (Opposite.op V')
              (efc.inv.app (Opposite.op V') (ek.inv mk)) = ek.inv mk := by
            have h := congrArg (fun k => k.app (Opposite.op V')) efc.inv_hom_id
            exact ConcreteCategory.congr_hom h (ek.inv mk)
          rw [show mbar = efc.inv.app (Opposite.op V') (ek.inv mk) from rfl, hcancel]
          change (ev.map (Limits.kernel.ι f)) (ek.inv mk) = nm
          have hek : ek.inv ≫ ev.map (Limits.kernel.ι f) =
              Limits.kernel.ι (ev.map f) := PreservesKernel.iso_inv_ι ev f
          rw [← ConcreteCategory.comp_apply, hek]
          change (Limits.kernel.ι (ev.map f))
            ((ModuleCat.kernelIsoKer (ev.map f)).inv ⟨nm, hc0⟩) = nm
          rw [← ConcreteCategory.comp_apply,
            ModuleCat.kernelIsoKer_inv_kernel_ι]
          rfl
        -- Cover from the image factorization.
        set S₁ : Sieve V' := Presheaf.imageSieve
          ((PresheafOfModules.toPresheaf (R.over Z).obj).map
            (Abelian.factorThruImage φQ).val) mbar with hS₁
        have hS₁cov : S₁ ∈ (J.over Z) V' :=
          Presheaf.imageSieve_mem (J.over Z)
            ((PresheafOfModules.toPresheaf (R.over Z).obj).map
              (Abelian.factorThruImage φQ).val) mbar
        have chm : ∀ (W₁ : Over Z) (g₁ : W₁ ⟶ V'), S₁.arrows g₁ →
            ∃ m : (MQ.val).obj (Opposite.op W₁),
              ((PresheafOfModules.toPresheaf (R.over Z).obj).map
                (Abelian.factorThruImage φQ).val).app (Opposite.op W₁) m
              = ((PresheafOfModules.toPresheaf (R.over Z).obj).obj
                (Abelian.image φQ).val).map g₁.op mbar := by
          intro W₁ g₁ hg₁
          exact hg₁
        -- Second cover from the finite epi, over chosen preimages.
        have hR₂cov : ∀ (W₁ : Over Z) (g₁ : W₁ ⟶ V') (hg₁ : S₁.arrows g₁),
            Presheaf.imageSieve
              ((PresheafOfModules.toPresheaf (R.over Z).obj).map εQ.val)
              (Classical.choose (chm W₁ g₁ hg₁)) ∈ (J.over Z) W₁ := by
          intro W₁ g₁ hg₁
          exact Presheaf.imageSieve_mem (J.over Z)
            ((PresheafOfModules.toPresheaf (R.over Z).obj).map εQ.val)
            (Classical.choose (chm W₁ g₁ hg₁))
        set Sbind : Sieve V' := Sieve.bind S₁
          (fun W₁ g₁ hg₁ => Presheaf.imageSieve
            ((PresheafOfModules.toPresheaf (R.over Z).obj).map εQ.val)
            (Classical.choose (chm W₁ g₁ hg₁))) with hSbind
        have hSbindcov : Sbind ∈ (J.over Z) V' :=
          (J.over Z).bind_covering hS₁cov (fun W₁ g₁ hg₁ => hR₂cov W₁ g₁ hg₁)
        refine (J.over Z).superset_covering (fun Z' h hh => ?_) hSbindcov
        obtain ⟨W₁, g₂, g₁, hg₁, hg₂, rfl⟩ := hh
        obtain ⟨b, hb⟩ := hg₂
        set m₁ : (MQ.val).obj (Opposite.op W₁) :=
          Classical.choose (chm W₁ g₁ hg₁) with hm₁
        have hm₁spec : ((PresheafOfModules.toPresheaf (R.over Z).obj).map
              (Abelian.factorThruImage φQ).val).app (Opposite.op W₁) m₁
            = ((PresheafOfModules.toPresheaf (R.over Z).obj).obj
              (Abelian.image φQ).val).map g₁.op mbar :=
          Classical.choose_spec (chm W₁ g₁ hg₁)
        have hm₁mod : (Abelian.factorThruImage φQ).val.app (Opposite.op W₁) m₁
            = ((Abelian.image φQ).val).map g₁.op mbar := hm₁spec
        have hεb : εQ.val.app (Opposite.op Z') b
            = (MQ.val).map g₂.op m₁ := hb
        -- `φ(m₁)` is the restriction of `n`.
        have hfacm : (Abelian.image.ι φQ).val.app (Opposite.op W₁)
              ((Abelian.factorThruImage φQ).val.app (Opposite.op W₁) m₁)
            = φQ.val.app (Opposite.op W₁) m₁ := by
          change ((Abelian.factorThruImage φQ ≫ Abelian.image.ι φQ).val.app
            (Opposite.op W₁)) m₁ = _
          rw [Abelian.image.fac φQ]
        have hφm : φQ.val.app (Opposite.op W₁) m₁
            = (NQ.val).map g₁.op nm := by
          rw [← hfacm, hm₁mod, PresheafOfModules.naturality_apply, hmbar0]
        -- Restrictions to the bind arrow.
        let a' : ((_root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin n))).val).obj
            (Opposite.op Z') :=
          ((_root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin n))).val).map (g₂ ≫ g₁).op am
        let n' : (NQ.val).obj (Opposite.op Z') :=
          (NQ.val).map (g₂ ≫ g₁).op nm
        have hutildea' : utildeQ.val.app (Opposite.op Z') a'
            = (NQ.val).map (g₂ ≫ g₁).op nm := by
          dsimp [a']
          rw [PresheafOfModules.naturality_apply, hnm]
        let m₁' : (MQ.val).obj (Opposite.op Z') :=
          (MQ.val).map g₂.op m₁
        have hφm' : φQ.val.app (Opposite.op Z') m₁' = n' := by
          dsimp [m₁', n']
          rw [PresheafOfModules.naturality_apply, hφm]
          exact (PresheafOfModules.map_comp_apply NQ.val g₁.op g₂.op nm).symm
        have hεb' : εQ.val.app (Opposite.op Z') b = m₁' := hεb
        have hutildea'' : utildeQ.val.app (Opposite.op Z') a' = n' := hutildea'
        -- Combine the restricted element and its chosen preimage pointwise.
        let pairEl : (((_root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin n))) ⊞
              _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin m))).val).obj
              (Opposite.op Z') :=
          (biprod.inl (X := _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin n)))
              (Y := _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin m)))).val.app
              (Opposite.op Z') a' +
            (biprod.inr (X := _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin n)))
              (Y := _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin m)))).val.app
              (Opposite.op Z') b
        let vEl : ((_root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin (n + m)))).val).obj
            (Opposite.op Z') := e_free.inv.val.app (Opposite.op Z') pairEl
        have heβ : e_free.inv ≫ βb = biprod.desc utildeQ (-(εQ ≫ φQ)) := by
          rw [hβb, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
        have hleft : (biprod.desc utildeQ (-(εQ ≫ φQ))).val.app
              (Opposite.op Z')
              ((biprod.inl (X := _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin n)))
                (Y := _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin m)))).val.app
                (Opposite.op Z') a') = utildeQ.val.app (Opposite.op Z') a' := by
          change (((biprod.inl : _root_.SheafOfModules.free (R :=
              R.over Z) (ULift.{u} (Fin n)) ⟶ _) ≫
            biprod.desc utildeQ (-(εQ ≫ φQ))).val.app (Opposite.op Z')) a' = _
          rw [biprod.inl_desc]
        have hright : (biprod.desc utildeQ (-(εQ ≫ φQ))).val.app
              (Opposite.op Z')
              ((biprod.inr (X := _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin n)))
                (Y := _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin m)))).val.app
                (Opposite.op Z') b) =
              (-(εQ ≫ φQ)).val.app (Opposite.op Z') b := by
          change (((biprod.inr : _root_.SheafOfModules.free (R :=
              R.over Z) (ULift.{u} (Fin m)) ⟶ _) ≫
            biprod.desc utildeQ (-(εQ ≫ φQ))).val.app (Opposite.op Z')) b = _
          rw [biprod.inr_desc]
        have hβvEl : βb.val.app (Opposite.op Z') vEl = 0 := by
          change βb.val.app (Opposite.op Z')
            (e_free.inv.val.app (Opposite.op Z') pairEl) = 0
          change ((e_free.inv ≫ βb).val.app (Opposite.op Z')) pairEl = 0
          rw [heβ]
          dsimp [pairEl]
          rw [map_add, hleft, hright]
          have hneg : (-(εQ ≫ φQ)).val = -(εQ ≫ φQ).val :=
            Functor.map_neg (SheafOfModules.forget (R.over Z))
          rw [hneg, PresheafOfModules.neg_app]
          change utildeQ.val.app (Opposite.op Z') a' +
            -(φQ.val.app (Opposite.op Z')
              (εQ.val.app (Opposite.op Z') b)) = 0
          rw [hutildea'', hεb', hφm']
          exact add_neg_cancel n'
        -- Lift the pointwise element through the preserved evaluation kernel.
        obtain ⟨efβ, hefβ⟩ := fkerIso βb
        let evβ := PresheafOfModules.evaluation (R.over Z).obj (Opposite.op Z')
        let fβ := βb.val
        let ekβ : evβ.obj (Limits.kernel fβ) ≅ Limits.kernel (evβ.map fβ) :=
          PreservesKernel.iso evβ fβ
        let mkβ : ↥(Limits.kernel (evβ.map fβ)) :=
          (ModuleCat.kernelIsoKer (evβ.map fβ)).inv ⟨vEl, hβvEl⟩
        let wEl : ((Limits.kernel βb).val).obj (Opposite.op Z') :=
          efβ.inv.app (Opposite.op Z') (ekβ.inv mkβ)
        have hwEl : (Limits.kernel.ι βb).val.app (Opposite.op Z') wEl = vEl := by
          have hefβV := ConcreteCategory.congr_hom
            (congrArg (fun k => k.app (Opposite.op Z')) hefβ)
          rw [← hefβV wEl]
          change (evβ.map (Limits.kernel.ι fβ))
            (efβ.hom.app (Opposite.op Z') wEl) = vEl
          have hcancel : efβ.hom.app (Opposite.op Z')
              (efβ.inv.app (Opposite.op Z') (ekβ.inv mkβ)) = ekβ.inv mkβ := by
            have h := congrArg (fun k => k.app (Opposite.op Z')) efβ.inv_hom_id
            exact ConcreteCategory.congr_hom h (ekβ.inv mkβ)
          rw [show wEl = efβ.inv.app (Opposite.op Z') (ekβ.inv mkβ) from rfl,
            hcancel]
          change (evβ.map (Limits.kernel.ι fβ)) (ekβ.inv mkβ) = vEl
          have hekβ : ekβ.inv ≫ evβ.map (Limits.kernel.ι fβ) =
              Limits.kernel.ι (evβ.map fβ) := PreservesKernel.iso_inv_ι evβ fβ
          rw [← ConcreteCategory.comp_apply, hekβ]
          change (Limits.kernel.ι (evβ.map fβ))
            ((ModuleCat.kernelIsoKer (evβ.map fβ)).inv ⟨vEl, hβvEl⟩) = vEl
          rw [← ConcreteCategory.comp_apply,
            ModuleCat.kernelIsoKer_inv_kernel_ι]
          rfl
        have huι : u ≫ Limits.kernel.ι ψQ
            = Limits.kernel.ι βb ≫ pdesc := by
          rw [hu]; exact Limits.kernel.lift_ι _ _ _
        have h1 : (Limits.kernel.ι ψQ).val.app (Opposite.op Z')
              (u.val.app (Opposite.op Z') wEl)
            = pdesc.val.app (Opposite.op Z')
              ((Limits.kernel.ι βb).val.app (Opposite.op Z') wEl) := by
          have hval : (u ≫ Limits.kernel.ι ψQ).val
              = (Limits.kernel.ι βb ≫ pdesc).val := by rw [huι]
          calc (Limits.kernel.ι ψQ).val.app _ (u.val.app _ wEl)
              = ((u ≫ Limits.kernel.ι ψQ).val).app _ wEl := by
                exact (CategoryTheory.comp_apply _ _ _).symm
            _ = (((Limits.kernel.ι βb ≫ pdesc).val).app _ wEl) := by rw [hval]
            _ = pdesc.val.app _ ((Limits.kernel.ι βb).val.app _ wEl) := by
                exact CategoryTheory.comp_apply _ _ _
        have heinvEl : e_free.hom.val.app (Opposite.op Z')
              (e_free.inv.val.app (Opposite.op Z') pairEl) = pairEl := by
          have h := congrArg (fun k => k.val.app (Opposite.op Z')) e_free.inv_hom_id
          exact ConcreteCategory.congr_hom h pairEl
        have hfstLeft : (biprod.fst (X := _root_.SheafOfModules.free (R :=
            R.over Z) (ULift.{u} (Fin n)))
              (Y := _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin m)))).val.app
              (Opposite.op Z')
              ((biprod.inl (X := _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin n)))
                (Y := _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin m)))).val.app
                (Opposite.op Z') a') = a' := by
          change ((((biprod.inl : _root_.SheafOfModules.free (R :=
              R.over Z) (ULift.{u} (Fin n)) ⟶ _) ≫
            biprod.fst).val.app (Opposite.op Z')) a') = a'
          rw [biprod.inl_fst]
          rfl
        have hfstRight : (biprod.fst (X := _root_.SheafOfModules.free (R :=
            R.over Z) (ULift.{u} (Fin n)))
              (Y := _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin m)))).val.app
              (Opposite.op Z')
              ((biprod.inr (X := _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin n)))
                (Y := _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin m)))).val.app
                (Opposite.op Z') b) = 0 := by
          change ((((biprod.inr : _root_.SheafOfModules.free (R :=
              R.over Z) (ULift.{u} (Fin m)) ⟶ _) ≫
            biprod.fst).val.app (Opposite.op Z')) b) = 0
          rw [biprod.inr_fst]
          rfl
        have h3 : pdesc.val.app (Opposite.op Z') vEl = a' := by
          change pdesc.val.app (Opposite.op Z')
            (e_free.inv.val.app (Opposite.op Z') pairEl) = a'
          rw [hpdesc]
          change (biprod.fst (X := _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin n)))
            (Y := _root_.SheafOfModules.free (R := R.over Z) (ULift.{u} (Fin m)))).val.app
            (Opposite.op Z')
            (e_free.hom.val.app (Opposite.op Z')
              (e_free.inv.val.app (Opposite.op Z') pairEl)) = a'
          rw [heinvEl]
          dsimp [pairEl]
          rw [map_add, hfstLeft, hfstRight, add_zero]
        have eL : (Limits.kernel.ι ψQ).val.app (Opposite.op Z')
              (u.val.app (Opposite.op Z') wEl) = a' := by
          rw [h1, hwEl]
          exact h3
        have xfac : (Limits.kernel.ι ψQ).val.app (Opposite.op V') x' = am := by
          have heψV := ConcreteCategory.congr_hom
            (congrArg (fun k => k.app (Opposite.op V')) heψ)
          change ((PresheafOfModules.toPresheaf (R.over Z).obj).map
            (Limits.kernel.ι ψQ).val).app (Opposite.op V') x' = am
          rw [← heψV x']
          exact (congrArg (fun y => (Limits.kernel.ι
            ((PresheafOfModules.toPresheaf (R.over Z).obj).map ψQ.val)).app
              (Opposite.op V') y) hx₁.symm).trans ha.symm
        have eR : (Limits.kernel.ι ψQ).val.app (Opposite.op Z')
              (((Limits.kernel ψQ).val).map (g₂ ≫ g₁).op x') = a' := by
          rw [PresheafOfModules.naturality_apply
            (Limits.kernel.ι ψQ).val (g₂ ≫ g₁).op x', xfac]
        have hfin : u.val.app (Opposite.op Z') wEl
            = ((Limits.kernel ψQ).val).map (g₂ ≫ g₁).op x' := by
          have hκι : Mono (Limits.kernel.ι ψQ).val := by
            change Mono ((SheafOfModules.forget (R.over Z)).map
              (Limits.kernel.ι ψQ))
            infer_instance
          apply PresheafOfModules.injective_of_mono (Limits.kernel.ι ψQ).val
            (Opposite.op Z')
          exact eL.trans eR.symm
        exact ⟨wEl, hfin⟩
      -- Finite type of the kernel over the base, and its local data.
      have iso1 : Limits.kernel βb ≅ Limits.kernel βcoh :=
        Limits.kernel.mapIso (f := βb) βcoh (Iso.refl _) (dC N).symm
          (show βb ≫ (dC N).symm.hom = (Iso.refl _).hom ≫ βcoh from by
            rw [hβcoh]; simp)
      have hKb : _root_.SheafOfModules.IsFiniteType (R := R.over Z) (Limits.kernel βb) := by
        let e : Limits.kernel βcoh ≅ Limits.kernel βb := iso1.symm
        have he : IsIso e.hom := Iso.isIso_hom e
        have : Epi e.hom := inferInstance
        exact isFiniteType_of_epi'
          (S := R.over Z) (M := Limits.kernel βcoh)
          (N := Limits.kernel βb) e.hom
      have huEpi' : Epi u := huEpi
      have hKQ : _root_.SheafOfModules.IsFiniteType (R := R.over Z) (Limits.kernel ψQ) :=
        isFiniteType_of_epi'
          (S := R.over Z) (M := Limits.kernel βb)
          (N := Limits.kernel ψQ) u
      obtain ⟨δ, hδ⟩ :=
        _root_.SheafOfModules.IsFiniteType.exists_localGeneratorsData (Limits.kernel ψQ)
      -- Transfer the cover to the double-slice side.
      set backward : Over U.left ⥤ Over U :=
        (Over.iteratedSliceEquiv U).symm.functor with hbackward
      set forward : Over U ⥤ Over U.left :=
        (Over.iteratedSliceEquiv U).functor with hforward
      set V : δ.I → Over U := fun l => backward.obj (δ.X l) with hV
      have hVcov : ((J.over X).over U).CoversTop V :=
        GrothendieckTopology.CoversTop.iteratedSliceEquiv_inverse U δ.coversTop
      -- Global comparison iso onto the kernel over `U`.
      have isoK0 : Limits.kernel ψQ ≅ Limits.kernel (E.inverse.map ψS) :=
        Limits.kernel.mapIso (f := ψQ) (E.inverse.map ψS) dF (Iso.refl _)
          (show ψQ ≫ (Iso.refl _).hom = dF.hom ≫ E.inverse.map ψS from by
            rw [hψQ]; simp)
      let eKU : (_root_.SheafOfModules.overFunctor (R.over X) U).obj (Limits.kernel ψ) ≅
          Limits.kernel ψS :=
        PreservesKernel.iso (_root_.SheafOfModules.overFunctor (R.over X) U) ψ
      have eBU : E.functor.obj (Limits.kernel ψQ) ≅ (Limits.kernel ψ).over U :=
        E.functor.mapIso isoK0 ≪≫
          PreservesKernel.iso E.functor (E.inverse.map ψS) ≪≫
          Limits.kernel.mapIso (f := E.functor.map (E.inverse.map ψS)) ψS
            (E.counitIso.app FS) (E.counitIso.app CS)
            (E.counitIso.hom.naturality ψS) ≪≫
          eKU.symm
      -- Un-sliced cover-preservation facts for the slice recipe.  State the
      -- canonical instances before bridging the local alias `Z = U.left`;
      -- dependent topology arguments cannot be rewritten with `rw hZ`.
      have hcontB0 : (Over.iteratedSliceEquiv U).inverse.IsContinuous
          (J.over U.left) ((J.over X).over U) := by
        infer_instance
      have hcontB : backward.IsContinuous (J.over Z) ((J.over X).over U) := by
        rw [hbackward]
        change (Over.iteratedSliceEquiv U).inverse.IsContinuous
          (J.over U.left) ((J.over X).over U)
        exact hcontB0
      have hcpU : CoverPreserving (J.over Z) ((J.over X).over U) backward :=
        CoverPreserving.of_isContinuous _ _ _
      have hcontFwd0 : (Over.iteratedSliceEquiv U).functor.IsContinuous
          ((J.over X).over U) (J.over U.left) := by
        infer_instance
      have hcontFwd : forward.IsContinuous ((J.over X).over U) (J.over Z) := by
        rw [hforward]
        change (Over.iteratedSliceEquiv U).functor.IsContinuous
          ((J.over X).over U) (J.over U.left)
        exact hcontFwd0
      have hcpUF : CoverPreserving ((J.over X).over U) (J.over Z) forward :=
        CoverPreserving.of_isContinuous _ _ _
      -- Per-piece data over the transferred cover.
      have pieceU : ∀ l : δ.I,
          ∃ (G : (((Limits.kernel ψ).over U).over (V l)).GeneratingSections),
            G.IsFiniteType := by
        intro l
        have hcpF : CoverPreserving ((J.over U.left).over (δ.X l))
            (((J.over X).over U).over (V l))
            (Over.postEquiv (Over.iteratedSliceEquiv U).symm
              (X := δ.X l)).functor :=
          CoverPreserving.overPost _ hcpU
        have hcontF : (Over.postEquiv (Over.iteratedSliceEquiv U).symm
            (X := δ.X l)).functor.IsContinuous ((J.over U.left).over (δ.X l))
            (((J.over X).over U).over (V l)) :=
          Functor.isContinuous_of_coverPreserving
            (Functor.IsCoverDense.compatiblePreserving _ _) hcpF
        have hcpPostF : CoverPreserving ((((J.over X).over U).over (V l)))
            ((J.over U.left).over (forward.obj (V l)))
            (Over.post forward) :=
          CoverPreserving.overPost _ hcpUF
        have hcpMap : CoverPreserving
            ((J.over U.left).over (forward.obj (V l)))
            ((J.over U.left).over (δ.X l))
            (Over.map ((Over.iteratedSliceEquiv U).symm.unitIso.inv.app (δ.X l))) :=
          CoverPreserving.of_isContinuous _ _ _
        have hcpUI : CoverPreserving ((((J.over X).over U).over (V l)))
            ((J.over U.left).over (δ.X l))
            (Over.postEquiv (Over.iteratedSliceEquiv U).symm
              (X := δ.X l)).inverse :=
          CoverPreserving.comp _ _ hcpPostF hcpMap
        have hcontI : (Over.postEquiv (Over.iteratedSliceEquiv U).symm
            (X := δ.X l)).inverse.IsContinuous ((((J.over X).over U).over (V l)))
            ((J.over U.left).over (δ.X l)) :=
          Functor.isContinuous_of_coverPreserving
            (Functor.IsCoverDense.compatiblePreserving _ _) hcpUI
        set Eₗ : SheafOfModules.{u} ((R.over U.left).over (δ.X l)) ≌
            SheafOfModules.{u} (((R.over X).over U).over (V l)) :=
          (_root_.SheafOfModules.pushforwardPushforwardEquivalence
            (Over.postEquiv (Over.iteratedSliceEquiv U).symm (X := δ.X l))
            (S := ((R.over U.left).over (δ.X l)))
            (R := (((R.over X).over U).over (V l)))
            (𝟙 _) (𝟙 _) (by ext : 2; exact R.1.map_id _)
            (by ext : 2; exact R.1.map_id _)).symm with hEₗ
        have hEcolₗ : PreservesColimitsOfSize.{u, u} Eₗ.functor := inferInstance
        have hDlFT : ((δ.generators l)).IsFiniteType := hδ.isFiniteType l
        have Cl : Eₗ.functor.obj (((Limits.kernel ψQ).over (δ.X l))) ≅
            ((E.functor.obj (Limits.kernel ψQ)).over (V l)) :=
          Iso.refl _
        have eBl : Eₗ.functor.obj (((Limits.kernel ψQ).over (δ.X l))) ≅
            (((Limits.kernel ψ).over U).over (V l)) :=
          Cl ≪≫ (_root_.SheafOfModules.overFunctor (((R.over X).over U)) (V l)).mapIso eBU
        let Gₗ := ((δ.generators l).mapEquivalenceWeak Eₗ (Iso.refl _)).ofEpi eBl.hom
        refine ⟨Gₗ, ?_⟩
        exact ⟨hDlFT.finite⟩
      -- Local data for the kernel over `U`.
      choose genU hgenU using pieceU
      exact ⟨⟨δ.I, V, hVcov, genU⟩,
        ⟨fun l => ⟨(hgenU l).finite⟩⟩⟩
    choose genD hgenD using piece
    -- Outer bind over `Y0`.
    have hcoverOv := hcover.over (I' := fun i0 => (genD i0).I)
      (Y := fun i0 l => (genD i0).X l) (fun i0 => (genD i0).coversTop)
    have hcover1 : (J.over X).CoversTop
        (fun j : (i0 : I0) × (genD i0).I =>
          (((genD j.1).X j.2).left : Over X)) :=
      hcoverOv
    have piece1 : ∀ j : (i0 : I0) × (genD i0).I,
        ∃ (G : (((Limits.kernel ψ).over
          (((genD j.1).X j.2).left : Over X)).GeneratingSections)),
          G.IsFiniteType := by
      rintro ⟨i0, l⟩
      set W : Over (Y0 i0) := (genD i0).X l with hW
      set E'' : SheafOfModules.{u} ((((R.over X).over (Y0 i0)).over W)) ≌
          SheafOfModules.{u} ((R.over X).over (W.left)) :=
        (_root_.SheafOfModules.overOverEquivalence (S := R.over X) W).symm with hE''
      have hEcol'' : PreservesColimitsOfSize.{u, u} E''.functor := inferInstance
      have hGlFT : (((genD i0).generators l)).IsFiniteType :=
        (hgenD i0).isFiniteType l
      have C'' : E''.functor.obj ((((Limits.kernel ψ).over (Y0 i0)).over W)) ≅
          ((Limits.kernel ψ).over (W.left)) :=
        Iso.refl _
      exact ⟨(((genD i0).generators l).map E''.functor (Iso.refl _)).ofEpi
          C''.hom,
        ⟨(inferInstance : ((genD i0).generators l).IsFiniteType).finite⟩⟩
    choose gen1 hgen1 using piece1
    exact ⟨((⟨(i0 : I0) × (genD i0).I, (fun j : (i0 : I0) × (genD i0).I =>
        (((genD j.1).X j.2).left : Over X)), hcover1, gen1⟩ :
      (Limits.kernel ψ).LocalGeneratorsData)).shrink,
      ⟨fun s ↦ hgen1 s.2.choose⟩⟩

-- Extensions of finite-type sheaves are finite type, with no binary-product
-- hypothesis (Stacks 01BY, extension part, finite-type half). The statement
-- is proved via the sheafify tower rather than limit data.
omit [∀ (X : C) (Y : Over X),
    HasWeakSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X),
    ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X) (Z : Over Y),
    HasWeakSheafify (((J.over X).over Y).over Z) AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X) (Z : Over Y),
    (((J.over X).over Y).over Z).WEqualsLocallyBijective AddCommGrpCat.{u}] in
theorem isFiniteType_extension' {S : ShortComplex (SheafOfModules.{u} R)}
    (hS : S.ShortExact) [_root_.SheafOfModules.IsFiniteType (R := R) S.X₁]
    [_root_.SheafOfModules.IsFiniteType (R := R) S.X₃] :
    _root_.SheafOfModules.IsFiniteType (R := R) S.X₂ := by
  classical
  have := hS.mono_f
  have := hS.epi_g
  obtain ⟨σ1, hσ1⟩ := _root_.SheafOfModules.IsFiniteType.exists_localGeneratorsData S.X₁
  obtain ⟨σ3, hσ3⟩ := _root_.SheafOfModules.IsFiniteType.exists_localGeneratorsData S.X₃
  have hfin3 : ∀ j : σ3.I, ∃ n : ℕ, Nonempty (Fin n ≃ (σ3.generators j).I) := by
    intro j
    have := hσ3.isFiniteType j
    obtain ⟨m, ⟨ei⟩⟩ := Finite.exists_equiv_fin (α := (σ3.generators j).I)
    exact ⟨m, ⟨ei.symm⟩⟩
  choose n eNe using hfin3
  have e : ∀ j, Fin (n j) ≃ (σ3.generators j).I :=
    fun j => Classical.choice (eNe j)
  set I0 : Type _ :=
    Σ (U : C) (i : σ1.I) (j : σ3.I), (U ⟶ σ1.X i) × (U ⟶ σ3.X j)
  set Y0 : I0 → C := fun p => p.1
  have hbase : J.CoversTop Y0 := by
    intro W
    apply J.superset_covering
      (S := Sieve.ofObjects σ1.X W ⊓ Sieve.ofObjects σ3.X W) _
      (J.intersection_covering (σ1.coversTop W) (σ3.coversTop W))
    intro U f hf
    rcases hf with ⟨hf1, hf3⟩
    rw [Sieve.mem_ofObjects_iff] at hf1 hf3 ⊢
    obtain ⟨i, ⟨a1⟩⟩ := hf1
    obtain ⟨j, ⟨a3⟩⟩ := hf3
    exact ⟨⟨U, i, j, (a1, a3)⟩, ⟨𝟙 U⟩⟩
  have hLS : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map (S.g).val) :=
    locallySurjective_of_epi S.g
  -- Sections over each common-cover object from the quotient generators.
  set xk : ∀ (p : I0) (k : (σ3.generators p.2.2.1).I),
      (((PresheafOfModules.toPresheaf R.obj).obj (S.X₃.val)).obj
        (Opposite.op (Y0 p))) :=
    fun p k => ((σ3.generators p.2.2.1).s k).eval
      (Opposite.op (Over.mk p.2.2.2.2)) with hxk_def
  -- Combined sieves over each common-cover object.
  set Tp : ∀ p : I0, Sieve (Y0 p) := fun p =>
    Finset.univ.inf (fun a : Fin (n p.2.2.1) =>
      Presheaf.imageSieve ((PresheafOfModules.toPresheaf R.obj).map (S.g).val)
        (xk p (e p.2.2.1 a))) with hTp_eq
  have hTp : ∀ p, Tp p ∈ J (Y0 p) := fun p =>
    GrothendieckTopology.finsetInf_mem
      (fun a : Fin (n p.2.2.1) => Presheaf.imageSieve
        ((PresheafOfModules.toPresheaf R.obj).map (S.g).val)
          (xk p (e p.2.2.1 a)))
      (fun a => Presheaf.imageSieve_mem J
        ((PresheafOfModules.toPresheaf R.obj).map (S.g).val)
          (xk p (e p.2.2.1 a)))
  -- Refined cover.
  set L : Type _ :=
    Σ (p : I0) (V : C) (h : V ⟶ Y0 p), PLift ((Tp p).arrows h) with hL
  set WL : L → C := fun l => l.2.1 with hWL
  have hWLcov : J.CoversTop WL := by
    intro T0
    apply J.transitive (hbase T0)
    intro Y f hf
    rw [Sieve.mem_ofObjects_iff] at hf
    obtain ⟨p, ⟨g⟩⟩ := hf
    rw [Sieve.pullback_ofObjects]
    apply J.superset_covering (S := (Tp p).pullback g) _
      (J.pullback_stable g (hTp p))
    intro V b hb
    rw [Sieve.mem_ofObjects_iff]
    exact ⟨⟨p, V, b ≫ g, PLift.up hb⟩, ⟨𝟙 V⟩⟩
  -- Local generators over each refined object.
  have piece : ∀ l : L, ∃ (g : (S.X₂.over (WL l)).GeneratingSections),
      g.IsFiniteType := by
    rintro ⟨⟨U, i, j, ⟨a1, a3⟩⟩, V, h, hmem⟩
    have h1fin : ((σ1.generators i).IsFiniteType) := hσ1.isFiniteType i
    have h3fin : ((σ3.generators j).IsFiniteType) := hσ3.isFiniteType j
    set q1 : V ⟶ σ1.X i := h ≫ a1 with hq1
    set q2 : V ⟶ σ3.X j := h ≫ a3 with hq2
    set gen1V : (S.X₁.over V).GeneratingSections :=
      ((σ1.generators i).mapFinite q1
        (locallySurjective_of_epi (σ1.generators i).π)).ofEpi
          ((_root_.SheafOfModules.overFunctorMap R q1).app S.X₁).hom with hgen1V
    set gen3V : (S.X₃.over V).GeneratingSections :=
      ((σ3.generators j).mapFinite q2
        (locallySurjective_of_epi (σ3.generators j).π)).ofEpi
          ((_root_.SheafOfModules.overFunctorMap R q2).app S.X₃).hom with hgen3V
    -- Local preservation instances at module universe `u`: the statement's
    -- hypotheses quantify `overFunctor` at an unbound universe, so they cannot
    -- be instantiated here; infer what is needed at `.{u}` from the shared
    -- instances instead (cf. `PreservesKernel.iso` at `overFunctor`).
    have hzeroV : (_root_.SheafOfModules.overFunctor.{u} R V).PreservesZeroMorphisms :=
      inferInstance
    have hlimV : PreservesFiniteLimits (_root_.SheafOfModules.overFunctor.{u} R V) := by
      constructor
      intro Jcat _ _
      constructor
      intro K
      have hcomp : PreservesLimit K
          (_root_.SheafOfModules.overFunctor.{u} R V ⋙ SheafOfModules.forget (R.over V)) := by
        constructor
        intro c hc
        refine ⟨PresheafOfModules.evaluationJointlyReflectsLimits
          (F := K ⋙ _root_.SheafOfModules.overFunctor.{u} R V ⋙ SheafOfModules.forget (R.over V))
          (((_root_.SheafOfModules.overFunctor.{u} R V ⋙ SheafOfModules.forget (R.over V)).mapCone
              c))
          (fun U' => ?_)⟩
        change IsLimit ((SheafOfModules.forget R ⋙
          PresheafOfModules.evaluation R.obj ((Over.forget V).op.obj U') ⋙
            ModuleCat.restrictScalars (RingHom.id _)).mapCone c)
        exact isLimitOfPreserves _ hc
      have hrefl : ReflectsLimit (K ⋙ _root_.SheafOfModules.overFunctor.{u} R V)
          (SheafOfModules.forget (R.over V)) := inferInstance
      exact preservesLimit_of_reflects_of_preserves
        (_root_.SheafOfModules.overFunctor.{u} R V) (SheafOfModules.forget (R.over V))
    let F := _root_.SheafOfModules.overFunctor.{u} R V
    have hepiF : F.PreservesEpimorphisms := ⟨by
      intro A B f hf
      exact epi_of_locallySurjective _
        (locallySurjective_over f (locallySurjective_of_epi f) V)⟩
    have hkerF : ∀ {A B : SheafOfModules.{u} R} (f : A ⟶ B),
        PreservesLimit (parallelPair f 0) F := by
      intro A B f
      infer_instance
    have hhomF : F.PreservesHomology :=
      CategoryTheory.Functor.preservesHomology_of_preservesEpis_and_kernels F
    have hSE : (S.map F).ShortExact := hS.map F
    have := hSE.mono_f
    have := hSE.epi_g
    -- Lifts of the quotient generators.
    have hk : ∀ k : (σ3.generators j).I,
        (Presheaf.imageSieve ((PresheafOfModules.toPresheaf R.obj).map (S.g).val)
          (xk ⟨U, i, j, (a1, a3)⟩ k)).arrows h := by
      intro k
      have hmem' := Sieve.finsetInf_arrows
        (fun a => Presheaf.imageSieve _ (xk ⟨U, i, j, (a1, a3)⟩ (e j a))) h hmem.down
        ((e j).symm k)
      rwa [Equiv.apply_symm_apply] at hmem'
    choose t ht using hk
    let liftsec : ∀ k : (σ3.generators j).I, (S.X₂.over V).sections :=
      fun k => PresheafOfModules.sectionsMk
        (fun U' => (S.X₂.val).map (U'.unop.hom).op (t k)) (fun U1 U2 f => by
        dsimp only
        have tri : U2.unop.hom
            = (Over.forget V).map f.unop ≫ U1.unop.hom := (Over.w f.unop).symm
        have key : ((_root_.SheafOfModules.overFunctor.{u} R V).obj S.X₂).val.map f
            = (S.X₂.val).map ((Over.forget V).map f.unop).op := rfl
        change ((_root_.SheafOfModules.overFunctor.{u} R V).obj S.X₂).val.map f
            ((S.X₂.val).map (U1.unop.hom).op (t k)) = _
        rw [key, tri]
        exact (PresheafOfModules.map_comp_apply (M := S.X₂.val)
          (i := (U1.unop.hom).op) (j := ((Over.forget V).map f.unop).op)
          (t k)).symm)
    have liftsec_eval : ∀ k (U' : (Over V)ᵒᵖ),
        (liftsec k).eval U' = (S.X₂.val).map (U'.unop.hom).op (t k) :=
      fun k U' => rfl
    set uLift : SheafOfModules.free (R := R.over V) (σ3.generators j).I ⟶
        S.X₂.over V := (S.X₂.over V).freeHomEquiv.symm liftsec with huLift
    -- The lift equation.
    have sm_eval : ∀ {M N : SheafOfModules.{u} (R.over V)}
        (f : M ⟶ N) (s : M.sections) (X),
        (SheafOfModules.sectionsMap f s).eval X = f.val.app X (s.eval X) :=
      fun f s X => rfl
    have heval : ∀ (k : (σ3.generators j).I) (U' : (Over V)ᵒᵖ),
        (SheafOfModules.sectionsMap ((_root_.SheafOfModules.overFunctor.{u} R V).map S.g)
          (liftsec k)).eval U' = (gen3V.s k).eval U' := by
      intro k U'
      have hLHS : (SheafOfModules.sectionsMap ((_root_.SheafOfModules.overFunctor.{u} R V).map S.g)
            (liftsec k)).eval U'
          = (S.X₃.val).map (U'.unop.hom ≫ h).op (xk ⟨U, i, j, (a1, a3)⟩ k) := by
        rw [sm_eval, liftsec_eval]
        have eapp : (((_root_.SheafOfModules.overFunctor.{u} R V).map S.g).val.app U'
            ((S.X₂.val).map (U'.unop.hom).op (t k)))
            = (S.g).val.app (Opposite.op U'.unop.left)
              ((S.X₂.val).map (U'.unop.hom).op (t k)) := by

          rfl
        rw [eapp]
        have ht' : (S.g).val.app (Opposite.op V) (t k)
            = (S.X₃.val).map h.op (xk ⟨U, i, j, (a1, a3)⟩ k) := ht k
        refine (PresheafOfModules.naturality_apply (S.g).val
          (U'.unop.hom).op (t k)).trans ?_
        rw [ht']
        refine (PresheafOfModules.map_comp_apply (M := S.X₃.val)
          (i := h.op) (j := (U'.unop.hom).op) (xk ⟨U, i, j, (a1, a3)⟩ k)).symm.trans ?_
        congr 1
      have hIdx : gen3V.I = (σ3.generators j).I := rfl
      have hRHS : (gen3V.s k).eval U'
          = (S.X₃.val).map (U'.unop.hom ≫ h).op (xk ⟨U, i, j, (a1, a3)⟩ k) := by
        change (((((σ3.generators j).mapFinite q2
          (locallySurjective_of_epi (σ3.generators j).π)).ofEpi
          ((_root_.SheafOfModules.overFunctorMap R q2).app S.X₃).hom).s k)).eval U' = _
        rw [transported_section_eval_mapFinite _ q2 k U']
        have hproof : (U'.unop.hom ≫ h) ≫ a3
            = U'.unop.hom ≫ q2 := by
          rw [hq2, Category.assoc]
        have hcomp : ((σ3.generators j).s k).eval
              (Opposite.op (Over.mk (U'.unop.hom ≫ q2)))
            = (S.X₃.val).map (U'.unop.hom ≫ h).op (xk ⟨U, i, j, (a1, a3)⟩ k) := by
          have hpr := PresheafOfModules.sections_property
            ((σ3.generators j).s k)
            ((Over.homMk (U'.unop.hom ≫ h) hproof :
              Over.mk (U'.unop.hom ≫ q2) ⟶
              Over.mk a3).op)
          exact hpr.symm
        exact hcomp
      rw [hLHS, hRHS]
    have hlift : uLift ≫ (_root_.SheafOfModules.overFunctor R V).map S.g = gen3V.π := by
      apply (S.X₃.over V).freeHomEquiv.injective
      funext k
      have eUtil : (S.X₂.over V).freeHomEquiv uLift k = liftsec k := by
        rw [huLift]
        exact congrFun ((S.X₂.over V).freeHomEquiv.apply_symm_apply _) k
      have eR : (S.X₃.over V).freeHomEquiv gen3V.π k = gen3V.s k := by
        exact congrFun ((S.X₃.over V).freeHomEquiv.apply_symm_apply _) k
      rw [_root_.SheafOfModules.freeHomEquiv_comp_apply, eUtil]
      apply PresheafOfModules.sections_ext
      intro U'
      exact (heval k U').trans (congrArg (fun s => s.eval U') eR).symm
    -- The combined map is epi.
    set d : SheafOfModules.free (R := R.over V) ((σ1.generators i).I) ⨿
        SheafOfModules.free (σ3.generators j).I ⟶ S.X₂.over V :=
      coprod.desc (gen1V.π ≫ (_root_.SheafOfModules.overFunctor R V).map S.f) uLift with hd_eq
    have hdEpi : Epi d := by
      have hcond : d ≫ Limits.cokernel.π d = 0 := Limits.cokernel.condition d
      have hdesc : coprod.inl ≫ d
          = gen1V.π ≫ (_root_.SheafOfModules.overFunctor R V).map S.f := by
        rw [hd_eq]
        exact coprod.inl_desc _ _
      have hinr : coprod.inr ≫ d = uLift := by
        rw [hd_eq]
        exact coprod.inr_desc _ _
      have hmapf : (S.map (_root_.SheafOfModules.overFunctor R
          V)).f = (_root_.SheafOfModules.overFunctor R V).map S.f := rfl
      have hfq : (S.map (_root_.SheafOfModules.overFunctor R V)).f ≫ Limits.cokernel.π d = 0 := by
        apply (cancel_epi gen1V.π).mp
        exact (congrArg (gen1V.π ≫ ·)
          (congrArg (· ≫ Limits.cokernel.π d) hmapf)).trans
          (((Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ Limits.cokernel.π d) hdesc.symm)).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (coprod.inl ≫ ·) hcond).trans
              (comp_zero.trans comp_zero.symm))))
      obtain ⟨δ, hδ⟩ := hSE.exact.desc' (Limits.cokernel.π d) hfq
      have hmapg : (S.map (_root_.SheafOfModules.overFunctor R
          V)).g = (_root_.SheafOfModules.overFunctor R V).map S.g := rfl
      rw [hmapg] at hδ
      have hδ0 : δ = 0 := by
        apply (cancel_epi gen3V.π).mp
        exact (congrArg (· ≫ δ) hlift.symm).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (uLift ≫ ·) hδ).trans
              ((congrArg (· ≫ Limits.cokernel.π d) hinr.symm).trans
                ((Category.assoc _ _ _).trans
                  ((congrArg (coprod.inr ≫ ·) hcond).trans
                    (comp_zero.trans comp_zero.symm))))))
      have hq0 : Limits.cokernel.π d = 0 :=
        hδ.symm.trans
          ((congrArg ((_root_.SheafOfModules.overFunctor R V).map S.g ≫ ·) hδ0).trans comp_zero)
      exact Abelian.epi_of_cokernel_π_eq_zero d hq0
    have hw2 : Epi ((SheafOfModules.freeSumIso (R := R.over V)
        ((σ1.generators i).I) ((σ3.generators j).I)).inv ≫ d) :=
      epi_comp _ _
    refine ⟨⟨_, (S.X₂.over V).freeHomEquiv
      ((SheafOfModules.freeSumIso (R := R.over V) _ _).inv ≫ d), ?_⟩, ?_⟩
    · rw [Equiv.symm_apply_apply]
      exact hw2
    · let : Fintype (σ1.generators i).I := Fintype.ofFinite _
      let : Fintype (σ3.generators j).I := Fintype.ofFinite _
      exact ⟨Finite.of_fintype ((σ1.generators i).I ⊕ (σ3.generators j).I)⟩
  -- The refined index `L` lives in `Type (max v₁ u)` since it packages arrows;
  -- shrink back into the site universe `u` via
  -- `SheafOfModules.LocalGeneratorsData.shrink` (Mathlib `Sheaf/Generators`).
  refine ⟨(⟨L, WL, hWLcov, fun l => (piece l).choose⟩ :
    S.X₂.LocalGeneratorsData).shrink,
    _root_.SheafOfModules.LocalGeneratorsData.IsFiniteType.shrink _ ⟨fun l => (piece
        l).choose_spec⟩⟩

-- Local finite-type kernel data over a slice, by transport along the
-- iterated-slice equivalence to the coherent base.

omit [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private theorem localKernelData
    {X : C} {M : SheafOfModules.{u} (R.over X)}
    (N : SheafOfModules.{u} R) [IsCoherent (R := R) N]
    (φ : M ⟶ N.over X) (U : Over X) (n : ℕ)
    (π : _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin n)) ⟶ M.over U) :
    ∃ τ : (Limits.kernel (π ≫
        (_root_.SheafOfModules.overFunctor (R.over X) U).map φ)).LocalGeneratorsData.{max u v₁},
      τ.IsFiniteType := by
    let E := kernelIteratedSliceEquiv (R := R) X U
    let eF : _root_.SheafOfModules.free (R := R.over U.left) (ULift.{u} (Fin n)) ≅
        E.inverse.obj
          (_root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin n))) :=
      _root_.SheafOfModules.mapFreeIso E.inverse _ (Iso.refl _)
    have hpreN : E.functor.obj (E.inverse.obj ((N.over X).over U)) ≅
        E.functor.obj (N.over U.left) := E.counitIso.app _
    let eN : E.inverse.obj ((N.over X).over U) ≅ N.over U.left :=
      E.fullyFaithfulFunctor.preimageIso hpreN
    let q : _root_.SheafOfModules.free (R := R.over U.left) (ULift.{u} (Fin n)) ⟶
        N.over U.left :=
      eF.hom ≫ E.inverse.map
          (π ≫ (_root_.SheafOfModules.overFunctor (R.over X) U).map φ) ≫ eN.hom
    have hq : _root_.SheafOfModules.IsFiniteType (R := R.over U.left) (Limits.kernel q) :=
      IsCoherent.kernel_finiteType U.left q
    obtain ⟨δ, hδ⟩ := hq.exists_localGeneratorsData
    let dM := _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin n))
    let dN := (N.over X).over U
    let comp := π ≫ (_root_.SheafOfModules.overFunctor (R.over X) U).map φ
    let ek0 : Limits.kernel q ≅ Limits.kernel (E.inverse.map comp) :=
      Limits.kernel.mapIso q (E.inverse.map comp) eF eN.symm
        (by
          dsimp only [q, comp]
          rw [E.inverse.map_comp]
          simp only [Category.assoc]
          simp)
    let ek : E.functor.obj (Limits.kernel q) ≅ Limits.kernel comp :=
      E.functor.mapIso ek0 ≪≫
        PreservesKernel.iso E.functor (E.inverse.map comp) ≪≫
        Limits.kernel.mapIso (E.functor.map (E.inverse.map comp)) comp
          (E.counitIso.app dM) (E.counitIso.app dN)
          (E.counitIso.hom.naturality comp)
    let backward : Over U.left ⥤ Over U :=
      (Over.iteratedSliceEquiv U).symm.functor
    let forward : Over U ⥤ Over U.left :=
      (Over.iteratedSliceEquiv U).functor
    let V : δ.I → Over U := fun l => backward.obj (δ.X l)
    have hVcov : ((J.over X).over U).CoversTop V :=
      GrothendieckTopology.CoversTop.iteratedSliceEquiv_inverse U δ.coversTop
    have hcontB : backward.IsContinuous (J.over U.left)
        ((J.over X).over U) := by
      change U.iteratedSliceBackward.IsContinuous _ _
      infer_instance
    have hcpB : CoverPreserving (J.over U.left)
        ((J.over X).over U) backward :=
      CoverPreserving.of_isContinuous _ _ _
    have hcontFwd : forward.IsContinuous ((J.over X).over U)
        (J.over U.left) := by
      change U.iteratedSliceForward.IsContinuous _ _
      infer_instance
    have hcpFwd : CoverPreserving ((J.over X).over U)
        (J.over U.left) forward :=
      CoverPreserving.of_isContinuous _ _ _
    have piece : ∀ l : δ.I,
        ∃ G : ((Limits.kernel comp).over (V l)).GeneratingSections,
          G.IsFiniteType := by
      intro l
      have hcpPost : CoverPreserving ((J.over U.left).over (δ.X l))
          (((J.over X).over U).over (V l))
          (Over.postEquiv (Over.iteratedSliceEquiv U).symm
            (X := δ.X l)).functor :=
        CoverPreserving.overPost _ hcpB
      have hcontPost : (Over.postEquiv (Over.iteratedSliceEquiv U).symm
          (X := δ.X l)).functor.IsContinuous
          ((J.over U.left).over (δ.X l))
          (((J.over X).over U).over (V l)) :=
        Functor.isContinuous_of_coverPreserving
          (Functor.IsCoverDense.compatiblePreserving _ _) hcpPost
      have hcpBack : CoverPreserving (((J.over X).over U).over (V l))
          ((J.over U.left).over (forward.obj (V l))) (Over.post forward) :=
        CoverPreserving.overPost _ hcpFwd
      have hcpMap : CoverPreserving
          ((J.over U.left).over (forward.obj (V l)))
          ((J.over U.left).over (δ.X l))
          (Over.map ((Over.iteratedSliceEquiv U).symm.unitIso.inv.app (δ.X l))) :=
        CoverPreserving.of_isContinuous _ _ _
      have hcpInv : CoverPreserving (((J.over X).over U).over (V l))
          ((J.over U.left).over (δ.X l))
          (Over.postEquiv (Over.iteratedSliceEquiv U).symm
            (X := δ.X l)).inverse :=
        CoverPreserving.comp _ _ hcpBack hcpMap
      have hcontInv : (Over.postEquiv (Over.iteratedSliceEquiv U).symm
          (X := δ.X l)).inverse.IsContinuous
          (((J.over X).over U).over (V l))
          ((J.over U.left).over (δ.X l)) :=
        Functor.isContinuous_of_coverPreserving
          (Functor.IsCoverDense.compatiblePreserving _ _) hcpInv
      let Eₗ : SheafOfModules.{u} ((R.over U.left).over (δ.X l)) ≌
          SheafOfModules.{u} (((R.over X).over U).over (V l)) :=
        (_root_.SheafOfModules.pushforwardPushforwardEquivalence
          (Over.postEquiv (Over.iteratedSliceEquiv U).symm (X := δ.X l))
          (S := ((R.over U.left).over (δ.X l)))
          (R := (((R.over X).over U).over (V l)))
          (𝟙 _) (𝟙 _) (by ext : 2; exact R.1.map_id _)
          (by ext : 2; exact R.1.map_id _)).symm
      have hEcol : PreservesColimitsOfSize.{u, u} Eₗ.functor := inferInstance
      have hδfin : (δ.generators l).IsFiniteType := hδ.isFiniteType l
      have Cl : Eₗ.functor.obj ((Limits.kernel q).over (δ.X l)) ≅
          (E.functor.obj (Limits.kernel q)).over (V l) := Iso.refl _
      let el : Eₗ.functor.obj ((Limits.kernel q).over (δ.X l)) ≅
          (Limits.kernel comp).over (V l) :=
        Cl ≪≫ (_root_.SheafOfModules.overFunctor ((R.over X).over U) (V l)).mapIso ek
      let eFree : _root_.SheafOfModules.free (R := (((R.over X).over U).over (V l)))
          (δ.generators l).I ≅
          Eₗ.functor.obj (_root_.SheafOfModules.free (R := ((R.over U.left).over (δ.X l)))
            (δ.generators l).I) :=
        (_root_.SheafOfModules.isColimitFreeCofan (δ.generators l).I).coconePointsIsoOfNatIso
          (isColimitOfPreserves Eₗ.functor
            (_root_.SheafOfModules.isColimitFreeCofan (δ.generators l).I))
          (Discrete.natIso fun _ => Iso.refl _)
      let G : (Eₗ.functor.obj ((Limits.kernel q).over (δ.X l))).GeneratingSections :=
        { I := (δ.generators l).I
          s := _root_.SheafOfModules.freeHomEquiv _
            (eFree.hom ≫ Eₗ.functor.map (δ.generators l).π)
          epi := by
            simp only [Equiv.symm_apply_apply]
            infer_instance }
      let G' : ((Limits.kernel comp).over (V l)).GeneratingSections :=
        G.ofEpi el.hom
      exact ⟨G', ⟨(inferInstance : (δ.generators l).IsFiniteType).finite⟩⟩
    choose gen hgen using piece
    exact ⟨⟨δ.I, V, hVcov, gen⟩,
      ⟨fun l => ⟨(hgen l).finite⟩⟩⟩

-- Coherence gives finite-type kernels after restriction to a slice.

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private theorem finiteType_kernel_to_coherent_over
    {X : C} {M : SheafOfModules.{u} (R.over X)}
    (N : SheafOfModules.{u} R) [IsCoherent (R := R) N]
    [_root_.SheafOfModules.IsFiniteType (R := R.over X) M] (φ : M ⟶ N.over X) :
    _root_.SheafOfModules.IsFiniteType (R := R.over X) (Limits.kernel φ) := by
  classical
  obtain ⟨σ, hσ⟩ := _root_.SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  have hLocal (i : σ.I) : ∃ (n : ℕ)
      (π : _root_.SheafOfModules.free (R := (R.over X).over (σ.X i)) (ULift.{u} (Fin n)) ⟶
        M.over (σ.X i))
      (τ : (Limits.kernel (π ≫
          (_root_.SheafOfModules.overFunctor (R.over X) (σ.X
          i)).map φ)).LocalGeneratorsData.{max u v₁}),
      Epi π ∧ τ.IsFiniteType := by
    have := hσ.isFiniteType i
    obtain ⟨n, π, hπ⟩ := epiFreeFin_of_finiteGenerators_slice
      (K := J.over X) (S := R.over X) (Y := σ.X i) (σ.generators i)
    have : Epi π := hπ
    obtain ⟨τ, hτ⟩ := localKernelData N φ (σ.X i) n π
    exact ⟨n, π, τ, hπ, hτ⟩
  choose n π τ hπ hτ using hLocal
  -- Strong sheafification on double slices, derived from the single-slice
  -- hypothesis via the iterated-slice equivalence (cf.
  -- `hasSheafifyIteratedSlice`): needed for the abelian structure of
  -- double-slice modules in `hα` below and for `kernelPieceGeneratorsOver`.
  have hstrong₂ : ∀ Z : Over X,
      HasSheafify ((J.over X).over Z) AddCommGrpCat.{u} :=
    fun Z => hasSheafifyIteratedSlice J X Z
  have hα : ∀ i, ∃ (α : Limits.kernel ((π i) ≫
      (_root_.SheafOfModules.overFunctor (R.over X) (σ.X i)).map φ) ⟶
      (Limits.kernel φ).over (σ.X i)), Epi α := by
    intro i
    have hπi : Epi (π i) := hπ i
    have h0 : (Limits.kernel.ι ((π i) ≫
          (_root_.SheafOfModules.overFunctor (R.over X) (σ.X i)).map φ) ≫ π i) ≫
          (_root_.SheafOfModules.overFunctor (R.over X) (σ.X i)).map φ = 0 := by
      rw [Category.assoc]
      exact Limits.kernel.condition _
    have hm : Limits.pullback.fst (π i)
          (Limits.kernel.ι ((_root_.SheafOfModules.overFunctor (R.over X) (σ.X i)).map φ)) ≫
          ((π i) ≫ (_root_.SheafOfModules.overFunctor (R.over X) (σ.X i)).map φ) = 0 := by
      simp only [← Category.assoc, Limits.pullback.condition]
      simp only [Category.assoc, Limits.kernel.condition, comp_zero]
    have heq : Limits.kernel.lift ((π i) ≫
          (_root_.SheafOfModules.overFunctor (R.over X) (σ.X i)).map φ)
          (Limits.pullback.fst (π i)
            (Limits.kernel.ι ((_root_.SheafOfModules.overFunctor (R.over X) (σ.X i)).map φ))) hm ≫
          Limits.kernel.lift ((_root_.SheafOfModules.overFunctor (R.over X) (σ.X i)).map φ)
            (Limits.kernel.ι ((π i) ≫
              (_root_.SheafOfModules.overFunctor (R.over X) (σ.X i)).map φ) ≫ π i) h0 =
          Limits.pullback.snd (π i)
            (Limits.kernel.ι ((_root_.SheafOfModules.overFunctor (R.over X) (σ.X i)).map φ)) := by
      refine (cancel_mono
        (Limits.kernel.ι ((_root_.SheafOfModules.overFunctor (R.over X) (σ.X i)).map φ))).mp ?_
      rw [Category.assoc, Limits.kernel.lift_ι, ← Category.assoc,
        Limits.kernel.lift_ι]
      exact Limits.pullback.condition
    have : Epi (Limits.pullback.snd (π i)
        (Limits.kernel.ι ((_root_.SheafOfModules.overFunctor (R.over X) (σ.X i)).map
            φ))) := inferInstance
    have hLiftEpi : Epi (Limits.kernel.lift
        ((_root_.SheafOfModules.overFunctor (R.over X) (σ.X i)).map φ)
        (Limits.kernel.ι ((π i) ≫
          (_root_.SheafOfModules.overFunctor (R.over X) (σ.X i)).map φ) ≫ π i) h0) :=
      epi_of_epi_fac heq
    exact ⟨Limits.kernel.lift ((_root_.SheafOfModules.overFunctor (R.over X) (σ.X i)).map φ)
        (Limits.kernel.ι ((π i) ≫
          (_root_.SheafOfModules.overFunctor (R.over X) (σ.X i)).map φ) ≫ π i) h0 ≫
        (PreservesKernel.iso
          (_root_.SheafOfModules.overFunctor (R.over X) (σ.X i)) φ).symm.hom, inferInstance⟩
  choose α hαEpi using hα
  have piece : ∀ p : (i : σ.I) × (τ i).I,
      ∃ G : ((Limits.kernel φ).over (((τ p.1).X p.2).left)).GeneratingSections,
        G.IsFiniteType := by
    intro ⟨i, j⟩
    have hfin : ((τ i).generators j).IsFiniteType := (hτ i).isFiniteType j
    have := hαEpi i
    exact kernelPieceGeneratorsOver (Limits.kernel φ) (σ.X i) ((τ i).X j)
      (Limits.kernel ((π i) ≫ (_root_.SheafOfModules.overFunctor (R.over X) (σ.X i)).map φ))
      (α i) ((τ i).generators j)
  choose gen hgen using piece
  have hcover : (J.over X).CoversTop
      (fun p : (i : σ.I) × (τ i).I => ((τ p.1).X p.2).left) :=
    σ.coversTop.over (fun i => (τ i).coversTop)
  exact ⟨⟨(i : σ.I) × (τ i).I,
    fun p : (i : σ.I) × (τ i).I => ((τ p.1).X p.2).left, hcover, gen⟩,
    ⟨fun p => ⟨(hgen p).finite⟩⟩⟩

theorem isCoherent_extension
    {S : ShortComplex (SheafOfModules.{u} R)} (hS : S.ShortExact)
    [IsCoherent (R := R) S.X₁]
    [IsCoherent (R := R) S.X₃] :
    IsCoherent (R := R) S.X₂ := by
  constructor
  · let : _root_.SheafOfModules.IsFiniteType (R := R) S.X₁ := IsCoherent.finiteType
    let : _root_.SheafOfModules.IsFiniteType (R := R) S.X₃ := IsCoherent.finiteType
    exact isFiniteType_extension' hS
  · intro X n ψ
    let F := _root_.SheafOfModules.overFunctor R X
    have hzero : F.PreservesZeroMorphisms := inferInstance
    have hker : ∀ {A B : SheafOfModules.{u} R} (f : A ⟶ B),
        PreservesLimit (parallelPair f 0) F := fun f => preservesKernel_overFunctor f X
    have hcoker : ∀ {A B : SheafOfModules.{u} R} (f : A ⟶ B),
        PreservesColimit (parallelPair f 0) F := fun f => preservesCokernel_overFunctor f X
    have hlim : PreservesFiniteLimits F :=
      Functor.preservesFiniteLimits_of_preservesKernels F
    have hcolim : PreservesFiniteColimits F :=
      Functor.preservesFiniteColimits_of_preservesCokernels F
    let T := S.map F
    change _root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin n)) ⟶ T.X₂ at ψ
    have hT : T.ShortExact := hS.map_of_exact F
    have hmT : Mono T.f := hT.mono_f
    have heT : Epi T.g := hT.epi_g
    let q := ψ ≫ T.g
    have hKq : _root_.SheafOfModules.IsFiniteType (R := R.over X) (Limits.kernel q) :=
      IsCoherent.kernel_finiteType X q
    change _root_.SheafOfModules.IsFiniteType (R := R.over X) (Limits.kernel ψ)
    let P := Limits.pullback ψ T.f
    let liftF : ∀ s : KernelFork q, s.pt ⟶ T.X₁ := fun s =>
      hT.fIsKernel.lift (KernelFork.ofι (Fork.ι s ≫ ψ) (by
        simpa only [q, Category.assoc] using KernelFork.condition s))
    have liftF_f : ∀ s : KernelFork q, liftF s ≫ T.f = Fork.ι s ≫ ψ := by
      intro s
      dsimp only [liftF]
      exact Fork.IsLimit.lift_ι hT.fIsKernel
    let kP : IsLimit (KernelFork.ofι (Limits.pullback.fst ψ T.f) (by
        calc
          Limits.pullback.fst ψ T.f ≫ q =
              (Limits.pullback.fst ψ T.f ≫ ψ) ≫ T.g := by
                simp only [q, Category.assoc]
          _ = (Limits.pullback.snd ψ T.f ≫ T.f) ≫ T.g := by
                rw [Limits.pullback.condition]
          _ = 0 := by rw [Category.assoc, T.zero, comp_zero])) :=
      Fork.IsLimit.mk _
        (fun s => Limits.pullback.lift (Fork.ι s) (liftF s) (liftF_f s).symm)
        (fun s => Limits.pullback.lift_fst _ _ _)
        (fun s m hm => by
          apply Limits.pullback.hom_ext
          · dsimp only [KernelFork.ι_ofι] at hm
            exact hm.trans (Limits.pullback.lift_fst _ _ _).symm
          · dsimp only [KernelFork.ι_ofι] at hm
            have hm' : m ≫ Limits.pullback.snd ψ T.f = liftF s := by
              apply (cancel_mono T.f).mp
              calc
                (m ≫ Limits.pullback.snd ψ T.f) ≫ T.f =
                    (m ≫ Limits.pullback.fst ψ T.f) ≫ ψ := by
                      simp only [Category.assoc, Limits.pullback.condition]
                _ = Fork.ι s ≫ ψ := by rw [hm]
                _ = liftF s ≫ T.f := (liftF_f s).symm
            exact hm'.trans (Limits.pullback.lift_snd _ _ _).symm)
    let eP : P ≅ Limits.kernel q :=
      kP.conePointUniqueUpToIso (Limits.limit.isLimit _)
    let b : P ⟶ T.X₁ := Limits.pullback.snd ψ T.f
    have hP : _root_.SheafOfModules.IsFiniteType (R := R.over X) P := by
      have : Epi eP.symm.hom := IsIso.epi_of_iso _
      exact isFiniteType_of_epi' (K := J.over X) (S := R.over X) eP.symm.hom
    have hKb : _root_.SheafOfModules.IsFiniteType (R := R.over X) (Limits.kernel b) :=
      finiteType_kernel_to_coherent_over S.X₁ b
    have sq : IsPullback (Limits.pullback.fst ψ T.f)
        (Limits.pullback.snd ψ T.f) ψ T.f := IsPullback.of_hasPullback ψ T.f
    let kb : Limits.kernel b ⟶ Limits.kernel ψ :=
      Limits.kernel.map b ψ (Limits.pullback.fst ψ T.f) T.f sq.flip.w
    have hIso : IsIso kb := by
      dsimp [kb, b]
      exact Limits.isIso_kernel_map_of_isPullback sq.flip
    exact isFiniteType_of_epi' kb

-- When `R` is coherent, (ii) FP ↔ (iii) Coherent (Stacks 01BZ).
-- `QC ∧ FT ↔ FP` and `QC ∧ FT ↔ Coherent` are false over merely coherent `R`
-- (e.g. `R = k[x₁,x₂,…]`, `M = R/(x₁,…)`) and belong to the locally
-- Noetherian comparison in `AlgebraicGeometry.Modules.Coherent`.

private noncomputable def kernelBiprodLiftIso {A : Type*} [Category A]
    [Preadditive A] [HasKernels A] [HasBinaryBiproducts A]
    {P Q U : A} (a : P ⟶ Q) (b : P ⟶ U) :
    kernel (biprod.lift a b) ≅ kernel (kernel.ι a ≫ b) := by
  let f : P ⟶ Q ⊞ U := biprod.lift a b
  let k : kernel a ⟶ U := kernel.ι a ≫ b
  have hfa : kernel.ι f ≫ a = 0 := by
    rw [← biprod.lift_fst a b, ← Category.assoc, kernel.condition, zero_comp]
  let toKa : kernel f ⟶ kernel a := kernel.lift a (kernel.ι f) hfa
  have htoKa : toKa ≫ k = 0 := by
    rw [show k = kernel.ι a ≫ b from rfl, ← Category.assoc]
    rw [show toKa ≫ kernel.ι a = kernel.ι f from kernel.lift_ι _ _ _]
    rw [← biprod.lift_snd a b, ← Category.assoc, kernel.condition, zero_comp]
  let e : kernel f ⟶ kernel k := kernel.lift k toKa htoKa
  have hback : (kernel.ι k ≫ kernel.ι a) ≫ f = 0 := by
    rw [show f = biprod.lift a b from rfl]
    rw [Category.assoc, biprod.lift_eq, Preadditive.comp_add,
      ← Category.assoc, ← Category.assoc, kernel.condition, zero_comp,
      zero_add]
    rw [← Category.assoc]
    change (kernel.ι k ≫ k) ≫ biprod.inr = 0
    rw [kernel.condition, zero_comp]
  let einv : kernel k ⟶ kernel f :=
    kernel.lift f (kernel.ι k ≫ kernel.ι a) hback
  refine ⟨e, einv, ?_, ?_⟩
  · apply (cancel_mono (kernel.ι f)).mp
    rw [Category.assoc, show einv ≫ kernel.ι f = kernel.ι k ≫ kernel.ι a from
      kernel.lift_ι _ _ _, ← Category.assoc,
      show e ≫ kernel.ι k = toKa from kernel.lift_ι _ _ _,
      show toKa ≫ kernel.ι a = kernel.ι f from kernel.lift_ι _ _ _, Category.id_comp]
  · apply (cancel_mono (kernel.ι k)).mp
    rw [Category.assoc, show e ≫ kernel.ι k = toKa from kernel.lift_ι _ _ _,
      show einv ≫ toKa = kernel.ι k from by
        apply (cancel_mono (kernel.ι a)).mp
        rw [Category.assoc, show toKa ≫ kernel.ι a = kernel.ι f from
          kernel.lift_ι _ _ _, show einv ≫ kernel.ι f = kernel.ι k ≫ kernel.ι a from
          kernel.lift_ι _ _ _],
      Category.id_comp]


private lemma kernelBiprodDesc_fst_comp
    {𝒜 : Type w} [Category.{v₂} 𝒜] [Abelian 𝒜]
    {A B F N : 𝒜}
    (q : B ⟶ N) (r : A ⟶ Limits.kernel q) (l : F ⟶ B) :
    (Limits.kernel.ι (biprod.desc l (-(r ≫ Limits.kernel.ι q))) ≫ biprod.fst) ≫ l =
      (Limits.kernel.ι (biprod.desc l (-(r ≫ Limits.kernel.ι q))) ≫ biprod.snd) ≫
        (r ≫ Limits.kernel.ι q) := by
  let k := Limits.kernel.ι (biprod.desc l (-(r ≫ Limits.kernel.ι q)))
  have hk : biprod.lift (k ≫ biprod.fst) (k ≫ biprod.snd) = k := by
    apply biprod.hom_ext <;> simp
  have hd0 := Limits.kernel.condition (biprod.desc l (-(r ≫ Limits.kernel.ι q)))
  have hsum : (k ≫ biprod.fst) ≫ l + (k ≫ biprod.snd) ≫ (-(r ≫ Limits.kernel.ι q)) = 0 := by
    rw [← biprod.lift_desc, hk]
    exact hd0
  apply sub_eq_zero.mp
  simpa only [Preadditive.comp_neg, sub_eq_add_neg] using hsum

private noncomputable def kernelBiprodComparison
    {𝒜 : Type w} [Category.{v₂} 𝒜] [Abelian 𝒜]
    {A B F N : 𝒜}
    (q : B ⟶ N) (r : A ⟶ Limits.kernel q) (l : F ⟶ B) (φ : F ⟶ N)
    (hl : l ≫ q = φ) :
    Limits.kernel (biprod.desc l (-(r ≫ Limits.kernel.ι q))) ⟶ Limits.kernel φ :=
  Limits.kernel.lift φ
    (Limits.kernel.ι (biprod.desc l (-(r ≫ Limits.kernel.ι q))) ≫ biprod.fst) (by
      calc
        (Limits.kernel.ι (biprod.desc l (-(r ≫ Limits.kernel.ι q))) ≫ biprod.fst) ≫ φ =
            (Limits.kernel.ι (biprod.desc l (-(r ≫ Limits.kernel.ι q))) ≫ biprod.fst) ≫
              (l ≫ q) := by rw [hl]
        _ = ((Limits.kernel.ι (biprod.desc l (-(r ≫ Limits.kernel.ι q))) ≫ biprod.fst) ≫ l) ≫ q :=
          (Category.assoc _ _ _).symm
        _ = ((Limits.kernel.ι (biprod.desc l (-(r ≫ Limits.kernel.ι q))) ≫ biprod.snd) ≫
              (r ≫ Limits.kernel.ι q)) ≫ q := by
          rw [kernelBiprodDesc_fst_comp q r l]
        _ = 0 := by simp only [Category.assoc, Limits.kernel.condition, comp_zero])

private theorem epi_kernelBiprodComparison
    {𝒜 : Type w} [Category.{v₂} 𝒜] [Abelian 𝒜]
    {A B F N : 𝒜}
    (q : B ⟶ N) (r : A ⟶ Limits.kernel q) [Epi r]
    (l : F ⟶ B) (φ : F ⟶ N) (hl : l ≫ q = φ) :
    Epi (kernelBiprodComparison q r l φ hl) := by
  let a : A ⟶ B := r ≫ Limits.kernel.ι q
  let d : F ⊞ A ⟶ B := biprod.desc l (-a)
  let e : Limits.kernel d ⟶ Limits.kernel φ :=
    kernelBiprodComparison q r l φ hl
  change Epi e
  have he_ι : e ≫ Limits.kernel.ι φ = Limits.kernel.ι d ≫ biprod.fst := by
    dsimp [e, kernelBiprodComparison, d, a]
    apply Limits.kernel.lift_ι
  let h : Limits.kernel φ ⟶ Limits.kernel q := Limits.kernel.lift q
    (Limits.kernel.ι φ ≫ l) (by
      rw [Category.assoc, hl]
      exact Limits.kernel.condition _)
  have hh_ι : h ≫ Limits.kernel.ι q = Limits.kernel.ι φ ≫ l :=
    Limits.kernel.lift_ι _ _ _
  let s : Limits.kernel d ⟶ A := Limits.kernel.ι d ≫ biprod.snd
  have hs_r : s ≫ r = e ≫ h := by
    apply (cancel_mono (Limits.kernel.ι q)).1
    calc
      (s ≫ r) ≫ Limits.kernel.ι q =
          (Limits.kernel.ι d ≫ biprod.snd) ≫ (r ≫ Limits.kernel.ι q) := by simp [s]
      _ = (Limits.kernel.ι d ≫ biprod.fst) ≫ l := by
        dsimp [d, a]
        exact (kernelBiprodDesc_fst_comp q r l).symm
      _ = (e ≫ Limits.kernel.ι φ) ≫ l := by rw [he_ι]
      _ = (e ≫ h) ≫ Limits.kernel.ι q := by simp only [Category.assoc, hh_ι]
  have he_pullback : IsPullback e s h r := by
    refine ⟨⟨hs_r.symm⟩, ⟨PullbackCone.IsLimit.mk hs_r.symm ?_ ?_ ?_ ?_⟩⟩
    · intro t
      have hxy : biprod.lift (t.fst ≫ Limits.kernel.ι φ) t.snd ≫ d = 0 := by
        dsimp [d, a]
        rw [biprod.lift_desc, Preadditive.comp_neg, ← sub_eq_add_neg, sub_eq_zero]
        calc
          (t.fst ≫ Limits.kernel.ι φ) ≫ l = t.fst ≫ (h ≫ Limits.kernel.ι q) := by
            rw [hh_ι, Category.assoc]
          _ = (t.fst ≫ h) ≫ Limits.kernel.ι q := (Category.assoc _ _ _).symm
          _ = (t.snd ≫ r) ≫ Limits.kernel.ι q := by rw [t.condition]
          _ = t.snd ≫ (r ≫ Limits.kernel.ι q) := Category.assoc _ _ _
      exact Limits.kernel.lift d (biprod.lift (t.fst ≫ Limits.kernel.ι φ) t.snd) hxy
    · intro t
      apply (cancel_mono (Limits.kernel.ι φ)).1
      rw [Category.assoc, he_ι, ← Category.assoc, Limits.kernel.lift_ι, biprod.lift_fst]
    · intro t
      dsimp [s]
      rw [← Category.assoc, Limits.kernel.lift_ι, biprod.lift_snd]
    · intro t m hm₁ hm₂
      apply (cancel_mono (Limits.kernel.ι d)).1
      rw [Limits.kernel.lift_ι]
      apply biprod.hom_ext
      · simpa only [Category.assoc, he_ι, biprod.lift_fst] using
          congrArg (fun k => k ≫ Limits.kernel.ι φ) hm₁
      · dsimp [s] at hm₂
        simpa only [Category.assoc, biprod.lift_snd] using hm₂
  exact Abelian.epi_fst_of_isLimit h r he_pullback.isLimit
private theorem probeFreeFT
    {D : Type w} [Category.{v₂} D]
    {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
    [HasSheafify K AddCommGrpCat.{u}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ Y : D, HasWeakSheafify (K.over Y) AddCommGrpCat.{u}]
    [∀ Y : D, (K.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (n : ℕ) : _root_.SheafOfModules.IsFiniteType (R := S)
      (_root_.SheafOfModules.free (R := S) (ULift.{u} (Fin n))) := by
  let G₀ : ∀ (Y : D),
      (_root_.SheafOfModules.free (R := S.over Y) (ULift.{u} (Fin n))).GeneratingSections :=
    fun Y => ⟨ULift.{u} (Fin n), fun i => _root_.SheafOfModules.freeSection i, by
      rw [show (_root_.SheafOfModules.freeHomEquiv _).symm (fun i =>
          _root_.SheafOfModules.freeSection i) = 𝟙 _ from
        (_root_.SheafOfModules.freeHomEquiv _).symm_apply_apply _]
      infer_instance⟩
  let q : (_root_.SheafOfModules.free (R := S) (ULift.{u} (Fin n))).LocalGeneratorsData :=
    ⟨D, id, by
      intro Y
      apply GrothendieckTopology.covering_of_eq_top
      rw [Sieve.ext_iff]
      intro _ f
      simp [Sieve.top_apply],
      fun Y => (G₀ Y).ofEpi (finiteFreeOverIso S Y n).hom⟩
  have hq : q.IsFiniteType := by
    constructor
    intro Y
    refine ⟨?_⟩
    change Finite (ULift.{u} (Fin n))
    exact inferInstance
  exact ⟨q, hq⟩

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private theorem free_to_free_kernel_finiteType_nobp
    [IsCoherentRing (R := R)] (X : C) {n m : ℕ}
    (phi : _root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin n)) ⟶
         _root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin m))) :
  _root_.SheafOfModules.IsFiniteType (R := R.over X) (Limits.kernel phi) := by
  classical
  induction m with
  | zero =>
    have hzero : IsZero (_root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin 0))) := by
      apply IsInitial.isZero
      exact IsInitial.ofUniqueHom (fun A => (0 :
        _root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin 0)) ⟶ A)) (fun A f => by
          apply (_root_.SheafOfModules.freeHomEquiv A).injective
          funext i
          exact Fin.elim0 i.down)
    have hphi : phi = 0 := hzero.eq_of_tgt _ _
    have : IsIso (Limits.kernel.ι phi) := Limits.kernel.ι_of_zero hphi
    have hsrc : _root_.SheafOfModules.IsFiniteType (R := R.over X)
        (_root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin n))) :=
      probeFreeFT (K := J.over X) (S := R.over X) n
    let eKernel : Limits.kernel phi ≅
        _root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin n)) :=
      asIso (Limits.kernel.ι phi)
    have : Epi eKernel.inv := IsIso.epi_of_iso _
    exact isFiniteType_of_epi' (K := J.over X) (S := R.over X) eKernel.inv
  | succ m ih =>
    let eSplit : _root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin (m + 1))) ≅
        _root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin m)) ⊞
          _root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin 1)) := by
      let eIdx : ULift.{u} (Fin m) ⊕ ULift.{u} (Fin 1) ≃
          ULift.{u} (Fin (m + 1)) :=
        (Equiv.sumCongr Equiv.ulift Equiv.ulift).trans
          (finSumFinEquiv.trans Equiv.ulift.symm)
      exact (biprod.isoCoprod _ _ ≪≫ _root_.SheafOfModules.freeSumIso _ _ ≪≫
        (_root_.SheafOfModules.freeFunctor (R := R.over X)).mapIso eIdx.toIso).symm
    let a : _root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin n)) ⟶
        _root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin m)) :=
      phi ≫ eSplit.hom ≫ biprod.fst
    let b : _root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin n)) ⟶
        _root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin 1)) :=
      phi ≫ eSplit.hom ≫ biprod.snd
    let k : Limits.kernel a ⟶ _root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin 1)) :=
      Limits.kernel.ι a ≫ b
    let eOne : _root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin 1)) ≅
        (_root_.SheafOfModules.unit (R := R.over X) : SheafOfModules.{u} (R.over X)) := by
      let e : _root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin 1)) ⟶
          (_root_.SheafOfModules.unit (R := R.over X) : SheafOfModules.{u} (R.over X)) :=
        Sigma.desc (fun _ => 𝟙 _)
      let r : (_root_.SheafOfModules.unit (R := R.over X) : SheafOfModules.{u} (R.over X)) ⟶
          _root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin 1)) :=
        _root_.SheafOfModules.ιFree (ULift.up (0 : Fin 1))
      refine ⟨e, r, ?_, Sigma.ι_comp_desc _ _⟩
      refine Cofan.IsColimit.hom_ext
        (_root_.SheafOfModules.isColimitFreeCofan (R :=
            R.over X) (ULift.{u} (Fin 1))) _ _ fun j => ?_
      have hι : (_root_.SheafOfModules.freeCofan (R :=
          R.over X) (ULift.{u} (Fin 1))).inj j ≫ e = 𝟙 _ :=
        Sigma.ι_comp_desc _ _
      have hj : j = ULift.up (0 : Fin 1) := by
        cases j with
        | up a => rw [Fin.eq_zero a]
      subst hj
      refine Eq.trans ((Category.assoc _ _ _).symm) ?_
      refine Eq.trans (congrArg (· ≫ _) hι) ?_
      refine Eq.trans (Category.id_comp _) ?_
      change r = r ≫ 𝟙 _
      exact (Category.comp_id _).symm
    have haFT : _root_.SheafOfModules.IsFiniteType (R := R.over X) (Limits.kernel a) := ih a
    have : IsIso eOne.hom := Iso.isIso_hom eOne
    let ku : Limits.kernel a ⟶
        (_root_.SheafOfModules.unit (R := R.over X) : SheafOfModules.{u} (R.over X)) :=
      k ≫ eOne.hom
    have hkuFT : _root_.SheafOfModules.IsFiniteType (R := R.over X) (Limits.kernel ku) :=
      finiteType_kernel_to_coherent_over (N := _root_.SheafOfModules.unit R) ku
    let eK : Limits.kernel k ≅ Limits.kernel ku :=
      (Limits.kernelCompMono k eOne.hom).symm
    have hkFT : _root_.SheafOfModules.IsFiniteType (R := R.over X) (Limits.kernel k) := by
      have : Epi eK.inv := IsIso.epi_of_iso _
      exact isFiniteType_of_epi' (K := J.over X) (S := R.over X) eK.inv
    let f : _root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin n)) ⟶
        (_root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin m)) ⊞
          _root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin 1))) :=
      phi ≫ eSplit.hom
    have hf : f = biprod.lift a b := by
      apply biprod.hom_ext
      · simp [f, a]
      · simp [f, b]
    let ephi : Limits.kernel phi ≅ Limits.kernel f :=
      (Limits.kernelCompMono phi eSplit.hom).symm
    let ef : Limits.kernel f ≅ Limits.kernel (biprod.lift a b) :=
      Limits.kernelIsoOfEq hf
    let eKernel : Limits.kernel phi ≅ Limits.kernel k :=
      ephi ≪≫ ef ≪≫ kernelBiprodLiftIso a b
    have : Epi eKernel.inv := IsIso.epi_of_iso _
    exact isFiniteType_of_epi' (K := J.over X) (S := R.over X) eKernel.inv

omit [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private theorem localPresentationKernelFiniteTypeOver
    [IsCoherentRing (R := R)] {X : C} {M : SheafOfModules.{u} (R.over X)}
    (P : M.Presentation) [P.IsFinite] {n : ℕ}
    (φ : _root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin n)) ⟶ M) :
    _root_.SheafOfModules.IsFiniteType (R := R.over X) (Limits.kernel φ) := by
  classical
  have hstrongX : HasSheafify (J.over X) AddCommGrpCat.{u} := inferInstance
  let hstrong2 : ∀ U : Over X,
      HasSheafify ((J.over X).over U) AddCommGrpCat.{u} :=
    fun U => hasSheafifyIteratedSlice J X U
  obtain ⟨m, ⟨eg⟩⟩ := Finite.exists_equiv_fin (α := P.generators.I)
  obtain ⟨a, ⟨er⟩⟩ := Finite.exists_equiv_fin (α := P.relations.I)
  let eg' : P.generators.I ≃ ULift.{u} (Fin m) := eg.trans Equiv.ulift.symm
  let er' : P.relations.I ≃ ULift.{u} (Fin a) := er.trans Equiv.ulift.symm
  let q : _root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin m)) ⟶ M :=
    ((_root_.SheafOfModules.freeFunctor (R := R.over X)).mapIso eg'.toIso.symm).hom ≫ P.generators.π
  have hqEpi : Epi q := by dsimp [q]; infer_instance
  let eq : _root_.SheafOfModules.free (R := R.over X) P.generators.I ≅
      _root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin m)) :=
    (_root_.SheafOfModules.freeFunctor (R := R.over X)).mapIso eg'.toIso
  let ek : Limits.kernel q ≅ Limits.kernel P.generators.π :=
    Limits.kernel.mapIso q P.generators.π eq.symm (Iso.refl _) (by simp [q, eq])
  let r : _root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin a)) ⟶ Limits.kernel q :=
    ((_root_.SheafOfModules.freeFunctor (R := R.over X)).mapIso er'.toIso.symm).hom ≫
      (_root_.SheafOfModules.freeHomEquiv _).symm P.relations.s ≫ ek.inv
  have hrEpi : Epi r := by
    dsimp [r]
    have : Epi ((_root_.SheafOfModules.freeHomEquiv _).symm P.relations.s) := P.relations.epi
    infer_instance
  have hls : Presheaf.IsLocallySurjective (J.over X)
      ((PresheafOfModules.toPresheaf (R.over X).obj).map q.val) :=
    locallySurjective_of_epi q
  let c : Fin n → M.sections := fun k => M.freeHomEquiv φ (ULift.up k)
  have hInter : ∀ (V : Over X),
      Finset.univ.inf (fun k : Fin n => Presheaf.imageSieve
        ((PresheafOfModules.toPresheaf (R.over X).obj).map q.val)
        ((c k).eval (Opposite.op V))) ∈ (J.over X) V := by
    let : Presheaf.IsLocallySurjective (J.over X)
        ((PresheafOfModules.toPresheaf (R.over X).obj).map q.val) := hls
    intro V
    exact GrothendieckTopology.finsetInf_mem _ (fun k =>
      Presheaf.imageSieve_mem (J.over X) _ _)
  let I : Type _ := Σ (V : Over X) (U : Over X) (f : U ⟶ V),
    PLift ((Finset.univ.inf (fun k : Fin n => Presheaf.imageSieve
      ((PresheafOfModules.toPresheaf (R.over X).obj).map q.val)
      ((c k).eval (Opposite.op V)))).arrows f)
  let Y : I → Over X := fun i => i.2.1
  have hcover : (J.over X).CoversTop Y := by
    intro V
    apply (J.over X).superset_covering
      (S := Finset.univ.inf (fun k : Fin n => Presheaf.imageSieve
        ((PresheafOfModules.toPresheaf (R.over X).obj).map q.val)
        ((c k).eval (Opposite.op V)))) _ (hInter V)
    intro U f hf
    exact ⟨⟨V, U, f, PLift.up hf⟩, ⟨𝟙 U⟩⟩
  have piece : ∀ i : I, ∃ D : ((Limits.kernel φ).over (Y i)).LocalGeneratorsData,
      D.IsFiniteType := by
    rintro ⟨V, U, f, hf⟩
    have hfmem : ∀ k : Fin n, (Presheaf.imageSieve
        ((PresheafOfModules.toPresheaf (R.over X).obj).map q.val)
        ((c k).eval (Opposite.op V))).arrows f :=
      Sieve.finsetInf_arrows _ f hf.down
    choose t ht using hfmem
    let F := _root_.SheafOfModules.overFunctor (R.over X) U
    let eFn := finiteFreeOverIso (R.over X) U n
    let eFm := finiteFreeOverIso (R.over X) U m
    let liftsec : ∀ k : ULift.{u} (Fin n),
        (F.obj (_root_.SheafOfModules.free (R :=
            R.over X) (ULift.{u} (Fin m)))).sections := fun k =>
      PresheafOfModules.sectionsMk
        (fun (W : (Over U)ᵒᵖ) =>
          (_root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin m))).val.map
            W.unop.hom.op (t k.down))
        (fun W₁ W₂ g => by
          dsimp only
          have tri : W₂.unop.hom = (Over.forget U).map g.unop ≫ W₁.unop.hom :=
            (Over.w g.unop).symm
          change (F.obj (_root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin m)))).val.map g
              ((_root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin m))).val.map
                W₁.unop.hom.op (t k.down)) = _
          rw [tri]
          exact (PresheafOfModules.map_comp_apply
            (M := (_root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin m))).val)
            (i := W₁.unop.hom.op) (j := ((Over.forget U).map g.unop).op)
            (t k.down)).symm)
    let l0 : _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin n)) ⟶
        F.obj (_root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin m))) :=
      (_root_.SheafOfModules.freeHomEquiv _).symm liftsec
    let l : _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin n)) ⟶
        _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin m)) := l0 ≫ eFm.inv
    let qU : _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin m)) ⟶ M.over U :=
      eFm.hom ≫ F.map q
    have hl0 : l0 ≫ F.map q = eFn.hom ≫ F.map φ := by
      apply (F.obj M).freeHomEquiv.injective
      funext j
      rw [_root_.SheafOfModules.freeHomEquiv_comp_apply,
          _root_.SheafOfModules.freeHomEquiv_comp_apply]
      have eL : (F.obj (_root_.SheafOfModules.free (R :=
          R.over X) (ULift.{u} (Fin m)))).freeHomEquiv l0 j =
          liftsec j := by
        dsimp [l0]
        exact congrFun ((_root_.SheafOfModules.freeHomEquiv _).apply_symm_apply _) j
      rw [eL]
      have eR : _root_.SheafOfModules.sectionsMap eFn.hom (_root_.SheafOfModules.freeSection j) =
          (F.obj (_root_.SheafOfModules.free (R := R.over X) (ULift.{u} (Fin n)))).unitHomEquiv
            (F.map (_root_.SheafOfModules.ιFree j)) := by
        have e1 : _root_.SheafOfModules.freeSection (R := (R.over X).over U) j =
            (_root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin n))).unitHomEquiv
              (_root_.SheafOfModules.ιFree j ≫ 𝟙 _) := rfl
        simp only [e1, ← _root_.SheafOfModules.unitHomEquiv_comp_apply, Category.assoc,
            Category.id_comp, eFn]
        rw [ιFree_finiteFreeOverIso_hom (R.over X) U n j]
      rw [_root_.SheafOfModules.freeHomEquiv_apply]
      change _root_.SheafOfModules.sectionsMap (F.map q) (liftsec j) =
        _root_.SheafOfModules.sectionsMap (F.map φ) (_root_.SheafOfModules.sectionsMap eFn.hom
            (_root_.SheafOfModules.freeSection j))
      rw [eR]
      apply PresheafOfModules.sections_ext
      intro W
      change (_root_.SheafOfModules.sectionsMap (F.map q) (liftsec j)).eval W = _
      have hLHS : (_root_.SheafOfModules.sectionsMap (F.map q) (liftsec j)).eval W =
          M.val.map W.unop.hom.op
            (q.val.app (Opposite.op U) (t j.down)) := by
        dsimp only [F, liftsec]
        exact PresheafOfModules.naturality_apply q.val W.unop.hom.op (t j.down)
      change (_root_.SheafOfModules.sectionsMap (F.map q) (liftsec j)).eval W = _
      rw [hLHS]
      have ht' : q.val.app (Opposite.op U) (t j.down) =
          M.val.map f.op ((c j.down).eval (Opposite.op V)) := ht j.down
      have step := congrArg (M.val.map W.unop.hom.op) ht'
      rw [step]
      refine (PresheafOfModules.map_comp_apply (M := M.val)
        f.op W.unop.hom.op ((c j.down).eval (Opposite.op V))).symm.trans ?_
      refine (PresheafOfModules.sections_property (c j.down) _).trans ?_
      dsimp [c]
      rfl
    have hl : l ≫ qU = eFn.hom ≫ F.map φ := by
      simpa only [l, qU, F, Category.assoc, Iso.inv_hom_id_assoc] using hl0
    let rU : _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin a)) ⟶
        Limits.kernel qU := by
      let ekU : F.obj (Limits.kernel q) ≅ Limits.kernel qU :=
        PreservesKernel.iso (_root_.SheafOfModules.overFunctor (R.over X) U) q ≪≫
          Limits.kernel.mapIso (F.map q) qU
          eFm.symm (Iso.refl _) (by simp [qU])
      exact (finiteFreeOverIso (R.over X) U a).hom ≫ F.map r ≫ ekU.hom
    have hrUEpi : Epi rU := by
      dsimp [rU]
      let eFree := (finiteFreeOverIso (R.over X) U a).hom
      let mappedR := F.map r
      let eKernelOver :=
        (PreservesKernel.iso (_root_.SheafOfModules.overFunctor (R.over X) U) q).hom
      let eKernelMap := (Limits.kernel.mapIso (F.map q) qU
        eFm.symm (Iso.refl _) (by simp [qU])).hom
      have : Epi eFree := IsIso.epi_of_iso _
      have : Epi mappedR := epi_over_of_epi r U
      have : Epi eKernelOver := IsIso.epi_of_iso _
      have : Epi eKernelMap := IsIso.epi_of_iso _
      change Epi (eFree ≫ mappedR ≫ eKernelOver ≫ eKernelMap)
      infer_instance
    let d : _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin n)) ⊞
        _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin a)) ⟶
        _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin m)) :=
      biprod.desc l (-(rU ≫ Limits.kernel.ι qU))
    have hdFT : _root_.SheafOfModules.IsFiniteType (R := (R.over X).over U) (Limits.kernel d) := by
      let es : _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin (n + a))) ≅
          _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin n)) ⊞
            _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin a)) := by
        let ei : ULift.{u} (Fin n) ⊕ ULift.{u} (Fin a) ≃ ULift.{u} (Fin (n + a)) :=
          (Equiv.sumCongr Equiv.ulift Equiv.ulift).trans
            (finSumFinEquiv.trans Equiv.ulift.symm)
        exact (biprod.isoCoprod _ _ ≪≫ _root_.SheafOfModules.freeSumIso _ _ ≪≫
          (_root_.SheafOfModules.freeFunctor (R := (R.over X).over U)).mapIso ei.toIso).symm
      let d' := es.hom ≫ d
      let E := kernelIteratedSliceEquiv (R := R) X U
      have hEinvCol : PreservesColimitsOfSize.{u, u} E.inverse := inferInstance
      let eFs : _root_.SheafOfModules.free (R := R.over U.left) (ULift.{u} (Fin (n + a))) ≅
          E.inverse.obj
            (_root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin (n + a)))) :=
        _root_.SheafOfModules.mapFreeIso E.inverse _ (Iso.refl _)
      let eFt : _root_.SheafOfModules.free (R := R.over U.left) (ULift.{u} (Fin m)) ≅
          E.inverse.obj (_root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin m))) :=
        _root_.SheafOfModules.mapFreeIso E.inverse _ (Iso.refl _)
      let q : _root_.SheafOfModules.free (R := R.over U.left) (ULift.{u} (Fin (n + a))) ⟶
          _root_.SheafOfModules.free (R := R.over U.left) (ULift.{u} (Fin m)) :=
        eFs.hom ≫ E.inverse.map d' ≫ eFt.inv
      have hq : _root_.SheafOfModules.IsFiniteType (R := R.over U.left) (Limits.kernel q) :=
        free_to_free_kernel_finiteType_nobp U.left q
      obtain ⟨δ, hδ⟩ := hq.exists_localGeneratorsData
      let ek0 : Limits.kernel q ≅ Limits.kernel (E.inverse.map d') :=
        Limits.kernel.mapIso q (E.inverse.map d') eFs eFt
          (by dsimp [q]; simp)
      let ek : E.functor.obj (Limits.kernel q) ≅ Limits.kernel d' :=
        E.functor.mapIso ek0 ≪≫
          PreservesKernel.iso E.functor (E.inverse.map d') ≪≫
          Limits.kernel.mapIso (E.functor.map (E.inverse.map d')) d'
            (E.counitIso.app _) (E.counitIso.app _)
            (E.counitIso.hom.naturality d')
      let backward : Over U.left ⥤ Over U :=
        (Over.iteratedSliceEquiv U).symm.functor
      let forward : Over U ⥤ Over U.left :=
        (Over.iteratedSliceEquiv U).functor
      let V' : δ.I → Over U := fun z => backward.obj (δ.X z)
      have hV' : ((J.over X).over U).CoversTop V' :=
        GrothendieckTopology.CoversTop.iteratedSliceEquiv_inverse U δ.coversTop
      have hcontB : backward.IsContinuous (J.over U.left)
          ((J.over X).over U) := by
        change U.iteratedSliceBackward.IsContinuous _ _
        infer_instance
      have hcpB : CoverPreserving (J.over U.left)
          ((J.over X).over U) backward :=
        CoverPreserving.of_isContinuous _ _ _
      have hcontFwd : forward.IsContinuous ((J.over X).over U)
          (J.over U.left) := by
        change U.iteratedSliceForward.IsContinuous _ _
        infer_instance
      have hcpFwd : CoverPreserving ((J.over X).over U)
          (J.over U.left) forward :=
        CoverPreserving.of_isContinuous _ _ _
      have pieces : ∀ z : δ.I,
          ∃ G : ((Limits.kernel d').over (V' z)).GeneratingSections,
            G.IsFiniteType := by
        intro z
        have hcpPost : CoverPreserving ((J.over U.left).over (δ.X z))
            (((J.over X).over U).over (V' z))
            (Over.postEquiv (Over.iteratedSliceEquiv U).symm
              (X := δ.X z)).functor :=
          CoverPreserving.overPost _ hcpB
        have hcontPost : (Over.postEquiv (Over.iteratedSliceEquiv U).symm
            (X := δ.X z)).functor.IsContinuous
            ((J.over U.left).over (δ.X z))
            (((J.over X).over U).over (V' z)) :=
          Functor.isContinuous_of_coverPreserving
            (Functor.IsCoverDense.compatiblePreserving _ _) hcpPost
        have hcpBack : CoverPreserving (((J.over X).over U).over (V' z))
            ((J.over U.left).over (forward.obj (V' z))) (Over.post forward) :=
          CoverPreserving.overPost _ hcpFwd
        have hcpMap : CoverPreserving
            ((J.over U.left).over (forward.obj (V' z)))
            ((J.over U.left).over (δ.X z))
            (Over.map ((Over.iteratedSliceEquiv U).symm.unitIso.inv.app (δ.X z))) :=
          CoverPreserving.of_isContinuous _ _ _
        have hcpInv : CoverPreserving (((J.over X).over U).over (V' z))
            ((J.over U.left).over (δ.X z))
            (Over.postEquiv (Over.iteratedSliceEquiv U).symm
              (X := δ.X z)).inverse :=
          CoverPreserving.comp _ _ hcpBack hcpMap
        have hcontInv : (Over.postEquiv (Over.iteratedSliceEquiv U).symm
            (X := δ.X z)).inverse.IsContinuous
            (((J.over X).over U).over (V' z))
            ((J.over U.left).over (δ.X z)) :=
          Functor.isContinuous_of_coverPreserving
            (Functor.IsCoverDense.compatiblePreserving _ _) hcpInv
        let Eₗ : SheafOfModules.{u} ((R.over U.left).over (δ.X z)) ≌
            SheafOfModules.{u} (((R.over X).over U).over (V' z)) :=
          (_root_.SheafOfModules.pushforwardPushforwardEquivalence
            (Over.postEquiv (Over.iteratedSliceEquiv U).symm (X := δ.X z))
            (S := ((R.over U.left).over (δ.X z)))
            (R := (((R.over X).over U).over (V' z)))
            (𝟙 _) (𝟙 _) (by ext : 2; exact R.1.map_id _)
            (by ext : 2; exact R.1.map_id _)).symm
        have hEcol : PreservesColimitsOfSize.{u, u} Eₗ.functor := inferInstance
        have hδfin : (δ.generators z).IsFiniteType := hδ.isFiniteType z
        have Cz : Eₗ.functor.obj ((Limits.kernel q).over (δ.X z)) ≅
            (E.functor.obj (Limits.kernel q)).over (V' z) := Iso.refl _
        let ez : Eₗ.functor.obj ((Limits.kernel q).over (δ.X z)) ≅
            (Limits.kernel d').over (V' z) :=
          Cz ≪≫ (_root_.SheafOfModules.overFunctor ((R.over X).over U) (V' z)).mapIso ek
        let G := ((δ.generators z).mapEquivalenceWeak Eₗ (Iso.refl _)).ofEpi ez.hom
        exact ⟨G, ⟨(inferInstance : (δ.generators z).IsFiniteType).finite⟩⟩
      choose gen hgen using pieces
      have hd'FT : _root_.SheafOfModules.IsFiniteType (R := (R.over X).over U) (Limits.kernel d') :=
        ⟨⟨δ.I, V', hV', gen⟩, ⟨fun z => ⟨(hgen z).finite⟩⟩⟩
      let ed : Limits.kernel d' ≅ Limits.kernel d :=
        Limits.kernel.mapIso d' d es (Iso.refl _) (by simp [d'])
      have : Epi ed.hom := inferInstance
      exact isFiniteType_of_epi' ed.hom
    let target : _root_.SheafOfModules.free (R :=
        (R.over X).over U) (ULift.{u} (Fin n)) ⟶ M.over U :=
      eFn.hom ≫ F.map φ
    have hlTarget : l ≫ qU = target := by
      exact hl
    let e : Limits.kernel d ⟶ Limits.kernel target := by
      dsimp only [d]
      change Limits.kernel (biprod.desc
          (l : _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin n)) ⟶
            _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin m)))
          (-((rU : _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin a)) ⟶
            Limits.kernel qU) ≫ Limits.kernel.ι qU))) ⟶
        Limits.kernel
          (target : _root_.SheafOfModules.free (R :=
              (R.over X).over U) (ULift.{u} (Fin n)) ⟶ M.over U)
      exact kernelBiprodComparison
        (A := _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin a)))
        (B := _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin m)))
        (F := _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin n)))
        (N := M.over U) (q := (qU : _root_.SheafOfModules.free (R := (R.over X).over U)
          (ULift.{u} (Fin m)) ⟶ M.over U))
        (r := (rU : _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin a)) ⟶
          Limits.kernel qU))
        (l := (l : _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin n)) ⟶
          _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin m))))
        (φ := (target : _root_.SheafOfModules.free (R :=
            (R.over X).over U) (ULift.{u} (Fin n)) ⟶ M.over U))
        (hl := hlTarget)
    have he : Epi e := by
      dsimp only [e, d]
      change Epi (kernelBiprodComparison
        (A := _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin a)))
        (B := _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin m)))
        (F := _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin n)))
        (N := M.over U)
        (q := (qU : _root_.SheafOfModules.free (R :=
            (R.over X).over U) (ULift.{u} (Fin m)) ⟶ M.over U))
        (r := (rU : _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin a)) ⟶
          Limits.kernel qU))
        (l := (l : _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin n)) ⟶
          _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin m))))
        (φ := (target : _root_.SheafOfModules.free (R :=
            (R.over X).over U) (ULift.{u} (Fin n)) ⟶ M.over U))
        (hl := hlTarget))
      exact epi_kernelBiprodComparison
        (A := _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin a)))
        (B := _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin m)))
        (F := _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin n)))
        (N := M.over U)
        (q := (qU : _root_.SheafOfModules.free (R :=
            (R.over X).over U) (ULift.{u} (Fin m)) ⟶ M.over U))
        (r := (rU : _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin a)) ⟶
          Limits.kernel qU))
        (l := (l : _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin n)) ⟶
          _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin m))))
        (φ := (target : _root_.SheafOfModules.free (R :=
            (R.over X).over U) (ULift.{u} (Fin n)) ⟶ M.over U))
        (hl := hlTarget)
    have hkt : _root_.SheafOfModules.IsFiniteType (R := (R.over X).over U)
        (Limits.kernel target) := isFiniteType_of_epi' e
    let eφ : Limits.kernel target ≅ (Limits.kernel φ).over U := by
      dsimp only [target]
      exact Limits.kernel.mapIso
        ((finiteFreeOverIso (R.over X) U n).hom ≫
          (_root_.SheafOfModules.overFunctor (R.over X) U).map φ)
        ((_root_.SheafOfModules.overFunctor (R.over X) U).map φ)
        (finiteFreeOverIso (R.over X) U n) (Iso.refl _) (by simp) ≪≫
        (PreservesKernel.iso (_root_.SheafOfModules.overFunctor (R.over X) U) φ).symm
    obtain ⟨D, hD⟩ :=
      _root_.SheafOfModules.IsFiniteType.exists_localGeneratorsData (Limits.kernel target)
    have piece' : ∀ j : D.I,
        ∃ G : (((Limits.kernel φ).over U).over (D.X j)).GeneratingSections,
          G.IsFiniteType := by
      intro j
      have hj : (D.generators j).IsFiniteType := hD.isFiniteType j
      have : Epi eφ.hom := inferInstance
      exact ⟨(D.generators j).ofEpi ((_root_.SheafOfModules.overFunctor ((R.over X).over U) (D.X
          j)).map eφ.hom),
        ⟨hj.finite⟩⟩
    choose gen hgen using piece'
    exact ⟨⟨D.I, D.X, D.coversTop, gen⟩, ⟨fun j => hgen j⟩⟩
  choose data hdata using piece
  have hcover' := hcover.over (I' := fun i => (data i).I)
    (Y := fun i j => (data i).X j) (fun i => (data i).coversTop)
  have piece' : ∀ z : (i : I) × (data i).I,
      ∃ G : ((Limits.kernel φ).over (((data z.1).X z.2).left)).GeneratingSections,
        G.IsFiniteType := by
    intro z
    have := (hdata z.1).isFiniteType z.2
    exact kernelPieceGeneratorsOver (Limits.kernel φ) (Y z.1) ((data z.1).X z.2)
      ((Limits.kernel φ).over (Y z.1)) (𝟙 _) ((data z.1).generators z.2)
  choose gen hgen using piece'
  let assembled : (Limits.kernel φ).LocalGeneratorsData.{max u v₁} :=
    ⟨(i : I) × (data i).I,
      fun z => ((data z.1).X z.2).left, hcover', gen⟩
  have hAssembled : assembled.IsFiniteType := ⟨fun z => hgen z⟩
  refine ⟨assembled.shrink, ?_⟩
  exact { isFiniteType := fun i => hAssembled.isFiniteType (i.2.choose) }

omit [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
theorem isCoherent_iff_isFinitePresentation_of_isCoherentRing
    [IsCoherentRing (R := R)] (M : SheafOfModules.{u} R) :
    IsCoherent (R := R) M ↔ _root_.SheafOfModules.IsFinitePresentation (R := R) M := by
  constructor
  · intro h
    have := h
    infer_instance
  · intro h
    let : _root_.SheafOfModules.IsFinitePresentation (R := R) M := h
    constructor
    · infer_instance
    · intro X n phi
      classical
      have hstrong₂ : ∀ U : Over X,
          HasSheafify ((J.over X).over U) AddCommGrpCat.{u} :=
        fun U => hasSheafifyIteratedSlice J X U
      obtain ⟨q, hq⟩ := _root_.SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
      let I₀ : Type _ := Σ (U : Over X) (i : q.I), U.left ⟶ q.X i
      let Y₀ : I₀ → Over X := fun p => p.1
      have hcover : (J.over X).CoversTop Y₀ := by
        intro W
        have hT : (Sieve.overEquiv W).symm (Sieve.ofObjects q.X W.left) ∈
            (J.over X) W :=
          J.overEquiv_symm_mem_over W _ (q.coversTop W.left)
        apply (J.over X).superset_covering
          (S := (Sieve.overEquiv W).symm (Sieve.ofObjects q.X W.left)) _ hT
        intro U a ha
        obtain ⟨i, ⟨f⟩⟩ := (Sieve.mem_ofObjects_iff _ _).mp
          ((Sieve.overEquiv_symm_iff _ _).mp ha)
        exact ⟨⟨U, i, f⟩, ⟨𝟙 U⟩⟩
      have piece : ∀ i₀ : I₀,
          ∃ D : ((Limits.kernel phi).over (Y₀ i₀)).LocalGeneratorsData,
            D.IsFiniteType := by
        rintro ⟨U, i, f⟩
        have hPi : (q.presentation i).IsFinite := hq.isFinite_presentation i
        let P₁ := (q.presentation i).mapOfPreserves
          (_root_.SheafOfModules.overMap R f)
          (_root_.SheafOfModules.overMapUnitIso f).symm
          (preservesColimit_parallelPair_overMap _ f)
        have hP₁ : P₁.IsFinite := inferInstance
        let e₁ := (_root_.SheafOfModules.overFunctorMap R f).app M
        let P₂ : (M.over U.left).Presentation := P₁.ofIsIso e₁.hom
        have hP₂ : P₂.IsFinite := inferInstance
        let E := kernelIteratedSliceEquiv (R := R) X U
        have hEinvCol : PreservesColimitsOfSize.{u, u} E.inverse := inferInstance
        let phiS : _root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin n)) ⟶
            (M.over X).over U :=
          (finiteFreeOverIso (R.over X) U n).hom ≫
            (_root_.SheafOfModules.overFunctor (R.over X) U).map phi
        let eF : _root_.SheafOfModules.free (R := R.over U.left) (ULift.{u} (Fin n)) ≅
            E.inverse.obj
              (_root_.SheafOfModules.free (R := (R.over X).over U) (ULift.{u} (Fin n))) :=
          weakMapFreeIso E.inverse _ (Iso.refl _)
        have hpreM : E.functor.obj (E.inverse.obj ((M.over X).over U)) ≅
            E.functor.obj (M.over U.left) := E.counitIso.app _
        let eM : E.inverse.obj ((M.over X).over U) ≅ M.over U.left :=
          E.fullyFaithfulFunctor.preimageIso hpreM
        let d : _root_.SheafOfModules.free (R :=
            R.over U.left) (ULift.{u} (Fin n)) ⟶ M.over U.left :=
          eF.hom ≫ E.inverse.map phiS ≫ eM.hom
        have hd : _root_.SheafOfModules.IsFiniteType (R := R.over U.left) (Limits.kernel d) :=
          localPresentationKernelFiniteTypeOver P₂ d
        obtain ⟨δ, hδ⟩ := hd.exists_localGeneratorsData
        let ek₀ : Limits.kernel d ≅ Limits.kernel (E.inverse.map phiS) :=
          Limits.kernel.mapIso d (E.inverse.map phiS) eF eM.symm
            (by dsimp only [d]; simp)
        let ek₁ : E.functor.obj (Limits.kernel d) ≅ Limits.kernel phiS :=
          E.functor.mapIso ek₀ ≪≫
            PreservesKernel.iso E.functor (E.inverse.map phiS) ≪≫
            Limits.kernel.mapIso (E.functor.map (E.inverse.map phiS)) phiS
              (E.counitIso.app _) (E.counitIso.app _)
              (E.counitIso.hom.naturality phiS)
        let ephi : Limits.kernel phiS ≅ (Limits.kernel phi).over U :=
          Limits.kernel.mapIso phiS ((_root_.SheafOfModules.overFunctor (R.over X) U).map phi)
            (finiteFreeOverIso (R.over X) U n) (Iso.refl _) (by simp [phiS]) ≪≫
            (PreservesKernel.iso (_root_.SheafOfModules.overFunctor (R.over X) U) phi).symm
        let ek : E.functor.obj (Limits.kernel d) ≅ (Limits.kernel phi).over U :=
          ek₁ ≪≫ ephi
        let backward : Over U.left ⥤ Over U :=
          (Over.iteratedSliceEquiv U).symm.functor
        let forward : Over U ⥤ Over U.left :=
          (Over.iteratedSliceEquiv U).functor
        let V : δ.I → Over U := fun j => backward.obj (δ.X j)
        have hV : ((J.over X).over U).CoversTop V :=
          GrothendieckTopology.CoversTop.iteratedSliceEquiv_inverse U δ.coversTop
        have hcontB : backward.IsContinuous (J.over U.left)
            ((J.over X).over U) := by
          change U.iteratedSliceBackward.IsContinuous _ _
          infer_instance
        have hcpB : CoverPreserving (J.over U.left)
            ((J.over X).over U) backward :=
          CoverPreserving.of_isContinuous _ _ _
        have hcontF : forward.IsContinuous ((J.over X).over U)
            (J.over U.left) := by
          change U.iteratedSliceForward.IsContinuous _ _
          infer_instance
        have hcpF : CoverPreserving ((J.over X).over U)
            (J.over U.left) forward :=
          CoverPreserving.of_isContinuous _ _ _
        have pieces : ∀ j : δ.I,
            ∃ G : (((Limits.kernel phi).over U).over (V j)).GeneratingSections,
              G.IsFiniteType := by
          intro j
          have hcpPost : CoverPreserving ((J.over U.left).over (δ.X j))
              (((J.over X).over U).over (V j))
              (Over.postEquiv (Over.iteratedSliceEquiv U).symm
                (X := δ.X j)).functor :=
            CoverPreserving.overPost _ hcpB
          have hcontPost : (Over.postEquiv (Over.iteratedSliceEquiv U).symm
              (X := δ.X j)).functor.IsContinuous
              ((J.over U.left).over (δ.X j))
              (((J.over X).over U).over (V j)) :=
            Functor.isContinuous_of_coverPreserving
              (Functor.IsCoverDense.compatiblePreserving _ _) hcpPost
          have hcpBack : CoverPreserving (((J.over X).over U).over (V j))
              ((J.over U.left).over (forward.obj (V j))) (Over.post forward) :=
            CoverPreserving.overPost _ hcpF
          have hcpMap : CoverPreserving
              ((J.over U.left).over (forward.obj (V j)))
              ((J.over U.left).over (δ.X j))
              (Over.map ((Over.iteratedSliceEquiv U).symm.unitIso.inv.app (δ.X j))) :=
            CoverPreserving.of_isContinuous _ _ _
          have hcpInv : CoverPreserving (((J.over X).over U).over (V j))
              ((J.over U.left).over (δ.X j))
              (Over.postEquiv (Over.iteratedSliceEquiv U).symm
                (X := δ.X j)).inverse :=
            CoverPreserving.comp _ _ hcpBack hcpMap
          have hcontInv : (Over.postEquiv (Over.iteratedSliceEquiv U).symm
              (X := δ.X j)).inverse.IsContinuous
              (((J.over X).over U).over (V j))
              ((J.over U.left).over (δ.X j)) :=
            Functor.isContinuous_of_coverPreserving
              (Functor.IsCoverDense.compatiblePreserving _ _) hcpInv
          let Ej : SheafOfModules.{u} ((R.over U.left).over (δ.X j)) ≌
              SheafOfModules.{u} (((R.over X).over U).over (V j)) :=
            (_root_.SheafOfModules.pushforwardPushforwardEquivalence
              (Over.postEquiv (Over.iteratedSliceEquiv U).symm (X := δ.X j))
              (S := ((R.over U.left).over (δ.X j)))
              (R := (((R.over X).over U).over (V j)))
              (𝟙 _) (𝟙 _) (by ext : 2; exact R.1.map_id _)
              (by ext : 2; exact R.1.map_id _)).symm
          have hEjCol : PreservesColimitsOfSize.{u, u} Ej.functor := inferInstance
          have hjfin : (δ.generators j).IsFiniteType := hδ.isFiniteType j
          have Cj : Ej.functor.obj ((Limits.kernel d).over (δ.X j)) ≅
              (E.functor.obj (Limits.kernel d)).over (V j) := Iso.refl _
          let ej : Ej.functor.obj ((Limits.kernel d).over (δ.X j)) ≅
              ((Limits.kernel phi).over U).over (V j) :=
            Cj ≪≫ (_root_.SheafOfModules.overFunctor ((R.over X).over U) (V j)).mapIso ek
          let Gj := ((δ.generators j).mapEquivalenceWeak Ej (Iso.refl _)).ofEpi ej.hom
          exact ⟨Gj, ⟨(inferInstance : (δ.generators j).IsFiniteType).finite⟩⟩
        choose gen hgen using pieces
        exact ⟨⟨δ.I, V, hV, gen⟩, ⟨fun j => ⟨(hgen j).finite⟩⟩⟩
      choose localData hlocal using piece
      have htotal := hcover.over (I' := fun i₀ => (localData i₀).I)
        (Y := fun i₀ j => (localData i₀).X j)
        (fun i₀ => (localData i₀).coversTop)
      have pieces : ∀ z : (i₀ : I₀) × (localData i₀).I,
          ∃ G : ((Limits.kernel phi).over (((localData z.1).X z.2).left)).GeneratingSections,
            G.IsFiniteType := by
        intro z
        have := (hlocal z.1).isFiniteType z.2
        exact kernelPieceGeneratorsOver (Limits.kernel phi) (Y₀ z.1)
          ((localData z.1).X z.2) ((Limits.kernel phi).over (Y₀ z.1))
          (𝟙 _) ((localData z.1).generators z.2)
      choose gen hgen using pieces
      let assembled : (Limits.kernel phi).LocalGeneratorsData.{max u v₁} :=
        ⟨(i₀ : I₀) × (localData i₀).I,
          fun z => ((localData z.1).X z.2).left, htotal, gen⟩
      have hAssembled : assembled.IsFiniteType := ⟨fun z => hgen z⟩
      refine ⟨assembled.shrink, ?_⟩
      exact { isFiniteType := fun i => hAssembled.isFiniteType (i.2.choose) }

end SheafOfModules

end
