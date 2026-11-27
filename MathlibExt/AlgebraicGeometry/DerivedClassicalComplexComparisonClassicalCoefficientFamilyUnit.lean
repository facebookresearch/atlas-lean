/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ClassicalComplexCoefficientMaps

/-!
# The classical coefficient family unit

Identity coefficient family maps agree with the native derived unit.
The proof normalizes coefficient units and étale adjunction mates.

References: Toën--Vaquié math/0503269v5 §3.1 pp36--37 and p8;
Stacks 03G8, 06YY, 0D6D, 0DLD/0DLE. The native ordinary-stack source
is ComplexesStack.lean at AxiomMath/Stacks
c496df0d9beea9deaeabcea8492605f9a0a2313b; its general algebraic-space
algebraicity theorem is not re-requested here.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.CosimplicialDGMappingModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedDGModuli
open MathlibExt.AlgebraicGeometry.ClassicalComplexesSourceModels
open MathlibExt.AlgebraicGeometry.DerivedOrdinaryComplexModels
open MathlibExt.AlgebraicGeometry.DerivedClassicalComplexComparisonModels
open MathlibExt.AlgebraicGeometry.EtaleComplexesPullbackCoherence
open MathlibExt.AlgebraicGeometry.ClassicalComplexCoefficientMaps
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false

universe u

attribute [local instance] HasDerivedCategory.standard

/-- The ring map of an identity algebra map is the identity ring map. -/
private theorem ring_id_of_alg_id (k : Type u) [CommRing k] (A : CommAlgCat.{u} k) :
    CommRingCat.ofHom (𝟙 A : A ⟶ A).hom.toRingHom = 𝟙 (ordinaryRing A) := by
  rfl

/-- The spectrum of an identity algebra map is the identity scheme map. -/
private theorem spec_id_of_alg_id (k : Type u) [CommRing k] (A : CommAlgCat.{u} k) :
    Spec.map (CommRingCat.ofHom (𝟙 A : A ⟶ A).hom.toRingHom) = 𝟙 (Spec (ordinaryRing A)) := by
  rw [ring_id_of_alg_id]
  exact Spec.map_id _

/-- The underived moduli functor preserves identity maps. -/
private theorem moduli_map_id_of_alg_id (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (R : DGFrame k (oppositeCategory (scalarCategory k))) (P : StrictPerfectSystem N S)
    (A : CommAlgCat.{u} k) :
    (underivedModuliFunctor R P).map (𝟙 A) = 𝟙 ((underivedModuliFunctor R P).obj A) := by
  exact (underivedModuliFunctor R P).map_id A

/-- The identity moduli map fixes every vertex. -/
private theorem vertex_fixed_of_map_id (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (R : DGFrame k (oppositeCategory (scalarCategory k))) (P : StrictPerfectSystem N S)
    (A : CommAlgCat.{u} k) (E : ((underivedModuliFunctor R P).obj A) _⦋0⦌) :
    (((underivedModuliFunctor R P).map (𝟙 A)).app (op ⦋0⦌) E) = E := by
  exact congrArg (fun f => f.app (op ⦋0⦌) E) (moduli_map_id_of_alg_id k N S R P A)

private theorem coefficient_map_id (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (A : SAlg k) :
    coefficientMap N (𝟙 A) = 𝟙 (coefficientCategory N A) := by
  dsimp only [coefficientMap, coefficientCategory]
  rw [CategoryTheory.Functor.map_id]
  apply EnrichedFunctor.ext (Cochains k) (fun x => by cases x; rfl)
  intro x y
  change 𝟙 (N.functor.obj A).X = 𝟙 (N.functor.obj A).X
  rfl

private theorem restriction_id_object (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N) (A : SAlg k)
    (M : RightModule k (coefficientCategory N A)) :
    (S.restriction A A (𝟙 A)).functor.obj M = M := by
  rw [(S.restriction A A (𝟙 A)).object_eq]
  rw [coefficient_map_id]
  apply DGFunctor.ext
  apply EnrichedFunctor.ext (Cochains k) (fun _ => rfl)
  intro x y
  simp [MathlibExt.CategoryTheory.DGScalarExtensionModels.restrictModule,
    EnrichedFunctor.comp]

private theorem dgApp_heq_of_heq (k : Type u) [CommRing k]
    (C : DGCat k) (F G H : RightModule k C) (hGH : G = H)
    (a : DGHom k 0 F G) (b : DGHom k 0 F H) (hab : HEq a b) (x : Cᵒᵖ) :
    HEq (DGFunctor.dgApp k 0 x a) (DGFunctor.dgApp k 0 x b) := by
  subst H
  cases eq_of_heq hab
  rfl

private theorem unit_component_id (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (P : StrictPerfectSystem N S) (A : SAlg k) (x : P.functor.obj A) :
    HEq (DGFunctor.dgApp k (C := (coefficientCategory N A)ᵒᵖ)
      0 (op PUnit.unit) (P.unit A A (𝟙 A) x))
      (dgId k (((P.realization A).obj x).obj.toEnrichedFunctor.obj (op PUnit.unit))) := by
  have ht : (S.restriction A A (𝟙 A)).functor.obj
      ((P.realization A).obj ((P.functor.map (𝟙 A)).obj x)).obj =
        ((P.realization A).obj x).obj := by
    rw [restriction_id_object]
    rw [P.functor.map_id]
    rfl
  exact (dgApp_heq_of_heq k (coefficientCategory N A) _ _ _ ht
    (P.unit A A (𝟙 A) x) (dgId k ((P.realization A).obj x).obj)
    (P.unit_identity A x) (op PUnit.unit)).trans
      (heq_of_eq (DGFunctor.dgApp_dgId k _ _))

private theorem cochainEval_heq_of_heq (k : Type u) [CommRing k]
    (K L M : CochainComplex (ModuleCat.{u} k) ℤ) (hLM : L = M)
    (a : DGHom k 0 K L) (b : DGHom k 0 K M) (hab : HEq a b)
    (n : ℤ) (x : K.X n) : HEq (cochainEval k x 0 n (by omega) a)
      (cochainEval k x 0 n (by omega) b) := by
  subst M
  cases eq_of_heq hab
  rfl

private theorem unit_eval_id (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (P : StrictPerfectSystem N S) (A : SAlg k) (x : P.functor.obj A)
    (n : ℤ) (y : (((P.realization A).obj x).obj.toEnrichedFunctor.obj (op PUnit.unit)).X n) :
    HEq (cochainEval k y 0 n (by omega)
      (DGFunctor.dgApp k (C := (coefficientCategory N A)ᵒᵖ)
        0 (op PUnit.unit) (P.unit A A (𝟙 A) x))) y := by
  have ht : (S.restriction A A (𝟙 A)).functor.obj
      ((P.realization A).obj ((P.functor.map (𝟙 A)).obj x)).obj =
        ((P.realization A).obj x).obj := by
    rw [restriction_id_object, P.functor.map_id]
    rfl
  have h := cochainEval_heq_of_heq k _ _ _
    (congrArg (fun M => M.toEnrichedFunctor.obj (op PUnit.unit)) ht)
    _ _ (unit_component_id k N S P A x) n y
  exact h.trans (heq_of_eq (by
    simp [cochainEval_apply, dgId_linearHomComplex]))

private theorem eqToIso_f_apply_heq (k : Type u) [CommRing k]
    (K L : CochainComplex (ModuleCat.{u} k) ℤ) (hKL : K = L)
    (n : ℤ) (x : K.X n) : HEq (((eqToIso hKL).hom.f n).hom x) x := by
  subst L
  rfl

private theorem restricted_value_hom_apply_heq (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (A B : CommAlgCat.{u} k) (f : A ⟶ B)
    (M : RightModule k (coefficientCategory N (ordinaryAlgebras.obj B)))
    (n : ℤ) (x : (((S.restriction (ordinaryAlgebras.obj A) (ordinaryAlgebras.obj B)
      (ordinaryAlgebras.map f)).functor.obj M).toEnrichedFunctor.obj (op PUnit.unit)).X n) :
    HEq (((restrictedCoefficientValueIso S f M).hom.f n).hom x) x := by
  have h : ((S.restriction (ordinaryAlgebras.obj A) (ordinaryAlgebras.obj B)
      (ordinaryAlgebras.map f)).functor.obj M).toEnrichedFunctor.obj (op PUnit.unit) =
        M.toEnrichedFunctor.obj (op PUnit.unit) := by
    rw [(S.restriction (ordinaryAlgebras.obj A) (ordinaryAlgebras.obj B)
      (ordinaryAlgebras.map f)).object_eq]
    rfl
  exact eqToIso_f_apply_heq k _ _ h n x

private theorem underlying_iso_heq_injective (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (A : CommAlgCat.{u} k)
    (C : OrdinaryCoefficientSource N A) (V : OrdinaryModuleSource C)
    (M M' : RightModule k (coefficientCategory N (ordinaryAlgebras.obj A)))
    (hMM' : M = M') (n : ℤ) (x : (V.functor.obj M).X n) (y : (V.functor.obj M').X n)
    (h : HEq (((V.underlyingIso.hom.app M).f n).hom x)
      (((V.underlyingIso.hom.app M').f n).hom y)) : HEq x y := by
  subst M'
  apply heq_of_eq
  have h' := congrArg (fun z => ((V.underlyingIso.inv.app M).f n).hom z) (eq_of_heq h)
  simpa only [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f,
    Iso.hom_inv_id_app, HomologicalComplex.id_f, ModuleCat.id_apply] using h'

private theorem ordinary_identity_unit_value (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (R : DGFrame k (oppositeCategory (scalarCategory k))) (r : ScalarFramePoint R)
    (P : StrictPerfectSystem N S) (O : ∀ X : Scheme.{u}, EtaleStructureSource X)
    (L : EtalePullbackSystem O) (Z : OrdinaryComplexSourceSystem r P O L)
    (D : CoefficientMapSystem Z) (A : CommAlgCat.{u} k)
    (E : ((underivedModuliFunctor R P).obj A) _⦋0⦌)
    (n : ℤ) (x : (vertexOrdinaryComplex r P A (Z.module A) E).X n) :
    HEq (((D.ordinary (𝟙 A) E).map.f n).hom
      ((ModuleCat.ExtendRestrictScalarsAdj.Unit.map (𝟙 A : A ⟶ A).hom.toRingHom).hom x)) x := by
  have h := (D.ordinary (𝟙 A) E).unit_eq n x
  have hu := unit_eval_id k N S P (ordinaryAlgebras.obj A) (E.obj r.point) n
    ((((Z.module A).underlyingIso.hom.app (vertexModule r P A E)).f n).hom x)
  have he := restricted_value_hom_apply_heq k N S A A (𝟙 A)
    (vertexModule r P A (((underivedModuliFunctor R P).map (𝟙 A)).app (op ⦋0⦌) E)) n
    (cochainEval k ((((Z.module A).underlyingIso.hom.app (vertexModule r P A E)).f n).hom x)
      0 n (by omega)
      (DGFunctor.dgApp k (C := (coefficientCategory N (ordinaryAlgebras.obj A))ᵒᵖ)
        0 (op PUnit.unit) (P.unit (ordinaryAlgebras.obj A) (ordinaryAlgebras.obj A)
          (ordinaryAlgebras.map (𝟙 A)) (E.obj r.point))))
  apply (underlying_iso_heq_injective k N A (Z.coefficient A) (Z.module A)
    _ _ (congrArg (vertexModule r P A) (vertex_fixed_of_map_id k N S R P A E)) n _ x)
  exact (heq_of_eq h).trans (he.trans (by
    exact hu))

private theorem global_pullback_identity (X : Scheme.{u}) (M : X.Modules)
    (x : Γ(M, ⊤)) :
    (((Scheme.Modules.pullbackId X).hom.app M).app ⊤)
      ((globalPullbackUnit (𝟙 X) M) x) = x := by
  have h := congrArg (fun α => α.app M) (Scheme.Modules.conjugateEquiv_pullbackId_hom X)
  have h' : (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app M ≫
      (Scheme.Modules.pushforward (𝟙 X)).map ((Scheme.Modules.pullbackId X).hom.app M) =
        (Scheme.Modules.pushforwardId X).inv.app M := by
    simpa [conjugateEquiv_apply_app] using h
  have hx := congrArg (fun a => (a.app ⊤) x) h'
  simpa [globalPullbackUnit] using hx

private theorem tilde_pullback_hom_ext (A : CommRingCat.{u}) (M N : ModuleCat.{u} A)
    (a b : (Scheme.Modules.pullback (𝟙 (Spec A))).obj ((tilde.functor A).obj M) ⟶
      (tilde.functor A).obj N)
    (h : ∀ x : M,
      (a.app ⊤) ((globalPullbackUnit (𝟙 (Spec A)) ((tilde.functor A).obj M))
        ((tilde.isoTop M).hom.hom x)) =
      (b.app ⊤) ((globalPullbackUnit (𝟙 (Spec A)) ((tilde.functor A).obj M))
        ((tilde.isoTop M).hom.hom x))) : a = b := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 (Spec A))).homEquiv _ _).injective
  apply ((tilde.adjunction (R := A)).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  ext x
  change (a.app ⊤)
      (((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 (Spec A))).unit.app
        ((tilde.functor A).obj M)).app ⊤ ((tilde.isoTop M).hom.hom x)) =
    (b.app ⊤)
      (((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 (Spec A))).unit.app
        ((tilde.functor A).obj M)).app ⊤ ((tilde.isoTop M).hom.hom x))
  simpa [globalPullbackUnit] using h x

private theorem tilde_coefficient_component (A B : CommRingCat.{u}) (f : A ⟶ B)
    (T : TildeAffinePullbackSource f)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (K' : CochainComplex (ModuleCat.{u} B) ℤ)
    (a : ((ModuleCat.extendScalars f.hom).mapHomologicalComplex (.up ℤ)).obj K ⟶ K') (n : ℤ) :
    (tildeCoefficientMap T a).f n =
      T.iso.hom.app (K.X n) ≫ (tilde.functor B).map (a.f n) := by
  simp [tildeCoefficientMap]

private theorem tilde_map_top (A : CommRingCat.{u}) (M N : ModuleCat.{u} A)
    (a : M ⟶ N) (x : M) :
    (((tilde.functor A).map a).app ⊤) ((tilde.isoTop M).hom.hom x) =
      (tilde.isoTop N).hom.hom (a.hom x) := by
  have h := congrArg (fun q => q.hom x) (tilde.toOpen_map_app a ⊤)
  exact h

private theorem tilde_unit_top (A B : CommRingCat.{u}) (f : A ⟶ B)
    (T : TildeAffinePullbackSource f) (M : ModuleCat.{u} A) (x : M) :
    ((T.iso.hom.app M).app ⊤)
      ((globalPullbackUnit (Spec.map f) ((tilde.functor A).obj M))
        ((tilde.isoTop M).hom.hom x)) =
      (tilde.isoTop ((ModuleCat.extendScalars f.hom).obj M)).hom.hom
        ((ModuleCat.ExtendRestrictScalarsAdj.Unit.map f.hom).hom x) := by
  have h := congrArg (fun q => (tilde.isoTop ((ModuleCat.extendScalars f.hom).obj M)).hom.hom q)
    (T.unit_eq M x)
  simpa only [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply] using h

private theorem tilde_top_heq (A : CommRingCat.{u}) (M N : ModuleCat.{u} A)
    (hMN : M = N) (x : M) (y : N) (hxy : HEq x y) :
    HEq ((tilde.isoTop M).hom.hom x) ((tilde.isoTop N).hom.hom y) := by
  subst N
  cases eq_of_heq hxy
  rfl

private theorem tilde_pullback_hom_heq (A : CommRingCat.{u})
    (g : Spec A ⟶ Spec A) (hg : g = 𝟙 (Spec A)) (M N : ModuleCat.{u} A) (hNM : N = M)
    (a : (Scheme.Modules.pullback g).obj ((tilde.functor A).obj M) ⟶ (tilde.functor A).obj N)
    (h : ∀ x : M, HEq
      ((a.app ⊤) ((globalPullbackUnit g ((tilde.functor A).obj M)) ((tilde.isoTop M).hom.hom x)))
      ((((Scheme.Modules.pullbackId (Spec A)).hom.app ((tilde.functor A).obj M)).app ⊤)
        ((globalPullbackUnit (𝟙 (Spec A)) ((tilde.functor A).obj M))
          ((tilde.isoTop M).hom.hom x)))) :
    HEq a ((Scheme.Modules.pullbackId (Spec A)).hom.app ((tilde.functor A).obj M)) := by
  subst g
  subst N
  apply heq_of_eq
  apply tilde_pullback_hom_ext
  exact fun x => eq_of_heq (h x)

private theorem tilde_identity_component (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (R : DGFrame k (oppositeCategory (scalarCategory k))) (r : ScalarFramePoint R)
    (P : StrictPerfectSystem N S) (O : ∀ X : Scheme.{u}, EtaleStructureSource X)
    (L : EtalePullbackSystem O) (Z : OrdinaryComplexSourceSystem r P O L)
    (D : CoefficientMapSystem Z) (A : CommAlgCat.{u} k)
    (E : ((underivedModuliFunctor R P).obj A) _⦋0⦌) (n : ℤ) :
    HEq ((tildeCoefficientMap (D.tilde (𝟙 A)) (D.ordinary (𝟙 A) E).map).f n)
      ((Scheme.Modules.pullbackId (Spec (ordinaryRing A))).hom.app
        ((tilde.functor (ordinaryRing A)).obj
          ((vertexOrdinaryComplex r P A (Z.module A) E).X n))) := by
  apply tilde_pullback_hom_heq (ordinaryRing A) _ (spec_id_of_alg_id k A) _ _
    (congrArg (fun E => (vertexOrdinaryComplex r P A (Z.module A) E).X n)
      (vertex_fixed_of_map_id k N S R P A E))
  intro x
  rw [tilde_coefficient_component]
  change HEq
    ((((tilde.functor (ordinaryRing A)).map ((D.ordinary (𝟙 A) E).map.f n)).app ⊤)
      (((D.tilde (𝟙 A)).iso.hom.app ((vertexOrdinaryComplex r P A (Z.module A) E).X n)).app ⊤
        ((globalPullbackUnit (Spec.map (CommRingCat.ofHom (𝟙 A : A ⟶ A).hom.toRingHom))
          ((tilde.functor (ordinaryRing A)).obj ((vertexOrdinaryComplex r P A (Z.module A) E).X n)))
          ((tilde.isoTop (R := ordinaryRing A)
            ((vertexOrdinaryComplex r P A (Z.module A) E).X n)).hom.hom x)))) _
  erw [tilde_unit_top (ordinaryRing A) (ordinaryRing A) _ (D.tilde (𝟙 A))
    ((vertexOrdinaryComplex r P A (Z.module A) E).X n) x]
  erw [tilde_map_top (ordinaryRing A) _ _ ((D.ordinary (𝟙 A) E).map.f n)]
  exact (tilde_top_heq (ordinaryRing A) _ _
    (congrArg (fun E => (vertexOrdinaryComplex r P A (Z.module A) E).X n)
      (vertex_fixed_of_map_id k N S R P A E)) _ x
    (ordinary_identity_unit_value k N S R r P O L Z D A E n x)).trans
      (heq_of_eq (global_pullback_identity _ _ _).symm)

private theorem etale_id_inv_apply
    (O : ∀ X : Scheme.{u}, EtaleStructureSource X) (L : EtalePullbackSystem O)
    (C : EtalePushforwardCoherence L) (X : Scheme.{u}) (M : EtaleModules O X)
    (U : X.Etale) (x : M.val.obj (op U)) :
    (((C.idIso X).inv.app M).val.app (op U)).hom x =
      M.val.presheaf.map (((C.baseId X).iso.hom.app U).op) x := by
  have h := congrArg
    (fun q => M.val.presheaf.map (((C.baseId X).iso.hom.app U).op)
      (q ((((C.idIso X).inv.app M).val.app (op U)).hom x))) (C.id_eq X M U)
  have hi := congrArg (fun a => ((a.val.app (op U)).hom x)) ((C.idIso X).inv_hom_id_app M)
  have hi' : (((C.idIso X).hom.app M).val.app (op U)).hom
      ((((C.idIso X).inv.app M).val.app (op U)).hom x) = x := by
    exact hi
  change M.val.presheaf.map (((C.baseId X).iso.hom.app U).op)
      ((((C.idIso X).hom.app M).val.app (op U)).hom
        ((((C.idIso X).inv.app M).val.app (op U)).hom x)) = _ at h
  rw [hi'] at h
  have hh : M.val.presheaf.map (((C.baseId X).iso.inv.app U).op) ≫
      M.val.presheaf.map (((C.baseId X).iso.hom.app U).op) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, ← op_comp, Iso.hom_inv_id_app, op_id,
      CategoryTheory.Functor.map_id]
  have hv : M.val.presheaf.map (((C.baseId X).iso.hom.app U).op)
      (M.val.presheaf.map (((C.baseId X).iso.inv.app U).op)
        ((((C.idIso X).inv.app M).val.app (op U)).hom x)) =
      (((C.idIso X).inv.app M).val.app (op U)).hom x := by
    exact congrArg (fun q => q ((((C.idIso X).inv.app M).val.app (op U)).hom x)) hh
  exact hv.symm.trans h.symm

private theorem native_test_pasting (A : CommRingCat.{u})
    (B : EtaleBaseChangeUnitSource (Spec A)) (g : Spec A ⟶ Spec A) (hg : g = 𝟙 (Spec A))
    (M : ModuleCat.{u} A)
    (a : (Scheme.Modules.pullback g).obj ((tilde.functor A).obj M) ⟶ (tilde.functor A).obj M)
    (ha : HEq a ((Scheme.Modules.pullbackId (Spec A)).hom.app ((tilde.functor A).obj M)))
    (U : (Spec A).Etale) :
    HEq (globalPullbackUnit (pullback.fst U.hom g)
        ((Scheme.Modules.pullback U.hom).obj ((tilde.functor A).obj M)) ≫
      ((Scheme.Modules.pullbackComp (pullback.fst U.hom g) U.hom ≪≫
        Scheme.Modules.pullbackCongr (pullback.condition (f := U.hom) (g := g)) ≪≫
        (Scheme.Modules.pullbackComp (pullback.snd U.hom g) g).symm).hom.app
          ((tilde.functor A).obj M)).app ⊤ ≫
      ((Scheme.Modules.pullback (pullback.snd U.hom g)).map a).app ⊤)
      (zarEtaleRestriction A M (B.iso.hom.app U)) := by
  subst g
  rw [eq_of_heq ha]
  let b : (etaleBaseChange (𝟙 (Spec A))).obj U ⟶ U :=
    MorphismProperty.Over.homMk (pullback.fst U.hom (𝟙 (Spec A)))
      (by
        change pullback.fst U.hom (𝟙 (Spec A)) ≫ U.hom = pullback.snd U.hom (𝟙 (Spec A))
        simpa only [Category.comp_id] using
          pullback.condition (f := U.hom) (g := 𝟙 (Spec A)))
  have hb : B.iso.hom.app U = b := by
    apply MorphismProperty.Over.Hom.ext
    exact B.normalized U
  rw [hb]
  dsimp [zarEtaleRestriction, b]
  apply heq_of_eq
  have hu := congrArg (fun α => α.app ((tilde.functor A).obj M))
    (Scheme.Modules.pseudofunctor_left_unitality (pullback.snd U.hom (𝟙 (Spec A))))
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at hu
  simp only [← Category.assoc] at hu
  replace hu := (Category.comp_id _).symm.trans hu
  simp only [Category.assoc]
  simp only [← Scheme.Modules.Hom.comp_app]
  rw [hu]
  simp [Scheme.Modules.pullbackCongr, globalPullbackUnit, MorphismProperty.Over.homMk,
    CategoryTheory.Over.homMk]

private theorem tilde_test_identity (A : CommRingCat.{u})
    (B : EtaleBaseChangeUnitSource (Spec A))
    (K K' : CochainComplex (ModuleCat.{u} A) ℤ) (hK : K' = K)
    (a : ((Scheme.Modules.pullback (Spec.map (𝟙 A))).mapHomologicalComplex (.up ℤ)).obj
      (((tilde.functor A).mapHomologicalComplex (.up ℤ)).obj K) ⟶
        ((tilde.functor A).mapHomologicalComplex (.up ℤ)).obj K')
    (ha : ∀ n : ℤ, HEq (a.f n)
      ((Scheme.Modules.pullbackId (Spec A)).hom.app ((tilde.functor A).obj (K.X n))))
    (n : ℤ) (U : (Spec A).Etale) :
    HEq (tildeCoefficientMapAtTest (f := 𝟙 A) a n U)
      (zarEtaleRestriction A (K.X n) (B.iso.hom.app U)) := by
  subst K'
  exact native_test_pasting A B _ (Spec.map_id A) (K.X n) (a.f n) (ha n) U

private theorem etale_mate_component
    (O : ∀ X : Scheme.{u}, EtaleStructureSource X) (L : EtalePullbackSystem O)
    (A B : CommRingCat.{u}) (f : A ⟶ B)
    (K : CochainComplex (EtaleModules O (Spec A)) ℤ)
    (K' : CochainComplex (EtaleModules O (Spec B)) ℤ)
    (a : ((etaleModulePullback (L.ringed (Spec.map f))).mapHomologicalComplex (.up ℤ)).obj K ⟶ K')
    (n : ℤ) :
    (etaleCoefficientMate (L := L) f a).f n =
      (etalePullPushAdjunction (L.ringed (Spec.map f))).homEquiv (K.X n) (K'.X n) (a.f n) := by
  simp [etaleCoefficientMate, Adjunction.homEquiv_unit]

private theorem adjunction_identity_mate (C : Type*) [Category C]
    (F G : C ⥤ C) (adj : F ⊣ G) (e : G ≅ 𝟭 C) (M : C) :
    adj.homEquiv M M ((adj.leftAdjointIdIso e).hom.app M) = e.inv.app M := by
  have h := congrArg (fun α => α.app M)
    (Adjunction.conjugateEquiv_leftAdjointIdIso_hom adj e)
  simpa only [conjugateEquiv_apply_app, Adjunction.id_counit, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.comp_id, CategoryTheory.Functor.id_obj,
    CategoryTheory.Functor.comp_obj, Adjunction.homEquiv_unit] using h

private theorem raw_id_mate
    (O : ∀ X : Scheme.{u}, EtaleStructureSource X) (L : EtalePullbackSystem O)
    (C : EtalePushforwardCoherence L) (X : Scheme.{u}) (M : EtaleModules O X) :
    (etalePullPushAdjunction (L.ringed (𝟙 X))).homEquiv M M
      ((etaleRawPullbackId C X).hom.app M) = (C.idIso X).inv.app M := by
  exact adjunction_identity_mate _ _ _ (etalePullPushAdjunction (L.ringed (𝟙 X))) (C.idIso X) M

private theorem etale_map_of_test
    (O : ∀ X : Scheme.{u}, EtaleStructureSource X) (L : EtalePullbackSystem O)
    (C : EtalePushforwardCoherence L) (A : CommRingCat.{u})
    (J : AffineEtaleModuleSource O A) (g : Spec A ⟶ Spec A) (hg : g = 𝟙 (Spec A))
    (K K' : CochainComplex (ModuleCat.{u} A) ℤ) (hK : K' = K)
    (a : ((etaleModulePullback (L.ringed g)).mapHomologicalComplex (.up ℤ)).obj
      (associatedEtaleComplex J K) ⟶ associatedEtaleComplex J K')
    (h : ∀ (n : ℤ) (U : (Spec A).Etale)
      (s : (J.functor.obj (K.X n)).val.obj (op U)),
      HEq (((J.testIso ((etaleBaseChange g).obj U)).hom.app (K'.X n)).hom
        ((((etalePullPushAdjunction (L.ringed g)).homEquiv
          (J.functor.obj (K.X n)) (J.functor.obj (K'.X n)) (a.f n)).val.app (op U)).hom s))
        ((zarEtaleRestriction A (K.X n) ((C.baseId (Spec A)).iso.hom.app U))
          (((J.testIso U).hom.app (K.X n)).hom s))) :
    HEq a ((etaleRawComplexId C (Spec A)).hom.app (associatedEtaleComplex J K)) := by
  subst g K'
  apply heq_of_eq
  apply HomologicalComplex.Hom.ext
  funext n
  change a.f n = (etaleRawPullbackId C (Spec A)).hom.app (J.functor.obj (K.X n))
  apply ((etalePullPushAdjunction (L.ringed (𝟙 (Spec A)))).homEquiv _ _).injective
  erw [raw_id_mate O L C (Spec A) (J.functor.obj (K.X n))]
  apply SheafOfModules.hom_ext
  ext U s
  apply ((J.testIso ((etaleBaseChange (𝟙 (Spec A))).obj (unop U))).app
    (K.X n)).toLinearEquiv.injective
  have ht := congrArg (fun m => m s)
    (J.testRestriction (K.X n) ((C.baseId (Spec A)).iso.hom.app (unop U)))
  have hi := etale_id_inv_apply O L C (Spec A) (J.functor.obj (K.X n)) (unop U) s
  exact (eq_of_heq (h n (unop U) s)).trans (ht.symm.trans (congrArg
    (fun x => ((J.testIso ((etaleBaseChange (𝟙 (Spec A))).obj (unop U))).hom.app (K.X n)).hom x)
      hi.symm))

private theorem test_section_apply_heq (A : CommRingCat.{u})
    (g : Spec A ⟶ Spec A) (hg : g = 𝟙 (Spec A))
    (M N : ModuleCat.{u} A) (hNM : N = M) (U : (Spec A).Etale)
    (a : Γ((Scheme.Modules.pullback U.hom).obj ((tilde.functor A).obj M), ⊤) ⟶
      Γ((Scheme.Modules.pullback ((etaleBaseChange g).obj U).hom).obj
        ((tilde.functor A).obj N), ⊤))
    (b : Γ((Scheme.Modules.pullback U.hom).obj ((tilde.functor A).obj M), ⊤) ⟶
      Γ((Scheme.Modules.pullback ((etaleBaseChange (𝟙 (Spec A))).obj U).hom).obj
        ((tilde.functor A).obj M), ⊤))
    (h : HEq a b)
    (s : Γ((Scheme.Modules.pullback U.hom).obj ((tilde.functor A).obj M), ⊤)) :
    HEq (a s) (b s) := by
  subst g N
  rw [eq_of_heq h]

private theorem etale_family_raw_identity (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (R : DGFrame k (oppositeCategory (scalarCategory k))) (r : ScalarFramePoint R)
    (P : StrictPerfectSystem N S) (O : ∀ X : Scheme.{u}, EtaleStructureSource X)
    (L : EtalePullbackSystem O) (Z : OrdinaryComplexSourceSystem r P O L)
    (D : CoefficientMapSystem Z) (C : EtalePushforwardCoherence L) (A : CommAlgCat.{u} k)
    (E : ((underivedModuliFunctor R P).obj A) _⦋0⦌) :
    HEq (D.etale (𝟙 A) E).map
      ((etaleRawComplexId C (Spec (ordinaryRing A))).hom.app
        (associatedEtaleComplex (Z.etale A) (vertexOrdinaryComplex r P A (Z.module A) E))) := by
  have hK := congrArg (vertexOrdinaryComplex r P A (Z.module A))
    (vertex_fixed_of_map_id k N S R P A E)
  apply etale_map_of_test O L C (ordinaryRing A) (Z.etale A) _
    (spec_id_of_alg_id k A) _ _ hK (D.etale (𝟙 A) E).map
  intro n U s
  have hn := (D.etale (𝟙 A) E).normalized n U s
  erw [etale_mate_component] at hn
  apply (heq_of_eq hn).trans
  apply test_section_apply_heq (ordinaryRing A) _ (spec_id_of_alg_id k A) _ _
    (congrArg (fun K => K.X n) hK) U
  exact tilde_test_identity (ordinaryRing A) (C.baseId (Spec (ordinaryRing A))) _ _ hK
    (tildeCoefficientMap (D.tilde (𝟙 A)) (D.ordinary (𝟙 A) E).map)
    (tilde_identity_component k N S R r P O L Z D A E) n U

private theorem derived_id_on_complex
    (O : ∀ X : Scheme.{u}, EtaleStructureSource X) (L : EtalePullbackSystem O)
    (C : EtalePushforwardCoherence L) (X : Scheme.{u})
    (K : CochainComplex (EtaleModules O X) ℤ) :
    (etaleDerivedId C X).hom.app (DerivedCategory.Q.obj K) =
      (etaleDerivedPullbackCounit (L.derived (𝟙 X))).app K ≫
        DerivedCategory.Q.map ((etaleRawComplexId C X).hom.app K) := by
  let := (L.derived (𝟙 X)).hasLeftDerived
  let := Functor.isLeftDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso (EtaleModules O X) (.up ℤ))
    (𝟭 (EtaleDerived O X)) (etaleBeforeDerivedId C X)
  have h := Functor.leftDerivedNatTrans_app
    (etaleDerivedPullback (L.derived (𝟙 X))) (𝟭 (EtaleDerived O X))
    (etaleDerivedPullbackCounit (L.derived (𝟙 X))) (etaleBeforeDerivedId C X).hom
    (HomologicalComplex.quasiIso (EtaleModules O X) (.up ℤ)) (𝟙 _) K
  have h' : (etaleDerivedId C X).hom.app (DerivedCategory.Q.obj K) ≫
      (etaleBeforeDerivedId C X).hom.app K =
        (etaleDerivedPullbackCounit (L.derived (𝟙 X))).app K := by
    simpa only [etaleDerivedId, Functor.leftDerivedUnique, Functor.leftDerivedNatIso,
      Iso.refl_hom, NatTrans.id_app, Category.comp_id] using h
  have hi : (etaleBeforeDerivedId C X).inv.app K =
      DerivedCategory.Q.map ((etaleRawComplexId C X).hom.app K) := by
    simp [etaleBeforeDerivedId, Functor.leftUnitor, Functor.rightUnitor]
  calc
    (etaleDerivedId C X).hom.app (DerivedCategory.Q.obj K) =
        (etaleDerivedId C X).hom.app (DerivedCategory.Q.obj K) ≫
          (etaleBeforeDerivedId C X).hom.app K ≫ (etaleBeforeDerivedId C X).inv.app K := by
      simp
    _ = (etaleDerivedPullbackCounit (L.derived (𝟙 X))).app K ≫
        DerivedCategory.Q.map ((etaleRawComplexId C X).hom.app K) := by
      rw [← Category.assoc, h', hi]

private theorem derived_map_identity_heq
    (O : ∀ X : Scheme.{u}, EtaleStructureSource X) (L : EtalePullbackSystem O)
    (C : EtalePushforwardCoherence L) (X : Scheme.{u})
    (g : X ⟶ X) (hg : g = 𝟙 X)
    (K K' : CochainComplex (EtaleModules O X) ℤ) (hK : K' = K)
    (a : ((etaleModulePullback (L.ringed g)).mapHomologicalComplex (.up ℤ)).obj K ⟶ K')
    (ha : HEq a ((etaleRawComplexId C X).hom.app K)) :
    HEq ((etaleDerivedPullbackCounit (L.derived g)).app K ≫ DerivedCategory.Q.map a)
      ((etaleDerivedId C X).hom.app (DerivedCategory.Q.obj K)) := by
  subst g K'
  rw [eq_of_heq ha, ← derived_id_on_complex]

/-- Identity coefficients give the exact native derived unit, with actual functor-law transports. -/
public theorem classical_coefficient_family_unit (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (R : DGFrame k (oppositeCategory (scalarCategory k))) (r : ScalarFramePoint R)
    (P : StrictPerfectSystem N S) (O : ∀ X : Scheme.{u}, EtaleStructureSource X)
    (L : EtalePullbackSystem O) (Z : OrdinaryComplexSourceSystem r P O L)
    (D : CoefficientMapSystem Z)
    (C : EtalePushforwardCoherence L) (A : CommAlgCat.{u} k)
    (E : ((underivedModuliFunctor R P).obj A) _⦋0⦌) :
  HEq (coefficientFamilyMap D (𝟙 A) E)
    ((etaleDerivedId C (Spec (ordinaryRing A))).hom.app
      (vertexEtaleDerived r P A (Z.module A) (Z.etale A) E))
    := by
  apply derived_map_identity_heq O L C (Spec (ordinaryRing A)) _
    (spec_id_of_alg_id k A) _ _
    (congrArg (fun E => associatedEtaleComplex (Z.etale A)
      (vertexOrdinaryComplex r P A (Z.module A) E))
        (vertex_fixed_of_map_id k N S R P A E))
  exact etale_family_raw_identity k N S R r P O L Z D C A E
