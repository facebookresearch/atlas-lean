/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HodgeTateComparison

/-!
# Composition law for étale Galois operators

The operators on rational pro-étale cohomology given by inverse image along
`id_X × Spec σ` satisfy the multiplication law `etaleGalois_mul`.

Reference: Peter Scholze, *p-adic Hodge theory for rigid-analytic varieties*,
Corollary 1.8, p. 4, and preceding Theorem 1.6 for Galois equivariance;
the algebraic scheme case follows by the comparisons described on p. 5.
https://arxiv.org/abs/1205.3463
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace WantedExt.AlgebraicGeometry.HodgeTateComparison

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian
open _root_.Opposite _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ContinuousAdicCoefficients
open MathlibExt.AlgebraicGeometry.ProEtaleCohomologyFunctoriality
open MathlibExt.AlgebraicGeometry.HodgeTateComparison
open MathlibExt.AlgebraicGeometry.GeometricAdicGaloisOperators
open MathlibExt.AlgebraicGeometry.AdicLinearFunctoriality

private def baseChangeComp (Y : Scheme.{0}) (f g : Y ⟶ Y) :
    baseChange (f ≫ g) ≅ baseChange g ⋙ baseChange f := by
  letI : MorphismProperty.HasPullbacksAlong (@WeaklyEtale : MorphismProperty Scheme.{0}) f :=
    ⟨fun _ _ ↦ inferInstance⟩
  letI : MorphismProperty.HasPullbacksAlong (@WeaklyEtale : MorphismProperty Scheme.{0}) g :=
    ⟨fun _ _ ↦ inferInstance⟩
  letI : MorphismProperty.IsStableUnderBaseChangeAlong
      (@WeaklyEtale : MorphismProperty Scheme.{0}) f :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  letI : MorphismProperty.IsStableUnderBaseChangeAlong
      (@WeaklyEtale : MorphismProperty Scheme.{0}) g :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  exact MorphismProperty.Over.pullbackComp f g

private def pushforwardComp (R : Type) [CommRing R] (Y : Scheme.{0}) (f g : Y ⟶ Y) :
    pushforward R f ⋙ pushforward R g ≅ pushforward R (f ≫ g) :=
  Functor.sheafPushforwardContinuousComp' (baseChangeComp Y f g).symm
    (ModuleCat.{1} R) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology Y)
      (Scheme.ProEt.topology Y)

private def pullbackCompAdj (R : Type) [CommRing R] (Y : Scheme.{0}) (f g : Y ⟶ Y) :
    pullback R g ⋙ pullback R f ⊣ pushforward R (f ≫ g) :=
  ((pullbackAdjunction R g).comp (pullbackAdjunction R f)).ofNatIsoRight
    (pushforwardComp R Y f g)

private def pullbackComp (R : Type) [CommRing R] (Y : Scheme.{0}) (f g : Y ⟶ Y) :
    pullback R (f ≫ g) ≅ pullback R g ⋙ pullback R f :=
  (pullbackAdjunction R (f ≫ g)).leftAdjointUniq (pullbackCompAdj R Y f g)

private theorem baseChangeComp_fst (Y : Scheme.{0}) (f g : Y ⟶ Y) (U : Y.ProEt) :
    ((baseChangeComp Y f g).hom.app U).left ≫
      pullback.fst (pullback.snd U.hom g) f ≫ pullback.fst U.hom g =
        pullback.fst U.hom (f ≫ g) := by
  unfold baseChangeComp
  exact MorphismProperty.Over.pullbackComp_left_fst_fst f g U

private theorem coefficientPushforward_comp (R : Type) [CommRing R]
    (M : Type 1) [TopologicalSpace M] [AddCommGroup M] [Module R M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    (Y : Scheme.{0}) (f g : Y ⟶ Y) :
    coefficientPushforward R M g ≫
      (pushforward R g).map (coefficientPushforward R M f) ≫
        (pushforwardComp R Y f g).hom.app (continuousModuleSheaf R M Y) =
          coefficientPushforward R M (f ≫ g) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  let a' : C(U.unop.left, M) := a
  apply ContinuousMap.ext
  intro x
  change a' ((pullback.fst U.unop.hom g).base.hom
    ((pullback.fst (pullback.snd U.unop.hom g) f).base.hom
      (((baseChangeComp Y f g).hom.app U.unop).left.base.hom x))) =
        a' ((pullback.fst U.unop.hom (f ≫ g)).base.hom x)
  exact congrArg (fun h : pullback U.unop.hom (f ≫ g) ⟶ U.unop.left ↦
    a' (h.base.hom x)) (baseChangeComp_fst Y f g U.unop)

private theorem pullbackComp_homEquiv (R : Type) [CommRing R]
    (Y : Scheme.{0}) (f g : Y ⟶ Y) (F G : CoefficientSheaf Y R)
    (c : (pullback R g ⋙ pullback R f).obj F ⟶ G) :
    (pullbackAdjunction R (f ≫ g)).homEquiv _ _
        ((pullbackComp R Y f g).hom.app F ≫ c) =
      (pullbackCompAdj R Y f g).homEquiv _ _ c := by
  dsimp only [pullbackComp]
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]

private theorem coefficientPullback_comp (R : Type) [CommRing R]
    (M : Type 1) [TopologicalSpace M] [AddCommGroup M] [Module R M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    (Y : Scheme.{0}) (f g : Y ⟶ Y) :
    (pullbackComp R Y f g).hom.app (continuousModuleSheaf R M Y) ≫
      (pullback R f).map (coefficientPullback R M g) ≫ coefficientPullback R M f =
        coefficientPullback R M (f ≫ g) := by
  apply ((pullbackAdjunction R (f ≫ g)).homEquiv _ _).injective
  rw [pullbackComp_homEquiv, pullbackCompAdj,
    Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change (pullbackAdjunction R g).homEquiv _ _
      ((pullbackAdjunction R f).homEquiv _ _
        ((pullback R f).map (coefficientPullback R M g) ≫ coefficientPullback R M f)) ≫
      (pushforwardComp R Y f g).hom.app (continuousModuleSheaf R M Y) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [coefficientPullback, Equiv.apply_symm_apply]
  exact coefficientPushforward_comp R M Y f g

private theorem constantPullbackIso_homEquiv (R : Type) [CommRing R]
    (Y : Scheme.{0}) (f : Y ⟶ Y) :
    (constantSheafAdj (Scheme.ProEt.topology Y) (ModuleCat.{1} R)
      (terminalIsTerminal (C := Y.ProEt))).homEquiv _ _
      ((pullbackAdjunction R f).homEquiv _ _ (constantPullbackIso R f).hom) =
    (constantSheafAdj (Scheme.ProEt.topology Y) (ModuleCat.{1} R)
      (IsTerminal.isTerminalObj (baseChange f) _ terminalIsTerminal)).unit.app
        (ModuleCat.of R (ULift.{1} R)) := by
  simpa only [Adjunction.comp_homEquiv, Equiv.trans_apply] using!
    Adjunction.homEquiv_leftAdjointUniq_hom_app
      ((constantSheafAdj (Scheme.ProEt.topology Y) (ModuleCat.{1} R)
        (terminalIsTerminal (C := Y.ProEt))).comp (pullbackAdjunction R f))
      (constantSheafAdj (Scheme.ProEt.topology Y) (ModuleCat.{1} R)
        (IsTerminal.isTerminalObj (baseChange f) _ terminalIsTerminal))
      (ModuleCat.of R (ULift.{1} R))

private theorem constantSheafAdj_unit (R : Type) [CommRing R]
    (Y : Scheme.{0}) (U : Y.ProEt) (hU : IsTerminal U) :
    (constantSheafAdj (Scheme.ProEt.topology Y) (ModuleCat.{1} R) hU).unit.app
        (ModuleCat.of R (ULift.{1} R)) =
      (toSheafify (Scheme.ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (ModuleCat.of R (ULift.{1} R)))).app (op U) := by
  simp [constantSheafAdj, Adjunction.comp_unit_app, constantPresheafAdj]

private theorem constantSheafAdj_homEquiv (R : Type) [CommRing R]
    (Y : Scheme.{0}) (U : Y.ProEt) (hU : IsTerminal U) (F : CoefficientSheaf Y R)
    (c : constantUnit R Y ⟶ F) :
    (constantSheafAdj (Scheme.ProEt.topology Y) (ModuleCat.{1} R) hU).homEquiv _ _ c =
      (toSheafify (Scheme.ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (ModuleCat.of R (ULift.{1} R)))).app (op U) ≫
          c.hom.app (op U) := by
  rw [Adjunction.homEquiv_unit, constantSheafAdj_unit]
  rfl

private theorem constantPullbackIso_generators (R : Type) [CommRing R]
    (Y : Scheme.{0}) (f : Y ⟶ Y) (U : Y.ProEtᵒᵖ) :
    (toSheafify (Scheme.ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (ModuleCat.of R (ULift.{1} R)))).app U ≫
      ((pullbackAdjunction R f).homEquiv _ _ (constantPullbackIso R f).hom).hom.app U =
    (toSheafify (Scheme.ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (ModuleCat.of R (ULift.{1} R)))).app
          (op ((baseChange f).obj U.unop)) := by
  let η := toSheafify (Scheme.ProEt.topology Y)
    ((Functor.const Y.ProEtᵒᵖ).obj (ModuleCat.of R (ULift.{1} R)))
  let c := (pullbackAdjunction R f).homEquiv _ _ (constantPullbackIso R f).hom
  have ht := constantPullbackIso_homEquiv R Y f
  rw [constantSheafAdj_homEquiv, constantSheafAdj_unit] at ht
  have hn := (η ≫ c.hom).naturality
    (IsTerminal.from (terminalIsTerminal (C := Y.ProEt)) U.unop).op
  have hm := η.naturality
    ((baseChange f).map (IsTerminal.from (terminalIsTerminal (C := Y.ProEt)) U.unop)).op
  dsimp only [NatTrans.comp_app, Functor.const_obj_map] at hn
  erw [Category.id_comp, ht] at hn
  simpa only [Category.id_comp] using! hn.trans hm.symm

private theorem constantPullbackIso_comp (R : Type) [CommRing R]
    (Y : Scheme.{0}) (f g : Y ⟶ Y) :
    (pullbackComp R Y f g).hom.app (constantUnit R Y) ≫
      (pullback R f).map (constantPullbackIso R g).hom ≫ (constantPullbackIso R f).hom =
        (constantPullbackIso R (f ≫ g)).hom := by
  apply ((pullbackAdjunction R (f ≫ g)).homEquiv _ _).injective
  rw [pullbackComp_homEquiv, pullbackCompAdj,
    Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change (pullbackAdjunction R g).homEquiv _ _
      ((pullbackAdjunction R f).homEquiv _ _
        ((pullback R f).map (constantPullbackIso R g).hom ≫ (constantPullbackIso R f).hom)) ≫
      (pushforwardComp R Y f g).hom.app (constantUnit R Y) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ ((pushforward R (f ≫ g)).obj (constantUnit R Y)).property
  apply NatTrans.ext
  funext U
  change (toSheafify (Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (ModuleCat.of R (ULift.{1} R)))).app U ≫
      ((pullbackAdjunction R g).homEquiv _ _ (constantPullbackIso R g).hom).hom.app U ≫
      ((pullbackAdjunction R f).homEquiv _ _ (constantPullbackIso R f).hom).hom.app
        (op ((baseChange g).obj U.unop)) ≫
      ((pushforwardComp R Y f g).hom.app (constantUnit R Y)).hom.app U =
    (toSheafify (Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (ModuleCat.of R (ULift.{1} R)))).app U ≫
      ((pullbackAdjunction R (f ≫ g)).homEquiv _ _
        (constantPullbackIso R (f ≫ g)).hom).hom.app U
  rw [← Category.assoc, constantPullbackIso_generators R Y g U,
    ← Category.assoc, constantPullbackIso_generators,
    constantPullbackIso_generators]
  change (toSheafify (Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (ModuleCat.of R (ULift.{1} R)))).app
        (op ((baseChange f).obj ((baseChange g).obj U.unop))) ≫
      (constantUnit R Y).obj.map (((baseChangeComp Y f g).hom.app U.unop).op) = _
  simpa using! (toSheafify (Scheme.ProEt.topology Y)
    ((Functor.const Y.ProEtᵒᵖ).obj (ModuleCat.of R (ULift.{1} R)))).naturality
      (((baseChangeComp Y f g).hom.app U.unop).op) |>.symm

private theorem constantPullbackIso_inv_comp (R : Type) [CommRing R]
    (Y : Scheme.{0}) (f g : Y ⟶ Y) :
    (constantPullbackIso R (f ≫ g)).inv ≫
      (pullbackComp R Y f g).hom.app (constantUnit R Y) =
        (constantPullbackIso R f).inv ≫ (pullback R f).map (constantPullbackIso R g).inv := by
  apply (cancel_epi (constantPullbackIso R (f ≫ g)).hom).mp
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← constantPullbackIso_comp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, Iso.hom_inv_id]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

private theorem ext_comp (C : Type*) [Category* C] [Abelian C] [HasExt.{1} C]
    (P Q T : C ⥤ C) [P.Additive] [Q.Additive] [T.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (e : T ≅ P ⋙ Q) (A B : C)
    (s : A ⟶ T.obj A) (sg : A ⟶ P.obj A) (sf : A ⟶ Q.obj A)
    (c : T.obj B ⟶ B) (cg : P.obj B ⟶ B) (cf : Q.obj B ⟶ B)
    (hs : s ≫ e.hom.app A = sf ≫ Q.map sg)
    (hc : e.hom.app B ≫ Q.map cg ≫ cf = c) (n : ℕ) (a : Ext.{1} A B n) :
    (Ext.mk₀ s).comp ((a.mapExactFunctor T).comp (Ext.mk₀ c) (add_zero n)) (zero_add n) =
      (Ext.mk₀ sf).comp
        ((((Ext.mk₀ sg).comp ((a.mapExactFunctor P).comp (Ext.mk₀ cg) (add_zero n))
          (zero_add n)).mapExactFunctor Q).comp (Ext.mk₀ cf) (add_zero n)) (zero_add n) := by
  rw [← hc]
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ← Ext.comp_mapExactFunctor]
  rw [← Ext.mk₀_comp_mk₀ (e.hom.app B) (Q.map cg ≫ cf),
    ← Ext.comp_assoc_of_second_deg_zero,
    Ext.mapExactFunctor_comp_mk₀_natTransApp]
  simp only [Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_mk₀, hs]

private theorem continuousCohomologyPullback_comp (R : Type) [CommRing R]
    (M : Type 1) [TopologicalSpace M] [AddCommGroup M] [Module R M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    (Y : Scheme.{0}) (f g : Y ⟶ Y) (n : ℕ)
    (a : Cohomology R Y (continuousModuleSheaf R M Y) n) :
    continuousCohomologyPullback R M (f ≫ g) n a =
      continuousCohomologyPullback R M f n (continuousCohomologyPullback R M g n a) := by
  exact ext_comp (CoefficientSheaf Y R) (pullback R g) (pullback R f) (pullback R (f ≫ g))
    (pullbackComp R Y f g) (constantUnit R Y) (continuousModuleSheaf R M Y)
    (constantPullbackIso R (f ≫ g)).inv (constantPullbackIso R g).inv
    (constantPullbackIso R f).inv (coefficientPullback R M (f ≫ g))
    (coefficientPullback R M g) (coefficientPullback R M f)
    (constantPullbackIso_inv_comp R Y f g) (coefficientPullback_comp R M Y f g) n a

private theorem continuousPullbackLinear_comp
    (p : ℕ) [Fact p.Prime] (Y : Scheme.{0}) (f g : Y ⟶ Y) (n : ℕ) :
    continuousPullbackLinear ℚ_[p] (RationalCoefficients.{0} p) (f ≫ g) n =
      continuousPullbackLinear ℚ_[p] (RationalCoefficients.{0} p) f n ∘ₗ
        continuousPullbackLinear ℚ_[p] (RationalCoefficients.{0} p) g n := by
  apply LinearMap.ext
  intro a
  exact continuousCohomologyPullback_comp ℚ_[p] (RationalCoefficients.{0} p) Y f g n a

/-- For a prime $p$, a scheme $X$ over $ℚ_p$, elements $σ, τ$ of $\mathrm{Gal}(\bar{ℚ}_p/ℚ_p)$ and
$n ∈ ℕ$: the operators on the rational pro-étale cohomology $H^n$ of the geometric fibre
$X_{\bar{ℚ}_p}$ given by inverse image along $\mathrm{id}_X × \mathrm{Spec}\,σ$ (`etaleGalois`)
form a left action: the operator of $στ$ is the operator of $σ$ composed after that of $τ$
(functoriality of sheaf cohomology, since inverse image reverses composition). -/
public theorem etaleGalois_mul
    (p : ℕ) [Fact p.Prime]
    (X : Over (Spec (CommRingCat.of.{0} ℚ_[p]))) (σ τ : Galois p) (n : ℕ) :
    etaleGalois p X (σ * τ) n = etaleGalois p X σ n ∘ₗ etaleGalois p X τ n := by
  unfold etaleGalois
  rw [galoisSchemeOperator_mul]
  exact continuousPullbackLinear_comp p _ _ _ n

end WantedExt.AlgebraicGeometry.HodgeTateComparison
