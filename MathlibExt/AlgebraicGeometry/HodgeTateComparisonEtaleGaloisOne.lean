/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import MathlibExt.AlgebraicGeometry.HodgeTateComparison
import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-!
# Identity law for the étale Galois operators

The operator of the identity element of `Gal(Q̄_p/Q_p)` on the rational pro-étale
cohomology of the geometric fibre, inverse image along `id_X × Spec 1`
(`etaleGalois_one`), is the identity.

The identity operator comes from pullback along `id_X × Spec 1`, and this pullback acts as the
identity on `Ext`; the argument works for an arbitrary scheme `X` over `Q_p` and uses no
comparison theorem. The base change `id_X × Spec 1` is the identity morphism of the geometric
fibre (`galoisSchemeOperator_one`). Pullback of coefficient sheaves along an identity morphism is
naturally isomorphic to the identity functor, compatibly with the comparison maps of the
continuous coefficient sheaf and of the constant unit sheaf, so the induced map on `Ext`, and
hence on cohomology, is the identity.

Background: Peter Scholze, *p-adic Hodge theory for rigid-analytic varieties*, studies the Galois
action on the cohomology of proper smooth rigid-analytic varieties (Theorem 1.6, Corollary 1.8),
and its GAGA remark concerns proper smooth algebraic varieties. These results are context
only; the statement here is for arbitrary schemes and does not depend on them.
https://arxiv.org/abs/1205.3463
-/

namespace WantedExt.AlgebraicGeometry.HodgeTateComparison

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.HodgeTateComparison
open CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme
open MathlibExt.AlgebraicGeometry.ProEtaleCohomologyFunctoriality
open MathlibExt.AlgebraicGeometry.ContinuousAdicCoefficients
open MathlibExt.AlgebraicGeometry.AdicLinearFunctoriality
open MathlibExt.AlgebraicGeometry.GeometricAdicGaloisOperators

universe u

noncomputable section

private def baseChangeIdApp (X : Scheme.{u}) (A : X.ProEt) :
    (baseChange (𝟙 X)).obj A ≅ A := by
  haveI : IsIso (pullback.fst A.hom (𝟙 X)) := inferInstance
  let e : pullback A.hom (𝟙 X) ≅ A.left := asIso (pullback.fst A.hom (𝟙 X))
  refine MorphismProperty.Over.isoMk e ?_
  change e.hom ≫ A.hom = pullback.snd A.hom (𝟙 X)
  simp [e, pullback.condition]

private theorem baseChangeIdApp_hom_left (X : Scheme.{u}) (A : X.ProEt) :
    (baseChangeIdApp X A).hom.left = pullback.fst A.hom (𝟙 X) := rfl

private theorem baseChange_map_left (X : Scheme.{u}) {A B : X.ProEt} (g : A ⟶ B) :
    ((baseChange (𝟙 X)).map g).left =
      pullback.lift (pullback.fst A.hom (𝟙 X) ≫ g.left) (pullback.snd A.hom (𝟙 X))
        (by simp [pullback.condition]) := rfl

private def baseChangeId (X : Scheme.{u}) : baseChange (𝟙 X) ≅ 𝟭 X.ProEt :=
  NatIso.ofComponents (fun A ↦ baseChangeIdApp X A) (fun {A B} g ↦ by
    apply MorphismProperty.Over.Hom.ext
    change ((baseChange (𝟙 X)).map g).left ≫ (baseChangeIdApp X B).hom.left =
      (baseChangeIdApp X A).hom.left ≫ g.left
    simp only [baseChangeIdApp_hom_left, baseChange_map_left]
    exact pullback.lift_fst _ _ _)

private def pushforwardId (R : Type) [CommRing R] (X : Scheme.{u}) :
    pushforward R (𝟙 X) ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId' (baseChangeId X) _ _

private def pullbackId (R : Type) [CommRing R] (X : Scheme.{u}) :
    pullback R (𝟙 X) ≅ 𝟭 _ :=
  (pullbackAdjunction R (𝟙 X)).leftAdjointIdIso (pushforwardId R X)

private theorem homEquiv_pullbackId_hom_app (R : Type) [CommRing R] (X : Scheme.{u})
    (F : CoefficientSheaf X R) :
    ((pullbackAdjunction R (𝟙 X)).homEquiv _ F ((pullbackId R X).hom.app F)) =
      (pushforwardId R X).inv.app F := by
  rw [Adjunction.homEquiv_unit]
  have hfold : (pullbackId R X).hom =
      ((pullbackAdjunction R (𝟙 X)).leftAdjointIdIso (pushforwardId R X)).hom := rfl
  have hconj := Adjunction.conjugateEquiv_leftAdjointIdIso_hom
    (pullbackAdjunction R (𝟙 X)) (pushforwardId R X)
  have h2 : (conjugateEquiv Adjunction.id (pullbackAdjunction R (𝟙 X))
      (pullbackId R X).hom).app F = (pushforwardId R X).inv.app F := by
    rw [hfold, hconj]
  have h1 := unit_conjugateEquiv Adjunction.id (pullbackAdjunction R (𝟙 X))
    (pullbackId R X).hom F
  simp only [Functor.id_obj] at h1
  rw [h2] at h1
  have hid : (Adjunction.id (C := CoefficientSheaf X R)).unit.app F = 𝟙 F := rfl
  rw [hid, Category.id_comp] at h1
  exact h1.symm

private theorem pushforwardId_inv_app (R : Type) [CommRing R] (X : Scheme.{u})
    (M : Type (u + 1)) [TopologicalSpace M] [AddCommGroup M] [Module R M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] :
    (pushforwardId R X).inv.app (continuousModuleSheaf R M X) =
      coefficientPushforward R M (𝟙 X) := by
  ext U
  rfl

private theorem coefficientPullback_eq (R : Type) [CommRing R] (X : Scheme.{u})
    (M : Type (u + 1)) [TopologicalSpace M] [AddCommGroup M] [Module R M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] :
    coefficientPullback R M (𝟙 X) =
      (pullbackId R X).hom.app (continuousModuleSheaf R M X) := by
  apply Equiv.injective ((pullbackAdjunction R (𝟙 X)).homEquiv _ _)
  simp only [coefficientPullback, Equiv.apply_symm_apply]
  rw [homEquiv_pullbackId_hom_app]
  exact (pushforwardId_inv_app R X M).symm

private theorem pushforwardId_hom_app_eq (R : Type) [CommRing R] (X : Scheme.{u})
    (U : X.ProEtᵒᵖ) :
    ((pushforwardId R X).inv.app (constantUnit R X)).hom.app U =
      (constantUnit R X).obj.map ((NatTrans.op (baseChangeId X).hom).app U) := by
  have h : ((pushforwardId R X).inv.app (constantUnit R X)).hom.app U =
      𝟙 _ ≫ (constantUnit R X).obj.map ((NatTrans.op (baseChangeId X).hom).app U) :=
    rfl
  rw [h, Category.id_comp]

private theorem mate_pushforwardId_inv_app (R : Type) [CommRing R] (X : Scheme.{u}) :
    (constantSheafAdj (ProEt.topology X) (ModuleCat.{u + 1} R)
      (terminalIsTerminal (C := X.ProEt))).homEquiv _ _
      ((pushforwardId R X).inv.app (constantUnit R X)) =
    (constantSheafAdj (ProEt.topology X) (ModuleCat.{u + 1} R)
      (IsTerminal.isTerminalObj (baseChange (𝟙 X)) _ terminalIsTerminal)).unit.app _ := by
  simp only [Adjunction.homEquiv_unit, constantSheafAdj, Adjunction.comp_unit_app,
    constantPresheafAdj_unit_app, Category.id_comp, evaluation_obj_map,
    sheafSections, Functor.flip_obj_map, ObjectProperty.ι_map]
  rw [pushforwardId_hom_app_eq]
  have hnat := NatTrans.naturality
    ((sheafificationAdjunction (ProEt.topology X) (ModuleCat.{u + 1} R)).unit.app
      ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of R (ULift.{u + 1} R))))
    ((NatTrans.op (baseChangeId X).hom).app (op (⊤_ X.ProEt)))
  simp only [Functor.const_obj_map, Functor.op_obj, Opposite.unop_op,
    Functor.id_obj] at hnat
  exact hnat.symm

private theorem constantPullbackIso_hom (R : Type) [CommRing R] (X : Scheme.{u}) :
    (constantPullbackIso R (𝟙 X)).hom =
      (pullbackId R X).hom.app (constantUnit R X) := by
  simp only [constantPullbackIso, Iso.app_hom]
  apply Equiv.injective (((constantSheafAdj (ProEt.topology X) (ModuleCat.{u + 1} R)
    (terminalIsTerminal (C := X.ProEt))).comp (pullbackAdjunction R (𝟙 X))).homEquiv _ _)
  have hchar := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((constantSheafAdj (ProEt.topology X) (ModuleCat.{u + 1} R)
      (terminalIsTerminal (C := X.ProEt))).comp (pullbackAdjunction R (𝟙 X)))
    (constantSheafAdj (ProEt.topology X) (ModuleCat.{u + 1} R)
      (IsTerminal.isTerminalObj (baseChange (𝟙 X)) (⊤_ X.ProEt) terminalIsTerminal))
    (ModuleCat.of R (ULift.{u + 1} R))
  rw [hchar]
  rw [Adjunction.comp_homEquiv, Equiv.trans_apply]
  rw [homEquiv_pullbackId_hom_app]
  exact (mate_pushforwardId_inv_app R X).symm

private theorem continuousPullbackLinear_id (R : Type) [CommRing R]
    (M : Type 1) [TopologicalSpace M] [AddCommGroup M] [Module R M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    (X : Scheme.{0}) (n : ℕ) :
    continuousPullbackLinear R M (𝟙 X) n = LinearMap.id := by
  apply LinearMap.ext
  intro α
  change (Abelian.Ext.mk₀ (constantPullbackIso R (𝟙 X)).inv).comp
      (((Abelian.Ext.mapExactFunctor (pullback R (𝟙 X)) α).comp
        (Abelian.Ext.mk₀ (coefficientPullback R M (𝟙 X))) (add_zero n))) (zero_add n) = α
  rw [coefficientPullback_eq]
  rw [Abelian.Ext.mapExactFunctor_comp_mk₀_natTransApp _ (pullbackId R X).hom]
  rw [Abelian.Ext.id_mapExactFunctor]
  rw [Abelian.Ext.mk₀_comp_mk₀_assoc]
  have hE : (constantPullbackIso R (𝟙 X)).inv ≫
      (pullbackId R X).hom.app (constantUnit R X) = 𝟙 _ := by
    rw [← constantPullbackIso_hom]
    exact Iso.inv_hom_id _
  rw [hE]
  exact Abelian.Ext.mk₀_id_comp _

end

@[expose] public noncomputable section

/-- For a prime $p$, a scheme $X$ over $\mathbb{Q}_p$ and $n \in \mathbb{N}$: the operator of the
identity element of $\mathrm{Gal}(\bar{\mathbb{Q}}_p/\mathbb{Q}_p)$ on the rational pro-étale
cohomology $H^n$ of the geometric fibre $X_{\bar{\mathbb{Q}}_p}$, inverse image along
$\mathrm{id}_X \times \mathrm{Spec}\,1$ (`etaleGalois`), is the identity (functoriality of sheaf
cohomology under inverse image). -/
public theorem etaleGalois_one
    (p : ℕ) [Fact p.Prime]
    (X : Over (Spec (CommRingCat.of.{0} ℚ_[p]))) (n : ℕ) :
    etaleGalois p X 1 n = LinearMap.id := by
  unfold etaleGalois
  rw [galoisSchemeOperator_one]
  exact continuousPullbackLinear_id _ _ _ _

end

end WantedExt.AlgebraicGeometry.HodgeTateComparison
