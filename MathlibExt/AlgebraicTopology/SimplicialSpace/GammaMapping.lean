/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Quasicategory.PointwiseCore
public import MathlibExt.AlgebraicTopology.SimplicialSpace.GammaDiagram
public import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerEnrichment

/-!
# The natural Gamma mapping comparison

The actual inner enriched end from the discrete inner embedding of A to the
raw core/function diagram of Q is isomorphic to core(Q^A), naturally in A
and quasicategory Q. No Gamma fibrancy or model assumption is used.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

open CategoryTheory Limits Opposite MonoidalClosed MonoidalCategory BraidedCategory
open scoped Simplicial SimplicialSpace.Inner

universe u

namespace SSet.Rezk

private def homTranspose {A K Q : SSet.{u}} (f : K ⟶ (ihom A).obj Q) :
    A ⟶ (ihom K).obj Q :=
  curry ((β_ K A).hom ≫ uncurry f)

private lemma homTranspose_pre {A A' K Q : SSet.{u}} (a : A' ⟶ A)
    (f : K ⟶ (ihom A).obj Q) :
    homTranspose (f ≫ (pre a).app Q) = a ≫ homTranspose f := by
  rw [homTranspose, uncurry_pre_app, ← Category.assoc,
    ← braiding_naturality_right, Category.assoc, curry_natural_left]
  rfl

private lemma homTranspose_homTranspose {A K Q : SSet.{u}} (f : K ⟶ (ihom A).obj Q) :
    homTranspose (homTranspose f) = f := by
  simp only [homTranspose, uncurry_curry, ← Category.assoc,
    SymmetricCategory.symmetry, Category.id_comp, curry_uncurry]

private def homTransposeEquiv (A K Q : SSet.{u}) :
    (K ⟶ (ihom A).obj Q) ≃ (A ⟶ (ihom K).obj Q) where
  toFun := homTranspose
  invFun := homTranspose
  left_inv := homTranspose_homTranspose
  right_inv := homTranspose_homTranspose


end SSet.Rezk

namespace SSet.Rezk

private abbrev gammaSpace (Q : SSet.{u}) : SimplicialSpace.{u} :=
  SimplicialSpace.ofSimplicialObject.obj (gammaDiagram.obj Q)

private abbrev discreteSpace (A : SSet.{u}) : SimplicialSpace.{u} :=
  SimplicialSpace.ofSimplicialObject.obj (SSet.simplicialSpaceDiscrete.obj A)

private def discreteSpaceMap {A A' : SSet.{u}} (a : A' ⟶ A) :
    discreteSpace A' ⟶ discreteSpace A :=
  SimplicialSpace.ofSimplicialObject.map (SSet.simplicialSpaceDiscrete.map a)

private def gammaRestriction (A Q : SSet.{u}) (m : SimplexCategoryᵒᵖ) (a : A.obj m) :
    (core ((ihom A).obj Q) : SSet.{u}) ⟶ (gammaDiagram.obj Q).obj m :=
  core.map ((pre (yonedaEquiv.symm a : stdSimplex.obj m.unop ⟶ A)).app Q)

private def constantFamilyMap (T : Type u) (K Y : SSet.{u}) (f : T → (K ⟶ Y)) :
    (SimplicialObject.const (Type u)).obj T ⊗ K ⟶ Y where
  app n := ↾fun ⟨t, k⟩ ↦ (f t).app n k
  naturality n p α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨t, k⟩
    exact NatTrans.naturality_apply (f t) α k

private def gammaCoreEvaluationComponent (A Q : SSet.{u}) (m : SimplexCategoryᵒᵖ) :
    (SSet.simplicialSpaceDiscrete.obj A).obj m ⊗ (core ((ihom A).obj Q) : SSet.{u}) ⟶
      (gammaDiagram.obj Q).obj m :=
  constantFamilyMap (A.obj m) (core ((ihom A).obj Q) : SSet.{u})
    ((gammaDiagram.obj Q).obj m) (gammaRestriction A Q m)

private lemma gammaCoreEvaluationComponent_outer (A Q : SSet.{u})
    {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n) :
    ((SSet.simplicialSpaceDiscrete.obj A).map α ▷ (core ((ihom A).obj Q) : SSet.{u})) ≫
      gammaCoreEvaluationComponent A Q n =
    gammaCoreEvaluationComponent A Q m ≫ (gammaDiagram.obj Q).map α := by
  ext p ⟨a, c⟩
  change
      (core.map
        ((pre (yonedaEquiv.symm (A.map α a) : stdSimplex.obj n.unop ⟶ A)).app Q)).app p c =
    ((core.map ((pre (stdSimplex.map α.unop)).app Q)).app p)
      ((core.map ((pre (yonedaEquiv.symm a : stdSimplex.obj m.unop ⟶ A)).app Q)).app p c)
  rw [← NatTrans.comp_app_apply, ← core.map_comp]
  have hYoneda : (yonedaEquiv.symm (A.map α a) : stdSimplex.obj n.unop ⟶ A) =
      stdSimplex.map α.unop ≫ (yonedaEquiv.symm a : stdSimplex.obj m.unop ⟶ A) := by
    simpa using (yonedaEquiv_symm_naturality_left (X := A) α.unop
      (show A.obj m from a)).symm
  rw [hYoneda]
  simp only [pre_map, NatTrans.comp_app]

private def gammaCoreEvaluation (A Q : SSet.{u}) :
    (SimplicialSpace.innerTensor (core ((ihom A).obj Q) : SSet.{u})).obj
      (discreteSpace A) ⟶ gammaSpace Q :=
  InducedCategory.homMk
    { app := gammaCoreEvaluationComponent A Q
      naturality := fun {_ _} α ↦ gammaCoreEvaluationComponent_outer A Q α }

private def gammaMappingInverse (A Q : SSet.{u}) :
    (core ((ihom A).obj Q) : SSet.{u}) ⟶
      (SimplicialSpace.innerHomFunctor.obj (op (discreteSpace A))).obj (gammaSpace Q) :=
  SimplicialSpace.innerTensorHomEquiv _ (discreteSpace A) (gammaSpace Q)
    (gammaCoreEvaluation A Q)

private lemma gammaMappingInverse_projection (A Q : SSet.{u}) (m : SimplexCategoryᵒᵖ) :
    gammaMappingInverse A Q ≫ SimplicialSpace.innerHomπ (discreteSpace A) (gammaSpace Q) m =
      curry (gammaCoreEvaluationComponent A Q m) := by
  exact SimplicialSpace.innerTensorHomEquiv_π
    (core ((ihom A).obj Q) : SSet.{u}) (discreteSpace A) (gammaSpace Q)
    (gammaCoreEvaluation A Q) m


end SSet.Rezk



namespace SSet.Rezk

private def pairAt (A K : SSet.{u}) (m : SimplexCategoryᵒᵖ) (a : A.obj m) :
    K ⟶ (SSet.simplicialSpaceDiscrete.obj A).obj m ⊗ K where
  app n := ↾fun k ↦ (a, k)
  naturality _ _ _ := by ext k; rfl

private lemma pairAt_outer (A K : SSet.{u}) {m n : SimplexCategoryᵒᵖ}
    (α : m ⟶ n) (a : A.obj m) :
    pairAt A K m a ≫ ((SSet.simplicialSpaceDiscrete.obj A).map α ▷ K) =
      pairAt A K n (A.map α a) := by
  ext p k <;> rfl

private def gammaCone {A K Q : SSet.{u}}
    (f : (SimplicialSpace.innerTensor K).obj (discreteSpace A) ⟶ gammaSpace Q)
    (m : SimplexCategoryᵒᵖ) (a : A.obj m) :
    K ⟶ (ihom (stdSimplex.obj m.unop)).obj Q :=
  pairAt A K m a ≫ f.hom.app m ≫ (core ((ihom (stdSimplex.obj m.unop)).obj Q)).ι

private lemma gammaCone_outer {A K Q : SSet.{u}}
    (f : (SimplicialSpace.innerTensor K).obj (discreteSpace A) ⟶ gammaSpace Q)
    {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n) (a : A.obj m) :
    gammaCone f n (A.map α a) =
      gammaCone f m a ≫ (pre (stdSimplex.map α.unop)).app Q := by
  let fm : (SSet.simplicialSpaceDiscrete.obj A).obj m ⊗ K ⟶
      (gammaDiagram.obj Q).obj m := f.hom.app m
  let fn : (SSet.simplicialSpaceDiscrete.obj A).obj n ⊗ K ⟶
      (gammaDiagram.obj Q).obj n := f.hom.app n
  have hnat : ((SSet.simplicialSpaceDiscrete.obj A).map α ▷ K) ≫ fn =
      fm ≫ (gammaDiagram.obj Q).map α := f.hom.naturality α
  change pairAt A K n (A.map α a) ≫ fn ≫
      (core ((ihom (stdSimplex.obj n.unop)).obj Q)).ι =
    pairAt A K m a ≫ fm ≫ (core ((ihom (stdSimplex.obj m.unop)).obj Q)).ι ≫
      (pre (stdSimplex.map α.unop)).app Q
  rw [← pairAt_outer A K α a]
  have h := congrArg (fun g ↦ pairAt A K m a ≫ g ≫
    (core ((ihom (stdSimplex.obj n.unop)).obj Q)).ι) hnat
  simpa only [Category.assoc, gammaDiagram_obj_map, core.map_ι] using h

private def gammaTransform {A K Q : SSet.{u}}
    (f : (SimplicialSpace.innerTensor K).obj (discreteSpace A) ⟶ gammaSpace Q) :
    A ⟶ (ihom K).obj Q where
  app m := ↾fun a ↦ yonedaEquiv (homTranspose (gammaCone f m a))
  naturality m n α := by
    apply ConcreteCategory.hom_ext
    intro a
    change yonedaEquiv (homTranspose (gammaCone f n (A.map α a))) =
      ((ihom K).obj Q).map α (yonedaEquiv (homTranspose (gammaCone f m a)))
    rw [gammaCone_outer, homTranspose_pre]
    exact (yonedaEquiv_naturality α.unop (homTranspose (gammaCone f m a))).symm

private def gammaUnderlying {A K Q : SSet.{u}}
    (f : (SimplicialSpace.innerTensor K).obj (discreteSpace A) ⟶ gammaSpace Q) :
    K ⟶ (ihom A).obj Q :=
  homTranspose (gammaTransform f)

private lemma gammaUnderlying_restriction {A K Q : SSet.{u}}
    (f : (SimplicialSpace.innerTensor K).obj (discreteSpace A) ⟶ gammaSpace Q)
    (m : SimplexCategoryᵒᵖ) (a : A.obj m) :
    gammaUnderlying f ≫ (pre (yonedaEquiv.symm a : stdSimplex.obj m.unop ⟶ A)).app Q =
      gammaCone f m a := by
  apply (homTransposeEquiv (stdSimplex.obj m.unop) K Q).injective
  change homTranspose (_ ≫ _) = homTranspose _
  rw [homTranspose_pre, gammaUnderlying, homTranspose_homTranspose]
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
  rfl

private lemma ihomHom_ext_simplex_restrictions {A K Q : SSet.{u}}
    {f g : K ⟶ (ihom A).obj Q}
    (h : ∀ (m : SimplexCategoryᵒᵖ) (a : A.obj m),
      f ≫ (pre (yonedaEquiv.symm a : stdSimplex.obj m.unop ⟶ A)).app Q =
        g ≫ (pre (yonedaEquiv.symm a : stdSimplex.obj m.unop ⟶ A)).app Q) : f = g := by
  apply (homTransposeEquiv A K Q).injective
  ext m a
  have he := congrArg (fun k ↦ yonedaEquiv (homTranspose k)) (h m a)
  rw [homTranspose_pre, homTranspose_pre, yonedaEquiv_comp,
    yonedaEquiv_comp, Equiv.apply_symm_apply] at he
  exact he

private lemma gammaBoxHom_ext {A K Q : SSet.{u}}
    {f g : (SimplicialSpace.innerTensor K).obj (discreteSpace A) ⟶ gammaSpace Q}
    (h : ∀ (m : SimplexCategoryᵒᵖ) (a : A.obj m), gammaCone f m a = gammaCone g m a) :
    f = g := by
  apply InducedCategory.hom_ext
  apply NatTrans.ext
  funext m
  apply (cancel_mono (core ((ihom (stdSimplex.obj m.unop)).obj Q)).ι).1
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨a, k⟩
  have hm := congrArg (fun f ↦ f.app n k) (h m (show A.obj m from a))
  exact hm

private lemma gammaCone_scalar {A K L Q : SSet.{u}} (k : L ⟶ K)
    (f : (SimplicialSpace.innerTensor K).obj (discreteSpace A) ⟶ gammaSpace Q)
    (m : SimplexCategoryᵒᵖ) (a : A.obj m) :
    gammaCone ((SimplicialSpace.innerTensorBifunctor.obj (discreteSpace A)).map k ≫ f) m a =
      k ≫ gammaCone f m a := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro l
  rfl

private lemma gammaUnderlying_scalar {A K L Q : SSet.{u}} (k : L ⟶ K)
    (f : (SimplicialSpace.innerTensor K).obj (discreteSpace A) ⟶ gammaSpace Q) :
    gammaUnderlying ((SimplicialSpace.innerTensorBifunctor.obj (discreteSpace A)).map k ≫ f) =
      k ≫ gammaUnderlying f := by
  apply ihomHom_ext_simplex_restrictions
  intro m a
  rw [gammaUnderlying_restriction, gammaCone_scalar, Category.assoc,
    gammaUnderlying_restriction]


end SSet.Rezk

namespace SSet.Rezk

private abbrev gammaMappingSpace (A Q : SSet.{u}) : SSet.{u} :=
  (SimplicialSpace.innerHomFunctor.obj (op (discreteSpace A))).obj (gammaSpace Q)

private abbrev coreFunction (A Q : SSet.{u}) : SSet.{u} :=
  core ((ihom A).obj Q)

private def gammaCounit (A Q : SSet.{u}) :
    (SimplicialSpace.innerTensor (gammaMappingSpace A Q)).obj (discreteSpace A) ⟶ gammaSpace Q :=
  (SimplicialSpace.innerTensorHomEquiv _ (discreteSpace A) (gammaSpace Q)).symm (𝟙 _)

private lemma gammaCone_factorsCore {A K Q : SSet.{u}}
    (f : (SimplicialSpace.innerTensor K).obj (discreteSpace A) ⟶ gammaSpace Q)
    (m : SimplexCategoryᵒᵖ) (a : A.obj m) :
    ∃ g : K ⟶ (gammaDiagram.obj Q).obj m,
      gammaCone f m a = g ≫ (core ((ihom (stdSimplex.obj m.unop)).obj Q)).ι :=
  ⟨pairAt A K m a ≫ f.hom.app m, rfl⟩

private lemma gammaUnderlying_range_core {A K Q : SSet.{u}} [Quasicategory Q]
    (f : (SimplicialSpace.innerTensor K).obj (discreteSpace A) ⟶ gammaSpace Q) :
    Subcomplex.range (gammaUnderlying f) ≤ core ((ihom A).obj Q) := by
  intro n x hx
  obtain ⟨k, hk⟩ := hx
  subst x
  apply (mem_core_ihom_iff_forall_eval_vertex _).2
  intro a
  change ((gammaUnderlying f ≫
    (pre (yonedaEquiv.symm a : Δ[0] ⟶ A)).app Q ≫ (evalDeltaZeroIso Q).hom).app n k) ∈
      (core Q).obj n
  rw [← Category.assoc, gammaUnderlying_restriction]
  obtain ⟨g, hg⟩ := gammaCone_factorsCore f (op ⦋0⦌) a
  rw [hg, Category.assoc, ← core.map_ι]
  exact ((g ≫ core.map (evalDeltaZeroIso Q).hom).app n k).property

private def gammaMappingForward (A Q : SSet.{u}) [Quasicategory Q] :
    gammaMappingSpace A Q ⟶ coreFunction A Q :=
  Subcomplex.lift (gammaUnderlying (gammaCounit A Q))
    (gammaUnderlying_range_core (gammaCounit A Q))

private lemma gammaMappingForward_ι (A Q : SSet.{u}) [Quasicategory Q] :
    gammaMappingForward A Q ≫ (core ((ihom A).obj Q)).ι =
      gammaUnderlying (gammaCounit A Q) :=
  Subcomplex.lift_ι _ _

private lemma gammaCone_evaluation (A Q : SSet.{u})
    (m : SimplexCategoryᵒᵖ) (a : A.obj m) :
    gammaCone (gammaCoreEvaluation A Q) m a =
      (core ((ihom A).obj Q)).ι ≫
        (pre (yonedaEquiv.symm a : stdSimplex.obj m.unop ⟶ A)).app Q := by
  have h : pairAt A (coreFunction A Q) m a ≫ gammaCoreEvaluationComponent A Q m =
      gammaRestriction A Q m a := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro k
    rfl
  change (pairAt A (coreFunction A Q) m a ≫ gammaCoreEvaluationComponent A Q m) ≫
    (core ((ihom (stdSimplex.obj m.unop)).obj Q)).ι = _
  rw [h, gammaRestriction, core.map_ι]

private lemma gammaUnderlying_evaluation (A Q : SSet.{u}) :
    gammaUnderlying (gammaCoreEvaluation A Q) = (core ((ihom A).obj Q)).ι := by
  apply ihomHom_ext_simplex_restrictions
  intro m a
  rw [gammaUnderlying_restriction, gammaCone_evaluation]

private lemma gammaCounit_scalar (A Q : SSet.{u}) {K : SSet.{u}}
    (k : K ⟶ gammaMappingSpace A Q) :
    (SimplicialSpace.innerTensorBifunctor.obj (discreteSpace A)).map k ≫ gammaCounit A Q =
      (SimplicialSpace.innerTensorHomEquiv K (discreteSpace A) (gammaSpace Q)).symm k := by
  apply (SimplicialSpace.innerTensorHomEquiv K (discreteSpace A) (gammaSpace Q)).injective
  have hs : SimplicialSpace.innerTensorHomEquiv K (discreteSpace A) (gammaSpace Q)
      ((SimplicialSpace.innerTensorBifunctor.obj (discreteSpace A)).map k ≫ gammaCounit A Q) =
      k ≫ SimplicialSpace.innerTensorHomEquiv (gammaMappingSpace A Q)
        (discreteSpace A) (gammaSpace Q) (gammaCounit A Q) :=
    SimplicialSpace.innerTensorHomEquiv_scalar k _ _ _
  have ht : k ≫ SimplicialSpace.innerTensorHomEquiv (gammaMappingSpace A Q)
      (discreteSpace A) (gammaSpace Q) (gammaCounit A Q) = k := by
    rw [gammaCounit, Equiv.apply_symm_apply]
    exact Category.comp_id k
  have hr : SimplicialSpace.innerTensorHomEquiv K (discreteSpace A) (gammaSpace Q)
      ((SimplicialSpace.innerTensorHomEquiv K (discreteSpace A) (gammaSpace Q)).symm k) = k :=
    Equiv.apply_symm_apply _ _
  exact hs.trans (ht.trans hr.symm)

private lemma gammaInverse_counit (A Q : SSet.{u}) :
    (SimplicialSpace.innerTensorBifunctor.obj (discreteSpace A)).map (gammaMappingInverse A Q) ≫
        gammaCounit A Q =
      gammaCoreEvaluation A Q := by
  rw [gammaCounit_scalar, gammaMappingInverse, Equiv.symm_apply_apply]

private lemma gammaForward_evaluation (A Q : SSet.{u}) [Quasicategory Q] :
    (SimplicialSpace.innerTensorBifunctor.obj (discreteSpace A)).map (gammaMappingForward A Q) ≫
      gammaCoreEvaluation A Q = gammaCounit A Q := by
  apply gammaBoxHom_ext
  intro m a
  rw [gammaCone_scalar, gammaCone_evaluation, ← Category.assoc,
    gammaMappingForward_ι, gammaUnderlying_restriction]

private lemma gammaMappingForward_inverse (A Q : SSet.{u}) [Quasicategory Q] :
    gammaMappingForward A Q ≫ gammaMappingInverse A Q = 𝟙 (gammaMappingSpace A Q) := by
  have h := congrArg
    (SimplicialSpace.innerTensorHomEquiv (gammaMappingSpace A Q) (discreteSpace A) (gammaSpace Q))
    (gammaForward_evaluation A Q)
  have hs :
      SimplicialSpace.innerTensorHomEquiv (gammaMappingSpace A Q)
          (discreteSpace A) (gammaSpace Q)
          ((SimplicialSpace.innerTensorBifunctor.obj (discreteSpace A)).map
              (gammaMappingForward A Q) ≫
            gammaCoreEvaluation A Q) =
        gammaMappingForward A Q ≫ gammaMappingInverse A Q :=
    SimplicialSpace.innerTensorHomEquiv_scalar (gammaMappingForward A Q) _ _ _
  have ht : SimplicialSpace.innerTensorHomEquiv (gammaMappingSpace A Q)
      (discreteSpace A) (gammaSpace Q) (gammaCounit A Q) = 𝟙 _ := by
    rw [gammaCounit, Equiv.apply_symm_apply]
  exact hs.symm.trans (h.trans ht)

private lemma gammaMappingInverse_forward (A Q : SSet.{u}) [Quasicategory Q] :
    gammaMappingInverse A Q ≫ gammaMappingForward A Q = 𝟙 (coreFunction A Q) := by
  apply (cancel_mono (core ((ihom A).obj Q)).ι).1
  rw [Category.assoc, gammaMappingForward_ι, ← gammaUnderlying_scalar,
    gammaInverse_counit, gammaUnderlying_evaluation, Category.id_comp]

/-- The actual inner mapping end from a discrete source to Gamma is the
core of the corresponding function object. -/
@[no_expose]
noncomputable def gammaMappingIso (A Q : SSet.{u}) [Quasicategory Q] :
    (SimplicialSpace.innerHomFunctor.obj
      (op (SimplicialSpace.ofSimplicialObject.obj (SSet.simplicialSpaceDiscrete.obj A)))).obj
        (SimplicialSpace.ofSimplicialObject.obj (gammaDiagram.obj Q)) ≅
          (core ((ihom A).obj Q) : SSet.{u}) where
  hom := gammaMappingForward A Q
  inv := gammaMappingInverse A Q
  hom_inv_id := gammaMappingForward_inverse A Q
  inv_hom_id := gammaMappingInverse_forward A Q


end SSet.Rezk

namespace SSet.Rezk

private def gammaSpaceMap {Q Q' : SSet.{u}} (q : Q ⟶ Q') : gammaSpace Q ⟶ gammaSpace Q' :=
  SimplicialSpace.ofSimplicialObject.map (gammaDiagram.map q)

private lemma gammaCone_source {A A' K Q : SSet.{u}} (a : A' ⟶ A)
    (f : (SimplicialSpace.innerTensor K).obj (discreteSpace A) ⟶ gammaSpace Q)
    (m : SimplexCategoryᵒᵖ) (x : A'.obj m) :
    gammaCone ((SimplicialSpace.innerTensor K).map (discreteSpaceMap a) ≫ f) m x =
      gammaCone f m (a.app m x) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro k
  rfl

private lemma gammaUnderlying_source {A A' K Q : SSet.{u}} (a : A' ⟶ A)
    (f : (SimplicialSpace.innerTensor K).obj (discreteSpace A) ⟶ gammaSpace Q) :
    gammaUnderlying ((SimplicialSpace.innerTensor K).map (discreteSpaceMap a) ≫ f) =
      gammaUnderlying f ≫ (pre a).app Q := by
  apply ihomHom_ext_simplex_restrictions
  intro m x
  rw [gammaUnderlying_restriction, gammaCone_source]
  have hy : (yonedaEquiv.symm (a.app m x) : stdSimplex.obj m.unop ⟶ A) =
      (yonedaEquiv.symm x : stdSimplex.obj m.unop ⟶ A') ≫ a := by
    apply yonedaEquiv.injective
    rw [Equiv.apply_symm_apply, yonedaEquiv_comp, Equiv.apply_symm_apply]
  have hp : (pre a).app Q ≫
      (pre (yonedaEquiv.symm x : stdSimplex.obj m.unop ⟶ A')).app Q =
        (pre (yonedaEquiv.symm (a.app m x) : stdSimplex.obj m.unop ⟶ A)).app Q := by
    rw [← NatTrans.comp_app, ← pre_map, ← hy]
  rw [Category.assoc, hp, gammaUnderlying_restriction]

private lemma gammaCone_target {A K Q Q' : SSet.{u}} (q : Q ⟶ Q')
    (f : (SimplicialSpace.innerTensor K).obj (discreteSpace A) ⟶ gammaSpace Q)
    (m : SimplexCategoryᵒᵖ) (a : A.obj m) :
    gammaCone (f ≫ gammaSpaceMap q) m a =
      gammaCone f m a ≫ (ihom (stdSimplex.obj m.unop)).map q := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro k
  have h := core.map_ι ((ihom (stdSimplex.obj m.unop)).map q)
  exact ConcreteCategory.congr_hom (congr_app h n)
    ((f.hom.app m).app n ((pairAt A K m a).app n k))

private lemma gammaUnderlying_target {A K Q Q' : SSet.{u}} (q : Q ⟶ Q')
    (f : (SimplicialSpace.innerTensor K).obj (discreteSpace A) ⟶ gammaSpace Q) :
    gammaUnderlying (f ≫ gammaSpaceMap q) = gammaUnderlying f ≫ (ihom A).map q := by
  apply ihomHom_ext_simplex_restrictions
  intro m a
  rw [gammaUnderlying_restriction, gammaCone_target, Category.assoc,
    ← pre_comm_ihom_map, ← Category.assoc, gammaUnderlying_restriction]

private lemma gammaCounit_source {A A' Q : SSet.{u}} (a : A' ⟶ A) :
    (SimplicialSpace.innerTensor (gammaMappingSpace A Q)).map (discreteSpaceMap a) ≫
        gammaCounit A Q =
      (SimplicialSpace.innerTensorBifunctor.obj (discreteSpace A')).map
        ((SimplicialSpace.innerHomFunctor.map (discreteSpaceMap a).op).app (gammaSpace Q)) ≫
          gammaCounit A' Q := by
  let k := (SimplicialSpace.innerHomFunctor.map (discreteSpaceMap a).op).app (gammaSpace Q)
  let e := SimplicialSpace.innerTensorHomEquiv (gammaMappingSpace A Q) (discreteSpace A')
      (gammaSpace Q)
  apply e.injective
  have hl := SimplicialSpace.innerTensorHomEquiv_source (discreteSpaceMap a)
    (gammaMappingSpace A Q) (gammaSpace Q) (gammaCounit A Q)
  have hr := SimplicialSpace.innerTensorHomEquiv_scalar k (discreteSpace A') (gammaSpace Q)
    (gammaCounit A' Q)
  have hlt : SimplicialSpace.innerTensorHomEquiv (gammaMappingSpace A Q)
      (discreteSpace A) (gammaSpace Q) (gammaCounit A Q) ≫ k = k := by
    rw [gammaCounit, Equiv.apply_symm_apply]
    exact Category.id_comp k
  have hrt : k ≫ SimplicialSpace.innerTensorHomEquiv (gammaMappingSpace A' Q)
      (discreteSpace A') (gammaSpace Q) (gammaCounit A' Q) = k := by
    rw [gammaCounit, Equiv.apply_symm_apply]
    exact Category.comp_id k
  exact (hl.trans hlt).trans (hr.trans hrt).symm

private lemma gammaCounit_target {A Q Q' : SSet.{u}} (q : Q ⟶ Q') :
    gammaCounit A Q ≫ gammaSpaceMap q =
      (SimplicialSpace.innerTensorBifunctor.obj (discreteSpace A)).map
        ((SimplicialSpace.innerHomFunctor.obj (op (discreteSpace A))).map (gammaSpaceMap q)) ≫
          gammaCounit A Q' := by
  let k := (SimplicialSpace.innerHomFunctor.obj (op (discreteSpace A))).map (gammaSpaceMap q)
  let e := SimplicialSpace.innerTensorHomEquiv (gammaMappingSpace A Q) (discreteSpace A)
      (gammaSpace Q')
  apply e.injective
  have hl := SimplicialSpace.innerTensorHomEquiv_target (gammaMappingSpace A Q)
    (discreteSpace A) (gammaSpaceMap q) (gammaCounit A Q)
  have hr := SimplicialSpace.innerTensorHomEquiv_scalar k (discreteSpace A) (gammaSpace Q')
    (gammaCounit A Q')
  have hlt : SimplicialSpace.innerTensorHomEquiv (gammaMappingSpace A Q)
      (discreteSpace A) (gammaSpace Q) (gammaCounit A Q) ≫ k = k := by
    rw [gammaCounit, Equiv.apply_symm_apply]
    exact Category.id_comp k
  have hrt : k ≫ SimplicialSpace.innerTensorHomEquiv (gammaMappingSpace A Q')
      (discreteSpace A) (gammaSpace Q') (gammaCounit A Q') = k := by
    rw [gammaCounit, Equiv.apply_symm_apply]
    exact Category.comp_id k
  exact (hl.trans hlt).trans (hr.trans hrt).symm

/-- Contravariant naturality uses the original map of the actual inner end. -/
lemma gammaMappingIso_naturality_source {A A' Q : SSet.{u}} [Quasicategory Q]
    (a : A' ⟶ A) :
    (SimplicialSpace.innerHomFunctor.map
      (SimplicialSpace.ofSimplicialObject.map (SSet.simplicialSpaceDiscrete.map a)).op).app
        (SimplicialSpace.ofSimplicialObject.obj (gammaDiagram.obj Q)) ≫
        (gammaMappingIso A' Q).hom =
      (gammaMappingIso A Q).hom ≫ core.map ((pre a).app Q) := by
  apply (cancel_mono (core ((ihom A').obj Q)).ι).1
  change (_ ≫ gammaMappingForward A' Q) ≫ _ =
    (gammaMappingForward A Q ≫ core.map ((pre a).app Q)) ≫ _
  rw [Category.assoc, gammaMappingForward_ι, Category.assoc, core.map_ι]
  rw [← Category.assoc (gammaMappingForward A Q) (core ((ihom A).obj Q)).ι
    ((pre a).app Q), gammaMappingForward_ι]
  have h := gammaUnderlying_scalar
    ((SimplicialSpace.innerHomFunctor.map (discreteSpaceMap a).op).app (gammaSpace Q))
        (gammaCounit A' Q)
  rw [← gammaCounit_source, gammaUnderlying_source] at h
  exact h.symm

/-- Covariant naturality uses Gamma's original postcomposition map. -/
lemma gammaMappingIso_naturality_target {A Q Q' : SSet.{u}}
    [Quasicategory Q] [Quasicategory Q'] (q : Q ⟶ Q') :
    (SimplicialSpace.innerHomFunctor.obj
      (op (SimplicialSpace.ofSimplicialObject.obj (SSet.simplicialSpaceDiscrete.obj A)))).map
        (SimplicialSpace.ofSimplicialObject.map (gammaDiagram.map q)) ≫
        (gammaMappingIso A Q').hom =
      (gammaMappingIso A Q).hom ≫ core.map ((ihom A).map q) := by
  apply (cancel_mono (core ((ihom A).obj Q')).ι).1
  change (_ ≫ gammaMappingForward A Q') ≫ _ =
    (gammaMappingForward A Q ≫ core.map ((ihom A).map q)) ≫ _
  rw [Category.assoc, gammaMappingForward_ι, Category.assoc, core.map_ι]
  rw [← Category.assoc (gammaMappingForward A Q) (core ((ihom A).obj Q)).ι
    ((ihom A).map q), gammaMappingForward_ι]
  have h := gammaUnderlying_scalar
    ((SimplicialSpace.innerHomFunctor.obj (op (discreteSpace A))).map (gammaSpaceMap q))
        (gammaCounit A Q')
  rw [← gammaCounit_target, gammaUnderlying_target] at h
  exact h.symm

end SSet.Rezk
