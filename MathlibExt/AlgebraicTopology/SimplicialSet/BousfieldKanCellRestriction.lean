/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanSkeletalPullback
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationStdSimplex
import MathlibExt.CategoryTheory.CategoryBar.ElementsComparison
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Topology.Category.TopCat.Limits.Products
import MathlibExt.Topology.Category.TopCat.PushoutOpenComplement
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.Boundary
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizationBoundaryZeroCoordinate
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationCellInterior
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.Product.SSetRealizationFiniteProductComparisonArbitrary

/-!
# Actual coefficient cells in the Bousfield–Kan diagonal

The cell map is the canonical weighted chain inclusion followed by the actual
diagonal cell map. It retains the original coefficient and base chain.
Characteristic maps of nondegenerate nerve cells are allowed to identify
boundary points. The actual attachment and its native open-interior products
are constructed here. The lifted radial deformation and its endpoint weak
equivalences remain obligations of the BK skeletal induction.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory Topology
open scoped Simplicial

universe u v

namespace SSet

/-- The actual forward arrow from the first object of a chain to the first
object selected by a simplex reindexing. -/
@[expose]
def bkChainFirstArrow {J : Type u} [Category.{v} J] {m n : ℕ}
    (c : ComposableArrows J n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    c.left ⟶ ((nerve J).map θ.op c).left :=
  c.map' 0 (θ.toOrderHom 0).val (hjn := Nat.le_of_lt_succ (θ.toOrderHom 0).isLt)

/-- The first-arrow reindexing is the corresponding arrow of the original chain. -/
theorem bkChainFirstArrow_eq_map' {J : Type u} [Category.{v} J] {m n : ℕ}
    (c : ComposableArrows J n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    bkChainFirstArrow c θ =
      c.map' 0 (θ.toOrderHom 0).val (hjn := Nat.le_of_lt_succ (θ.toOrderHom 0).isLt) :=
  rfl

private abbrev coefficientBar {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) :
    SimplicialObject SSet.{max u v} :=
  StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D

private def sigmaPointEquiv {I : Type u} (F : I → SSet.{u})
    (a : SimplexCategoryᵒᵖ) : (∐ F).obj a ≃ Σ i, (F i).obj a :=
  (sigmaObjIso F a ≪≫ Types.coproductIso (fun i => (F i).obj a)).toEquiv

private theorem sigmaPointEquiv_ι {I : Type u} (F : I → SSet.{u})
    (a : SimplexCategoryᵒᵖ) (i : I) (x : (F i).obj a) :
    sigmaPointEquiv F a ((Sigma.ι F i).app a x) = ⟨i, x⟩ := by
  have h₁ := ConcreteCategory.congr_hom (ι_comp_sigmaObjIso_hom F a i) x
  have h₂ := ConcreteCategory.congr_hom
    (Types.coproductIso_ι_comp_hom (fun i => (F i).obj a) i) x
  exact (congrArg (fun y => (Types.coproductIso (fun i => (F i).obj a)).hom y) h₁).trans h₂

private theorem sigmaPoint_jointly_surjective {I : Type u} (F : I → SSet.{u})
    (a : SimplexCategoryᵒᵖ) (z : (∐ F).obj a) :
    ∃ (i : I) (x : (F i).obj a), (Sigma.ι F i).app a x = z := by
  refine ⟨(sigmaPointEquiv F a z).1, (sigmaPointEquiv F a z).2,
    (sigmaPointEquiv F a).injective ?_⟩
  exact sigmaPointEquiv_ι F a (sigmaPointEquiv F a z).1 (sigmaPointEquiv F a z).2

private theorem sigmaPointEquiv_map {I : Type u} (F G : I → SSet.{u})
    (f : ∀ i, F i ⟶ G i) (a : SimplexCategoryᵒᵖ) (z : (∐ F).obj a) :
    sigmaPointEquiv G a ((Limits.Sigma.map f).app a z) =
      ⟨(sigmaPointEquiv F a z).1, (f (sigmaPointEquiv F a z).1).app a
        (sigmaPointEquiv F a z).2⟩ := by
  obtain ⟨i, x, rfl⟩ := sigmaPoint_jointly_surjective F a z
  have h := ConcreteCategory.congr_hom (congr_app (Sigma.ι_map f i) a) x
  calc
    sigmaPointEquiv G a ((Limits.Sigma.map f).app a ((Sigma.ι F i).app a x)) =
        sigmaPointEquiv G a ((Sigma.ι G i).app a ((f i).app a x)) :=
      congrArg (sigmaPointEquiv G a) h
    _ = ⟨i, (f i).app a x⟩ := sigmaPointEquiv_ι G a i _
    _ = _ := by rw [sigmaPointEquiv_ι]

private theorem sigmaMap_mono {I : Type u} (F G : I → SSet.{u})
    (f : ∀ i, F i ⟶ G i) (hf : ∀ i, Mono (f i)) : Mono (Limits.Sigma.map f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro a
  rw [mono_iff_injective]
  intro z w h
  obtain ⟨i, x, rfl⟩ := sigmaPoint_jointly_surjective F a z
  obtain ⟨j, y, rfl⟩ := sigmaPoint_jointly_surjective F a w
  have h' := congrArg (sigmaPointEquiv G a) h
  rw [sigmaPointEquiv_map, sigmaPointEquiv_map, sigmaPointEquiv_ι, sigmaPointEquiv_ι] at h'
  have hij := congrArg Sigma.fst h'
  dsimp only at hij
  subst j
  have hxy : (f i).app a x = (f i).app a y := eq_of_heq (Sigma.mk.inj h').2
  let _ : Mono (f i) := hf i
  exact congrArg (fun z => (Sigma.ι F i).app a z)
    ((mono_iff_injective ((f i).app a)).mp inferInstance hxy)

private def coefficientRowIso {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (a : SimplexCategoryᵒᵖ) :
    simplicialRow (coefficientBar D) a ≅ nerve (wbarDegreeCoefficient D a).Elements :=
  wbarRowEvaluationIso D a ≪≫ terminalWeightRowIso D a ≪≫
    CategoryBar.replNerveSimplicialIso (wbarDegreeCoefficient D a)

private theorem coefficientRowIso_wbarIncl {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (a : SimplexCategoryᵒᵖ) (n : ℕ) (c : ComposableArrows J n)
    (x : (D.obj c.left).obj a) :
    (coefficientRowIso D a).hom.app (op ⦋n⦌)
      ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n ⟨c, PUnit.unit⟩).app a x) =
    CategoryBar.replElementsEquiv J (wbarDegreeCoefficient D a) n ⟨c, x, PUnit.unit⟩ := by
  change (CategoryBar.replNerveSimplicialIso (wbarDegreeCoefficient D a)).hom.app (op ⦋n⦌)
      ((terminalWeightRowIso D a).hom.app (op ⦋n⦌)
        ((wbarRowEvaluationIso D a).hom.app (op ⦋n⦌)
          ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n ⟨c,
            PUnit.unit⟩).app a x))) = _
  have he := ConcreteCategory.congr_hom (wbarRowEvaluationIso_hom_app D a (op ⦋n⦌))
    ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n ⟨c, PUnit.unit⟩).app a x)
  have hi := ConcreteCategory.congr_hom (wbarRowIncl_eq_wbarIncl_app D a n ⟨c, PUnit.unit⟩) x
  have he' : (wbarRowEvaluationIso D a).hom.app (op ⦋n⦌)
      ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n ⟨c, PUnit.unit⟩).app a x) =
        wbarRowIncl D a n ⟨c, PUnit.unit⟩ x := he.trans hi.symm
  have ht := ConcreteCategory.congr_hom
    (terminalWeightRowIso_hom_rowIncl D a n ⟨c, PUnit.unit⟩) x
  have het : (terminalWeightRowIso D a).hom.app (op ⦋n⦌)
      ((wbarRowEvaluationIso D a).hom.app (op ⦋n⦌)
        ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n ⟨c, PUnit.unit⟩).app
          a x)) =
      terminalWeightReplIncl D a n ⟨c, PUnit.unit⟩ x :=
    (congrArg (fun y => (terminalWeightRowIso D a).hom.app (op ⦋n⦌) y) he').trans ht
  have hf : (CategoryBar.replNerveSimplicialIso (wbarDegreeCoefficient D a)).hom.app (op ⦋n⦌)
      (terminalWeightReplIncl D a n ⟨c, PUnit.unit⟩ x) =
      CategoryBar.replElementsEquiv J (wbarDegreeCoefficient D a) n ⟨c, x, PUnit.unit⟩ := rfl
  exact (congrArg (fun y =>
    (CategoryBar.replNerveSimplicialIso (wbarDegreeCoefficient D a)).hom.app (op ⦋n⦌) y)
      het).trans hf

private def replPointEquiv {J : Type u} [Category.{v} J]
    (L : J ⥤ Type (max u v)) (n : ℕ) : CategoryBar.replObj J L n ≃ Σ c : ComposableArrows J n, L.obj
      c.left where
  toFun p := ⟨p.1, p.2.1⟩
  invFun p := ⟨p.1, p.2, PUnit.unit⟩
  left_inv := by
    rintro ⟨c, x, w⟩
    cases w
    rfl
  right_inv _ := rfl

private def outerRowPointEquiv {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) (a : SimplexCategoryᵒᵖ) :
    ((coefficientBar D).obj (op ⦋n⦌)).obj a ≃
      Σ c : ComposableArrows J n, (D.obj c.left).obj a :=
  ((coefficientRowIso D a).app (op ⦋n⦌)).toEquiv.trans
    ((CategoryBar.replElementsEquiv J (wbarDegreeCoefficient D a) n).symm.trans
      (replPointEquiv (wbarDegreeCoefficient D a) n))

private theorem outerRowPointEquiv_wbarIncl {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) (a : SimplexCategoryᵒᵖ)
    (c : ComposableArrows J n) (x : (D.obj c.left).obj a) :
    outerRowPointEquiv D n a
      ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n ⟨c, PUnit.unit⟩).app a x) =
        ⟨c, x⟩ := by
  let L := wbarDegreeCoefficient D a
  let e := CategoryBar.replElementsEquiv J L n
  have h := coefficientRowIso_wbarIncl D a n c x
  have h' := congrArg (fun G => replPointEquiv L n (e.symm G)) h
  have hr : replPointEquiv L n (e.symm (e ⟨c, x, PUnit.unit⟩)) = ⟨c, x⟩ := by
    exact congrArg (replPointEquiv L n)
      (e.symm_apply_apply (⟨c, x, PUnit.unit⟩ : CategoryBar.replObj J L n))
  exact h'.trans hr

private theorem outerRowPoint_jointly_surjective {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) (a : SimplexCategoryᵒᵖ)
    (z : ((coefficientBar D).obj (op ⦋n⦌)).obj a) :
    ∃ (c : ComposableArrows J n) (x : (D.obj c.left).obj a),
      (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n ⟨c, PUnit.unit⟩).app a x
        = z := by
  refine ⟨(outerRowPointEquiv D n a z).1, (outerRowPointEquiv D n a z).2,
    (outerRowPointEquiv D n a).injective ?_⟩
  exact outerRowPointEquiv_wbarIncl D n a
    (outerRowPointEquiv D n a z).1 (outerRowPointEquiv D n a z).2

private theorem elementsLift_reindex {J : Type u} [Category.{v} J]
    (L : J ⥤ Type (max u v)) {m n : ℕ} (c : ComposableArrows J n) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (x : L.obj c.left) :
    (nerve L.Elements).map θ.op (CategoryBar.replElementsEquiv J L n ⟨c, x, PUnit.unit⟩) =
      CategoryBar.replElementsEquiv J L m
        ⟨(nerve J).map θ.op c, L.map (bkChainFirstArrow c θ) x, PUnit.unit⟩ := by
  apply ((CategoryBar.replElementsEquiv J L m).symm).injective
  let t : CategoryBar.replObj J L m :=
    ⟨(nerve J).map θ.op c, L.map (bkChainFirstArrow c θ) x, PUnit.unit⟩
  have hr : (CategoryBar.replElementsEquiv J L m).symm
      (CategoryBar.replElementsEquiv J L m t) = t :=
    (CategoryBar.replElementsEquiv J L m).symm_apply_apply t
  have hl : (CategoryBar.replElementsEquiv J L m).symm
      ((nerve L.Elements).map θ.op (CategoryBar.replElementsEquiv J L n ⟨c, x, PUnit.unit⟩)) =
        t := by
    refine Sigma.ext rfl (heq_of_eq ?_)
    apply Prod.ext
    · rfl
    · rfl
  exact hl.trans hr.symm

private theorem firstArrow_sigma_isIso {J : Type u} [Category.{v} J]
    {n : ℕ} (c : ComposableArrows J n) (i : Fin (n + 1)) :
    IsIso (bkChainFirstArrow c (SimplexCategory.σ i)) := by
  let j : Fin (n + 1) := (SimplexCategory.σ i).toOrderHom 0
  have hj : j = 0 := by
    change i.predAbove (0 : Fin (n + 2)) = 0
    exact Fin.predAbove_right_zero
  let _ : IsIso (homOfLE (Fin.zero_le j)) := by
    have he : (homOfLE (Fin.zero_le j) : (0 : Fin (n + 1)) ⟶ j) = eqToHom hj.symm :=
      Subsingleton.elim _ _
    exact he.symm ▸ (inferInstance : IsIso (eqToHom hj.symm))
  change IsIso (c.map (homOfLE (Fin.zero_le j)))
  infer_instance

private def coefficientRowProjection {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (a : SimplexCategoryᵒᵖ) :
    simplicialRow (coefficientBar D) a ⟶ nerve J :=
  (coefficientRowIso D a).hom ≫
    nerveMapCommonHom.{u, v, 0} (Functor.Elements.π (wbarDegreeCoefficient D a))

private theorem coefficientRowProjection_wbarIncl {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (a : SimplexCategoryᵒᵖ) (n : ℕ) (c : ComposableArrows J n)
    (x : (D.obj c.left).obj a) :
    (coefficientRowProjection D a).app (op ⦋n⦌)
      ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n ⟨c, PUnit.unit⟩).app a
        x) = c := by
  have h := coefficientRowIso_wbarIncl D a n c x
  exact congrArg
    (fun G =>
      (nerveMapCommonHom.{u, v, 0} (Functor.Elements.π (wbarDegreeCoefficient D a))).app
        (op ⦋n⦌) G) h

private theorem outerMap_wbarIncl_aux {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (a : SimplexCategoryᵒᵖ) {m n : ℕ}
    (c : ComposableArrows J n) (θ : ⦋m⦌ ⟶ ⦋n⦌) (x : (D.obj c.left).obj a) :
    ((coefficientBar D).map θ.op).app a
      ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n ⟨c, PUnit.unit⟩).app a x) =
    (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D m
      ⟨(nerve J).map θ.op c, PUnit.unit⟩).app a ((D.map (bkChainFirstArrow c θ)).app a x) := by
  apply ((coefficientRowIso D a).app (op ⦋m⦌)).toEquiv.injective
  let z := (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n ⟨c, PUnit.unit⟩).app a x
  have hn := (coefficientRowIso D a).hom.naturality_apply θ.op z
  have hs := coefficientRowIso_wbarIncl D a n c x
  have ht := coefficientRowIso_wbarIncl D a m ((nerve J).map θ.op c)
    ((D.map (bkChainFirstArrow c θ)).app a x)
  exact hn.trans ((congrArg (fun G => (nerve (wbarDegreeCoefficient D a).Elements).map θ.op G)
    hs).trans
    ((elementsLift_reindex (wbarDegreeCoefficient D a) c θ x).trans ht.symm))

/-- Every actual outer reindexing acts on the first coefficient through the
forward arrow selected by its first vertex, including degenerate target chains. -/
theorem bkOuterMap_wbarIncl {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (a : SimplexCategoryᵒᵖ) {m n : ℕ}
    (c : ComposableArrows J n) (θ : ⦋m⦌ ⟶ ⦋n⦌) (x : (D.obj c.left).obj a) :
    ((StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D).map θ.op).app a
      ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n ⟨c, PUnit.unit⟩).app a x) =
    (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D m
      ⟨(nerve J).map θ.op c, PUnit.unit⟩).app a ((D.map (bkChainFirstArrow c θ)).app a x) :=
  outerMap_wbarIncl_aux D a c θ x

private theorem mem_latching_wbarIncl_aux {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (a : SimplexCategoryᵒᵖ) (n : ℕ) (c : ComposableArrows J n)
    (x : (D.obj c.left).obj a) :
    (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n ⟨c, PUnit.unit⟩).app a x ∈
        (outerLatching (coefficientBar D) n).obj a ↔ c ∈ (nerve J).degenerate n := by
  constructor
  · intro hx
    have h := degenerate_app_apply hx (coefficientRowProjection D a)
    have hc := coefficientRowProjection_wbarIncl D a n c x
    exact hc ▸ h
  · intro hc
    cases n with
    | zero =>
        rw [degenerate_zero] at hc
        exact hc.elim
    | succ n =>
        rw [degenerate_eq_iUnion_range_σ] at hc
        obtain ⟨i, c', rfl⟩ := Set.mem_iUnion.mp hc
        let _ : IsIso (bkChainFirstArrow c' (SimplexCategory.σ i)) := firstArrow_sigma_isIso c' i
        let f := D.map (bkChainFirstArrow c' (SimplexCategory.σ i))
        let _ : IsIso f := inferInstance
        let x' := (inv f).app a x
        have hx : f.app a x' = x := by
          have h := ConcreteCategory.congr_hom (Iso.inv_hom_id_app (asIso f) a) x
          exact h
        change (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D (n + 1)
          ⟨(nerve J).σ i c', PUnit.unit⟩).app a x ∈
          (simplicialRow (coefficientBar D) a).degenerate (n + 1)
        rw [degenerate_eq_iUnion_range_σ]
        refine Set.mem_iUnion.mpr ⟨i, ?_⟩
        refine ⟨(StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n
          ⟨c', PUnit.unit⟩).app a x', ?_⟩
        have hf := bkOuterMap_wbarIncl D a c' (SimplexCategory.σ i) x'
        have hi := congrArg (fun y =>
          (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D (n + 1)
            ⟨(nerve J).σ i c', PUnit.unit⟩).app a y) hx
        exact hf.trans hi

/-- The actual outer latching row consists exactly of the degenerate-chain
summands, independently of the coefficient diagram. -/
theorem bkOuterLatching_wbarIncl_iff {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (a : SimplexCategoryᵒᵖ) (n : ℕ) (c : ComposableArrows J n)
    (x : (D.obj c.left).obj a) :
    (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n ⟨c, PUnit.unit⟩).app a x ∈
        (outerLatching (StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D)
          n).obj a ↔
      c ∈ (nerve J).degenerate n :=
  mem_latching_wbarIncl_aux D a n c x

/-- The actual coefficient cell for a chain, with the coefficient at its
first object. Degenerate chains are allowed in this definition. -/
def bkChainCellMap {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) {n : ℕ}
    (c : ComposableArrows J n) : D.obj c.left ⊗ (Δ[n] : SSet.{max u v}) ⟶ bkHocolim D :=
  (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n ⟨c, PUnit.unit⟩ ▷
    (Δ[n] : SSet.{max u v})) ≫
      diagonalCellMap (StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D) n

private theorem bkChainCellMap_app_aux {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) {n : ℕ} (c : ComposableArrows J n)
    (a : SimplexCategoryᵒᵖ) (x : (D.obj c.left).obj a) (θ : (Δ[n] : SSet.{max u v}).obj a) :
    (bkChainCellMap D c).app a ⟨x, θ⟩ =
      ((StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D).map
        (stdSimplex.objEquiv θ).op).app a
        ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n ⟨c, PUnit.unit⟩).app
          a x) :=
  rfl

/-- The coefficient cell applies the actual outer simplex reindexing to its
weighted chain summand. This characteristic does not expose the wrapper value. -/
theorem bkChainCellMap_app_apply {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) {n : ℕ} (c : ComposableArrows J n)
    (a : SimplexCategoryᵒᵖ) (x : (D.obj c.left).obj a) (θ : (Δ[n] : SSet.{max u v}).obj a) :
    (bkChainCellMap D c).app a ⟨x, θ⟩ =
      ((StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) D).map
        (stdSimplex.objEquiv θ).op).app a
        ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n ⟨c, PUnit.unit⟩).app
          a x) :=
  bkChainCellMap_app_aux D c a x θ

private theorem bkChainCellMap_reindex_aux {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) {m n : ℕ} (c : ComposableArrows J n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (D.obj c.left ◁ (SSet.stdSimplex : SimplexCategory ⥤ SSet.{max u v}).map θ) ≫
        bkChainCellMap D c =
      (D.map (bkChainFirstArrow c θ) ▷ (Δ[m] : SSet.{max u v})) ≫
        bkChainCellMap D ((nerve J).map θ.op c) := by
  ext a z
  obtain ⟨⟨k⟩⟩ := a
  obtain ⟨x, α⟩ := z
  change (bkChainCellMap D c).app (op ⦋k⦌)
      ⟨x, ((SSet.stdSimplex : SimplexCategory ⥤ SSet.{max u v}).map θ).app (op ⦋k⦌) α⟩ =
    (bkChainCellMap D ((nerve J).map θ.op c)).app (op ⦋k⦌)
      ⟨(D.map (bkChainFirstArrow c θ)).app (op ⦋k⦌) x, α⟩
  have hl := bkChainCellMap_app_apply D c (op ⦋k⦌) x
    (((SSet.stdSimplex : SimplexCategory ⥤ SSet.{max u v}).map θ).app (op ⦋k⦌) α)
  have hr := bkChainCellMap_app_apply D ((nerve J).map θ.op c) (op ⦋k⦌)
    ((D.map (bkChainFirstArrow c θ)).app (op ⦋k⦌) x) α
  have hα : stdSimplex.objEquiv (((SSet.stdSimplex : SimplexCategory ⥤ SSet.{max u v}).map θ).app
      (op ⦋k⦌) α) =
      stdSimplex.objEquiv α ≫ θ := rfl
  let z := (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n ⟨c, PUnit.unit⟩).app
    (op ⦋k⦌) x
  have hc := congrArg (fun f : ⦋k⦌ ⟶ ⦋n⦌ =>
    ((coefficientBar D).map f.op).app (op ⦋k⦌) z) hα
  have hm := ConcreteCategory.congr_hom
    (congrArg (fun f : (coefficientBar D).obj (op ⦋n⦌) ⟶ (coefficientBar D).obj (op ⦋k⦌) =>
      f.app (op ⦋k⦌))
      ((coefficientBar D).map_comp θ.op (stdSimplex.objEquiv α).op)) z
  have hx := bkOuterMap_wbarIncl D (op ⦋k⦌) c θ x
  have hb := congrArg
    (fun y => ((coefficientBar D).map (stdSimplex.objEquiv α).op).app (op ⦋k⦌) y) hx
  exact hl.trans (hc.trans (hm.trans hb)) |>.trans hr.symm

/-- The complete coefficient-cell face/reindexing square: simplex
reindexing changes the first coefficient by the actual forward diagram map. -/
@[reassoc]
theorem bkChainCellMap_reindex {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) {m n : ℕ} (c : ComposableArrows J n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (D.obj c.left ◁ (SSet.stdSimplex : SimplexCategory ⥤ SSet.{max u v}).map θ) ≫
        bkChainCellMap D c =
      (D.map (bkChainFirstArrow c θ) ▷ (Δ[m] : SSet.{max u v})) ≫
        bkChainCellMap D ((nerve J).map θ.op c) :=
  bkChainCellMap_reindex_aux D c θ

/-- The actual base coordinate of the coefficient cell is the characteristic
map of its chain. No injectivity of that characteristic map is assumed. -/
@[reassoc]
theorem bkChainCellMap_comp_projection {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) {n : ℕ} (c : ComposableArrows J n) :
    bkChainCellMap D c ≫ bkHocolimToNerve D =
      CartesianMonoidalCategory.snd (D.obj c.left) (Δ[n] : SSet.{max u v}) ≫
        yonedaEquiv.symm c := by
  ext a z
  obtain ⟨⟨m⟩⟩ := a
  obtain ⟨x, θ⟩ := z
  change (bkHocolimToNerve D).app (op ⦋m⦌) ((bkChainCellMap D c).app (op ⦋m⦌) ⟨x, θ⟩) =
    (nerve J).map (stdSimplex.objEquiv θ).op c
  rw [bkChainCellMap_app_apply]
  exact bkHocolimToNerve_outerMap_wbarIncl D (stdSimplex.objEquiv θ) ⟨c, PUnit.unit⟩ x

/-- Every actual coefficient cell lies in its prescribed outer stage. -/
theorem range_bkChainCellMap_le {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) {n : ℕ} (c : ComposableArrows J n) :
    Subcomplex.range (bkChainCellMap D c) ≤ bkSkeletalFiltration D n := by
  rw [bkSkeletalFiltration_eq_preimage]
  rintro ⟨⟨m⟩⟩ z ⟨⟨x, θ⟩, rfl⟩
  change (bkHocolimToNerve D).app (op ⦋m⦌) ((bkChainCellMap D c).app (op ⦋m⦌) ⟨x, θ⟩) ∈
    ((nerve J).skeleton (n + 1)).obj (op ⦋m⦌)
  rw [bkChainCellMap_app_apply,
    bkHocolimToNerve_outerMap_wbarIncl D (stdSimplex.objEquiv θ) ⟨c, PUnit.unit⟩ x]
  exact ((nerve J).skeleton (n + 1)).map (stdSimplex.objEquiv θ).op
    ((nerve J).mem_skeleton c (Nat.lt_succ_self n))

/-- The actual coefficient cell as a map into the outer stage. -/
def bkChainCellToStage {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) {n : ℕ} (c : ComposableArrows J n) :
    D.obj c.left ⊗ (Δ[n] : SSet.{max u v}) ⟶ (bkSkeletalFiltration D n : SSet.{max u v}) :=
  Subcomplex.lift (bkChainCellMap D c) (range_bkChainCellMap_le D c)

@[reassoc]
theorem bkChainCellToStage_ι {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) {n : ℕ} (c : ComposableArrows J n) :
    bkChainCellToStage D c ≫ (bkSkeletalFiltration D n).ι = bkChainCellMap D c :=
  Subcomplex.lift_ι _ _

private theorem nondegenerate_characteristic_preimage_skeleton
    (X : SSet.{u}) {n : ℕ} (c : X.nonDegenerate n) :
    (X.skeleton n).preimage (yonedaEquiv.symm c.1) = boundary n := by
  let e : relativeCellComplexOfMono.Cell (⊥ : X.Subcomplex).ι n :=
    { simplex := c.1
      nonDegenerate := c.2
      notMem := by rintro ⟨x, _⟩; exact x.2.elim }
  have h₀ : Subcomplex.range (⊥ : X.Subcomplex).ι = ⊥ := by
    ext a x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro h
      exact h.elim
  simpa only [relativeCellComplexOfMono.Cell.map, skeletonOfMono, OrderHom.coe_mk, h₀,
    bot_sup_eq] using e.preimage_map

set_option backward.isDefEq.respectTransparency false in
/-- A nondegenerate coefficient cell meets the preceding outer stage exactly
over its simplex boundary, even when its boundary characteristic is nonregular. -/
theorem bkChainCellMap_preimage_stage {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) {n : ℕ} (c : (nerve J).nonDegenerate (n + 1)) :
    (bkSkeletalFiltration D n).preimage (bkChainCellMap D c.1) =
      (⊤ : (D.obj c.1.left).Subcomplex).prod (boundary (n + 1)) := by
  rw [bkSkeletalFiltration_eq_preimage, ← Subcomplex.preimage_comp,
    bkChainCellMap_comp_projection]
  have h := nondegenerate_characteristic_preimage_skeleton (nerve J) c
  ext a ⟨x, θ⟩
  change (nerve J).map (stdSimplex.objEquiv θ).op c.1 ∈
      ((nerve J).skeleton (n + 1)).obj a ↔
    x ∈ (⊤ : (D.obj c.1.left).Subcomplex).obj a ∧
      θ ∈ (boundary (n + 1)).obj a
  have hθ := congrArg (fun A : (Δ[n + 1] : SSet.{max u v}).Subcomplex => θ ∈ A.obj a) h
  have hθ' : (nerve J).map (stdSimplex.objEquiv θ).op c.1 ∈
      ((nerve J).skeleton (n + 1)).obj a ↔ θ ∈ (boundary (n + 1)).obj a :=
    Iff.of_eq hθ
  constructor
  · intro hz
    exact ⟨by trivial, hθ'.mp hz⟩
  · rintro ⟨_, hθ⟩
    exact hθ'.mpr hθ

/-- The coproduct of the actual coefficient cells over the nondegenerate
`n`-chains. -/
abbrev bkNondegenerateCellDomain {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) : SSet.{max u v} :=
  ∐ (fun c : (nerve J).nonDegenerate n => D.obj c.1.left ⊗ (Δ[n] : SSet.{max u v}))

/-- The corresponding coproduct of coefficient times simplex boundaries. -/
abbrev bkNondegenerateCellBoundary {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) : SSet.{max u v} :=
  ∐ (fun c : (nerve J).nonDegenerate n => D.obj c.1.left ⊗ (boundary n : SSet.{max u v}))

/-- The literal boundary inclusion in every nondegenerate coefficient cell. -/
def bkNondegenerateCellBoundaryInclusion {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    bkNondegenerateCellBoundary D n ⟶ bkNondegenerateCellDomain D n :=
  Limits.Sigma.map (fun c : (nerve J).nonDegenerate n => D.obj c.1.left ◁ (boundary n).ι)

/-- The actual map of the coproduct of nondegenerate coefficient cells to
the Bousfield–Kan diagonal. -/
def bkNondegenerateCellMap {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    bkNondegenerateCellDomain D n ⟶ bkHocolim D :=
  Sigma.desc (fun c => bkChainCellMap D c.1)

private theorem bkNondegenerateCellMap_ι_aux {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) (c : (nerve J).nonDegenerate n) :
    Sigma.ι (fun c : (nerve J).nonDegenerate n => D.obj c.1.left ⊗ (Δ[n] : SSet.{max u v})) c ≫
      bkNondegenerateCellMap D n = bkChainCellMap D c.1 :=
  Sigma.ι_comp_desc _ _

@[reassoc]
theorem bkNondegenerateCellMap_ι {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) (c : (nerve J).nonDegenerate n) :
    Sigma.ι (fun c : (nerve J).nonDegenerate n => D.obj c.1.left ⊗ (Δ[n] : SSet.{max u v})) c ≫
      bkNondegenerateCellMap D n = bkChainCellMap D c.1 :=
  bkNondegenerateCellMap_ι_aux D n c

private theorem bkNondegenerateCellMap_ι_apply {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) (c : (nerve J).nonDegenerate n)
    (a : SimplexCategoryᵒᵖ) (p : (D.obj c.1.left ⊗ (Δ[n] : SSet.{max u v})).obj a) :
    (bkNondegenerateCellMap D n).app a
      ((Sigma.ι (fun c : (nerve J).nonDegenerate n => D.obj c.1.left ⊗ (Δ[n] : SSet.{max u v}))
        c).app a p) =
        (bkChainCellMap D c.1).app a p :=
  ConcreteCategory.congr_hom (congr_app (bkNondegenerateCellMap_ι D n c) a) p

private theorem bkNondegenerateCellBoundaryInclusion_ι_aux
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate n) :
    Sigma.ι (fun c : (nerve J).nonDegenerate n =>
      D.obj c.1.left ⊗ (boundary n : SSet.{max u v})) c ≫
      bkNondegenerateCellBoundaryInclusion D n =
    (D.obj c.1.left ◁ (boundary n).ι) ≫
      Sigma.ι (fun c : (nerve J).nonDegenerate n => D.obj c.1.left ⊗ (Δ[n] : SSet.{max u v})) c :=
  Sigma.ι_map _ _

@[reassoc]
theorem bkNondegenerateCellBoundaryInclusion_ι
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate n) :
    Sigma.ι (fun c : (nerve J).nonDegenerate n =>
      D.obj c.1.left ⊗ (boundary n : SSet.{max u v})) c ≫
      bkNondegenerateCellBoundaryInclusion D n =
    (D.obj c.1.left ◁ (boundary n).ι) ≫
      Sigma.ι (fun c : (nerve J).nonDegenerate n => D.obj c.1.left ⊗ (Δ[n] : SSet.{max u v})) c :=
  bkNondegenerateCellBoundaryInclusion_ι_aux D n c

private theorem bkNondegenerateCellBoundaryInclusion_mono_aux
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    Mono (bkNondegenerateCellBoundaryInclusion D n) :=
  sigmaMap_mono _ _
    (fun c : (nerve J).nonDegenerate n => D.obj c.1.left ◁ (boundary n).ι)
    (fun c => by
      rw [NatTrans.mono_iff_mono_app]
      intro a
      rw [mono_iff_injective]
      intro z w h
      change (z.1, z.2.1) = (w.1, w.2.1) at h
      have h₁ : z.1 = w.1 :=
        congrArg (fun p : (D.obj c.1.left).obj a × (Δ[n] : SSet.{max u v}).obj a => p.1) h
      have h₂ : z.2.1 = w.2.1 :=
        congrArg (fun p : (D.obj c.1.left).obj a × (Δ[n] : SSet.{max u v}).obj a => p.2) h
      exact Prod.ext h₁ (Subtype.ext h₂))

instance bkNondegenerateCellBoundaryInclusion_mono
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    Mono (bkNondegenerateCellBoundaryInclusion D n) :=
  bkNondegenerateCellBoundaryInclusion_mono_aux D n

private theorem chainCell_mem_old_iff_boundary
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) {n : ℕ}
    (c : (nerve J).nonDegenerate (n + 1)) (a : SimplexCategoryᵒᵖ)
    (x : (D.obj c.1.left).obj a) (θ : (Δ[n + 1] : SSet.{max u v}).obj a) :
    (bkChainCellMap D c.1).app a ⟨x, θ⟩ ∈ (bkSkeletalFiltration D n).obj a ↔
      θ ∈ (boundary (n + 1)).obj a := by
  have h := congrArg
    (fun A : (D.obj c.1.left ⊗ (Δ[n + 1] : SSet.{max u v})).Subcomplex => ⟨x, θ⟩ ∈ A.obj a)
    (bkChainCellMap_preimage_stage D c)
  have h' : (bkChainCellMap D c.1).app a ⟨x, θ⟩ ∈ (bkSkeletalFiltration D n).obj a ↔
      x ∈ (⊤ : (D.obj c.1.left).Subcomplex).obj a ∧ θ ∈ (boundary (n + 1)).obj a :=
    Iff.of_eq h
  constructor
  · exact fun hx => (h'.mp hx).2
  · intro hθ
    exact h'.mpr ⟨by trivial, hθ⟩

/-- The complete nondegenerate-cell attachment has exactly its literal
coefficient-boundary coproduct as the preimage of the preceding stage. -/
theorem bkNondegenerateCellMap_preimage_stage
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    (bkSkeletalFiltration D n).preimage (bkNondegenerateCellMap D (n + 1)) =
      Subcomplex.range (bkNondegenerateCellBoundaryInclusion D (n + 1)) := by
  ext a z
  constructor
  · intro hz
    obtain ⟨c, ⟨x, θ⟩, rfl⟩ := sigmaPoint_jointly_surjective
      (fun c : (nerve J).nonDegenerate (n + 1) => D.obj c.1.left ⊗ (Δ[n + 1] : SSet.{max u v})) a z
    have hc := ConcreteCategory.congr_hom
      (congr_app (bkNondegenerateCellMap_ι D (n + 1) c) a) ⟨x, θ⟩
    have hθ := (chainCell_mem_old_iff_boundary D c a x θ).mp (hc ▸ hz)
    refine ⟨(Sigma.ι
      (fun c : (nerve J).nonDegenerate (n + 1) =>
        D.obj c.1.left ⊗ (boundary (n + 1) : SSet.{max u v})) c).app a ⟨x, ⟨θ, hθ⟩⟩, ?_⟩
    exact ConcreteCategory.congr_hom
      (congr_app (bkNondegenerateCellBoundaryInclusion_ι D (n + 1) c) a) ⟨x, ⟨θ, hθ⟩⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨c, ⟨x, θ⟩, rfl⟩ := sigmaPoint_jointly_surjective
      (fun c : (nerve J).nonDegenerate (n + 1) =>
        D.obj c.1.left ⊗ (boundary (n + 1) : SSet.{max u v})) a y
    have hb := ConcreteCategory.congr_hom
      (congr_app (bkNondegenerateCellBoundaryInclusion_ι D (n + 1) c) a) ⟨x, θ⟩
    have hc := ConcreteCategory.congr_hom
      (congr_app (bkNondegenerateCellMap_ι D (n + 1) c) a) ⟨x, θ.1⟩
    have h := (congrArg (fun z => (bkNondegenerateCellMap D (n + 1)).app a z) hb).trans hc
    change (bkNondegenerateCellMap D (n + 1)).app a
      ((bkNondegenerateCellBoundaryInclusion D (n + 1)).app a
        ((Sigma.ι (fun c : (nerve J).nonDegenerate (n + 1) =>
          D.obj c.1.left ⊗ (boundary (n + 1) : SSet.{max u v})) c).app a ⟨x, θ⟩)) ∈
      (bkSkeletalFiltration D n).obj a
    exact h.symm ▸ (chainCell_mem_old_iff_boundary D c a x θ.1).mpr θ.2

set_option backward.isDefEq.respectTransparency false in
private theorem bkNondegenerateCellMap_injective_off_stage
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (a : SimplexCategoryᵒᵖ) (z w : (bkNondegenerateCellDomain D (n + 1)).obj a)
    (hz : z ∉ ((bkSkeletalFiltration D n).preimage
      (bkNondegenerateCellMap D (n + 1))).obj a)
    (hw : w ∉ ((bkSkeletalFiltration D n).preimage
      (bkNondegenerateCellMap D (n + 1))).obj a)
    (h : (bkNondegenerateCellMap D (n + 1)).app a z =
      (bkNondegenerateCellMap D (n + 1)).app a w) : z = w := by
  obtain ⟨⟨k⟩⟩ := a
  obtain ⟨c, ⟨x, θ⟩, rfl⟩ := sigmaPoint_jointly_surjective
    (fun c : (nerve J).nonDegenerate (n + 1) => D.obj c.1.left ⊗ (Δ[n + 1] : SSet.{max u v})) _ z
  obtain ⟨d, ⟨y, φ⟩, rfl⟩ := sigmaPoint_jointly_surjective
    (fun c : (nerve J).nonDegenerate (n + 1) => D.obj c.1.left ⊗ (Δ[n + 1] : SSet.{max u v})) _ w
  have hc := ConcreteCategory.congr_hom
    (congr_app (bkNondegenerateCellMap_ι D (n + 1) c) (op ⦋k⦌)) ⟨x, θ⟩
  have hd := ConcreteCategory.congr_hom
    (congr_app (bkNondegenerateCellMap_ι D (n + 1) d) (op ⦋k⦌)) ⟨y, φ⟩
  have hθ : θ ∉ (boundary (n + 1)).obj (op ⦋k⦌) := by
    intro hθ
    apply hz
    change (bkNondegenerateCellMap D (n + 1)).app (op ⦋k⦌) _ ∈
      (bkSkeletalFiltration D n).obj (op ⦋k⦌)
    exact hc.symm ▸ (chainCell_mem_old_iff_boundary D c _ x θ).mpr hθ
  have hφ : φ ∉ (boundary (n + 1)).obj (op ⦋k⦌) := by
    intro hφ
    apply hw
    change (bkNondegenerateCellMap D (n + 1)).app (op ⦋k⦌) _ ∈
      (bkSkeletalFiltration D n).obj (op ⦋k⦌)
    exact hd.symm ▸ (chainCell_mem_old_iff_boundary D d _ y φ).mpr hφ
  let α : ⦋k⦌ ⟶ ⦋n + 1⦌ := stdSimplex.objEquiv θ
  let β : ⦋k⦌ ⟶ ⦋n + 1⦌ := stdSimplex.objEquiv φ
  let _ : Epi α := by
    rw [SimplexCategory.epi_iff_surjective]
    by_contra hbad
    exact hθ hbad
  let _ : Epi β := by
    rw [SimplexCategory.epi_iff_surjective]
    by_contra hbad
    exact hφ hbad
  let R := simplicialRow (coefficientBar D) (op ⦋k⦌)
  let xc : R _⦋n + 1⦌ :=
    (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D (n + 1)
      ⟨c.1, PUnit.unit⟩).app (op ⦋k⦌) x
  let yd : R _⦋n + 1⦌ :=
    (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D (n + 1)
      ⟨d.1, PUnit.unit⟩).app (op ⦋k⦌) y
  have hxc : xc ∈ R.nonDegenerate (n + 1) := by
    rw [mem_nonDegenerate_iff_notMem_degenerate]
    intro hx
    have hdeg := (bkOuterLatching_wbarIncl_iff D (op ⦋k⦌) (n + 1) c.1 x).mp hx
    exact (((nerve J).mem_nonDegenerate_iff_notMem_degenerate c.1).mp c.2) hdeg
  have hyd : yd ∈ R.nonDegenerate (n + 1) := by
    rw [mem_nonDegenerate_iff_notMem_degenerate]
    intro hy
    have hdeg := (bkOuterLatching_wbarIncl_iff D (op ⦋k⦌) (n + 1) d.1 y).mp hy
    exact (((nerve J).mem_nonDegenerate_iff_notMem_degenerate d.1).mp d.2) hdeg
  have hcell := hc.symm.trans (h.trans hd)
  have hrow : R.map α.op xc = R.map β.op yd :=
    (bkChainCellMap_app_apply D c.1 (op ⦋k⦌) x θ).symm.trans
      (hcell.trans (bkChainCellMap_app_apply D d.1 (op ⦋k⦌) y φ))
  have hpoints := congrArg Subtype.val
    (R.unique_nonDegenerate_simplex (R.map α.op xc) α ⟨xc, hxc⟩ rfl β ⟨yd, hyd⟩ hrow)
  have hαβ := R.unique_nonDegenerate_map (R.map α.op xc) α ⟨xc, hxc⟩ rfl β ⟨yd, hyd⟩ hrow
  have hcoeffs := congrArg (outerRowPointEquiv D (n + 1) (op ⦋k⦌)) hpoints
  dsimp only [xc, yd] at hcoeffs
  rw [outerRowPointEquiv_wbarIncl, outerRowPointEquiv_wbarIncl] at hcoeffs
  have hcd : c = d := Subtype.ext (congrArg Sigma.fst hcoeffs)
  subst d
  have hxy : x = y := eq_of_heq (Sigma.mk.inj hcoeffs).2
  have hθφ : θ = φ := stdSimplex.objEquiv.injective hαβ
  subst y
  subst φ
  rfl

/-- The coproduct of the nondegenerate coefficient cells lies in its actual
outer stage. -/
theorem range_bkNondegenerateCellMap_le
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    Subcomplex.range (bkNondegenerateCellMap D n) ≤ bkSkeletalFiltration D n := by
  rintro a z ⟨y, rfl⟩
  obtain ⟨c, p, rfl⟩ := sigmaPoint_jointly_surjective
    (fun c : (nerve J).nonDegenerate n => D.obj c.1.left ⊗ (Δ[n] : SSet.{max u v})) a y
  have hc := ConcreteCategory.congr_hom (congr_app (bkNondegenerateCellMap_ι D n c) a) p
  have hmem := range_bkChainCellMap_le D c.1 a ⟨p, rfl⟩
  exact hc.symm ▸ hmem

private theorem bkStage_mono {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) {m n : ℕ} (h : m ≤ n) :
    bkSkeletalFiltration D m ≤ bkSkeletalFiltration D n := by
  rw [bkSkeletalFiltration_eq_preimage, bkSkeletalFiltration_eq_preimage]
  exact Subcomplex.preimage_monotone _
    ((nerve J).skeleton.monotone (Nat.add_le_add_right h 1))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
-- The nondegenerate-support reconstruction traverses nested coproduct and bar coordinates.
/-- The next actual BK outer stage is the preceding stage together with
the nondegenerate coefficient cells of the new dimension. -/
theorem bkSkeletalFiltration_succ_eq_sup_nonDegenerateCells
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    bkSkeletalFiltration D (n + 1) = bkSkeletalFiltration D n ⊔
      Subcomplex.range (bkNondegenerateCellMap D (n + 1)) := by
  apply le_antisymm
  · rintro ⟨⟨k⟩⟩ z hz
    let R := simplicialRow (coefficientBar D) (op ⦋k⦌)
    let zR : R _⦋k⦌ := z
    obtain ⟨m, α, hα, y, hy⟩ := R.exists_nonDegenerate zR
    let _ : Epi α := hα
    obtain ⟨c, x, hcx⟩ := outerRowPoint_jointly_surjective D m (op ⦋k⦌) y.1
    have hc : c ∈ (nerve J).nonDegenerate m := by
      rw [mem_nonDegenerate_iff_notMem_degenerate]
      intro hcdeg
      have hdeg := (bkOuterLatching_wbarIncl_iff D (op ⦋k⦌) m c x).mpr hcdeg
      have hydeg : y.1 ∈ R.degenerate m := hcx ▸ hdeg
      exact ((R.mem_nonDegenerate_iff_notMem_degenerate y.1).mp y.2) hydeg
    have hcell : (bkChainCellMap D c).app (op ⦋k⦌) ⟨x, stdSimplex.objEquiv.symm α⟩ = z := by
      have h := bkChainCellMap_app_apply D c (op ⦋k⦌) x (stdSimplex.objEquiv.symm α)
      simp only [Equiv.apply_symm_apply] at h
      exact h.trans ((congrArg (fun q => R.map α.op q) hcx).trans hy.symm)
    have hbase : (bkHocolimToNerve D).app (op ⦋k⦌) z = (nerve J).map α.op c := by
      have hi := bkChainCellMap_app_apply D c (op ⦋k⦌) x (stdSimplex.objEquiv.symm α)
      simp only [Equiv.apply_symm_apply] at hi
      have hp := bkHocolimToNerve_outerMap_wbarIncl D α ⟨c, PUnit.unit⟩ x
      exact (congrArg (fun q => (bkHocolimToNerve D).app (op ⦋k⦌) q) hcell).symm.trans
        ((congrArg (fun q => (bkHocolimToNerve D).app (op ⦋k⦌) q) hi).trans hp)
    have hzbase : (nerve J).map α.op c ∈ ((nerve J).skeleton (n + 2)).obj (op ⦋k⦌) := by
      rw [bkSkeletalFiltration_eq_preimage] at hz
      exact hbase ▸ hz
    have hle := (Subcomplex.ofSimplex_le_iff _ _).mpr hzbase
    rw [Subcomplex.ofSimplex_map_of_epi (X := nerve J) α c] at hle
    have hm : m < n + 2 := ((nerve J).mem_skeleton_obj_iff_of_nonDegenerate ⟨c, hc⟩ (n + 2)).mp
      ((Subcomplex.ofSimplex_le_iff _ _).mp hle)
    change z ∈ (bkSkeletalFiltration D n).obj (op ⦋k⦌) ∨
      z ∈ Set.range ((bkNondegenerateCellMap D (n + 1)).app (op ⦋k⦌))
    by_cases hmn : m ≤ n
    · left
      rw [bkSkeletalFiltration_eq_preimage]
      change (bkHocolimToNerve D).app (op ⦋k⦌) z ∈ ((nerve J).skeleton (n + 1)).obj (op ⦋k⦌)
      rw [hbase]
      exact ((nerve J).skeleton (n + 1)).map α.op
        ((nerve J).mem_skeleton c (Nat.lt_succ_of_le hmn))
    · have hmn : m = n + 1 := by omega
      subst m
      right
      refine ⟨(Sigma.ι (fun c : (nerve J).nonDegenerate (n + 1) =>
        D.obj c.1.left ⊗ (Δ[n + 1] : SSet.{max u v})) ⟨c, hc⟩).app (op ⦋k⦌)
          ⟨x, stdSimplex.objEquiv.symm α⟩, ?_⟩
      exact (bkNondegenerateCellMap_ι_apply D (n + 1) ⟨c, hc⟩ (op ⦋k⦌)
        ⟨x, stdSimplex.objEquiv.symm α⟩).trans hcell
  · exact sup_le (bkStage_mono D (Nat.le_succ n)) (range_bkNondegenerateCellMap_le D (n + 1))

/-- The canonical inclusion between actual outer BK stages. -/
def bkSkeletalFiltrationMap {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) {m n : ℕ} (h : m ≤ n) :
    (bkSkeletalFiltration D m : SSet.{max u v}) ⟶ (bkSkeletalFiltration D n : SSet.{max u v}) :=
  Subcomplex.homOfLE (bkStage_mono D h)

private theorem bkSkeletalFiltrationMap_ι_aux {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) {m n : ℕ} (h : m ≤ n) :
    bkSkeletalFiltrationMap D h ≫ (bkSkeletalFiltration D n).ι = (bkSkeletalFiltration D m).ι :=
  Subcomplex.homOfLE_ι (bkStage_mono D h)

@[reassoc]
theorem bkSkeletalFiltrationMap_ι {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) {m n : ℕ} (h : m ≤ n) :
    bkSkeletalFiltrationMap D h ≫ (bkSkeletalFiltration D n).ι = (bkSkeletalFiltration D m).ι :=
  bkSkeletalFiltrationMap_ι_aux D h

instance bkSkeletalFiltrationMap_mono {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) {m n : ℕ} (h : m ≤ n) : Mono (bkSkeletalFiltrationMap D h) :=
  mono_of_mono_fac (bkSkeletalFiltrationMap_ι D h)

/-- The actual nondegenerate-cell map with codomain restricted to its stage. -/
def bkNondegenerateCellToStage {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    bkNondegenerateCellDomain D n ⟶ (bkSkeletalFiltration D n : SSet.{max u v}) :=
  Subcomplex.lift (bkNondegenerateCellMap D n) (range_bkNondegenerateCellMap_le D n)

@[reassoc]
theorem bkNondegenerateCellToStage_ι {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    bkNondegenerateCellToStage D n ≫ (bkSkeletalFiltration D n).ι = bkNondegenerateCellMap D n :=
  Subcomplex.lift_ι _ _

private def nondegenerateBoundaryPreimageIso {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    bkNondegenerateCellBoundary D (n + 1) ≅
      ((bkSkeletalFiltration D n).preimage (bkNondegenerateCellMap D (n + 1)) : SSet.{max u v}) :=
  asIso (Subcomplex.toRange (bkNondegenerateCellBoundaryInclusion D (n + 1))) ≪≫
    Subcomplex.eqToIso (bkNondegenerateCellMap_preimage_stage D n).symm

private theorem nondegenerateBoundaryPreimageIso_hom_ι
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    (nondegenerateBoundaryPreimageIso D n).hom ≫
      ((bkSkeletalFiltration D n).preimage (bkNondegenerateCellMap D (n + 1))).ι =
        bkNondegenerateCellBoundaryInclusion D (n + 1) := by
  simp [nondegenerateBoundaryPreimageIso]

/-- The actual attachment of the coefficient times boundary to the preceding
stage. Its first coefficient changes on a face by `bkChainFirstArrow`. -/
def bkNondegenerateCellAttachment {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    bkNondegenerateCellBoundary D (n + 1) ⟶ (bkSkeletalFiltration D n : SSet.{max u v}) :=
  (nondegenerateBoundaryPreimageIso D n).hom ≫
    (bkSkeletalFiltration D n).fromPreimage (bkNondegenerateCellMap D (n + 1))

private theorem bkNondegenerateCellAttachment_ι_aux
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    bkNondegenerateCellAttachment D n ≫ (bkSkeletalFiltration D n).ι =
      bkNondegenerateCellBoundaryInclusion D (n + 1) ≫ bkNondegenerateCellMap D (n + 1) := by
  dsimp only [bkNondegenerateCellAttachment]
  rw [Category.assoc, Subcomplex.fromPreimage_ι, ← Category.assoc,
    nondegenerateBoundaryPreimageIso_hom_ι]

@[reassoc]
theorem bkNondegenerateCellAttachment_ι
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    bkNondegenerateCellAttachment D n ≫ (bkSkeletalFiltration D n).ι =
      bkNondegenerateCellBoundaryInclusion D (n + 1) ≫ bkNondegenerateCellMap D (n + 1) :=
  bkNondegenerateCellAttachment_ι_aux D n

/-- The complete actual nondegenerate-coefficient attachment square. The
simplex characteristics may identify boundary points and faces may degenerate. -/
theorem bkSkeletalFiltrationSucc_nonDegenerate_isPushout
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    IsPushout (bkNondegenerateCellAttachment D n)
      (bkNondegenerateCellBoundaryInclusion D (n + 1))
      (bkSkeletalFiltrationMap D (Nat.le_succ n))
      (bkNondegenerateCellToStage D (n + 1)) := by
  have h := Subcomplex.preimageSupRange_isPushout (bkSkeletalFiltration D n)
    (bkNondegenerateCellMap D (n + 1)) (bkNondegenerateCellMap_injective_off_stage D n)
  apply h.of_iso' (nondegenerateBoundaryPreimageIso D n) (Iso.refl _) (Iso.refl _)
    (Subcomplex.eqToIso (bkSkeletalFiltration_succ_eq_sup_nonDegenerateCells D n))
  · simp [bkNondegenerateCellAttachment]
  · simpa using nondegenerateBoundaryPreimageIso_hom_ι D n
  · apply (cancel_mono
      (bkSkeletalFiltration D n ⊔ Subcomplex.range (bkNondegenerateCellMap D (n + 1))).ι).mp
    simp [bkSkeletalFiltrationMap_ι]
  · apply (cancel_mono
      (bkSkeletalFiltration D n ⊔ Subcomplex.range (bkNondegenerateCellMap D (n + 1))).ι).mp
    simp [bkNondegenerateCellToStage_ι]

/-- Realization preserves the complete actual coefficient-cell attachment
square. No product hypothesis on the coefficient realization is added. -/
theorem bkSkeletalFiltrationSucc_nonDegenerate_realized_isPushout
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    IsPushout (toTop.map (bkNondegenerateCellAttachment D n))
      (toTop.map (bkNondegenerateCellBoundaryInclusion D (n + 1)))
      (toTop.map (bkSkeletalFiltrationMap D (Nat.le_succ n)))
      (toTop.map (bkNondegenerateCellToStage D (n + 1))) :=
  (bkSkeletalFiltrationSucc_nonDegenerate_isPushout D n).map toTop

private theorem finiteRightCartesianComparison_isIso (X K : SSet.{u}) [K.Finite] :
    IsIso (CartesianMonoidalCategory.prodComparison toTop X K) := by
  let _ : IsIso (Limits.prodComparison toTop K X) :=
    isIso_prodComparison_toTop_finite_arbitrary K X
  have h := Limits.map_braiding_hom_comp_prodComparison toTop (A := K) (B := X)
  let _ : IsIso (Limits.prodComparison toTop X K ≫
      (Limits.prod.braiding (toTop.obj X) (toTop.obj K)).hom) := by
    rw [← h]
    infer_instance
  let _ : IsIso (Limits.prodComparison toTop X K) :=
    IsIso.of_isIso_comp_right _ (Limits.prod.braiding (toTop.obj X) (toTop.obj K)).hom
  let _ : PreservesLimit (pair X K) toTop :=
    Limits.PreservesLimitPair.of_iso_prod_comparison toTop X K
  infer_instance

private def realizationCellProductIso (X : SSet.{u}) (n : ℕ) :
    toTop.obj (X ⊗ (Δ[n] : SSet.{u})) ≅
      TopCat.of (toTop.obj X × Convexity.StdSimplex ℝ (Fin (n + 1))) := by
  let _ : IsIso (CartesianMonoidalCategory.prodComparison toTop X (Δ[n] : SSet.{u})) :=
    finiteRightCartesianComparison_isIso _ _
  exact TopCat.isoOfHomeo
    ((TopCat.homeoOfIso (asIso (CartesianMonoidalCategory.prodComparison toTop X (Δ[n] :
      SSet.{u})))).trans
      (Homeomorph.prodCongr (Homeomorph.refl _) (SimplexCategory.toTopHomeo.{u} ⦋n⦌)))

private theorem realizationCellProductIso_hom_apply (X : SSet.{u}) (n : ℕ)
    (z : toTop.obj (X ⊗ (Δ[n] : SSet.{u}))) :
    (realizationCellProductIso X n).hom z =
      (toTop.map (CartesianMonoidalCategory.fst X (Δ[n] : SSet.{u})) z,
        SimplexCategory.toTopHomeo.{u} ⦋n⦌
          (toTop.map (CartesianMonoidalCategory.snd X (Δ[n] : SSet.{u})) z)) := by
  have hf := ConcreteCategory.congr_hom
    (CartesianMonoidalCategory.prodComparison_fst toTop X (Δ[n] : SSet.{u})) z
  have hs := ConcreteCategory.congr_hom
    (CartesianMonoidalCategory.prodComparison_snd toTop X (Δ[n] : SSet.{u})) z
  change (((CartesianMonoidalCategory.prodComparison toTop X (Δ[n] : SSet.{u})) z).1,
      SimplexCategory.toTopHomeo.{u} ⦋n⦌
        (((CartesianMonoidalCategory.prodComparison toTop X (Δ[n] : SSet.{u})) z).2)) = _
  exact Prod.ext hf (congrArg (SimplexCategory.toTopHomeo.{u} ⦋n⦌) hs)

private def nativeCellProductMap {X Y : SSet.{u}} {m n : ℕ}
    (f : X ⟶ Y) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    TopCat.of (toTop.obj X × Convexity.StdSimplex ℝ (Fin (m + 1))) ⟶
      TopCat.of (toTop.obj Y × Convexity.StdSimplex ℝ (Fin (n + 1))) :=
  TopCat.ofHom ((toTop.map f).hom.prodMap (stdSimplex.toTopMap θ).hom)

private theorem realizationCellProductIso_natural {X Y : SSet.{u}} {m n : ℕ}
    (f : X ⟶ Y) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    toTop.map (f ⊗ₘ (SSet.stdSimplex : SimplexCategory ⥤ SSet.{u}).map θ) ≫
      (realizationCellProductIso Y n).hom =
    (realizationCellProductIso X m).hom ≫ nativeCellProductMap f θ := by
  apply TopCat.ext
  intro z
  change (realizationCellProductIso Y n).hom
      (toTop.map (f ⊗ₘ (SSet.stdSimplex : SimplexCategory ⥤ SSet.{u}).map θ) z) =
    (toTop.map f ((realizationCellProductIso X m).hom z).1,
      Convexity.StdSimplex.map θ ((realizationCellProductIso X m).hom z).2)
  rw [realizationCellProductIso_hom_apply, realizationCellProductIso_hom_apply]
  have hf := congrArg toTop.map
    (CartesianMonoidalCategory.tensorHom_fst f ((SSet.stdSimplex : SimplexCategory ⥤
      SSet.{u}).map θ))
  have hs := congrArg toTop.map
    (CartesianMonoidalCategory.tensorHom_snd f ((SSet.stdSimplex : SimplexCategory ⥤
      SSet.{u}).map θ))
  simp only [Functor.map_comp] at hf hs
  apply Prod.ext
  · exact ConcreteCategory.congr_hom hf z
  · exact (congrArg (SimplexCategory.toTopHomeo.{u} ⦋n⦌)
      (ConcreteCategory.congr_hom hs z)).trans
      (SimplexCategory.toTopHomeo_naturality_apply θ
        (toTop.map (CartesianMonoidalCategory.snd X (Δ[m] : SSet.{u})) z))

private theorem realizationCellProductIso_inv_natural {X Y : SSet.{u}} {m n : ℕ}
    (f : X ⟶ Y) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (realizationCellProductIso X m).inv ≫
      toTop.map (f ⊗ₘ (SSet.stdSimplex : SimplexCategory ⥤ SSet.{u}).map θ) =
    nativeCellProductMap f θ ≫ (realizationCellProductIso Y n).inv := by
  apply (cancel_mono (realizationCellProductIso Y n).hom).mp
  calc
    ((realizationCellProductIso X m).inv ≫
        toTop.map (f ⊗ₘ (SSet.stdSimplex : SimplexCategory ⥤ SSet.{u}).map θ)) ≫
          (realizationCellProductIso Y n).hom =
      (realizationCellProductIso X m).inv ≫
        (toTop.map (f ⊗ₘ (SSet.stdSimplex : SimplexCategory ⥤ SSet.{u}).map θ) ≫
          (realizationCellProductIso Y n).hom) := Category.assoc _ _ _
    _ = (realizationCellProductIso X m).inv ≫
        ((realizationCellProductIso X m).hom ≫ nativeCellProductMap f θ) := by
      rw [realizationCellProductIso_natural]
    _ = nativeCellProductMap f θ := by simp
    _ = (nativeCellProductMap f θ ≫ (realizationCellProductIso Y n).inv) ≫
        (realizationCellProductIso Y n).hom := by simp [Category.assoc]

/-- The actual realization of a coefficient cell is the native product of
its coefficient realization and standard topological simplex, in every
coefficient universe. The simplex is the only finite factor. -/
def bkChainCellProductIso {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) {n : ℕ} (c : ComposableArrows J n) :
    toTop.obj (D.obj c.left ⊗ (Δ[n] : SSet.{max u v})) ≅
      TopCat.of (toTop.obj (D.obj c.left) × Convexity.StdSimplex ℝ (Fin (n + 1))) :=
  realizationCellProductIso (D.obj c.left) n

/-- Both actual coordinates of the coefficient-cell realization isomorphism. -/
theorem bkChainCellProductIso_hom_apply {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) {n : ℕ} (c : ComposableArrows J n)
    (z : toTop.obj (D.obj c.left ⊗ (Δ[n] : SSet.{max u v}))) :
    (bkChainCellProductIso D c).hom z =
      (toTop.map (CartesianMonoidalCategory.fst (D.obj c.left) (Δ[n] : SSet.{max u v})) z,
        SimplexCategory.toTopHomeo.{max u v} ⦋n⦌
          (toTop.map (CartesianMonoidalCategory.snd (D.obj c.left) (Δ[n] : SSet.{max u v})) z)) :=
  realizationCellProductIso_hom_apply (D.obj c.left) n z

/-- The actual realized coefficient cell, in native coefficient and simplex
coordinates. Degenerate chains are allowed. -/
def bkRealizedChainCell {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) {n : ℕ} (c : ComposableArrows J n) :
    TopCat.of (toTop.obj (D.obj c.left) × Convexity.StdSimplex ℝ (Fin (n + 1))) ⟶
      toTop.obj (bkHocolim D) :=
  (bkChainCellProductIso D c).inv ≫ toTop.map (bkChainCellMap D c)

/-- The same actual realized cell with codomain restricted to its stage. -/
def bkRealizedChainCellToStage {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) {n : ℕ} (c : ComposableArrows J n) :
    TopCat.of (toTop.obj (D.obj c.left) × Convexity.StdSimplex ℝ (Fin (n + 1))) ⟶
      toTop.obj (bkSkeletalFiltration D n : SSet.{max u v}) :=
  (bkChainCellProductIso D c).inv ≫ toTop.map (bkChainCellToStage D c)

@[reassoc]
theorem bkRealizedChainCellToStage_ι {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) {n : ℕ} (c : ComposableArrows J n) :
    bkRealizedChainCellToStage D c ≫ toTop.map (bkSkeletalFiltration D n).ι =
      bkRealizedChainCell D c := by
  dsimp only [bkRealizedChainCellToStage, bkRealizedChainCell]
  rw [Category.assoc, ← Functor.map_comp, bkChainCellToStage_ι]

/-- The actual base coordinate of the native realized cell is the chain's
characteristic map evaluated at its original simplex coordinate. -/
theorem bkRealizedChainCell_projection_apply {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) {n : ℕ} (c : ComposableArrows J n)
    (x : toTop.obj (D.obj c.left)) (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    toTop.map (bkHocolimToNerve D) (bkRealizedChainCell D c (x, t)) =
      toTop.map (yonedaEquiv.symm c) ((SimplexCategory.toTopHomeo.{max u v} ⦋n⦌).symm t) := by
  let q := (bkChainCellProductIso D c).inv (x, t)
  have he : (bkChainCellProductIso D c).hom q = (x, t) :=
    ConcreteCategory.congr_hom (bkChainCellProductIso D c).inv_hom_id (x, t)
  have hs : SimplexCategory.toTopHomeo.{max u v} ⦋n⦌
      (toTop.map (CartesianMonoidalCategory.snd (D.obj c.left) (Δ[n] : SSet.{max u v})) q) = t :=
    congrArg Prod.snd ((bkChainCellProductIso_hom_apply D c q).symm.trans he)
  have hq : toTop.map (CartesianMonoidalCategory.snd (D.obj c.left) (Δ[n] : SSet.{max u v})) q =
      (SimplexCategory.toTopHomeo.{max u v} ⦋n⦌).symm t :=
    (SimplexCategory.toTopHomeo.{max u v} ⦋n⦌).injective
      (hs.trans ((SimplexCategory.toTopHomeo.{max u v} ⦋n⦌).apply_symm_apply t).symm)
  have hp := congrArg toTop.map (bkChainCellMap_comp_projection D c)
  simp only [Functor.map_comp] at hp
  have h := ConcreteCategory.congr_hom hp q
  let f : (Δ[n] : SSet.{max u v}) ⟶ nerve J := yonedaEquiv.symm c
  change toTop.map (bkHocolimToNerve D) (toTop.map (bkChainCellMap D c) q) =
    toTop.map f
      (toTop.map (CartesianMonoidalCategory.snd (D.obj c.left) (Δ[n] : SSet.{max u v})) q) at h
  change toTop.map (bkHocolimToNerve D) (toTop.map (bkChainCellMap D c) q) = _
  exact h.trans (congrArg (fun z : toTop.obj (Δ[n] : SSet.{max u v}) => toTop.map f z) hq)

set_option backward.isDefEq.respectTransparency false in
/-- The full actual realized coefficient-cell face square in native
coordinates, including faces that are degenerate. -/
@[reassoc]
theorem bkRealizedChainCell_reindex {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) {m n : ℕ} (c : ComposableArrows J n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    TopCat.ofHom ((ContinuousMap.id (toTop.obj (D.obj c.left))).prodMap
        (stdSimplex.toTopMap θ).hom) ≫ bkRealizedChainCell D c =
      TopCat.ofHom ((toTop.map (D.map (bkChainFirstArrow c θ))).hom.prodMap
        (ContinuousMap.id (Convexity.StdSimplex ℝ (Fin (m + 1))))) ≫
          bkRealizedChainCell D ((nerve J).map θ.op c) := by
  let X := D.obj c.left
  let d := (nerve J).map θ.op c
  let f := D.map (bkChainFirstArrow c θ)
  let L := TopCat.ofHom ((ContinuousMap.id (toTop.obj X)).prodMap (stdSimplex.toTopMap θ).hom)
  let R := TopCat.ofHom ((toTop.map f).hom.prodMap
    (ContinuousMap.id (Convexity.StdSimplex ℝ (Fin (m + 1)))))
  have hL : nativeCellProductMap (𝟙 X) θ = L := by
    apply TopCat.ext
    intro z
    change (toTop.map (𝟙 X) z.1, Convexity.StdSimplex.map θ z.2) =
      (z.1, Convexity.StdSimplex.map θ z.2)
    rw [toTop.map_id]
    rfl
  have hR : nativeCellProductMap f (𝟙 ⦋m⦌) = R := by
    apply TopCat.ext
    intro z
    change (toTop.map f z.1, SimplexCategory.toTop₀.map (𝟙 ⦋m⦌) z.2) =
      (toTop.map f z.1, z.2)
    rw [SimplexCategory.toTop₀.map_id]
    rfl
  have hl : (realizationCellProductIso X m).inv ≫
      toTop.map (X ◁ (SSet.stdSimplex : SimplexCategory ⥤ SSet.{max u v}).map θ) =
        L ≫ (realizationCellProductIso X n).inv := by
    rw [← hL]
    simpa only [id_tensorHom] using
      realizationCellProductIso_inv_natural (𝟙 X) θ
  have hr : (realizationCellProductIso X m).inv ≫ toTop.map (f ▷ (Δ[m] : SSet.{max u v})) =
      R ≫ (realizationCellProductIso (D.obj d.left) m).inv := by
    have hStd : (SSet.stdSimplex : SimplexCategory ⥤ SSet.{max u v}).map (𝟙 ⦋m⦌) =
        𝟙 (Δ[m] : SSet.{max u v}) := (SSet.stdSimplex : SimplexCategory ⥤ SSet.{max u v}).map_id _
    have h := realizationCellProductIso_inv_natural f (𝟙 ⦋m⦌)
    rw [hStd, tensorHom_id, hR] at h
    exact h
  change L ≫ ((realizationCellProductIso X n).inv ≫ toTop.map (bkChainCellMap D c)) =
    R ≫ ((realizationCellProductIso (D.obj d.left) m).inv ≫ toTop.map (bkChainCellMap D d))
  calc
    L ≫ ((realizationCellProductIso X n).inv ≫ toTop.map (bkChainCellMap D c)) =
        (L ≫ (realizationCellProductIso X n).inv) ≫ toTop.map (bkChainCellMap D c) :=
      (Category.assoc _ _ _).symm
    _ = ((realizationCellProductIso X m).inv ≫
        toTop.map (X ◁ (SSet.stdSimplex : SimplexCategory ⥤ SSet.{max u v}).map θ)) ≫
          toTop.map (bkChainCellMap D c) := congrArg (fun q => q ≫ toTop.map (bkChainCellMap D
            c)) hl.symm
    _ = (realizationCellProductIso X m).inv ≫
        toTop.map ((X ◁ (SSet.stdSimplex : SimplexCategory ⥤ SSet.{max u v}).map θ) ≫
          bkChainCellMap D c) := by rw [Category.assoc, ← Functor.map_comp]
    _ = (realizationCellProductIso X m).inv ≫
        toTop.map ((f ▷ (Δ[m] : SSet.{max u v})) ≫ bkChainCellMap D d) := by
      rw [bkChainCellMap_reindex]
    _ = ((realizationCellProductIso X m).inv ≫ toTop.map (f ▷ (Δ[m] : SSet.{max u v}))) ≫
        toTop.map (bkChainCellMap D d) := by rw [Functor.map_comp, Category.assoc]
    _ = (R ≫ (realizationCellProductIso (D.obj d.left) m).inv) ≫
        toTop.map (bkChainCellMap D d) := congrArg (fun q => q ≫ toTop.map (bkChainCellMap D d)) hr
    _ = R ≫ ((realizationCellProductIso (D.obj d.left) m).inv ≫
        toTop.map (bkChainCellMap D d)) := Category.assoc _ _ _

private abbrev nativeNondegenerateCellFamily {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) (c : (nerve J).nonDegenerate n) : TopCat.{max u v} :=
  TopCat.of (toTop.obj (D.obj c.1.left) × Convexity.StdSimplex ℝ (Fin (n + 1)))

/-- The actual realized coproduct of nondegenerate coefficient cells is
the native disjoint family of their coefficient and simplex coordinates. -/
def bkNondegenerateCellsProductIso {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    toTop.obj (bkNondegenerateCellDomain D n) ≅
      TopCat.of (Σ c : (nerve J).nonDegenerate n,
        toTop.obj (D.obj c.1.left) × Convexity.StdSimplex ℝ (Fin (n + 1))) :=
  (asIso (Limits.sigmaComparison toTop
    (fun c : (nerve J).nonDegenerate n => D.obj c.1.left ⊗ (Δ[n] : SSet.{max u v})))).symm ≪≫
      Limits.Sigma.mapIso (fun c => bkChainCellProductIso D c.1) ≪≫
        TopCat.sigmaIsoSigma (nativeNondegenerateCellFamily D n)

private theorem bkNondegenerateCellsProductIso_hom_cell_aux
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate n) :
    toTop.map (Sigma.ι (fun c : (nerve J).nonDegenerate n =>
      D.obj c.1.left ⊗ (Δ[n] : SSet.{max u v})) c) ≫ (bkNondegenerateCellsProductIso D n).hom =
        (bkChainCellProductIso D c.1).hom ≫ TopCat.sigmaι (nativeNondegenerateCellFamily D n) c
          := by
  dsimp only [bkNondegenerateCellsProductIso, Iso.trans_hom, Iso.symm_hom, asIso_inv]
  rw [← Category.assoc, ← Category.assoc, Limits.map_ι_comp_inv_sigmaComparison]
  rw [Category.assoc, ← Category.assoc, Limits.Sigma.ι_mapIso_hom]
  rw [Category.assoc, TopCat.sigmaIsoSigma_hom_ι]

/-- The actual coproduct inclusion retains its exact chain and both
native coefficient-cell coordinates. -/
theorem bkNondegenerateCellsProductIso_hom_cell_apply
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate n)
    (q : toTop.obj (D.obj c.1.left ⊗ (Δ[n] : SSet.{max u v}))) :
    (bkNondegenerateCellsProductIso D n).hom
      (toTop.map (Sigma.ι (fun c : (nerve J).nonDegenerate n =>
        D.obj c.1.left ⊗ (Δ[n] : SSet.{max u v})) c) q) =
          ⟨c, (bkChainCellProductIso D c.1).hom q⟩ :=
  ConcreteCategory.congr_hom (bkNondegenerateCellsProductIso_hom_cell_aux D n c) q

/-- The inverse disjoint-cell dictionary is the actual coproduct inclusion
after the native coefficient-cell realization isomorphism. -/
theorem bkNondegenerateCellsProductIso_inv_cell_apply
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate n) (x : toTop.obj (D.obj c.1.left))
    (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    (bkNondegenerateCellsProductIso D n).inv ⟨c, x, t⟩ =
      toTop.map (Sigma.ι (fun c : (nerve J).nonDegenerate n =>
        D.obj c.1.left ⊗ (Δ[n] : SSet.{max u v})) c)
          ((bkChainCellProductIso D c.1).inv (x, t)) := by
  apply (TopCat.homeoOfIso (bkNondegenerateCellsProductIso D n)).injective
  have hl := ConcreteCategory.congr_hom (bkNondegenerateCellsProductIso D n).inv_hom_id ⟨c, x, t⟩
  have hr := bkNondegenerateCellsProductIso_hom_cell_apply D n c ((bkChainCellProductIso D
    c.1).inv (x, t))
  have hc := ConcreteCategory.congr_hom (bkChainCellProductIso D c.1).inv_hom_id (x, t)
  exact hl.trans (hr.trans (congrArg (fun p => Sigma.mk c p) hc)).symm

private def realizedSigmaEquiv {I : Type u} (F : I → SSet.{u}) :
    toTop.obj (∐ F) ≃ Σ i, toTop.obj (F i) :=
  (TopCat.homeoOfIso ((asIso (Limits.sigmaComparison toTop F)).symm ≪≫
    TopCat.sigmaIsoSigma (fun i => toTop.obj (F i)))).toEquiv

private theorem realizedSigmaEquiv_ι {I : Type u} (F : I → SSet.{u})
    (i : I) (q : toTop.obj (F i)) :
    realizedSigmaEquiv F (toTop.map (Sigma.ι F i) q) = ⟨i, q⟩ := by
  have h := ConcreteCategory.congr_hom (Limits.map_ι_comp_inv_sigmaComparison toTop F i) q
  exact (congrArg (fun y => (TopCat.sigmaIsoSigma (fun i => toTop.obj (F i))).hom y) h).trans
    (TopCat.sigmaIsoSigma_hom_ι_apply (fun i => toTop.obj (F i)) i q)

private theorem realizedSigma_jointly_surjective {I : Type u} (F : I → SSet.{u})
    (y : toTop.obj (∐ F)) : ∃ (i : I) (q : toTop.obj (F i)), toTop.map (Sigma.ι F i) q = y := by
  refine ⟨(realizedSigmaEquiv F y).1, (realizedSigmaEquiv F y).2,
    (realizedSigmaEquiv F).injective ?_⟩
  exact realizedSigmaEquiv_ι F (realizedSigmaEquiv F y).1 (realizedSigmaEquiv F y).2

private def realizationProductPoint (X K : SSet.{u}) [K.Finite]
    (x : toTop.obj X) (y : toTop.obj K) : toTop.obj (X ⊗ K) := by
  let _ : IsIso (CartesianMonoidalCategory.prodComparison toTop X K) :=
    finiteRightCartesianComparison_isIso X K
  exact inv (CartesianMonoidalCategory.prodComparison toTop X K) (x, y)

private theorem realizationProductPoint_fst (X K : SSet.{u}) [K.Finite]
    (x : toTop.obj X) (y : toTop.obj K) :
    toTop.map (CartesianMonoidalCategory.fst X K) (realizationProductPoint X K x y) = x := by
  let _ : IsIso (CartesianMonoidalCategory.prodComparison toTop X K) :=
    finiteRightCartesianComparison_isIso X K
  exact ConcreteCategory.congr_hom
    (CartesianMonoidalCategory.inv_prodComparison_map_fst toTop X K) (x, y)

private theorem realizationProductPoint_snd (X K : SSet.{u}) [K.Finite]
    (x : toTop.obj X) (y : toTop.obj K) :
    toTop.map (CartesianMonoidalCategory.snd X K) (realizationProductPoint X K x y) = y := by
  let _ : IsIso (CartesianMonoidalCategory.prodComparison toTop X K) :=
    finiteRightCartesianComparison_isIso X K
  exact ConcreteCategory.congr_hom
    (CartesianMonoidalCategory.inv_prodComparison_map_snd toTop X K) (x, y)

private theorem realizationCellProductIso_boundary_apply (X : SSet.{u}) (n : ℕ)
    (q : toTop.obj (X ⊗ (boundary n : SSet.{u}))) :
    (realizationCellProductIso X n).hom (toTop.map (X ◁ (boundary n).ι) q) =
      (toTop.map (CartesianMonoidalCategory.fst X (boundary n : SSet.{u})) q,
        SimplexCategory.toTopHomeo.{u} ⦋n⦌
          (toTop.map (boundary n).ι
            (toTop.map (CartesianMonoidalCategory.snd X (boundary n : SSet.{u})) q))) := by
  have hf := congrArg toTop.map (CartesianMonoidalCategory.whiskerLeft_fst X (boundary n).ι)
  have hs := congrArg toTop.map (CartesianMonoidalCategory.whiskerLeft_snd X (boundary n).ι)
  simp only [Functor.map_comp] at hf hs
  exact (realizationCellProductIso_hom_apply X n (toTop.map (X ◁ (boundary n).ι) q)).trans
    (Prod.ext (ConcreteCategory.congr_hom hf q)
      (congrArg (SimplexCategory.toTopHomeo.{u} ⦋n⦌) (ConcreteCategory.congr_hom hs q)))

private theorem bkNondegenerateCellsProductIso_hom_boundary_apply
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate n)
    (q : toTop.obj (D.obj c.1.left ⊗ (boundary n : SSet.{max u v}))) :
    (bkNondegenerateCellsProductIso D n).hom
      (toTop.map (bkNondegenerateCellBoundaryInclusion D n)
        (toTop.map (Sigma.ι (fun c : (nerve J).nonDegenerate n =>
          D.obj c.1.left ⊗ (boundary n : SSet.{max u v})) c) q)) =
      ⟨c, toTop.map
        (CartesianMonoidalCategory.fst (D.obj c.1.left) (boundary n : SSet.{max u v})) q,
        SimplexCategory.toTopHomeo.{max u v} ⦋n⦌
          (toTop.map (boundary n).ι
            (toTop.map
              (CartesianMonoidalCategory.snd (D.obj c.1.left) (boundary n : SSet.{max u v}))
              q))⟩ := by
  have hb := congrArg toTop.map (bkNondegenerateCellBoundaryInclusion_ι D n c)
  simp only [Functor.map_comp] at hb
  have h := ConcreteCategory.congr_hom hb q
  exact (congrArg (fun y => (bkNondegenerateCellsProductIso D n).hom y) h).trans
    ((bkNondegenerateCellsProductIso_hom_cell_apply D n c
      (toTop.map (D.obj c.1.left ◁ (boundary n).ι) q)).trans
        (congrArg (fun p => Sigma.mk c p) (realizationCellProductIso_boundary_apply (D.obj
          c.1.left) n q)))

set_option backward.isDefEq.respectTransparency false in
/-- The boundary range in the actual disjoint coefficient-cell realization
is precisely the zero-coordinate locus in the native simplex coordinates. -/
theorem bkNondegenerateCellsProductIso_inv_mem_boundary_iff
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (z : Σ c : (nerve J).nonDegenerate n,
      toTop.obj (D.obj c.1.left) × Convexity.StdSimplex ℝ (Fin (n + 1))) :
    (bkNondegenerateCellsProductIso D n).inv z ∈
      Set.range (toTop.map (bkNondegenerateCellBoundaryInclusion D n)) ↔
        ∃ i, z.2.2.weights i = 0 := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨c, q, rfl⟩ := realizedSigma_jointly_surjective
      (fun c : (nerve J).nonDegenerate n => D.obj c.1.left ⊗ (boundary n : SSet.{max u v})) y
    have hp := bkNondegenerateCellsProductIso_hom_boundary_apply D n c q
    have he : (bkNondegenerateCellsProductIso D n).hom
        ((bkNondegenerateCellsProductIso D n).inv z) = z :=
      ConcreteCategory.congr_hom (bkNondegenerateCellsProductIso D n).inv_hom_id z
    have hz := hp.symm.trans ((congrArg (fun y => (bkNondegenerateCellsProductIso D n).hom y)
      hy).trans he)
    have hzero : ∃ i, ((SimplexCategory.toTopHomeo.{max u v} ⦋n⦌)
        (toTop.map (boundary n).ι
          (toTop.map (CartesianMonoidalCategory.snd (D.obj c.1.left) (boundary n : SSet.{max u v}))
            q))).weights i = 0 :=
      boundary.mem_zeroCoord_of_mem_realizedBoundaryRange n _ ⟨_, rfl⟩
    exact hz ▸ hzero
  · rcases z with ⟨c, x, t⟩
    rintro ⟨i, hi⟩
    obtain ⟨q, hq⟩ := mem_realizedBoundary_of_zeroCoord.{max u v} n t i hi
    let qP := realizationProductPoint (D.obj c.1.left) (boundary n : SSet.{max u v}) x q
    refine ⟨toTop.map (Sigma.ι (fun c : (nerve J).nonDegenerate n =>
      D.obj c.1.left ⊗ (boundary n : SSet.{max u v})) c) qP, ?_⟩
    apply (TopCat.homeoOfIso (bkNondegenerateCellsProductIso D n)).injective
    have hp := bkNondegenerateCellsProductIso_hom_boundary_apply D n c qP
    dsimp only [qP] at hp
    rw [realizationProductPoint_fst, realizationProductPoint_snd, hq,
      Homeomorph.apply_symm_apply] at hp
    have he := ConcreteCategory.congr_hom (bkNondegenerateCellsProductIso D n).inv_hom_id ⟨c, x, t⟩
    exact hp.trans he.symm

/-- The actual new-cell part of a stage is homeomorphic to its preimage in
the coproduct of coefficient cells. This is derived from the actual realized
attachment and its closed preceding-stage inclusion. -/
theorem bkNondegenerateCellInterior_isHomeomorph
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    IsHomeomorph
      (((Set.range (toTop.map (bkSkeletalFiltrationMap D (Nat.le_succ n))))ᶜ).restrictPreimage
        (toTop.map (bkNondegenerateCellToStage D (n + 1)))) := by
  have h := bkSkeletalFiltrationSucc_nonDegenerate_realized_isPushout D n
  have hclosed : IsClosedEmbedding (toTop.map (bkSkeletalFiltrationMap D (Nat.le_succ n))) :=
    TopCat.closedT1Embeddings_le_isClosedEmbedding _
      (closedT1Embeddings_toTop_map_of_mono (bkSkeletalFiltrationMap D (Nat.le_succ n)))
  apply TopCat.isHomeomorph_restrictPreimage_inr_of_isPushout h hclosed.isClosed_range.isOpen_compl
  · ext z
    constructor
    · intro hz
      exact (hz ⟨z, rfl⟩).elim
    · intro hz
      exact hz.elim
  · intro z hz
    rintro ⟨y, rfl⟩
    exact hz ⟨toTop.map (bkNondegenerateCellAttachment D n) y,
      ConcreteCategory.congr_hom h.w y⟩

/-- The new-cell preimage of the complement of the preceding stage is
exactly the complement of the actual coefficient-boundary inclusion. -/
theorem bkNondegenerateCellToStage_preimage_compl_range
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    (toTop.map (bkNondegenerateCellToStage D (n + 1))) ⁻¹'
      (Set.range (toTop.map (bkSkeletalFiltrationMap D (Nat.le_succ n))))ᶜ =
        (Set.range (toTop.map (bkNondegenerateCellBoundaryInclusion D (n + 1))))ᶜ := by
  have h := bkSkeletalFiltrationSucc_nonDegenerate_realized_isPushout D n
  have ht := h.map (forget TopCat)
  ext z
  constructor
  · intro hz
    rintro ⟨y, rfl⟩
    exact hz ⟨toTop.map (bkNondegenerateCellAttachment D n) y,
      ConcreteCategory.congr_hom h.w y⟩
  · intro hz
    rintro ⟨y, hy⟩
    exact (Types.pushoutCocone_inl_ne_inr_of_not_mem_range_of_isColimit ht.isColimit
      (z := y) (x := z) hz) hy

/-- In the native disjoint-cell dictionary, the part away from the
preceding stage consists exactly of positive simplex coordinates. -/
theorem bkNondegenerateCellsProductIso_inv_mem_interior_iff
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (z : Σ c : (nerve J).nonDegenerate (n + 1),
      toTop.obj (D.obj c.1.left) × Convexity.StdSimplex ℝ (Fin (n + 2))) :
    (bkNondegenerateCellsProductIso D (n + 1)).inv z ∈
      (toTop.map (bkNondegenerateCellToStage D (n + 1))) ⁻¹'
        (Set.range (toTop.map (bkSkeletalFiltrationMap D (Nat.le_succ n))))ᶜ ↔
          ∀ i, 0 < z.2.2.weights i := by
  rw [bkNondegenerateCellToStage_preimage_compl_range]
  change (¬(bkNondegenerateCellsProductIso D (n + 1)).inv z ∈
    Set.range (toTop.map (bkNondegenerateCellBoundaryInclusion D (n + 1)))) ↔ _
  rw [bkNondegenerateCellsProductIso_inv_mem_boundary_iff]
  constructor
  · intro h i
    by_contra hi
    have hzero : z.2.2.weights i = 0 :=
      le_antisymm (le_of_not_gt hi) (z.2.2.weights_nonneg i)
    exact h ⟨i, hzero⟩
  · intro h
    rintro ⟨i, hi⟩
    have hp := h i
    rw [hi] at hp
    exact lt_irrefl _ hp

private abbrev positiveNativeCells {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :=
  Σ c : (nerve J).nonDegenerate n,
    toTop.obj (D.obj c.1.left) ×
      {t : Convexity.StdSimplex ℝ (Fin (n + 1)) // ∀ i, 0 < t.weights i}

private def nativeCellsPositiveSet {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    Set (Σ c : (nerve J).nonDegenerate n,
      toTop.obj (D.obj c.1.left) × Convexity.StdSimplex ℝ (Fin (n + 1))) :=
  {z | ∀ i, 0 < z.2.2.weights i}

private def positiveNativeCellInclusion {J : Type u} [Category.{v} J]
    (D : J ⥤ SSet.{max u v}) (n : ℕ) : positiveNativeCells D n →
    Σ c : (nerve J).nonDegenerate n,
      toTop.obj (D.obj c.1.left) × Convexity.StdSimplex ℝ (Fin (n + 1)) :=
  fun z => ⟨z.1, z.2.1, z.2.2.1⟩

private theorem positiveNativeCellInclusion_openEmbedding
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    IsOpenEmbedding (positiveNativeCellInclusion D n) := by
  rw [isOpenEmbedding_iff_continuous_injective_isOpenMap]
  refine ⟨?_, ?_, ?_⟩
  · exact continuous_sigma (fun _ => continuous_sigmaMk.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  · rintro ⟨c, x, t⟩ ⟨d, y, s⟩ h
    have hcd : c = d := congrArg Sigma.fst h
    subst d
    have hp : (x, t.1) = (y, s.1) := eq_of_heq (Sigma.mk.inj h).2
    have hxy : x = y :=
      congrArg (fun p : toTop.obj (D.obj c.1.left) × Convexity.StdSimplex ℝ (Fin (n + 1)) => p.1) hp
    have hts : t = s := Subtype.ext
      (congrArg (fun p : toTop.obj (D.obj c.1.left) × Convexity.StdSimplex ℝ (Fin (n + 1)) =>
        p.2) hp)
    subst y
    subst s
    rfl
  · have hpos : IsOpen (realizationCellInterior.openCell n) :=
      realizationCellInterior.openCell_isOpen n
    exact isOpenMap_sigma.2 (fun _ => isOpenMap_sigmaMk.comp
      (IsOpenMap.id.prodMap hpos.isOpenEmbedding_subtypeVal.isOpenMap))

private theorem positiveNativeCellInclusion_range
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    Set.range (positiveNativeCellInclusion D n) = nativeCellsPositiveSet D n := by
  ext z
  constructor
  · rintro ⟨⟨c, x, t⟩, rfl⟩
    exact t.2
  · rcases z with ⟨c, x, t⟩
    intro ht
    exact ⟨⟨c, x, ⟨t, ht⟩⟩, rfl⟩

private def positiveNativeCellsHomeomorph
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    positiveNativeCells D n ≃ₜ nativeCellsPositiveSet D n :=
  (positiveNativeCellInclusion_openEmbedding D n).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (positiveNativeCellInclusion_range D n))

private theorem nativePositiveCells_image
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    (TopCat.homeoOfIso (bkNondegenerateCellsProductIso D (n + 1))).symm ''
      nativeCellsPositiveSet D (n + 1) =
    (toTop.map (bkNondegenerateCellToStage D (n + 1))) ⁻¹'
      (Set.range (toTop.map (bkSkeletalFiltrationMap D (Nat.le_succ n))))ᶜ := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (bkNondegenerateCellsProductIso_inv_mem_interior_iff D n z).mpr hz
  · intro hy
    let e := TopCat.homeoOfIso (bkNondegenerateCellsProductIso D (n + 1))
    have he : e.symm (e y) = y := e.symm_apply_apply y
    refine ⟨e y, ?_, he⟩
    exact (bkNondegenerateCellsProductIso_inv_mem_interior_iff D n (e y)).mp (he.symm ▸ hy)

private def nondegenerateCellInteriorProductHomeomorph
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    positiveNativeCells D (n + 1) ≃ₜ
      ↥((Set.range (toTop.map (bkSkeletalFiltrationMap D (Nat.le_succ n))))ᶜ) :=
  (positiveNativeCellsHomeomorph D (n + 1)).trans
    (((TopCat.homeoOfIso (bkNondegenerateCellsProductIso D (n + 1))).symm.image
      (nativeCellsPositiveSet D (n + 1))).trans
      ((Homeomorph.setCongr (nativePositiveCells_image D n)).trans
        ((bkNondegenerateCellInterior_isHomeomorph D n).homeomorph
          (((Set.range (toTop.map (bkSkeletalFiltrationMap D (Nat.le_succ n))))ᶜ).restrictPreimage
            (toTop.map (bkNondegenerateCellToStage D (n + 1)))))))

/-- The actual new-cell part of the BK stage is the native disjoint union
of coefficient realizations times open simplex interiors. No regularity or
finite coefficient hypothesis is imposed. -/
def bkNondegenerateCellInteriorProductIso
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ) :
    TopCat.of (Σ c : (nerve J).nonDegenerate (n + 1),
      toTop.obj (D.obj c.1.left) ×
        {t : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < t.weights i}) ≅
      TopCat.of ↥((Set.range (toTop.map (bkSkeletalFiltrationMap D (Nat.le_succ n))))ᶜ) :=
  TopCat.isoOfHomeo (nondegenerateCellInteriorProductHomeomorph D n)

private theorem bkNondegenerateCellInteriorProductIso_hom_aux
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1)) (x : toTop.obj (D.obj c.1.left))
    (t : {t : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < t.weights i}) :
    ((bkNondegenerateCellInteriorProductIso D n).hom ⟨c, x, t⟩).1 =
      toTop.map (bkNondegenerateCellToStage D (n + 1))
        ((bkNondegenerateCellsProductIso D (n + 1)).inv ⟨c, x, t.1⟩) := rfl

private theorem bkNondegenerateCellToStage_cell
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate n) :
    Sigma.ι (fun c : (nerve J).nonDegenerate n => D.obj c.1.left ⊗ (Δ[n] : SSet.{max u v})) c ≫
      bkNondegenerateCellToStage D n = bkChainCellToStage D c.1 := by
  apply (cancel_mono (bkSkeletalFiltration D n).ι).mp
  rw [Category.assoc, bkNondegenerateCellToStage_ι, bkNondegenerateCellMap_ι]
  exact (bkChainCellToStage_ι D c.1).symm

/-- The interior product isomorphism is the original realized cell map on
each exact chain and coefficient, with its codomain in the actual stage. -/
theorem bkNondegenerateCellInteriorProductIso_hom_apply
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) (n : ℕ)
    (c : (nerve J).nonDegenerate (n + 1)) (x : toTop.obj (D.obj c.1.left))
    (t : {t : Convexity.StdSimplex ℝ (Fin (n + 2)) // ∀ i, 0 < t.weights i}) :
    ((bkNondegenerateCellInteriorProductIso D n).hom ⟨c, x, t⟩).1 =
      bkRealizedChainCellToStage D c.1 (x, t.1) := by
  have h := bkNondegenerateCellInteriorProductIso_hom_aux D n c x t
  have hi := bkNondegenerateCellsProductIso_inv_cell_apply D (n + 1) c x t.1
  have hm := congrArg toTop.map (bkNondegenerateCellToStage_cell D (n + 1) c)
  simp only [Functor.map_comp] at hm
  have hc := ConcreteCategory.congr_hom hm ((bkChainCellProductIso D c.1).inv (x, t.1))
  exact h.trans ((congrArg (fun z => toTop.map (bkNondegenerateCellToStage D (n + 1)) z)
    hi).trans hc)

/-- The original realized chain-to-stage map in native coordinates, on the
whole closed simplex including its boundary. -/
private theorem bkRealizedChainCellToStage_eq_aux
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) {n : ℕ} (c : ComposableArrows J n) :
    bkRealizedChainCellToStage D c =
      (bkChainCellProductIso D c).inv ≫ toTop.map (bkChainCellToStage D c) := rfl

/-- The whole closed-cell characteristic, without opening the map definition. -/
theorem bkRealizedChainCellToStage_eq
    {J : Type u} [Category.{v} J] (D : J ⥤ SSet.{max u v}) {n : ℕ} (c : ComposableArrows J n) :
    bkRealizedChainCellToStage D c =
      (bkChainCellProductIso D c).inv ≫ toTop.map (bkChainCellToStage D c) :=
  bkRealizedChainCellToStage_eq_aux D c

private theorem bkChainFirstArrow_isIso_of_epi_aux
    {J : Type u} [Category.{v} J] {m n : ℕ} (c : ComposableArrows J n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) [Epi θ] : IsIso (bkChainFirstArrow c θ) := by
  let j : Fin (n + 1) := θ.toOrderHom 0
  have hj : j = 0 := by
    obtain ⟨a, ha⟩ := (SimplexCategory.epi_iff_surjective.mp (inferInstance : Epi θ)) 0
    exact le_antisymm ((θ.toOrderHom.monotone (Fin.zero_le a)).trans_eq ha) (Fin.zero_le j)
  let _ : IsIso (homOfLE (Fin.zero_le j)) := by
    have he : (homOfLE (Fin.zero_le j) : (0 : Fin (n + 1)) ⟶ j) = eqToHom hj.symm :=
      Subsingleton.elim _ _
    exact he.symm ▸ (inferInstance : IsIso (eqToHom hj.symm))
  change IsIso (c.map (homOfLE (Fin.zero_le j)))
  infer_instance

/-- An epi indexing map preserves the first vertex, so its original BK
first-coefficient arrow is an isomorphism. -/
theorem bkChainFirstArrow_isIso_of_epi
    {J : Type u} [Category.{v} J] {m n : ℕ} (c : ComposableArrows J n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) [Epi θ] : IsIso (bkChainFirstArrow c θ) :=
  bkChainFirstArrow_isIso_of_epi_aux c θ

end SSet

end
