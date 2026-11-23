/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanHomologyBicomplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
public import MathlibExt.AlgebraicTopology.SimplicialSet.HomotopyComp
public import MathlibExt.Algebra.Homology.TotalHomotopy
public import MathlibExt.Algebra.Homology.TotalComplexSymmetryDownNat
public import Mathlib.CategoryTheory.Monoidal.Closed.Types
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty

/-!
# Diagram homotopies on the actual Bousfield–Kan bar

A strictly natural family of simplicial cylinders induces vertical prisms
on the terminal-weight BK bar. Each prism retains the entire weighted outer
chain and acts on its left-endpoint coefficient. Its signed totalization
therefore preserves the horizontal degree.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial

universe w v vA uA

/-- The canonical closed structure distributes interval tensoring over coproducts. -/
local instance diagramHomotopyMonoidalClosed : MonoidalClosed SSet.{w} :=
  CategoryTheory.cartesianClosedFunctorToTypes

namespace SSet

variable {J : Type w} [Category.{v} J]
  {D E : J ⥤ SSet.{max w v}} {α β : D ⟶ E}

/-- A family of actual simplicial cylinders that is strictly natural in the
indexing category, with prescribed endpoint diagram maps. -/
structure DiagramHomotopy (α β : D ⟶ E) where
  /-- The actual cylinder at each diagram object. -/
  app (j : J) : SSet.Homotopy (α.app j) (β.app j)
  /-- Base maps commute with the entire cylinder, including its interval coordinate. -/
  naturality {j k : J} (a : j ⟶ k) :
    (D.map a ▷ (Δ[1] : SSet.{max w v})) ≫ (app k).h = (app j).h ≫ E.map a

namespace DiagramHomotopy

variable (H : DiagramHomotopy α β)

/-- The natural transformation of actual cylinders. -/
def cylinder : D ⋙ tensorRight (Δ[1] : SSet.{max w v}) ⟶ E where
  app j := (H.app j).h
  naturality _ _ a := H.naturality a

/-- The cylinder on one actual terminal-weight weighted-bar degree. -/
def barCylinder (p : ℕ) :
    StrictOrdinaryWeightedBar.wbarObj (CategoryBar.replUnit J) D p ⊗
        (Δ[1] : SSet.{max w v}) ⟶
      StrictOrdinaryWeightedBar.wbarObj (CategoryBar.replUnit J) E p :=
  inv (sigmaComparison (tensorRight (Δ[1] : SSet.{max w v}))
      (fun s : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) p =>
        D.obj s.1.left)) ≫
    StrictOrdinaryWeightedBar.wbarMapF p H.cylinder

/-- The bar cylinder fixes its weighted chain and uses the cylinder of the
coefficient at that chain's left endpoint. -/
@[reassoc]
theorem barCylinder_ι (p : ℕ)
    (s : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) p) :
    (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D p s ▷
        (Δ[1] : SSet.{max w v})) ≫ H.barCylinder p =
      (H.app s.1.left).h ≫
        StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) E p s := by
  unfold barCylinder
  change (tensorRight (Δ[1] : SSet.{max w v})).map (Sigma.ι _ s) ≫ _ = _
  rw [← Category.assoc, map_ι_comp_inv_sigmaComparison]
  exact StrictOrdinaryWeightedBar.wbarMapF_ι p H.cylinder s

/-- The actual row homotopy has the prescribed weighted-bar endpoint maps. -/
def barHomotopy (p : ℕ) :
    SSet.Homotopy
      (StrictOrdinaryWeightedBar.wbarMapF (W := CategoryBar.replUnit J) p α)
      (StrictOrdinaryWeightedBar.wbarMapF (W := CategoryBar.replUnit J) p β) where
  h := H.barCylinder p
  h₀ := by
    apply Sigma.hom_ext
    intro s
    change StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D p s ≫
        (ι₀ ≫ H.barCylinder p) = _
    calc
      _ = ι₀ ≫ ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D p s ▷
            (Δ[1] : SSet.{max w v})) ≫ H.barCylinder p) := by
        rw [← Category.assoc, ← ι₀_comp, Category.assoc]
      _ = ι₀ ≫ ((H.app s.1.left).h ≫
          StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) E p s) := by
        rw [barCylinder_ι]
      _ = α.app s.1.left ≫
          StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) E p s := by
        rw [← Category.assoc, (H.app s.1.left).h₀]
      _ = _ := (StrictOrdinaryWeightedBar.wbarMapF_ι p α s).symm
  h₁ := by
    apply Sigma.hom_ext
    intro s
    change StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D p s ≫
        (ι₁ ≫ H.barCylinder p) = _
    calc
      _ = ι₁ ≫ ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D p s ▷
            (Δ[1] : SSet.{max w v})) ≫ H.barCylinder p) := by
        rw [← Category.assoc, ← ι₁_comp, Category.assoc]
      _ = ι₁ ≫ ((H.app s.1.left).h ≫
          StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) E p s) := by
        rw [barCylinder_ι]
      _ = β.app s.1.left ≫
          StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) E p s := by
        rw [← Category.assoc, (H.app s.1.left).h₁]
      _ = _ := (StrictOrdinaryWeightedBar.wbarMapF_ι p β s).symm
  rel := by
    ext a z
    exact z.1.2.elim

private theorem barCylinder_naturality_of_components {p q : ℕ}
    (k : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) p →
      StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) q)
    (a : ∀ s, s.1.left ⟶ (k s).1.left)
    (f : StrictOrdinaryWeightedBar.wbarObj (CategoryBar.replUnit J) D p ⟶
      StrictOrdinaryWeightedBar.wbarObj (CategoryBar.replUnit J) D q)
    (g : StrictOrdinaryWeightedBar.wbarObj (CategoryBar.replUnit J) E p ⟶
      StrictOrdinaryWeightedBar.wbarObj (CategoryBar.replUnit J) E q)
    (hf : ∀ s, StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D p s ≫ f =
      D.map (a s) ≫ StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D q (k s))
    (hg : ∀ s, StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) E p s ≫ g =
      E.map (a s) ≫ StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) E q (k s)) :
    (f ▷ (Δ[1] : SSet.{max w v})) ≫ H.barCylinder q = H.barCylinder p ≫ g := by
  apply (isColimitOfHasCoproductOfPreservesColimit (tensorRight (Δ[1] : SSet.{max w v}))
    (fun s : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) p =>
      D.obj s.1.left)).hom_ext
  rintro ⟨s⟩
  change (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D p s ▷
      (Δ[1] : SSet.{max w v})) ≫ ((f ▷ (Δ[1] : SSet.{max w v})) ≫ H.barCylinder q) = _
  calc
    _ = ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D p s ≫ f) ▷
        (Δ[1] : SSet.{max w v})) ≫ H.barCylinder q := by
      rw [comp_whiskerRight, Category.assoc]
    _ = ((D.map (a s) ≫
        StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D q (k s)) ▷
        (Δ[1] : SSet.{max w v})) ≫ H.barCylinder q := by rw [hf]
    _ = (D.map (a s) ▷ (Δ[1] : SSet.{max w v})) ≫
        ((H.app (k s).1.left).h ≫
          StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) E q (k s)) := by
      rw [comp_whiskerRight, Category.assoc, barCylinder_ι]
    _ = (H.app s.1.left).h ≫ (E.map (a s) ≫
        StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) E q (k s)) := by
      rw [← Category.assoc, H.naturality, Category.assoc]
    _ = (H.app s.1.left).h ≫
        (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) E p s ≫ g) := by
      rw [hg]
    _ = (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D p s ▷
        (Δ[1] : SSet.{max w v})) ≫ (H.barCylinder p ≫ g) := by
      exact (congrArg (fun k => k ≫ g) (H.barCylinder_ι p s)).symm.trans
        (Category.assoc _ _ _)

/-- Every outer face commutes with the actual weighted-bar cylinder. The
zeroth face uses the first chain arrow; the other faces retain their canonical transports. -/
theorem barCylinder_δ (n : ℕ) (i : Fin (n + 2)) :
    (StrictOrdinaryWeightedBar.wbarδ (CategoryBar.replUnit J) D n i ▷
        (Δ[1] : SSet.{max w v})) ≫ H.barCylinder n =
      H.barCylinder (n + 1) ≫
        StrictOrdinaryWeightedBar.wbarδ (CategoryBar.replUnit J) E n i := by
  by_cases hi0 : i = 0
  · subst i
    rw [StrictOrdinaryWeightedBar.wbarδ_zero, StrictOrdinaryWeightedBar.wbarδ_zero]
    apply H.barCylinder_naturality_of_components
      (StrictOrdinaryWeightedBar.wFaceZeroIdx (CategoryBar.replUnit J) n)
      (fun s => s.1.map' 0 1)
    · intro s
      simpa only [SrepBridge.srepFaceZeroComponent, SrepBridge.srepLeftZero,
        SrepBridge.srepDropFirst_left, eqToHom_refl, Category.id_comp, Category.comp_id] using
        StrictOrdinaryWeightedBar.wbarFaceZero_ι (CategoryBar.replUnit J) D n s
    · intro s
      simpa only [SrepBridge.srepFaceZeroComponent, SrepBridge.srepLeftZero,
        SrepBridge.srepDropFirst_left, eqToHom_refl, Category.id_comp, Category.comp_id] using
        StrictOrdinaryWeightedBar.wbarFaceZero_ι (CategoryBar.replUnit J) E n s
  · by_cases hiLast : i = Fin.last (n + 1)
    · subst i
      rw [StrictOrdinaryWeightedBar.wbarδ_last, StrictOrdinaryWeightedBar.wbarδ_last]
      apply H.barCylinder_naturality_of_components
        (StrictOrdinaryWeightedBar.wFaceLastIdx (CategoryBar.replUnit J) n)
        (fun s => 𝟙 s.1.left)
      · intro s
        rw [D.map_id]
        simpa only [SrepBridge.srepFaceLastComponent, SrepBridge.srepDropLast_left,
          eqToHom_refl] using
          StrictOrdinaryWeightedBar.wbarFaceLast_ι (CategoryBar.replUnit J) D n s
      · intro s
        rw [E.map_id]
        simpa only [SrepBridge.srepFaceLastComponent, SrepBridge.srepDropLast_left,
          eqToHom_refl] using
          StrictOrdinaryWeightedBar.wbarFaceLast_ι (CategoryBar.replUnit J) E n s
    · let _ : NeZero (n + 1) := ⟨by omega⟩
      rw [StrictOrdinaryWeightedBar.wbarδ_inner _ _ _ i hi0 hiLast,
        StrictOrdinaryWeightedBar.wbarδ_inner _ _ _ i hi0 hiLast]
      apply H.barCylinder_naturality_of_components
        (StrictOrdinaryWeightedBar.wFaceInnerIdx (CategoryBar.replUnit J) n i hiLast)
        (fun s => eqToHom (StrictOrdinaryWeightedBar.wOmitInner_obj_zero hi0 s.1).symm)
      · intro s
        simpa only [StrictOrdinaryWeightedBar.wFaceInnerComponent, eqToHom_map] using
          StrictOrdinaryWeightedBar.wbarFaceInner_ι (CategoryBar.replUnit J) D n i hi0 hiLast s
      · intro s
        simpa only [StrictOrdinaryWeightedBar.wFaceInnerComponent, eqToHom_map] using
          StrictOrdinaryWeightedBar.wbarFaceInner_ι (CategoryBar.replUnit J) E n i hi0 hiLast s

/-- Every outer degeneracy commutes with the cylinder and retains the
weighted index map and left-endpoint equality transport. -/
theorem barCylinder_σ (n : ℕ) (i : Fin (n + 1)) :
    (StrictOrdinaryWeightedBar.wbarσ (CategoryBar.replUnit J) D n i ▷
        (Δ[1] : SSet.{max w v})) ≫ H.barCylinder (n + 1) =
      H.barCylinder n ≫ StrictOrdinaryWeightedBar.wbarσ (CategoryBar.replUnit J) E n i := by
  let _ : NeZero (n + 1) := ⟨by omega⟩
  apply H.barCylinder_naturality_of_components
    (StrictOrdinaryWeightedBar.wDegInnerIdx (CategoryBar.replUnit J) n i)
    (fun s => eqToHom (StrictOrdinaryWeightedBar.wDupInner_obj_zero s.1).symm)
  · intro s
    simpa only [StrictOrdinaryWeightedBar.wDegInnerComponent, eqToHom_map] using
      StrictOrdinaryWeightedBar.wbarσ_ι (CategoryBar.replUnit J) D n i s
  · intro s
    simpa only [StrictOrdinaryWeightedBar.wDegInnerComponent, eqToHom_map] using
      StrictOrdinaryWeightedBar.wbarσ_ι (CategoryBar.replUnit J) E n i s

private def barCylinderApp (a : SimplexCategoryᵒᵖ) :
    (bkBarBisimplicial D).obj a ⊗ (Δ[1] : SSet.{max w v}) ⟶ (bkBarBisimplicial E).obj a := by
  induction a using Opposite.rec with
  | _ a =>
    induction a using SimplexCategory.rec with
    | _ n => exact H.barCylinder n

private abbrev barCylinderNaturality : MorphismProperty SimplexCategory :=
  (MorphismProperty.naturalityProperty
    (F₁ := bkBarBisimplicial D ⋙ tensorRight (Δ[1] : SSet.{max w v}))
    (F₂ := bkBarBisimplicial E) (barCylinderApp H)).unop

private theorem barCylinderNaturality_eq_top : H.barCylinderNaturality = ⊤ := by
  apply SimplexCategory.morphismProperty_eq_top
  · intro n i
    change ((bkBarBisimplicial D).map (SimplexCategory.δ i).op ▷
        (Δ[1] : SSet.{max w v})) ≫ H.barCylinder n =
      H.barCylinder (n + 1) ≫ (bkBarBisimplicial E).map (SimplexCategory.δ i).op
    simpa only [bkBarBisimplicial, bkBarBisimplicialFunctor,
      StrictOrdinaryWeightedBar.wbarSimplicial_map_δ] using H.barCylinder_δ n i
  · intro n i
    change ((bkBarBisimplicial D).map (SimplexCategory.σ i).op ▷
        (Δ[1] : SSet.{max w v})) ≫ H.barCylinder (n + 1) =
      H.barCylinder n ≫ (bkBarBisimplicial E).map (SimplexCategory.σ i).op
    simpa only [bkBarBisimplicial, bkBarBisimplicialFunctor,
      StrictOrdinaryWeightedBar.wbarSimplicial_map_σ] using H.barCylinder_σ n i

/-- The actual bar cylinders commute with all outer simplex operators. -/
def barCylinderMap : bkBarBisimplicial D ⋙ tensorRight (Δ[1] : SSet.{max w v}) ⟶
    bkBarBisimplicial E where
  app a := by
    induction a using Opposite.rec with
    | _ a =>
      induction a using SimplexCategory.rec with
      | _ n => exact H.barCylinder n
  naturality _ _ f := by
    exact (barCylinderNaturality_eq_top H).symm.le f.unop (by simp)

/-- The outer natural cylinder uses the specified row cylinder in each degree. -/
@[simp]
theorem barCylinderMap_app (p : ℕ) :
    H.barCylinderMap.app (op ⦋p⦌) = H.barCylinder p := rfl

private theorem prism_naturality {X Y X' Y' : SSet.{w}}
    {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}
    (K : SSet.Homotopy f g) (L : SSet.Homotopy f' g')
    (a : X ⟶ X') (b : Y ⟶ Y')
    (h : (a ▷ (Δ[1] : SSet.{w})) ≫ L.h = K.h ≫ b)
    {q : ℕ} (i : Fin (q + 1)) :
    a.app (op ⦋q⦌) ≫ L.toSimplicialObjectHomotopy.h i =
      K.toSimplicialObjectHomotopy.h i ≫ b.app (op ⦋q + 1⦌) := by
  ext x
  change L.h.app (op ⦋q + 1⦌)
      (X'.σ i (a.app (op ⦋q⦌) x), stdSimplex.objMk₁ i.succ.castSucc) =
    b.app (op ⦋q + 1⦌) (K.h.app (op ⦋q + 1⦌)
      (X.σ i x, stdSimplex.objMk₁ i.succ.castSucc))
  have hh := congrArg (fun m => m.app (op ⦋q + 1⦌)
    (X.σ i x, stdSimplex.objMk₁ i.succ.castSucc)) h
  change L.h.app (op ⦋q + 1⦌)
      (a.app (op ⦋q + 1⦌) (X.σ i x), stdSimplex.objMk₁ i.succ.castSucc) =
    b.app (op ⦋q + 1⦌) (K.h.app (op ⦋q + 1⦌)
      (X.σ i x, stdSimplex.objMk₁ i.succ.castSucc)) at hh
  have ha := ConcreteCategory.congr_hom (a.naturality (SimplexCategory.σ i).op) x
  change a.app (op ⦋q + 1⦌) (X.σ i x) = X'.σ i (a.app (op ⦋q⦌) x) at ha
  rw [← ha]
  exact hh

/-- The combinatorial inner prism retains the weighted outer chain on each
coefficient summand. -/
theorem barPrism_ι (p q : ℕ)
    (s : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) p)
    (i : Fin (q + 1)) :
    (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D p s).app (op ⦋q⦌) ≫
        (H.barHomotopy p).toSimplicialObjectHomotopy.h i =
      (H.app s.1.left).toSimplicialObjectHomotopy.h i ≫
        (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) E p s).app
          (op ⦋q + 1⦌) :=
  prism_naturality (H.app s.1.left) (H.barHomotopy p) _ _ (H.barCylinder_ι p s) i

/-- Inner prism components commute with every outer simplex operator. -/
theorem barPrism_naturality {p p' : ℕ} (φ : ⦋p⦌ ⟶ ⦋p'⦌)
    (q : ℕ) (i : Fin (q + 1)) :
    ((bkBarBisimplicial D).map φ.op).app (op ⦋q⦌) ≫
        (H.barHomotopy p).toSimplicialObjectHomotopy.h i =
      (H.barHomotopy p').toSimplicialObjectHomotopy.h i ≫
        ((bkBarBisimplicial E).map φ.op).app (op ⦋q + 1⦌) := by
  apply prism_naturality (H.barHomotopy p') (H.barHomotopy p) _ _ _ i
  exact H.barCylinderMap.naturality φ.op

section Coefficients

variable (A : Type uA) [Category.{vA} A] [HasCoproducts.{max w v} A] [Preadditive A]
  (R : A)

/-- The actual vertical chain homotopy on each BK column. -/
def verticalHomotopy (p : ℕ) :
    _root_.Homotopy
      (((bkAlternatingBicomplexFunctor A R).map α).f p)
      (((bkAlternatingBicomplexFunctor A R).map β).f p) :=
  (H.barHomotopy p).chainComplexMap R

/-- The vertical homotopy is the minus alternating sum of the actual inner
prism, with the library's prescribed endpoint orientation. -/
theorem verticalHomotopy_hom (p q : ℕ) :
    (H.verticalHomotopy A R p).hom q (q + 1) =
      -∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) •
        ((sigmaConst : A ⥤ (Type (max w v) ⥤ A)).obj R).map
          ((H.barHomotopy p).toSimplicialObjectHomotopy.h i) := by
  change SimplicialObject.Homotopy.ToChainHomotopy.hom _ q (q + 1) = _
  rw [SimplicialObject.Homotopy.ToChainHomotopy.hom_eq]
  rfl

/-- The actual vertical chain homotopy is natural for every outer simplex operator. -/
theorem verticalHomotopy_naturality {p p' : ℕ} (φ : ⦋p⦌ ⟶ ⦋p'⦌) (q q' : ℕ) :
    (chainComplexMap ((bkBarBisimplicial D).map φ.op) R).f q ≫
        (H.verticalHomotopy A R p).hom q q' =
      (H.verticalHomotopy A R p').hom q q' ≫
        (chainComplexMap ((bkBarBisimplicial E).map φ.op) R).f q' := by
  by_cases hq : q + 1 = q'
  · subst q'
    rw [verticalHomotopy_hom, verticalHomotopy_hom]
    change ((sigmaConst : A ⥤ (Type (max w v) ⥤ A)).obj R).map
        (((bkBarBisimplicial D).map φ.op).app (op ⦋q⦌)) ≫ _ =
      _ ≫ ((sigmaConst : A ⥤ (Type (max w v) ⥤ A)).obj R).map
        (((bkBarBisimplicial E).map φ.op).app (op ⦋q + 1⦌))
    simp only [Preadditive.comp_neg, Preadditive.neg_comp, Preadditive.comp_sum,
      Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    rw [← Functor.map_comp, ← Functor.map_comp, H.barPrism_naturality φ q i]
  · rw [(H.verticalHomotopy A R p).zero q q' hq,
      (H.verticalHomotopy A R p').zero q q' hq]
    simp

private theorem horizontal_d_eq_sum (F : J ⥤ SSet.{max w v}) (p q : ℕ) :
    ((bkAlternatingBicomplex A R F).d (p + 1) p).f q =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        (chainComplexMap ((bkBarBisimplicial F).δ i) R).f q := by
  change ((AlgebraicTopology.bisimplicialAlternatingBicomplex A
    ((bisimplicialLinearizationFunctor A R).obj (bkBarBisimplicial F))).d (p + 1) p).f q = _
  rw [AlgebraicTopology.bisimplicialAlternatingBicomplex_horizontal_d_f_eq_sum]
  rfl

/-- The row homotopies form a genuine vertical homotopy of the actual BK
bicomplex maps; their components are horizontal chain maps. -/
def bicomplexHomotopy :
    _root_.Homotopy
      (HomologicalComplex₂.flipMap ((bkAlternatingBicomplexFunctor A R).map α))
      (HomologicalComplex₂.flipMap ((bkAlternatingBicomplexFunctor A R).map β)) where
  hom q q' :=
    { f := fun p => (H.verticalHomotopy A R p).hom q q'
      comm' := by
        intro p p' hp
        obtain rfl : p = p' + 1 := hp.symm
        change (H.verticalHomotopy A R (p' + 1)).hom q q' ≫
            ((bkAlternatingBicomplex A R E).d (p' + 1) p').f q' =
          ((bkAlternatingBicomplex A R D).d (p' + 1) p').f q ≫
            (H.verticalHomotopy A R p').hom q q'
        rw [horizontal_d_eq_sum A R E, horizontal_d_eq_sum A R D]
        simp only [Preadditive.comp_sum, Preadditive.sum_comp,
          Preadditive.comp_zsmul, Preadditive.zsmul_comp]
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg (fun f => (-1 : ℤ) ^ (i : ℕ) • f)
          (H.verticalHomotopy_naturality A R (SimplexCategory.δ i) q q').symm }
  zero q q' hq := by
    ext p
    exact (H.verticalHomotopy A R p).zero q q' hq
  comm q := by
    ext p
    change (((bkAlternatingBicomplexFunctor A R).map α).f p).f q =
      dNext q (H.verticalHomotopy A R p).hom +
        prevD q (H.verticalHomotopy A R p).hom +
        (((bkAlternatingBicomplexFunctor A R).map β).f p).f q
    exact (H.verticalHomotopy A R p).comm q

/-- The vertical homotopy has exactly the row-prism components. -/
@[simp]
theorem bicomplexHomotopy_hom_f (q q' p : ℕ) :
    ((H.bicomplexHomotopy A R).hom q q').f p =
      (H.verticalHomotopy A R p).hom q q' := rfl

end Coefficients

end DiagramHomotopy

end SSet
