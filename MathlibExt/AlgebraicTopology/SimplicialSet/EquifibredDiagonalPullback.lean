/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialDiagonal
public import MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialDiagonalWeakEquivalence
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Row-to-diagonal pullback comparisons

Constant simplex operators define maps from each row of a bisimplicial set to its diagonal, indexed by a chosen vertex. The associated pullback comparisons retain their projection and naturality equations and are realization weak equivalences when every operator-relative row comparison is a realization weak equivalence.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet.EquifibredDiagonal

/-- Original precomposition of a constant ordinal operator. -/
theorem constant_precomp {a b n : SimplexCategory} (f : a ⟶ b)
    (v : Fin (n.len + 1)) :
    f ≫ SimplexCategory.const b n v = SimplexCategory.const a n v := by
  ext i
  rfl

/-- Original site postcomposition moves the specified target vertex. -/
theorem constant_postcomp {a n m : SimplexCategory} (f : n ⟶ m)
    (v : Fin (n.len + 1)) :
    SimplexCategory.const a n v ≫ f = SimplexCategory.const a m (f v) := by
  ext i
  rfl

/-- The actual constant-row map uses opposite original operators [e]→[n]. -/
def vertexConstantDiagramMap (X : SimplicialObject SSet.{u})
    (n : SimplexCategory) (v : Fin (n.len + 1)) :
    (SimplicialObject.const SSet.{u}).obj (X.obj (op n)) ⟶ X where
  app e := X.map (SimplexCategory.const e.unop n v).op
  naturality a b f := by
    change 𝟙 _ ≫ X.map (SimplexCategory.const b.unop n v).op =
      X.map (SimplexCategory.const a.unop n v).op ≫ X.map f
    rw [Category.id_comp, ← X.map_comp]
    change X.map (SimplexCategory.const b.unop n v).op =
      X.map (f.unop ≫ SimplexCategory.const a.unop n v).op
    rw [constant_precomp]

/-- The constant-row maps respect the same original natural transformation. -/
theorem vertexConstantDiagramMap_naturality
    {X Y : SimplicialObject SSet.{u}} (p : X ⟶ Y)
    (n : SimplexCategory) (v : Fin (n.len + 1)) :
    vertexConstantDiagramMap X n v ≫ p =
      (SimplicialObject.const SSet.{u}).map (p.app (op n)) ≫
        vertexConstantDiagramMap Y n v := by
  apply NatTrans.ext
  funext e
  simpa only [vertexConstantDiagramMap, NatTrans.comp_app, Functor.const_map_app,
    op_unop] using p.naturality (SimplexCategory.const e.unop n v).op

/-- The original constant-row map moves the chosen vertex under every site map. -/
theorem vertexConstantDiagramMap_site (X : SimplicialObject SSet.{u})
    {n m : SimplexCategory} (f : n ⟶ m) (v : Fin (n.len + 1)) :
    (SimplicialObject.const SSet.{u}).map (X.map f.op) ≫
        vertexConstantDiagramMap X n v = vertexConstantDiagramMap X m (f v) := by
  apply NatTrans.ext
  funext e
  simp only [vertexConstantDiagramMap, NatTrans.comp_app, Functor.const_map_app]
  rw [← X.map_comp, ← op_comp, constant_postcomp]

/-- The actual row-to-diagonal map uses the inverse constant-diagonal Iso. -/
def rowVertexToDiagonal (X : SimplicialObject SSet.{u})
    (n : SimplexCategory) (v : Fin (n.len + 1)) :
    X.obj (op n) ⟶ SSet.simplicialDiagonalFunctor.obj X :=
  (SSet.diagonalConstIso (X.obj (op n))).inv ≫
    SSet.simplicialDiagonalFunctor.map (vertexConstantDiagramMap X n v)

/-- Every original scalar degree retains that same constant ordinal operator. -/
theorem rowVertexToDiagonal_app (X : SimplicialObject SSet.{u})
    (n : SimplexCategory) (v : Fin (n.len + 1)) (e : SimplexCategoryᵒᵖ) :
    (rowVertexToDiagonal X n v).app e =
      (X.map (SimplexCategory.const e.unop n v).op).app e := by
  simp only [rowVertexToDiagonal, NatTrans.comp_app,
    SSet.simplicialDiagonalFunctor_map_app, SSet.diagonalConstIso,
    CategoryTheory.SimplicialObject.diagonalConstIso_inv_app, vertexConstantDiagramMap,
    ]
  exact Category.id_comp _

/-- Original inner operators commute with the actual row map. -/
theorem rowVertexToDiagonal_operator (X : SimplicialObject SSet.{u})
    (n : SimplexCategory) (v : Fin (n.len + 1))
    {a b : SimplexCategoryᵒᵖ} (f : a ⟶ b) :
    (X.obj (op n)).map f ≫ (rowVertexToDiagonal X n v).app b =
      (rowVertexToDiagonal X n v).app a ≫
        (SSet.simplicialDiagonalFunctor.obj X).map f :=
  (rowVertexToDiagonal X n v).naturality f

/-- The whole diagonal square belongs to the same original p. -/
theorem rowVertexToDiagonal_naturality
    {X Y : SimplicialObject SSet.{u}} (p : X ⟶ Y)
    (n : SimplexCategory) (v : Fin (n.len + 1)) :
    rowVertexToDiagonal X n v ≫ SSet.simplicialDiagonalFunctor.map p =
      p.app (op n) ≫ rowVertexToDiagonal Y n v := by
  apply NatTrans.ext
  funext e
  simp only [NatTrans.comp_app, rowVertexToDiagonal_app,
    SSet.simplicialDiagonalFunctor_map_app]
  exact congrArg (fun f => f.app e)
    (p.naturality (SimplexCategory.const e.unop n v).op)

/-- Site naturality transports the vertex, including zero-moving operators. -/
theorem rowVertexToDiagonal_site (X : SimplicialObject SSet.{u})
    {n m : SimplexCategory} (f : n ⟶ m) (v : Fin (n.len + 1)) :
    X.map f.op ≫ rowVertexToDiagonal X n v = rowVertexToDiagonal X m (f v) := by
  apply NatTrans.ext
  funext e
  simp only [NatTrans.comp_app, rowVertexToDiagonal_app]
  have h : X.map f.op ≫ X.map (SimplexCategory.const e.unop n v).op =
      X.map (SimplexCategory.const e.unop m (f v)).op := by
    rw [← X.map_comp, ← op_comp, constant_postcomp]
  exact congrArg (fun a => a.app e) h

/-- The original operator-relative comparison is a literal pullback lift. -/
def relativeComparison {X Y : SimplicialObject SSet.{u}} (p : X ⟶ Y)
    {n m : SimplexCategory} (f : n ⟶ m) :
    X.obj (op m) ⟶ pullback (p.app (op n)) (Y.map f.op) :=
  pullback.lift (X.map f.op) (p.app (op m)) (p.naturality f.op)

/-- Construct the actual simplicial pullback before taking its diagonal. -/
@[reducible] def vertexPullbackDiagram {X Y : SimplicialObject SSet.{u}} (p : X ⟶ Y)
    (n : SimplexCategory) (v : Fin (n.len + 1)) : SimplicialObject SSet.{u} :=
  pullback p (vertexConstantDiagramMap Y n v)

/-- Its comparison uses the original constant-row maps and nth component of p. -/
def vertexComparisonDiagram {X Y : SimplicialObject SSet.{u}} (p : X ⟶ Y)
    (n : SimplexCategory) (v : Fin (n.len + 1)) :
    (SimplicialObject.const SSet.{u}).obj (X.obj (op n)) ⟶ vertexPullbackDiagram p n v :=
  pullback.lift (vertexConstantDiagramMap X n v)
    ((SimplicialObject.const SSet.{u}).map (p.app (op n)))
    (vertexConstantDiagramMap_naturality p n v)

/-- Both original simplicial projection equations hold. -/
theorem vertexComparisonDiagram_legs {X Y : SimplicialObject SSet.{u}} (p : X ⟶ Y)
    (n : SimplexCategory) (v : Fin (n.len + 1)) :
    vertexComparisonDiagram p n v ≫ pullback.fst p (vertexConstantDiagramMap Y n v) =
      vertexConstantDiagramMap X n v ∧
    vertexComparisonDiagram p n v ≫ pullback.snd p (vertexConstantDiagramMap Y n v) =
      (SimplicialObject.const SSet.{u}).map (p.app (op n)) :=
  ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

/-- Evaluation gives the actual original scalar pullback Iso. -/
def vertexPullbackEvalIso {X Y : SimplicialObject SSet.{u}} (p : X ⟶ Y)
    (n : SimplexCategory) (v : Fin (n.len + 1)) (e : SimplexCategoryᵒᵖ) :
    (vertexPullbackDiagram p n v).obj e ≅
      pullback (p.app e) (Y.map (SimplexCategory.const e.unop n v).op) :=
  ((IsPullback.of_hasPullback p (vertexConstantDiagramMap Y n v)).map
    ((evaluation SimplexCategoryᵒᵖ SSet.{u}).obj e)).isoPullback

/-- The evaluated comparison is the same operator-relative comparison. -/
theorem vertexComparisonEval_factor
    {X Y : SimplicialObject SSet.{u}} (p : X ⟶ Y)
    (n : SimplexCategory) (v : Fin (n.len + 1)) (e : SimplexCategoryᵒᵖ) :
    (vertexComparisonDiagram p n v).app e ≫ (vertexPullbackEvalIso p n v e).hom =
      relativeComparison p (SimplexCategory.const e.unop n v) := by
  cases e with
  | op e =>
    dsimp only [vertexPullbackDiagram, relativeComparison]
    have hf : (vertexPullbackEvalIso p n v (op e)).hom ≫ pullback.fst _ _ =
        (pullback.fst p (vertexConstantDiagramMap Y n v)).app (op e) :=
      ((IsPullback.of_hasPullback p (vertexConstantDiagramMap Y n v)).map
        ((evaluation SimplexCategoryᵒᵖ SSet.{u}).obj (op e))).isoPullback_hom_fst
    have hs : (vertexPullbackEvalIso p n v (op e)).hom ≫ pullback.snd _ _ =
        (pullback.snd p (vertexConstantDiagramMap Y n v)).app (op e) :=
      ((IsPullback.of_hasPullback p (vertexConstantDiagramMap Y n v)).map
        ((evaluation SimplexCategoryᵒᵖ SSet.{u}).obj (op e))).isoPullback_hom_snd
    apply pullback.hom_ext
    · rw [Category.assoc, hf]
      exact (congrArg (fun f => f.app (op e)) (vertexComparisonDiagram_legs p n v).1).trans
        (pullback.lift_fst (X.map (SimplexCategory.const e n v).op)
          (p.app (op n)) (p.naturality (SimplexCategory.const e n v).op)).symm
    · rw [Category.assoc, hs]
      exact (congrArg (fun f => f.app (op e)) (vertexComparisonDiagram_legs p n v).2).trans
        (pullback.lift_snd (X.map (SimplexCategory.const e n v).op)
          (p.app (op n)) (p.naturality (SimplexCategory.const e n v).op)).symm

/-- Both endpoints of the evaluated whole Arrow comparison are retained. -/
def vertexComparisonEvalArrowIso
    {X Y : SimplicialObject SSet.{u}} (p : X ⟶ Y)
    (n : SimplexCategory) (v : Fin (n.len + 1)) (e : SimplexCategoryᵒᵖ) :
    Arrow.mk ((vertexComparisonDiagram p n v).app e) ≅
      Arrow.mk (relativeComparison p (SimplexCategory.const e.unop n v)) :=
  Arrow.isoMk' _ _ (Iso.refl _) (vertexPullbackEvalIso p n v e)
    (by
      cases e
      simpa only [Iso.refl_hom, Category.id_comp] using
        (vertexComparisonEval_factor p n v _).symm)

/-- Diagonal preservation and the original constant Iso give a constructed pullback square. -/
theorem vertexPullbackDiagonal_isPullback
    {X Y : SimplicialObject SSet.{u}} (p : X ⟶ Y)
    (n : SimplexCategory) (v : Fin (n.len + 1)) :
    IsPullback
      (SSet.simplicialDiagonalFunctor.map (pullback.fst p (vertexConstantDiagramMap Y n v)))
      (SSet.simplicialDiagonalFunctor.map (pullback.snd p (vertexConstantDiagramMap Y n v)) ≫
        (SSet.diagonalConstIso (Y.obj (op n))).hom)
      (SSet.simplicialDiagonalFunctor.map p) (rowVertexToDiagonal Y n v) := by
  have h := (IsPullback.of_hasPullback p (vertexConstantDiagramMap Y n v)).map
    SSet.simplicialDiagonalFunctor
  apply h.of_iso (Iso.refl _) (Iso.refl _)
    (SSet.diagonalConstIso (Y.obj (op n))) (Iso.refl _)
  · simp
  · simp
  · simp
  · simp [rowVertexToDiagonal]

/-- The actual preserved-diagonal pullback Iso is constructed internally. -/
@[reducible] def vertexPullbackDiagonalIso
    {X Y : SimplicialObject SSet.{u}} (p : X ⟶ Y)
    (n : SimplexCategory) (v : Fin (n.len + 1)) :
    SSet.simplicialDiagonalFunctor.obj (vertexPullbackDiagram p n v) ≅
      pullback (SSet.simplicialDiagonalFunctor.map p) (rowVertexToDiagonal Y n v) :=
  (vertexPullbackDiagonal_isPullback p n v).isoPullback

/-- Both forward and both inverse projection equations use the original const Iso. -/
theorem vertexPullbackDiagonalIso_legs
    {X Y : SimplicialObject SSet.{u}} (p : X ⟶ Y)
    (n : SimplexCategory) (v : Fin (n.len + 1)) :
    (vertexPullbackDiagonalIso p n v).hom ≫ pullback.fst _ _ =
      SSet.simplicialDiagonalFunctor.map (pullback.fst p (vertexConstantDiagramMap Y n v)) ∧
    (vertexPullbackDiagonalIso p n v).hom ≫ pullback.snd _ _ =
      SSet.simplicialDiagonalFunctor.map (pullback.snd p (vertexConstantDiagramMap Y n v)) ≫
        (SSet.diagonalConstIso (Y.obj (op n))).hom ∧
    (vertexPullbackDiagonalIso p n v).inv ≫
        SSet.simplicialDiagonalFunctor.map (pullback.fst p (vertexConstantDiagramMap Y n v)) =
      pullback.fst _ _ ∧
    (vertexPullbackDiagonalIso p n v).inv ≫
        SSet.simplicialDiagonalFunctor.map (pullback.snd p (vertexConstantDiagramMap Y n v)) =
      pullback.snd _ _ ≫ (SSet.diagonalConstIso (Y.obj (op n))).inv := by
  refine ⟨(vertexPullbackDiagonal_isPullback p n v).isoPullback_hom_fst,
    (vertexPullbackDiagonal_isPullback p n v).isoPullback_hom_snd,
    (vertexPullbackDiagonal_isPullback p n v).isoPullback_inv_fst, ?_⟩
  apply (cancel_mono (SSet.diagonalConstIso (Y.obj (op n))).hom).1
  simpa only [vertexPullbackDiagonalIso, Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    (vertexPullbackDiagonal_isPullback p n v).isoPullback_inv_snd

/-- The actual ordinary diagonal pullback comparison. -/
@[reducible] def vertexDiagonalPullbackComparison
    {X Y : SimplicialObject SSet.{u}} (p : X ⟶ Y)
    (n : SimplexCategory) (v : Fin (n.len + 1)) :
    X.obj (op n) ⟶
      pullback (SSet.simplicialDiagonalFunctor.map p) (rowVertexToDiagonal Y n v) :=
  pullback.lift (rowVertexToDiagonal X n v) (p.app (op n))
    (rowVertexToDiagonal_naturality p n v)

/-- Both original ordinary-pullback projection equations. -/
theorem vertexDiagonalPullbackComparison_legs
    {X Y : SimplicialObject SSet.{u}} (p : X ⟶ Y)
    (n : SimplexCategory) (v : Fin (n.len + 1)) :
    vertexDiagonalPullbackComparison p n v ≫ pullback.fst _ _ = rowVertexToDiagonal X n v ∧
    vertexDiagonalPullbackComparison p n v ≫ pullback.snd _ _ = p.app (op n) :=
  ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

/-- The exact diagonal comparison factorization uses both original endpoints. -/
theorem vertexComparisonDiagonal_factor
    {X Y : SimplicialObject SSet.{u}} (p : X ⟶ Y)
    (n : SimplexCategory) (v : Fin (n.len + 1)) :
    SSet.simplicialDiagonalFunctor.map (vertexComparisonDiagram p n v) ≫
        (vertexPullbackDiagonalIso p n v).hom =
      (SSet.diagonalConstIso (X.obj (op n))).hom ≫ vertexDiagonalPullbackComparison p n v := by
  apply pullback.hom_ext
  · calc
      (SSet.simplicialDiagonalFunctor.map (vertexComparisonDiagram p n v) ≫
          (vertexPullbackDiagonalIso p n v).hom) ≫ pullback.fst _ _ =
        SSet.simplicialDiagonalFunctor.map (vertexComparisonDiagram p n v) ≫
          SSet.simplicialDiagonalFunctor.map
            (pullback.fst p (vertexConstantDiagramMap Y n v)) := by
        rw [Category.assoc, (vertexPullbackDiagonalIso_legs p n v).1]
      _ = SSet.simplicialDiagonalFunctor.map (vertexComparisonDiagram p n v ≫
          pullback.fst p (vertexConstantDiagramMap Y n v)) :=
        (SSet.simplicialDiagonalFunctor.map_comp _ _).symm
      _ = SSet.simplicialDiagonalFunctor.map (vertexConstantDiagramMap X n v) := by
        rw [(vertexComparisonDiagram_legs p n v).1]
      _ = ((SSet.diagonalConstIso (X.obj (op n))).hom ≫
          vertexDiagonalPullbackComparison p n v) ≫ pullback.fst _ _ := by
        rw [Category.assoc, (vertexDiagonalPullbackComparison_legs p n v).1]
        simp only [rowVertexToDiagonal, Iso.hom_inv_id_assoc]
  · calc
      (SSet.simplicialDiagonalFunctor.map (vertexComparisonDiagram p n v) ≫
          (vertexPullbackDiagonalIso p n v).hom) ≫ pullback.snd _ _ =
        SSet.simplicialDiagonalFunctor.map (vertexComparisonDiagram p n v) ≫
          SSet.simplicialDiagonalFunctor.map
            (pullback.snd p (vertexConstantDiagramMap Y n v)) ≫
              (SSet.diagonalConstIso (Y.obj (op n))).hom := by
        rw [Category.assoc, (vertexPullbackDiagonalIso_legs p n v).2.1]
      _ = SSet.simplicialDiagonalFunctor.map (vertexComparisonDiagram p n v ≫
          pullback.snd p (vertexConstantDiagramMap Y n v)) ≫
            (SSet.diagonalConstIso (Y.obj (op n))).hom := by
        exact congrArg (fun h => h ≫ (SSet.diagonalConstIso (Y.obj (op n))).hom)
          (SSet.simplicialDiagonalFunctor.map_comp (vertexComparisonDiagram p n v)
            (pullback.snd p (vertexConstantDiagramMap Y n v))).symm
      _ = SSet.simplicialDiagonalFunctor.map
          ((SimplicialObject.const SSet.{u}).map (p.app (op n))) ≫
            (SSet.diagonalConstIso (Y.obj (op n))).hom := by
        rw [(vertexComparisonDiagram_legs p n v).2]
      _ = (SSet.diagonalConstIso (X.obj (op n))).hom ≫ p.app (op n) :=
        CategoryTheory.SimplicialObject.diagonalConstIso_naturality
          (Type u) (p.app (op n))
      _ = ((SSet.diagonalConstIso (X.obj (op n))).hom ≫
          vertexDiagonalPullbackComparison p n v) ≫ pullback.snd _ _ := by
        rw [Category.assoc, (vertexDiagonalPullbackComparison_legs p n v).2]

/-- The whole Arrow Iso from diagonal psi to the same ordinary kappa. -/
def vertexComparisonDiagonalArrowIso
    {X Y : SimplicialObject SSet.{u}} (p : X ⟶ Y)
    (n : SimplexCategory) (v : Fin (n.len + 1)) :
    Arrow.mk (SSet.simplicialDiagonalFunctor.map (vertexComparisonDiagram p n v)) ≅
      Arrow.mk (vertexDiagonalPullbackComparison p n v) :=
  Arrow.isoMk' _ _ (SSet.diagonalConstIso (X.obj (op n)))
    (vertexPullbackDiagonalIso p n v) (vertexComparisonDiagonal_factor p n v).symm

/-- All four whole Arrow components are the actual d_X/e_P hom and inverse maps. -/
theorem vertexComparisonDiagonalArrowIso_components
    {X Y : SimplicialObject SSet.{u}} (p : X ⟶ Y)
    (n : SimplexCategory) (v : Fin (n.len + 1)) :
    (vertexComparisonDiagonalArrowIso p n v).hom.left = (SSet.diagonalConstIso (X.obj (op n))).hom ∧
    (vertexComparisonDiagonalArrowIso p n v).hom.right = (vertexPullbackDiagonalIso p n v).hom ∧
    (vertexComparisonDiagonalArrowIso p n v).inv.left = (SSet.diagonalConstIso (X.obj (op n))).inv ∧
    (vertexComparisonDiagonalArrowIso p n v).inv.right = (vertexPullbackDiagonalIso p n v).inv :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Both exact whole Arrow equations, including inverse transport. -/
theorem vertexComparisonDiagonalArrowIso_squares
    {X Y : SimplicialObject SSet.{u}} (p : X ⟶ Y)
    (n : SimplexCategory) (v : Fin (n.len + 1)) :
    (SSet.diagonalConstIso (X.obj (op n))).hom ≫ vertexDiagonalPullbackComparison p n v =
      SSet.simplicialDiagonalFunctor.map (vertexComparisonDiagram p n v) ≫
        (vertexPullbackDiagonalIso p n v).hom ∧
    (SSet.diagonalConstIso (X.obj (op n))).inv ≫
        SSet.simplicialDiagonalFunctor.map (vertexComparisonDiagram p n v) =
      vertexDiagonalPullbackComparison p n v ≫ (vertexPullbackDiagonalIso p n v).inv :=
  ⟨(vertexComparisonDiagonalArrowIso p n v).hom.w,
    (vertexComparisonDiagonalArrowIso p n v).inv.w⟩

/-- All original relative-comparison weakness implies the strict ordinary diagonal comparison. -/
theorem realizationWeak_vertexDiagonalPullbackComparison
    {X Y : SimplicialObject SSet.{u}} (p : X ⟶ Y)
    (h : ∀ {n m : SimplexCategory} (f : n ⟶ m),
      SSet.realizationWeakEquivalences (relativeComparison p f))
    (n : SimplexCategory) (v : Fin (n.len + 1)) :
    SSet.realizationWeakEquivalences (vertexDiagonalPullbackComparison p n v) := by
  have hpsi (e : ℕ) : SSet.realizationWeakEquivalences
      ((vertexComparisonDiagram p n v).app (op ⦋e⦌)) :=
    (SSet.realizationWeakEquivalences.arrow_mk_iso_iff
      (vertexComparisonEvalArrowIso p n v (op ⦋e⦌))).mpr
      (h (SimplexCategory.const ⦋e⦌ n v))
  have hd := SSet.simplicialDiagonal_map_mem_realizationWeakEquivalences
    (vertexComparisonDiagram p n v) hpsi
  exact (SSet.realizationWeakEquivalences.arrow_mk_iso_iff
    (vertexComparisonDiagonalArrowIso p n v)).mp hd

/-- The original vertex-site map between the two ordinary target pullbacks. -/
def vertexSitePullbackMap
    {X Y : SimplicialObject SSet.{u}} (p : X ⟶ Y)
    {n m : SimplexCategory} (f : n ⟶ m) (v : Fin (n.len + 1)) :
    pullback (SSet.simplicialDiagonalFunctor.map p) (rowVertexToDiagonal Y m (f v)) ⟶
      pullback (SSet.simplicialDiagonalFunctor.map p) (rowVertexToDiagonal Y n v) :=
  pullback.map _ _ _ _ (𝟙 _) (Y.map f.op) (𝟙 _) (by simp)
    (by simpa only [Category.comp_id] using (rowVertexToDiagonal_site Y f v).symm)

/-- Kappa site naturality retains the original p and moves v to f(v). -/
theorem vertexDiagonalPullbackComparison_site
    {X Y : SimplicialObject SSet.{u}} (p : X ⟶ Y)
    {n m : SimplexCategory} (f : n ⟶ m) (v : Fin (n.len + 1)) :
    vertexDiagonalPullbackComparison p m (f v) ≫ vertexSitePullbackMap p f v =
      X.map f.op ≫ vertexDiagonalPullbackComparison p n v := by
  apply pullback.hom_ext
  · simp only [vertexSitePullbackMap, Category.assoc, pullback.lift_fst,
      (vertexDiagonalPullbackComparison_legs p m (f v)).1,
      (vertexDiagonalPullbackComparison_legs p n v).1, Category.comp_id]
    exact (rowVertexToDiagonal_site X f v).symm
  · simp only [vertexSitePullbackMap, Category.assoc, pullback.lift_snd,
      (vertexDiagonalPullbackComparison_legs p n v).2]
    rw [← Category.assoc, (vertexDiagonalPullbackComparison_legs p m (f v)).2]
    exact (p.naturality f.op).symm

/-- Compatible original diagram maps give the actual ordinary target pullback map. -/
def vertexTargetPullbackMap
    {X Y X' Y' : SimplicialObject SSet.{u}} {p : X ⟶ Y} {p' : X' ⟶ Y'}
    (a : X ⟶ X') (b : Y ⟶ Y') (h : a ≫ p' = p ≫ b)
    (n : SimplexCategory) (v : Fin (n.len + 1)) :
    pullback (SSet.simplicialDiagonalFunctor.map p) (rowVertexToDiagonal Y n v) ⟶
      pullback (SSet.simplicialDiagonalFunctor.map p') (rowVertexToDiagonal Y' n v) :=
  pullback.map _ _ _ _ (SSet.simplicialDiagonalFunctor.map a) (b.app (op n))
    (SSet.simplicialDiagonalFunctor.map b)
    (by simpa only [Functor.map_comp] using
      congrArg SSet.simplicialDiagonalFunctor.map h.symm)
    (rowVertexToDiagonal_naturality b n v)

/-- All original diagram maps commute with the same kappa without an outcome callback. -/
theorem vertexDiagonalPullbackComparison_naturality
    {X Y X' Y' : SimplicialObject SSet.{u}} {p : X ⟶ Y} {p' : X' ⟶ Y'}
    (a : X ⟶ X') (b : Y ⟶ Y') (h : a ≫ p' = p ≫ b)
    (n : SimplexCategory) (v : Fin (n.len + 1)) :
    vertexDiagonalPullbackComparison p n v ≫ vertexTargetPullbackMap a b h n v =
      a.app (op n) ≫ vertexDiagonalPullbackComparison p' n v := by
  apply pullback.hom_ext
  · simp only [vertexTargetPullbackMap, Category.assoc, pullback.lift_fst,
      (vertexDiagonalPullbackComparison_legs p' n v).1]
    rw [← Category.assoc, (vertexDiagonalPullbackComparison_legs p n v).1]
    exact rowVertexToDiagonal_naturality a n v
  · simp only [vertexTargetPullbackMap, Category.assoc, pullback.lift_snd,
      (vertexDiagonalPullbackComparison_legs p' n v).2]
    rw [← Category.assoc, (vertexDiagonalPullbackComparison_legs p n v).2]
    simpa only [NatTrans.comp_app] using (congrArg (fun f => f.app (op n)) h).symm

end SSet.EquifibredDiagonal
