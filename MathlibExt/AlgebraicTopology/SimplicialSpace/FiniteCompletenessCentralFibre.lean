/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.FiniteCompletenessComparison
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerHomColimits
import MathlibExt.AlgebraicTopology.SimplicialSpace.InverseTriangleData

/-!
# The original finite-K mapping presentation and central coherence fibre

Both chosen collapse pushouts are retained. Their contravariant inner mapping
pullbacks construct the inverse-test isomorphism and the strict central fibre,
including the whole adjacent tetrahedron and both independent inverse triangles.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SimplicialSpace.FiniteCompletenessMapping

open SSet.Rezk.FiniteCompleteness SegalHomotopy

/-- The actual contravariant inner mapping functor on the original raw diagrams. -/
def mappingFunctor (W : SimplicialSpace.{u}) :
    (SimplicialObject SSet.{u})ᵒᵖ ⥤ SSet.{u} :=
  ofSimplicialObject.op ⋙ innerHomFunctor.flip.obj W

/-- The same mapping functor, covariant into opposite simplicial sets. -/
def oppositeMappingFunctor (W : SimplicialSpace.{u}) :
    SimplicialObject SSet.{u} ⥤ SSet.{u}ᵒᵖ :=
  ofSimplicialObject ⋙ (innerHomFunctor.flip.obj W).rightOp

/-- Inner mapping out of an original raw simplicial-space diagram. -/
abbrev rawMapping (W : SimplicialSpace.{u}) (A : SimplicialObject SSet.{u}) :
    SSet.{u} := (mappingFunctor W).obj (op A)

/-- The actual original restriction along a raw diagram map. -/
abbrev restriction (W : SimplicialSpace.{u}) {A B : SimplicialObject SSet.{u}}
    (f : A ⟶ B) : rawMapping W B ⟶ rawMapping W A :=
  (mappingFunctor W).map f.op

/-- Restriction reverses the same original composite. -/
@[reassoc]
theorem restriction_comp (W : SimplicialSpace.{u})
    {A B C : SimplicialObject SSet.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    restriction W (f ≫ g) = restriction W g ≫ restriction W f := by
  exact (mappingFunctor W).map_comp g.op f.op

/-- The represented inner end identifies with the same outer value. -/
def representableMappingIso (W : SimplicialSpace.{u}) (n : ℕ) :
    rawMapping W (SSet.Rezk.representable n) ≅ W.diagram _⦋n⦌ :=
  discreteYonedaIso W n

/-- The original represented restriction preserves every ordinal operator. -/
@[reassoc]
theorem representableMappingIso_naturality (W : SimplicialSpace.{u})
    {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) :
    restriction W (SSet.simplicialSpaceDiscrete.map (SSet.stdSimplex.map f)) ≫
      (representableMappingIso W m).hom =
        (representableMappingIso W n).hom ≫ W.diagram.map f.op :=
  discreteYonedaIso_naturality_index W f

/-- The original inner mapping object of K. -/
abbrev mapping (W : SimplicialSpace.{u}) : SSet.{u} := rawMapping W K

/-- The first pushout retains the original three-simplex restriction. -/
def stage1ToThree (W : SimplicialSpace.{u}) :
    rawMapping W stage1 ⟶ W.diagram _⦋3⦌ :=
  restriction W stage1Cocone.inr ≫ (representableMappingIso W 3).hom

/-- The first pushout retains its original collapsed point. -/
def stage1ToPoint (W : SimplicialSpace.{u}) :
    rawMapping W stage1 ⟶ W.diagram _⦋0⦌ :=
  restriction W stage1Cocone.inl ≫ (representableMappingIso W 0).hom

/-- The second pushout retains its original first-stage restriction. -/
abbrev toStage1 (W : SimplicialSpace.{u}) : mapping W ⟶ rawMapping W stage1 :=
  restriction W stage2Cocone.inl

/-- The actual first collapsed point of K. -/
def toFirst (W : SimplicialSpace.{u}) : mapping W ⟶ W.diagram _⦋0⦌ :=
  toStage1 W ≫ stage1ToPoint W

/-- The actual middle three-simplex of K. -/
def toThree (W : SimplicialSpace.{u}) : mapping W ⟶ W.diagram _⦋3⦌ :=
  toStage1 W ≫ stage1ToThree W

/-- The actual last collapsed point of K. -/
def toLast (W : SimplicialSpace.{u}) : mapping W ⟶ W.diagram _⦋0⦌ :=
  restriction W stage2Cocone.inr ≫ (representableMappingIso W 0).hom

/-- The whole original central12 edge, in its backward orientation. -/
def toCentral (W : SimplicialSpace.{u}) : mapping W ⟶ W.diagram _⦋1⦌ :=
  toThree W ≫ W.diagram.map (SimplexCategory.mkOfLe (1 : Fin 4) 2 (by decide)).op

private theorem collapseIsSigma :
    SimplexCategory.const ⦋1⦌ ⦋0⦌ 0 = SimplexCategory.σ (0 : Fin 1) := by
  ext i
  fin_cases i <;> rfl

private theorem edge02IsOriginal :
    edge02 = SimplexCategory.mkOfLe (0 : Fin 4) 2 (by decide) := by
  ext i
  fin_cases i <;> rfl

private theorem edge13IsOriginal :
    edge13 = SimplexCategory.mkOfLe (1 : Fin 4) 3 (by decide) := by
  ext i
  fin_cases i <;> rfl

/-- Mapping preserves the actual original first collapse square as a pullback. -/
theorem stage1_isPullback (W : SimplicialSpace.{u}) :
    IsPullback (stage1ToThree W) (stage1ToPoint W)
      (W.diagram.map edge02.op) (W.diagram.σ (0 : Fin 1)) := by
  let _ := innerHom_rightOp_preservesColimitsOfShape WalkingSpan W
  let _ : PreservesColimitsOfShape WalkingSpan (oppositeMappingFunctor W) := by
    unfold oppositeMappingFunctor
    infer_instance
  have sq := (Functor.map_isPushout (oppositeMappingFunctor W)
    (IsPushout.of_isColimit stage1IsColimit)).unop
  refine sq.of_iso (Iso.refl _) (representableMappingIso W 3)
    (representableMappingIso W 0) (representableMappingIso W 1) ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · exact representableMappingIso_naturality W edge02
  · change restriction W (representableCollapse 1) ≫ (representableMappingIso W 1).hom =
      (representableMappingIso W 0).hom ≫ W.diagram.map (SimplexCategory.σ (0 : Fin 1)).op
    rw [← collapseIsSigma]
    exact representableMappingIso_naturality W (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0)

/-- Mapping preserves the actual second collapse square, with its original order. -/
theorem stage2_isPullback (W : SimplicialSpace.{u}) :
    IsPullback (toStage1 W) (toLast W)
      (stage1ToThree W ≫ W.diagram.map edge13.op) (W.diagram.σ (0 : Fin 1)) := by
  let _ := innerHom_rightOp_preservesColimitsOfShape WalkingSpan W
  let _ : PreservesColimitsOfShape WalkingSpan (oppositeMappingFunctor W) := by
    unfold oppositeMappingFunctor
    infer_instance
  have sq := (Functor.map_isPushout (oppositeMappingFunctor W)
    (IsPushout.of_isColimit stage2IsColimit)).unop.flip
  refine sq.of_iso (Iso.refl _) (Iso.refl _) (representableMappingIso W 0)
    (representableMappingIso W 1) ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · change restriction W secondLeg ≫ (representableMappingIso W 1).hom = _
    rw [secondLeg, restriction_comp, Category.assoc,
      representableMappingIso_naturality]
    rfl
  · change restriction W (representableCollapse 1) ≫ (representableMappingIso W 1).hom =
      (representableMappingIso W 0).hom ≫ W.diagram.map (SimplexCategory.σ (0 : Fin 1)).op
    rw [← collapseIsSigma]
    exact representableMappingIso_naturality W (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0)

/-- The original02 long edge is the degeneracy of the first collapsed point. -/
@[reassoc]
theorem toThree_edge02 (W : SimplicialSpace.{u}) :
    toThree W ≫ W.diagram.map edge02.op = toFirst W ≫ W.diagram.σ (0 : Fin 1) := by
  simpa only [toThree, toFirst, Category.assoc] using
    congrArg (fun f => toStage1 W ≫ f) (stage1_isPullback W).w

/-- The original13 long edge is the degeneracy of the last collapsed point. -/
@[reassoc]
theorem toThree_edge13 (W : SimplicialSpace.{u}) :
    toThree W ≫ W.diagram.map edge13.op = toLast W ≫ W.diagram.σ (0 : Fin 1) := by
  simpa only [toThree, Category.assoc] using (stage2_isPullback W).w

/-- The lift into the same original mapping end from its three compatible legs. -/
def mappingLift (W : SimplicialSpace.{u}) {T : SSet.{u}}
    (t : T ⟶ W.diagram _⦋3⦌) (p₀ p₁ : T ⟶ W.diagram _⦋0⦌)
    (h₀ : t ≫ W.diagram.map edge02.op = p₀ ≫ W.diagram.σ (0 : Fin 1))
    (h₁ : t ≫ W.diagram.map edge13.op = p₁ ≫ W.diagram.σ (0 : Fin 1)) :
    T ⟶ mapping W :=
  (stage2_isPullback W).lift ((stage1_isPullback W).lift t p₀ h₀) p₁ (by
    rw [← Category.assoc, IsPullback.lift_fst]
    exact h₁)

/-- The universal lift retains the whole original three-simplex. -/
@[reassoc (attr := simp)]
theorem mappingLift_three (W : SimplicialSpace.{u}) {T : SSet.{u}}
    (t : T ⟶ W.diagram _⦋3⦌) (p₀ p₁ : T ⟶ W.diagram _⦋0⦌) (h₀ h₁) :
    mappingLift W t p₀ p₁ h₀ h₁ ≫ toThree W = t := by
  unfold mappingLift toThree
  rw [← Category.assoc, IsPullback.lift_fst, IsPullback.lift_fst]

/-- The universal lift retains the first actual collapse point. -/
@[reassoc (attr := simp)]
theorem mappingLift_first (W : SimplicialSpace.{u}) {T : SSet.{u}}
    (t : T ⟶ W.diagram _⦋3⦌) (p₀ p₁ : T ⟶ W.diagram _⦋0⦌) (h₀ h₁) :
    mappingLift W t p₀ p₁ h₀ h₁ ≫ toFirst W = p₀ := by
  unfold mappingLift toFirst
  rw [← Category.assoc, IsPullback.lift_fst, IsPullback.lift_snd]

/-- The universal lift retains the last actual collapse point. -/
@[reassoc (attr := simp)]
theorem mappingLift_last (W : SimplicialSpace.{u}) {T : SSet.{u}}
    (t : T ⟶ W.diagram _⦋3⦌) (p₀ p₁ : T ⟶ W.diagram _⦋0⦌) (h₀ h₁) :
    mappingLift W t p₀ p₁ h₀ h₁ ≫ toLast W = p₁ := by
  unfold mappingLift
  exact IsPullback.lift_snd _ _ _ _

/-- All three original K legs jointly determine a map into its mapping end. -/
theorem mapping_hom_ext (W : SimplicialSpace.{u}) {T : SSet.{u}}
    {f g : T ⟶ mapping W}
    (ht : f ≫ toThree W = g ≫ toThree W)
    (h₀ : f ≫ toFirst W = g ≫ toFirst W)
    (h₁ : f ≫ toLast W = g ≫ toLast W) : f = g := by
  apply (stage2_isPullback W).hom_ext
  · apply (stage1_isPullback W).hom_ext
    · simpa only [toThree, Category.assoc] using ht
    · simpa only [toFirst, Category.assoc] using h₀
  · exact h₁

private theorem centralTargetOrdinal :
    SimplexCategory.δ (0 : Fin 2) ≫ edge02 =
      SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.mkOfLe (1 : Fin 4) 2 (by decide) := by
  ext i
  fin_cases i
  rfl

private theorem centralSourceOrdinal :
    SimplexCategory.δ (1 : Fin 2) ≫ edge13 =
      SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.mkOfLe (1 : Fin 4) 2 (by decide) := by
  ext i
  fin_cases i
  rfl

/-- The first collapsed point is the target of the original central12 edge. -/
@[reassoc]
theorem toFirst_target (W : SimplicialSpace.{u}) :
    toFirst W = toCentral W ≫ W.diagram.δ (0 : Fin 2) := by
  have h := congrArg (fun f => f ≫ W.diagram.δ (0 : Fin 2)) (toThree_edge02 W)
  have he : W.diagram.map edge02.op ≫ W.diagram.δ (0 : Fin 2) =
      W.diagram.map (SimplexCategory.mkOfLe (1 : Fin 4) 2 (by decide)).op ≫
        W.diagram.δ (0 : Fin 2) := by
    change W.diagram.map edge02.op ≫ W.diagram.map _ = _ ≫ W.diagram.map _
    rw [← W.diagram.map_comp, ← W.diagram.map_comp, ← op_comp, ← op_comp]
    congr 1
    exact congrArg Quiver.Hom.op centralTargetOrdinal
  have hs : W.diagram.σ (0 : Fin 1) ≫ W.diagram.δ (0 : Fin 2) = 𝟙 _ :=
    W.diagram.δ_comp_σ_self (i := (0 : Fin 1))
  simpa only [Category.assoc, he, hs,
    Category.comp_id, toCentral] using h.symm

/-- The last collapsed point is the source of the same original central12 edge. -/
@[reassoc]
theorem toLast_source (W : SimplicialSpace.{u}) :
    toLast W = toCentral W ≫ W.diagram.δ (1 : Fin 2) := by
  have h := congrArg (fun f => f ≫ W.diagram.δ (1 : Fin 2)) (toThree_edge13 W)
  have he : W.diagram.map edge13.op ≫ W.diagram.δ (1 : Fin 2) =
      W.diagram.map (SimplexCategory.mkOfLe (1 : Fin 4) 2 (by decide)).op ≫
        W.diagram.δ (1 : Fin 2) := by
    change W.diagram.map edge13.op ≫ W.diagram.map _ = _ ≫ W.diagram.map _
    rw [← W.diagram.map_comp, ← W.diagram.map_comp, ← op_comp, ← op_comp]
    congr 1
    exact congrArg Quiver.Hom.op centralSourceOrdinal
  have hs : W.diagram.σ (0 : Fin 1) ≫ W.diagram.δ (1 : Fin 2) = 𝟙 _ :=
    W.diagram.δ_comp_σ_succ (i := (0 : Fin 1))
  simpa only [Category.assoc, he, hs,
    Category.comp_id, toCentral] using h.symm

/-- The actual chosen inverse-test pullback, retaining its W3 and W1 projections. -/
abbrev inverseTest (W : SimplicialSpace.{u}) : SSet.{u} :=
  pullback (inverseRestriction W) (identityTriple W)

/-- The original whole K restriction into the chosen inverse-test pullback. -/
def inverseTestHom (W : SimplicialSpace.{u}) : mapping W ⟶ inverseTest W :=
  pullback.lift (toThree W) (toCentral W) (by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · change toThree W ≫ inverseRestriction W ≫ inverseFirst W =
          toCentral W ≫ identityTriple W ≫ inverseFirst W
        rw [inverseRestriction_first, identityTriple_first, ← edge02IsOriginal,
          ← Category.assoc, toThree_edge02, toFirst_target, Category.assoc]
      · change toThree W ≫ inverseRestriction W ≫ inverseMiddle W =
          toCentral W ≫ identityTriple W ≫ inverseMiddle W
        rw [inverseRestriction_middle, identityTriple_middle, Category.comp_id]
        rfl
    · change toThree W ≫ inverseRestriction W ≫ inverseLast W =
        toCentral W ≫ identityTriple W ≫ inverseLast W
      rw [inverseRestriction_last, identityTriple_last, ← edge13IsOriginal,
        ← Category.assoc, toThree_edge13, toLast_source, Category.assoc])

/-- The inverse-test map retains the whole original three-simplex. -/
@[reassoc (attr := simp)]
theorem inverseTestHom_three (W : SimplicialSpace.{u}) :
    inverseTestHom W ≫ pullback.fst _ _ = toThree W := pullback.lift_fst _ _ _

/-- The inverse-test map retains precisely the original central12 edge. -/
@[reassoc (attr := simp)]
theorem inverseTestHom_central (W : SimplicialSpace.{u}) :
    inverseTestHom W ≫ pullback.snd _ _ = toCentral W := pullback.lift_snd _ _ _

/-- The inverse-test pullback gives the two original collapse compatibilities. -/
def inverseTestInv (W : SimplicialSpace.{u}) : inverseTest W ⟶ mapping W :=
  mappingLift W (pullback.fst _ _) (pullback.snd _ _ ≫ W.diagram.δ (0 : Fin 2))
    (pullback.snd _ _ ≫ W.diagram.δ (1 : Fin 2))
    (by
      have h := congrArg (fun f => f ≫ inverseFirst W)
        (pullback.condition (f := inverseRestriction W) (g := identityTriple W))
      simpa only [Category.assoc, inverseRestriction_first, identityTriple_first,
        edge02IsOriginal] using h)
    (by
      have h := congrArg (fun f => f ≫ inverseLast W)
        (pullback.condition (f := inverseRestriction W) (g := identityTriple W))
      simpa only [Category.assoc, inverseRestriction_last, identityTriple_last,
        edge13IsOriginal] using h)

/-- The reverse inverse-test map retains its entire W3 projection. -/
@[reassoc (attr := simp)]
theorem inverseTestInv_three (W : SimplicialSpace.{u}) :
    inverseTestInv W ≫ toThree W = pullback.fst _ _ := by
  unfold inverseTestInv
  exact mappingLift_three _ _ _ _ _ _

/-- The reverse inverse-test map retains its original first collapse point. -/
@[reassoc (attr := simp)]
theorem inverseTestInv_first (W : SimplicialSpace.{u}) :
    inverseTestInv W ≫ toFirst W = pullback.snd _ _ ≫ W.diagram.δ (0 : Fin 2) := by
  unfold inverseTestInv
  exact mappingLift_first _ _ _ _ _ _

/-- The reverse inverse-test map retains its original last collapse point. -/
@[reassoc (attr := simp)]
theorem inverseTestInv_last (W : SimplicialSpace.{u}) :
    inverseTestInv W ≫ toLast W = pullback.snd _ _ ≫ W.diagram.δ (1 : Fin 2) := by
  unfold inverseTestInv
  exact mappingLift_last _ _ _ _ _ _

/-- The reverse inverse-test map retains its original central12 edge. -/
@[reassoc (attr := simp)]
theorem inverseTestInv_central (W : SimplicialSpace.{u}) :
    inverseTestInv W ≫ toCentral W = pullback.snd _ _ := by
  rw [toCentral, inverseTestInv_three_assoc]
  have h := congrArg (fun f => f ≫ inverseMiddle W)
    (pullback.condition (f := inverseRestriction W) (g := identityTriple W))
  simpa only [Category.assoc, inverseRestriction_middle, identityTriple_middle,
    Category.comp_id] using h

/-- The whole original K mapping presentation, with the same native inverse-test projections. -/
def inverseTestIso (W : SimplicialSpace.{u}) : mapping W ≅ inverseTest W where
  hom := inverseTestHom W
  inv := inverseTestInv W
  hom_inv_id := by
    apply mapping_hom_ext W
    · simp only [Category.assoc, inverseTestInv_three, inverseTestHom_three,
        Category.id_comp]
    · simp only [Category.assoc, inverseTestInv_first, inverseTestHom_central_assoc,
        ← toFirst_target, Category.id_comp]
    · simp only [Category.assoc, inverseTestInv_last, inverseTestHom_central_assoc,
        ← toLast_source, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, inverseTestHom_three, inverseTestInv_three,
        Category.id_comp]
    · simp only [Category.assoc, inverseTestHom_central, inverseTestInv_central,
        Category.id_comp]

private theorem faceMap (W : SimplicialSpace.{u}) (i : Fin 4) (j : Fin 3)
    (e : ⦋1⦌ ⟶ ⦋3⦌) (h : SimplexCategory.δ j ≫ SimplexCategory.δ i = e) :
    W.diagram.δ i ≫ W.diagram.δ j = W.diagram.map e.op := by
  change W.diagram.map (SimplexCategory.δ i).op ≫
    W.diagram.map (SimplexCategory.δ j).op = _
  rw [← W.diagram.map_comp, ← op_comp, h]

private theorem edgeEndpoint (W : SimplicialSpace.{u}) (e e' : ⦋1⦌ ⟶ ⦋3⦌)
    (i j : Fin 2) (h : SimplexCategory.δ i ≫ e = SimplexCategory.δ j ≫ e') :
    W.diagram.map e.op ≫ W.diagram.δ i = W.diagram.map e'.op ≫ W.diagram.δ j := by
  change W.diagram.map e.op ≫ W.diagram.map (SimplexCategory.δ i).op =
    W.diagram.map e'.op ≫ W.diagram.map (SimplexCategory.δ j).op
  rw [← W.diagram.map_comp, ← W.diagram.map_comp, ← op_comp, ← op_comp, h]

variable (W : SimplicialSpace.{u}) (x y : (W.diagram _⦋0⦌) _⦋0⦌)
  (a : (mappingFibre W y x) _⦋0⦌)

/-- The strict fibre of the same original central12 restriction at a. -/
abbrev centralFibre : SSet.{u} :=
  pullback (toCentral W) (SSet.yonedaEquiv.symm a ≫ mappingFibre.fst W y x)

/-- The original K projection of the strict central fibre. -/
abbrev centralProjection : centralFibre W x y a ⟶ mapping W := pullback.fst _ _

/-- The original scalar point of the strict central fibre. -/
abbrev centralPoint : centralFibre W x y a ⟶ (Δ[0] : SSet.{u}) := pullback.snd _ _

/-- The ordered independent inverse triangles give the actual adjacent pair. -/
def pairedToAdjacent :
    InverseTriangle.pairedSpace W y x a ⟶ AdjacentTriangle.pair W x y x y :=
  pullback.lift
    (InverseTriangle.pairedLeft W y x a ≫ InverseTriangle.leftTriangle W y x a)
    (InverseTriangle.pairedRight W y x a ≫ InverseTriangle.rightTriangle W y x a)
    (by
      simp only [Category.assoc, InverseTriangle.left_fixedLast,
        InverseTriangle.right_fixedFirst]
      change (InverseTriangle.pairedLeft W y x a ≫ InverseTriangle.leftToPoint W y x a) ≫
          SSet.yonedaEquiv.symm a =
        (InverseTriangle.pairedRight W y x a ≫ InverseTriangle.rightToPoint W y x a) ≫
          SSet.yonedaEquiv.symm a
      rw [InverseTriangle.pairedToPoint_right]
      rfl)

/-- The adjacent pair keeps the whole original left012 triangle. -/
@[reassoc (attr := simp)]
theorem pairedToAdjacent_left :
    pairedToAdjacent W x y a ≫ AdjacentTriangle.pair012 W x y x y =
      InverseTriangle.pairedLeft W y x a ≫ InverseTriangle.leftTriangle W y x a :=
  pullback.lift_fst _ _ _

/-- The adjacent pair keeps the whole original right123 triangle. -/
@[reassoc (attr := simp)]
theorem pairedToAdjacent_right :
    pairedToAdjacent W x y a ≫ AdjacentTriangle.pair123 W x y x y =
      InverseTriangle.pairedRight W y x a ≫ InverseTriangle.rightTriangle W y x a :=
  pullback.lift_snd _ _ _

/-- The actual coherence pullback includes the full original tetrahedron. -/
abbrev coherentFibre : SSet.{u} :=
  pullback (AdjacentTriangle.comparison W x y x y) (pairedToAdjacent W x y a)

/-- The whole W3 map of the coherence pullback. -/
def coherentThree : coherentFibre W x y a ⟶ W.diagram _⦋3⦌ :=
  pullback.fst _ _ ≫ AdjacentTriangle.tetrahedronProjection W x y x y

/-- Its original Delta0 projection uses the given ordered pair. -/
def coherentPoint : coherentFibre W x y a ⟶ (Δ[0] : SSet.{u}) :=
  pullback.snd _ _ ≫ InverseTriangle.pairedToPoint W y x a

/-- The same independent left inverse-space projection. -/
abbrev coherentLeft : coherentFibre W x y a ⟶ InverseTriangle.leftSpace W y x a :=
  pullback.snd _ _ ≫ InverseTriangle.pairedLeft W y x a

/-- The same independent right inverse-space projection. -/
abbrev coherentRight : coherentFibre W x y a ⟶ InverseTriangle.rightSpace W y x a :=
  pullback.snd _ _ ≫ InverseTriangle.pairedRight W y x a

/-- The full original three-edge projection of the coherent tetrahedron. -/
def coherentEdges : coherentFibre W x y a ⟶
    (mappingFibre W x y ⨯ mappingFibre W y x) ⨯ mappingFibre W x y :=
  pullback.fst (AdjacentTriangle.comparison W x y x y) (pairedToAdjacent W x y a) ≫
    AdjacentTriangle.tetrahedronEdges W x y x y

/-- The literal delta3 face of the whole W3 map is precisely the left triangle. -/
@[reassoc]
theorem coherent_face012 :
    coherentThree W x y a ≫ W.diagram.δ (3 : Fin 4) =
      coherentLeft W x y a ≫ InverseTriangle.leftTriangle W y x a ≫
        triangleProjection W x y x := by
  have h := congrArg (fun f => f ≫ AdjacentTriangle.pair012 W x y x y ≫
      triangleProjection W x y x)
    (pullback.condition (f := AdjacentTriangle.comparison W x y x y)
      (g := pairedToAdjacent W x y a))
  simpa only [Category.assoc, AdjacentTriangle.comparison012_assoc,
    AdjacentTriangle.face012_projection, pairedToAdjacent_left_assoc,
    coherentThree, coherentLeft] using h

/-- The literal delta0 face of the whole W3 map is precisely the right triangle. -/
@[reassoc]
theorem coherent_face123 :
    coherentThree W x y a ≫ W.diagram.δ (0 : Fin 4) =
      coherentRight W x y a ≫ InverseTriangle.rightTriangle W y x a ≫
        triangleProjection W y x y := by
  have h := congrArg (fun f => f ≫ AdjacentTriangle.pair123 W x y x y ≫
      triangleProjection W y x y)
    (pullback.condition (f := AdjacentTriangle.comparison W x y x y)
      (g := pairedToAdjacent W x y a))
  simpa only [Category.assoc, AdjacentTriangle.comparison123_assoc,
    AdjacentTriangle.face123_projection, pairedToAdjacent_right_assoc,
    coherentThree, coherentRight] using h

/-- The whole original02 edge in the coherent fibre is the identity at x. -/
@[reassoc]
theorem coherent_edge02 :
    coherentThree W x y a ≫ W.diagram.map edge02.op =
      coherentPoint W x y a ≫ SSet.yonedaEquiv.symm x ≫ W.diagram.σ (0 : Fin 1) := by
  have hface : W.diagram.δ (3 : Fin 4) ≫ W.diagram.δ (1 : Fin 3) =
      W.diagram.map edge02.op := faceMap W 3 1 edge02 (by ext i; fin_cases i <;> rfl)
  rw [← hface, ← Category.assoc, coherent_face012]
  simp only [Category.assoc]
  rw [← triangleMiddle_fst, InverseTriangle.left_middle_assoc,
    InverseTriangle.identityPoint_fst]
  rfl

/-- The whole original13 edge in the coherent fibre is the identity at y. -/
@[reassoc]
theorem coherent_edge13 :
    coherentThree W x y a ≫ W.diagram.map edge13.op =
      coherentPoint W x y a ≫ SSet.yonedaEquiv.symm y ≫ W.diagram.σ (0 : Fin 1) := by
  have hface : W.diagram.δ (0 : Fin 4) ≫ W.diagram.δ (1 : Fin 3) =
      W.diagram.map edge13.op := faceMap W 0 1 edge13 (by ext i; fin_cases i <;> rfl)
  rw [← hface, ← Category.assoc, coherent_face123]
  simp only [Category.assoc]
  rw [← triangleMiddle_fst, InverseTriangle.right_middle_assoc,
    InverseTriangle.identityPoint_fst]
  simp only [coherentPoint, Category.assoc,
    InverseTriangle.pairedToPoint_right_assoc]

/-- The original central12 edge is the same prescribed a throughout the coherent fibre. -/
@[reassoc]
theorem coherent_central :
    coherentThree W x y a ≫
      W.diagram.map (SimplexCategory.mkOfLe (1 : Fin 4) 2 (by decide)).op =
        coherentPoint W x y a ≫ SSet.yonedaEquiv.symm a ≫ mappingFibre.fst W y x := by
  have hface : W.diagram.δ (3 : Fin 4) ≫ W.diagram.δ (0 : Fin 3) =
      W.diagram.map (SimplexCategory.mkOfLe (1 : Fin 4) 2 (by decide)).op :=
    faceMap W 3 0 _ (by ext i; fin_cases i <;> rfl)
  rw [← hface, ← Category.assoc, coherent_face012]
  simp only [Category.assoc]
  rw [InverseTriangle.left_lastFace]
  rfl

/-- The coherent tetrahedron and original point construct the same K mapping lift. -/
def coherentToMapping : coherentFibre W x y a ⟶ mapping W :=
  mappingLift W (coherentThree W x y a)
    (coherentPoint W x y a ≫ SSet.yonedaEquiv.symm x)
    (coherentPoint W x y a ≫ SSet.yonedaEquiv.symm y)
    (by simpa only [Category.assoc] using coherent_edge02 W x y a)
    (by simpa only [Category.assoc] using coherent_edge13 W x y a)

/-- The reverse coherent map preserves the whole original W3 projection. -/
@[reassoc (attr := simp)]
theorem coherentToMapping_three :
    coherentToMapping W x y a ≫ toThree W = coherentThree W x y a := by
  unfold coherentToMapping
  exact mappingLift_three _ _ _ _ _ _

/-- The reverse coherent map preserves the first collapsed point. -/
@[reassoc (attr := simp)]
theorem coherentToMapping_first :
    coherentToMapping W x y a ≫ toFirst W =
      coherentPoint W x y a ≫ SSet.yonedaEquiv.symm x := by
  unfold coherentToMapping
  exact mappingLift_first _ _ _ _ _ _

/-- The reverse coherent map preserves the last collapsed point. -/
@[reassoc (attr := simp)]
theorem coherentToMapping_last :
    coherentToMapping W x y a ≫ toLast W =
      coherentPoint W x y a ≫ SSet.yonedaEquiv.symm y := by
  unfold coherentToMapping
  exact mappingLift_last _ _ _ _ _ _

/-- The coherent tetrahedron gives the reverse map into the strict original central fibre. -/
def centralInv : coherentFibre W x y a ⟶ centralFibre W x y a :=
  pullback.lift (coherentToMapping W x y a) (coherentPoint W x y a) (by
    rw [toCentral, coherentToMapping_three_assoc, coherent_central])

/-- The reverse central map keeps its whole original K mapping point. -/
@[reassoc (attr := simp)]
theorem centralInv_projection :
    centralInv W x y a ≫ centralProjection W x y a = coherentToMapping W x y a :=
  pullback.lift_fst _ _ _

/-- The reverse central map keeps the same original Delta0 point. -/
@[reassoc (attr := simp)]
theorem centralInv_point :
    centralInv W x y a ≫ centralPoint W x y a = coherentPoint W x y a :=
  pullback.lift_snd _ _ _

private theorem centralFirst :
    centralProjection W x y a ≫ toFirst W =
      centralPoint W x y a ≫ SSet.yonedaEquiv.symm x := by
  have hp : SSet.yonedaEquiv.symm a ≫ mappingFibre.snd W y x = 𝟙 _ :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have ha : SSet.yonedaEquiv.symm a ≫ mappingFibre.fst W y x ≫ W.diagram.δ (0 : Fin 2) =
      SSet.yonedaEquiv.symm x := by
    rw [mappingFibre.target_eq, ← Category.assoc, hp, Category.id_comp]
  have h := congrArg (fun f => f ≫ W.diagram.δ (0 : Fin 2))
    (pullback.condition (f := toCentral W)
      (g := SSet.yonedaEquiv.symm a ≫ mappingFibre.fst W y x))
  simpa only [Category.assoc, ha, ← toFirst_target] using h

private theorem centralLast :
    centralProjection W x y a ≫ toLast W =
      centralPoint W x y a ≫ SSet.yonedaEquiv.symm y := by
  have hp : SSet.yonedaEquiv.symm a ≫ mappingFibre.snd W y x = 𝟙 _ :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have ha : SSet.yonedaEquiv.symm a ≫ mappingFibre.fst W y x ≫ W.diagram.δ (1 : Fin 2) =
      SSet.yonedaEquiv.symm y := by
    rw [mappingFibre.source_eq, ← Category.assoc, hp, Category.id_comp]
  have h := congrArg (fun f => f ≫ W.diagram.δ (1 : Fin 2))
    (pullback.condition (f := toCentral W)
      (g := SSet.yonedaEquiv.symm a ≫ mappingFibre.fst W y x))
  simpa only [Category.assoc, ha, ← toLast_source] using h

private def centralCandidateLeft : centralFibre W x y a ⟶ mappingFibre W x y :=
  pullback.lift
    (centralProjection W x y a ≫ toThree W ≫
      W.diagram.map (SimplexCategory.mkOfSucc (0 : Fin 3)).op)
    (centralPoint W x y a) (by
      apply prod.hom_ext
      · simp only [Category.assoc, mappingEndpoint_fst, mappingPointPair_fst]
        have he := edgeEndpoint W (SimplexCategory.mkOfSucc (0 : Fin 3)) edge02 1 1
          (by ext i; fin_cases i; rfl)
        rw [he, toThree_edge02_assoc]
        have hs : W.diagram.σ (0 : Fin 1) ≫ W.diagram.δ (1 : Fin 2) = 𝟙 _ :=
          W.diagram.δ_comp_σ_succ (i := (0 : Fin 1))
        rw [hs, Category.comp_id, centralFirst]
      · simp only [Category.assoc, mappingEndpoint_snd, mappingPointPair_snd]
        have he := edgeEndpoint W (SimplexCategory.mkOfSucc (0 : Fin 3))
          (SimplexCategory.mkOfLe (1 : Fin 4) 2 (by decide)) 0 1
          (by ext i; fin_cases i; rfl)
        rw [he]
        change centralProjection W x y a ≫ toCentral W ≫ W.diagram.δ (1 : Fin 2) = _
        rw [← toLast_source, centralLast])

private def centralCandidateRight : centralFibre W x y a ⟶ mappingFibre W x y :=
  pullback.lift
    (centralProjection W x y a ≫ toThree W ≫
      W.diagram.map (SimplexCategory.mkOfSucc (2 : Fin 3)).op)
    (centralPoint W x y a) (by
      apply prod.hom_ext
      · simp only [Category.assoc, mappingEndpoint_fst, mappingPointPair_fst]
        have he := edgeEndpoint W (SimplexCategory.mkOfSucc (2 : Fin 3))
          (SimplexCategory.mkOfLe (1 : Fin 4) 2 (by decide)) 1 0
          (by ext i; fin_cases i; rfl)
        rw [he]
        change centralProjection W x y a ≫ toCentral W ≫ W.diagram.δ (0 : Fin 2) = _
        rw [← toFirst_target, centralFirst]
      · simp only [Category.assoc, mappingEndpoint_snd, mappingPointPair_snd]
        have he := edgeEndpoint W (SimplexCategory.mkOfSucc (2 : Fin 3)) edge13 0 0
          (by ext i; fin_cases i; rfl)
        rw [he, toThree_edge13_assoc]
        have hs : W.diagram.σ (0 : Fin 1) ≫ W.diagram.δ (0 : Fin 2) = 𝟙 _ :=
          W.diagram.δ_comp_σ_self (i := (0 : Fin 1))
        rw [hs, Category.comp_id, centralLast])

@[reassoc (attr := simp)]
private theorem centralCandidateLeft_fst :
    centralCandidateLeft W x y a ≫ mappingFibre.fst W x y =
      centralProjection W x y a ≫ toThree W ≫
        W.diagram.map (SimplexCategory.mkOfSucc (0 : Fin 3)).op :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem centralCandidateRight_fst :
    centralCandidateRight W x y a ≫ mappingFibre.fst W x y =
      centralProjection W x y a ≫ toThree W ≫
        W.diagram.map (SimplexCategory.mkOfSucc (2 : Fin 3)).op :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem centralCandidateLeft_snd :
    centralCandidateLeft W x y a ≫ mappingFibre.snd W x y = centralPoint W x y a :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
private theorem centralCandidateRight_snd :
    centralCandidateRight W x y a ≫ mappingFibre.snd W x y = centralPoint W x y a :=
  pullback.lift_snd _ _ _

private def centralTriangleLeft : centralFibre W x y a ⟶ triangleSpace W x y x :=
  pullback.lift (centralProjection W x y a ≫ toThree W ≫ W.diagram.δ (3 : Fin 4))
    (prod.lift (centralCandidateLeft W x y a)
      (centralPoint W x y a ≫ SSet.yonedaEquiv.symm a)) (by
      apply pullback.hom_ext
      · simp only [Category.assoc, twoEdgeComparison_fst, twoEdgePair_fst,
          prod.lift_fst_assoc, centralCandidateLeft_fst]
        rw [faceMap W 3 2 (SimplexCategory.mkOfSucc (0 : Fin 3))
          (by ext i; fin_cases i <;> rfl)]
      · simp only [Category.assoc, twoEdgeComparison_snd, twoEdgePair_snd,
          prod.lift_snd_assoc]
        rw [faceMap W 3 0 (SimplexCategory.mkOfLe (1 : Fin 4) 2 (by decide))
          (by ext i; fin_cases i <;> rfl)]
        change centralProjection W x y a ≫ toCentral W = _
        exact pullback.condition)

private def centralTriangleRight : centralFibre W x y a ⟶ triangleSpace W y x y :=
  pullback.lift (centralProjection W x y a ≫ toThree W ≫ W.diagram.δ (0 : Fin 4))
    (prod.lift (centralPoint W x y a ≫ SSet.yonedaEquiv.symm a)
      (centralCandidateRight W x y a)) (by
      apply pullback.hom_ext
      · simp only [Category.assoc, twoEdgeComparison_fst, twoEdgePair_fst,
          prod.lift_fst_assoc]
        rw [faceMap W 0 2 (SimplexCategory.mkOfLe (1 : Fin 4) 2 (by decide))
          (by ext i; fin_cases i <;> rfl)]
        change centralProjection W x y a ≫ toCentral W = _
        exact pullback.condition
      · simp only [Category.assoc, twoEdgeComparison_snd, twoEdgePair_snd,
          prod.lift_snd_assoc, centralCandidateRight_fst]
        rw [faceMap W 0 0 (SimplexCategory.mkOfSucc (2 : Fin 3))
          (by ext i; fin_cases i <;> rfl)])

@[reassoc (attr := simp)]
private theorem centralTriangleLeft_projection :
    centralTriangleLeft W x y a ≫ triangleProjection W x y x =
      centralProjection W x y a ≫ toThree W ≫ W.diagram.δ (3 : Fin 4) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem centralTriangleRight_projection :
    centralTriangleRight W x y a ≫ triangleProjection W y x y =
      centralProjection W x y a ≫ toThree W ≫ W.diagram.δ (0 : Fin 4) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem centralTriangleLeft_comparison :
    centralTriangleLeft W x y a ≫ triangleComparison W x y x =
      prod.lift (centralCandidateLeft W x y a)
        (centralPoint W x y a ≫ SSet.yonedaEquiv.symm a) := pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
private theorem centralTriangleRight_comparison :
    centralTriangleRight W x y a ≫ triangleComparison W y x y =
      prod.lift (centralPoint W x y a ≫ SSet.yonedaEquiv.symm a)
        (centralCandidateRight W x y a) := pullback.lift_snd _ _ _

private theorem centralTriangleLeft_middle :
    centralTriangleLeft W x y a ≫ triangleMiddle W x y x =
      centralPoint W x y a ≫ InverseTriangle.identityPoint W x := by
  apply pullback.hom_ext (f := mappingEndpoint W) (g := mappingPointPair W x x)
  · change (centralTriangleLeft W x y a ≫ triangleMiddle W x y x) ≫ mappingFibre.fst W x x =
      (centralPoint W x y a ≫ InverseTriangle.identityPoint W x) ≫ mappingFibre.fst W x x
    simp only [Category.assoc, triangleMiddle_fst, centralTriangleLeft_projection_assoc,
      InverseTriangle.identityPoint_fst]
    rw [faceMap W 3 1 edge02 (by ext i; fin_cases i <;> rfl), toThree_edge02]
    rw [← Category.assoc, centralFirst, Category.assoc]
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

private theorem centralTriangleRight_middle :
    centralTriangleRight W x y a ≫ triangleMiddle W y x y =
      centralPoint W x y a ≫ InverseTriangle.identityPoint W y := by
  apply pullback.hom_ext (f := mappingEndpoint W) (g := mappingPointPair W y y)
  · change (centralTriangleRight W x y a ≫ triangleMiddle W y x y) ≫ mappingFibre.fst W y y =
      (centralPoint W x y a ≫ InverseTriangle.identityPoint W y) ≫ mappingFibre.fst W y y
    simp only [Category.assoc, triangleMiddle_fst, centralTriangleRight_projection_assoc,
      InverseTriangle.identityPoint_fst]
    rw [faceMap W 0 1 edge13 (by ext i; fin_cases i <;> rfl), toThree_edge13]
    rw [← Category.assoc, centralLast, Category.assoc]
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

private def centralFixedLeft : centralFibre W x y a ⟶ FixedEdgeTriangle.leftTriangle W y x a :=
  (FixedEdgeTriangle.leftGeometry W y x a).1.lift
    (centralTriangleLeft W x y a) (centralCandidateLeft W x y a) (by
      apply prod.hom_ext
      · simp only [Category.assoc, centralTriangleLeft_comparison, prod.lift_fst,
          (FixedEdgeTriangle.leftPairLaws W y x a).1, Category.comp_id]
      · simp only [Category.assoc, centralTriangleLeft_comparison, prod.lift_snd,
          (FixedEdgeTriangle.leftPairLaws W y x a).2, centralCandidateLeft_snd_assoc])

private def centralFixedRight : centralFibre W x y a ⟶ FixedEdgeTriangle.rightTriangle W y x a :=
  (FixedEdgeTriangle.rightGeometry W y x a).1.lift
    (centralTriangleRight W x y a) (centralCandidateRight W x y a) (by
      apply prod.hom_ext
      · simp only [Category.assoc, centralTriangleRight_comparison, prod.lift_fst,
          (FixedEdgeTriangle.rightPairLaws W y x a).1, centralCandidateRight_snd_assoc]
      · simp only [Category.assoc, centralTriangleRight_comparison, prod.lift_snd,
          (FixedEdgeTriangle.rightPairLaws W y x a).2, Category.comp_id])

@[reassoc (attr := simp)]
private theorem centralFixedLeft_projection :
    centralFixedLeft W x y a ≫ FixedEdgeTriangle.leftTriangleProjection W y x a =
      centralTriangleLeft W x y a := by
  unfold centralFixedLeft
  exact IsPullback.lift_fst _ _ _ _

@[reassoc (attr := simp)]
private theorem centralFixedRight_projection :
    centralFixedRight W x y a ≫ FixedEdgeTriangle.rightTriangleProjection W y x a =
      centralTriangleRight W x y a := by
  unfold centralFixedRight
  exact IsPullback.lift_fst _ _ _ _

private theorem centralFixedLeft_middle :
    centralFixedLeft W x y a ≫ InverseTriangle.leftMiddle W y x a =
      centralPoint W x y a ≫ InverseTriangle.identityPoint W x := by
  unfold InverseTriangle.leftMiddle
  rw [← Category.assoc, centralFixedLeft_projection, centralTriangleLeft_middle]

private theorem centralFixedRight_middle :
    centralFixedRight W x y a ≫ InverseTriangle.rightMiddle W y x a =
      centralPoint W x y a ≫ InverseTriangle.identityPoint W y := by
  unfold InverseTriangle.rightMiddle
  rw [← Category.assoc, centralFixedRight_projection, centralTriangleRight_middle]

/-- The original left strict inverse triangle extracted from the central fibre. -/
def centralLeft : centralFibre W x y a ⟶ InverseTriangle.leftSpace W y x a :=
  (InverseTriangle.left_isPullback W y x a).lift (centralFixedLeft W x y a)
    (centralPoint W x y a) (centralFixedLeft_middle W x y a)

/-- The original right strict inverse triangle, with its independent exterior edge. -/
def centralRight : centralFibre W x y a ⟶ InverseTriangle.rightSpace W y x a :=
  (InverseTriangle.right_isPullback W y x a).lift (centralFixedRight W x y a)
    (centralPoint W x y a) (centralFixedRight_middle W x y a)

/-- The left strict triangle retains the original Delta0 projection. -/
@[reassoc (attr := simp)]
theorem centralLeft_point :
    centralLeft W x y a ≫ InverseTriangle.leftToPoint W y x a = centralPoint W x y a := by
  unfold centralLeft
  exact IsPullback.lift_snd _ _ _ _

/-- The right strict triangle retains the same original Delta0 projection. -/
@[reassoc (attr := simp)]
theorem centralRight_point :
    centralRight W x y a ≫ InverseTriangle.rightToPoint W y x a = centralPoint W x y a := by
  unfold centralRight
  exact IsPullback.lift_snd _ _ _ _

/-- The left triangle retains precisely the original delta3 face. -/
@[reassoc (attr := simp)]
theorem centralLeft_projection :
    centralLeft W x y a ≫ InverseTriangle.leftTriangle W y x a ≫
      triangleProjection W x y x =
        centralProjection W x y a ≫ toThree W ≫ W.diagram.δ (3 : Fin 4) := by
  have h : centralLeft W x y a ≫ InverseTriangle.leftToFixed W y x a =
      centralFixedLeft W x y a := by
    unfold centralLeft
    exact IsPullback.lift_fst _ _ _ _
  calc
    centralLeft W x y a ≫ InverseTriangle.leftTriangle W y x a ≫ triangleProjection W x y x =
        (centralLeft W x y a ≫ InverseTriangle.leftToFixed W y x a) ≫
          (FixedEdgeTriangle.leftTriangleProjection W y x a ≫ triangleProjection W x y x) := by
      simp only [InverseTriangle.leftTriangle, Category.assoc]
    _ = centralFixedLeft W x y a ≫
        (FixedEdgeTriangle.leftTriangleProjection W y x a ≫ triangleProjection W x y x) := by rw [h]
    _ = _ := by
      rw [← Category.assoc, centralFixedLeft_projection, centralTriangleLeft_projection]

/-- The right triangle retains precisely the original delta0 face. -/
@[reassoc (attr := simp)]
theorem centralRight_projection :
    centralRight W x y a ≫ InverseTriangle.rightTriangle W y x a ≫
      triangleProjection W y x y =
        centralProjection W x y a ≫ toThree W ≫ W.diagram.δ (0 : Fin 4) := by
  have h : centralRight W x y a ≫ InverseTriangle.rightToFixed W y x a =
      centralFixedRight W x y a := by
    unfold centralRight
    exact IsPullback.lift_fst _ _ _ _
  calc
    centralRight W x y a ≫ InverseTriangle.rightTriangle W y x a ≫ triangleProjection W y x y =
        (centralRight W x y a ≫ InverseTriangle.rightToFixed W y x a) ≫
          (FixedEdgeTriangle.rightTriangleProjection W y x a ≫ triangleProjection W y x y) := by
      simp only [InverseTriangle.rightTriangle, Category.assoc]
    _ = centralFixedRight W x y a ≫
        (FixedEdgeTriangle.rightTriangleProjection W y x a ≫
            triangleProjection W y x y) := by rw [h]
    _ = _ := by
      rw [← Category.assoc, centralFixedRight_projection, centralTriangleRight_projection]

private def centralTetrahedron : centralFibre W x y a ⟶ AdjacentTriangle.tetrahedron W x y x y :=
  (AdjacentTriangle.comparison_isPullback W x y x y).lift
    (prod.lift (centralLeft W x y a) (centralRight W x y a) ≫ pairedToAdjacent W x y a)
    (centralProjection W x y a ≫ toThree W) (by
      apply pullback.hom_ext
      · simp only [Category.assoc, AdjacentTriangle.pairProjection_fst,
          pairedToAdjacent_left_assoc, prod.lift_fst_assoc, centralLeft_projection,
          AdjacentTriangle.rawComparison, pullback.lift_fst]
      · simp only [Category.assoc, AdjacentTriangle.pairProjection_snd,
          pairedToAdjacent_right_assoc, prod.lift_snd_assoc, centralRight_projection,
          AdjacentTriangle.rawComparison, pullback.lift_snd])

private theorem centralTetrahedron_comparison :
    centralTetrahedron W x y a ≫ AdjacentTriangle.comparison W x y x y =
      prod.lift (centralLeft W x y a) (centralRight W x y a) ≫ pairedToAdjacent W x y a := by
  unfold centralTetrahedron
  exact IsPullback.lift_fst _ _ _ _

/-- The strict central fibre maps to the whole tetrahedron and its two independent inverse
spaces. -/
def centralHom : centralFibre W x y a ⟶ coherentFibre W x y a :=
  pullback.lift (centralTetrahedron W x y a)
    (prod.lift (centralLeft W x y a) (centralRight W x y a))
    (centralTetrahedron_comparison W x y a)

/-- The forward central map retains the whole original W3 map. -/
@[reassoc (attr := simp)]
theorem centralHom_three :
    centralHom W x y a ≫ coherentThree W x y a = centralProjection W x y a ≫ toThree W := by
  have h : centralHom W x y a ≫ pullback.fst _ _ = centralTetrahedron W x y a := by
    unfold centralHom
    exact pullback.lift_fst _ _ _
  calc
    centralHom W x y a ≫ coherentThree W x y a =
        (centralHom W x y a ≫ pullback.fst _ _) ≫
          AdjacentTriangle.tetrahedronProjection W x y x y := by rw [coherentThree, Category.assoc]
    _ = centralTetrahedron W x y a ≫ AdjacentTriangle.tetrahedronProjection W x y x y := by rw [h]
    _ = _ := by
      unfold centralTetrahedron
      exact IsPullback.lift_snd _ _ _ _

/-- The forward central map retains the original left strict inverse triangle. -/
@[reassoc (attr := simp)]
theorem centralHom_left :
    centralHom W x y a ≫ coherentLeft W x y a = centralLeft W x y a := by
  unfold centralHom coherentLeft
  rw [← Category.assoc, pullback.lift_snd, prod.lift_fst]

/-- The forward central map retains the independent right strict inverse triangle. -/
@[reassoc (attr := simp)]
theorem centralHom_right :
    centralHom W x y a ≫ coherentRight W x y a = centralRight W x y a := by
  unfold centralHom coherentRight
  rw [← Category.assoc, pullback.lift_snd, prod.lift_snd]

/-- Both strict pullbacks retain the same original Delta0 point. -/
@[reassoc (attr := simp)]
theorem centralHom_point :
    centralHom W x y a ≫ coherentPoint W x y a = centralPoint W x y a := by
  have h := congrArg (fun f => f ≫ InverseTriangle.leftToPoint W y x a)
    (centralHom_left W x y a)
  simpa only [coherentPoint, coherentLeft, InverseTriangle.pairedToPoint,
    Category.assoc] using h.trans (centralLeft_point W x y a)

private theorem pointMono {Z : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ Z) : Mono p := by
  let _ : IsSplitMono p := IsTerminal.isSplitMono_from SSet.stdSimplex.isTerminalObj₀ p
  infer_instance

private theorem fibreProjectionMono (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) : Mono (mappingFibre.fst W x y) := by
  let _ : Mono (mappingPointPair W x y) := pointMono _
  change Mono (pullback.fst (mappingEndpoint W) (mappingPointPair W x y))
  infer_instance

private theorem twoEdgePairMono (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) : Mono (twoEdgePair W x y z) := by
  let _ := fibreProjectionMono W x y
  let _ := fibreProjectionMono W y z
  refine ⟨fun {T} f g h => ?_⟩
  apply prod.hom_ext
  · apply (cancel_mono (mappingFibre.fst W x y)).mp
    have ht := congrArg (fun k => k ≫ pullback.fst _ _) h
    simpa only [Category.assoc, twoEdgePair_fst] using ht
  · apply (cancel_mono (mappingFibre.fst W y z)).mp
    have ht := congrArg (fun k => k ≫ pullback.snd _ _) h
    simpa only [Category.assoc, twoEdgePair_snd] using ht

private theorem leftRawMono :
    Mono (InverseTriangle.leftTriangle W y x a ≫ triangleProjection W x y x) := by
  let _ : Mono (FixedEdgeTriangle.leftPair W y x a) := by
    refine ⟨fun {T} f g h => ?_⟩
    have ht := congrArg (fun k => k ≫ prod.fst) h
    simpa only [Category.assoc, (FixedEdgeTriangle.leftPairLaws W y x a).1,
      Category.comp_id] using ht
  let _ := twoEdgePairMono W x y x
  let _ : Mono (InverseTriangle.identityPoint W x) := pointMono _
  let _ : Mono (InverseTriangle.leftToFixed W y x a) := by
    change Mono (pullback.fst _ _)
    infer_instance
  let _ : Mono (FixedEdgeTriangle.leftTriangleProjection W y x a) := by
    change Mono (pullback.fst _ _)
    infer_instance
  let _ : Mono (triangleProjection W x y x) := by
    change Mono (pullback.fst _ _)
    infer_instance
  unfold InverseTriangle.leftTriangle
  infer_instance

private theorem rightRawMono :
    Mono (InverseTriangle.rightTriangle W y x a ≫ triangleProjection W y x y) := by
  let _ : Mono (FixedEdgeTriangle.rightPair W y x a) := by
    refine ⟨fun {T} f g h => ?_⟩
    have ht := congrArg (fun k => k ≫ prod.snd) h
    simpa only [Category.assoc, (FixedEdgeTriangle.rightPairLaws W y x a).2,
      Category.comp_id] using ht
  let _ := twoEdgePairMono W y x y
  let _ : Mono (InverseTriangle.identityPoint W y) := pointMono _
  let _ : Mono (InverseTriangle.rightToFixed W y x a) := by
    change Mono (pullback.fst _ _)
    infer_instance
  let _ : Mono (FixedEdgeTriangle.rightTriangleProjection W y x a) := by
    change Mono (pullback.fst _ _)
    infer_instance
  let _ : Mono (triangleProjection W y x y) := by
    change Mono (pullback.fst _ _)
    infer_instance
  unfold InverseTriangle.rightTriangle
  infer_instance

private theorem coherentThreeMono : Mono (coherentThree W x y a) := by
  let _ := leftRawMono W x y a
  let _ := rightRawMono W x y a
  refine ⟨fun {T} f g h => ?_⟩
  have hp : f ≫ (pullback.snd _ _ : coherentFibre W x y a ⟶ _) = g ≫ pullback.snd _ _ := by
    apply prod.hom_ext
    · apply (cancel_mono (InverseTriangle.leftTriangle W y x a ≫
        triangleProjection W x y x)).mp
      have ht := congrArg (fun k => k ≫ W.diagram.δ (3 : Fin 4)) h
      simpa only [Category.assoc, coherent_face012] using ht
    · apply (cancel_mono (InverseTriangle.rightTriangle W y x a ≫
        triangleProjection W y x y)).mp
      have ht := congrArg (fun k => k ≫ W.diagram.δ (0 : Fin 4)) h
      simpa only [Category.assoc, coherent_face123] using ht
  apply pullback.hom_ext
  · apply (AdjacentTriangle.comparison_isPullback W x y x y).hom_ext
    · have hc := pullback.condition (f := AdjacentTriangle.comparison W x y x y)
        (g := pairedToAdjacent W x y a)
      calc
        (f ≫ pullback.fst _ _) ≫ AdjacentTriangle.comparison W x y x y =
            (f ≫ pullback.snd _ _) ≫ pairedToAdjacent W x y a := by
          simpa only [Category.assoc] using congrArg (fun k => f ≫ k) hc
        _ = (g ≫ pullback.snd _ _) ≫ pairedToAdjacent W x y a := by rw [hp]
        _ = (g ≫ pullback.fst _ _) ≫ AdjacentTriangle.comparison W x y x y := by
          simpa only [Category.assoc] using (congrArg (fun k => g ≫ k) hc).symm
    · simpa only [coherentThree, Category.assoc] using h
  · exact hp

/-- The strict central fibre is the full coherent pullback, retaining both inverse triangles. -/
def centralIso : centralFibre W x y a ≅ coherentFibre W x y a where
  hom := centralHom W x y a
  inv := centralInv W x y a
  hom_inv_id := by
    apply pullback.hom_ext
    · apply mapping_hom_ext W
      · simp only [Category.assoc, centralInv_projection, coherentToMapping_three,
          centralHom_three, Category.id_comp]
      · simp only [Category.assoc, centralInv_projection, coherentToMapping_first,
          centralHom_point_assoc, Category.id_comp]
        exact (centralFirst W x y a).symm
      · simp only [Category.assoc, centralInv_projection, coherentToMapping_last,
          centralHom_point_assoc, Category.id_comp]
        exact (centralLast W x y a).symm
    · simp only [Category.assoc, centralInv_point, centralHom_point, Category.id_comp]
  inv_hom_id := by
    let _ := coherentThreeMono W x y a
    apply (cancel_mono (coherentThree W x y a)).mp
    simp only [Category.assoc, centralHom_three, centralInv_projection_assoc,
      coherentToMapping_three, Category.id_comp]

/-- The actual first-point inclusion through both original pushouts. -/
def firstInclusion : SSet.Rezk.representable.{u} 0 ⟶ K :=
  stage1Cocone.inl ≫ stage2Cocone.inl

/-- The actual whole three-simplex inclusion through both original pushouts. -/
def threeInclusion : SSet.Rezk.representable.{u} 3 ⟶ K :=
  stage1Cocone.inr ≫ stage2Cocone.inl

/-- The actual last-point inclusion into the second original pushout. -/
def lastInclusion : SSet.Rezk.representable.{u} 0 ⟶ K := stage2Cocone.inr

/-- The actual central12 inclusion into the same original K. -/
def centralInclusion : SSet.Rezk.representable.{u} 1 ⟶ K :=
  SSet.simplicialSpaceDiscrete.map
    (SSet.stdSimplex.map (SimplexCategory.mkOfLe (1 : Fin 4) 2 (by decide))) ≫ threeInclusion

/-- The first map is precisely restriction along the original first inclusion. -/
theorem toFirst_restriction : toFirst W =
    restriction W firstInclusion ≫ (representableMappingIso W 0).hom := by
  rw [firstInclusion, restriction_comp]
  rfl

/-- The whole W3 map is precisely restriction along the original three-simplex. -/
theorem toThree_restriction : toThree W =
    restriction W threeInclusion ≫ (representableMappingIso W 3).hom := by
  rw [threeInclusion, restriction_comp]
  rfl

/-- The last map is precisely restriction along the original last inclusion. -/
theorem toLast_restriction : toLast W =
    restriction W lastInclusion ≫ (representableMappingIso W 0).hom := rfl

/-- The central map is precisely restriction along the original central12 inclusion. -/
theorem toCentral_restriction : toCentral W =
    restriction W centralInclusion ≫ (representableMappingIso W 1).hom := by
  rw [centralInclusion, restriction_comp, Category.assoc,
    representableMappingIso_naturality, ← Category.assoc, ← toThree_restriction]
  rfl

/-- The natural transformation induced by an actual original target map. -/
def rawMappingNat {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    mappingFunctor W ⟶ mappingFunctor V :=
  Functor.whiskerLeft ofSimplicialObject.op (innerHomFunctor.flip.map q)

/-- The original K mapping map, with the original target morphism. -/
abbrev mappingMap {W V : SimplicialSpace.{u}} (q : W ⟶ V) : mapping W ⟶ mapping V :=
  (rawMappingNat q).app (op K)

/-- Original restriction and target maps commute before any representation change. -/
@[reassoc]
theorem restriction_naturality {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    {A B : SimplicialObject SSet.{u}} (f : A ⟶ B) :
    (rawMappingNat q).app (op B) ≫ restriction V f =
      restriction W f ≫ (rawMappingNat q).app (op A) :=
  ((rawMappingNat q).naturality f.op).symm

/-- The original represented comparison retains the target-map equation. -/
@[reassoc]
theorem representableMappingIso_target {W V : SimplicialSpace.{u}} (q : W ⟶ V) (n : ℕ) :
    (rawMappingNat q).app (op (SSet.Rezk.representable n)) ≫
      (representableMappingIso V n).hom =
        (representableMappingIso W n).hom ≫ q.hom.app (op ⦋n⦌) :=
  discreteYonedaIso_naturality_target q n

/-- The original target map retains the first collapsed point. -/
@[reassoc]
theorem mappingMap_first {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    mappingMap q ≫ toFirst V = toFirst W ≫ q.hom.app (op ⦋0⦌) := by
  rw [toFirst_restriction, ← Category.assoc, restriction_naturality,
    Category.assoc, representableMappingIso_target, ← Category.assoc, ← toFirst_restriction]

/-- The original target map retains the whole three-simplex. -/
@[reassoc]
theorem mappingMap_three {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    mappingMap q ≫ toThree V = toThree W ≫ q.hom.app (op ⦋3⦌) := by
  rw [toThree_restriction, ← Category.assoc, restriction_naturality,
    Category.assoc, representableMappingIso_target, ← Category.assoc, ← toThree_restriction]

/-- The original target map retains the last collapsed point. -/
@[reassoc]
theorem mappingMap_last {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    mappingMap q ≫ toLast V = toLast W ≫ q.hom.app (op ⦋0⦌) := by
  rw [toLast_restriction, ← Category.assoc, restriction_naturality,
    Category.assoc, representableMappingIso_target, ← Category.assoc, ← toLast_restriction]

/-- The same actual target map retains the original central12 edge. -/
@[reassoc]
theorem mappingMap_central {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    mappingMap q ≫ toCentral V = toCentral W ≫ q.hom.app (op ⦋1⦌) := by
  rw [toCentral_restriction, ← Category.assoc, restriction_naturality,
    Category.assoc, representableMappingIso_target, ← Category.assoc, ← toCentral_restriction]

/-- The actual target map of the first original inverse-edge pullback. -/
def inversePairMap {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    inversePairLimit W ⟶ inversePairLimit V :=
  pullback.map (W.diagram.δ (0 : Fin 2)) (W.diagram.δ (0 : Fin 2))
    (V.diagram.δ (0 : Fin 2)) (V.diagram.δ (0 : Fin 2))
    (q.hom.app (op ⦋1⦌)) (q.hom.app (op ⦋1⦌)) (q.hom.app (op ⦋0⦌))
    (q.hom.naturality (SimplexCategory.δ (0 : Fin 2)).op)
    (q.hom.naturality (SimplexCategory.δ (0 : Fin 2)).op)

/-- The inverse-pair target map retains its first edge. -/
@[reassoc (attr := simp)]
theorem inversePairMap_first {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    inversePairMap q ≫ pullback.fst _ _ = pullback.fst _ _ ≫ q.hom.app (op ⦋1⦌) :=
  pullback.lift_fst _ _ _

/-- The inverse-pair target map retains its second edge. -/
@[reassoc (attr := simp)]
theorem inversePairMap_second {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    inversePairMap q ≫ pullback.snd _ _ = pullback.snd _ _ ≫ q.hom.app (op ⦋1⦌) :=
  pullback.lift_snd _ _ _

/-- The actual target map of the whole original02/12/13 inverse-edge limit. -/
def inverseEdgeMap {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    inverseEdgeLimit W ⟶ inverseEdgeLimit V :=
  pullback.map (pullback.snd _ _ ≫ W.diagram.δ (1 : Fin 2)) (W.diagram.δ (1 : Fin 2))
    (pullback.snd _ _ ≫ V.diagram.δ (1 : Fin 2)) (V.diagram.δ (1 : Fin 2))
    (inversePairMap q) (q.hom.app (op ⦋1⦌)) (q.hom.app (op ⦋0⦌))
    (by
      have hn : W.diagram.δ (1 : Fin 2) ≫ q.hom.app (op ⦋0⦌) =
          q.hom.app (op ⦋1⦌) ≫ V.diagram.δ (1 : Fin 2) :=
        q.hom.naturality (SimplexCategory.δ (1 : Fin 2)).op
      calc
        (pullback.snd _ _ ≫ W.diagram.δ (1 : Fin 2)) ≫ q.hom.app (op ⦋0⦌) =
            pullback.snd _ _ ≫ q.hom.app (op ⦋1⦌) ≫ V.diagram.δ (1 : Fin 2) := by
          rw [Category.assoc, hn]
        _ = inversePairMap q ≫ (pullback.snd _ _ ≫ V.diagram.δ (1 : Fin 2)) := by
          simpa only [Category.assoc] using
            (congrArg (fun f => f ≫ V.diagram.δ (1 : Fin 2)) (inversePairMap_second q)).symm)
    (q.hom.naturality (SimplexCategory.δ (1 : Fin 2)).op)

/-- The whole inverse-edge target map retains the original02 projection. -/
@[reassoc (attr := simp)]
theorem inverseEdgeMap_first {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    inverseEdgeMap q ≫ inverseFirst V = inverseFirst W ≫ q.hom.app (op ⦋1⦌) := by
  unfold inverseEdgeMap inverseFirst
  rw [← Category.assoc, pullback.lift_fst]
  simp only [Category.assoc, inversePairMap_first]

/-- The whole inverse-edge target map retains the original12 projection. -/
@[reassoc (attr := simp)]
theorem inverseEdgeMap_middle {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    inverseEdgeMap q ≫ inverseMiddle V = inverseMiddle W ≫ q.hom.app (op ⦋1⦌) := by
  unfold inverseEdgeMap inverseMiddle
  rw [← Category.assoc, pullback.lift_fst]
  simp only [Category.assoc, inversePairMap_second]

/-- The whole inverse-edge target map retains the original13 projection. -/
@[reassoc (attr := simp)]
theorem inverseEdgeMap_last {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    inverseEdgeMap q ≫ inverseLast V = inverseLast W ≫ q.hom.app (op ⦋1⦌) :=
  pullback.lift_snd _ _ _

private theorem inverseEdge_hom_ext (W : SimplicialSpace.{u}) {T : SSet.{u}}
    {f g : T ⟶ inverseEdgeLimit W}
    (h₀ : f ≫ inverseFirst W = g ≫ inverseFirst W)
    (h₁ : f ≫ inverseMiddle W = g ≫ inverseMiddle W)
    (h₂ : f ≫ inverseLast W = g ≫ inverseLast W) : f = g := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · exact h₀
    · exact h₁
  · exact h₂

/-- The original three-simplex inverse restriction commutes with actual target maps. -/
@[reassoc]
theorem inverseRestriction_naturality {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    inverseRestriction W ≫ inverseEdgeMap q = q.hom.app (op ⦋3⦌) ≫ inverseRestriction V := by
  apply inverseEdge_hom_ext V
  · simp only [Category.assoc, inverseEdgeMap_first, inverseRestriction_first_assoc,
      inverseRestriction_first]
    exact q.hom.naturality (SimplexCategory.mkOfLe (0 : Fin 4) 2 (by decide)).op
  · simp only [Category.assoc, inverseEdgeMap_middle, inverseRestriction_middle_assoc,
      inverseRestriction_middle]
    exact q.hom.naturality (SimplexCategory.mkOfLe (1 : Fin 4) 2 (by decide)).op
  · simp only [Category.assoc, inverseEdgeMap_last, inverseRestriction_last_assoc,
      inverseRestriction_last]
    exact q.hom.naturality (SimplexCategory.mkOfLe (1 : Fin 4) 3 (by decide)).op

/-- The original identity triple commutes with actual target maps. -/
@[reassoc]
theorem identityTriple_naturality {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    identityTriple W ≫ inverseEdgeMap q = q.hom.app (op ⦋1⦌) ≫ identityTriple V := by
  apply inverseEdge_hom_ext V
  · simp only [Category.assoc, inverseEdgeMap_first, identityTriple_first_assoc,
      identityTriple_first]
    have hs : W.diagram.σ (0 : Fin 1) ≫ q.hom.app (op ⦋1⦌) =
        q.hom.app (op ⦋0⦌) ≫ V.diagram.σ (0 : Fin 1) :=
      q.hom.naturality (SimplexCategory.σ (0 : Fin 1)).op
    have hd : W.diagram.δ (0 : Fin 2) ≫ q.hom.app (op ⦋0⦌) =
        q.hom.app (op ⦋1⦌) ≫ V.diagram.δ (0 : Fin 2) :=
      q.hom.naturality (SimplexCategory.δ (0 : Fin 2)).op
    rw [hs, ← Category.assoc, hd, Category.assoc]
  · simp only [Category.assoc, inverseEdgeMap_middle, identityTriple_middle_assoc,
      identityTriple_middle,
      Category.comp_id]
  · simp only [Category.assoc, inverseEdgeMap_last, identityTriple_last_assoc, identityTriple_last]
    have hs : W.diagram.σ (0 : Fin 1) ≫ q.hom.app (op ⦋1⦌) =
        q.hom.app (op ⦋0⦌) ≫ V.diagram.σ (0 : Fin 1) :=
      q.hom.naturality (SimplexCategory.σ (0 : Fin 1)).op
    have hd : W.diagram.δ (1 : Fin 2) ≫ q.hom.app (op ⦋0⦌) =
        q.hom.app (op ⦋1⦌) ≫ V.diagram.δ (1 : Fin 2) :=
      q.hom.naturality (SimplexCategory.δ (1 : Fin 2)).op
    rw [hs, ← Category.assoc, hd, Category.assoc]

/-- The actual chosen inverse-test pullback map, with its original W3 and W1 maps. -/
def inverseTestMap {W V : SimplicialSpace.{u}} (q : W ⟶ V) : inverseTest W ⟶ inverseTest V :=
  pullback.map (inverseRestriction W) (identityTriple W)
    (inverseRestriction V) (identityTriple V)
    (q.hom.app (op ⦋3⦌)) (q.hom.app (op ⦋1⦌)) (inverseEdgeMap q)
    (inverseRestriction_naturality q) (identityTriple_naturality q)

/-- The actual inverse-test target map retains the whole W3 projection. -/
@[reassoc (attr := simp)]
theorem inverseTestMap_three {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    inverseTestMap q ≫ pullback.fst _ _ = pullback.fst _ _ ≫ q.hom.app (op ⦋3⦌) :=
  pullback.lift_fst _ _ _

/-- The actual inverse-test target map retains the original central12 projection. -/
@[reassoc (attr := simp)]
theorem inverseTestMap_central {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    inverseTestMap q ≫ pullback.snd _ _ = pullback.snd _ _ ≫ q.hom.app (op ⦋1⦌) :=
  pullback.lift_snd _ _ _

/-- Both original inverse-test isomorphism projections commute with actual target maps. -/
@[reassoc]
theorem inverseTestIso_hom_naturality {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    mappingMap q ≫ (inverseTestIso V).hom = (inverseTestIso W).hom ≫ inverseTestMap q := by
  apply pullback.hom_ext
  · simp only [Category.assoc, inverseTestIso, inverseTestHom_three, inverseTestMap_three,
      inverseTestHom_three_assoc, mappingMap_three]
  · simp only [Category.assoc, inverseTestIso, inverseTestHom_central, inverseTestMap_central,
      inverseTestHom_central_assoc, mappingMap_central]

/-- The reverse original inverse-test map retains the same target naturality square. -/
@[reassoc]
theorem inverseTestIso_inv_naturality {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    inverseTestMap q ≫ (inverseTestIso V).inv = (inverseTestIso W).inv ≫ mappingMap q := by
  apply (cancel_epi (inverseTestIso W).hom).mp
  have h := congrArg (fun f => f ≫ (inverseTestIso V).inv) (inverseTestIso_hom_naturality q)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc] using h.symm

section PointedTransport

variable {W V : SimplicialSpace.{u}} (q : W ⟶ V)
  {x y : (W.diagram _⦋0⦌) _⦋0⦌} {x' y' : (V.diagram _⦋0⦌) _⦋0⦌}
  {a : (mappingFibre W y x) _⦋0⦌} {a' : (mappingFibre V y' x') _⦋0⦌}
  (hx : mappingVertexMap q x = x') (hy : mappingVertexMap q y = y')
  (ha : (mappingFibre.map q hy hx).app (op ⦋0⦌) a = a')

include ha in
/-- The same original prescribed point moves by its actual mapping-fibre map. -/
@[reassoc]
theorem prescribedPoint_naturality :
    SSet.yonedaEquiv.symm a ≫ mappingFibre.map q hy hx = SSet.yonedaEquiv.symm a' := by
  rw [SSet.yonedaEquiv_symm_comp, ha]

/-- The actual target map of the same strict original central fibre. -/
def centralFibreMap : centralFibre W x y a ⟶ centralFibre V x' y' a' :=
  pullback.map (toCentral W) (SSet.yonedaEquiv.symm a ≫ mappingFibre.fst W y x)
    (toCentral V) (SSet.yonedaEquiv.symm a' ≫ mappingFibre.fst V y' x')
    (mappingMap q) (𝟙 _) (q.hom.app (op ⦋1⦌)) (mappingMap_central q).symm (by
      calc
        (SSet.yonedaEquiv.symm a ≫ mappingFibre.fst W y x) ≫ q.hom.app (op ⦋1⦌) =
            SSet.yonedaEquiv.symm a ≫ mappingFibre.map q hy hx ≫ mappingFibre.fst V y' x' := by
          rw [Category.assoc, mappingFibre.map_fst]
        _ = SSet.yonedaEquiv.symm a' ≫ mappingFibre.fst V y' x' := by
          rw [← Category.assoc, prescribedPoint_naturality q hx hy ha]
        _ = (𝟙 _) ≫ (SSet.yonedaEquiv.symm a' ≫ mappingFibre.fst V y' x') := by
          rw [Category.id_comp])

/-- The actual central-fibre target map retains the whole original K map. -/
@[reassoc (attr := simp)]
theorem centralFibreMap_projection :
    centralFibreMap q hx hy ha ≫ centralProjection V x' y' a' =
      centralProjection W x y a ≫ mappingMap q := pullback.lift_fst _ _ _

/-- The actual central-fibre target map keeps the original Delta0 point. -/
@[reassoc (attr := simp)]
theorem centralFibreMap_point :
    centralFibreMap q hx hy ha ≫ centralPoint V x' y' a' = centralPoint W x y a := by
  unfold centralFibreMap
  rw [pullback.lift_snd, Category.comp_id]

/-- The independent inverse triangles move into the same original adjacent pair. -/
@[reassoc]
theorem pairedToAdjacent_naturality :
    InverseTriangle.pairedMap q hy hx ha ≫ pairedToAdjacent V x' y' a' =
      pairedToAdjacent W x y a ≫ AdjacentTriangle.pairMap q hx hy hx hy := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pairedToAdjacent_left, InverseTriangle.pairedMap_left_assoc,
      InverseTriangle.leftMap_triangle, AdjacentTriangle.pairMap012, pairedToAdjacent_left_assoc]
  · simp only [Category.assoc, pairedToAdjacent_right, InverseTriangle.pairedMap_right_assoc,
      InverseTriangle.rightMap_triangle, AdjacentTriangle.pairMap123, pairedToAdjacent_right_assoc]

/-- The actual original coherent target map retains both the tetrahedron and independent pair. -/
def coherentFibreMap : coherentFibre W x y a ⟶ coherentFibre V x' y' a' :=
  pullback.map (AdjacentTriangle.comparison W x y x y) (pairedToAdjacent W x y a)
    (AdjacentTriangle.comparison V x' y' x' y') (pairedToAdjacent V x' y' a')
    (AdjacentTriangle.tetrahedronMap q hx hy hx hy) (InverseTriangle.pairedMap q hy hx ha)
    (AdjacentTriangle.pairMap q hx hy hx hy)
    (AdjacentTriangle.comparison_naturality q hx hy hx hy).symm
    (pairedToAdjacent_naturality q hx hy ha).symm

/-- The coherent target map retains the whole original W3 map. -/
@[reassoc (attr := simp)]
theorem coherentFibreMap_three :
    coherentFibreMap q hx hy ha ≫ coherentThree V x' y' a' =
      coherentThree W x y a ≫ q.hom.app (op ⦋3⦌) := by
  unfold coherentFibreMap coherentThree
  rw [← Category.assoc, pullback.lift_fst]
  simp only [Category.assoc, AdjacentTriangle.tetrahedronMap_projection]

/-- The coherent target map preserves its whole original left inverse-space leg. -/
@[reassoc (attr := simp)]
theorem coherentFibreMap_left :
    coherentFibreMap q hx hy ha ≫ coherentLeft V x' y' a' =
      coherentLeft W x y a ≫ InverseTriangle.leftMap q hy hx ha := by
  unfold coherentFibreMap coherentLeft
  rw [← Category.assoc, pullback.lift_snd]
  simp only [Category.assoc, InverseTriangle.pairedMap_left]

/-- The coherent target map preserves its independent original right inverse-space leg. -/
@[reassoc (attr := simp)]
theorem coherentFibreMap_right :
    coherentFibreMap q hx hy ha ≫ coherentRight V x' y' a' =
      coherentRight W x y a ≫ InverseTriangle.rightMap q hy hx ha := by
  unfold coherentFibreMap coherentRight
  rw [← Category.assoc, pullback.lift_snd]
  simp only [Category.assoc, InverseTriangle.pairedMap_right]

/-- The coherent target map retains the same original Delta0 point. -/
@[reassoc (attr := simp)]
theorem coherentFibreMap_point :
    coherentFibreMap q hx hy ha ≫ coherentPoint V x' y' a' = coherentPoint W x y a := by
  unfold coherentFibreMap coherentPoint
  rw [← Category.assoc, pullback.lift_snd]
  simp only [Category.assoc, InverseTriangle.pairedMap_point]

/-- The forward strict central isomorphism commutes with actual original target maps. -/
@[reassoc]
theorem centralIso_hom_naturality :
    centralFibreMap q hx hy ha ≫ (centralIso V x' y' a').hom =
      (centralIso W x y a).hom ≫ coherentFibreMap q hx hy ha := by
  let _ := coherentThreeMono V x' y' a'
  apply (cancel_mono (coherentThree V x' y' a')).mp
  simp only [Category.assoc, centralIso, centralHom_three, centralFibreMap_projection_assoc,
    mappingMap_three, coherentFibreMap_three, centralHom_three_assoc]

/-- The reverse strict central isomorphism retains the same original target-map square. -/
@[reassoc]
theorem centralIso_inv_naturality :
    coherentFibreMap q hx hy ha ≫ (centralIso V x' y' a').inv =
      (centralIso W x y a).inv ≫ centralFibreMap q hx hy ha := by
  apply (cancel_epi (centralIso W x y a).hom).mp
  have h := congrArg (fun f => f ≫ (centralIso V x' y' a').inv)
    (centralIso_hom_naturality q hx hy ha)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc] using h.symm

end PointedTransport

/-- The reverse isomorphism retains the same original left inverse triangle. -/
@[reassoc]
theorem centralIso_inv_left :
    (centralIso W x y a).inv ≫ centralLeft W x y a = coherentLeft W x y a := by
  apply (cancel_epi (centralIso W x y a).hom).mp
  rw [Iso.hom_inv_id_assoc]
  exact (centralHom_left W x y a).symm

/-- The reverse isomorphism retains the independent original right inverse triangle. -/
@[reassoc]
theorem centralIso_inv_right :
    (centralIso W x y a).inv ≫ centralRight W x y a = coherentRight W x y a := by
  apply (cancel_epi (centralIso W x y a).hom).mp
  rw [Iso.hom_inv_id_assoc]
  exact (centralHom_right W x y a).symm

/-- Every original simplex operator commutes with both central isomorphism directions. -/
theorem centralIso_operators {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n) :
    (centralFibre W x y a).map f ≫ (centralIso W x y a).hom.app n =
        (centralIso W x y a).hom.app m ≫ (coherentFibre W x y a).map f ∧
      (coherentFibre W x y a).map f ≫ (centralIso W x y a).inv.app n =
        (centralIso W x y a).inv.app m ≫ (centralFibre W x y a).map f :=
  ⟨(centralIso W x y a).hom.naturality f, (centralIso W x y a).inv.naturality f⟩

/-- Every original simplex operator commutes with both whole inverse-test directions. -/
theorem inverseTestIso_operators (W : SimplicialSpace.{u})
    {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n) :
    (mapping W).map f ≫ (inverseTestIso W).hom.app n =
        (inverseTestIso W).hom.app m ≫ (inverseTest W).map f ∧
      (inverseTest W).map f ≫ (inverseTestIso W).inv.app n =
        (inverseTestIso W).inv.app m ≫ (mapping W).map f :=
  ⟨(inverseTestIso W).hom.naturality f, (inverseTestIso W).inv.naturality f⟩

/-- The native universal K lift commutes with every original parameter precomposition. -/
theorem mappingLift_precomp (W : SimplicialSpace.{u}) {T U : SSet.{u}}
    (k : U ⟶ T) (t : T ⟶ W.diagram _⦋3⦌) (p₀ p₁ : T ⟶ W.diagram _⦋0⦌) (h₀ h₁) :
    mappingLift W (k ≫ t) (k ≫ p₀) (k ≫ p₁)
        (by simpa only [Category.assoc] using congrArg (fun f => k ≫ f) h₀)
        (by simpa only [Category.assoc] using congrArg (fun f => k ≫ f) h₁) =
      k ≫ mappingLift W t p₀ p₁ h₀ h₁ := by
  apply mapping_hom_ext W <;>
    simp only [Category.assoc, mappingLift_three, mappingLift_first, mappingLift_last]

/-- The full consecutive triple retains b, the original a, and the independent c. -/
theorem coherentEdges_eq : coherentEdges W x y a =
    prod.lift
      (prod.lift (coherentLeft W x y a ≫ InverseTriangle.leftCandidate W y x a)
        (coherentPoint W x y a ≫ SSet.yonedaEquiv.symm a))
      (coherentRight W x y a ≫ InverseTriangle.rightCandidate W y x a) := by
  have h : coherentEdges W x y a =
      pullback.snd _ _ ≫ pairedToAdjacent W x y a ≫ AdjacentTriangle.pairEdges W x y x y := by
    have ht := congrArg (fun f => f ≫ AdjacentTriangle.pairEdges W x y x y)
      (pullback.condition (f := AdjacentTriangle.comparison W x y x y)
        (g := pairedToAdjacent W x y a))
    simpa only [coherentEdges, Category.assoc, AdjacentTriangle.comparison_edges] using ht
  apply prod.hom_ext
  · apply prod.hom_ext
    · rw [h]
      simp only [Category.assoc, prod.lift_fst, AdjacentTriangle.pairEdges_fst_assoc,
        pairedToAdjacent_left_assoc, InverseTriangle.left_varyingFirst]
    · rw [h]
      simp only [Category.assoc, prod.lift_fst, prod.lift_snd,
        AdjacentTriangle.pairEdges_fst_assoc, pairedToAdjacent_left_assoc,
        InverseTriangle.left_fixedLast]
      rfl
  · rw [h]
    simp only [Category.assoc, prod.lift_snd, AdjacentTriangle.pairEdges_snd,
      pairedToAdjacent_right_assoc, InverseTriangle.right_varyingLast]

/-- Every original point in every bidegree of K lies in one of its three original cocone legs. -/
theorem original_points_covered (m n : SimplexCategoryᵒᵖ) (z : (K.{u}.obj m).obj n) :
    (∃ p : ((SSet.Rezk.representable.{u} 0).obj m).obj n,
      ((firstInclusion.app m).app n) p = z) ∨
    (∃ t : ((SSet.Rezk.representable.{u} 3).obj m).obj n,
      ((threeInclusion.app m).app n) t = z) ∨
    (∃ p : ((SSet.Rezk.representable.{u} 0).obj m).obj n,
      ((lastInclusion.app m).app n) p = z) := by
  let outer := (evaluation SimplexCategoryᵒᵖ SSet.{u}).obj m
  let inner := (evaluation SimplexCategoryᵒᵖ (Type u)).obj n
  have h₁ := ((IsPushout.of_isColimit stage1IsColimit.{u}).map outer).map inner
  have h₂ := ((IsPushout.of_isColimit stage2IsColimit.{u}).map outer).map inner
  obtain ⟨s, hs⟩ | ⟨p, hp⟩ := Types.eq_or_eq_of_isPushout h₂ z
  · change ((stage2Cocone.inl.app m).app n) s = z at hs
    obtain ⟨p, hp⟩ | ⟨t, ht⟩ := Types.eq_or_eq_of_isPushout h₁ s
    · left
      refine ⟨p, ?_⟩
      change ((stage1Cocone.inl.app m).app n) p = s at hp
      change ((stage2Cocone.inl.app m).app n) (((stage1Cocone.inl.app m).app n) p) = z
      rw [hp]
      exact hs
    · right
      left
      refine ⟨t, ?_⟩
      change ((stage1Cocone.inr.app m).app n) t = s at ht
      change ((stage2Cocone.inl.app m).app n) (((stage1Cocone.inr.app m).app n) t) = z
      rw [ht]
      exact hs
  · exact Or.inr (Or.inr ⟨p, hp⟩)

private abbrev walkingAlternating : SSet.coherentIso.{u} _⦋3⦌ :=
  ComposableArrows.mk₃ WalkingIso.iso.{u}.hom WalkingIso.iso.inv WalkingIso.iso.hom

private abbrev walkingBackward : SSet.coherentIso.{u} _⦋1⦌ :=
  ComposableArrows.mk₁ WalkingIso.iso.{u}.inv

/-- The literal raw comparison sends central12 to the backward walking-isomorphism edge10. -/
theorem centralInclusion_comparison :
    centralInclusion.{u} ≫ comparison =
      SSet.simplicialSpaceDiscrete.map
        (SSet.yonedaEquiv.symm (ComposableArrows.mk₁ WalkingIso.iso.{u}.inv)) := by
  have h : SSet.stdSimplex.map (SimplexCategory.mkOfLe (1 : Fin 4) 2 (by decide)) ≫
      (SSet.yonedaEquiv.symm walkingAlternating.{u} : (Δ[3] : SSet.{u}) ⟶ SSet.coherentIso.{u}) =
      (SSet.yonedaEquiv.symm walkingBackward.{u} : (Δ[1] : SSet.{u}) ⟶ SSet.coherentIso.{u}) := by
    rw [SSet.yonedaEquiv_symm_naturality_left]
    apply congrArg SSet.yonedaEquiv.symm
    apply CategoryTheory.nerve.ext_of_isThin
    funext i
    fin_cases i <;> rfl
  unfold centralInclusion threeInclusion
  simp only [Category.assoc]
  rw [comparison_mid]
  change SSet.simplicialSpaceDiscrete.map _ ≫
      SSet.simplicialSpaceDiscrete.map (SSet.yonedaEquiv.symm walkingAlternating.{u}) =
        SSet.simplicialSpaceDiscrete.map (SSet.yonedaEquiv.symm walkingBackward.{u})
  rw [← SSet.simplicialSpaceDiscrete.map_comp, h]

end SimplicialSpace.FiniteCompletenessMapping
