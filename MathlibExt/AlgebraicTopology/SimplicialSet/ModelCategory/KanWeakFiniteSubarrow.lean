/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Order.CompleteLattice.Lemmas
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanHomotopyPullback
public import MathlibExt.CategoryTheory.SmallObject.TerminalIteration
public import MathlibExt.CategoryTheory.SmallObject.PresheafAttachmentCardinalColimits
public import MathlibExt.CategoryTheory.SmallObject.Iteration.Accessible

/-!
# Finite original subarrows and strict Kan lift descent

This helper retains the two original subcomplex inclusions and the entire
restricted arrow. Its filtered colimit is the original arrow. The scalar
completion used below is the native horn terminal iteration.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.KanWeakInterpolation

variable {X Y : SSet.{u}} (f : X ⟶ Y)

/-- The actual finite original subarrows of a simplicial-set map. -/
abbrev FiniteSubarrow : Type u :=
  { p : X.Subcomplex × Y.Subcomplex //
    SSet.Finite p.1 ∧ SSet.Finite p.2 ∧ p.1.image f ≤ p.2 }

namespace FiniteSubarrow

instance : PartialOrder (FiniteSubarrow f) := inferInstance

/-- The finite original source subcomplex of this subarrow. -/
abbrev left (j : FiniteSubarrow f) : X.Subcomplex := j.val.1
/-- The finite original target subcomplex of this subarrow. -/
abbrev right (j : FiniteSubarrow f) : Y.Subcomplex := j.val.2

instance (j : FiniteSubarrow f) : SSet.Finite (j.left f) := j.property.1
instance (j : FiniteSubarrow f) : SSet.Finite (j.right f) := j.property.2.1

theorem image_le (j : FiniteSubarrow f) : (j.left f).image f ≤ j.right f :=
  j.property.2.2

private theorem finite_bot (Z : SSet.{u}) : SSet.Finite (⊥ : Z.Subcomplex) := by
  have h : SSet.Finite (⨆ i : Empty, (fun _ => (⊥ : Z.Subcomplex)) i :) :=
    (SSet.finite_iSup_iff (fun _ : Empty => (⊥ : Z.Subcomplex))).mpr
      (fun i => nomatch i)
  simpa using h

private theorem finite_sup {Z : SSet.{u}} (A B : Z.Subcomplex)
    [SSet.Finite A] [SSet.Finite B] : SSet.Finite (A ⊔ B : Z.Subcomplex) := by
  have h : SSet.Finite (⨆ b : Bool, (if b then A else B) :) :=
    (SSet.finite_iSup_iff (fun b : Bool => if b then A else B)).mpr
      (by intro b; cases b <;> dsimp <;> infer_instance)
  simpa only [iSup_bool_eq, ite_true, Bool.false_eq_true, ite_false] using h

/-- The empty finite original subarrow, including arrows with empty endpoints. -/
@[no_expose]
def empty : FiniteSubarrow f :=
  ⟨(⊥, ⊥), finite_bot X, finite_bot Y,
    (Subcomplex.image_le_iff (⊥ : X.Subcomplex) f (⊥ : Y.Subcomplex)).mpr bot_le⟩

instance : Nonempty (FiniteSubarrow f) := ⟨empty f⟩

/-- A common finite original upper subarrow, formed by the two endpoint unions. -/
@[no_expose]
def upper (j k : FiniteSubarrow f) : FiniteSubarrow f := by
  refine ⟨(j.left f ⊔ k.left f, j.right f ⊔ k.right f),
    finite_sup _ _, finite_sup _ _, ?_⟩
  rw [Subcomplex.image_le_iff]
  apply sup_le
  · exact (Subcomplex.image_le_iff (j.left f) f _).mp
      ((j.image_le f).trans le_sup_left)
  · exact (Subcomplex.image_le_iff (k.left f) f _).mp
      ((k.image_le f).trans le_sup_right)

theorem le_upper_left (j k : FiniteSubarrow f) : j ≤ upper f j k :=
  ⟨le_sup_left, le_sup_left⟩

theorem le_upper_right (j k : FiniteSubarrow f) : k ≤ upper f j k :=
  ⟨le_sup_right, le_sup_right⟩

instance : IsDirectedOrder (FiniteSubarrow f) :=
  ⟨fun j k => ⟨upper f j k, le_upper_left f j k, le_upper_right f j k⟩⟩

instance : IsFiltered (FiniteSubarrow f) := inferInstance

/-- The original restricted map, with its original source and target. -/
def hom (j : FiniteSubarrow f) : (j.left f : SSet.{u}) ⟶ (j.right f : SSet.{u}) :=
  (j.left f).toImage f ≫ Subcomplex.homOfLE (j.image_le f)

@[reassoc (attr := simp)]
theorem hom_right_ι (j : FiniteSubarrow f) :
    j.hom f ≫ (j.right f).ι = (j.left f).ι ≫ f := by
  rw [hom, Category.assoc, Subcomplex.homOfLE_ι, Subcomplex.toImage_ι]

/-- The diagram of finite original source subcomplexes and their inclusion maps. -/
def leftDiagram : FiniteSubarrow f ⥤ SSet.{u} where
  obj j := j.left f
  map h := Subcomplex.homOfLE (leOfHom h).1
  map_id j := Subcomplex.homOfLE_refl (j.left f)
  map_comp _h _k := rfl

/-- The diagram of finite original target subcomplexes and their inclusion maps. -/
def rightDiagram : FiniteSubarrow f ⥤ SSet.{u} where
  obj j := j.right f
  map h := Subcomplex.homOfLE (leOfHom h).2
  map_id j := Subcomplex.homOfLE_refl (j.right f)
  map_comp _h _k := rfl

/-- The natural transformation of literal restrictions of the original arrow. -/
def originalArrow : leftDiagram f ⟶ rightDiagram f where
  app j := j.hom f
  naturality j k h := by
    apply (cancel_mono (k.right f).ι).mp
    change (Subcomplex.homOfLE (leOfHom h).1 ≫ k.hom f) ≫ (k.right f).ι =
      (j.hom f ≫ Subcomplex.homOfLE (leOfHom h).2) ≫ (k.right f).ι
    rw [Category.assoc, hom_right_ι, ← Category.assoc, Subcomplex.homOfLE_ι,
      Category.assoc, Subcomplex.homOfLE_ι, hom_right_ι]

/-- The original source inclusion cocone with the original source as its point. -/
def leftCocone : Cocone (leftDiagram f) where
  pt := X
  ι :=
    { app j := (j.left f).ι
      naturality j k h := by
        change Subcomplex.homOfLE (leOfHom h).1 ≫ (k.left f).ι = (j.left f).ι ≫ 𝟙 X
        rw [Subcomplex.homOfLE_ι, Category.comp_id] }

/-- The original target inclusion cocone with the original target as its point. -/
def rightCocone : Cocone (rightDiagram f) where
  pt := Y
  ι :=
    { app j := (j.right f).ι
      naturality j k h := by
        change Subcomplex.homOfLE (leOfHom h).2 ≫ (k.right f).ι = (j.right f).ι ≫ 𝟙 Y
        rw [Subcomplex.homOfLE_ι, Category.comp_id] }

@[reassoc]
theorem originalArrow_cocone (j : FiniteSubarrow f) :
    (leftCocone f).ι.app j ≫ f = (originalArrow f).app j ≫ (rightCocone f).ι.app j :=
  (hom_right_ι f j).symm

/-- The finite original subarrow generated by a source simplex and its image. -/
def ofLeftSimplex {n : ℕ} (x : X _⦋n⦌) : FiniteSubarrow f := by
  let U := Subcomplex.ofSimplex x
  have : SSet.Finite (U.image f) := by
    rw [Subcomplex.image_eq_range]
    infer_instance
  exact ⟨(U, U.image f), inferInstance, inferInstance, le_rfl⟩

/-- A finite original subarrow containing a prescribed target simplex. -/
def ofRightSimplex {n : ℕ} (y : Y _⦋n⦌) : FiniteSubarrow f := by
  have hbot : SSet.Finite (⊥ : X.Subcomplex) := by
    have h : SSet.Finite (⨆ i : Empty, (fun _ => (⊥ : X.Subcomplex)) i :) :=
      (SSet.finite_iSup_iff (fun _ : Empty => (⊥ : X.Subcomplex))).mpr
        (fun i => nomatch i)
    simpa using h
  exact ⟨(⊥, Subcomplex.ofSimplex y), hbot, inferInstance,
    (Subcomplex.image_le_iff (⊥ : X.Subcomplex) f _).mpr bot_le⟩

/-- The actual inclusion cocone recovers the whole original source. -/
def isColimitLeft : IsColimit (leftCocone f) := by
  apply evaluationJointlyReflectsColimits
  intro m
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    let j := ofLeftSimplex f (n := m.unop.len) x
    exact ⟨j, ⟨x, Subcomplex.mem_ofSimplex_obj x⟩, rfl⟩
  · intro j x y h
    refine ⟨j, 𝟙 j, ?_⟩
    exact congrArg (fun z => ((leftDiagram f).map (𝟙 j)).app m z) (Subtype.ext h)

/-- The actual inclusion cocone recovers the whole original target. -/
def isColimitRight : IsColimit (rightCocone f) := by
  apply evaluationJointlyReflectsColimits
  intro m
  apply Types.FilteredColimit.isColimitOf'
  · intro y
    let j := ofRightSimplex f (n := m.unop.len) y
    refine ⟨j, ⟨y, ?_⟩, rfl⟩
    dsimp only [j, ofRightSimplex, right]
    exact Subcomplex.mem_ofSimplex_obj y
  · intro j x y h
    refine ⟨j, 𝟙 j, ?_⟩
    exact congrArg (fun z => ((rightDiagram f).map (𝟙 j)).app m z) (Subtype.ext h)

end FiniteSubarrow


attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

open HomotopicalAlgebra CategoryTheory.MorphismProperty
open SSet.modelCategoryQuillen in
/-- The same native horn terminal iteration on every original simplicial set. -/
def completion : SSet.{u} ⥤ SSet.{u} :=
  SmallObject.terminalIteration J Cardinal.aleph0

open SSet.modelCategoryQuillen in
/-- Its original small-object unit, with naturality on every original map. -/
def completionUnit : 𝟭 SSet.{u} ⟶ completion where
  app X := SmallObject.ιObj J Cardinal.aleph0 (terminal.from X)
  naturality X Y f := by
    exact (SmallObject.ιObj_naturality J Cardinal.aleph0
      ((terminal.arrowFunctor SSet.{u}).map f)).symm

@[reassoc]
theorem completionUnit_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    completionUnit.app X ≫ completion.map f = f ≫ completionUnit.app Y :=
  (completionUnit.naturality f).symm

/-- The original unit is a scalar trivial cofibration in the actual Kan model. -/
theorem completionUnit_trivial (X : SSet.{u}) :
    trivialCofibrations SSet.{u} (completionUnit.app X) := by
  rw [← fibrations_llp, SSet.modelCategoryQuillen.fibrations_eq]
  exact SmallObject.llp_rlp_ιObj SSet.modelCategoryQuillen.J Cardinal.aleph0
    (terminal.from X)

instance completion_isKan (X : SSet.{u}) : KanComplex (completion.obj X) := by
  apply (HomotopicalAlgebra.isFibrant_iff _).mpr
  rw [HomotopicalAlgebra.fibration_iff, SSet.modelCategoryQuillen.fibrations_eq]
  have h := SmallObject.rlp_πObj SSet.modelCategoryQuillen.J Cardinal.aleph0
    (terminal.from X)
  change SSet.modelCategoryQuillen.J.rlp
    (terminal.from (SmallObject.obj SSet.modelCategoryQuillen.J Cardinal.aleph0
      (terminal.from X)))
  rwa [Subsingleton.elim
    (SmallObject.πObj SSet.modelCategoryQuillen.J Cardinal.aleph0 (terminal.from X))
    (terminal.from (SmallObject.obj SSet.modelCategoryQuillen.J Cardinal.aleph0
      (terminal.from X)))] at h

/-- Completion detects the original all-endpoint scalar weak class through its two units. -/
theorem completion_map_weak_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    realizationWeakEquivalences (completion.map f) ↔ realizationWeakEquivalences f := by
  have hx : realizationWeakEquivalences (completionUnit.app X) :=
    (completionUnit_trivial X).2
  have hy : realizationWeakEquivalences (completionUnit.app Y) :=
    (completionUnit_trivial Y).2
  constructor
  · intro hf
    have h := realizationWeakEquivalences.comp_mem _ _ hx hf
    rw [completionUnit_naturality] at h
    exact realizationWeakEquivalences.of_postcomp f (completionUnit.app Y) hy h
  · intro hf
    have h := realizationWeakEquivalences.comp_mem _ _ hf hy
    rw [← completionUnit_naturality] at h
    exact realizationWeakEquivalences.of_precomp (completionUnit.app X) (completion.map f) hx h

private theorem hornFamily_left_finite (j : SSet.modelCategoryQuillen.J.{u}.toSet) :
    SSet.Finite j.val.left := by
  have h := j.property
  change SSet.modelCategoryQuillen.J j.val.hom at h
  simp only [SSet.modelCategoryQuillen.J, CategoryTheory.MorphismProperty.iSup_iff] at h
  obtain ⟨n, h⟩ := h
  obtain ⟨i, hi⟩ := (CategoryTheory.MorphismProperty.ofHoms_iff _ _).mp h
  have hleft := congrArg Arrow.leftFunc.obj hi
  change j.val.left = (SSet.horn.{u} (n + 1) i : SSet.{u}) at hleft
  rw [hleft]
  infer_instance

private theorem hornFamily_right_finite (j : SSet.modelCategoryQuillen.J.{u}.toSet) :
    SSet.Finite j.val.right := by
  have h := j.property
  change SSet.modelCategoryQuillen.J j.val.hom at h
  simp only [SSet.modelCategoryQuillen.J, CategoryTheory.MorphismProperty.iSup_iff] at h
  obtain ⟨n, h⟩ := h
  obtain ⟨i, hi⟩ := (CategoryTheory.MorphismProperty.ofHoms_iff _ _).mp h
  have hright := congrArg Arrow.rightFunc.obj hi
  change j.val.right = (Δ[n + 1] : SSet.{u}) at hright
  rw [hright]
  infer_instance

/-- The same concrete horn completion preserves ℵ₀-filtered colimits. -/
theorem completion_isCardinalAccessible :
    completion.{u}.IsCardinalAccessible Cardinal.aleph0.{u} := by
  let : ∀ j : SSet.modelCategoryQuillen.J.{u}.toSet,
      SSet.Finite j.val.left := hornFamily_left_finite
  let : ∀ j : SSet.modelCategoryQuillen.J.{u}.toSet,
      SSet.Finite j.val.right := hornFamily_right_finite
  let : ∀ j : SSet.modelCategoryQuillen.J.{u}.toSet,
      Mono (SSet.modelCategoryQuillen.J.homFamily j) := fun j =>
    SSet.modelCategoryQuillen.J_le_monomorphisms _ j.property
  let : (SmallObject.functor SSet.modelCategoryQuillen.J.{u}.homFamily).IsCardinalAccessible
      Cardinal.aleph0.{u} :=
    SmallObject.presheafAttachment_isCardinalAccessible
      SSet.modelCategoryQuillen.J.{u}.homFamily Cardinal.aleph0.{u}
  let :
      (SmallObject.iteration SSet.modelCategoryQuillen.J.{u}
        Cardinal.aleph0.{u}).IsCardinalAccessible
      Cardinal.aleph0.{u} := by
    exact SmallObject.SuccStruct.isCardinalAccessible_iteration
      (SmallObject.ε SSet.modelCategoryQuillen.J.{u}.homFamily) Cardinal.aleph0.{u}
  exact SmallObject.terminalIteration_isCardinalAccessible
    SSet.modelCategoryQuillen.J.{u} Cardinal.aleph0.{u} Cardinal.aleph0.{u}

instance completion_preservesFilteredColimitsOfShape
    (K : Type u) [SmallCategory K] [IsFiltered K] :
    PreservesColimitsOfShape K completion.{u} := by
  let : completion.{u}.IsCardinalAccessible Cardinal.aleph0.{u} :=
    completion_isCardinalAccessible
  let : IsCardinalFiltered K Cardinal.aleph0.{u} :=
    (isCardinalFiltered_aleph0_iff K).mpr inferInstance
  exact Functor.preservesColimitsOfShape_of_isCardinalAccessible
    completion Cardinal.aleph0 K

namespace FiniteSubarrow

/-- The original source inclusion cocone mapped by the same horn completion. -/
def completedLeftCocone : Cocone (leftDiagram f ⋙ completion) :=
  completion.mapCocone (leftCocone f)

/-- The original target inclusion cocone mapped by the same horn completion. -/
def completedRightCocone : Cocone (rightDiagram f ⋙ completion) :=
  completion.mapCocone (rightCocone f)

/-- Finite original source inclusions still recover the completed original source. -/
def isColimitCompletedLeft : IsColimit (completedLeftCocone f) :=
  isColimitOfPreserves completion (isColimitLeft f)

/-- Finite original target inclusions still recover the completed original target. -/
def isColimitCompletedRight : IsColimit (completedRightCocone f) :=
  isColimitOfPreserves completion (isColimitRight f)

/-- The same completion applied to every original restricted arrow and square. -/
def completedArrow : leftDiagram f ⋙ completion ⟶ rightDiagram f ⋙ completion :=
  CategoryTheory.Functor.whiskerRight (originalArrow f) completion

@[reassoc]
theorem completedArrow_cocone (j : FiniteSubarrow f) :
    completion.map (j.left f).ι ≫ completion.map f =
      completion.map (j.hom f) ≫ completion.map (j.right f).ι := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg completion.map (hom_right_ι f j).symm

end FiniteSubarrow

/-- The mapping-path map associated to a whole original square. -/
def pathMap {X Y X' Y' : SSet.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (s : Arrow.mk f ⟶ Arrow.mk g) : mappingPathSpace f ⟶ mappingPathSpace g :=
  pullback.lift (mappingPathRetract f ≫ s.left)
    (mappingPathEval f ≫ (ihom (Δ[1] : SSet.{u})).map s.right) (by
      have hs : s.left ≫ g = f ≫ s.right := s.w
      have hp : mappingPathRetract f ≫ f = mappingPathEval f ≫ (eval₀ : pathSpace Y ⟶ Y) :=
        pullback.condition
      rw [Category.assoc, hs, ← Category.assoc, hp, Category.assoc,
        ← pathSpace_map_eval₀, ← Category.assoc])

@[reassoc (attr := simp)]
theorem pathMap_retract {X Y X' Y' : SSet.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (s : Arrow.mk f ⟶ Arrow.mk g) :
    pathMap s ≫ mappingPathRetract g = mappingPathRetract f ≫ s.left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pathMap_eval {X Y X' Y' : SSet.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (s : Arrow.mk f ⟶ Arrow.mk g) :
    pathMap s ≫ mappingPathEval g =
      mappingPathEval f ≫ (ihom (Δ[1] : SSet.{u})).map s.right :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem pathMap_target {X Y X' Y' : SSet.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (s : Arrow.mk f ⟶ Arrow.mk g) :
    pathMap s ≫ mappingPathTarget g = mappingPathTarget f ≫ s.right := by
  rw [mappingPathTarget, pathMap_eval_assoc, pathSpace_map_eval₁]
  rfl

/-- The original square's mapping-path map retains the original constant-path section. -/
theorem pathMap_section {X Y X' Y' : SSet.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (s : Arrow.mk f ⟶ Arrow.mk g) :
    mappingPathSection f ≫ pathMap s = s.left ≫ mappingPathSection g := by
  apply pullback.hom_ext
  · change (mappingPathSection f ≫ pathMap s) ≫ mappingPathRetract g =
      (s.left ≫ mappingPathSection g) ≫ mappingPathRetract g
    have hL := (Category.assoc _ _ _).trans
      ((congrArg (fun k => mappingPathSection f ≫ k) (pathMap_retract s)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ s.left) (mappingPathSection_comp_retract f)).trans
            (Category.id_comp _))))
    have hR := (Category.assoc _ _ _).trans
      ((congrArg (fun k => s.left ≫ k) (mappingPathSection_comp_retract g)).trans
        (Category.comp_id _))
    exact hL.trans hR.symm
  · change (mappingPathSection f ≫ pathMap s) ≫ mappingPathEval g =
      (s.left ≫ mappingPathSection g) ≫ mappingPathEval g
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => mappingPathSection f ≫ k) (pathMap_eval s)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ (ihom (Δ[1] : SSet.{u})).map s.right)
            (mappingPathSection_comp_eval f)).trans
            ((Category.assoc _ _ _).trans
              ((congrArg (fun k => f ≫ k) (constPath_naturality s.right).symm).trans
                ((Category.assoc _ _ _).symm.trans
                  ((congrArg (fun k => k ≫ constPath Y') s.w.symm).trans
                    ((Category.assoc _ _ _).trans
                      ((congrArg (fun k => s.left ≫ k) (mappingPathSection_comp_eval g).symm).trans
                        (Category.assoc _ _ _).symm)))))))))

theorem pathMap_id {X Y : SSet.{u}} (f : X ⟶ Y) :
    pathMap (𝟙 (Arrow.mk f)) = 𝟙 (mappingPathSpace f) := by
  apply pullback.hom_ext
  · change pathMap (𝟙 (Arrow.mk f)) ≫ mappingPathRetract f =
      𝟙 (mappingPathSpace f) ≫ mappingPathRetract f
    rw [pathMap_retract]
    change mappingPathRetract f ≫ 𝟙 X = 𝟙 (mappingPathSpace f) ≫ mappingPathRetract f
    rw [Category.comp_id, Category.id_comp]
  · change pathMap (𝟙 (Arrow.mk f)) ≫ mappingPathEval f =
      𝟙 (mappingPathSpace f) ≫ mappingPathEval f
    rw [pathMap_eval]
    change mappingPathEval f ≫ (ihom (Δ[1] : SSet.{u})).map (𝟙 Y) =
      𝟙 (mappingPathSpace f) ≫ mappingPathEval f
    rw [(ihom (Δ[1] : SSet.{u})).map_id, Category.comp_id, Category.id_comp]

theorem pathMap_comp {X Y X' Y' X'' Y'' : SSet.{u}}
    {f : X ⟶ Y} {g : X' ⟶ Y'} {h : X'' ⟶ Y''}
    (s : Arrow.mk f ⟶ Arrow.mk g) (t : Arrow.mk g ⟶ Arrow.mk h) :
    pathMap (s ≫ t) = pathMap s ≫ pathMap t := by
  apply pullback.hom_ext
  · change pathMap (s ≫ t) ≫ mappingPathRetract h =
      (pathMap s ≫ pathMap t) ≫ mappingPathRetract h
    simp only [pathMap_retract, Category.assoc,
      pathMap_retract_assoc, Arrow.comp_left]
  · change pathMap (s ≫ t) ≫ mappingPathEval h =
      (pathMap s ≫ pathMap t) ≫ mappingPathEval h
    simp only [pathMap_eval, Category.assoc,
      pathMap_eval_assoc, Arrow.comp_right, Functor.map_comp]

/-- The concrete boundary-filler detector has no condition on the original endpoints. -/
theorem weak_iff_completedPathTarget_rlp {X Y : SSet.{u}} (f : X ⟶ Y) :
    realizationWeakEquivalences f ↔
      SSet.modelCategoryQuillen.I.rlp (mappingPathTarget (completion.map f)) := by
  have hsection : realizationWeakEquivalences
      (mappingPathSection (completion.map f)) :=
    (KanComplex.W_iff_realizationWeakEquivalence _).mp
      (KanComplex.W.of_mappingPathSection _)
  calc
    realizationWeakEquivalences f ↔ realizationWeakEquivalences (completion.map f) :=
      (completion_map_weak_iff f).symm
    _ ↔ realizationWeakEquivalences
        (mappingPathSection (completion.map f) ≫ mappingPathTarget (completion.map f)) := by
      rw [mappingPathSection_comp_target]
    _ ↔ realizationWeakEquivalences (mappingPathTarget (completion.map f)) :=
      realizationWeakEquivalences.precomp_iff _ _ hsection
    _ ↔ SSet.modelCategoryQuillen.I.rlp (mappingPathTarget (completion.map f)) :=
      (SSet.modelCategoryQuillen.I_rlp_iff_realizationWeakEquivalence_of_fibration _).symm

namespace FiniteSubarrow

/-- The whole original square between two nested finite subarrows. -/
def transition {j k : FiniteSubarrow f} (h : j ≤ k) : Arrow.mk (j.hom f) ⟶ Arrow.mk (k.hom f) :=
  Arrow.homMk (Subcomplex.homOfLE h.1) (Subcomplex.homOfLE h.2)
    ((originalArrow f).naturality (homOfLE h))

/-- The whole square of the two original finite subcomplex inclusions. -/
def inclusion (j : FiniteSubarrow f) : Arrow.mk (j.hom f) ⟶ Arrow.mk f :=
  Arrow.homMk (j.left f).ι (j.right f).ι (hom_right_ι f j).symm

/-- The native Arrow image of an original finite-subarrow transition. -/
def completedTransition {j k : FiniteSubarrow f} (h : j ≤ k) :
    Arrow.mk (completion.map (j.hom f)) ⟶ Arrow.mk (completion.map (k.hom f)) :=
  completion.mapArrow.map (transition f h)

/-- The native Arrow image of both original finite-subarrow inclusions. -/
def completedInclusion (j : FiniteSubarrow f) :
    Arrow.mk (completion.map (j.hom f)) ⟶ Arrow.mk (completion.map f) :=
  completion.mapArrow.map (inclusion f j)

@[reassoc (attr := simp)]
theorem completed_left_ι {j k : FiniteSubarrow f} (h : j ≤ k) :
    completion.map (Subcomplex.homOfLE h.1) ≫ completion.map (k.left f).ι =
      completion.map (j.left f).ι := by
  rw [← Functor.map_comp, Subcomplex.homOfLE_ι]

@[reassoc (attr := simp)]
theorem completed_right_ι {j k : FiniteSubarrow f} (h : j ≤ k) :
    completion.map (Subcomplex.homOfLE h.2) ≫ completion.map (k.right f).ι =
      completion.map (j.right f).ι := by
  rw [← Functor.map_comp, Subcomplex.homOfLE_ι]

@[reassoc]
theorem completed_transition_w {j k : FiniteSubarrow f} (h : j ≤ k) :
    completion.map (Subcomplex.homOfLE h.1) ≫ completion.map (k.hom f) =
      completion.map (j.hom f) ≫ completion.map (Subcomplex.homOfLE h.2) :=
  (completedTransition f h).w

/-- Finite maps factor through the same completed source inclusion cocone. -/
theorem existsCompletedLeftFactor {T : SSet.{u}} [SSet.Finite T]
    (p : T ⟶ completion.obj X) :
    ∃ (j : FiniteSubarrow f) (p' : T ⟶ completion.obj (j.left f)),
      p' ≫ completion.map (j.left f).ι = p :=
  IsFinitelyPresentable.exists_hom_of_isColimit (isColimitCompletedLeft f) p

/-- Finite maps factor through the same completed target inclusion cocone. -/
theorem existsCompletedRightFactor {T : SSet.{u}} [SSet.Finite T]
    (p : T ⟶ completion.obj Y) :
    ∃ (j : FiniteSubarrow f) (p' : T ⟶ completion.obj (j.right f)),
      p' ≫ completion.map (j.right f).ι = p :=
  IsFinitelyPresentable.exists_hom_of_isColimit (isColimitCompletedRight f) p

theorem eventuallyEqCompletedLeft {T : SSet.{u}} [SSet.Finite T]
    {j : FiniteSubarrow f} (p q : T ⟶ completion.obj (j.left f))
    (h : p ≫ completion.map (j.left f).ι = q ≫ completion.map (j.left f).ι) :
    ∃ (k : FiniteSubarrow f) (hjk : j ≤ k),
      p ≫ completion.map (Subcomplex.homOfLE hjk.1) =
        q ≫ completion.map (Subcomplex.homOfLE hjk.1) := by
  obtain ⟨k, s, t, hst⟩ := IsFinitelyPresentable.exists_eq_of_isColimit
    (isColimitCompletedLeft f) p q h
  have he : s = t := Subsingleton.elim _ _
  subst t
  exact ⟨k, leOfHom s, hst⟩

theorem eventuallyEqCompletedRight {T : SSet.{u}} [SSet.Finite T]
    {j : FiniteSubarrow f} (p q : T ⟶ completion.obj (j.right f))
    (h : p ≫ completion.map (j.right f).ι = q ≫ completion.map (j.right f).ι) :
    ∃ (k : FiniteSubarrow f) (hjk : j ≤ k),
      p ≫ completion.map (Subcomplex.homOfLE hjk.2) =
        q ≫ completion.map (Subcomplex.homOfLE hjk.2) := by
  obtain ⟨k, s, t, hst⟩ := IsFinitelyPresentable.exists_eq_of_isColimit
    (isColimitCompletedRight f) p q h
  have he : s = t := Subsingleton.elim _ _
  subst t
  exact ⟨k, leOfHom s, hst⟩

end FiniteSubarrow


/-- Initial vertex with the literal left-tensor convention of internal paths. -/
def initialVertex (T : SSet.{u}) : T ⟶ (Δ[1] : SSet.{u}) ⊗ T :=
  SSet.ι₀ ≫ (β_ T (Δ[1] : SSet.{u})).hom

/-- Final vertex with the same tensor convention. -/
def finalVertex (T : SSet.{u}) : T ⟶ (Δ[1] : SSet.{u}) ⊗ T :=
  SSet.ι₁ ≫ (β_ T (Δ[1] : SSet.{u})).hom

@[reassoc]
theorem initialVertex_uncurry {T Z : SSet.{u}} (p : T ⟶ pathSpace Z) :
    initialVertex T ≫ MonoidalClosed.uncurry p = p ≫ eval₀ :=
  (comp_eval₀_eq_ι₀_braiding_uncurry p).symm

@[reassoc]
theorem finalVertex_uncurry {T Z : SSet.{u}} (p : T ⟶ pathSpace Z) :
    finalVertex T ≫ MonoidalClosed.uncurry p = p ≫ eval₁ :=
  (comp_eval₁_eq_ι₁_braiding_uncurry p).symm

namespace FiniteSubarrow

/-- The actual completed restricted-arrow diagram, retaining both endpoints. -/
def completedWholeDiagram : FiniteSubarrow f ⥤ Arrow SSet.{u} :=
  NatTrans.arrow (completedArrow f)

/-- The whole original completed Arrow inclusion cocone. -/
def completedWholeCocone : Cocone (completedWholeDiagram f) where
  pt := Arrow.mk (completion.map f)
  ι :=
    { app j := completedInclusion f j
      naturality j k h := by
        apply Arrow.hom_ext
        · change (completion.map (Subcomplex.homOfLE (leOfHom h).1)) ≫
            completion.map (k.left f).ι = completion.map (j.left f).ι ≫ 𝟙 _
          rw [completed_left_ι f (leOfHom h), Category.comp_id]
        · change (completion.map (Subcomplex.homOfLE (leOfHom h).2)) ≫
            completion.map (k.right f).ι = completion.map (j.right f).ι ≫ 𝟙 _
          rw [completed_right_ι f (leOfHom h), Category.comp_id] }

/-- The two completed inclusion colimits jointly recover the whole original Arrow. -/
def isColimitCompletedWhole : IsColimit (completedWholeCocone f) := by
  apply Comma.fstSndJointlyReflectColimit
  · change IsColimit (completedLeftCocone f)
    exact isColimitCompletedLeft f
  · change IsColimit (completedRightCocone f)
    exact isColimitCompletedRight f

end FiniteSubarrow


@[reassoc]
theorem initialVertex_naturality {A B : SSet.{u}} (i : A ⟶ B) :
    i ≫ initialVertex B = initialVertex A ≫ ((Δ[1] : SSet.{u}) ◁ i) := by
  rfl

@[reassoc]
theorem finalVertex_naturality {A B : SSet.{u}} (i : A ⟶ B) :
    i ≫ finalVertex B = finalVertex A ≫ ((Δ[1] : SSet.{u}) ◁ i) := by
  rfl

namespace FiniteSubarrow

private theorem finiteArrowPresentable (t : Arrow SSet.{u})
    [SSet.Finite t.left] [SSet.Finite t.right] :
    IsFinitelyPresentable.{u} t :=
  Comma.isCardinalPresentable_mk (F₁ := 𝟭 SSet.{u}) (F₂ := 𝟭 SSet.{u}) t.hom

theorem existsCompletedWholeFactor (t : Arrow SSet.{u})
    [SSet.Finite t.left] [SSet.Finite t.right]
    (s : t ⟶ Arrow.mk (completion.map f)) :
    ∃ (j : FiniteSubarrow f) (s' : t ⟶ Arrow.mk (completion.map (j.hom f))),
      s' ≫ completedInclusion f j = s := by
  let : IsFinitelyPresentable.{u} t := finiteArrowPresentable t
  exact IsFinitelyPresentable.exists_hom_of_isColimit (isColimitCompletedWhole f) s

theorem eventuallyEqCompletedWhole (t : Arrow SSet.{u})
    [SSet.Finite t.left] [SSet.Finite t.right] {j : FiniteSubarrow f}
    (p q : t ⟶ Arrow.mk (completion.map (j.hom f)))
    (h : p ≫ completedInclusion f j = q ≫ completedInclusion f j) :
    ∃ (k : FiniteSubarrow f) (hjk : j ≤ k),
      p ≫ completedTransition f hjk = q ≫ completedTransition f hjk := by
  let : IsFinitelyPresentable.{u} t := finiteArrowPresentable t
  obtain ⟨k, s, t, hst⟩ := IsFinitelyPresentable.exists_eq_of_isColimit
    (isColimitCompletedWhole f) p q h
  have he : s = t := Subsingleton.elim _ _
  subst t
  exact ⟨k, leOfHom s, hst⟩

@[reassoc (attr := simp)]
theorem completedTransition_inclusion {j k : FiniteSubarrow f} (h : j ≤ k) :
    completedTransition f h ≫ completedInclusion f k = completedInclusion f j := by
  apply Arrow.hom_ext
  · exact completed_left_ι f h
  · exact completed_right_ι f h

theorem completedTransition_comp {j k l : FiniteSubarrow f} (h : j ≤ k) (h' : k ≤ l) :
    completedTransition f h ≫ completedTransition f h' = completedTransition f (h.trans h') := by
  apply Arrow.hom_ext
  · change completion.map (Subcomplex.homOfLE h.1) ≫
      completion.map (Subcomplex.homOfLE h'.1) = completion.map (Subcomplex.homOfLE (h.trans h').1)
    rw [← CategoryTheory.Functor.map_comp]
    rfl
  · change completion.map (Subcomplex.homOfLE h.2) ≫
      completion.map (Subcomplex.homOfLE h'.2) = completion.map (Subcomplex.homOfLE (h.trans h').2)
    rw [← CategoryTheory.Functor.map_comp]
    rfl

end FiniteSubarrow


namespace FiniteSubarrow

/-- Four finite equations descend together to one finite ORIGINAL subarrow.
The ambient path is supplied by the actual ambient lift in the next theorem. -/
theorem descendPathData {A B : SSet.{u}} [SSet.Finite A] [SSet.Finite B]
    (i : A ⟶ B) (j₀ : FiniteSubarrow f)
    (top : A ⟶ mappingPathSpace (completion.map (j₀.hom f)))
    (bottom : B ⟶ completion.obj (j₀.right f))
    (L : B ⟶ completion.obj X) (H : (Δ[1] : SSet.{u}) ⊗ B ⟶ completion.obj Y)
    (hstart : initialVertex B ≫ H = L ≫ completion.map f)
    (hend : finalVertex B ≫ H = bottom ≫ completion.map (j₀.right f).ι)
    (hleft : i ≫ L =
      (top ≫ mappingPathRetract (completion.map (j₀.hom f))) ≫
        completion.map (j₀.left f).ι)
    (hpath : ((Δ[1] : SSet.{u}) ◁ i) ≫ H =
      MonoidalClosed.uncurry (top ≫ mappingPathEval (completion.map (j₀.hom f))) ≫
        completion.map (j₀.right f).ι) :
    ∃ (j : FiniteSubarrow f) (h : j₀ ≤ j)
      (L' : B ⟶ completion.obj (j.left f))
      (H' : (Δ[1] : SSet.{u}) ⊗ B ⟶ completion.obj (j.right f)),
      L' ≫ completion.map (j.hom f) = initialVertex B ≫ H' ∧
      finalVertex B ≫ H' = bottom ≫ (completedTransition f h).right ∧
      i ≫ L' = (top ≫ mappingPathRetract (completion.map (j₀.hom f))) ≫
        (completedTransition f h).left ∧
      ((Δ[1] : SSet.{u}) ◁ i) ≫ H' =
        MonoidalClosed.uncurry (top ≫ mappingPathEval (completion.map (j₀.hom f))) ≫
          (completedTransition f h).right := by
  let tA := Arrow.mk (initialVertex A)
  let tB := Arrow.mk (initialVertex B)
  let : SSet.Finite tA.left := by change SSet.Finite A; infer_instance
  let : SSet.Finite tA.right := by
    change SSet.Finite ((Δ[1] : SSet.{u}) ⊗ A); infer_instance
  let : SSet.Finite tB.left := by change SSet.Finite B; infer_instance
  let : SSet.Finite tB.right := by
    change SSet.Finite ((Δ[1] : SSet.{u}) ⊗ B); infer_instance
  let boundaryArrow : tA ⟶ tB :=
    Arrow.homMk i ((Δ[1] : SSet.{u}) ◁ i) (initialVertex_naturality i)
  let sTop : tA ⟶ Arrow.mk (completion.map (j₀.hom f)) :=
    Arrow.homMk (top ≫ mappingPathRetract (completion.map (j₀.hom f)))
      (MonoidalClosed.uncurry (top ≫ mappingPathEval (completion.map (j₀.hom f)))) (by
        change (top ≫ mappingPathRetract (completion.map (j₀.hom f))) ≫ completion.map (j₀.hom f) =
          initialVertex A ≫ MonoidalClosed.uncurry
              (top ≫ mappingPathEval (completion.map (j₀.hom f)))
        rw [initialVertex_uncurry]
        have hp : mappingPathRetract (completion.map (j₀.hom f)) ≫ completion.map (j₀.hom f) =
            mappingPathEval (completion.map (j₀.hom f)) ≫ eval₀ := pullback.condition
        rw [Category.assoc, hp, Category.assoc])
  let sAmbient : tB ⟶ Arrow.mk (completion.map f) := Arrow.homMk L H hstart.symm
  obtain ⟨jF, sF, hF⟩ := existsCompletedWholeFactor f tB sAmbient
  let j₁ := upper f j₀ jF
  let h₀₁ : j₀ ≤ j₁ := le_upper_left f j₀ jF
  let hF₁ : jF ≤ j₁ := le_upper_right f j₀ jF
  let s₁ : tB ⟶ Arrow.mk (completion.map (j₁.hom f)) :=
    sF ≫ completedTransition f hF₁
  let p₁ : tA ⟶ Arrow.mk (completion.map (j₁.hom f)) := boundaryArrow ≫ s₁
  let q₁ : tA ⟶ Arrow.mk (completion.map (j₁.hom f)) :=
    sTop ≫ completedTransition f h₀₁
  have hs₁ : s₁ ≫ completedInclusion f j₁ = sAmbient := by
    dsimp only [s₁]
    rw [Category.assoc, completedTransition_inclusion, hF]
  have hpq : p₁ ≫ completedInclusion f j₁ = q₁ ≫ completedInclusion f j₁ := by
    dsimp only [p₁, q₁]
    rw [Category.assoc, hs₁, Category.assoc, completedTransition_inclusion]
    apply Arrow.hom_ext
    · change i ≫ L =
        (top ≫ mappingPathRetract (completion.map (j₀.hom f))) ≫
          completion.map (j₀.left f).ι
      exact hleft
    · change ((Δ[1] : SSet.{u}) ◁ i) ≫ H =
        MonoidalClosed.uncurry (top ≫ mappingPathEval (completion.map (j₀.hom f))) ≫
          completion.map (j₀.right f).ι
      exact hpath
  obtain ⟨j₂, h₁₂, hboundary⟩ := eventuallyEqCompletedWhole f tA p₁ q₁ hpq
  let h₀₂ := h₀₁.trans h₁₂
  let s₂ : tB ⟶ Arrow.mk (completion.map (j₂.hom f)) := s₁ ≫ completedTransition f h₁₂
  have hs₂ : s₂ ≫ completedInclusion f j₂ = sAmbient := by
    dsimp only [s₂]
    rw [Category.assoc, completedTransition_inclusion, hs₁]
  have hboundary₂ : boundaryArrow ≫ s₂ = sTop ≫ completedTransition f h₀₂ := by
    simpa only [p₁, q₁, s₂, h₀₂, Category.assoc, completedTransition_comp] using hboundary
  have hright₂ : s₂.right ≫ completion.map (j₂.right f).ι = H := by
    have he := congrArg Arrow.Hom.right hs₂
    exact he
  have hend₂ :
      (finalVertex B ≫ s₂.right) ≫ completion.map (j₂.right f).ι =
        (bottom ≫ (completedTransition f h₀₂).right) ≫ completion.map (j₂.right f).ι := by
    change (finalVertex B ≫ s₂.right) ≫ completion.map (j₂.right f).ι =
      (bottom ≫ completion.map (Subcomplex.homOfLE h₀₂.2)) ≫ completion.map (j₂.right f).ι
    rw [Category.assoc, hright₂, Category.assoc, completed_right_ι f h₀₂]
    exact hend
  obtain ⟨j₃, h₂₃, hfinish⟩ := eventuallyEqCompletedRight f
    (finalVertex B ≫ s₂.right) (bottom ≫ (completedTransition f h₀₂).right) hend₂
  let h₀₃ := h₀₂.trans h₂₃
  let s₃ : tB ⟶ Arrow.mk (completion.map (j₃.hom f)) := s₂ ≫ completedTransition f h₂₃
  have hboundary₃ : boundaryArrow ≫ s₃ = sTop ≫ completedTransition f h₀₃ := by
    dsimp only [s₃, h₀₃]
    rw [← Category.assoc, hboundary₂, Category.assoc, completedTransition_comp]
  refine ⟨j₃, h₀₃, s₃.left, s₃.right, s₃.w, ?_, ?_, ?_⟩
  · change finalVertex B ≫ (s₂.right ≫ completion.map (Subcomplex.homOfLE h₂₃.2)) =
      bottom ≫ completion.map (Subcomplex.homOfLE h₀₃.2)
    have ht : completion.map (Subcomplex.homOfLE h₀₂.2) ≫
        completion.map (Subcomplex.homOfLE h₂₃.2) =
        completion.map (Subcomplex.homOfLE h₀₃.2) := by
      rw [← CategoryTheory.Functor.map_comp]
      rfl
    change (finalVertex B ≫ s₂.right) ≫ completion.map (Subcomplex.homOfLE h₂₃.2) =
      (bottom ≫ completion.map (Subcomplex.homOfLE h₀₂.2)) ≫
        completion.map (Subcomplex.homOfLE h₂₃.2) at hfinish
    simpa only [Category.assoc, ht] using hfinish
  · exact congrArg Arrow.Hom.left hboundary₃
  · exact congrArg Arrow.Hom.right hboundary₃

end FiniteSubarrow


namespace FiniteSubarrow

/-- Every finite monic test over a finite original subarrow of a weak original map
has a strict lift after one finite original enlargement, retaining BOTH laws. -/
theorem existsFiniteLift (hf : realizationWeakEquivalences f)
    {A B : SSet.{u}} [SSet.Finite A] [SSet.Finite B]
    (i : A ⟶ B) [Mono i] (j₀ : FiniteSubarrow f)
    (top : A ⟶ mappingPathSpace (completion.map (j₀.hom f)))
    (bottom : B ⟶ completion.obj (j₀.right f))
    (sq : CommSq top i (mappingPathTarget (completion.map (j₀.hom f))) bottom) :
    ∃ (j : FiniteSubarrow f) (h : j₀ ≤ j)
      (l : B ⟶ mappingPathSpace (completion.map (j.hom f))),
      i ≫ l = top ≫ pathMap (completedTransition f h) ∧
      l ≫ mappingPathTarget (completion.map (j.hom f)) =
        bottom ≫ (completedTransition f h).right := by
  have hrlp : (monomorphisms SSet.{u}).rlp (mappingPathTarget (completion.map f)) := by
    rw [SSet.rlp_monomorphisms]
    exact (weak_iff_completedPathTarget_rlp f).mp hf
  let : HasLiftingProperty i (mappingPathTarget (completion.map f)) := hrlp i inferInstance
  let inc := completedInclusion f j₀
  let ambientSquare : CommSq (top ≫ pathMap inc) i
      (mappingPathTarget (completion.map f)) (bottom ≫ inc.right) :=
    ⟨by rw [Category.assoc, pathMap_target, ← Category.assoc, sq.w, Category.assoc]⟩
  let l := ambientSquare.lift
  let L := l ≫ mappingPathRetract (completion.map f)
  let H := MonoidalClosed.uncurry (l ≫ mappingPathEval (completion.map f))
  have hstart : initialVertex B ≫ H = L ≫ completion.map f := by
    dsimp only [L, H]
    rw [initialVertex_uncurry, Category.assoc]
    have hp : mappingPathRetract (completion.map f) ≫ completion.map f =
        mappingPathEval (completion.map f) ≫ eval₀ := pullback.condition
    rw [Category.assoc, hp]
  have hend : finalVertex B ≫ H = bottom ≫ completion.map (j₀.right f).ι := by
    dsimp only [H]
    rw [finalVertex_uncurry, Category.assoc]
    change l ≫ mappingPathTarget (completion.map f) = bottom ≫ inc.right
    exact ambientSquare.fac_right
  have hleft : i ≫ L =
      (top ≫ mappingPathRetract (completion.map (j₀.hom f))) ≫
        completion.map (j₀.left f).ι := by
    dsimp only [L, l]
    rw [← Category.assoc, ambientSquare.fac_left, Category.assoc, pathMap_retract]
    rw [Category.assoc]
    rfl
  have hpath : ((Δ[1] : SSet.{u}) ◁ i) ≫ H =
      MonoidalClosed.uncurry (top ≫ mappingPathEval (completion.map (j₀.hom f))) ≫
        completion.map (j₀.right f).ι := by
    dsimp only [H, l]
    rw [← MonoidalClosed.uncurry_natural_left, ← Category.assoc,
      ambientSquare.fac_left, Category.assoc, pathMap_eval,
      ← Category.assoc, MonoidalClosed.uncurry_natural_right]
    rfl
  obtain ⟨j, h, Lj, Hj, hstartj, hendj, hleftj, hpathj⟩ :=
    descendPathData f i j₀ top bottom L H hstart hend hleft hpath
  let lj : B ⟶ mappingPathSpace (completion.map (j.hom f)) :=
    pullback.lift Lj (MonoidalClosed.curry Hj) (by
      rw [hstartj, ← initialVertex_uncurry, MonoidalClosed.uncurry_curry])
  have hjleft : lj ≫ mappingPathRetract (completion.map (j.hom f)) = Lj :=
    pullback.lift_fst _ _ _
  have hjpath : lj ≫ mappingPathEval (completion.map (j.hom f)) = MonoidalClosed.curry Hj :=
    pullback.lift_snd _ _ _
  refine ⟨j, h, lj, ?_, ?_⟩
  · apply pullback.hom_ext
    · change (i ≫ lj) ≫ mappingPathRetract (completion.map (j.hom f)) =
        (top ≫ pathMap (completedTransition f h)) ≫ mappingPathRetract (completion.map (j.hom f))
      rw [Category.assoc, hjleft, Category.assoc, pathMap_retract, ← Category.assoc, hleftj]
    · change (i ≫ lj) ≫ mappingPathEval (completion.map (j.hom f)) =
        (top ≫ pathMap (completedTransition f h)) ≫ mappingPathEval (completion.map (j.hom f))
      rw [Category.assoc, hjpath, Category.assoc, pathMap_eval, ← Category.assoc,
        ← MonoidalClosed.curry_natural_left, hpathj,
        MonoidalClosed.curry_natural_right, MonoidalClosed.curry_uncurry]
  · rw [mappingPathTarget, ← Category.assoc, hjpath,
      ← finalVertex_uncurry, MonoidalClosed.uncurry_curry]
    exact hendj

end FiniteSubarrow


/-- An arbitrary actual original subarrow; its endpoints need not be finite. -/
abbrev OriginalSubarrow : Type u :=
  {p : X.Subcomplex × Y.Subcomplex // p.1.image f ≤ p.2}

namespace OriginalSubarrow

instance : PartialOrder (OriginalSubarrow f) := inferInstance

/-- The original source subcomplex, which may have infinitely many nondegenerate simplices. -/
abbrev left (s : OriginalSubarrow f) : X.Subcomplex := s.val.1
/-- The original target subcomplex, with no finiteness requirement. -/
abbrev right (s : OriginalSubarrow f) : Y.Subcomplex := s.val.2

/-- The literal restriction of the original map to the recorded endpoint subcomplexes. -/
def hom (s : OriginalSubarrow f) : (s.left f : SSet.{u}) ⟶ (s.right f : SSet.{u}) :=
  (s.left f).toImage f ≫ Subcomplex.homOfLE s.property

@[reassoc (attr := simp)]
theorem hom_right_ι (s : OriginalSubarrow f) :
    s.hom f ≫ (s.right f).ι = (s.left f).ι ≫ f := by
  rw [hom, Category.assoc, Subcomplex.homOfLE_ι, Subcomplex.toImage_ι]

/-- Forget only the finiteness proofs of a finite original subarrow. -/
def ofFinite (j : FiniteSubarrow f) : OriginalSubarrow f := ⟨j.val, j.property.2.2⟩

/-- Adjoin a finite original addition to both endpoints of an arbitrary original subarrow. -/
def enlarge (s : OriginalSubarrow f) (j : FiniteSubarrow f) : OriginalSubarrow f := by
  refine ⟨(s.left f ⊔ j.left f, s.right f ⊔ j.right f), ?_⟩
  rw [Subcomplex.image_le_iff]
  apply sup_le
  · exact (Subcomplex.image_le_iff (s.left f) f _).mp (s.property.trans le_sup_left)
  · exact (Subcomplex.image_le_iff (j.left f) f _).mp ((j.image_le f).trans le_sup_right)

theorem le_enlarge (s : OriginalSubarrow f) (j : FiniteSubarrow f) :
    s ≤ enlarge f s j := ⟨le_sup_left, le_sup_left⟩

theorem enlarge_mono (s : OriginalSubarrow f) {j k : FiniteSubarrow f} (h : j ≤ k) :
    enlarge f s j ≤ enlarge f s k :=
  ⟨sup_le_sup le_rfl h.1, sup_le_sup le_rfl h.2⟩

/-- The whole original inclusion square of two nested original subarrows. -/
def map {s t : OriginalSubarrow f} (h : s ≤ t) : Arrow.mk (s.hom f) ⟶ Arrow.mk (t.hom f) :=
  Arrow.homMk (Subcomplex.homOfLE h.1) (Subcomplex.homOfLE h.2) (by
    apply (cancel_mono (t.right f).ι).mp
    change (Subcomplex.homOfLE h.1 ≫ t.hom f) ≫ (t.right f).ι =
      (s.hom f ≫ Subcomplex.homOfLE h.2) ≫ (t.right f).ι
    rw [Category.assoc, hom_right_ι, ← Category.assoc, Subcomplex.homOfLE_ι,
      Category.assoc, Subcomplex.homOfLE_ι, hom_right_ι])

/-- The original source and target inclusions into the original ambient arrow. -/
def inclusion (s : OriginalSubarrow f) : Arrow.mk (s.hom f) ⟶ Arrow.mk f :=
  Arrow.homMk (s.left f).ι (s.right f).ι (hom_right_ι f s).symm

/-- The same completion applied to the whole original subarrow inclusion square. -/
def completedMap {s t : OriginalSubarrow f} (h : s ≤ t) :
    Arrow.mk (completion.map (s.hom f)) ⟶ Arrow.mk (completion.map (t.hom f)) :=
  completion.mapArrow.map (map f h)

/-- The same completion applied to both original ambient inclusions. -/
def completedInclusion (s : OriginalSubarrow f) :
    Arrow.mk (completion.map (s.hom f)) ⟶ Arrow.mk (completion.map f) :=
  completion.mapArrow.map (inclusion f s)

@[reassoc (attr := simp)]
theorem completedMap_inclusion {s t : OriginalSubarrow f} (h : s ≤ t) :
    completedMap f h ≫ completedInclusion f t = completedInclusion f s := by
  apply Arrow.hom_ext
  · change completion.map (Subcomplex.homOfLE h.1) ≫ completion.map (t.left f).ι =
      completion.map (s.left f).ι
    rw [← CategoryTheory.Functor.map_comp, Subcomplex.homOfLE_ι]
  · change completion.map (Subcomplex.homOfLE h.2) ≫ completion.map (t.right f).ι =
      completion.map (s.right f).ι
    rw [← CategoryTheory.Functor.map_comp, Subcomplex.homOfLE_ι]

theorem completedMap_comp {s t v : OriginalSubarrow f} (h : s ≤ t) (h' : t ≤ v) :
    completedMap f h ≫ completedMap f h' = completedMap f (h.trans h') := by
  apply Arrow.hom_ext
  · change completion.map (Subcomplex.homOfLE h.1) ≫
      completion.map (Subcomplex.homOfLE h'.1) = completion.map (Subcomplex.homOfLE (h.trans h').1)
    rw [← CategoryTheory.Functor.map_comp]
    rfl
  · change completion.map (Subcomplex.homOfLE h.2) ≫
      completion.map (Subcomplex.homOfLE h'.2) = completion.map (Subcomplex.homOfLE (h.trans h').2)
    rw [← CategoryTheory.Functor.map_comp]
    rfl

/-- The actual source diagram obtained by finite additions to an arbitrary original base. -/
def enlargementLeftDiagram (s : OriginalSubarrow f) : FiniteSubarrow f ⥤ SSet.{u} where
  obj j := (enlarge f s j).left f
  map h := Subcomplex.homOfLE (enlarge_mono f s (leOfHom h)).1
  map_id _j := Subcomplex.homOfLE_refl _
  map_comp _h _k := rfl

/-- The actual target diagram obtained by finite additions to the same original base. -/
def enlargementRightDiagram (s : OriginalSubarrow f) : FiniteSubarrow f ⥤ SSet.{u} where
  obj j := (enlarge f s j).right f
  map h := Subcomplex.homOfLE (enlarge_mono f s (leOfHom h)).2
  map_id _j := Subcomplex.homOfLE_refl _
  map_comp _h _k := rfl

/-- The natural original restriction on every finite enlargement of the base subarrow. -/
def enlargementArrow (s : OriginalSubarrow f) :
    enlargementLeftDiagram f s ⟶ enlargementRightDiagram f s where
  app j := (enlarge f s j).hom f
  naturality _j _k h := (map f (enlarge_mono f s (leOfHom h))).w

/-- The original ambient source inclusion cocone of the finite enlargements. -/
def enlargementLeftCocone (s : OriginalSubarrow f) : Cocone (enlargementLeftDiagram f s) where
  pt := X
  ι :=
    { app j := ((enlarge f s j).left f).ι
      naturality j k h := by
        change Subcomplex.homOfLE (enlarge_mono f s (leOfHom h)).1 ≫
          ((enlarge f s k).left f).ι = ((enlarge f s j).left f).ι ≫ 𝟙 X
        rw [Subcomplex.homOfLE_ι, Category.comp_id] }

/-- The original ambient target inclusion cocone of the finite enlargements. -/
def enlargementRightCocone (s : OriginalSubarrow f) : Cocone (enlargementRightDiagram f s) where
  pt := Y
  ι :=
    { app j := ((enlarge f s j).right f).ι
      naturality j k h := by
        change Subcomplex.homOfLE (enlarge_mono f s (leOfHom h)).2 ≫
          ((enlarge f s k).right f).ι = ((enlarge f s j).right f).ι ≫ 𝟙 Y
        rw [Subcomplex.homOfLE_ι, Category.comp_id] }

/-- Finite additions to any original base recover the original ambient source. -/
def isColimitEnlargementLeft (s : OriginalSubarrow f) : IsColimit (enlargementLeftCocone f s) := by
  apply evaluationJointlyReflectsColimits
  intro m
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    let j := FiniteSubarrow.ofLeftSimplex f (n := m.unop.len) x
    refine ⟨j, ⟨x, ?_⟩, rfl⟩
    change x ∈ (s.left f).obj m ∨ x ∈ (j.left f).obj m
    exact Or.inr (Subcomplex.mem_ofSimplex_obj x)
  · intro j x y h
    refine ⟨j, 𝟙 j, ?_⟩
    exact congrArg (fun z => ((enlargementLeftDiagram f s).map (𝟙 j)).app m z) (Subtype.ext h)

/-- Finite additions to any original base recover the original ambient target. -/
def isColimitEnlargementRight (s : OriginalSubarrow f) :
    IsColimit (enlargementRightCocone f s) := by
  apply evaluationJointlyReflectsColimits
  intro m
  apply Types.FilteredColimit.isColimitOf'
  · intro y
    let j := FiniteSubarrow.ofRightSimplex f (n := m.unop.len) y
    refine ⟨j, ⟨y, ?_⟩, rfl⟩
    change y ∈ (s.right f).obj m ∨ y ∈ (j.right f).obj m
    dsimp only [j, FiniteSubarrow.ofRightSimplex, FiniteSubarrow.right]
    exact Or.inr (Subcomplex.mem_ofSimplex_obj y)
  · intro j x y h
    refine ⟨j, 𝟙 j, ?_⟩
    exact congrArg (fun z => ((enlargementRightDiagram f s).map (𝟙 j)).app m z) (Subtype.ext h)

end OriginalSubarrow


/-- Finite nondegenerate support gives COUNTABLE total original elements. -/
instance finiteElementsCountable (T : SSet.{u}) [SSet.Finite T] : Countable T.Elements := by
  let : ∀ n : ℕ, Countable (T _⦋n⦌) := fun _ => inferInstance
  let cover : (Σ n : ℕ, T _⦋n⦌) → T.Elements :=
    fun z => CategoryTheory.Functor.elementsMk T (op ⦋z.1⦌) z.2
  have hcover : Function.Surjective cover := by
    intro q
    refine ⟨⟨q.obj.unop.len, q.val⟩, ?_⟩
    cases q
    rfl
  exact Cardinal.mk_le_aleph0_iff.mp
    ((Cardinal.mk_le_of_surjective hcover).trans Cardinal.mk_le_aleph0)

theorem finiteElements_le_aleph0 (T : SSet.{u}) [SSet.Finite T] :
    Cardinal.mk T.Elements ≤ Cardinal.aleph0.{u} :=
  Cardinal.mk_le_aleph0

namespace OriginalSubarrow

/-- The native whole-Arrow completion of the actual finite-addition diagram. -/
def completedEnlargementDiagram (s : OriginalSubarrow f) : FiniteSubarrow f ⥤ Arrow SSet.{u} :=
  NatTrans.arrow (CategoryTheory.Functor.whiskerRight (enlargementArrow f s) completion)

/-- The completed ambient inclusion cocone of the actual finite-addition diagram. -/
def completedEnlargementCocone (s : OriginalSubarrow f) :
    Cocone (completedEnlargementDiagram f s) where
  pt := Arrow.mk (completion.map f)
  ι :=
    { app j := completedInclusion f (enlarge f s j)
      naturality j k h := by
        apply Arrow.hom_ext
        · change completion.map (Subcomplex.homOfLE (enlarge_mono f s (leOfHom h)).1) ≫
            completion.map ((enlarge f s k).left f).ι =
            completion.map ((enlarge f s j).left f).ι ≫ 𝟙 _
          rw [← CategoryTheory.Functor.map_comp, Subcomplex.homOfLE_ι, Category.comp_id]
        · change completion.map (Subcomplex.homOfLE (enlarge_mono f s (leOfHom h)).2) ≫
            completion.map ((enlarge f s k).right f).ι =
            completion.map ((enlarge f s j).right f).ι ≫ 𝟙 _
          rw [← CategoryTheory.Functor.map_comp, Subcomplex.homOfLE_ι, Category.comp_id] }

/-- The same completion preserves the actual whole finite-addition colimit. -/
def isColimitCompletedEnlargement (s : OriginalSubarrow f) :
    IsColimit (completedEnlargementCocone f s) := by
  apply Comma.fstSndJointlyReflectColimit
  · change IsColimit (completion.mapCocone (enlargementLeftCocone f s))
    exact isColimitOfPreserves completion (isColimitEnlargementLeft f s)
  · change IsColimit (completion.mapCocone (enlargementRightCocone f s))
    exact isColimitOfPreserves completion (isColimitEnlargementRight f s)

theorem existsEnlargementWholeFactor (s : OriginalSubarrow f) (t : Arrow SSet.{u})
    [SSet.Finite t.left] [SSet.Finite t.right] (a : t ⟶ Arrow.mk (completion.map f)) :
    ∃ (j : FiniteSubarrow f)
      (a' : t ⟶ Arrow.mk (completion.map ((enlarge f s j).hom f))),
      a' ≫ completedInclusion f (enlarge f s j) = a := by
  let : IsFinitelyPresentable.{u} t :=
    Comma.isCardinalPresentable_mk (F₁ := 𝟭 SSet.{u}) (F₂ := 𝟭 SSet.{u}) t.hom
  exact IsFinitelyPresentable.exists_hom_of_isColimit (isColimitCompletedEnlargement f s) a

theorem eventuallyEqEnlargementWhole (s : OriginalSubarrow f) (t : Arrow SSet.{u})
    [SSet.Finite t.left] [SSet.Finite t.right] {j : FiniteSubarrow f}
    (a b : t ⟶ Arrow.mk (completion.map ((enlarge f s j).hom f)))
    (hab : a ≫ completedInclusion f (enlarge f s j) =
      b ≫ completedInclusion f (enlarge f s j)) :
    ∃ (k : FiniteSubarrow f) (h : j ≤ k),
      a ≫ completedMap f (enlarge_mono f s h) = b ≫ completedMap f (enlarge_mono f s h) := by
  let : IsFinitelyPresentable.{u} t :=
    Comma.isCardinalPresentable_mk (F₁ := 𝟭 SSet.{u}) (F₂ := 𝟭 SSet.{u}) t.hom
  obtain ⟨k, u, v, huv⟩ := IsFinitelyPresentable.exists_eq_of_isColimit
    (isColimitCompletedEnlargement f s) a b hab
  have he : u = v := Subsingleton.elim _ _
  subst v
  exact ⟨k, leOfHom u, huv⟩

theorem eventuallyEqEnlargementRight (s : OriginalSubarrow f)
    {T : SSet.{u}} [SSet.Finite T] {j : FiniteSubarrow f}
    (a b : T ⟶ completion.obj ((enlarge f s j).right f))
    (hab : a ≫ completion.map ((enlarge f s j).right f).ι =
      b ≫ completion.map ((enlarge f s j).right f).ι) :
    ∃ (k : FiniteSubarrow f) (h : j ≤ k),
      a ≫ (completedMap f (enlarge_mono f s h)).right =
        b ≫ (completedMap f (enlarge_mono f s h)).right := by
  have hc := isColimitOfPreserves completion (isColimitEnlargementRight f s)
  obtain ⟨k, u, v, huv⟩ := IsFinitelyPresentable.exists_eq_of_isColimit hc a b hab
  have he : u = v := Subsingleton.elim _ _
  subst v
  exact ⟨k, leOfHom u, huv⟩

end OriginalSubarrow


namespace OriginalSubarrow

/-- Four finite equations descend to a finite ADDITION to an arbitrary
original subarrow; no finiteness of that subarrow is assumed. -/
theorem descendFiniteAdditionData (s : OriginalSubarrow f)
    {A B : SSet.{u}} [SSet.Finite A] [SSet.Finite B] (i : A ⟶ B)
    (top : A ⟶ mappingPathSpace (completion.map (s.hom f)))
    (bottom : B ⟶ completion.obj (s.right f))
    (L : B ⟶ completion.obj X) (H : (Δ[1] : SSet.{u}) ⊗ B ⟶ completion.obj Y)
    (hstart : initialVertex B ≫ H = L ≫ completion.map f)
    (hend : finalVertex B ≫ H = bottom ≫ completion.map (s.right f).ι)
    (hleft : i ≫ L = (top ≫ mappingPathRetract (completion.map (s.hom f))) ≫
      completion.map (s.left f).ι)
    (hpath : ((Δ[1] : SSet.{u}) ◁ i) ≫ H =
      MonoidalClosed.uncurry (top ≫ mappingPathEval (completion.map (s.hom f))) ≫
        completion.map (s.right f).ι) :
    ∃ (j : FiniteSubarrow f)
      (L' : B ⟶ completion.obj ((enlarge f s j).left f))
      (H' : (Δ[1] : SSet.{u}) ⊗ B ⟶ completion.obj ((enlarge f s j).right f)),
      L' ≫ completion.map ((enlarge f s j).hom f) = initialVertex B ≫ H' ∧
      finalVertex B ≫ H' = bottom ≫ (completedMap f (le_enlarge f s j)).right ∧
      i ≫ L' = (top ≫ mappingPathRetract (completion.map (s.hom f))) ≫
        (completedMap f (le_enlarge f s j)).left ∧
      ((Δ[1] : SSet.{u}) ◁ i) ≫ H' =
        MonoidalClosed.uncurry (top ≫ mappingPathEval (completion.map (s.hom f))) ≫
          (completedMap f (le_enlarge f s j)).right := by
  let tA := Arrow.mk (initialVertex A)
  let tB := Arrow.mk (initialVertex B)
  let : SSet.Finite tA.left := by change SSet.Finite A; infer_instance
  let : SSet.Finite tA.right := by change SSet.Finite ((Δ[1] : SSet.{u}) ⊗ A); infer_instance
  let : SSet.Finite tB.left := by change SSet.Finite B; infer_instance
  let : SSet.Finite tB.right := by change SSet.Finite ((Δ[1] : SSet.{u}) ⊗ B); infer_instance
  let boundaryArrow : tA ⟶ tB :=
    Arrow.homMk i ((Δ[1] : SSet.{u}) ◁ i) (initialVertex_naturality i)
  let sTop : tA ⟶ Arrow.mk (completion.map (s.hom f)) :=
    Arrow.homMk (top ≫ mappingPathRetract (completion.map (s.hom f)))
      (MonoidalClosed.uncurry (top ≫ mappingPathEval (completion.map (s.hom f)))) (by
        change (top ≫ mappingPathRetract (completion.map (s.hom f))) ≫ completion.map (s.hom f) =
          initialVertex A ≫ MonoidalClosed.uncurry
              (top ≫ mappingPathEval (completion.map (s.hom f)))
        rw [initialVertex_uncurry]
        have hp : mappingPathRetract (completion.map (s.hom f)) ≫ completion.map (s.hom f) =
            mappingPathEval (completion.map (s.hom f)) ≫ eval₀ := pullback.condition
        rw [Category.assoc, hp, Category.assoc])
  let sAmbient : tB ⟶ Arrow.mk (completion.map f) := Arrow.homMk L H hstart.symm
  obtain ⟨j₀, s₀, hs₀⟩ := existsEnlargementWholeFactor f s tB sAmbient
  let p₀ : tA ⟶ Arrow.mk (completion.map ((enlarge f s j₀).hom f)) := boundaryArrow ≫ s₀
  let q₀ : tA ⟶ Arrow.mk (completion.map ((enlarge f s j₀).hom f)) :=
    sTop ≫ completedMap f (le_enlarge f s j₀)
  have hpq : p₀ ≫ completedInclusion f (enlarge f s j₀) =
      q₀ ≫ completedInclusion f (enlarge f s j₀) := by
    dsimp only [p₀, q₀]
    rw [Category.assoc, hs₀, Category.assoc, completedMap_inclusion]
    apply Arrow.hom_ext
    · exact hleft
    · exact hpath
  obtain ⟨j₁, h₀₁, hb₁⟩ := eventuallyEqEnlargementWhole f s tA p₀ q₀ hpq
  let s₁ : tB ⟶ Arrow.mk (completion.map ((enlarge f s j₁).hom f)) :=
    s₀ ≫ completedMap f (enlarge_mono f s h₀₁)
  have hs₁ : s₁ ≫ completedInclusion f (enlarge f s j₁) = sAmbient := by
    dsimp only [s₁]
    rw [Category.assoc, completedMap_inclusion, hs₀]
  have hboundary₁ : boundaryArrow ≫ s₁ = sTop ≫ completedMap f (le_enlarge f s j₁) := by
    simpa only [p₀, q₀, s₁, Category.assoc, completedMap_comp] using hb₁
  have hright₁ : s₁.right ≫ completion.map ((enlarge f s j₁).right f).ι = H :=
    congrArg Arrow.Hom.right hs₁
  have hbase₁ : (completedMap f (le_enlarge f s j₁)).right ≫
      completion.map ((enlarge f s j₁).right f).ι = completion.map (s.right f).ι :=
    congrArg Arrow.Hom.right (completedMap_inclusion f (le_enlarge f s j₁))
  have he₁ : (finalVertex B ≫ s₁.right) ≫ completion.map ((enlarge f s j₁).right f).ι =
      (bottom ≫ (completedMap f (le_enlarge f s j₁)).right) ≫
        completion.map ((enlarge f s j₁).right f).ι := by
    rw [Category.assoc, hright₁, Category.assoc, hbase₁]
    exact hend
  obtain ⟨j₂, h₁₂, he₂⟩ := eventuallyEqEnlargementRight f s
    (finalVertex B ≫ s₁.right) (bottom ≫ (completedMap f (le_enlarge f s j₁)).right) he₁
  let s₂ : tB ⟶ Arrow.mk (completion.map ((enlarge f s j₂).hom f)) :=
    s₁ ≫ completedMap f (enlarge_mono f s h₁₂)
  have hboundary₂ : boundaryArrow ≫ s₂ = sTop ≫ completedMap f (le_enlarge f s j₂) := by
    dsimp only [s₂]
    rw [← Category.assoc, hboundary₁, Category.assoc, completedMap_comp]
  refine ⟨j₂, s₂.left, s₂.right, s₂.w, ?_, ?_, ?_⟩
  · have ht : (completedMap f (le_enlarge f s j₁)).right ≫
        (completedMap f (enlarge_mono f s h₁₂)).right =
        (completedMap f (le_enlarge f s j₂)).right :=
      congrArg Arrow.Hom.right (completedMap_comp f (le_enlarge f s j₁) (enlarge_mono f s h₁₂))
    change finalVertex B ≫ (s₁.right ≫ (completedMap f (enlarge_mono f s h₁₂)).right) =
      bottom ≫ (completedMap f (le_enlarge f s j₂)).right
    simpa only [Category.assoc, ht] using he₂
  · exact congrArg Arrow.Hom.left hboundary₂
  · exact congrArg Arrow.Hom.right hboundary₂

end OriginalSubarrow


namespace OriginalSubarrow

/-- A weak ambient original map supplies a strict lift after a finite original
ADDITION to any original subarrow, including one with infinite endpoints. -/
theorem existsFiniteAdditionLift (hf : realizationWeakEquivalences f)
    (s : OriginalSubarrow f) {A B : SSet.{u}} [SSet.Finite A] [SSet.Finite B]
    (i : A ⟶ B) [Mono i]
    (top : A ⟶ mappingPathSpace (completion.map (s.hom f)))
    (bottom : B ⟶ completion.obj (s.right f))
    (sq : CommSq top i (mappingPathTarget (completion.map (s.hom f))) bottom) :
    ∃ (j : FiniteSubarrow f)
      (l : B ⟶ mappingPathSpace (completion.map ((enlarge f s j).hom f))),
      i ≫ l = top ≫ pathMap (completedMap f (le_enlarge f s j)) ∧
      l ≫ mappingPathTarget (completion.map ((enlarge f s j).hom f)) =
        bottom ≫ (completedMap f (le_enlarge f s j)).right := by
  have hrlp : (monomorphisms SSet.{u}).rlp (mappingPathTarget (completion.map f)) := by
    rw [SSet.rlp_monomorphisms]
    exact (weak_iff_completedPathTarget_rlp f).mp hf
  let : HasLiftingProperty i (mappingPathTarget (completion.map f)) := hrlp i inferInstance
  let inc := completedInclusion f s
  let ambientSquare : CommSq (top ≫ pathMap inc) i
      (mappingPathTarget (completion.map f)) (bottom ≫ inc.right) :=
    ⟨by rw [Category.assoc, pathMap_target, ← Category.assoc, sq.w, Category.assoc]⟩
  let l := ambientSquare.lift
  let L := l ≫ mappingPathRetract (completion.map f)
  let H := MonoidalClosed.uncurry (l ≫ mappingPathEval (completion.map f))
  have hstart : initialVertex B ≫ H = L ≫ completion.map f := by
    dsimp only [L, H]
    rw [initialVertex_uncurry, Category.assoc]
    have hp : mappingPathRetract (completion.map f) ≫ completion.map f =
        mappingPathEval (completion.map f) ≫ eval₀ := pullback.condition
    rw [Category.assoc, hp]
  have hend : finalVertex B ≫ H = bottom ≫ completion.map (s.right f).ι := by
    dsimp only [H]
    rw [finalVertex_uncurry, Category.assoc]
    change l ≫ mappingPathTarget (completion.map f) = bottom ≫ inc.right
    exact ambientSquare.fac_right
  have hleft : i ≫ L = (top ≫ mappingPathRetract (completion.map (s.hom f))) ≫
      completion.map (s.left f).ι := by
    dsimp only [L, l]
    rw [← Category.assoc, ambientSquare.fac_left, Category.assoc, pathMap_retract]
    rw [Category.assoc]
    rfl
  have hpath : ((Δ[1] : SSet.{u}) ◁ i) ≫ H =
      MonoidalClosed.uncurry (top ≫ mappingPathEval (completion.map (s.hom f))) ≫
        completion.map (s.right f).ι := by
    dsimp only [H, l]
    rw [← MonoidalClosed.uncurry_natural_left, ← Category.assoc,
      ambientSquare.fac_left, Category.assoc, pathMap_eval,
      ← Category.assoc, MonoidalClosed.uncurry_natural_right]
    rfl
  obtain ⟨j, Lj, Hj, hstartj, hendj, hleftj, hpathj⟩ :=
    descendFiniteAdditionData f s i top bottom L H hstart hend hleft hpath
  let lj : B ⟶ mappingPathSpace (completion.map ((enlarge f s j).hom f)) :=
    pullback.lift Lj (MonoidalClosed.curry Hj) (by
      rw [hstartj, ← initialVertex_uncurry, MonoidalClosed.uncurry_curry])
  have hjleft : lj ≫ mappingPathRetract (completion.map ((enlarge f s j).hom f)) = Lj :=
    pullback.lift_fst _ _ _
  have hjpath : lj ≫ mappingPathEval (completion.map ((enlarge f s j).hom f)) =
      MonoidalClosed.curry Hj := pullback.lift_snd _ _ _
  refine ⟨j, lj, ?_, ?_⟩
  · apply pullback.hom_ext
    · change (i ≫ lj) ≫ mappingPathRetract (completion.map ((enlarge f s j).hom f)) =
        (top ≫ pathMap (completedMap f (le_enlarge f s j))) ≫
          mappingPathRetract (completion.map ((enlarge f s j).hom f))
      rw [Category.assoc, hjleft, Category.assoc, pathMap_retract, ← Category.assoc, hleftj]
    · change (i ≫ lj) ≫ mappingPathEval (completion.map ((enlarge f s j).hom f)) =
        (top ≫ pathMap (completedMap f (le_enlarge f s j))) ≫
          mappingPathEval (completion.map ((enlarge f s j).hom f))
      rw [Category.assoc, hjpath, Category.assoc, pathMap_eval, ← Category.assoc,
        ← MonoidalClosed.curry_natural_left, hpathj,
        MonoidalClosed.curry_natural_right, MonoidalClosed.curry_uncurry]
  · rw [mappingPathTarget, ← Category.assoc, hjpath,
      ← finalVertex_uncurry, MonoidalClosed.uncurry_curry]
    exact hendj

end OriginalSubarrow

end SSet.KanWeakInterpolation
