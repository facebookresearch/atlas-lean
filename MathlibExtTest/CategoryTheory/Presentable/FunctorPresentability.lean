/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Presentable.FunctorPresentability
public import Mathlib.CategoryTheory.Presentable.Type
public import Mathlib.Algebra.Group.ULift
public import Mathlib.CategoryTheory.SingleObj

/-!
# Entire original bounded-shape and component-compactness contracts

The complete native shape keeps distinct first/second arrows at coincident
endpoints. Original shape and working universes remain independent.
The component theorem uses the SAME chosen evaluation/cofree data.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe w uM vM uD vD uK vK t uL uR

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Presentable.FunctorPresentabilityTest

open FunctorPresentability

example {M : Type uM} [Category.{vM} M]
    {K : Type uK} [Category.{vK} K] [HasLimitsOfShape K (Type t)]
    {F : K ⥤ M ⥤ Type t} (c : Cone F) (hc : IsLimit c)
    (χ : Cardinal.{w}) [Fact χ.IsRegular] (hK : HasCardinalLT (Arrow K) χ)
    [∀ k : K, (F.obj k).IsCardinalAccessible χ] :
    c.pt.IsCardinalAccessible χ :=
  Functor.isCardinalAccessible_of_isLimit c hc χ hK

example (S : MulticospanShape.{uL, uR}) (a : Arrow (WalkingMulticospan S)) :
    (multicospanArrowEquiv S).symm ((multicospanArrowEquiv S) a) = a :=
  (multicospanArrowEquiv S).symm_apply_apply a

example (S : MulticospanShape.{uL, uR}) (a : S.L ⊕ (S.R ⊕ (S.R ⊕ S.R))) :
    multicospanArrowEquiv S ((multicospanArrowEquiv S).symm a) = a :=
  (multicospanArrowEquiv S).apply_symm_apply a

example (S : MulticospanShape.{uL, uR}) (l : S.L) :
    (multicospanArrowEquiv S).symm (.inl l) =
      Arrow.mk (WalkingMulticospan.Hom.id (.left l)) := rfl

example (S : MulticospanShape.{uL, uR}) (r : S.R) :
    (multicospanArrowEquiv S).symm (.inr (.inl r)) =
      Arrow.mk (WalkingMulticospan.Hom.id (.right r)) := rfl

example (S : MulticospanShape.{uL, uR}) (r : S.R) :
    (multicospanArrowEquiv S).symm (.inr (.inr (.inl r))) =
      Arrow.mk (WalkingMulticospan.Hom.fst r) := rfl

example (S : MulticospanShape.{uL, uR}) (r : S.R) :
    (multicospanArrowEquiv S).symm (.inr (.inr (.inr r))) =
      Arrow.mk (WalkingMulticospan.Hom.snd r) := rfl

example (S : MulticospanShape.{uL, uR}) (χ : Cardinal.{w})
    (hχ : Cardinal.aleph0 ≤ χ) (hL : HasCardinalLT S.L χ) (hR : HasCardinalLT S.R χ) :
    HasCardinalLT (Arrow (WalkingMulticospan S)) χ :=
  multicospanArrow_bound S χ hχ hL hR

example {S : Type uD} [Category.{vD} S] (χ : Cardinal.{w}) [Fact χ.IsRegular]
    (hS : HasCardinalLT (Arrow S) χ) :
    HasCardinalLT (Arrow (WalkingMulticospan (multicospanShapeEnd S))) χ :=
  endShapeArrow_bound χ hS


section ComponentEquations

variable (M : Type uM) [Category.{vM} M] {S : Type w} [SmallCategory S] (F : S ⥤ M)

example (G : S ⥤ M) (s : S) :
    (componentProjection M F s).app G =
      ↾fun a : F ⟶ G ↦ ULift.up (a.app s) := rfl

example (G : S ⥤ M) (f : Arrow S) :
    ((equationIndex M F).fst f).app G =
      ↾fun h : ULift.{w} (F.obj f.left ⟶ G.obj f.left) ↦
        ULift.up (h.down ≫ G.map f.hom) := rfl

example (G : S ⥤ M) (f : Arrow S) :
    ((equationIndex M F).snd f).app G =
      ↾fun h : ULift.{w} (F.obj f.right ⟶ G.obj f.right) ↦
        ULift.up (F.map f.hom ≫ h.down) := rfl

example (G : S ⥤ M) (s : S) :
    (fun a : F ⟶ G ↦ ((componentCone M F).ι s).app G a) =
      fun a ↦ ULift.up (a.app s) := by
  funext a
  exact componentCone_ι_app M F G s a

example (G : S ⥤ M) (f : Arrow S) (a : F ⟶ G) :
    ((componentCone M F).π.app (.right f)).app G a =
      ULift.up (a.app f.left ≫ G.map f.hom) :=
  componentCone_right_app M F G f a

example (T : Multifork (equationIndex M F)) (G : S ⥤ M) (s : S) :
    (fun x : T.pt.obj G ↦ ((componentLift M F T).app G x).app s) =
      fun x ↦ (((T.ι s).app G) x).down := by
  funext x
  exact componentLift_app M F T G x s

example (T : Multifork (equationIndex M F)) (G : S ⥤ M)
    (x : T.pt.obj G) {s t : S} (f : s ⟶ t) :
    F.map f ≫ ((componentLift M F T).app G x).app t =
      ((componentLift M F T).app G x).app s ≫ G.map f :=
  ((componentLift M F T).app G x).naturality f

example (T : Multifork (equationIndex M F)) {G H : S ⥤ M} (a : G ⟶ H) :
    T.pt.map a ≫ (componentLift M F T).app H =
      (componentLift M F T).app G ≫ (componentCone M F).pt.map a :=
  (componentLift M F T).naturality a

example : IsLimit (componentCone M F) := componentConeIsLimit M F

example (T : Multifork (equationIndex M F)) :
    (componentConeIsLimit M F).lift T = componentLift M F T :=
  componentConeIsLimit_lift M F T

example (T : Multifork (equationIndex M F)) (s : S) :
    componentLift M F T ≫ (componentCone M F).ι s = T.ι s :=
  componentLift_ι M F T s

example (T : Multifork (equationIndex M F)) (m : T.pt ⟶ (componentCone M F).pt)
    (hm : ∀ s : S, m ≫ (componentCone M F).ι s = T.ι s) :
    m = componentLift M F T :=
  componentLift_unique M F T m hm

example : componentLift M F (componentCone M F) = 𝟙 (componentCone M F).pt := by
  apply Multifork.IsLimit.hom_ext (componentConeIsLimit M F)
  intro s
  exact (componentLift_ι M F (componentCone M F) s).trans (Category.id_comp _).symm

example (κLP : Cardinal.{w}) [Fact κLP.IsRegular] [IsCardinalLocallyPresentable M κLP]
    (χ : Cardinal.{w}) [Fact χ.IsRegular] (hS : HasCardinalLT (Arrow S) χ)
    (hF : ∀ s : S, IsCardinalPresentable (F.obj s) χ) : IsCardinalPresentable F χ :=
  small_diagram_presentable M F κLP χ hS hF

end ComponentEquations


section OriginalComponents

variable (M : Type uM) [Category.{vM} M] (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
  [IsCardinalLocallyPresentable M κLP]
  {D : Type uD} [Category.{vD} D] {S : Type w} [SmallCategory S] (s : D ≌ S)

example (χ : Cardinal.{w}) [Fact χ.IsRegular] (hLP : κLP ≤ χ)
    (hD : HasCardinalLT (Arrow S) χ) (F : D ⥤ M)
    [IsCardinalPresentable F χ] (d : D) : IsCardinalPresentable (F.obj d) χ :=
  component_presentable M κLP s χ hLP hD F d

example (χ : Cardinal.{w}) [Fact χ.IsRegular] (hLP : κLP ≤ χ)
    (hD : HasCardinalLT (Arrow S) χ) (F : D ⥤ M)
    [IsCardinalPresentable F χ] :
    ∀ d : D, IsCardinalPresentable (F.obj d) χ :=
  fun d ↦ component_presentable M κLP s χ hLP hD F d


example (χ : Cardinal.{w}) [Fact χ.IsRegular]
    (hD : HasCardinalLT (Arrow S) χ) (F : D ⥤ M)
    (hF : ∀ d : D, IsCardinalPresentable (F.obj d) χ) : IsCardinalPresentable F χ :=
  diagram_presentable M κLP s χ hD F hF

example (χ : Cardinal.{w}) [Fact χ.IsRegular] (hLP : κLP ≤ χ)
    (hD : HasCardinalLT (Arrow S) χ) (F : D ⥤ M) :
    IsCardinalPresentable F χ ↔ ∀ d : D, IsCardinalPresentable (F.obj d) χ :=
  presentable_iff_components M κLP s χ hLP hD F


end OriginalComponents

section Concrete

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- This SAME native shape has coincident leg endpoints and two distinct legs per label. -/
def parallelShape : MulticospanShape.{0, 0} where
  L := PUnit
  R := Bool
  fst _ := PUnit.unit
  snd _ := PUnit.unit

/-- The actual first and second arrows are distinct even with identical endpoints. -/
example (r : Bool) :
    (Arrow.mk (WalkingMulticospan.Hom.fst (J := parallelShape) r) :
        Arrow (WalkingMulticospan parallelShape)) ≠
      (Arrow.mk (WalkingMulticospan.Hom.snd (J := parallelShape) r) :
        Arrow (WalkingMulticospan parallelShape)) := by
  intro h
  have ht := congrArg (multicospanArrowEquiv parallelShape) h
  change Sum.inr (Sum.inr (Sum.inl r)) = Sum.inr (Sum.inr (Sum.inr r)) at ht
  have hf := Sum.inr_injective (Sum.inr_injective ht)
  cases hf

example : HasCardinalLT (Arrow (WalkingMulticospan parallelShape)) Cardinal.aleph0.{0} := by
  apply multicospanArrow_bound parallelShape Cardinal.aleph0.{0} le_rfl
  · change HasCardinalLT (PUnit : Type) Cardinal.aleph0.{0}
    exact hasCardinalLT_of_finite _ _ le_rfl
  · change HasCardinalLT Bool Cardinal.aleph0.{0}
    exact hasCardinalLT_of_finite _ _ le_rfl

/-- Both native label universes can be raised independently of the working bound. -/
def raisedShape : MulticospanShape.{1, 2} where
  L := ULift.{1, 0} PUnit
  R := ULift.{2, 0} Bool
  fst _ := ⟨PUnit.unit⟩
  snd _ := ⟨PUnit.unit⟩

example : HasCardinalLT (Arrow (WalkingMulticospan raisedShape)) Cardinal.aleph0.{0} := by
  apply multicospanArrow_bound raisedShape Cardinal.aleph0.{0} le_rfl
  · change HasCardinalLT (ULift.{1, 0} PUnit) Cardinal.aleph0.{0}
    exact hasCardinalLT_of_finite _ _ le_rfl
  · change HasCardinalLT (ULift.{2, 0} Bool) Cardinal.aleph0.{0}
    exact hasCardinalLT_of_finite _ _ le_rfl

/-- No native arrows are inserted when both original label families are empty. -/
def emptyShape : MulticospanShape.{0, 0} where
  L := PEmpty
  R := PEmpty
  fst x := nomatch x
  snd x := nomatch x

example : HasCardinalLT (Arrow (WalkingMulticospan emptyShape)) Cardinal.aleph0.{0} := by
  apply multicospanArrow_bound emptyShape Cardinal.aleph0.{0} le_rfl
  · change HasCardinalLT (PEmpty : Type) Cardinal.aleph0.{0}
    exact hasCardinalLT_of_finite _ _ le_rfl
  · change HasCardinalLT (PEmpty : Type) Cardinal.aleph0.{0}
    exact hasCardinalLT_of_finite _ _ le_rfl

/-- The original finite presentation is kept literally, including its identity equivalence. -/
def finiteIndexData : Discrete Bool ≌ Discrete Bool := Equivalence.refl

example (F : Discrete Bool ⥤ Type) [IsCardinalPresentable F Cardinal.aleph0.{0}]
    (d : Discrete Bool) :
    IsCardinalPresentable (F.obj d) Cardinal.aleph0.{0} :=
  component_presentable (Type) Cardinal.aleph0.{0} finiteIndexData Cardinal.aleph0.{0} le_rfl
    ((hasCardinalLT_arrow_discrete_iff _).2 (hasCardinalLT_of_finite Bool _ le_rfl)) F d

/-- A genuine free finite object supplies compactness without an objectwise-compactness premise. -/
example (d : Discrete Bool) :
    IsCardinalPresentable
      (((HomPowerAccessibility.free (Type) Cardinal.aleph0.{0} finiteIndexData
        (Discrete.mk true)).obj PUnit).obj d) Cardinal.aleph0.{0} := by
  let : Functor.IsCardinalAccessible
      ((evaluation (Discrete Bool) (Type)).obj (Discrete.mk true)) Cardinal.aleph0.{0} :=
    HomPowerAccessibility.evaluation_isCardinalAccessible (Type) Cardinal.aleph0.{0} _
  let : IsCardinalPresentable (PUnit : Type) Cardinal.aleph0.{0} :=
    (hasCardinalLT_of_finite (PUnit : Type) Cardinal.aleph0.{0} le_rfl).isCardinalPresentable
  let F := (HomPowerAccessibility.free (Type) Cardinal.aleph0.{0} finiteIndexData
    (Discrete.mk true)).obj PUnit
  let : IsCardinalPresentable F Cardinal.aleph0.{0} :=
    Adjunction.isCardinalPresentable_leftAdjoint_obj
      (HomPowerAccessibility.freeEvaluationAdjunction (Type) Cardinal.aleph0.{0}
        finiteIndexData (Discrete.mk true)) Cardinal.aleph0.{0} PUnit
  exact component_presentable (Type) Cardinal.aleph0.{0} finiteIndexData Cardinal.aleph0.{0}
    le_rfl ((hasCardinalLT_arrow_discrete_iff _).2
      (hasCardinalLT_of_finite Bool _ le_rfl)) F d


/-- Infinite discrete labels do not satisfy the fixed aleph0 whole-shape bound. -/
example : ¬ HasCardinalLT (Arrow (Discrete ℕ)) Cardinal.aleph0.{0} := by
  rw [hasCardinalLT_arrow_discrete_iff, hasCardinalLT_aleph0_iff]
  intro h
  let : Finite ℕ := h
  exact not_finite ℕ

/-- Its individual constant-singleton components are nevertheless genuinely compact. -/
example (d : Discrete ℕ) :
    IsCardinalPresentable (((Functor.const (Discrete ℕ)).obj (PUnit : Type)).obj d)
      Cardinal.aleph0.{0} :=
  (hasCardinalLT_of_finite (PUnit : Type) Cardinal.aleph0.{0} le_rfl).isCardinalPresentable

/-- The actual nonthin index acts nontrivially on its ORIGINAL Nat coefficient object. -/
def natAction : SingleObj ℕ ⥤ Type where
  obj _ := ℕ
  map n := ↾fun x : ℕ ↦ (show ℕ from n) * x
  map_id _ := by
    ext x
    change 1 * x = x
    exact Nat.one_mul x
  map_comp n m := by
    ext x
    let n₀ : ℕ := n
    let m₀ : ℕ := m
    change (m₀ * n₀) * x = m₀ * (n₀ * x)
    exact Nat.mul_assoc m₀ n₀ x

/-- Doubling is an actual nonidentity transformation commuting with every index action. -/
def doubling : natAction ⟶ natAction where
  app _ := ↾fun x : ℕ ↦ 2 * x
  naturality := by
    intro X Y f
    ext x
    let f₀ : ℕ := f
    let x₀ : ℕ := x
    change 2 * (f₀ * x₀) = f₀ * (2 * x₀)
    exact Nat.mul_left_comm 2 f₀ x₀

/-- This is the actual original index arrow used by the projection-value test. -/
def threeArrow : Arrow (SingleObj ℕ) :=
  Arrow.mk (show SingleObj.star ℕ ⟶ SingleObj.star ℕ from (3 : ℕ))

example :
    ((componentCone (Type) natAction).π.app (.right threeArrow)).app natAction doubling =
      ULift.up (↾fun x : ℕ ↦ 6 * x) := by
  rw [componentCone_right_app]
  congr 1
  apply ConcreteCategory.hom_ext
  intro x
  let x₀ : ℕ := x
  change 3 * (2 * x₀) = 6 * x₀
  rw [← Nat.mul_assoc]

/-- A genuine original arrow bound supplies compactness of the nontrivial action diagram. -/
example (χ : Cardinal.{0}) [Fact χ.IsRegular]
    (hS : HasCardinalLT (Arrow (SingleObj ℕ)) χ) : IsCardinalPresentable natAction χ := by
  have hN : HasCardinalLT ℕ χ :=
    hS.of_injective
      (fun n : ℕ ↦ Arrow.mk (show SingleObj.star ℕ ⟶ SingleObj.star ℕ from n))
      (Arrow.mk_injective (SingleObj.star ℕ) (SingleObj.star ℕ))
  let : IsCardinalPresentable (ℕ : Type) χ := hN.isCardinalPresentable
  exact small_diagram_presentable (Type) natAction Cardinal.aleph0.{0} χ hS (fun _ ↦ by
    change IsCardinalPresentable (ℕ : Type) χ
    infer_instance)



/-- The empty original index and its literal identity presentation are kept. -/
def emptyIndexData : Discrete (PEmpty : Type) ≌ Discrete (PEmpty : Type) := Equivalence.refl

example (F : Discrete (PEmpty : Type) ⥤ Type) :
    IsCardinalPresentable F Cardinal.aleph0.{0} :=
  diagram_presentable (Type) Cardinal.aleph0.{0} emptyIndexData Cardinal.aleph0.{0}
    ((hasCardinalLT_arrow_discrete_iff _).2
      (hasCardinalLT_of_finite (PEmpty : Type) _ le_rfl)) F (fun d ↦ nomatch d.as)

/-- The original raised object/Hom presentation has its SAME explicit small equivalence. -/
def raisedIndexData : Discrete (ULift.{1} ℕ) ≌ Discrete ℕ := Discrete.equivalence Equiv.ulift

example (χ : Cardinal.{0}) [Fact χ.IsRegular]
    (hS : HasCardinalLT (Arrow (Discrete ℕ)) χ)
    (F : Discrete (ULift.{1} ℕ) ⥤ Type)
    (hF : ∀ d, IsCardinalPresentable (F.obj d) χ) : IsCardinalPresentable F χ :=
  diagram_presentable (Type) Cardinal.aleph0.{0} raisedIndexData χ hS F hF

example {F G : Discrete (ULift.{1} ℕ) ⥤ Type} (a : F ⟶ G) (n : ℕ) :
    ((raisedIndexData.congrLeft (E := Type)).functor.map a).app (Discrete.mk n) =
      a.app (Discrete.mk (ULift.up n)) := rfl


end Concrete

end CategoryTheory.Presentable.FunctorPresentabilityTest
