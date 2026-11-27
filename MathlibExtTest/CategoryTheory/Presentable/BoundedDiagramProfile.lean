/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Presentable.BoundedDiagramProfile
public import MathlibExtTest.CategoryTheory.Presentable.FunctorPresentability
public import MathlibExtTest.CategoryTheory.Presentable.DiagramCompactnessCardinal

/-!
# Entire original compactness-profile contracts

Every returned property is checked on the original categories and functors.
Filtered cocones keep their full original legs and naturality. Concrete
endpoint families vary their source and target types, and the coefficient
action is the original nonthin multiplicative Nat action. Empty, infinite
and independently raised original presentations use the same construction.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe w uM vM uD vD

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Presentable.BoundedDiagramProfileTest

open BoundedDiagramProfile

section ReturnedProperties

variable (M : Type uM) [Category.{vM} M] (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
  [IsCardinalLocallyPresentable M κLP]
  {D : Type uD} [Category.{vD} D] {S : Type w} [SmallCategory S] (s : D ≌ S)
  (κ : Cardinal.{w}) (I J : MorphismProperty M) (χ : Cardinal.{w}) [Fact χ.IsRegular]
  (p : Profile M κLP s κ I J χ)

example : κLP ≤ χ := p.lp_le
example : κ ≤ χ := p.generation_le
example : Cardinal.aleph0 < χ := p.uncountable
example : HasCardinalLT S χ := p.objects
example : HasCardinalLT (Arrow S) χ := p.arrows
example (i : I.toSet) : IsCardinalPresentable i.1.left χ := p.sourceI i
example (i : I.toSet) : IsCardinalPresentable i.1.right χ := p.targetI i
example (j : J.toSet) : IsCardinalPresentable j.1.left χ := p.sourceJ j
example (j : J.toSet) : IsCardinalPresentable j.1.right χ := p.targetJ j
example : IsCardinalLocallyPresentable M χ := p.baseLocallyPresentable
example : IsCardinalLocallyPresentable (D ⥤ M) χ := p.diagramLocallyPresentable
example : IsCardinalAccessibleCategory M χ := p.baseAccessible
example : IsCardinalAccessibleCategory (D ⥤ M) χ := p.diagramAccessible
example (d e : D) : HasCardinalLT (e ⟶ d) χ := p.originalHom d e

example (d : D) : (Completeness.cofree M κLP s d).IsCardinalAccessible χ :=
  p.cofreeAccessible d

example (d e : D) : (Completeness.homPower M κLP s d e).IsCardinalAccessible χ :=
  p.powerAccessible d e

example (d : D) : ((evaluation D M).obj d).IsCardinalAccessible χ :=
  p.evaluationAccessible d

example (F : D ⥤ M) :
    IsCardinalPresentable F χ ↔ ∀ d : D, IsCardinalPresentable (F.obj d) χ :=
  p.criterion F

example (F : D ⥤ M) (hF : ∀ d : D, IsCardinalPresentable (F.obj d) χ) :
    IsCardinalPresentable F χ := (p.criterion F).2 hF

example (F : D ⥤ M) [IsCardinalPresentable F χ] (d : D) :
    IsCardinalPresentable (F.obj d) χ := (p.criterion F).1 inferInstance d

/-- A genuine supplied filtered cocone is preserved by the SAME input-rank cofree value. -/
example {K : Type w} [SmallCategory K] [IsCardinalFiltered K χ]
    (G : K ⥤ M) (c : Cocone G) (hc : IsColimit c) (d : D) :
    IsColimit ((Completeness.cofree M κLP s d).mapCocone c) := by
  let : (Completeness.cofree M κLP s d).IsCardinalAccessible χ := p.cofreeAccessible d
  let : PreservesColimitsOfShape K (Completeness.cofree M κLP s d) :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible _ χ K
  exact isColimitOfPreserves _ hc

/-- The selected actual coefficient colimit is sent to an original diagram colimit. -/
example {K : Type w} [SmallCategory K] [IsCardinalFiltered K χ]
    (G : K ⥤ M) (d : D) :
    IsColimit ((Completeness.cofree M κLP s d).mapCocone (colimit.cocone G)) := by
  let : (Completeness.cofree M κLP s d).IsCardinalAccessible χ := p.cofreeAccessible d
  let : PreservesColimitsOfShape K (Completeness.cofree M κLP s d) :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible _ χ K
  exact isColimitOfPreserves _ (colimit.isColimit G)

/-- Every original Hom power preserves the actual selected filtered-colimit cocone. -/
example {K : Type w} [SmallCategory K] [IsCardinalFiltered K χ]
    (G : K ⥤ M) (d e : D) :
    IsColimit ((Completeness.homPower M κLP s d e).mapCocone (colimit.cocone G)) := by
  let : (Completeness.homPower M κLP s d e).IsCardinalAccessible χ := p.powerAccessible d e
  let : PreservesColimitsOfShape K (Completeness.homPower M κLP s d e) :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible _ χ K
  exact isColimitOfPreserves _ (colimit.isColimit G)

/-- Actual evaluation preserves the original filtered diagram cocone at the produced rank. -/
example {K : Type w} [SmallCategory K] [IsCardinalFiltered K χ]
    (G : K ⥤ D ⥤ M) (c : Cocone G) (hc : IsColimit c) (d : D) :
    IsColimit (((evaluation D M).obj d).mapCocone c) := by
  let : ((evaluation D M).obj d).IsCardinalAccessible χ := p.evaluationAccessible d
  let : PreservesColimitsOfShape K ((evaluation D M).obj d) :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible _ χ K
  exact isColimitOfPreserves _ hc

/-- The whole power-cocone leg is the original power function on the coefficient leg. -/
example {K : Type w} [SmallCategory K] (G : K ⥤ M) (c : Cocone G) (d e : D) (k : K) :
    ((Completeness.homPower M κLP s d e).mapCocone c).ι.app k =
      (Completeness.homPower M κLP s d e).map (c.ι.app k) := rfl

/-- The whole cofree-cocone leg retains every original component. -/
example {K : Type w} [SmallCategory K] (G : K ⥤ M) (c : Cocone G) (d e : D) (k : K) :
    (((Completeness.cofree M κLP s d).mapCocone c).ι.app k).app e =
      ((Completeness.cofree M κLP s d).map (c.ι.app k)).app e := rfl

/-- Each original index-action square of the actual preserved cofree leg is retained. -/
example {K : Type w} [SmallCategory K] (G : K ⥤ M) (c : Cocone G) (d : D) (k : K)
    {e f : D} (a : e ⟶ f) :
    ((Completeness.cofree M κLP s d).obj (G.obj k)).map a ≫
        (((Completeness.cofree M κLP s d).mapCocone c).ι.app k).app f =
      (((Completeness.cofree M κLP s d).mapCocone c).ι.app k).app e ≫
        ((Completeness.cofree M κLP s d).obj c.pt).map a :=
  (((Completeness.cofree M κLP s d).mapCocone c).ι.app k).naturality a

example [I.IsSmall.{w}] [J.IsSmall.{w}] :
    ∃ (μ : Cardinal.{w}) (_ : Fact μ.IsRegular), Profile M κLP s κ I J μ :=
  exists_profile M κLP s κ I J

example (hLP : κLP ≤ χ) (hκ : κ ≤ χ) (hω : Cardinal.aleph0 < χ)
    (hArrow : HasCardinalLT (Arrow S) χ)
    (hI : ∀ i : I.toSet, IsCardinalPresentable i.1.left χ ∧
      IsCardinalPresentable i.1.right χ)
    (hJ : ∀ j : J.toSet, IsCardinalPresentable j.1.left χ ∧
      IsCardinalPresentable j.1.right χ) :
    Profile M κLP s κ I J χ :=
  of_bounds M κLP s κ I J χ hLP hκ hω hArrow hI hJ

end ReturnedProperties

section RetainedAndEligibleRanks

variable (M : Type uM) [Category.{vM} M] (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
  [IsCardinalLocallyPresentable M κLP]
  {D : Type uD} [Category.{vD} D] {S : Type w} [SmallCategory S] (s : D ≌ S)
  (κ : Cardinal.{w}) [Fact κ.IsRegular] (I J : MorphismProperty M)

example (hLP : κLP ≤ κ) (hω : Cardinal.aleph0 < κ)
    (hArrow : HasCardinalLT (Arrow S) κ)
    (hI : ∀ i : I.toSet, IsCardinalPresentable i.1.left κ ∧
      IsCardinalPresentable i.1.right κ)
    (hJ : ∀ j : J.toSet, IsCardinalPresentable j.1.left κ ∧
      IsCardinalPresentable j.1.right κ) :
    Profile M κLP s κ I J κ :=
  profile_at_generation_rank M κLP s κ I J hLP hω hArrow hI hJ

example [OrderBot κ.ord.ToType]
    [I.IsCardinalForSmallObjectArgument κ] [J.IsCardinalForSmallObjectArgument κ] :
    ∃ (χ : Cardinal.{w}) (_ : Fact χ.IsRegular), Profile M κLP s κ I J χ :=
  exists_profile_of_eligible M κLP s κ I J

end RetainedAndEligibleRanks

section Concrete

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- Both source and target functions of the first family are genuinely nonconstant. -/
def firstSource : Bool → Type
  | false => PUnit
  | true => Bool

/-- The two original first-family targets are Bool and Nat. -/
def firstTarget : Bool → Type
  | false => Bool
  | true => ℕ

/-- Original tags select the constant-false arrow and the Boolean 0/1 arrow. -/
def firstArrow : (b : Bool) → firstSource b ⟶ firstTarget b
  | false => by
      change (PUnit : Type) ⟶ Bool
      exact ↾fun _ : PUnit ↦ false
  | true => by
      change (Bool : Type) ⟶ ℕ
      exact ↾fun b : Bool ↦ if b then (1 : ℕ) else 0

/-- The second family includes an infinite source and an independently lifted target. -/
def secondSource : Bool → Type
  | false => ℕ
  | true => PUnit

/-- The second-family targets are PUnit and the actual lifted Nat type. -/
def secondTarget : Bool → Type
  | false => PUnit
  | true => ULift.{0} ℕ

/-- The supplied collapse and constant-seven functions retain their original values. -/
def secondArrow : (b : Bool) → secondSource b ⟶ secondTarget b
  | false => ↾fun _ ↦ PUnit.unit
  | true => ↾fun _ ↦ ULift.up 7

/-- The class contains the two original first-family arrows with their varying endpoints. -/
def firstFamily : MorphismProperty (Type) := MorphismProperty.ofHoms firstArrow
/-- The second class retains its infinite source and lifted target arrow. -/
def secondFamily : MorphismProperty (Type) := MorphismProperty.ofHoms secondArrow

local instance : firstFamily.IsSmall.{0} := by
  dsimp [firstFamily]
  infer_instance

local instance : secondFamily.IsSmall.{0} := by
  dsimp [secondFamily]
  infer_instance

/-- These labels contain the literal supplied original arrows and their original endpoints. -/
def firstLabel (b : Bool) : firstFamily.toSet :=
  ⟨Arrow.mk (firstArrow b), MorphismProperty.ofHoms.mk b⟩

/-- The actual original second-family arrow label includes both original endpoint functions. -/
def secondLabel (b : Bool) : secondFamily.toSet :=
  ⟨Arrow.mk (secondArrow b), MorphismProperty.ofHoms.mk b⟩

example : (firstLabel false).1.left = (PUnit : Type) := rfl
example : (firstLabel false).1.right = (Bool : Type) := rfl
example : (firstLabel true).1.left = (Bool : Type) := rfl
example : (firstLabel true).1.right = (ℕ : Type) := rfl
example : (secondLabel false).1.left = (ℕ : Type) := rfl
example : (secondLabel false).1.right = (PUnit : Type) := rfl
example : (secondLabel true).1.left = (PUnit : Type) := rfl
example : (secondLabel true).1.right = (ULift.{0} ℕ : Type) := rfl

example : firstArrow false PUnit.unit = false := rfl
example : (show (Bool : Type) ⟶ ℕ from firstArrow true) false = 0 := rfl
example : (show (Bool : Type) ⟶ ℕ from firstArrow true) true = 1 := rfl
example (n : ℕ) : secondArrow false n = PUnit.unit := rfl
example : secondArrow true PUnit.unit = ULift.up 7 := rfl

/-- The input generation value is strictly different from the actual finite-presentability rank. -/
def generationRank : Cardinal.{0} := Order.succ Cardinal.aleph0.{0}

example : Cardinal.aleph0.{0} < generationRank := Order.lt_succ _

/-- The original infinite nonthin index has its literal identity equivalence. -/
def natIndexData : SingleObj ℕ ≌ SingleObj ℕ := Equivalence.refl

/-- The original infinite discrete index also retains its identity equivalence. -/
def infiniteIndexData : Discrete ℕ ≌ Discrete ℕ := Equivalence.refl

/-- The rank is selected from the actual complete original profile constructor. -/
def chosenRank {D : Type uD} [Category.{vD} D]
    {S : Type} [SmallCategory S] (s : D ≌ S) : Cardinal.{0} :=
  (exists_profile (Type) Cardinal.aleph0.{0} s generationRank firstFamily secondFamily).choose

local instance chosenRank_regular {D : Type uD} [Category.{vD} D]
    {S : Type} [SmallCategory S] (s : D ≌ S) : Fact (chosenRank s).IsRegular :=
  (exists_profile (Type) Cardinal.aleph0.{0} s generationRank firstFamily secondFamily).choose_spec.choose

theorem chosenProfile {D : Type uD} [Category.{vD} D]
    {S : Type} [SmallCategory S] (s : D ≌ S) :
    Profile (Type) Cardinal.aleph0.{0} s generationRank firstFamily secondFamily (chosenRank s) :=
  (exists_profile (Type) Cardinal.aleph0.{0} s generationRank firstFamily secondFamily).choose_spec.choose_spec

example : Cardinal.aleph0.{0} ≤ chosenRank natIndexData := (chosenProfile natIndexData).lp_le
example : generationRank ≤ chosenRank natIndexData := (chosenProfile natIndexData).generation_le
example : Cardinal.aleph0.{0} < chosenRank natIndexData := (chosenProfile natIndexData).uncountable
example : (chosenRank natIndexData).IsRegular := Fact.out

example : HasCardinalLT (SingleObj ℕ) (chosenRank natIndexData) :=
  (chosenProfile natIndexData).objects

example : HasCardinalLT (Arrow (SingleObj ℕ)) (chosenRank natIndexData) :=
  (chosenProfile natIndexData).arrows

example (b : Bool) : IsCardinalPresentable (firstSource b) (chosenRank natIndexData) :=
  (chosenProfile natIndexData).sourceI (firstLabel b)

example (b : Bool) : IsCardinalPresentable (firstTarget b) (chosenRank natIndexData) :=
  (chosenProfile natIndexData).targetI (firstLabel b)

example (b : Bool) : IsCardinalPresentable (secondSource b) (chosenRank natIndexData) :=
  (chosenProfile natIndexData).sourceJ (secondLabel b)

example (b : Bool) : IsCardinalPresentable (secondTarget b) (chosenRank natIndexData) :=
  (chosenProfile natIndexData).targetJ (secondLabel b)

/-- The resulting bound proves compactness of the actual nontrivial action diagram. -/
example : IsCardinalPresentable FunctorPresentabilityTest.natAction (chosenRank natIndexData) := by
  apply ((chosenProfile natIndexData).criterion FunctorPresentabilityTest.natAction).2
  intro d
  change IsCardinalPresentable (ℕ : Type) (chosenRank natIndexData)
  exact (chosenProfile natIndexData).sourceJ (secondLabel false)

/-- Both original component-equation maps still compute the full nonidentity action. -/
example :
    ((FunctorPresentability.componentCone (Type) FunctorPresentabilityTest.natAction).π.app
      (.right FunctorPresentabilityTest.threeArrow)).app
      FunctorPresentabilityTest.natAction FunctorPresentabilityTest.doubling =
        ULift.up (↾fun x : ℕ ↦ 6 * x) := by
  rw [FunctorPresentability.componentCone_right_app]
  congr 1
  apply ConcreteCategory.hom_ext
  intro x
  let x₀ : ℕ := x
  change 3 * (2 * x₀) = 6 * x₀
  rw [← Nat.mul_assoc]

/-- A genuinely varying infinite original diagram is compact at the chosen bound. -/
def varyingFiniteDiagram : Discrete ℕ ⥤ Type :=
  Discrete.functor (fun n : ℕ ↦ Fin (n + 1))

example : IsCardinalPresentable varyingFiniteDiagram (chosenRank infiniteIndexData) := by
  apply ((chosenProfile infiniteIndexData).criterion varyingFiniteDiagram).2
  intro d
  change IsCardinalPresentable (Fin (d.as + 1)) (chosenRank infiniteIndexData)
  let : IsCardinalPresentable (Fin (d.as + 1)) Cardinal.aleph0.{0} :=
    (hasCardinalLT_of_finite _ _ le_rfl).isCardinalPresentable
  exact isCardinalPresentable_of_le _ (chosenProfile infiniteIndexData).lp_le

example : ¬ HasCardinalLT (Arrow (Discrete ℕ)) Cardinal.aleph0.{0} := by
  rw [hasCardinalLT_arrow_discrete_iff, hasCardinalLT_aleph0_iff]
  intro h
  let : Finite ℕ := h
  exact not_finite ℕ

/-- Every original empty-index diagram satisfies the actual whole criterion. -/
example (F : Discrete (PEmpty : Type) ⥤ Type) :
    IsCardinalPresentable F (chosenRank FunctorPresentabilityTest.emptyIndexData) :=
  ((chosenProfile FunctorPresentabilityTest.emptyIndexData).criterion F).2
    (fun d ↦ nomatch d.as)

/-- The raised original carrier is retained while only its representative arrow type is bounded. -/
example (F : Discrete (ULift.{1} ℕ) ⥤ Type)
    (hF : ∀ d, IsCardinalPresentable (F.obj d)
      (chosenRank FunctorPresentabilityTest.raisedIndexData)) :
    IsCardinalPresentable F (chosenRank FunctorPresentabilityTest.raisedIndexData) :=
  ((chosenProfile FunctorPresentabilityTest.raisedIndexData).criterion F).2 hF

example {F G : Discrete (ULift.{1} ℕ) ⥤ Type} (a : F ⟶ G) (n : ℕ) :
    ((FunctorPresentabilityTest.raisedIndexData.congrLeft (E := Type)).functor.map a).app
      (Discrete.mk n) = a.app (Discrete.mk (ULift.up n)) := rfl

/-- The chosen actual filtered Type cocone is preserved by every original Nat-index Hom power. -/
example {K : Type} [SmallCategory K] [IsCardinalFiltered K (chosenRank natIndexData)]
    (G : K ⥤ Type) (d e : SingleObj ℕ) :
    IsColimit ((Completeness.homPower (Type) Cardinal.aleph0.{0} natIndexData d e).mapCocone
      (colimit.cocone G)) := by
  let R := Completeness.homPower (Type) Cardinal.aleph0.{0} natIndexData d e
  let : R.IsCardinalAccessible (chosenRank natIndexData) :=
    (chosenProfile natIndexData).powerAccessible d e
  let : PreservesColimitsOfShape K R :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible R (chosenRank natIndexData) K
  exact isColimitOfPreserves R (colimit.isColimit G)

/-- The stronger entry consumes the literal two nonconstant original families at the supplied κ. -/
example (κ : Cardinal.{0}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [firstFamily.IsCardinalForSmallObjectArgument κ]
    [secondFamily.IsCardinalForSmallObjectArgument κ] :
    ∃ (χ : Cardinal.{0}) (_ : Fact χ.IsRegular),
      Profile (Type) Cardinal.aleph0.{0} natIndexData κ firstFamily secondFamily χ :=
  exists_profile_of_eligible (Type) Cardinal.aleph0.{0} natIndexData κ firstFamily secondFamily

/-- Honest sufficient bounds retain this original κ while the cofree values still use aleph0. -/
example (κ : Cardinal.{0}) [Fact κ.IsRegular]
    (hLP : Cardinal.aleph0.{0} ≤ κ) (hω : Cardinal.aleph0.{0} < κ)
    (hArrow : HasCardinalLT (Arrow (SingleObj ℕ)) κ)
    (hI : ∀ i : firstFamily.toSet, IsCardinalPresentable i.1.left κ ∧
      IsCardinalPresentable i.1.right κ)
    (hJ : ∀ j : secondFamily.toSet, IsCardinalPresentable j.1.left κ ∧
      IsCardinalPresentable j.1.right κ) :
    Profile (Type) Cardinal.aleph0.{0} natIndexData κ firstFamily secondFamily κ :=
  profile_at_generation_rank (Type) Cardinal.aleph0.{0} natIndexData κ firstFamily secondFamily
    hLP hω hArrow hI hJ

end Concrete

end CategoryTheory.Presentable.BoundedDiagramProfileTest
