/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import MathlibExt.CategoryTheory.MorphismProperty.AdjointFamily
public import MathlibExt.CategoryTheory.Operad.Tensor.EnvelopingAttachmentFiltration

/-!
# The model category of original color-indexed objects

The model structure is constructed on the actual Pi category `W → C`.
Its factors and lifts are assembled from the original coordinate factors and
lifts. The original A5 color-support functor is left adjoint to evaluation,
so the literal color images of the given I/J families detect precisely the
coordinatewise trivial fibrations/fibrations.

This supplies the source category in White–Yau, *Bousfield localization and
algebras over colored operads*, arXiv:1503.06720v2, Theorem 6.3.1. It adds no
cofibrancy condition on the unit or the domains of the original generators.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v uc uj vj us

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.SemiModel.ColorSource

variable (C : Type u) [Category.{v} C] (W : Type uc)

/-- A property of the original arrows at every original color. -/
def pointwiseProperty (P : MorphismProperty C) : MorphismProperty (W → C) :=
  MorphismProperty.pi (fun _ : W => P)

/-- Pointwise membership retains the exact original coordinate arrows. -/
theorem pointwiseProperty_iff (P : MorphismProperty C) {X Y : W → C} (f : X ⟶ Y) :
    pointwiseProperty C W P f ↔ ∀ w, P (f w) := Iff.rfl

/-- Taking both base properties commutes with the actual pointwise property. -/
theorem pointwiseProperty_inf (P Q : MorphismProperty C) :
    pointwiseProperty C W (P ⊓ Q) =
      pointwiseProperty C W P ⊓ pointwiseProperty C W Q := by
  ext X Y f
  exact forall_and

/-- The pointwise weak class has the original two-out-of-three property. -/
theorem pointwiseProperty_hasTwoOutOfThree (P : MorphismProperty C)
    [P.HasTwoOutOfThreeProperty] :
    (pointwiseProperty C W P).HasTwoOutOfThreeProperty where
  comp_mem f g hf hg w := P.comp_mem (f w) (g w) (hf w) (hg w)
  of_postcomp f g hg hfg w := P.of_postcomp (f w) (g w) (hg w) (hfg w)
  of_precomp f g hf hfg w := P.of_precomp (f w) (g w) (hf w) (hfg w)

/-- Evaluating the actual arrow retract proves pointwise retract closure. -/
theorem pointwiseProperty_isStableUnderRetracts (P : MorphismProperty C)
    [P.IsStableUnderRetracts] :
    (pointwiseProperty C W P).IsStableUnderRetracts where
  of_retract h hg w := MorphismProperty.of_retract (h.map (Pi.eval (fun _ : W => C) w)) (hg w)

/-- The canonical discrete/Pi equivalence gives all original diagram limits. -/
theorem pointwiseHasLimitsOfShape (J : Type uj) [Category.{vj} J]
    [HasLimitsOfShape J C] : HasLimitsOfShape J (W → C) :=
  Adjunction.hasLimitsOfShape_of_equivalence (piEquivalenceFunctorDiscrete W C).functor

/-- The same equivalence gives all original diagram colimits. -/
theorem pointwiseHasColimitsOfShape (J : Type uj) [Category.{vj} J]
    [HasColimitsOfShape J C] : HasColimitsOfShape J (W → C) :=
  Adjunction.hasColimitsOfShape_of_equivalence (piEquivalenceFunctorDiscrete W C).functor

/-- Completeness in the original diagram universes passes to the actual Pi category. -/
theorem pointwiseHasLimitsOfSize [HasLimitsOfSize.{vj, uj} C] :
    HasLimitsOfSize.{vj, uj} (W → C) where
  has_limits_of_shape J := pointwiseHasLimitsOfShape C W J

/-- Cocompleteness in the original diagram universes passes to the actual Pi category. -/
theorem pointwiseHasColimitsOfSize [HasColimitsOfSize.{vj, uj} C] :
    HasColimitsOfSize.{vj, uj} (W → C) where
  has_colimits_of_shape J := pointwiseHasColimitsOfShape C W J

/-- Finite completeness is derived solely from the base finite completeness. -/
theorem pointwiseHasFiniteLimits [HasFiniteLimits C] : HasFiniteLimits (W → C) where
  out J := pointwiseHasLimitsOfShape C W J

/-- Finite cocompleteness is derived solely from the base finite cocompleteness. -/
theorem pointwiseHasFiniteColimits [HasFiniteColimits C] : HasFiniteColimits (W → C) where
  out J := pointwiseHasColimitsOfShape C W J

variable {C W}

/-- Every original square in the Pi category is lifted coordinatewise. -/
theorem pointwiseHasLiftingProperty {A B X Y : W → C} (i : A ⟶ B) (p : X ⟶ Y)
    (h : ∀ w, HasLiftingProperty (i w) (p w)) : HasLiftingProperty i p where
  sq_hasLift := fun {f g} sq => by
    let s (w : W) : CommSq (f w) (i w) (p w) (g w) := ⟨congrFun sq.w w⟩
    let (w : W) : HasLiftingProperty (i w) (p w) := h w
    exact CommSq.HasLift.mk'
      { l := fun w => (s w).lift
        fac_left := funext (fun w => (s w).fac_left)
        fac_right := funext (fun w => (s w).fac_right) }

variable (C W)

/-- The actual intermediate family and both factor maps use the base factors. -/
@[simps]
def pointwiseFactorizationData (P Q : MorphismProperty C) [HasFactorization P Q]
    {X Y : W → C} (f : X ⟶ Y) :
    MapFactorizationData (pointwiseProperty C W P) (pointwiseProperty C W Q) f where
  Z w := (factorizationData P Q (f w)).Z
  i w := (factorizationData P Q (f w)).i
  p w := (factorizationData P Q (f w)).p
  fac := funext (fun w => (factorizationData P Q (f w)).fac)
  hi w := (factorizationData P Q (f w)).hi
  hp w := (factorizationData P Q (f w)).hp

/-- Actual base factorizations give every pointwise factorization. -/
theorem pointwiseHasFactorization (P Q : MorphismProperty C) [HasFactorization P Q] :
    HasFactorization (pointwiseProperty C W P) (pointwiseProperty C W Q) where
  nonempty_mapFactorizationData f := ⟨pointwiseFactorizationData C W P Q f⟩

section Model

variable [ModelCategory C]

/-- The source fibration class is the original base class at every color. -/
@[instance_reducible]
def pointwiseCategoryWithFibrations : CategoryWithFibrations (W → C) :=
  ⟨pointwiseProperty C W (fibrations C)⟩

/-- The source cofibration class is the original base class at every color. -/
@[instance_reducible]
def pointwiseCategoryWithCofibrations : CategoryWithCofibrations (W → C) :=
  ⟨pointwiseProperty C W (cofibrations C)⟩

/-- The source weak class is the original base class at every color. -/
@[instance_reducible]
def pointwiseCategoryWithWeakEquivalences : CategoryWithWeakEquivalences (W → C) :=
  ⟨pointwiseProperty C W (weakEquivalences C)⟩

set_option backward.isDefEq.respectTransparency false in
/-- The genuine model category of the same original color-indexed objects. -/
@[instance_reducible]
def pointwiseModelCategory : ModelCategory (W → C) := by
  letI : CategoryWithFibrations (W → C) := pointwiseCategoryWithFibrations C W
  letI : CategoryWithCofibrations (W → C) := pointwiseCategoryWithCofibrations C W
  letI : CategoryWithWeakEquivalences (W → C) := pointwiseCategoryWithWeakEquivalences C W
  exact
    { categoryWithFibrations := pointwiseCategoryWithFibrations C W
      categoryWithCofibrations := pointwiseCategoryWithCofibrations C W
      categoryWithWeakEquivalences := pointwiseCategoryWithWeakEquivalences C W
      cm1a := pointwiseHasFiniteLimits C W
      cm1b := pointwiseHasFiniteColimits C W
      cm2 := pointwiseProperty_hasTwoOutOfThree C W (weakEquivalences C)
      cm3a := pointwiseProperty_isStableUnderRetracts C W (weakEquivalences C)
      cm3b := pointwiseProperty_isStableUnderRetracts C W (fibrations C)
      cm3c := pointwiseProperty_isStableUnderRetracts C W (cofibrations C)
      cm4a := fun i p hi hwi hp => by
        apply pointwiseHasLiftingProperty i p
        intro w
        let : Cofibration (i w) := ⟨hi.mem w⟩
        let : WeakEquivalence (i w) := ⟨hwi.mem w⟩
        let : Fibration (p w) := ⟨hp.mem w⟩
        infer_instance
      cm4b := fun i p hi hp hwp => by
        apply pointwiseHasLiftingProperty i p
        intro w
        let : Cofibration (i w) := ⟨hi.mem w⟩
        let : Fibration (p w) := ⟨hp.mem w⟩
        let : WeakEquivalence (p w) := ⟨hwp.mem w⟩
        infer_instance
      cm5a := by
        change HasFactorization
          (pointwiseProperty C W (cofibrations C) ⊓ pointwiseProperty C W (weakEquivalences C))
          (pointwiseProperty C W (fibrations C))
        rw [← pointwiseProperty_inf]
        exact pointwiseHasFactorization C W (trivialCofibrations C) (fibrations C)
      cm5b := by
        change HasFactorization (pointwiseProperty C W (cofibrations C))
          (pointwiseProperty C W (fibrations C) ⊓ pointwiseProperty C W (weakEquivalences C))
        rw [← pointwiseProperty_inf]
        exact pointwiseHasFactorization C W (cofibrations C) (trivialFibrations C) }

/-- The constructed source weak equivalences are exactly the coordinate weak equivalences. -/
theorem weakEquivalences_eq :
    letI : ModelCategory (W → C) := pointwiseModelCategory C W
    weakEquivalences (W → C) = pointwiseProperty C W (weakEquivalences C) := rfl

/-- The constructed source fibrations are exactly the coordinate fibrations. -/
theorem fibrations_eq :
    letI : ModelCategory (W → C) := pointwiseModelCategory C W
    fibrations (W → C) = pointwiseProperty C W (fibrations C) := rfl

/-- The constructed source cofibrations are exactly the coordinate cofibrations. -/
theorem cofibrations_eq :
    letI : ModelCategory (W → C) := pointwiseModelCategory C W
    cofibrations (W → C) = pointwiseProperty C W (cofibrations C) := rfl

/-- Both original source trivial-fibration conditions hold at every coordinate. -/
theorem trivialFibrations_eq :
    letI : ModelCategory (W → C) := pointwiseModelCategory C W
    trivialFibrations (W → C) = pointwiseProperty C W (trivialFibrations C) := by
  let : ModelCategory (W → C) := pointwiseModelCategory C W
  exact (pointwiseProperty_inf C W (fibrations C) (weakEquivalences C)).symm

/-- Both original source trivial-cofibration conditions hold at every coordinate. -/
theorem trivialCofibrations_eq :
    letI : ModelCategory (W → C) := pointwiseModelCategory C W
    trivialCofibrations (W → C) = pointwiseProperty C W (trivialCofibrations C) := by
  let : ModelCategory (W → C) := pointwiseModelCategory C W
  exact (pointwiseProperty_inf C W (cofibrations C) (weakEquivalences C)).symm

end Model

section ColorAdjunction

variable [HasInitial C]

/-- The actual A5 supported object and supported map, at the original color. -/
abbrev colorFree (w : W) : C ⥤ (W → C) :=
  Operad.Tensor.Enveloping.Filtration.colorFunctor w

/-- Evaluation reads the same original coordinate object and arrow. -/
abbrev colorEvaluation (w : W) : (W → C) ⥤ C := Pi.eval (fun _ : W => C) w

/-- The color-support Hom equivalence uses the actual A5 inclusion and comparison. -/
def colorHomEquiv (w : W) (X : C) (M : W → C) :
    ((colorFree C W w).obj X ⟶ M) ≃ (X ⟶ M w) where
  toFun f := (Operad.Tensor.Enveloping.Filtration.atColorIso w X).inv ≫ f w
  invFun := Operad.Tensor.Enveloping.Filtration.colorInclusion w
  left_inv f := by
    apply Operad.Tensor.Enveloping.Filtration.colorHom_ext w X
    apply (cancel_epi (Operad.Tensor.Enveloping.Filtration.atColorIso w X).inv).1
    exact Operad.Tensor.Enveloping.Filtration.colorInclusion_at w _
  right_inv f := Operad.Tensor.Enveloping.Filtration.colorInclusion_at w f

/-- The original supported-cell functor is actually left adjoint to color evaluation. -/
def colorFreeEvaluationAdjunction (w : W) : colorFree C W w ⊣ colorEvaluation C W w :=
  Adjunction.mkOfHomEquiv
    { homEquiv := colorHomEquiv C W w
      homEquiv_naturality_left_symm := fun f g =>
        (Operad.Tensor.Enveloping.Filtration.colorInclusion_pre w f g).symm
      homEquiv_naturality_right := fun f g => by
        change _ ≫ (f w ≫ g w) = (_ ≫ f w) ≫ g w
        exact (Category.assoc _ _ _).symm }

/-- The family retains the original color and original generator arrow together. -/
def colorGenerators (P : MorphismProperty C) : MorphismProperty (W → C) :=
  adjointFamilyGenerators (colorFree C W) P

/-- Right lifting against the actual supported generators is coordinate right lifting. -/
theorem colorGenerators_rlp_iff (P : MorphismProperty C) {X Y : W → C} (f : X ⟶ Y) :
    (colorGenerators C W P).rlp f ↔ ∀ w, P.rlp (f w) :=
  adjointFamilyGenerators_rlp_iff (colorFree C W) (colorEvaluation C W)
    (colorFreeEvaluationAdjunction C W) P f

/-- The full color right class equals the original pointwise right class. -/
theorem colorGenerators_rlp_eq (P : MorphismProperty C) :
    (colorGenerators C W P).rlp = pointwiseProperty C W P.rlp := by
  ext X Y f
  exact colorGenerators_rlp_iff C W P f

/-- Small colors and the original small family give the literal color-family size. -/
theorem colorGenerators_isSmall (P : MorphismProperty C)
    [Small.{us} W] [P.IsSmall.{us}] : (colorGenerators C W P).IsSmall.{us} :=
  adjointFamilyGenerators_isSmall (colorFree C W) P

/-- An original base-family member retains its actual whole supported map. -/
theorem colorFreeMap_mem_colorGenerators (P : MorphismProperty C) (w : W)
    {X Y : C} (f : X ⟶ Y) (hf : P f) :
    colorGenerators C W P ((colorFree C W w).map f) :=
  map_mem_adjointFamilyGenerators (colorFree C W) P w f hf

/-- The explicit pointwise initial object retains the original initial object at every color. -/
def pointwiseInitial : W → C := fun _ => ⊥_ C

/-- The actual initial maps of every original coordinate form one whole-family map. -/
def pointwiseInitialMap (X : W → C) : pointwiseInitial C W ⟶ X :=
  fun w => initial.to (X w)

/-- The explicit initial family is actually initial in the original Pi category. -/
def pointwiseInitialIsInitial : IsInitial (pointwiseInitial C W) :=
  IsInitial.ofUniqueHom (pointwiseInitialMap C W)
    (fun X f => funext (fun w => initial.hom_ext (f w) (initial.to (X w))))

end ColorAdjunction

section OriginalFamilies

variable [ModelCategory C]

/-- The original I-RLP equation gives precisely the source trivial fibrations. -/
theorem colorIGenerators_rlp_eq (I : MorphismProperty C)
    (hI : I.rlp = trivialFibrations C) :
    letI : ModelCategory (W → C) := pointwiseModelCategory C W
    (colorGenerators C W I).rlp = trivialFibrations (W → C) := by
  let : ModelCategory (W → C) := pointwiseModelCategory C W
  rw [colorGenerators_rlp_eq, hI]
  exact (trivialFibrations_eq C W).symm

/-- The original J-RLP equation gives precisely the source fibrations. -/
theorem colorJGenerators_rlp_eq (J : MorphismProperty C)
    (hJ : J.rlp = fibrations C) :
    letI : ModelCategory (W → C) := pointwiseModelCategory C W
    (colorGenerators C W J).rlp = fibrations (W → C) := by
  let : ModelCategory (W → C) := pointwiseModelCategory C W
  rw [colorGenerators_rlp_eq, hJ]
  exact (fibrations_eq C W).symm

/-- Original I-lifting determines the full actual source cofibration class. -/
theorem colorIGenerators_cofibrations_eq (I : MorphismProperty C)
    (hI : I.rlp = trivialFibrations C) :
    letI : ModelCategory (W → C) := pointwiseModelCategory C W
    (colorGenerators C W I).rlp.llp = cofibrations (W → C) := by
  let : ModelCategory (W → C) := pointwiseModelCategory C W
  rw [colorIGenerators_rlp_eq C W I hI]
  exact HomotopicalAlgebra.trivialFibrations_llp (W → C)

/-- Original J-lifting determines the full actual source trivial-cofibration class. -/
theorem colorJGenerators_trivialCofibrations_eq (J : MorphismProperty C)
    (hJ : J.rlp = fibrations C) :
    letI : ModelCategory (W → C) := pointwiseModelCategory C W
    (colorGenerators C W J).rlp.llp = trivialCofibrations (W → C) := by
  let : ModelCategory (W → C) := pointwiseModelCategory C W
  rw [colorJGenerators_rlp_eq C W J hJ]
  exact HomotopicalAlgebra.fibrations_llp (W → C)

/-- Every actual color-supported I-arrow is a source cofibration, without domain cofibrancy. -/
theorem colorIGenerators_le_cofibrations (I : MorphismProperty C)
    (hI : I.rlp = trivialFibrations C) :
    letI : ModelCategory (W → C) := pointwiseModelCategory C W
    colorGenerators C W I ≤ cofibrations (W → C) := by
  let : ModelCategory (W → C) := pointwiseModelCategory C W
  rw [← colorIGenerators_cofibrations_eq C W I hI]
  exact (colorGenerators C W I).le_llp_rlp

/-- Every actual color-supported J-arrow is a source trivial cofibration. -/
theorem colorJGenerators_le_trivialCofibrations (J : MorphismProperty C)
    (hJ : J.rlp = fibrations C) :
    letI : ModelCategory (W → C) := pointwiseModelCategory C W
    colorGenerators C W J ≤ trivialCofibrations (W → C) := by
  let : ModelCategory (W → C) := pointwiseModelCategory C W
  rw [← colorJGenerators_trivialCofibrations_eq C W J hJ]
  exact (colorGenerators C W J).le_llp_rlp

/-- The original I-RLP equation already implies that all original I-arrows are cofibrations. -/
theorem originalIGenerators_le_cofibrations (I : MorphismProperty C)
    (hI : I.rlp = trivialFibrations C) : I ≤ cofibrations C := by
  rw [← HomotopicalAlgebra.trivialFibrations_llp C, ← hI]
  exact I.le_llp_rlp

/-- The original J-RLP equation already implies that all original J-arrows are trivial cofibrations. -/
theorem originalJGenerators_le_trivialCofibrations (J : MorphismProperty C)
    (hJ : J.rlp = fibrations C) : J ≤ trivialCofibrations C := by
  rw [← HomotopicalAlgebra.fibrations_llp C, ← hJ]
  exact J.le_llp_rlp

/-- The actual supported image of any original cofibration is a source cofibration. -/
theorem colorFreeMap_cofibration (w : W) {X Y : C} (f : X ⟶ Y)
    (hf : cofibrations C f) :
    letI : ModelCategory (W → C) := pointwiseModelCategory C W
    cofibrations (W → C) ((colorFree C W w).map f) := by
  let : ModelCategory (W → C) := pointwiseModelCategory C W
  exact colorIGenerators_le_cofibrations C W (cofibrations C)
    (HomotopicalAlgebra.cofibrations_rlp C) _
    (colorFreeMap_mem_colorGenerators C W (cofibrations C) w f hf)

/-- The actual supported image of any original trivial cofibration is a source trivial cofibration. -/
theorem colorFreeMap_trivialCofibration (w : W) {X Y : C} (f : X ⟶ Y)
    (hf : trivialCofibrations C f) :
    letI : ModelCategory (W → C) := pointwiseModelCategory C W
    trivialCofibrations (W → C) ((colorFree C W w).map f) := by
  let : ModelCategory (W → C) := pointwiseModelCategory C W
  exact colorJGenerators_le_trivialCofibrations C W (trivialCofibrations C)
    (HomotopicalAlgebra.trivialCofibrations_rlp C) _
    (colorFreeMap_mem_colorGenerators C W (trivialCofibrations C) w f hf)

/-- Cofibrancy of the actual source initial map is exactly coordinate cofibrancy. -/
theorem isCofibrant_iff (X : W → C) :
    letI : ModelCategory (W → C) := pointwiseModelCategory C W
    IsCofibrant X ↔ ∀ w, IsCofibrant (X w) := by
  let : ModelCategory (W → C) := pointwiseModelCategory C W
  refine (HomotopicalAlgebra.isCofibrant_iff_of_isInitial
    (pointwiseInitialMap C W X) (pointwiseInitialIsInitial C W)).trans ?_
  simp only [cofibration_iff]
  exact Iff.rfl

end OriginalFamilies

section EmptyColors

variable [IsEmpty W]

/-- For empty original colors the actual source Hom type has exactly one arrow. -/
@[instance_reducible]
def emptyColorHomUnique (X Y : W → C) : Unique (X ⟶ Y) where
  default w := isEmptyElim w
  uniq _ := funext (fun w => isEmptyElim w)

/-- Every actual empty color family is initial, with its unique original maps. -/
def emptyColorIsInitial (X : W → C) : IsInitial X :=
  IsInitial.ofUniqueHom (fun Y => (emptyColorHomUnique C W X Y).default)
    (fun Y f => (emptyColorHomUnique C W X Y).uniq f)

/-- Every actual empty color family is terminal, with its unique original maps. -/
def emptyColorIsTerminal (X : W → C) : IsTerminal X :=
  IsTerminal.ofUniqueHom (fun Y => (emptyColorHomUnique C W Y X).default)
    (fun Y f => (emptyColorHomUnique C W Y X).uniq f)

/-- An empty original color family imposes no coordinate property conditions. -/
theorem pointwiseProperty_empty_eq_top (P : MorphismProperty C) :
    pointwiseProperty C W P = ⊤ := by
  ext X Y f
  exact ⟨fun _ => trivial, fun _ w => isEmptyElim w⟩

/-- The actual literal color generator family is empty when the original color type is empty. -/
theorem colorGenerators_empty_eq_bot [HasInitial C] (P : MorphismProperty C) :
    colorGenerators C W P = ⊥ := by
  ext X Y f
  constructor
  · intro hf
    obtain ⟨q, _⟩ := adjointFamilyGenerators_iff (colorFree C W) P f |>.mp hf
    exact isEmptyElim q.1
  · intro hf
    exact hf.elim

/-- All five source model classes have their terminal-category values for empty colors. -/
theorem emptyColorModelClasses_eq [ModelCategory C] :
    letI : ModelCategory (W → C) := pointwiseModelCategory C W
    weakEquivalences (W → C) = ⊤ ∧ fibrations (W → C) = ⊤ ∧
      cofibrations (W → C) = ⊤ ∧ trivialFibrations (W → C) = ⊤ ∧
      trivialCofibrations (W → C) = ⊤ := by
  let : ModelCategory (W → C) := pointwiseModelCategory C W
  rw [weakEquivalences_eq, fibrations_eq, cofibrations_eq,
    trivialFibrations_eq, trivialCofibrations_eq]
  exact ⟨pointwiseProperty_empty_eq_top C W _, pointwiseProperty_empty_eq_top C W _,
    pointwiseProperty_empty_eq_top C W _, pointwiseProperty_empty_eq_top C W _,
    pointwiseProperty_empty_eq_top C W _⟩

end EmptyColors

end HomotopicalAlgebra.SemiModel.ColorSource
